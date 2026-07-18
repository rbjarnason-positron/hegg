{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Projected (tests) where

import Control.Exception (SomeException, displayException, evaluate, try)
import Data.List (isInfixOf)
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Data.Equality.Analysis (Analysis (..))
import Data.Equality.Extraction (depthCost, extractBest)
import Data.Equality.Graph (ClassId, EGraph, ENode (..), find, sizeNM)
import Data.Equality.Graph.Internal (classes, memo)
import Data.Equality.Graph.Lens (_class, _data, _nodes, (^.))
import Data.Equality.Graph.Monad
    ( EGraphM
    , add
    , egraph
    , merge
    , rebuild
    , represent
    )
import Data.Equality.Matching (findVarName, pat)
import Data.Equality.Matching.Database (findSubst)
import Data.Equality.Saturation
    ( AppliedRoots
    , Projection (..)
    , Rewrite (..)
    , runEqualitySaturation
    , runEqualitySaturationWithProjections
    , wasAppliedAt
    )
import Data.Equality.Saturation.Scheduler
    ( BackoffScheduler (..)
    , defaultBackoffScheduler
    )
import Data.Equality.Utils (Fix (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
    ( assertBool
    , assertFailure
    , testCase
    , (@?=)
    )

data Term a
    = Value String
    | Ref String
    | Wrap a
    | Use a
    | Result a
    | Pair a a
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Analysis (Maybe String) Term where
    makeA = \case
      Value value -> Just value
      Ref _ -> Nothing
      Wrap child -> child
      Use child -> child
      Result child -> child
      Pair left right
        | left == right -> left
        | otherwise -> Nothing

    joinA Nothing right = right
    joinA left Nothing = left
    joinA left right
      | left == right = left
      | otherwise = Nothing

nodesAt :: ClassId -> EGraph analysis Term -> S.Set (ENode Term)
nodesAt classId graph = graph ^. _class (find classId graph) . _nodes

assertSeparate :: String -> EGraph analysis Term -> ClassId -> ClassId -> IO ()
assertSeparate message graph left right =
    assertBool message $ find left graph /= find right graph

runProjected
    :: [Projection]
    -> [Rewrite (Maybe String) Term]
    -> EGraphM (Maybe String) Term AppliedRoots
runProjected projections =
    runEqualitySaturationWithProjections projections defaultBackoffScheduler

tests :: TestTree
tests =
    testGroup
      "Projected saturation"
      [ testCase "follows transitive projections and reports roots" transitive
      , testCase "canonicalizes saved class IDs" recanonicalizes
      , testCase "does not rewrite protected anchor roots" protectsMatchRoots
      , testCase
          "conditions see definitions while RHS variables retain anchors"
          projectedCondition
      , testCase
          "condition-rejected matches are not reported"
          rejectedCondition
      , testCase "rejects a protected anchor as the whole RHS" protectedRhs
      , testCase "reports accepted no-op applications" reportsNoOp
      , testCase "retries banned rules at a fixed point" retriesBannedRules
      , testCase "rejects invalid projection graphs" rejectsInvalid
      , testCase "empty projections preserve ordinary behavior" ordinaryParity
      ]

transitive :: IO ()
transitive = do
    let ((definition, inner, outer, root, hit, applied), graph) = egraph $ do
          x <- add $ Node $ Value "x"
          definition' <- add $ Node $ Wrap x
          inner' <- add $ Node $ Ref "inner"
          outer' <- add $ Node $ Ref "outer"
          root' <- add $ Node $ Use outer'
          hit' <- add $ Node $ Value "hit"
          applied' <-
              runProjected
                [Projection inner' definition', Projection outer' inner']
                [pat (Use (pat (Wrap "x"))) := pat (Value "hit")]
          pure (definition', inner', outer', root', hit', applied')

    find root graph @?= find hit graph
    assertBool "application root was not reported" $ wasAppliedAt graph applied root
    assertSeparate "inner anchor merged with definition" graph inner definition
    assertSeparate "outer anchor merged with inner anchor" graph outer inner

recanonicalizes :: IO ()
recanonicalizes = do
    let ((definition, anchor, root, hit), graph) = egraph $ do
          x <- add $ Node $ Value "x"
          definition' <- add $ Node $ Wrap x
          anchor' <- add $ Node $ Ref "anchor"
          projection <- pure $ Projection anchor' definition'
          anchorPeer <- add $ Node $ Ref "anchor-peer"
          definitionPeer <- add $ Node $ Value "definition-peer"
          _ <- merge anchorPeer anchor'
          _ <- merge definitionPeer definition'
          root' <- add $ Node $ Use anchor'
          hit' <- add $ Node $ Value "hit"
          _ <- runProjected [projection]
                [pat (Use (pat (Wrap "x"))) := pat (Value "hit")]
          pure (definition', anchor', root', hit')

    find root graph @?= find hit graph
    assertSeparate "anchor merged with definition" graph anchor definition

protectsMatchRoots :: IO ()
protectsMatchRoots = do
    let ((definition, anchor, hit), graph) = egraph $ do
          x <- add $ Node $ Value "x"
          definition' <- add $ Node $ Wrap x
          anchor' <- add $ Node $ Ref "anchor"
          hit' <- add $ Node $ Value "hit"
          _ <- runProjected [Projection anchor' definition']
                [pat (Wrap "x") := pat (Value "hit")]
          pure (definition', anchor', hit')

    find definition graph @?= find hit graph
    assertSeparate "rewrite ran at the protected anchor" graph anchor hit

projectedCondition :: IO ()
projectedCondition = do
    let ((anchor, definition, root, applied), graph) = egraph $ do
          definition' <- add $ Node $ Value "shape"
          inner <- add $ Node $ Ref "inner"
          anchor' <- add $ Node $ Ref "bound"
          root' <- add $ Node $ Use anchor'
          applied' <- runProjected
            [Projection inner definition', Projection anchor' inner]
            [ (pat (Use "bound") := pat (Result "bound"))
                :| hasAnalysis "bound" "shape"
            ]
          pure (anchor', definition', root', applied')

    assertBool "conditioned application was not reported" $
      wasAppliedAt graph applied root
    assertSeparate "anchor merged with definition" graph anchor definition
    assertBool "RHS did not preserve the matched anchor" $
      Node (Result $ find anchor graph) `S.member` nodesAt root graph
    assertBool "RHS used the projected definition" $
      Node (Result $ find definition graph) `S.notMember` nodesAt root graph
  where
    hasAnalysis name expected vars subst graph =
        graph ^. _class classId . _data == Just expected
      where
        classId = findSubst (findVarName vars name) subst

rejectedCondition :: IO ()
rejectedCondition = do
    let ((root, applied), graph) = egraph $ do
          definition <- add $ Node $ Value "shape"
          anchor <- add $ Node $ Ref "bound"
          root' <- add $ Node $ Use anchor
          applied' <- runProjected [Projection anchor definition]
            [ (pat (Use "bound") := pat (Result "bound"))
                :| (\_ _ _ -> False)
            ]
          pure (root', applied')

    assertBool "condition-rejected match was reported" $
      not $ wasAppliedAt graph applied root

protectedRhs :: IO ()
protectedRhs = do
    let (root, graph) = egraph $ do
          definition <- add $ Node $ Value "x"
          anchor <- add $ Node $ Ref "anchor"
          root' <- add $ Node $ Use anchor
          _ <- runProjected [Projection anchor definition]
                [pat (Use "bound") := "bound"]
          pure root'
    assertError "a rewrite returned a protected anchor" $ find root graph

reportsNoOp :: IO ()
reportsNoOp = do
    let ((root, applied), graph) = egraph $ do
          value <- add $ Node $ Value "x"
          root' <- add $ Node $ Use value
          applied' <- runProjected []
            [pat (Use "x") := pat (Use "x")]
          pure (root', applied')
    assertBool "accepted no-op was not reported" $ wasAppliedAt graph applied root

retriesBannedRules :: IO ()
retriesBannedRules = do
    let a = Fix $ Value "a"
        b = Fix $ Value "b"
        c = Fix $ Value "c"
        d = Fix $ Value "d"
        expression = Fix $ Pair (Fix $ Pair (Fix $ Pair a b) c) d
        expected = Fix $ Pair a (Fix $ Pair b (Fix $ Pair c d))
        (root, graph) = egraph program
        program :: EGraphM (Maybe String) Term ClassId
        program = do
          root' <- represent expression
          _ <- runEqualitySaturationWithProjections
                []
                (BackoffScheduler 1 30)
                [ pat (Pair (pat $ Pair "x" "y") "z")
                    := pat (Pair "x" (pat $ Pair "y" "z"))
                ]
          pure root'
        rightAssociatedCost :: Term Integer -> Integer
        rightAssociatedCost = \case
          Pair left right -> 2 * left + right + 1
          _ -> 1

    extractBest graph rightAssociatedCost root @?= expected

rejectsInvalid :: IO ()
rejectsInvalid = do
    let (selfRoot, selfGraph) = egraph $ do
          anchor <- add $ Node $ Ref "self"
          _ <- runProjected [Projection anchor anchor] []
          pure anchor
    assertError "anchor merged with its definition" $ find selfRoot selfGraph

    let (cycleRoot, cycleGraph) = egraph $ do
          left <- add $ Node $ Ref "left"
          right <- add $ Node $ Ref "right"
          _ <- runProjected [Projection left right, Projection right left] []
          pure left
    assertError "projection cycle" $ find cycleRoot cycleGraph

ordinaryParity :: IO ()
ordinaryParity = do
    let (ordinaryRoot, ordinaryGraph) = plainGraph $ \rules ->
          runEqualitySaturation defaultBackoffScheduler rules
        (projectedRoot, projectedGraph) = plainGraph $ \rules -> do
          _ <- runProjected [] rules
          pure ()
        expected = Fix $ Result $ Fix $ Value "x"

    extractBest ordinaryGraph depthCost ordinaryRoot @?= expected
    extractBest projectedGraph depthCost projectedRoot @?= expected
    IM.size (classes projectedGraph) @?= IM.size (classes ordinaryGraph)
    sizeNM (memo projectedGraph) @?= sizeNM (memo ordinaryGraph)

plainGraph
    :: ([Rewrite (Maybe String) Term] -> EGraphM (Maybe String) Term ())
    -> (ClassId, EGraph (Maybe String) Term)
plainGraph runner = egraph $ do
    x <- add $ Node $ Value "x"
    wrapped <- add $ Node $ Wrap x
    root <- add $ Node $ Use wrapped
    rebuild
    runner [pat (Use (pat (Wrap "x"))) := pat (Result "x")]
    pure root

assertError :: String -> ClassId -> IO ()
assertError expected value = do
    result <- try (evaluate value) :: IO (Either SomeException ClassId)
    case result of
      Left exception ->
          assertBool
            ("unexpected exception: " <> displayException exception)
            (expected `isInfixOf` displayException exception)
      Right _ -> assertFailure $ "expected exception containing " <> show expected
