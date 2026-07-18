{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Projected (tests) where

import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Control.Monad (guard)
import Data.Equality.Analysis (Analysis (..))
import Data.Equality.Extraction (depthCost, extractBest)
import Data.Equality.Graph
    ( ClassId
    , EGraph
    , ENode (..)
    , find
    , sizeNM
    )
import Data.Equality.Graph.Internal (classes, memo)
import Data.Equality.Graph.Lens (_class, _nodes, (^.))
import Data.Equality.Graph.Monad
    ( EGraphM
    , add
    , egraph
    , merge
    , rebuild
    )
import Data.Equality.Matching (pat)
import Data.Equality.Saturation
    ( Rewrite (..)
    , fresh
    , lookupSubtree
    , matchAnalysis
    , runEqualitySaturation
    , runEqualitySaturationWithProjection
    )
import Data.Equality.Saturation.Projection
    ( Projection (..)
    , ProjectionView (..)
    )
import Data.Equality.Saturation.Scheduler (defaultBackoffScheduler)
import Data.Equality.Utils (Fix (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@?=), assertBool, testCase)

data Term a
    = Value String
    | Ref String
    | BindingRef String a
    | Alias a
    | Wrap a
    | Use a
    | Result a
    | Pair a a
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Analysis (Maybe String) Term where
    makeA = \case
        Value value -> Just value
        Ref _ -> Nothing
        BindingRef _ child -> child
        Alias child -> child
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

projectionView :: ProjectionView String Term
projectionView =
    ProjectionView
        { classifyProjection = \case
            BindingRef key child ->
                Just (ProtectedProjection key child)
            Alias child ->
                Just (TransparentProjection child)
            _ -> Nothing
        , reifyAlias = Alias
        }

emptyProjectionView :: ProjectionView () Term
emptyProjectionView =
    ProjectionView
        { classifyProjection = const Nothing
        , reifyAlias = Alias
        }

type Runner = [Rewrite () Term] -> EGraphM () Term ()

runProjected :: Runner
runProjected =
    runEqualitySaturationWithProjection
        projectionView
        defaultBackoffScheduler

-- Give the projection node an ordinary peer so the protected class remains a
-- materialized value in the physical e-graph.
addProtected
    :: Analysis analysis Term
    => String
    -> ClassId
    -> EGraphM analysis Term ClassId
addProtected key definition = do
    ref <- add (Node (Ref key))
    projection <- add (Node (BindingRef key definition))
    merge ref projection

nodesAt :: ClassId -> EGraph () Term -> S.Set (ENode Term)
nodesAt classId graph = graph ^. _class (find classId graph) . _nodes

assertSeparate
    :: String
    -> EGraph () Term
    -> ClassId
    -> ClassId
    -> IO ()
assertSeparate message graph left right =
    assertBool message (find left graph /= find right graph)

tests :: TestTree
tests =
    testGroup
        "Projected saturation"
        [ testCase "follows transitive projections" transitiveProjection
        , testCase
            "allows recanonicalized projection nodes"
            allowsRecanonicalizedProjectionNodes
        , testCase
            "preserves a captured projected subtree"
            preservesCapturedSubtree
        , testCase "aliases a protected RHS" aliasesProtectedRhs
        , testCase
            "aliases a fresh RHS which hash-conses to a protected class"
            aliasesHashConsedProtectedRhs
        , testCase
            "exposes projected analysis to computed rewrites"
            exposesProjectedAnalysis
        , testCase
            "keeps distinct equal-definition anchors nonlinear"
            rejectsDistinctAnchors
        , testCase "empty view agrees with the default runner" emptyViewMatchesDefault
        ]

allowsRecanonicalizedProjectionNodes :: IO ()
allowsRecanonicalizedProjectionNodes = do
    let ((definition, anchor, hit), graph) = egraph $ do
            value <- add (Node (Value "x"))
            definition' <- add (Node (Pair value value))
            anchor' <- addProtected "anchor" definition'
            hit' <- add (Node (Value "hit"))
            rebuild
            runProjected
                [ pat (Pair "x" "x") := pat (Value "hit")
                ]
            pure (definition', anchor', hit')

    find definition graph @?= find hit graph
    assertSeparate "anchor merged with its definition" graph anchor definition

transitiveProjection :: IO ()
transitiveProjection = do
    let ((definition, inner, outer, root, hit), graph) = egraph $ do
            x <- add (Node (Value "x"))
            definition' <- add (Node (Wrap x))
            inner' <- addProtected "inner" definition'
            outer' <- addProtected "outer" inner'
            root' <- add (Node (Use outer'))
            hit' <- add (Node (Value "hit"))
            rebuild
            runProjected
                [ pat (Use (pat (Wrap "x"))) := pat (Value "hit")
                ]
            pure (definition', inner', outer', root', hit')

    find root graph @?= find hit graph
    assertSeparate "inner anchor merged with its definition" graph inner definition
    assertSeparate "outer anchor merged with the inner anchor" graph outer inner
    assertSeparate
        "outer anchor merged with the definition"
        graph
        outer
        definition

preservesCapturedSubtree :: IO ()
preservesCapturedSubtree = do
    let ((definition, anchor, root), graph) = egraph $ do
            x <- add (Node (Value "x"))
            definition' <- add (Node (Wrap x))
            anchor' <- addProtected "anchor" definition'
            root' <- add (Node (Use anchor'))
            rebuild
            runProjected
                [ pat (Use (pat (Wrap "x")))
                    := pat (Result (pat (Wrap "x")))
                ]
            pure (definition', anchor', root')
        rootNodes = nodesAt root graph

    assertSeparate "anchor merged with its definition" graph anchor definition
    assertBool
        "rewrite did not reuse the captured anchor"
        (Node (Result (find anchor graph)) `S.member` rootNodes)
    assertBool
        "rewrite reconstructed the hidden definition"
        (Node (Result (find definition graph)) `S.notMember` rootNodes)

aliasesProtectedRhs :: IO ()
aliasesProtectedRhs = do
    let ((definition, anchor, root, seen), graph) = egraph $ do
            x <- add (Node (Value "x"))
            definition' <- add (Node (Wrap x))
            anchor' <- addProtected "anchor" definition'
            root' <- add (Node (Use anchor'))
            seen' <- add (Node (Value "seen"))
            rebuild
            runProjected
                [ pat (Use (pat (Wrap "x"))) := pat (Wrap "x")
                , pat (Wrap "x") := pat (Value "seen")
                ]
            pure (definition', anchor', root', seen')

    assertSeparate "anchor merged with its definition" graph anchor definition
    assertSeparate "rewrite merged its root into the anchor" graph root anchor
    find root graph @?= find seen graph
    assertBool
        "rewrite did not materialize an alias to the protected anchor"
        ( Node (Alias (find anchor graph))
            `S.member` nodesAt root graph
        )

aliasesHashConsedProtectedRhs :: IO ()
aliasesHashConsedProtectedRhs = do
    let ((anchor, root), graph) = egraph $ do
            value <- add (Node (Value "x"))
            definition <- add (Node (Wrap value))
            anchor' <- addProtected "anchor" definition
            root' <- add (Node (Use anchor'))
            rebuild
            runProjected
                [ pat (Use (pat (Wrap "x"))) := pat (Ref "anchor")
                ]
            pure (anchor', root')

    assertSeparate "rewrite merged its root into the anchor" graph root anchor
    assertBool
        "rewrite did not alias the hash-consed protected result"
        ( Node (Alias (find anchor graph))
            `S.member` nodesAt root graph
        )

exposesProjectedAnalysis :: IO ()
exposesProjectedAnalysis = do
    let ((root, hit), graph) = egraph program
        program :: EGraphM (Maybe String) Term (ClassId, ClassId)
        program = do
            value <- add (Node (Value "x"))
            definition <- add (Node (Wrap value))
            anchor <- addProtected "anchor" definition
            root' <- add (Node (Use anchor))
            hit' <- add (Node (Value "hit"))
            rebuild
            runEqualitySaturationWithProjection
                projectionView
                defaultBackoffScheduler
                [ pat (Use (pat (Wrap "x"))) :=> \context -> do
                    wrapped <- lookupSubtree (pat (Wrap "x")) context
                    guard $ matchAnalysis wrapped == Just "x"
                    pure $ fresh (Value "hit")
                ]
            pure (root', hit')

    find root graph @?= find hit graph

rejectsDistinctAnchors :: IO ()
rejectsDistinctAnchors = do
    let ((definition, left, right, root, collapsed), graph) = egraph $ do
            x <- add (Node (Value "x"))
            definition' <- add (Node (Wrap x))
            left' <- addProtected "left" definition'
            right' <- addProtected "right" definition'
            root' <- add (Node (Pair left' right'))
            collapsed' <- add (Node (Value "collapsed"))
            rebuild
            runProjected
                [ pat
                    ( Pair
                        (pat (Wrap "x"))
                        (pat (Wrap "x"))
                    )
                    := pat (Value "collapsed")
                ]
            pure (definition', left', right', root', collapsed')

    assertSeparate
        "distinct anchors were collapsed by a nonlinear match"
        graph
        root
        collapsed
    assertSeparate "distinct anchors merged with each other" graph left right
    assertSeparate "left anchor merged with its definition" graph left definition
    assertSeparate "right anchor merged with its definition" graph right definition

emptyViewMatchesDefault :: IO ()
emptyViewMatchesDefault = do
    let (ordinaryRoot, ordinaryGraph) =
            plainGraph (runEqualitySaturation defaultBackoffScheduler)
        (projectedRoot, projectedGraph) =
            plainGraph
                ( runEqualitySaturationWithProjection
                    emptyProjectionView
                    defaultBackoffScheduler
                )
        expected = Fix (Result (Fix (Value "x")))

    extractBest ordinaryGraph depthCost ordinaryRoot @?= expected
    extractBest projectedGraph depthCost projectedRoot @?= expected
    IM.size (classes projectedGraph) @?= IM.size (classes ordinaryGraph)
    sizeNM (memo projectedGraph) @?= sizeNM (memo ordinaryGraph)

plainGraph :: Runner -> (ClassId, EGraph () Term)
plainGraph runner = egraph $ do
    x <- add (Node (Value "x"))
    wrapped <- add (Node (Wrap x))
    root <- add (Node (Use wrapped))
    rebuild
    runner
        [ pat (Use (pat (Wrap "x"))) := pat (Result "x")
        ]
    pure root
