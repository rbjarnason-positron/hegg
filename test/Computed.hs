{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Computed (computedTests) where

import Data.Equality.Analysis (Analysis (..))
import Data.Equality.Extraction (depthCost)
import Data.Equality.Graph (ENode (..), find)
import Data.Equality.Graph.Monad (add, egraph, rebuild)
import Data.Equality.Matching (Pattern, pat)
import Data.Equality.Saturation
    ( Fix (..)
    , equalitySaturation
    , equalitySaturation'
    , runEqualitySaturation
    )
import Data.Equality.Saturation.Rewrites
import Data.Equality.Saturation.Scheduler
    ( BackoffScheduler (..)
    , defaultBackoffScheduler
    )
import qualified Data.Set as S
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit ((@?=), testCase)

data Lang a
  = Add a a
  | Lit Int
  | Symbol String
  | Observe a
  | Goal
  deriving (Functor, Foldable, Traversable, Eq, Ord, Show)

instance Analysis (Maybe Int) Lang where
  makeA = \case
    Add left right -> (+) <$> left <*> right
    Lit n -> Just n
    Symbol _ -> Nothing
    Observe value -> value
    Goal -> Nothing

  joinA Nothing right = right
  joinA left Nothing = left
  joinA left@(Just n) (Just m)
    | n == m = left
    | otherwise = error "merged e-classes have different constant values"

xPat, yPat :: Pattern Lang
xPat = "x"
yPat = "y"

foldAdd :: Rewrite (Maybe Int) Lang
foldAdd = pat (Add xPat yPat) :=> \ctx -> do
  xValue <- matchAnalysis =<< lookupBinding "x" ctx
  yValue <- matchAnalysis =<< lookupBinding "y" ctx
  pure (fresh (Lit (xValue + yValue)))

removeRightZero :: Rewrite (Maybe Int) Lang
removeRightZero = pat (Add xPat (pat (Lit 0))) :=> \ctx ->
  reuse <$> lookupBinding "x" ctx

removeRightZeroStatic :: Rewrite (Maybe Int) Lang
removeRightZeroStatic = pat (Add xPat (pat (Lit 0))) := xPat

waitForLiteral :: Rewrite (Maybe Int) Lang
waitForLiteral = pat (Observe xPat) :=> \ctx -> do
  matched <- lookupBinding "x" ctx
  let hasZero = Node (Lit 0) `S.member` matchNodes matched
  if hasZero then pure (fresh Goal) else Nothing

run :: [Rewrite (Maybe Int) Lang] -> Fix Lang -> Fix Lang
run rules expression = fst (equalitySaturation expression rules depthCost)

computedTests :: TestTree
computedTests =
  testGroup
    "Computed rewrites"
    [ testCase "build a fresh constant from matched analyses" $
        run [foldAdd] (Fix (Add (Fix (Lit 1)) (Fix (Lit 2))))
          @?= Fix (Lit 3)
    , testCase "skip when a matched analysis is unavailable" $
        let expression = Fix (Add (Fix (Symbol "x")) (Fix (Lit 2)))
         in run [foldAdd] expression @?= expression
    , testCase "check a condition before invoking the RHS callback" $
        let expression = Fix (Symbol "x")
            rewrite =
              pat (Symbol "x") :=> (\_ -> error "callback was invoked")
                :| (\_ _ _ -> False)
         in run [rewrite] expression @?= expression
    , testCase "do not instantiate a rejected static RHS" $
        let expression = Fix (Symbol "x")
            rewrite =
              pat (Symbol "x") := yPat :| (\_ _ _ -> False)
         in run [rewrite] expression @?= expression
    , testCase "reuse a matched e-class" $
        run [removeRightZero] (Fix (Add (Fix (Symbol "x")) (Fix (Lit 0))))
          @?= Fix (Symbol "x")
    , testCase "preserve variable RHS leader choice" $
        let ((symbol, root), graph) = egraph $ do
              symbol' <- add (Node (Symbol "x"))
              zero <- add (Node (Lit 0))
              root' <- add (Node (Add symbol' zero))
              _ <- add (Node (Observe root'))
              rebuild
              runEqualitySaturation
                defaultBackoffScheduler
                [removeRightZeroStatic]
              pure (symbol', root')
         in find root graph @?= symbol
    , testCase "declined matches do not trigger scheduler backoff" $
        let expression = Fix (Observe (Fix (Symbol "x")))
            rules =
              [ waitForLiteral
              , pat (Symbol "x") := pat (Lit 0)
              ]
            scheduler = BackoffScheduler 0 10
         in fst (equalitySaturation' scheduler expression rules depthCost)
              @?= Fix Goal
    ]
