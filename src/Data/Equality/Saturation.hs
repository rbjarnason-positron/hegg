{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE MonoLocalBinds #-}
{-|
  Given an input program 𝑝, equality saturation constructs an e-graph 𝐸 that
  represents a large set of programs equivalent to 𝑝, and then extracts the
  “best” program from 𝐸.

  The e-graph is grown by repeatedly applying pattern-based rewrites.
  Critically, these rewrites only add information to the e-graph, eliminating
  the need for careful ordering.

  Upon reaching a fixed point (saturation), 𝐸 will represent all equivalent
  ways to express 𝑝 with respect to the given rewrites.

  After saturation (or timeout), a final extraction procedure analyzes 𝐸 and
  selects the optimal program according to a user-provided cost function.
 -}
module Data.Equality.Saturation
    (
      -- * Equality saturation
      equalitySaturation, equalitySaturation', runEqualitySaturation
    , runEqualitySaturationWithProjection

      -- * Re-exports for equality saturation

      -- ** Writing rewrite rules
    , Rewrite(..), RewriteCondition, RewriteFun
    , Rhs, fresh, reuse
    , MatchContext, MatchInfo
    , matchRoot, lookupBinding, lookupSubtree, matchAnalysis, matchNodes

      -- ** Projected matching
    , Projection(..), ProjectionView(..)

      -- ** Writing cost functions
      --
      -- | 'CostFunction' re-exported from 'Data.Equality.Extraction' since they are required to do equality saturation
    , CostFunction --, depthCost

      -- ** Writing expressions
      -- 
      -- | Expressions must be written in their fixed-point form, since the
      -- 'Language' must be given in its base functor form
    , Fix(..), cata

    ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Lazy as M
import qualified Data.Set as S

import Control.Monad

import Data.Equality.Utils
import Data.Equality.Graph.Nodes
import Data.Equality.Graph.Lens
import Data.Equality.Graph.Internal (EGraph(classes))
import qualified Data.Equality.Graph as G
import Data.Equality.Graph.Monad
import Data.Equality.Language
import Data.Equality.Analysis
import Data.Equality.Graph.Classes
import Data.Equality.Matching
import Data.Equality.Matching.Internal
    ( CaptureSubst
    , CompiledPattern
    , captureMatch
    , compilePattern
    , compiledQuery
    , compiledVarsState
    , lookupCapture
    )
import Data.Equality.Matching.Database
import Data.Equality.Extraction

import Data.Equality.Saturation.Rewrites
import qualified Data.Equality.Saturation.Rewrites.Internal as RI
import Data.Equality.Saturation.Scheduler
import Data.Equality.Saturation.Projection
import Data.Equality.Saturation.Projection.Internal

data RhsPlan lang
    = ExistingClass !ClassId
    | FreshNode !(lang (RhsPlan lang))

data PlannedRewrite analysis lang = PlannedRewrite
    !Match
    (RhsPlan lang)
    !(Rewrite analysis lang)
    !VarsState
    !Subst

data ProjectionOps lang = ProjectionOps
    { makeAliasNode :: ClassId -> lang ClassId
    , classifyRhsProjection :: lang ClassId -> Maybe (Projection () ClassId)
    }

-- | Equality saturation with defaults
equalitySaturation :: forall a l cost
                    . (Analysis a l, Language l, Ord cost)
                   => Fix l               -- ^ Expression to run equality saturation on
                   -> [Rewrite a l]         -- ^ List of rewrite rules
                   -> CostFunction l cost -- ^ Cost function to extract the best equivalent representation
                   -> (Fix l, EGraph a l)   -- ^ Best equivalent expression and resulting e-graph
equalitySaturation = equalitySaturation' defaultBackoffScheduler


-- | Run equality saturation on an expression given a list of rewrites, and
-- extract the best equivalent expression according to the given cost function
--
-- This variant takes all arguments instead of using defaults
equalitySaturation' :: forall a l schd cost
                    . (Analysis a l, Language l, Scheduler l schd, Ord cost)
                    => schd                -- ^ Scheduler to use
                    -> Fix l               -- ^ Expression to run equality saturation on
                    -> [Rewrite a l]       -- ^ List of rewrite rules
                    -> CostFunction l cost -- ^ Cost function to extract the best equivalent representation
                    -> (Fix l, EGraph a l)   -- ^ Best equivalent expression and resulting e-graph
equalitySaturation' schd expr rewrites cost = egraph $ do

    -- Represent expression as an e-graph
    origClass <- represent expr

    -- Run equality saturation (by applying non-destructively all rewrites)
    runEqualitySaturation schd rewrites

    -- Extract best solution from the e-class of the original expression
    gets $ \g -> extractBest g cost origClass
{-# INLINABLE equalitySaturation' #-}


-- | Run equality saturation on an e-graph by non-destructively applying all
-- given rewrite rules until saturation (using the given 'Scheduler')
runEqualitySaturation :: forall a l schd
                       . (Analysis a l, Language l, Scheduler l schd)
                      => schd                -- ^ Scheduler to use
                      -> [Rewrite a l]       -- ^ List of rewrite rules
                      -> EGraphM a l ()
runEqualitySaturation =
    runEqualitySaturationUsing ordinaryMatchingView Nothing
{-# INLINEABLE runEqualitySaturation #-}

-- | Run equality saturation using one directed projection view for all rules.
-- The e-graph is rebuilt before the first projected database is constructed.
runEqualitySaturationWithProjection
    :: forall key analysis lang scheduler
     . ( Ord key
       , Analysis analysis lang
       , Language lang
       , Scheduler lang scheduler
       )
    => ProjectionView key lang
    -> scheduler
    -> [Rewrite analysis lang]
    -> EGraphM analysis lang ()
runEqualitySaturationWithProjection projectionView scheduler rewrites = do
    rebuild
    runEqualitySaturationUsing
      (projectedMatchingView projectionView)
      (Just projectionOps)
      scheduler
      rewrites
  where
    projectionOps = ProjectionOps
      { makeAliasNode = reifyAlias projectionView
      , classifyRhsProjection = \node ->
          case classifyProjection projectionView node of
            Nothing -> Nothing
            Just (ProtectedProjection _ child) ->
                Just $ ProtectedProjection () child
            Just (TransparentProjection child) ->
                Just $ TransparentProjection child
      }
{-# INLINEABLE runEqualitySaturationWithProjection #-}

runEqualitySaturationUsing
    :: forall analysis lang scheduler
     . ( Analysis analysis lang
       , Language lang
       , Scheduler lang scheduler
       )
    => (EGraph analysis lang -> MatchingView lang)
    -> Maybe (ProjectionOps lang)
    -> scheduler
    -> [Rewrite analysis lang]
    -> EGraphM analysis lang ()
runEqualitySaturationUsing buildView projectionOps scheduler rewrites =
    go 0 mempty
  where
    compiledRewrites =
        [ (rewrite, compilePattern $ rewriteLhs rewrite)
        | rewrite <- rewrites
        ]

    go :: Int -> IM.IntMap (Stat lang scheduler) -> EGraphM analysis lang ()
    go 30 _ = pure ()
    go iteration stats = do
        graph <- get
        let beforeMemo = graph ^. _memo
            beforeClasses = classes graph
            matchingView = buildView graph
            (!matches, newStats) =
                mconcat $
                  map
                    (matchRewrite graph matchingView iteration stats)
                    (zip [1 ..] compiledRewrites)

        forM_ matches $
          applyPlan projectionOps matchingView
        rebuild

        updated <- get
        validateProtected matchingView updated `seq` pure ()
        let afterMemo = updated ^. _memo
            afterClasses = classes updated
        unless
          ( G.sizeNM afterMemo == G.sizeNM beforeMemo
              && IM.size afterClasses == IM.size beforeClasses
          )
          (go (iteration + 1) newStats)

    matchRewrite
        :: EGraph analysis lang
        -> MatchingView lang
        -> Int
        -> IM.IntMap (Stat lang scheduler)
        -> (Int, (Rewrite analysis lang, CompiledPattern lang))
        -> ( [PlannedRewrite analysis lang]
           , IM.IntMap (Stat lang scheduler)
           )
    matchRewrite graph matchingView iteration stats
                 (rewriteId, (rewrite, compiled)) =
        case IM.lookup rewriteId stats of
          Just stat
            | isBanned @lang @scheduler iteration stat -> ([], stats)
          currentStat ->
            let candidateMatches =
                    filter
                      ( \matched ->
                          IS.notMember
                            (matchClassId matched)
                            (protectedClasses matchingView)
                      )
                      ( ematch
                          (matchingDatabase matchingView)
                          (compiledQuery compiled)
                      )
                capturedMatches =
                    [ (matched, captures)
                    | matched <- candidateMatches
                    , Just captures <- [captureMatch compiled matched]
                    ]
                plannedMatches =
                    [ plan
                    | (matched, captures) <- capturedMatches
                    , Just plan <-
                        [ planMatch
                            graph
                            matchingView
                            rewrite
                            (compiledVarsState compiled)
                            captures
                            matched
                        ]
                    ]
                acceptedMatches =
                    case withoutConditions rewrite of
                      _ := _ -> map fst capturedMatches
                      _ :=> _ ->
                          [ matched
                          | PlannedRewrite matched _ _ _ _ <- plannedMatches
                          ]
                      _ :| _ -> error "matchRewrite: unexpected conditional rewrite"
                updatedStats =
                    updateStats
                      scheduler
                      iteration
                      rewriteId
                      (withoutConditions rewrite)
                      currentStat
                      stats
                      acceptedMatches
             in (plannedMatches, updatedStats)

rewriteLhs :: Rewrite analysis lang -> Pattern lang
rewriteLhs (rewrite :| _) = rewriteLhs rewrite
rewriteLhs (lhs := _) = lhs
rewriteLhs (lhs :=> _) = lhs

planMatch
    :: forall analysis lang
     . (Analysis analysis lang, Language lang)
    => EGraph analysis lang
    -> MatchingView lang
    -> Rewrite analysis lang
    -> VarsState
    -> CaptureSubst lang
    -> Match
    -> Maybe (PlannedRewrite analysis lang)
planMatch graph matchingView rewrite vars captures matched
    = planRewrite makeContext $ withoutConditions rewrite
  where
    subst = matchSubst matched

    makeContext
        :: RI.MatchContext scope analysis lang
    makeContext =
        RI.MatchContext
          { RI.contextRoot = makeInfo graph $ matchClassId matched
          , RI.contextBindings =
              M.map (makeInfo graph . (`findSubst` subst)) (varNames vars)
          , RI.contextLookupSubtree = \pattern' ->
              makeInfo graph <$> lookupCapture pattern' captures
          }

    makeInfo
        :: EGraph analysis lang
        -> ClassId
        -> RI.MatchInfo scope analysis lang
    makeInfo snapshot classId =
        RI.MatchInfo
          { RI.matchInfoRef = RI.MatchRef classId
          , RI.matchInfoAnalysis = snapshot ^. _class canonical . _data
          , RI.matchInfoNodes =
              IM.findWithDefault S.empty canonical $ visibleNodes matchingView
          }
      where
        canonical = G.find classId snapshot

    planRewrite
        :: forall scope
         . RI.MatchContext scope analysis lang
        -> Rewrite analysis lang
        -> Maybe (PlannedRewrite analysis lang)
    planRewrite context' = \case
      _ := rhs ->
          Just $
            PlannedRewrite
              matched
              (lowerRhs $ RI.rhsFromPattern context' rhs)
              rewrite
              vars
              subst
      _ :=> rewriteFunction ->
          -- A callback may rely on its condition when inspecting the snapshot.
          -- The condition is checked again when the plan is applied.
          if conditionsHold rewrite vars subst graph
            then
              (\rhs -> PlannedRewrite matched (lowerRhs rhs) rewrite vars subst)
                <$> rewriteFunction context'
            else Nothing
      _ :| _ -> error "planMatch: unexpected conditional rewrite"

lowerRhs :: Functor lang => RI.Rhs scope lang -> RhsPlan lang
lowerRhs (RI.Existing ref) = ExistingClass $ RI.matchRefClass ref
lowerRhs (RI.Fresh node) = FreshNode $ fmap lowerRhs node

applyPlan
    :: (Analysis analysis lang, Language lang)
    => Maybe (ProjectionOps lang)
    -> MatchingView lang
    -> PlannedRewrite analysis lang
    -> EGraphM analysis lang ()
applyPlan projectionOps matchingView
          (PlannedRewrite matched rhs rewrite vars subst) = do
    graph <- get
    when (conditionsHold rewrite vars subst graph) $ do
      result <- instantiateRhsPlan projectionOps rhs
      current <- get
      let root = G.find (matchClassId matched) current
          result' = G.find result current
          protected =
              canonicalProtected current $ protectedClasses matchingView
      when (IS.member root protected) $
        error "projected saturation: a protected match root was merged"
      case projectionOps of
        Just ops | IS.member result' protected -> do
          let aliasNode = makeAliasNode ops result'
          case classifyRhsProjection ops aliasNode of
            Just (TransparentProjection child) | child == result' -> pure ()
            _ -> error "projected saturation: reifyAlias is not transparent"
          alias <- add $ Node aliasNode
          updated <- get
          when (IS.member (G.find alias updated) protected) $
            error "projected saturation: alias hash-consed to a protected class"
          void $ mergeRewriteResult rewrite root alias
        _ -> void $ mergeRewriteResult rewrite root result'

-- Preserve the leader choice of the original runner.  Variable right-hand
-- sides made the matched binding the leader; constructed terms made the match
-- root the leader.
mergeRewriteResult
    :: (Analysis analysis lang, Language lang)
    => Rewrite analysis lang
    -> ClassId
    -> ClassId
    -> EGraphM analysis lang ClassId
mergeRewriteResult rewrite root result =
    case withoutConditions rewrite of
      _ := VariablePattern _ -> merge result root
      _ -> merge root result

withoutConditions :: Rewrite analysis lang -> Rewrite analysis lang
withoutConditions (rewrite :| _) = withoutConditions rewrite
withoutConditions rewrite = rewrite

conditionsHold
    :: Rewrite analysis lang
    -> VarsState
    -> Subst
    -> EGraph analysis lang
    -> Bool
conditionsHold (rewrite :| condition) vars subst graph =
    condition vars subst graph
      && conditionsHold rewrite vars subst graph
conditionsHold _ _ _ _ = True

instantiateRhsPlan
    :: (Analysis analysis lang, Language lang)
    => Maybe (ProjectionOps lang)
    -> RhsPlan lang
    -> EGraphM analysis lang ClassId
instantiateRhsPlan _ (ExistingClass classId) =
    gets $ G.find classId
instantiateRhsPlan projectionOps (FreshNode node) = do
    node' <- traverse (instantiateRhsPlan projectionOps) node
    case projectionOps >>= (\ops -> classifyRhsProjection ops node') of
      Just (ProtectedProjection _ _) ->
          error "projected saturation: a rewrite constructed a protected projection"
      _ -> add $ Node node'

canonicalProtected :: EGraph analysis lang -> IS.IntSet -> IS.IntSet
canonicalProtected graph =
    IS.fromList . map (`G.find` graph) . IS.toList

-- Check the protected relationships visible in the iteration snapshot.
-- 'Analysis.modifyA' remains responsible for avoiding other protected merges,
-- as required by 'ProjectionView'.
validateProtected :: MatchingView lang -> EGraph analysis lang -> ()
validateProtected matchingView graph
  | length edges /= IS.size roots =
      error "projected saturation: protected projection classes were merged"
  | any (uncurry (==)) canonicalEdges =
      error "projected saturation: protected projection merged with its child"
  | otherwise = ()
  where
    edges = protectedEdges matchingView
    canonicalEdges =
        [(G.find root graph, G.find child graph) | (root, child) <- edges]
    roots = IS.fromList $ map fst canonicalEdges
