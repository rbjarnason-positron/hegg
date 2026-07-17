{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}

{-|
Description: Directed views of e-classes used during equality saturation

An e-graph represents equality, but programs with named or materialized values
also have directed boundaries which must not be turned into equality.  A
'ProjectionView' lets the saturation runner look through such boundaries while
matching without merging the boundary e-class with the projected value.

Projection nodes remain ordinary language nodes in the physical e-graph.  In
particular, their 'Data.Equality.Analysis.Analysis' case should propagate any
semantic information needed by rewrite guards.  The projected matching database
only changes what patterns can observe; it does not maintain a second e-graph.
-}
module Data.Equality.Saturation.Projection
    ( Projection(..)
    , ProjectionView(..)
    ) where

-- | How a projection node exposes its child to the matcher.
data Projection key child
    = ProtectedProjection !key !child
      -- ^ A stable materialization boundary.  Rewrites may observe through it,
      -- but may neither run at its root nor merge another class directly into
      -- it.  The key must uniquely identify the boundary within a run.
    | TransparentProjection !child
      -- ^ A directed alias created by the runner.  It is transparent to
      -- matching and may itself be rewritten.
    deriving (Eq, Ord, Show, Functor)

-- | Language-specific projection operations shared by every rewrite in a run.
--
-- Projection nodes are omitted from the matching database and replaced by the
-- ordinary nodes visible through their child.  This is transitive, so a
-- protected projection may point at another protected projection.
--
-- The view must satisfy:
--
-- @
-- classifyProjection (reifyAlias child)
--   == Just (TransparentProjection child)
-- @
--
-- Each 'ProtectedProjection' key must identify one distinct physical e-class.
-- Both projection forms should propagate their child's semantic analysis.
-- Protected nodes should be excluded from extraction, while aliases should be
-- cost-transparent and removed from the extracted result.
--
-- The runner prevents rewrites from merging a protected class.  Since
-- 'Data.Equality.Analysis.Analysis.modifyA' may mutate an e-graph arbitrarily,
-- an analysis used with projected saturation must uphold the same restriction.
data ProjectionView key lang = ProjectionView
    { classifyProjection
        :: forall child. lang child -> Maybe (Projection key child)
      -- ^ Recognize a projection node and its projected child.
    , reifyAlias
        :: forall child. child -> lang child
      -- ^ Construct a 'TransparentProjection'.  The runner uses this when a
      -- rewrite result denotes a protected boundary.
    }
