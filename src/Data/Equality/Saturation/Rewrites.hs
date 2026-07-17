{-# LANGUAGE QuantifiedConstraints, RankNTypes, UnicodeSyntax #-}
{-|

Definition of 'Rewrite' and 'RewriteCondition' used to define rewrite rules.

Rewrite rules are applied to all represented expressions in an e-graph every
iteration of equality saturation.

-}
module Data.Equality.Saturation.Rewrites
    ( Rewrite(..)
    , RewriteCondition
    , RewriteFun
    , Rhs
    , fresh
    , reuse
    , MatchContext
    , MatchInfo
    , matchRoot
    , lookupBinding
    , lookupSubtree
    , matchAnalysis
    , matchNodes
    ) where

import Data.Equality.Graph
import Data.Equality.Matching
import Data.Equality.Matching.Database
import qualified Data.Map.Lazy as M
import qualified Data.Set as S

import Data.Equality.Saturation.Rewrites.Internal
    ( MatchContext
    , MatchInfo
    , Rhs
    )
import qualified Data.Equality.Saturation.Rewrites.Internal as RI

-- | A rewrite rule that might have conditions for being applied
--
-- === __Example__
-- @
-- rewrites :: [Rewrite Expr] -- from Sym.hs
-- rewrites =
--     [ "x"+"y" := "y"+"x"
--     , "x"*("y"*"z") := ("x"*"y")*"z"
--
--     , "x"*0 := 0
--     , "x"*1 := "x"
--
--     , "a"-"a" := 1 -- cancel sub
--     , "a"/"a" := 1 :| is_not_zero "a"
--     ]
-- @
--
-- See the definition of @is_not_zero@ in the documentation for
-- 'RewriteCondition'
data Rewrite anl lang
    = !(Pattern lang) := !(Pattern lang) -- ^ Ordinary pattern rewrite
    | !(Pattern lang) :=> RewriteFun anl lang -- ^ Computed rewrite
    | !(Rewrite anl lang) :| !(RewriteCondition anl lang) -- ^ Conditional rewrite
infix 3 :=
infix 3 :=>
infixl 2 :|

-- | A rewrite condition. With a substitution from bound variables in the
-- pattern to e-classes and with the e-graph, return 'True' if the condition is
-- satisfied
--
-- A condition must be monotone: once it accepts a match, learning more
-- analysis or equality information must not cause it to reject that match.
--
-- === Example
-- @
-- is_not_zero :: String -> RewriteCondition Expr
-- is_not_zero v subst egr =
--    case lookup v subst of
--      Just class_id ->
--          egr^._class class_id._data /= Just 0
-- @
type RewriteCondition anl lang = VarsState -> Subst -> EGraph anl lang -> Bool

-- | Compute a declarative right-hand side from one match, or return 'Nothing'
-- to decline the match.
--
-- The scope parameter prevents references obtained from one invocation from
-- escaping or being combined with references from another match.
--
-- Like ordinary and conditional rewrites, a computed rewrite must only return
-- a right-hand side semantically equivalent to its left-hand side.  It must
-- also be monotone in the information exposed by 'MatchInfo': learning more
-- analysis facts or visible e-nodes may enable a previously declined match,
-- but must not invalidate a result which was already returned.  Results must
-- be deterministic and independent of incidental set traversal order.
type RewriteFun analysis lang =
    forall scope.
    MatchContext scope analysis lang -> Maybe (Rhs scope lang)

-- | Construct a fresh language node in a computed right-hand side.
fresh :: lang (Rhs scope lang) -> Rhs scope lang
fresh = RI.Fresh

-- | Reuse the e-class represented by a match.
reuse :: MatchInfo scope analysis lang -> Rhs scope lang
reuse = RI.Existing . RI.matchInfoRef

-- | Information about the e-class at which the left-hand side matched.
matchRoot :: MatchContext scope analysis lang -> MatchInfo scope analysis lang
matchRoot = RI.contextRoot

-- | Look up a named pattern variable.
lookupBinding
    :: String
    -> MatchContext scope analysis lang
    -> Maybe (MatchInfo scope analysis lang)
lookupBinding name = M.lookup name . RI.contextBindings

-- | Look up the exact boundary captured for a non-variable left-hand-side
-- subpattern.
lookupSubtree
    :: Pattern lang
    -> MatchContext scope analysis lang
    -> Maybe (MatchInfo scope analysis lang)
lookupSubtree pattern' = ($ pattern') . RI.contextLookupSubtree

-- | Analysis data for the matched e-class.
matchAnalysis :: MatchInfo scope analysis lang -> analysis
matchAnalysis = RI.matchInfoAnalysis

-- | E-nodes visible at the matched boundary.  Under projected matching, these
-- include nodes exposed through the projection.
matchNodes :: MatchInfo scope analysis lang -> S.Set (ENode lang)
matchNodes = RI.matchInfoNodes


instance (∀ a. Show a => Show (lang a)) => Show (Rewrite anl lang) where
  show (rw :| _) = show rw <> " :| <cond>"
  show (lhs := rhs) = show lhs <> " := " <> show rhs
  show (lhs :=> _) = show lhs <> " :=> <fun>"
