import ExistentialRules.ChaseSequence.ChaseBranch
import ExistentialRules.Models.Basic
import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.Basic
import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms
import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Universality

import ExistentialRules.ChaseSequence.Deterministic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

structure CoreChaseNode (rules : RuleSet sig) where
  fs : FactSet sig
  core : FactSet sig
  is_core : core.isWeakCore
  core_sse : core.homSubset fs
  origin : Option ((trg : RTrigger (RestrictedObsolescence sig).toLaxObsolescenceCondition rules) × Fin trg.val.mapped_head.length)
  fs_contains_origin_result : ∀ o ∈ origin, o.fst.val.mapped_head[o.snd.val].toSet ⊆ fs

namespace CoreChaseNode

def origin_result {rules : RuleSet sig} (node : CoreChaseNode rules) (isSome : node.origin.isSome) : List (Fact sig) :=
  let origin := node.origin.get isSome
  origin.fst.val.mapped_head[origin.snd.val]

end CoreChaseNode
