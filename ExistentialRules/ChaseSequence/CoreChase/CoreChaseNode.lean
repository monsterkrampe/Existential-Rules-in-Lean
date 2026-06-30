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
variable {kb : KnowledgeBase sig}
abbrev obs := RestrictedObsolescence sig


structure CoreChaseNode (rules : RuleSet sig) where
  fs : FactSet sig
  fs_fin : fs.finite
  core : FactSet sig
  is_core : core.isWeakCore
  core_sse : core.homSubset fs
  origin : Option ((trg : RTrigger obs.toLaxObsolescenceCondition rules) × Fin trg.val.mapped_head.length)
  fs_contains_origin_result : ∀ o ∈ origin, o.fst.val.mapped_head[o.snd.val].toSet ⊆ fs

namespace CoreChaseNode

  noncomputable instance : DecidableEq (CoreChaseNode kb.rules) := by
    exact Classical.typeDecidableEq (CoreChaseNode kb.rules)


  def origin_result {rules : RuleSet sig} (node : CoreChaseNode rules) (isSome : node.origin.isSome) : List (Fact sig) :=
    let origin := node.origin.get isSome
    origin.fst.val.mapped_head[origin.snd.val]

  @[grind .]
  theorem core_finite_if_fs_finite {rules : RuleSet sig} (node : CoreChaseNode rules) (fs_fin : node.fs.finite) : node.core.finite := by
    rcases node.core_sse with ⟨sub, ⟨gtm, gtm_hom⟩⟩
    exact Set.finite_of_subset_finite fs_fin sub

  @[grind .]
  theorem core_finite (node : CoreChaseNode kb.rules) : Set.finite (node.core) := by
    apply CoreChaseNode.core_finite_if_fs_finite
    exact node.fs_fin

  @[grind .]
  theorem fs_terms_sub_core_terms (cn : CoreChaseNode kb.rules) (t : GroundTerm sig) (t_in_core : t ∈ cn.core.terms) : t ∈ cn.fs.terms := by
      rcases t_in_core with ⟨f, f_c, f_t⟩
      have f_fs : f ∈ cn.fs := cn.core_sse.left f f_c
      exists f


end CoreChaseNode
