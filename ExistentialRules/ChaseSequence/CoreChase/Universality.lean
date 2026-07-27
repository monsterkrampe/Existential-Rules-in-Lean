/-
Copyright 2026 Henrik Tscherny, Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Deterministic
import ExistentialRules.ChaseSequence.Universality

import ExistentialRules.ChaseSequence.CoreChase.Basic
public import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch
public import ExistentialRules.ChaseSequence.CoreChase.CoreChaseTree

/-!
# Universality of the Core Chase Result

Just as for `RegularChaseTree`s, the result of a `CoreChaseTree` is a universal model set of the underlying `KnowledgeBase`.
Also, for determistic `CoreChaseBranch`es, result is a universal model.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

section CoreChaseTreeUniversality

namespace CoreChaseTree

variable {kb : KnowledgeBase sig}

open AuxiliaryDefsAndTheoremsForUniversalityProof

theorem universal_result (ct : CoreChaseTree kb) (terminates : ct.terminates) : ∀ (m : FactSet sig), m.modelsKb kb ->
    ∃ (fs : FactSet sig) (h : GroundTermMapping sig), fs ∈ CoreTreeDerivation.result ct.toTreeDerivation terminates ∧ h.isHomomorphism fs m := by

  have trg_inactive_of_fresh_term_present : ∀ (node : ct.NodeWithAddress) (trg : RTrigger (RestrictedObsolescence sig) kb.rules) i lt t, t ∈ trg.val.fresh_terms_for_head_disjunct i lt -> t ∈ (CoreChaseNode.coreChaseNodeInstance.outgoingFacts node.node).terms -> ¬ trg.val.active (CoreChaseNode.coreChaseNodeInstance.outgoingFacts node.node) := by
    intro node trg i lt t t_fresh t_mem_node trg_act
    rw [node.node.outgoingFacts_eq] at t_mem_node
    rw [node.node.outgoingFacts_eq] at trg_act
    rcases ct.trigger_introducing_functional_term_occurs_in_chase node (FactSet.terms_subset_of_subset node.node.homSubset.left _ t_mem_node) t_fresh
      with ⟨node2, node2_prec, orig, orig_mem, orig_equiv, head_idx_eq⟩
    exact ct.origin_trg_remains_inactive node2_prec _ orig_mem _ orig_equiv trg_act

  intro m m_is_model

  let derivs_with_homs := infinite_list_of_derivations_and_homomorphisms CoreChaseNode.out_sub_in ct m m_is_model trg_inactive_of_fresh_term_present
  let deriv := (head_infinite_list_of_derivations_and_homomorphisms CoreChaseNode.out_sub_in ct m m_is_model trg_inactive_of_fresh_term_present).fst
  let branch := ct.chaseBranch_for_branch (branch := deriv) mem_branches_fst_head_infinite_list_of_derivations_and_homomorphisms

  let target_idx := (deriv.branch.toList_of_finite (terminates _ mem_branches_fst_head_infinite_list_of_derivations_and_homomorphisms)).length - 1
  suffices (derivs_with_homs.get? target_idx).map (fun step => step.fst.head.core) = some (CoreChaseDerivation.result branch.toChaseDerivation (terminates _ mem_branches_fst_head_infinite_list_of_derivations_and_homomorphisms)) by
    have isSome : (derivs_with_homs.get? target_idx).isSome := by
      rw [Option.map_eq_some_iff] at this; rcases this with ⟨_, eq, _⟩; simp [eq]
    let step := (derivs_with_homs.get? target_idx).get isSome
    have step_eq_result : step.fst.head.core = CoreChaseDerivation.result branch.toChaseDerivation (terminates _ mem_branches_fst_head_infinite_list_of_derivations_and_homomorphisms) := by
      rw [← Option.some_get isSome, Option.map_some, Option.some_inj] at this; exact this
    exists CoreChaseDerivation.result branch.toChaseDerivation (terminates _ mem_branches_fst_head_infinite_list_of_derivations_and_homomorphisms)
    exists step.snd
    constructor
    . exists deriv, mem_branches_fst_head_infinite_list_of_derivations_and_homomorphisms
    . rw [← step_eq_result]
      apply each_step_isHomomorphism_in_infinite_list_of_derivations_and_homomorphisms
      rw [derivs_with_homs.mem_iff]
      exists target_idx
      simp [step]
  simp only [CoreChaseDerivation.result, ChaseDerivationSkeleton.last]
  rw [List.getLast_eq_getElem, ← Option.map_some, ← List.getElem?_eq_getElem]
  rw [PossiblyInfiniteList.getElem?_toList_of_finite]
  simp only [branch, ChaseTree.chaseBranch_for_branch]
  simp only [deriv, fst_head_infinite_list_of_derivations_and_homomorphisms_eq_list_of_all_heads]
  rw [PossiblyInfiniteList.get?_map, Option.map_map]
  congr
  simp only [← fst_head_infinite_list_of_derivations_and_homomorphisms_eq_list_of_all_heads]; rfl

end CoreChaseTree

end CoreChaseTreeUniversality


section CoreChaseDeterministic

namespace CoreTreeDerivation

variable {rules : RuleSet sig}

/-- The `firstResult` is the result of the `firstBranch`. -/
def firstResult (td : CoreTreeDerivation rules) (terminates : td.terminates) : FactSet sig := CoreChaseDerivation.result td.firstBranch (terminates _ td.firstBranch_mem_branches)

/-- The `firstResult` is a member of the `TreeDerivation.result`. -/
theorem firstResult_mem_result {td : CoreTreeDerivation rules} {terminates : td.terminates} : td.firstResult terminates ∈ td.result terminates := by
  unfold CoreTreeDerivation.result
  exists td.firstBranch; constructor
  . rfl
  . exact td.firstBranch_mem_branches

end CoreTreeDerivation

namespace CoreChaseTree

variable {kb : KnowledgeBase sig}

/-- In the deterministic setting, the `firstResult` of a `CoreChaseTree` is by itself a universal model. -/
theorem deterministicChaseTreeResultUniversallyModelsKb {ct : CoreChaseTree kb} (det : kb.isDeterministic) (terminates : ct.terminates) :
    (CoreTreeDerivation.firstResult ct.toTreeDerivation terminates).universallyModelsKb kb := by
  constructor
  . apply ct.result_models_kb; exact CoreTreeDerivation.firstResult_mem_result
  . intro m m_is_model
    rcases ct.universal_result terminates m m_is_model with ⟨res, hom, res_mem, hom_is_hom⟩
    unfold CoreTreeDerivation.result at res_mem
    rcases res_mem with ⟨b, b_mem, res_mem⟩
    have b_mem := TreeDerivation.branches_eq_firstBranch_of_determinsitic det _ b_mem
    unfold CoreTreeDerivation.firstResult
    unfold CoreChaseDerivation.result
    simp only [← b_mem, res_mem]
    exact ⟨_, hom_is_hom⟩

end CoreChaseTree

namespace CoreChaseDerivation

variable {rules : RuleSet sig}

/-- The `firstResult` of `intoTree` is the original `ChaseDerivationSkeleton.result`. -/
theorem firstResult_intoTree_eq_result (cd : CoreChaseDerivation rules) (det : rules.isDeterministic) (terminates : cd.terminates) :
    CoreTreeDerivation.firstResult (cd.intoTree det) (by unfold TreeDerivation.terminates; intro branch branch_mem; rw [cd.branches_intoTree det _ branch_mem]; exact terminates) = cd.result terminates := by
  unfold CoreTreeDerivation.firstResult
  congr
  exact cd.firstBranch_intoTree_eq_self det

end CoreChaseDerivation

namespace CoreChaseBranch

variable {kb : KnowledgeBase sig}

theorem result_universallyModels_kb {cb : CoreChaseBranch kb} (det : kb.isDeterministic) (terminates : cb.terminates) :
    (CoreChaseDerivation.result cb.toChaseDerivation terminates).universallyModelsKb kb := by
  unfold CoreChaseDerivation.result
  have eq := CoreChaseDerivation.firstResult_intoTree_eq_result cb.toChaseDerivation det terminates
  unfold CoreChaseDerivation.result at eq
  rw [← eq]
  apply CoreChaseTree.deterministicChaseTreeResultUniversallyModelsKb (ct := (cb.intoTree det)) det

end CoreChaseBranch

end CoreChaseDeterministic

