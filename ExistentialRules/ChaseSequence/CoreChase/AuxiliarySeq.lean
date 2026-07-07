/-
Copyright 2026 Henrik Tscherny, Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.ChaseBranch
import ExistentialRules.ChaseSequence.Deterministic

import ExistentialRules.ChaseSequence.CoreChase.Basic
public import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch

/-!
# The Core Chase terminates if a finite universal model exists

In this file, we aim to show the result from the title.
THIS IS EXTREMELY PRELIMINARY. A lot of things are still open here.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace CoreChaseBranch

variable {kb : KnowledgeBase sig}

theorem exTerminatingCoreChaseBranchIfExTerminatingChaseBranch (scb : RegularChaseBranch obs kb) (scb_term : scb.terminates) :
    ∃ (ccb : CoreChaseBranch kb), ccb.terminates := by
  -- the idea would be to build the core chase branch directly from the restricted chase branch by dropping the nodes whose triggers are no longer active after core computation; the construction is not trivial though
  sorry

theorem existsNonTerminatingChaseBranchIfExistsNonTerminatingCoreChaseBranch (ccb : CoreChaseBranch kb) (ccb_term : ¬ ccb.terminates) :
    ∃ (scb : RegularChaseBranch (RestrictedObsolescence sig) kb), ¬ scb.terminates := by
  sorry

public theorem exTerminatingCoreChaseBranchIfExFiniteUniversalModel (ccb : CoreChaseBranch kb) (kb_det : kb.isDeterministic) :
    (∃ (fs : FactSet sig), fs.finite ∧ fs.universallyModelsKb kb) → ccb.terminates := by

  /-
  ccb : A_0 → A_1 → A_2 .....
  scb : B_1 → B_2 → B_3 .....
              B_n
  -/

  intro ⟨M, ⟨M_list, _, M_eq⟩, M_umod⟩

  apply Classical.byContradiction
  intro contra

  have ex_inf_scb := existsNonTerminatingChaseBranchIfExistsNonTerminatingCoreChaseBranch ccb contra
  rcases ex_inf_scb with ⟨scb, scb_non_term⟩

  -- R = B^{res}_ω
  let R := scb.result

  have R_umod : R.universallyModelsKb kb := scb.deterministicChaseBranchResultUniversallyModelsKb kb_det

  have hom_M_R : ∃ (h : GroundTermMapping sig), h.isHomomorphism M R := by
    rcases M_umod with ⟨M_umod_l, M_umod_r⟩
    specialize M_umod_r R RegularChaseBranch.result_models_kb
    exact M_umod_r

  have hom_R_M : ∃ (h : GroundTermMapping sig), h.isHomomorphism R M := by
    rcases R_umod with ⟨R_umod_l, R_umod_r⟩
    specialize R_umod_r M M_umod.left
    exact R_umod_r

  rcases hom_M_R with ⟨h_M_R, hom_M_R⟩
  rcases hom_R_M with ⟨h_R_M, hom_R_M⟩

  rcases RegularChaseDerivationSkeleton.facts_mem_some_node_of_mem_result (M_list.map h_M_R.applyFact) (by
    intro f f_mem; apply hom_M_R.right; rw [GroundTermMapping.mem_applyFactSet]
    rw [List.mem_toSet, List.mem_map] at f_mem; rcases f_mem with ⟨e, e_mem, f_eq⟩
    exists e; rw [← M_eq, f_eq]; exact ⟨e_mem, rfl⟩)
  with ⟨node, node_mem, M_sub_node⟩

  have hom_M_node : h_M_R.isHomomorphism M node.facts := by
    constructor; exact hom_M_R.left
    intro f f_mem
    apply M_sub_node
    rw [List.mem_toSet, List.mem_map]
    rw [GroundTermMapping.mem_applyFactSet] at f_mem; rcases f_mem with ⟨e, e_mem, f_eq⟩
    exists e; rw [M_eq, f_eq]; exact ⟨e_mem, rfl⟩

  have hom_node_M : h_R_M.isHomomorphism node.facts M := by
    constructor; exact hom_R_M.left
    intro f f_mem
    apply hom_R_M.right
    apply h_R_M.apply_generalized_atom_set_subset_of_subset _ _ (RegularChaseDerivationSkeleton.facts_node_subset_result node node_mem)
    exact f_mem

  have node_finite := scb.facts_finite_of_mem ⟨node, node_mem⟩

  rcases node.facts.exists_weak_core_for_set_of_finite node_finite with ⟨node_core, node_core_isCore⟩

  -- the rest of the prove shall take scb up until node and then compute the core once
  -- we need to prove that a regular core chase branch with the same result exists (this could be a general theorem, i.e. computing the core after any finite number of steps does not make a difference for the result)
  -- then we need to argue that the result of this core chase branch is isomorphic to M (basically since node_core is isomorphic to M) and then we need to argue that the isomorphism preserves modelhood, i.e. that the result of the core chase branch is a model, which justifies that the core chase branch ends at this point. This also yields the desired contradiction.

  sorry

end CoreChaseBranch
