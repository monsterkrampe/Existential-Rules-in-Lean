/-
Copyright 2026 Henrik Tscherny, Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.Models.Cores
public import ExistentialRules.ChaseSequence.ChaseNode

/-!
# Core Chase Node

Similar to a `ChaseNode`, we define another elements of the core chase in a similar fashion.
Besides fact set and origin, these also store the core that the fact set is being condensed to. In principle any such core is allowed and we do not enforce a specific computation procedure.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

section AuxiliaryResultsForTriggerSatisfaction

/-!
## Trigger Satisfaction along finite `homSubset`s.

Given a few extra conditions, trigger satisfaction is preserved along the `homSubset` relation.
This is helpful for the `CoreChaseNode` later on as each node features a `homSubset` internally.
-/

/-- If a trigger is satisfied for fs and all of its frontier terms still occur in a finite core homSubset of fs, then the trigger is also satisfied in this homSubset. -/
theorem trg_remains_obsolete_of_isWeakCore_of_homSubset_of_finite
    {fs core : FactSet sig} (wc : core.isWeakCore) (homSub : core.homSubset fs) (fin : core.finite) :
    ∀ (trg : PreTrigger sig), trg.satisfied fs -> (trg.rule.frontier.map trg.subs).toSet ⊆ core.terms -> trg.satisfied core := by
  intro trg trg_sat frontier_in_core

  rcases trg_sat with ⟨idx, trg_sat⟩
  exists idx

  -- the first trigger is satisfied
  rcases trg_sat with ⟨subs, trg_sat⟩

  -- we have a homomorphism from fs to core; because of core is a homSubset of fs,
  -- it is even an endomorphism on core
  rcases homSub.right with ⟨h, hom⟩
  have h_endo : h.isHomomorphism core core := by
    constructor; exact hom.left
    apply Set.subset_trans _ hom.right
    apply TermMapping.apply_generalized_atom_set_subset_of_subset
    exact homSub.left

  -- we can repeat the homomorphism often enough such that it is the id on all terms in core;
  -- this works since core is finite and a core
  have node_strong_core : core.isStrongCore := core.isStrongCore_of_isWeakCore_of_finite wc fin
  have endo_surj : h.surjectiveSet core.terms core.terms := (node_strong_core h h_endo).right.right
  rcases core.terms_finite_of_finite fin with ⟨terms, _, terms_eq⟩
  have terms_eq : ∀ t, t ∈ core.terms ↔ t ∈ terms := by intro _; rw [terms_eq]
  rw [Function.surjective_set_list_equiv terms_eq terms_eq] at endo_surj
  rcases h.exists_repetition_that_is_inverse_of_surj terms endo_surj with ⟨k, inv⟩

  let target_h : GroundTermMapping sig := (h.repeat_fun k) ∘ h
  have target_h_hom : target_h.isHomomorphism fs core := by
    apply GroundTermMapping.isHomomorphism_compose; exact hom; exact GroundTermMapping.repeat_isHomomorphism h_endo k
  have target_h_id_terms : ∀ t ∈ terms, target_h t = t := inv

  -- we can use the repeated homomorphism together with the substitution that witnesses satisfaction to see that the trigger is also satisfied in core but this yields exactly the contridiction that we were looking for
  exists target_h ∘ subs; constructor
  . intro v v_mem; rw [Function.comp_apply, trg_sat.left v v_mem, target_h_id_terms]
    rw [← terms_eq]
    apply frontier_in_core; rw [List.mem_toSet]; apply List.mem_map_of_mem v_mem
  . rw [GroundSubstitution.apply_function_free_conj_compose_of_isIdOnConstants _ _ target_h_hom.left]
    intro f f_mem
    rw [List.mem_toSet, Function.comp_apply, TermMapping.mem_apply_generalized_atom_list] at f_mem
    rcases f_mem with ⟨intermediate, intermediate_mem, f_eq⟩
    apply target_h_hom.right
    rw [f_eq]
    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
    apply trg_sat.right
    rw [List.mem_toSet]
    exact intermediate_mem

/-- If a trigger is satisfied for fs, for every core homSubset of fs, every equivalent trigger is satisfied given that is is loaded.  This is a direct consequence of `trg_remains_obsolete_of_isWeakCore_of_homSubset_of_finite`. -/
theorem equiv_trg_obsolete_of_isWeakCore_of_homSubset_of_finite
    {fs core : FactSet sig} (wc : core.isWeakCore) (homSub : core.homSubset fs) (fin : core.finite) :
    ∀ (trg : PreTrigger sig), trg.satisfied fs ->
    ∀ (trg2 : PreTrigger sig), trg.equiv trg2 -> trg2.loaded core -> trg2.satisfied core := by
  intro trg trg_sat trg2 equiv trg2_loaded
  rw [← PreTrigger.satisfied_preserved_of_equiv equiv]
  apply trg_remains_obsolete_of_isWeakCore_of_homSubset_of_finite wc homSub fin trg trg_sat
  rw [equiv.left]
  intro t t_mem; apply FactSet.terms_subset_of_subset trg2_loaded
  rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
  apply Or.inr; rw [List.mem_toSet, List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_eq⟩
  exists v; constructor; apply Rule.frontier_subset_vars_body; exact v_mem
  rw [← equiv.left] at v_mem; rw [← equiv.right _ v_mem]; exact t_eq

end AuxiliaryResultsForTriggerSatisfaction

section CoreChaseNode

/-!
## CoreChaseNode Definition and Theorems

Here we present the actual `CoreChaseNode` definition and prove
some basic properties also relying on the results above.
-/

/-- The CoreChaseNode add a couple of fields on top of the RegularChaseNode but the `facts` field has a different meaning. This is why we duplicate the structure and not jsut extend it. We want to prevent that the `CoreChaseNode` is accidentally treated as a `RegularChaseNode`. -/
structure CoreChaseNode (rules : RuleSet sig) where
  facts : FactSet sig
  origin : Option ((trg : RTrigger (RestrictedObsolescence sig) rules) × Fin trg.val.mapped_head.length)
  facts_contain_origin_result : ∀ orig ∈ origin, orig.fst.val.mapped_head[orig.snd.val].toSet ⊆ facts
  core : FactSet sig
  isWeakCore : core.isWeakCore
  homSubset : core.homSubset facts

namespace CoreChaseNode

variable {rules : RuleSet sig}

/-- The `CoreChaseNode` is a `ChaseNode` where the outgoingFacts are a core of the ingoingFacts. -/
instance coreChaseNodeInstance : ChaseNode (CoreChaseNode rules) (RestrictedObsolescence sig) rules where
  ingoingFacts := CoreChaseNode.facts
  outgoingFacts := CoreChaseNode.core
  origin := CoreChaseNode.origin
  facts_contain_origin_result := CoreChaseNode.facts_contain_origin_result

theorem ingoingFacts_eq {node : CoreChaseNode rules} : coreChaseNodeInstance.ingoingFacts node = node.facts := by rfl
theorem outgoingFacts_eq {node : CoreChaseNode rules} : coreChaseNodeInstance.outgoingFacts node = node.core := by rfl

/-- The `CoreChaseNode` has the `ChaseNode.out_sub_in` property. -/
theorem out_sub_in : coreChaseNodeInstance.out_sub_in (N := CoreChaseNode rules) := by
  intro node f; rw [ingoingFacts_eq, outgoingFacts_eq]; exact node.homSubset.left f

/-- Every trigger equivalent to the origin trigger of a `CoreChaseNode` is inactive for each homSubset of the node's facts, given that this subset is finite. -/
theorem equiv_origin_trg_inactive_of_isWeakCore_of_homSubset_of_finite
    {node : CoreChaseNode rules} {fs : FactSet sig}
    (wc : fs.isWeakCore) (homSub : fs.homSubset node.facts) (fin : fs.finite) :
    ∀ orig ∈ node.origin, ∀ trg, orig.fst.equiv trg -> ¬ trg.val.active fs := by
  intro orig orig_mem trg equiv ⟨loaded, contra⟩
  apply contra
  apply equiv_trg_obsolete_of_isWeakCore_of_homSubset_of_finite wc homSub fin _ _ _ equiv loaded
  let idx : Fin orig.fst.val.rule.head.length := ⟨orig.snd.val, by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt⟩
  exists idx
  apply PreTrigger.satisfied_for_disj_of_mapped_head_contained
  apply node.facts_contain_origin_result
  exact orig_mem

/-- The origin trigger of a `CoreChaseNode` is inactive for each homSubset of the node's facts, given that this subset is finite. -/
theorem origin_trg_inactive_of_isWeakCore_of_homSubset_of_finite
    {node : CoreChaseNode rules} {fs : FactSet sig} (wc : fs.isWeakCore) (homSub : fs.homSubset node.facts) (fin : fs.finite) :
    ∀ orig ∈ node.origin, ¬ orig.fst.val.active fs := by
  intro orig orig_mem
  exact equiv_origin_trg_inactive_of_isWeakCore_of_homSubset_of_finite wc homSub fin orig orig_mem _ PreTrigger.equiv_refl

/-- Every trigger equivalent to the origin trigger of a `CoreChaseNode` is inactive on the node's core. -/
theorem equiv_origin_trg_inactive_for_own_core_of_finite {node : CoreChaseNode rules} (fin : node.core.finite) :
    ∀ orig ∈ node.origin, ∀ trg, orig.fst.equiv trg -> ¬ trg.val.active node.core := by
  intro orig orig_mem trg equiv
  exact equiv_origin_trg_inactive_of_isWeakCore_of_homSubset_of_finite node.isWeakCore node.homSubset fin orig orig_mem _ equiv

/-- The origin trigger of a `CoreChaseNode` is inactive on the node's core. -/
theorem origin_trg_inactive_for_own_core_of_finite {node : CoreChaseNode rules} (fin : node.core.finite) :
    ∀ orig ∈ node.origin, ¬ orig.fst.val.active node.core := by
  apply origin_trg_inactive_of_isWeakCore_of_homSubset_of_finite
  . exact node.isWeakCore
  . exact node.homSubset
  . exact fin

end CoreChaseNode

end CoreChaseNode

