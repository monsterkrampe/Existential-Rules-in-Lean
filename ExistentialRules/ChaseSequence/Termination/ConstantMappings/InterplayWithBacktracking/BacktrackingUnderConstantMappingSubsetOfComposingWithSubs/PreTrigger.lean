/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Termination.ConstantMappings.InterplayWithBacktracking.BacktrackingUnderConstantMappingSubsetOfComposingWithSubs.GroundTerm

/-!
# Interaction of Backtrackings and Strict Constant Mappings on PreTrigger

We merely lift `GroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs` to `PreTrigger` here.
-/

public section

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

/--
The affected rules for triggers with the `PreTrigger.same_skeleton` are the same.
-/
theorem PreTrigger.affected_rules_eq_of_same_skeleton {trg trg2 : PreTrigger sig} (same_skeleton : trg.same_skeleton trg2) :
    trg.affected_rules_for_backtracking = trg2.affected_rules_for_backtracking := by
  unfold affected_rules_for_backtracking
  rw [List.cons_eq_cons]; constructor; exact same_skeleton.left
  simp only [List.flatMap_def, List.map_flatten]
  apply List.flatten_eq_of_eq; apply List.flatten_eq_of_eq
  apply List.ext_getElem
  . simp [same_skeleton.left]
  . intro i _ _
    simp only [List.getElem_map, PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
    simp only [TermMapping.apply_generalized_atom]
    apply List.ext_getElem
    . simp [same_skeleton.left]
    . intro j _ _
      simp only [List.getElem_map]
      apply GroundTerm.rules_eq_of_same_skeleton
      simp only [← same_skeleton.left]
      cases eq : (trg.rule.body[i]'(by grind)).terms[j]'(by grind) with
      | const c => simp only [GroundSubstitution.apply_var_or_const]; exact GroundTerm.same_skeleton_const
      | var v =>
        apply GroundSubstitution.same_skeleton_of_mem_vars same_skeleton.right
        rw [List.mem_eraseDupsKeepRight, FunctionFreeConjunction.mem_vars', ← eq]
        apply List.mem_flatMap_of_mem
        . exact List.getElem_mem (n := i) (by grind)
        . simp

/--
Since a strict constant mapping does not change term structure, the affected rules of a trigger stay the same when a strict constant mapping is applied after the substitution.
-/
theorem PreTrigger.affected_rules_eq_of_composing_with_subs {trg : PreTrigger sig} : ∀ (g : StrictConstantMapping sig),
    trg.affected_rules_for_backtracking = { rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.affected_rules_for_backtracking := by
  intro g
  apply affected_rules_eq_of_same_skeleton
  apply same_skeleton_under_strict_constant_mapping

theorem PreTrigger.backtracking_under_constant_mapping_subset_of_composing_with_subs
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (trg : PreTrigger sig) :
    ∀ (g : StrictConstantMapping sig), (∀ d ∈ trg.affected_rules_for_backtracking.flatMap Rule.constants, g d = d) ->
      ∃ (fresh_constant_remapping : StrictConstantMapping sig),
      (∀ d ∉ trg.backtrackFacts.snd, fresh_constant_remapping d = d) ∧
      ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ trg.backtrackFacts.snd then fresh_constant_remapping c else g c)).apply_fact_set trg.backtrackFacts.fst.toSet ⊆
      {rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.backtrackFacts.fst.toSet) ∧
      (trg.backtrackFacts.snd.map fresh_constant_remapping = {rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.backtrackFacts.snd) := by
  intro g g_id
  rcases GroundTerm.backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs (trg.mapped_body.flatMap GeneralizedAtom.terms) trg.initial_forbidden_constants_for_backtracking (by apply List.subset_append_of_subset_left; intro d d_mem; rw [List.mem_flatMap] at d_mem; rcases d_mem with ⟨t, t_mem, d_mem⟩; rw [List.mem_flatMap] at t_mem; rcases t_mem with ⟨f, f_mem, t_mem⟩; rw [List.mem_flatMap]; exists f; constructor; exact f_mem; unfold Fact.constants; rw [List.mem_flatMap]; exists t) (by apply List.subset_append_of_subset_right; simp [PreTrigger.affected_rules_for_backtracking]) g (by intro d d_mem; apply g_id; apply List.mem_append_right; exact d_mem) with ⟨fresh_constant_remapping, fresh_constant_remapping_h⟩

  have mapped_body_map_swap : (trg.mapped_body.flatMap GeneralizedAtom.terms).map g.toConstantMapping.apply_ground_term = { rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig }.mapped_body.flatMap GeneralizedAtom.terms := by
    rw [List.map_flatMap]
    simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
    rw [List.flatMap_map, List.flatMap_map]
    unfold List.flatMap
    apply List.flatten_eq_of_eq
    rw [List.map_inj_left]
    intro a a_mem
    simp only [TermMapping.apply_generalized_atom]
    rw [List.map_map, List.map_inj_left]
    intro voc voc_mem
    simp only [Function.comp_apply, GroundSubstitution.apply_var_or_const]
    cases voc with
    | const c =>
      rw [ConstantMapping.apply_ground_term_constant]
      simp only [StrictConstantMapping.toConstantMapping, Function.comp_apply, GroundTerm.const, Subtype.mk.injEq, FiniteTree.leaf.injEq]
      apply g_id
      apply List.mem_append_left
      unfold Rule.constants
      rw [List.mem_append]
      apply Or.inl
      unfold FunctionFreeConjunction.consts
      rw [List.mem_flatMap]
      exists a
      constructor
      . exact a_mem
      . unfold FunctionFreeAtom.constants
        apply VarOrConst.mem_filterConsts_of_const
        exact voc_mem
    | var v => rfl

  have forbidden_constants_map_g_eq : trg.initial_forbidden_constants_for_backtracking.map g = { rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig }.initial_forbidden_constants_for_backtracking := by
    unfold PreTrigger.initial_forbidden_constants_for_backtracking
    rw [List.map_append]
    apply List.append_eq_append_of_parts_eq
    . rw [List.map_flatMap]
      simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
      rw [List.flatMap_map, List.flatMap_map]
      unfold List.flatMap
      apply List.flatten_eq_of_eq
      rw [List.map_inj_left]
      intro a a_mem
      simp only [Fact.constants, TermMapping.apply_generalized_atom]
      rw [List.map_flatMap, List.flatMap_map, List.flatMap_map]
      unfold List.flatMap
      apply List.flatten_eq_of_eq
      rw [List.map_inj_left]
      intro voc voc_mem
      simp only [GroundTerm.constants, Function.comp_apply, GroundSubstitution.apply_var_or_const]
      cases voc with
      | const c =>
        simp only [GroundTerm.const, FiniteTree.leaves]
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
        apply g_id
        apply List.mem_append_left
        unfold Rule.constants
        rw [List.mem_append]
        apply Or.inl
        unfold FunctionFreeConjunction.consts
        rw [List.mem_flatMap]
        exists a
        constructor
        . exact a_mem
        . unfold FunctionFreeAtom.constants
          apply VarOrConst.mem_filterConsts_of_const
          exact voc_mem
      | var v =>
        simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term]
        rw [StrictConstantMapping.map_leaves_eq_leaves_mapLeaves]
    . rw [affected_rules_eq_of_composing_with_subs]
      apply List.map_id_of_id_on_all_mem
      intro d d_mem; apply g_id
      rw [affected_rules_eq_of_composing_with_subs]
      exact d_mem

  exists fresh_constant_remapping
  constructor
  . exact fresh_constant_remapping_h.left
  constructor
  . intro e e_mem
    rw [GroundTermMapping.mem_applyFactSet] at e_mem
    rcases e_mem with ⟨f, f_mem, e_eq⟩
    simp only [List.mem_toSet, backtrackFacts, List.mem_append] at f_mem
    simp only [List.mem_toSet, backtrackFacts, List.mem_append]
    cases f_mem with
    | inl f_mem =>
      apply Or.inl
      simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list] at *
      rw [List.mem_map] at *
      rcases f_mem with ⟨a, a_mem, f_eq⟩
      exists a
      constructor
      . exact a_mem
      . rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose]
        . rw [e_eq, ← f_eq]
          rw [← ConstantMapping.apply_fact_eq_groundTermMapping_applyFact]
          apply ConstantMapping.apply_fact_congr_left
          intro d d_mem
          have : d ∉ trg.backtrackFacts.snd := by
            intro contra
            apply GroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d contra
            apply List.mem_append_left
            rw [List.mem_flatMap]
            exists f
            constructor
            . simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
              rw [List.mem_map]
              exists a
            . rw [← f_eq]
              exact d_mem
          simp [StrictConstantMapping.toConstantMapping, this]
        . intro d d_mem
          simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, StrictConstantMapping.toConstantMapping, Function.comp_apply, GroundTerm.const, Subtype.mk.injEq, FiniteTree.mapLeaves, FiniteTree.leaf.injEq]
          apply g_id
          apply List.mem_append_left
          unfold Rule.constants
          rw [List.mem_append]
          apply Or.inl
          unfold FunctionFreeConjunction.consts
          rw [List.mem_flatMap]
          exists a
    | inr f_mem =>
      apply Or.inr
      simp only [mapped_body_map_swap] at fresh_constant_remapping_h
      rw [forbidden_constants_map_g_eq] at fresh_constant_remapping_h
      rw [← List.mem_toSet]
      apply fresh_constant_remapping_h.right.left
      rw [GroundTermMapping.mem_applyFactSet]
      exists f; constructor; rw [List.mem_toSet]; exact f_mem; exact e_eq
  . simp only [backtrackFacts]
    rw [fresh_constant_remapping_h.right.right]
    simp only [mapped_body_map_swap, forbidden_constants_map_g_eq]

