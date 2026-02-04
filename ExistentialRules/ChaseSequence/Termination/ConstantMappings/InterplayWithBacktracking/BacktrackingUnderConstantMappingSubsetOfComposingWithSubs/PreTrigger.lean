import ExistentialRules.ChaseSequence.Termination.ConstantMappings.InterplayWithBacktracking.BacktrackingUnderConstantMappingSubsetOfComposingWithSubs.GroundTerm

/-!
# Interaction of Backtrackings and Strict Constant Mappings on PreTrigger

We merely lift `GroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs` to `PreTrigger` here.
-/

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

theorem PreTrigger.backtracking_under_constant_mapping_subset_of_composing_with_subs
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (rl : RuleList sig)
    (trg : PreTrigger sig)
    (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
    (trg_disjIdx_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid)
    (trg_rule_arity_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid)
    (trg_rule_in_rl : trg.rule ∈ rl.rules) :
    let backtracking := trg.backtrackFacts rl trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid
    ∀ (g : StrictConstantMapping sig), (∀ d, (d ∈ rl.rules.flatMap Rule.constants) -> g d = d) ->
      ∃ (fresh_constant_remapping : StrictConstantMapping sig),
      (∀ d ∉ backtracking.snd, fresh_constant_remapping d = d) ∧
      ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then fresh_constant_remapping c else g c)).apply_fact_set backtracking.fst.toSet ⊆
      ({rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.backtrackFacts rl (trg.compose_strict_constant_mapping_preserves_ruleId_validity g rl trg_ruleIds_valid) (trg.compose_strict_constant_mapping_preserves_disjIdx_validity g rl trg_ruleIds_valid trg_disjIdx_valid) (trg.compose_strict_constant_mapping_preserves_rule_arity_validity g rl trg_ruleIds_valid trg_rule_arity_valid)).fst.toSet) ∧
      (backtracking.snd.map fresh_constant_remapping = ({rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.backtrackFacts rl (trg.compose_strict_constant_mapping_preserves_ruleId_validity g rl trg_ruleIds_valid) (trg.compose_strict_constant_mapping_preserves_disjIdx_validity g rl trg_ruleIds_valid trg_disjIdx_valid) (trg.compose_strict_constant_mapping_preserves_rule_arity_validity g rl trg_ruleIds_valid trg_rule_arity_valid)).snd) := by
  intro backtracking g g_id
  let forbidden_constants := trg.mapped_body.flatMap Fact.constants ++ rl.rules.flatMap Rule.constants
  rcases GroundTerm.backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs rl (trg.mapped_body.flatMap GeneralizedAtom.terms) trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid forbidden_constants (by apply List.subset_append_of_subset_left; intro d d_mem; rw [List.mem_flatMap] at d_mem; rcases d_mem with ⟨t, t_mem, d_mem⟩; rw [List.mem_flatMap] at t_mem; rcases t_mem with ⟨f, f_mem, t_mem⟩; rw [List.mem_flatMap]; exists f; constructor; exact f_mem; unfold Fact.constants; rw [List.mem_flatMap]; exists t) (by apply List.subset_append_of_subset_right; simp) g g_id with ⟨fresh_constant_remapping, fresh_constant_remapping_h⟩

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
      rw [List.mem_flatMap]
      exists trg.rule
      constructor
      . exact trg_rule_in_rl
      . unfold Rule.constants
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

  have forbidden_constants_map_g_eq : forbidden_constants.map g = ({ rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig }.mapped_body.flatMap Fact.constants) ++ rl.rules.flatMap Rule.constants := by
    unfold forbidden_constants
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
        rw [List.mem_flatMap]
        exists trg.rule
        constructor
        . exact trg_rule_in_rl
        . unfold Rule.constants
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
    . apply List.map_id_of_id_on_all_mem
      intro d d_mem
      apply g_id
      exact d_mem

  exists fresh_constant_remapping
  constructor
  . exact fresh_constant_remapping_h.left
  constructor
  . intro e e_mem
    rcases e_mem with ⟨f, f_mem, e_eq⟩
    simp only [List.mem_toSet, backtracking, backtrackFacts, List.mem_append] at f_mem
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
          have : d ∉ backtracking.snd := by
            intro contra
            apply GroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d contra
            rw [List.mem_append]
            apply Or.inl
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
          rw [List.mem_flatMap]
          exists trg.rule
          constructor
          . exact trg_rule_in_rl
          . unfold Rule.constants
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
      exists f
  . simp only [backtracking, backtrackFacts]
    rw [fresh_constant_remapping_h.right.right]
    simp only [mapped_body_map_swap, forbidden_constants_map_g_eq]

