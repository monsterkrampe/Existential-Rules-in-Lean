import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts
import ExistentialRules.ChaseSequence.Termination.ConstantMappings.InterplayWithObsoletenessCondition

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

mutual

  theorem PreGroundTerm.backtrackFacts_under_strict_constant_mapping_same_number_of_fresh_constants
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (term : PreGroundTerm sig)
      (term_arity_ok : PreGroundTerm.arity_ok term)
      (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term)
      (term_disjIdx_valid : PreGroundTerm.skolem_disjIdx_valid rl term term_ruleIds_valid)
      (term_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid rl term term_ruleIds_valid)
      (forbidden_constants forbidden_constants_2 : List sig.C) :
      ∀ (g : StrictConstantMapping sig),
        (PreGroundTerm.backtrackFacts rl term term_arity_ok term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants).snd.length =
        (PreGroundTerm.backtrackFacts rl (g.toConstantMapping.apply_pre_ground_term term)
          (by apply ConstantMapping.apply_pre_ground_term_arity_ok; exact term_arity_ok)
          (by apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity; exact term_ruleIds_valid)
          (by apply StrictConstantMapping.apply_pre_ground_term_preserves_disjIdx_validity; exact term_disjIdx_valid)
          (by apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity; exact term_rule_arity_valid)
          forbidden_constants_2).snd.length := by
    intro g
    cases term with
    | leaf c => simp only [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const, backtrackFacts]
    | inner func ts =>
      simp only [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, backtrackFacts]
      simp only [backtrackTrigger]
      rw [List.length_append, List.length_append, Rule.length_fresh_consts_for_pure_body_vars, Rule.length_fresh_consts_for_pure_body_vars]
      rw [Nat.add_right_inj]
      rw [backtrackFacts_list_under_strict_constant_mapping_same_number_of_fresh_constants]

  theorem PreGroundTerm.backtrackFacts_list_under_strict_constant_mapping_same_number_of_fresh_constants
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (terms : List (PreGroundTerm sig))
      (terms_arity_ok : ∀ t ∈ terms, PreGroundTerm.arity_ok t)
      (terms_ruleIds_valid : ∀ t ∈ terms, PreGroundTerm.skolem_ruleIds_valid rl t)
      (terms_disjIdx_valid : ∀ t, (t_mem : t ∈ terms) -> PreGroundTerm.skolem_disjIdx_valid rl t (terms_ruleIds_valid t t_mem))
      (terms_rule_arity_valid : ∀ t, (t_mem : t ∈ terms) -> PreGroundTerm.skolem_rule_arity_valid rl t (terms_ruleIds_valid t t_mem))
      (forbidden_constants forbidden_constants_2 : List sig.C) :
      ∀ (g : StrictConstantMapping sig),
        (PreGroundTerm.backtrackFacts_list rl terms terms_arity_ok terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).snd.length =
        (PreGroundTerm.backtrackFacts_list rl (terms.map g.toConstantMapping.apply_pre_ground_term)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; rw [← t_eq]; apply ConstantMapping.apply_pre_ground_term_arity_ok; exact terms_arity_ok _ t'_mem)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; rw [← t_eq]; apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity; exact terms_ruleIds_valid _ t'_mem)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_pre_ground_term_preserves_disjIdx_validity; exact terms_disjIdx_valid _ t'_mem)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity; exact terms_rule_arity_valid _ t'_mem)
          forbidden_constants_2).snd.length := by
    intro g
    cases terms with
    | nil => simp [backtrackFacts_list]
    | cons hd tl =>
      simp only [backtrackFacts_list, List.map_cons]
      rw [List.length_append, List.length_append]
      rw [backtrackFacts_under_strict_constant_mapping_same_number_of_fresh_constants]
      simp only [ConstantMapping.apply_pre_ground_term]
      rw [backtrackFacts_list_under_strict_constant_mapping_same_number_of_fresh_constants]

end

mutual

  theorem PreGroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (term : PreGroundTerm sig)
      (term_arity_ok : PreGroundTerm.arity_ok term)
      (term_ruleIds_valid : term.skolem_ruleIds_valid rl)
      (term_disjIdx_valid : term.skolem_disjIdx_valid rl term_ruleIds_valid)
      (term_rule_arity_valid : term.skolem_rule_arity_valid rl term_ruleIds_valid)
      (forbidden_constants : List sig.C)
      (forbidden_constants_subsumes_term : term.leaves ⊆ forbidden_constants)
      (forbidden_constants_subsumes_rules : (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants) :
      let backtracking := (backtrackFacts rl term term_arity_ok term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants)
      ∀ (g : StrictConstantMapping sig), (∀ d, (d ∈ rl.rules.flatMap Rule.constants) -> g d = d) ->
        ∃ (fresh_constant_remapping : StrictConstantMapping sig),
        (∀ d ∉ backtracking.snd, fresh_constant_remapping d = d) ∧
        ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then fresh_constant_remapping c else g c)).apply_fact_set backtracking.fst.toSet ⊆
        (backtrackFacts rl (g.toConstantMapping.apply_pre_ground_term term)
          (by apply ConstantMapping.apply_pre_ground_term_arity_ok; exact term_arity_ok)
          (by apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity; exact term_ruleIds_valid)
          (by apply StrictConstantMapping.apply_pre_ground_term_preserves_disjIdx_validity; exact term_disjIdx_valid)
          (by apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity; exact term_rule_arity_valid)
          (forbidden_constants.map g)
        ).fst.toSet) ∧
        (backtracking.snd.map fresh_constant_remapping = (backtrackFacts rl (g.toConstantMapping.apply_pre_ground_term term)
          (by apply ConstantMapping.apply_pre_ground_term_arity_ok; exact term_arity_ok)
          (by apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity; exact term_ruleIds_valid)
          (by apply StrictConstantMapping.apply_pre_ground_term_preserves_disjIdx_validity; exact term_disjIdx_valid)
          (by apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity; exact term_rule_arity_valid)
          (forbidden_constants.map g)
        ).snd) := by
    intro backtracking g g_id
    cases term with
    | leaf c =>
      exists id
      constructor
      . simp
      constructor
      . intro e e_mem
        rcases e_mem with ⟨f, f_mem, e_eq⟩
        simp [List.mem_toSet, backtracking, backtrackFacts] at f_mem
      . simp only [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
        simp only [backtracking, backtrackFacts, GroundTerm.const, StrictConstantMapping.toConstantMapping]
        simp
    | inner func ts =>
      have term_arity_ok' : ts.length == func.arity && ts.attach.all (fun ⟨t, _⟩ => arity_ok t) := by unfold arity_ok at term_arity_ok; exact term_arity_ok
      have term_ruleIds_valid' : func.ruleId_valid rl ∧ ∀ t ∈ ts, PreGroundTerm.skolem_ruleIds_valid rl t := by unfold skolem_ruleIds_valid at term_ruleIds_valid; exact term_ruleIds_valid
      have term_disjIdx_valid' : func.disjunctIndex_valid rl term_ruleIds_valid'.left ∧ ∀ t, (t_mem : t ∈ ts) -> PreGroundTerm.skolem_disjIdx_valid rl t (term_ruleIds_valid'.right t t_mem) := by unfold skolem_disjIdx_valid at term_disjIdx_valid; exact term_disjIdx_valid
      have term_rule_arity_valid' : func.arity_valid rl term_ruleIds_valid'.left ∧ ∀ t, (t_mem : t ∈ ts) -> PreGroundTerm.skolem_rule_arity_valid rl t (term_ruleIds_valid'.right t t_mem) := by unfold skolem_rule_arity_valid at term_rule_arity_valid; exact term_rule_arity_valid

      let rule := rl.get_by_id func.ruleId term_ruleIds_valid'.left
      let pure_body_vars := rule.pure_body_vars
      let fresh_consts_for_pure_body_vars := rule.fresh_consts_for_pure_body_vars forbidden_constants
      let fresh_consts_for_pure_body_vars_2 := rule.fresh_consts_for_pure_body_vars (forbidden_constants.map g)

      let new_g : StrictConstantMapping sig := fun c =>
        if mem : c ∈ fresh_consts_for_pure_body_vars.val
        then
          let idx := fresh_consts_for_pure_body_vars.val.idxOf c
          have : idx < fresh_consts_for_pure_body_vars_2.val.length := by
            rw [fresh_consts_for_pure_body_vars_2.property.left]
            rw [← fresh_consts_for_pure_body_vars.property.left]
            apply List.idxOf_lt_length_of_mem
            exact mem
          fresh_consts_for_pure_body_vars_2.val[idx]
        else g c

      rcases backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs rl ts (by
        intro t t_mem
        have := (Bool.and_eq_true_iff.mp term_arity_ok').right
        rw [List.all_eq_true] at this
        apply this ⟨t, t_mem⟩
        apply List.mem_attach
      ) term_ruleIds_valid'.right term_disjIdx_valid'.right term_rule_arity_valid'.right (forbidden_constants ++ fresh_consts_for_pure_body_vars) (by apply List.subset_append_of_subset_left; simp only [FiniteTree.leaves] at forbidden_constants_subsumes_term; exact forbidden_constants_subsumes_term) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_rules) new_g
        (by intro d d_mem
            unfold new_g
            have : d ∉ fresh_consts_for_pure_body_vars.val := by
              intro contra
              apply fresh_consts_for_pure_body_vars.property.right.right d contra
              apply forbidden_constants_subsumes_rules
              exact d_mem
            simp only [this, ↓reduceDIte]
            apply g_id
            exact d_mem) with ⟨g_mapped_frontier, g_mapped_frontier_h⟩

      let combined_remapping : StrictConstantMapping sig := fun c =>
        if mem : c ∈ fresh_consts_for_pure_body_vars.val
        then
          let idx := fresh_consts_for_pure_body_vars.val.idxOf c
          have : idx < fresh_consts_for_pure_body_vars_2.val.length := by
            rw [fresh_consts_for_pure_body_vars_2.property.left]
            rw [← fresh_consts_for_pure_body_vars.property.left]
            apply List.idxOf_lt_length_of_mem
            exact mem
          fresh_consts_for_pure_body_vars_2.val[idx]
        else g_mapped_frontier c

      have new_g_on_forbidden_constants_is_g : forbidden_constants.map new_g = forbidden_constants.map g := by
        rw [List.map_inj_left]
        intro d d_mem
        have : d ∉ fresh_consts_for_pure_body_vars.val := by
          intro contra
          apply fresh_consts_for_pure_body_vars.property.right.right d contra
          exact d_mem
        simp [new_g, this]
      have new_g_on_fresh_is_fresh2 : fresh_consts_for_pure_body_vars.val.map new_g = fresh_consts_for_pure_body_vars_2.val := by
        rw [List.map_eq_iff]
        intro idx
        cases Decidable.em (idx < fresh_consts_for_pure_body_vars.val.length) with
        | inl idx_lt =>
          rw [List.getElem?_eq_getElem idx_lt, Option.map_some]
          rw [List.getElem?_eq_getElem]
          rw [Option.some_inj]
          . unfold new_g
            simp only [List.getElem_mem, ↓reduceDIte]
            simp only [List.idxOf_getElem fresh_consts_for_pure_body_vars.property.right.left]
          . rw [fresh_consts_for_pure_body_vars_2.property.left]
            rw [← fresh_consts_for_pure_body_vars.property.left]
            exact idx_lt
        | inr idx_lt =>
          rw [List.getElem?_eq_none]
          rw [List.getElem?_eq_none]
          . simp
          . apply Nat.le_of_not_lt; exact idx_lt
          . rw [fresh_consts_for_pure_body_vars_2.property.left]
            rw [← fresh_consts_for_pure_body_vars.property.left]
            apply Nat.le_of_not_lt; exact idx_lt
      have new_g_on_ts : (List.map new_g.toConstantMapping.apply_pre_ground_term ts) = (List.map g.toConstantMapping.apply_pre_ground_term ts) := by
        rw [List.map_inj_left]
        intro t t_mem
        apply ConstantMapping.apply_pre_ground_term_congr_left
        intro d d_mem
        simp only [StrictConstantMapping.toConstantMapping, new_g]
        have : d ∉ fresh_consts_for_pure_body_vars.val := by
          intro contra
          apply fresh_consts_for_pure_body_vars.property.right.right d contra
          apply forbidden_constants_subsumes_term
          simp only [FiniteTree.leaves, List.mem_flatMap]
          exists t
        simp [this]
      have combined_remapping_on_fresh_is_fresh2 : fresh_consts_for_pure_body_vars.val.map combined_remapping = fresh_consts_for_pure_body_vars_2.val := by
        rw [List.map_eq_iff]
        intro idx
        cases Decidable.em (idx < fresh_consts_for_pure_body_vars.val.length) with
        | inl idx_lt =>
          rw [List.getElem?_eq_getElem idx_lt, Option.map_some]
          rw [List.getElem?_eq_getElem]
          rw [Option.some_inj]
          . unfold combined_remapping
            simp only [List.getElem_mem, ↓reduceDIte]
            simp only [List.idxOf_getElem fresh_consts_for_pure_body_vars.property.right.left]
          . rw [fresh_consts_for_pure_body_vars_2.property.left]
            rw [← fresh_consts_for_pure_body_vars.property.left]
            exact idx_lt
        | inr idx_lt =>
          rw [List.getElem?_eq_none]
          rw [List.getElem?_eq_none]
          . simp
          . apply Nat.le_of_not_lt; exact idx_lt
          . rw [fresh_consts_for_pure_body_vars_2.property.left]
            rw [← fresh_consts_for_pure_body_vars.property.left]
            apply Nat.le_of_not_lt; exact idx_lt

      let trg_base : PreTrigger sig := PreGroundTerm.backtrackTrigger rl (.inner func ts) (by exists func, ts) term_arity_ok term_ruleIds_valid term_rule_arity_valid forbidden_constants

      let trg1 : PreTrigger sig := PreGroundTerm.backtrackTrigger rl
        (g.toConstantMapping.apply_pre_ground_term (.inner func ts))
        (by exists func, (ts.map g.toConstantMapping.apply_pre_ground_term); simp [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves])
        (by apply ConstantMapping.apply_pre_ground_term_arity_ok; exact term_arity_ok)
        (by apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity; exact term_ruleIds_valid)
        (by apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity; exact term_rule_arity_valid)
        (forbidden_constants.map g)

      have trg1_rule_eq_rule : trg1.rule = rule := by simp only [trg1, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]; rfl

      let trg2 : PreTrigger sig := {
        rule := trg_base.rule,
        subs := (StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then combined_remapping c else g c)).apply_ground_term ∘ trg_base.subs,
      }

      have strong_equiv : trg1.strong_equiv trg2 := by
        unfold PreTrigger.strong_equiv
        constructor
        . rw [trg1_rule_eq_rule]; rfl
        . intro v v_mem
          simp only [trg1, trg2, trg_base]
          simp only [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
          simp only [backtrackTrigger]
          cases Decidable.em (v ∈ rule.frontier) with
          | inl v_mem_frontier =>
            simp only [Function.comp_apply, rule, v_mem_frontier, ↓reduceDIte]
            simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, StrictConstantMapping.toConstantMapping]
            simp only [List.getElem_map, Subtype.mk.injEq]
            apply FiniteTree.mapLeaves_eq_of_map_leaves_eq
            rw [List.map_inj_left]
            intro d d_mem
            have : d ∉ backtracking.snd := by
              intro contra
              apply backtrackFacts_fresh_constants_not_forbidden d contra
              apply forbidden_constants_subsumes_term
              simp only [FiniteTree.leaves]
              apply List.mem_flatMap_of_mem _ d_mem
              apply List.getElem_mem
            simp [this]
          | inr v_mem_frontier =>
            have v_mem_pure_body : v ∈ pure_body_vars := by
              simp only [pure_body_vars, Rule.pure_body_vars, List.mem_filter, FunctionFreeConjunction.vars]
              constructor
              . unfold FunctionFreeConjunction.vars at v_mem
                rw [trg1_rule_eq_rule] at v_mem
                exact v_mem
              . apply decide_eq_true; exact v_mem_frontier
            simp only [rule] at v_mem_frontier
            simp only [pure_body_vars, rule] at v_mem_pure_body
            simp only [Function.comp_apply, v_mem_frontier, v_mem_pure_body, ↓reduceDIte]
            simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, StrictConstantMapping.toConstantMapping]
            simp only [GroundTerm.const, FiniteTree.mapLeaves, Subtype.mk.injEq, FiniteTree.leaf.injEq]
            have : fresh_consts_for_pure_body_vars.val[pure_body_vars.idxOf v]'(by rw [fresh_consts_for_pure_body_vars.property.left]; apply List.idxOf_lt_length_of_mem; exact v_mem_pure_body) ∈ backtracking.snd := by
              simp only [backtracking, backtrackFacts]
              apply List.mem_append_left
              apply List.getElem_mem
            simp only [fresh_consts_for_pure_body_vars, pure_body_vars, rule] at this
            simp only [this, ↓reduceIte]

            rw [List.map_eq_iff] at combined_remapping_on_fresh_is_fresh2
            specialize combined_remapping_on_fresh_is_fresh2 (pure_body_vars.idxOf v)
            rw [List.getElem?_eq_getElem (by rw [fresh_consts_for_pure_body_vars_2.property.left]; exact List.idxOf_lt_length_of_mem v_mem_pure_body)] at combined_remapping_on_fresh_is_fresh2
            rw [List.getElem?_eq_getElem (by rw [fresh_consts_for_pure_body_vars.property.left]; exact List.idxOf_lt_length_of_mem v_mem_pure_body)] at combined_remapping_on_fresh_is_fresh2
            simp only [Option.map_some, Option.some.injEq] at combined_remapping_on_fresh_is_fresh2
            rw [combined_remapping_on_fresh_is_fresh2]

      exists combined_remapping
      constructor
      . intro d d_mem
        simp only [backtracking, backtrackFacts] at d_mem
        rw [List.mem_append] at d_mem
        cases Decidable.em (d ∈ fresh_consts_for_pure_body_vars.val) with
        | inl d_mem' => apply False.elim; apply d_mem; apply Or.inl; exact d_mem'
        | inr d_mem' =>
          simp only [combined_remapping, d_mem', ↓reduceDIte]
          apply g_mapped_frontier_h.left
          intro contra; apply d_mem; apply Or.inr; exact contra
      constructor
      . intro e e_mem
        rcases e_mem with ⟨f, f_mem, e_eq⟩
        simp only [List.mem_toSet, backtracking, backtrackFacts] at f_mem
        rw [List.mem_append] at f_mem
        simp only [List.mem_toSet, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, backtrackFacts]
        rw [List.mem_append]
        cases f_mem with
        | inl f_mem =>
          apply Or.inl
          rw [List.mem_append] at f_mem
          rw [List.mem_append]
          cases f_mem with
          | inl f_mem =>
            apply Or.inl
            simp only [trg1, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves] at strong_equiv
            rw [PreTrigger.mapped_body_eq_of_strong_equiv strong_equiv]
            simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list] at f_mem
            simp only [trg2, PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
            rw [List.mem_map] at f_mem
            rcases f_mem with ⟨a, a_mem, f_eq⟩
            rw [List.mem_map]
            exists a
            constructor
            . exact a_mem
            . rw [← GroundSubstitution.apply_function_free_atom.eq_def]
              rw [GroundSubstitution.apply_function_free_atom_compose]
              . rw [e_eq, ← f_eq]
              . intro d d_mem
                have d_mem' : d ∈ rl.rules.flatMap Rule.constants := by
                  rw [List.mem_flatMap]
                  exists rule
                  constructor
                  . apply RuleList.get_by_id_mem
                  . unfold Rule.constants
                    apply List.mem_append_left
                    unfold FunctionFreeConjunction.consts
                    rw [List.mem_flatMap]
                    exists a
                have : d ∉ backtracking.snd := by
                  intro contra
                  apply backtrackFacts_fresh_constants_not_forbidden d contra
                  apply forbidden_constants_subsumes_rules
                  exact d_mem'
                simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, StrictConstantMapping.toConstantMapping]
                simp only [GroundTerm.const, FiniteTree.mapLeaves, Subtype.mk.injEq, FiniteTree.leaf.injEq]
                simp only [this, ↓reduceIte]
                apply g_id
                exact d_mem'
          | inr f_mem =>
            apply Or.inr
            have func_disjIdx_lt : func.disjunctIndex < rule.head.length := term_disjIdx_valid'.left
            rw [← PreTrigger.apply_subs_for_mapped_head_eq _ ⟨func.disjunctIndex, (by rw [PreTrigger.length_mapped_head]; exact func_disjIdx_lt)⟩] at f_mem
            rw [← PreTrigger.apply_subs_for_mapped_head_eq _ ⟨func.disjunctIndex, (by rw [PreTrigger.length_mapped_head]; exact func_disjIdx_lt)⟩]
            simp only [GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list] at f_mem
            simp only [GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
            rw [List.mem_map] at f_mem
            rw [List.mem_map]
            rcases f_mem with ⟨a, a_mem, f_eq⟩
            exists a
            constructor
            . exact a_mem
            . rw [e_eq, ← f_eq]
              rw [← GroundSubstitution.apply_function_free_atom.eq_def, ← GroundSubstitution.apply_function_free_atom.eq_def, PreTrigger.apply_subs_for_atom_eq, PreTrigger.apply_subs_for_atom_eq, ← ConstantMapping.apply_fact.eq_def, ConstantMapping.apply_fact_swap_apply_to_function_free_atom]
              . apply PreTrigger.apply_to_function_free_atom_eq_of_equiv
                apply PreTrigger.equiv_of_strong_equiv
                simp only [trg1, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves] at strong_equiv
                exact strong_equiv
              . intro d d_mem
                have d_mem' : d ∈ rl.rules.flatMap Rule.constants := by
                  rw [List.mem_flatMap]
                  exists rule
                  constructor
                  . apply RuleList.get_by_id_mem
                  . unfold Rule.constants
                    apply List.mem_append_right
                    unfold FunctionFreeConjunction.consts
                    rw [List.mem_flatMap]
                    exists rule.head[func.disjunctIndex]
                    constructor
                    . apply List.getElem_mem
                    . rw [List.mem_flatMap]
                      exists a
                have : d ∉ backtracking.snd := by
                  intro contra
                  apply backtrackFacts_fresh_constants_not_forbidden d contra
                  apply forbidden_constants_subsumes_rules
                  exact d_mem'
                simp only [StrictConstantMapping.toConstantMapping]
                simp only [GroundTerm.const, Subtype.mk.injEq, FiniteTree.leaf.injEq]
                simp only [this, ↓reduceIte]
                apply g_id
                exact d_mem'
        | inr f_mem =>
          apply Or.inr
          rw [← List.mem_toSet]
          have theorem_for_ts := g_mapped_frontier_h.right.left
          rw [List.map_append, new_g_on_forbidden_constants_is_g, new_g_on_fresh_is_fresh2] at theorem_for_ts
          simp only [new_g_on_ts] at theorem_for_ts
          apply theorem_for_ts
          exists f
          constructor
          . rw [List.mem_toSet]; exact f_mem
          . rw [e_eq]
            apply ConstantMapping.apply_fact_congr_left
            intro d d_mem
            cases PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f f_mem d d_mem with
            | inl d_mem =>
              have : d ∉ backtracking.snd := by
                intro contra
                apply backtrackFacts_fresh_constants_not_forbidden d contra
                apply forbidden_constants_subsumes_rules
                exact d_mem
              simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
              simp only [backtracking, backtrackFacts] at this
              rw [List.mem_append] at this
              split
              case isTrue heq => apply False.elim; apply this; apply Or.inr; exact heq
              case isFalse heq =>
                unfold new_g
                split
                case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
                case isFalse heq => rfl
            | inr d_mem =>
              cases d_mem with
              | inl d_mem =>
                have : d ∉ backtracking.snd := by
                  intro contra
                  apply backtrackFacts_fresh_constants_not_forbidden d contra
                  apply forbidden_constants_subsumes_term
                  simp only [FiniteTree.leaves]
                  exact d_mem
                simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
                simp only [backtracking, backtrackFacts] at this
                rw [List.mem_append] at this
                split
                case isTrue heq => apply False.elim; apply this; apply Or.inr; exact heq
                case isFalse heq =>
                  unfold new_g
                  split
                  case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
                  case isFalse heq => rfl
              | inr d_mem =>
                have : d ∈ backtracking.snd := by
                  simp only [backtracking, backtrackFacts]
                  rw [List.mem_append]
                  apply Or.inr
                  exact d_mem
                simp only [PreGroundTerm.backtrackTrigger] at d_mem
                simp only [StrictConstantMapping.toConstantMapping, fresh_consts_for_pure_body_vars, rule, d_mem, this, ↓reduceIte]
                have : d ∉ fresh_consts_for_pure_body_vars.val := by
                  intro contra
                  apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d d_mem
                  rw [List.mem_append]
                  apply Or.inr
                  exact contra
                simp [combined_remapping, this]
      . simp only [backtracking, backtrackFacts, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
        rw [List.map_append]
        apply List.append_eq_append_of_parts_eq
        . simp only [PreGroundTerm.backtrackTrigger]
          rw [combined_remapping_on_fresh_is_fresh2]
        . simp only [PreGroundTerm.backtrackTrigger]
          rw [← new_g_on_fresh_is_fresh2, ← new_g_on_forbidden_constants_is_g, ← List.map_append]
          conv at new_g_on_ts => right; unfold ConstantMapping.apply_pre_ground_term
          simp only [← new_g_on_ts]
          rw [← g_mapped_frontier_h.right.right]
          rw [List.map_inj_left]
          intro d d_mem
          have : d ∉ fresh_consts_for_pure_body_vars.val := by
            intro contra
            apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d d_mem
            rw [List.mem_append]
            apply Or.inr
            exact contra
          simp [combined_remapping, this]

  theorem PreGroundTerm.backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (terms : List (PreGroundTerm sig))
      (terms_arity_ok : ∀ t ∈ terms, PreGroundTerm.arity_ok t)
      (terms_ruleIds_valid : ∀ t ∈ terms, PreGroundTerm.skolem_ruleIds_valid rl t)
      (terms_disjIdx_valid : ∀ t, (t_mem : t ∈ terms) -> PreGroundTerm.skolem_disjIdx_valid rl t (terms_ruleIds_valid t t_mem))
      (terms_rule_arity_valid : ∀ t, (t_mem : t ∈ terms) -> PreGroundTerm.skolem_rule_arity_valid rl t (terms_ruleIds_valid t t_mem))
      (forbidden_constants : List sig.C)
      (forbidden_constants_subsumes_term : terms.flatMap FiniteTree.leaves ⊆ forbidden_constants)
      (forbidden_constants_subsumes_rules : (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants) :
      let backtracking := (backtrackFacts_list rl terms terms_arity_ok terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants)
      ∀ (g : StrictConstantMapping sig), (∀ d, (d ∈ rl.rules.flatMap Rule.constants) -> g d = d) ->
        ∃ (fresh_constant_remapping : StrictConstantMapping sig),
        (∀ d ∉ backtracking.snd, fresh_constant_remapping d = d) ∧
        ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then fresh_constant_remapping c else g c)).apply_fact_set backtracking.fst.toSet ⊆
        (backtrackFacts_list rl (terms.map g.toConstantMapping.apply_pre_ground_term)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; rw [← t_eq]; apply ConstantMapping.apply_pre_ground_term_arity_ok; exact terms_arity_ok _ t'_mem)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; rw [← t_eq]; apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity; exact terms_ruleIds_valid _ t'_mem)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_pre_ground_term_preserves_disjIdx_validity; exact terms_disjIdx_valid _ t'_mem)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity; exact terms_rule_arity_valid _ t'_mem)
          (forbidden_constants.map g)
        ).fst.toSet) ∧
        (backtracking.snd.map fresh_constant_remapping = (backtrackFacts_list rl (terms.map g.toConstantMapping.apply_pre_ground_term)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; rw [← t_eq]; apply ConstantMapping.apply_pre_ground_term_arity_ok; exact terms_arity_ok _ t'_mem)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; rw [← t_eq]; apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity; exact terms_ruleIds_valid _ t'_mem)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_pre_ground_term_preserves_disjIdx_validity; exact terms_disjIdx_valid _ t'_mem)
          (by simp only [List.mem_map]; rintro t ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity; exact terms_rule_arity_valid _ t'_mem)
          (forbidden_constants.map g)
        ).snd) := by
    intro backtracking g g_id
    cases terms with
    | nil =>
      exists id
      constructor
      . simp
      constructor
      . intro e e_mem
        rcases e_mem with ⟨f, f_mem, e_eq⟩
        simp [backtracking, List.mem_toSet, backtrackFacts_list] at f_mem
      . simp only [backtracking, List.map_nil, PreGroundTerm.backtrackFacts_list]
    | cons hd tl =>
      rw [List.flatMap_cons, List.append_subset] at forbidden_constants_subsumes_term
      have hd_arity_ok : PreGroundTerm.arity_ok hd := terms_arity_ok hd (by simp)
      have hd_ruleIds_valid : hd.skolem_ruleIds_valid rl := terms_ruleIds_valid hd (by simp)
      have hd_disjIdx_valid : hd.skolem_disjIdx_valid rl hd_ruleIds_valid := terms_disjIdx_valid hd (by simp)
      have hd_rule_arity_valid : hd.skolem_rule_arity_valid rl hd_ruleIds_valid := terms_rule_arity_valid hd (by simp)

      rcases backtrackFacts_under_constant_mapping_subset_of_composing_with_subs rl hd hd_arity_ok hd_ruleIds_valid hd_disjIdx_valid hd_rule_arity_valid forbidden_constants forbidden_constants_subsumes_term.left forbidden_constants_subsumes_rules g g_id with ⟨g_hd, g_hd_h⟩

      let t_res := PreGroundTerm.backtrackFacts rl hd hd_arity_ok hd_ruleIds_valid hd_disjIdx_valid hd_rule_arity_valid forbidden_constants

      let new_inner_g : StrictConstantMapping sig := fun c => if c ∈ t_res.snd then g_hd c else g c

      rcases backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs rl tl (by intro t t_mem; apply terms_arity_ok; simp [t_mem]) (by intro t t_mem; apply terms_ruleIds_valid; simp [t_mem]) (by intro t t_mem; apply terms_disjIdx_valid; simp [t_mem]) (by intro t t_mem; apply terms_rule_arity_valid; simp [t_mem]) (forbidden_constants ++ t_res.snd) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_term.right) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_rules) new_inner_g
        (by intro d d_mem
            unfold new_inner_g
            have : d ∉ t_res.snd := by
              intro contra
              apply PreGroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
              apply forbidden_constants_subsumes_rules
              exact d_mem
            simp only [this, ↓reduceIte]
            apply g_id
            exact d_mem) with ⟨g_tl, g_tl_h⟩

      let fresh_constant_remapping : StrictConstantMapping sig := fun c => if c ∈ t_res.snd then g_hd c else g_tl c

      have fresh_constant_remapping_is_g_hd_in_t_res : t_res.snd.map fresh_constant_remapping = t_res.snd.map g_hd := by
        rw [List.map_inj_left]
        intro d d_mem
        simp only [fresh_constant_remapping]
        simp [d_mem]
      have new_inner_g_is_g_hd_in_t_res : t_res.snd.map new_inner_g = t_res.snd.map g_hd := by
        rw [List.map_inj_left]
        intro d d_mem
        simp only [new_inner_g]
        simp [d_mem]
      have new_inner_g_on_tl : tl.map (StrictConstantMapping.toConstantMapping new_inner_g).apply_pre_ground_term = tl.map g.toConstantMapping.apply_pre_ground_term := by
        rw [List.map_inj_left]
        intro t t_mem
        apply ConstantMapping.apply_pre_ground_term_congr_left
        intro d d_mem
        simp only [StrictConstantMapping.toConstantMapping, new_inner_g]
        have : d ∉ t_res.snd := by
          intro contra
          apply backtrackFacts_fresh_constants_not_forbidden d contra
          apply forbidden_constants_subsumes_term.right
          rw [List.mem_flatMap]
          exists t
        simp [this]
      have new_inner_g_is_g_on_forbidden_constants : (forbidden_constants.map new_inner_g) = forbidden_constants.map g := by
        rw [List.map_inj_left]
        intro d d_mem
        unfold new_inner_g
        have : d ∉ t_res.snd := by
          intro contra
          apply backtrackFacts_fresh_constants_not_forbidden d contra
          exact d_mem
        simp [this]


      exists fresh_constant_remapping
      constructor
      . intro d d_nmem
        unfold fresh_constant_remapping
        cases Decidable.em (d ∈ t_res.snd) with
        | inl d_mem =>
          simp only [d_mem]
          apply g_hd_h.left
          intro contra
          apply d_nmem
          simp only [backtracking, PreGroundTerm.backtrackFacts_list_cons]
          rw [List.mem_append]
          apply Or.inl
          exact contra
        | inr d_mem =>
          simp only [d_mem, ↓reduceIte]
          apply g_tl_h.left
          intro contra
          apply d_nmem
          simp only [backtracking, PreGroundTerm.backtrackFacts_list_cons]
          rw [List.mem_append]
          apply Or.inr
          exact contra
      constructor
      . intro e e_mem
        rcases e_mem with ⟨f, f_mem, e_eq⟩
        simp only [backtracking, List.mem_toSet, backtrackFacts_list, List.mem_append] at f_mem
        simp only [List.map_cons, List.mem_toSet, backtrackFacts_list, List.mem_append]
        cases f_mem with
        | inl f_mem =>
          apply Or.inl
          rw [← List.mem_toSet]
          apply g_hd_h.right.left
          exists f
          constructor
          . rw [List.mem_toSet]; exact f_mem
          . rw [e_eq]
            apply ConstantMapping.apply_fact_congr_left
            intro d d_mem
            cases PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh f f_mem d d_mem with
            | inl d_mem =>
              have : d ∉ backtracking.snd := by
                intro contra
                apply backtrackFacts_list_fresh_constants_not_forbidden d contra
                apply forbidden_constants_subsumes_rules
                exact d_mem
              simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
              simp only [backtracking, backtrackFacts_list] at this
              rw [List.mem_append] at this
              split
              case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
              case isFalse heq => rfl
            | inr d_mem =>
              cases d_mem with
              | inl d_mem =>
                have : d ∉ backtracking.snd := by
                  intro contra
                  apply backtrackFacts_list_fresh_constants_not_forbidden d contra
                  apply forbidden_constants_subsumes_term.left
                  exact d_mem
                simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
                simp only [backtracking, backtrackFacts_list] at this
                rw [List.mem_append] at this
                split
                case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
                case isFalse heq => rfl
              | inr d_mem =>
                have : d ∈ backtracking.snd := by
                  simp only [backtracking, backtrackFacts_list]
                  rw [List.mem_append]
                  apply Or.inl
                  exact d_mem
                simp only [StrictConstantMapping.toConstantMapping, fresh_constant_remapping, t_res, d_mem, this, ↓reduceIte]
        | inr f_mem =>
          apply Or.inr
          have inner_ih := g_tl_h.right.left

          rw [List.map_append, new_inner_g_is_g_hd_in_t_res, new_inner_g_is_g_on_forbidden_constants, g_hd_h.right.right] at inner_ih
          simp only [new_inner_g_on_tl] at inner_ih
          rw [← List.mem_toSet]
          apply inner_ih
          exists f
          constructor
          . rw [List.mem_toSet]; exact f_mem
          . rw [e_eq]
            apply ConstantMapping.apply_fact_congr_left
            intro d d_mem
            cases PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f f_mem d d_mem with
            | inl d_mem =>
              have : d ∉ backtracking.snd := by
                intro contra
                apply backtrackFacts_list_fresh_constants_not_forbidden d contra
                apply forbidden_constants_subsumes_rules
                exact d_mem
              simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
              simp only [backtracking, backtrackFacts_list] at this
              rw [List.mem_append] at this
              split
              case isTrue heq => apply False.elim; apply this; apply Or.inr; exact heq
              case isFalse heq =>
                unfold new_inner_g
                split
                case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
                case isFalse heq => rfl
            | inr d_mem =>
              cases d_mem with
              | inl d_mem =>
                have : d ∉ backtracking.snd := by
                  intro contra
                  apply backtrackFacts_list_fresh_constants_not_forbidden d contra
                  apply forbidden_constants_subsumes_term.right
                  exact d_mem
                simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
                simp only [backtracking, backtrackFacts_list] at this
                rw [List.mem_append] at this
                split
                case isTrue heq => apply False.elim; apply this; apply Or.inr; exact heq
                case isFalse heq =>
                  unfold new_inner_g
                  split
                  case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
                  case isFalse heq => rfl
              | inr d_mem =>
                have : d ∈ backtracking.snd := by
                  simp only [backtracking, backtrackFacts_list]
                  rw [List.mem_append]
                  apply Or.inr
                  exact d_mem
                simp only [StrictConstantMapping.toConstantMapping, t_res, d_mem, this, ↓reduceIte]
                have : d ∉ t_res.snd := by
                  intro contra
                  apply backtrackFacts_list_fresh_constants_not_forbidden d d_mem
                  rw [List.mem_append]
                  apply Or.inr
                  exact contra
                simp [fresh_constant_remapping, this]
      . simp only [backtracking, List.map_cons, List.map_append, PreGroundTerm.backtrackFacts_list_cons]
        apply List.append_eq_append_of_parts_eq
        . rw [← g_hd_h.right.right]
          exact fresh_constant_remapping_is_g_hd_in_t_res
        . rw [← g_hd_h.right.right]
          rw [← fresh_constant_remapping_is_g_hd_in_t_res]
          rw [← new_inner_g_is_g_on_forbidden_constants, fresh_constant_remapping_is_g_hd_in_t_res, ← new_inner_g_is_g_hd_in_t_res, ← List.map_append]
          simp only [← new_inner_g_on_tl]
          rw [← g_tl_h.right.right, List.map_inj_left]
          intro d d_mem
          have : d ∉ t_res.snd := by
            intro contra
            apply backtrackFacts_list_fresh_constants_not_forbidden d d_mem
            rw [List.mem_append]
            apply Or.inr
            exact contra
          simp [fresh_constant_remapping, this]

end

