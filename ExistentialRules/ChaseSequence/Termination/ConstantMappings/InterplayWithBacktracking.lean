import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts
import ExistentialRules.ChaseSequence.Termination.ConstantMappings.Basic

section InterplayWithBacktracking

  variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

  mutual

    theorem PreGroundTerm.backtrackFacts_under_strict_constant_mapping_same_number_of_fresh_constants
        [GetFreshInhabitant sig.C]
        [Inhabited sig.C]
        (rl : RuleList sig)
        (term : FiniteTree (SkolemFS sig) sig.C)
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
        rw [Nat.add_left_inj]
        rw [backtrackFacts_list_under_strict_constant_mapping_same_number_of_fresh_constants]

    theorem PreGroundTerm.backtrackFacts_list_under_strict_constant_mapping_same_number_of_fresh_constants
        [GetFreshInhabitant sig.C]
        [Inhabited sig.C]
        (rl : RuleList sig)
        (terms : FiniteTreeList (SkolemFS sig) sig.C)
        (terms_arity_ok : PreGroundTerm.arity_ok_list terms)
        (terms_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl terms)
        (terms_disjIdx_valid : PreGroundTerm.skolem_disjIdx_valid_list rl terms terms_ruleIds_valid)
        (terms_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid_list rl terms terms_ruleIds_valid)
        (forbidden_constants forbidden_constants_2 : List sig.C) :
        ∀ (g : StrictConstantMapping sig),
          (PreGroundTerm.backtrackFacts_list rl terms terms_arity_ok terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).snd.length =
          (PreGroundTerm.backtrackFacts_list rl (FiniteTree.mapLeavesList (fun c => (g.toConstantMapping c).val) terms)
            (by apply ConstantMapping.apply_pre_ground_term_list_arity_ok; exact terms_arity_ok)
            (by have : (FiniteTreeList.fromList (FiniteTreeList.toList terms)) = terms := by rw [FiniteTreeList.toListFromListIsId]
                rw [← this, FiniteTree.mapLeavesList_fromList_eq_fromList_map]
                apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity_list; exact terms_ruleIds_valid)
            (by have : (FiniteTreeList.fromList (FiniteTreeList.toList terms)) = terms := by rw [FiniteTreeList.toListFromListIsId]
                conv => left; right; rw [← this]
                simp only [FiniteTree.mapLeavesList_fromList_eq_fromList_map]
                apply StrictConstantMapping.apply_pre_ground_term_preserves_disjIdx_validity_list; exact terms_disjIdx_valid)
            (by have : (FiniteTreeList.fromList (FiniteTreeList.toList terms)) = terms := by rw [FiniteTreeList.toListFromListIsId]
                conv => left; right; rw [← this]
                simp only [FiniteTree.mapLeavesList_fromList_eq_fromList_map]
                apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity_list; exact terms_rule_arity_valid)
            forbidden_constants_2).snd.length := by
      intro g
      cases terms with
      | nil => simp only [backtrackFacts_list, FiniteTree.mapLeavesList]
      | cons hd tl =>
        simp only [backtrackFacts_list, FiniteTree.mapLeavesList]
        rw [List.length_append, List.length_append]
        rw [backtrackFacts_under_strict_constant_mapping_same_number_of_fresh_constants]
        simp only [ConstantMapping.apply_pre_ground_term]
        rw [backtrackFacts_list_under_strict_constant_mapping_same_number_of_fresh_constants]
  end

  theorem GroundTerm.backtrackFacts_under_constant_mapping_exists_fresh_constant_remapping
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (term : GroundTerm sig)
      (term_ruleIds_valid : term.skolem_ruleIds_valid rl)
      (term_disjIdx_valid : term.skolem_disjIdx_valid rl term_ruleIds_valid)
      (term_rule_arity_valid : term.skolem_rule_arity_valid rl term_ruleIds_valid)
      (forbidden_constants : List sig.C)
      (forbidden_constants_subsumes_term : term.constants ⊆ forbidden_constants) :
      let backtracking := (backtrackFacts rl term term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants)
      ∀ (g : StrictConstantMapping sig),
        ∃ (fresh_constant_remapping : StrictConstantMapping sig),
        (∀ d ∉ backtracking.snd, fresh_constant_remapping d = d) ∧ -- Is this first condition even required?!
        (backtracking.snd.map fresh_constant_remapping = (backtrackFacts rl (g.toConstantMapping.apply_ground_term term)
          (by apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity; exact term_ruleIds_valid)
          (by apply StrictConstantMapping.apply_ground_term_preserves_disjIdx_validity; exact term_disjIdx_valid)
          (by apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity; exact term_rule_arity_valid)
          (forbidden_constants.map g)
        ).snd) := by
    intro backtracking g
    induction term generalizing forbidden_constants g with
    | const c =>
      exists id
      constructor
      . simp
      . simp only [ConstantMapping.apply_ground_term_constant]
        simp only [backtracking, backtrackFacts, PreGroundTerm.backtrackFacts, const, StrictConstantMapping.toConstantMapping]
        simp
    | func func ts arity_ok ih =>
      have : ∀ sublist, (sub : sublist ⊆ ts) -> ∀ forbidden_constants, (sublist.flatMap GroundTerm.constants ⊆ forbidden_constants) ->
          let inner_backtracking := (PreGroundTerm.backtrackFacts_list rl (FiniteTreeList.fromList sublist.unattach)
            (by rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]; intro t t_mem; rw [FiniteTreeList.fromListToListIsId, List.mem_unattach] at t_mem; rcases t_mem with ⟨h, _⟩; exact h)
            (by have := term_ruleIds_valid.right
                rw [GroundTerm.skolem_ruleIds_valid_list] at this
                rw [GroundTerm.skolem_ruleIds_valid_list]
                intro t t_mem
                apply this
                apply sub
                exact t_mem)
            (by have := term_disjIdx_valid.right
                rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
                rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by
                  have := term_ruleIds_valid.right
                  rw [GroundTerm.skolem_ruleIds_valid_list] at this
                  intro t t_mem
                  apply this
                  apply sub
                  exact t_mem
                )]
                intro t t_mem
                apply this
                apply sub
                exact t_mem)
            (by have := term_rule_arity_valid.right
                rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
                rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by
                  have := term_ruleIds_valid.right
                  rw [GroundTerm.skolem_ruleIds_valid_list] at this
                  intro t t_mem
                  apply this
                  apply sub
                  exact t_mem
                )]
                intro t t_mem
                apply this
                apply sub
                exact t_mem)
            forbidden_constants)
          ∀ (inner_g : StrictConstantMapping sig),
            ∃ (fresh_constant_remapping : StrictConstantMapping sig),
            (∀ d ∉ inner_backtracking.snd, fresh_constant_remapping d = d) ∧
            (inner_backtracking.snd.map fresh_constant_remapping =
              (PreGroundTerm.backtrackFacts_list rl (sublist.unattach.map inner_g.toConstantMapping.apply_pre_ground_term)
                (by rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]; intro t t_mem; rw [FiniteTreeList.fromListToListIsId, List.mem_map] at t_mem; rcases t_mem with ⟨s, s_mem, t_eq⟩; rw [← t_eq]; apply ConstantMapping.apply_pre_ground_term_arity_ok; rw [List.mem_unattach] at s_mem; rcases s_mem with ⟨h, _⟩; exact h)
                (by have : (FiniteTreeList.toList (FiniteTreeList.fromList sublist.unattach)) = sublist.unattach := by rw [FiniteTreeList.fromListToListIsId]
                    rw [← this]
                    apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity_list
                    have := term_ruleIds_valid.right
                    rw [GroundTerm.skolem_ruleIds_valid_list] at this
                    rw [GroundTerm.skolem_ruleIds_valid_list]
                    intro t t_mem
                    apply this
                    apply sub
                    exact t_mem)
                (by have ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList sublist.unattach) := by
                      have := term_ruleIds_valid.right
                      rw [GroundTerm.skolem_ruleIds_valid_list] at this
                      rw [GroundTerm.skolem_ruleIds_valid_list]
                      intro t t_mem
                      apply this
                      apply sub
                      exact t_mem

                    have : (FiniteTreeList.toList (FiniteTreeList.fromList sublist.unattach)) = sublist.unattach := by rw [FiniteTreeList.fromListToListIsId]
                    conv => left; rw [← this]
                    apply StrictConstantMapping.apply_pre_ground_term_preserves_disjIdx_validity_list _ _ _ ruleIds_valid
                    have := term_disjIdx_valid.right
                    rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
                    rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [GroundTerm.skolem_ruleIds_valid_list] at ruleIds_valid; exact ruleIds_valid)]
                    intro t t_mem
                    apply this
                    apply sub
                    exact t_mem)
                (by have ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList sublist.unattach) := by
                      have := term_ruleIds_valid.right
                      rw [GroundTerm.skolem_ruleIds_valid_list] at this
                      rw [GroundTerm.skolem_ruleIds_valid_list]
                      intro t t_mem
                      apply this
                      apply sub
                      exact t_mem

                    have : (FiniteTreeList.toList (FiniteTreeList.fromList sublist.unattach)) = sublist.unattach := by rw [FiniteTreeList.fromListToListIsId]
                    conv => left; rw [← this]
                    apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity_list _ _ _ ruleIds_valid
                    have := term_rule_arity_valid.right
                    rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
                    rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [GroundTerm.skolem_ruleIds_valid_list] at ruleIds_valid; exact ruleIds_valid)]
                    intro t t_mem
                    apply this
                    apply sub
                    exact t_mem)
                (forbidden_constants.map inner_g)
              ).snd) := by
        intro sublist sub forbidden_constants forbidden_constants_subsumes_term inner_backtracking inner_g
        induction sublist generalizing forbidden_constants inner_g with
        | nil =>
          exists id
          constructor
          . simp
          . simp only [inner_backtracking, List.unattach_nil, List.map_nil, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list]
        | cons hd tl inner_ih =>
          rw [List.flatMap_cons, List.append_subset] at forbidden_constants_subsumes_term
          have hd_ruleIds_valid : hd.skolem_ruleIds_valid rl := by
            have := term_ruleIds_valid.right
            rw [GroundTerm.skolem_ruleIds_valid_list] at this
            apply this
            exact (List.cons_subset.mp sub).left
          have hd_disjIdx_valid : hd.skolem_disjIdx_valid rl hd_ruleIds_valid := by
            have := term_disjIdx_valid.right
            rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
            apply this
            exact (List.cons_subset.mp sub).left
          have hd_rule_arity_valid : hd.skolem_rule_arity_valid rl hd_ruleIds_valid := by
            have := term_rule_arity_valid.right
            rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
            apply this
            exact (List.cons_subset.mp sub).left

          rcases ih hd (by rw [List.cons_subset] at sub; exact sub.left) hd_ruleIds_valid hd_disjIdx_valid hd_rule_arity_valid forbidden_constants forbidden_constants_subsumes_term.left inner_g with ⟨g_hd, g_hd_h⟩

          let t_res := PreGroundTerm.backtrackFacts rl hd.val hd.property hd_ruleIds_valid hd_disjIdx_valid hd_rule_arity_valid forbidden_constants

          let new_inner_g : StrictConstantMapping sig := fun c => if c ∈ t_res.snd then g_hd c else inner_g c

          rcases inner_ih (by apply List.subset_of_cons_subset; exact sub) (forbidden_constants ++ t_res.snd) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_term.right) new_inner_g with ⟨g_tl, g_tl_h⟩

          let fresh_constant_remapping : StrictConstantMapping sig := fun c => if c ∈ t_res.snd then g_hd c else g_tl c

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
              simp only [inner_backtracking, List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list]
              rw [List.mem_append]
              apply Or.inl
              exact contra
            | inr d_mem =>
              simp only [d_mem, ↓reduceIte]
              apply g_tl_h.left
              intro contra
              apply d_nmem
              simp only [inner_backtracking, List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list]
              rw [List.mem_append]
              apply Or.inr
              exact contra
          . simp only [inner_backtracking, List.unattach_cons, List.map_cons, List.map_append, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list]
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
            apply List.append_eq_append_of_parts_eq
            . have := g_hd_h.right
              simp only [backtrackFacts, ConstantMapping.apply_ground_term] at this
              rw [← this]
              exact fresh_constant_remapping_is_g_hd_in_t_res
            . have := g_hd_h.right
              simp only [backtrackFacts, ConstantMapping.apply_ground_term] at this
              rw [← this]
              rw [← fresh_constant_remapping_is_g_hd_in_t_res]
              have : (forbidden_constants.map new_inner_g) = forbidden_constants.map inner_g := by
                rw [List.map_inj_left]
                intro d d_mem
                unfold new_inner_g
                have : d ∉ t_res.snd := by
                  intro contra
                  apply GroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
                  exact d_mem
                simp [this]
              rw [← this, fresh_constant_remapping_is_g_hd_in_t_res, ← new_inner_g_is_g_hd_in_t_res, ← List.map_append]
              have : tl.unattach.map (StrictConstantMapping.toConstantMapping new_inner_g).apply_pre_ground_term = tl.unattach.map inner_g.toConstantMapping.apply_pre_ground_term := by
                rw [List.map_inj_left]
                intro t t_mem
                apply ConstantMapping.apply_pre_ground_term_congr_left
                intro d d_mem
                simp only [StrictConstantMapping.toConstantMapping, new_inner_g]
                have : d ∉ t_res.snd := by
                  intro contra
                  apply GroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
                  apply forbidden_constants_subsumes_term.right
                  rw [List.mem_unattach] at t_mem
                  rcases t_mem with ⟨h, t_mem⟩
                  rw [List.mem_flatMap]
                  exists ⟨t, h⟩
                simp [this]
              simp only [← this]
              rw [← g_tl_h.right, List.map_inj_left]
              intro d d_mem
              have : d ∉ t_res.snd := by
                have := PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d d_mem
                intro contra
                apply this
                rw [List.mem_append]
                apply Or.inr
                exact contra
              simp [fresh_constant_remapping, this]

      let rule := rl.get_by_id func.ruleId term_ruleIds_valid.left
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

      rcases this ts (by simp) (forbidden_constants ++ fresh_consts_for_pure_body_vars) (by apply List.subset_append_of_subset_left; rw [GroundTerm.constants_func] at forbidden_constants_subsumes_term; exact forbidden_constants_subsumes_term) new_g with ⟨g_mapped_frontier, g_mapped_frontier_h⟩

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

      exists combined_remapping
      constructor
      . intro d d_mem
        simp only [backtracking, backtrackFacts, GroundTerm.func, PreGroundTerm.backtrackFacts] at d_mem
        rw [List.mem_append] at d_mem
        cases Decidable.em (d ∈ fresh_consts_for_pure_body_vars.val) with
        | inl d_mem' => apply False.elim; apply d_mem; apply Or.inr; exact d_mem'
        | inr d_mem' =>
          simp only [combined_remapping, d_mem', ↓reduceDIte]
          apply g_mapped_frontier_h.left
          intro contra; apply d_mem; apply Or.inl; exact contra
      . simp only [backtracking, backtrackFacts, GroundTerm.func, PreGroundTerm.backtrackFacts, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
        rw [List.map_append]
        apply List.append_eq_append_of_parts_eq
        . simp only [FiniteTree.mapLeavesList_fromList_eq_fromList_map]
          simp only [PreGroundTerm.backtrackTrigger]
          rw [← new_g_on_fresh_is_fresh2, ← new_g_on_forbidden_constants_is_g, ← List.map_append]
          have : (List.map new_g.toConstantMapping.apply_pre_ground_term ts.unattach) = (List.map g.toConstantMapping.apply_pre_ground_term ts.unattach) := by
            rw [List.map_inj_left]
            intro t t_mem
            apply ConstantMapping.apply_pre_ground_term_congr_left
            intro d d_mem
            simp only [StrictConstantMapping.toConstantMapping, new_g]
            have : d ∉ fresh_consts_for_pure_body_vars.val := by
              intro contra
              apply fresh_consts_for_pure_body_vars.property.right.right d contra
              apply forbidden_constants_subsumes_term
              rw [List.mem_unattach] at t_mem
              rcases t_mem with ⟨h, t_mem⟩
              rw [GroundTerm.constants_func]
              rw [List.mem_flatMap]
              exists ⟨t, h⟩
            simp [this]
          conv at this => right; unfold ConstantMapping.apply_pre_ground_term
          simp only [← this]
          rw [← g_mapped_frontier_h.right]
          rw [List.map_inj_left]
          intro d d_mem
          have : d ∉ fresh_consts_for_pure_body_vars.val := by
            intro contra
            apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d d_mem
            rw [List.mem_append]
            apply Or.inr
            exact contra
          simp [combined_remapping, this]
        . simp only [PreGroundTerm.backtrackTrigger]
          rw [combined_remapping_on_fresh_is_fresh2]

  theorem GroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (term : GroundTerm sig)
      (term_ruleIds_valid : term.skolem_ruleIds_valid rl)
      (term_disjIdx_valid : term.skolem_disjIdx_valid rl term_ruleIds_valid)
      (term_rule_arity_valid : term.skolem_rule_arity_valid rl term_ruleIds_valid)
      (forbidden_constants : List sig.C)
      (forbidden_constants_subsumes_term : term.constants ⊆ forbidden_constants)
      (forbidden_constants_subsumes_rules : (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants) :
      let backtracking := (backtrackFacts rl term term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants)
      ∀ (g : StrictConstantMapping sig), (∀ d, (d ∈ rl.rules.flatMap Rule.constants) -> g d = d) ->
        ∀ (fresh_constant_remapping : StrictConstantMapping sig),
        (backtracking.snd.map fresh_constant_remapping = (backtrackFacts rl (g.toConstantMapping.apply_ground_term term)
          (by apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity; exact term_ruleIds_valid)
          (by apply StrictConstantMapping.apply_ground_term_preserves_disjIdx_validity; exact term_disjIdx_valid)
          (by apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity; exact term_rule_arity_valid)
          (forbidden_constants.map g)
        ).snd) ->
        ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then fresh_constant_remapping c else g c)).apply_fact_set backtracking.fst.toSet ⊆
        (backtrackFacts rl (g.toConstantMapping.apply_ground_term term)
          (by apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity; exact term_ruleIds_valid)
          (by apply StrictConstantMapping.apply_ground_term_preserves_disjIdx_validity; exact term_disjIdx_valid)
          (by apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity; exact term_rule_arity_valid)
          (forbidden_constants.map g)
        ).fst.toSet) := by
    intro backtracking g g_id fresh_constant_remapping fresh_constant_remapping_h
    induction term generalizing forbidden_constants g fresh_constant_remapping with
    | const c =>
      intro e e_mem
      rcases e_mem with ⟨f, f_mem, e_eq⟩
      simp [List.mem_toSet, backtracking, backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.const] at f_mem
    | func func ts arity_ok ih =>
      have theorem_for_ts : ∀ sublist, (sub : sublist ⊆ ts) -> ∀ forbidden_constants, (sublist.flatMap GroundTerm.constants ⊆ forbidden_constants) -> (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants ->
        let inner_backtracking := (PreGroundTerm.backtrackFacts_list rl (FiniteTreeList.fromList sublist.unattach)
          (by rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]; intro t t_mem; rw [FiniteTreeList.fromListToListIsId, List.mem_unattach] at t_mem; rcases t_mem with ⟨h, _⟩; exact h)
          (by have := term_ruleIds_valid.right
              rw [GroundTerm.skolem_ruleIds_valid_list] at this
              rw [GroundTerm.skolem_ruleIds_valid_list]
              intro t t_mem
              apply this
              apply sub
              exact t_mem)
          (by have := term_disjIdx_valid.right
              rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
              rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by
                have := term_ruleIds_valid.right
                rw [GroundTerm.skolem_ruleIds_valid_list] at this
                intro t t_mem
                apply this
                apply sub
                exact t_mem
              )]
              intro t t_mem
              apply this
              apply sub
              exact t_mem)
          (by have := term_rule_arity_valid.right
              rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
              rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by
                have := term_ruleIds_valid.right
                rw [GroundTerm.skolem_ruleIds_valid_list] at this
                intro t t_mem
                apply this
                apply sub
                exact t_mem
              )]
              intro t t_mem
              apply this
              apply sub
              exact t_mem)
          forbidden_constants)
        ∀ (inner_g : StrictConstantMapping sig), (∀ d, (d ∈ rl.rules.flatMap Rule.constants) -> inner_g d = d) ->
        ∀ (fresh_constant_remapping : StrictConstantMapping sig),
          (inner_backtracking.snd.map fresh_constant_remapping =
            (PreGroundTerm.backtrackFacts_list rl (sublist.unattach.map inner_g.toConstantMapping.apply_pre_ground_term)
              (by rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]; intro t t_mem; rw [FiniteTreeList.fromListToListIsId, List.mem_map] at t_mem; rcases t_mem with ⟨s, s_mem, t_eq⟩; rw [← t_eq]; apply ConstantMapping.apply_pre_ground_term_arity_ok; rw [List.mem_unattach] at s_mem; rcases s_mem with ⟨h, _⟩; exact h)
              (by have : (FiniteTreeList.toList (FiniteTreeList.fromList sublist.unattach)) = sublist.unattach := by rw [FiniteTreeList.fromListToListIsId]
                  rw [← this]
                  apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity_list
                  have := term_ruleIds_valid.right
                  rw [GroundTerm.skolem_ruleIds_valid_list] at this
                  rw [GroundTerm.skolem_ruleIds_valid_list]
                  intro t t_mem
                  apply this
                  apply sub
                  exact t_mem)
              (by have ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList sublist.unattach) := by
                    have := term_ruleIds_valid.right
                    rw [GroundTerm.skolem_ruleIds_valid_list] at this
                    rw [GroundTerm.skolem_ruleIds_valid_list]
                    intro t t_mem
                    apply this
                    apply sub
                    exact t_mem

                  have : (FiniteTreeList.toList (FiniteTreeList.fromList sublist.unattach)) = sublist.unattach := by rw [FiniteTreeList.fromListToListIsId]
                  conv => left; rw [← this]
                  apply StrictConstantMapping.apply_pre_ground_term_preserves_disjIdx_validity_list _ _ _ ruleIds_valid
                  have := term_disjIdx_valid.right
                  rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
                  rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [GroundTerm.skolem_ruleIds_valid_list] at ruleIds_valid; exact ruleIds_valid)]
                  intro t t_mem
                  apply this
                  apply sub
                  exact t_mem)
              (by have ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList sublist.unattach) := by
                    have := term_ruleIds_valid.right
                    rw [GroundTerm.skolem_ruleIds_valid_list] at this
                    rw [GroundTerm.skolem_ruleIds_valid_list]
                    intro t t_mem
                    apply this
                    apply sub
                    exact t_mem

                  have : (FiniteTreeList.toList (FiniteTreeList.fromList sublist.unattach)) = sublist.unattach := by rw [FiniteTreeList.fromListToListIsId]
                  conv => left; rw [← this]
                  apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity_list _ _ _ ruleIds_valid
                  have := term_rule_arity_valid.right
                  rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
                  rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [GroundTerm.skolem_ruleIds_valid_list] at ruleIds_valid; exact ruleIds_valid)]
                  intro t t_mem
                  apply this
                  apply sub
                  exact t_mem)
              (forbidden_constants.map inner_g)
            ).snd) ->
          ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ inner_backtracking.snd then fresh_constant_remapping c else inner_g c)).apply_fact_set inner_backtracking.fst.toSet ⊆
            (PreGroundTerm.backtrackFacts_list rl (sublist.unattach.map inner_g.toConstantMapping.apply_pre_ground_term)
              (by rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]; intro t t_mem; rw [FiniteTreeList.fromListToListIsId, List.mem_map] at t_mem; rcases t_mem with ⟨s, s_mem, t_eq⟩; rw [← t_eq]; apply ConstantMapping.apply_pre_ground_term_arity_ok; rw [List.mem_unattach] at s_mem; rcases s_mem with ⟨h, _⟩; exact h)
              (by have : (FiniteTreeList.toList (FiniteTreeList.fromList sublist.unattach)) = sublist.unattach := by rw [FiniteTreeList.fromListToListIsId]
                  rw [← this]
                  apply StrictConstantMapping.apply_pre_ground_term_preserves_ruleId_validity_list
                  have := term_ruleIds_valid.right
                  rw [GroundTerm.skolem_ruleIds_valid_list] at this
                  rw [GroundTerm.skolem_ruleIds_valid_list]
                  intro t t_mem
                  apply this
                  apply sub
                  exact t_mem)
              (by have ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList sublist.unattach) := by
                    have := term_ruleIds_valid.right
                    rw [GroundTerm.skolem_ruleIds_valid_list] at this
                    rw [GroundTerm.skolem_ruleIds_valid_list]
                    intro t t_mem
                    apply this
                    apply sub
                    exact t_mem

                  have : (FiniteTreeList.toList (FiniteTreeList.fromList sublist.unattach)) = sublist.unattach := by rw [FiniteTreeList.fromListToListIsId]
                  conv => left; rw [← this]
                  apply StrictConstantMapping.apply_pre_ground_term_preserves_disjIdx_validity_list _ _ _ ruleIds_valid
                  have := term_disjIdx_valid.right
                  rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
                  rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [GroundTerm.skolem_ruleIds_valid_list] at ruleIds_valid; exact ruleIds_valid)]
                  intro t t_mem
                  apply this
                  apply sub
                  exact t_mem)
              (by have ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList sublist.unattach) := by
                    have := term_ruleIds_valid.right
                    rw [GroundTerm.skolem_ruleIds_valid_list] at this
                    rw [GroundTerm.skolem_ruleIds_valid_list]
                    intro t t_mem
                    apply this
                    apply sub
                    exact t_mem

                  have : (FiniteTreeList.toList (FiniteTreeList.fromList sublist.unattach)) = sublist.unattach := by rw [FiniteTreeList.fromListToListIsId]
                  conv => left; rw [← this]
                  apply StrictConstantMapping.apply_pre_ground_term_preserves_rule_arity_validity_list _ _ _ ruleIds_valid
                  have := term_rule_arity_valid.right
                  rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
                  rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [GroundTerm.skolem_ruleIds_valid_list] at ruleIds_valid; exact ruleIds_valid)]
                  intro t t_mem
                  apply this
                  apply sub
                  exact t_mem)
              (forbidden_constants.map inner_g)
            ).fst.toSet) := by
        intro sublist sub forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules inner_backtracking inner_g inner_g_id fresh_constant_remapping fresh_constant_remapping_h
        induction sublist generalizing forbidden_constants inner_g with
        | nil =>
          intro e e_mem
          rcases e_mem with ⟨f, f_mem, e_eq⟩
          simp [inner_backtracking, List.unattach_nil, List.mem_toSet, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list] at f_mem
        | cons hd tl inner_ih =>
          rw [List.flatMap_cons, List.append_subset] at forbidden_constants_subsumes_term

          simp only [inner_backtracking, List.unattach_cons, List.map_cons, List.map_append, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list] at fresh_constant_remapping_h
          have fresh_constant_remapping_h := List.append_args_eq_of_append_eq_of_same_length (by rw [List.length_map, PreGroundTerm.backtrackFacts_under_strict_constant_mapping_same_number_of_fresh_constants]) fresh_constant_remapping_h

          have hd_ruleIds_valid : hd.skolem_ruleIds_valid rl := by
            have := term_ruleIds_valid.right
            rw [GroundTerm.skolem_ruleIds_valid_list] at this
            apply this
            exact (List.cons_subset.mp sub).left
          have hd_disjIdx_valid : hd.skolem_disjIdx_valid rl hd_ruleIds_valid := by
            have := term_disjIdx_valid.right
            rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
            apply this
            exact (List.cons_subset.mp sub).left
          have hd_rule_arity_valid : hd.skolem_rule_arity_valid rl hd_ruleIds_valid := by
            have := term_rule_arity_valid.right
            rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact term_ruleIds_valid.right)] at this
            apply this
            exact (List.cons_subset.mp sub).left

          let t_res := PreGroundTerm.backtrackFacts rl hd.val hd.property hd_ruleIds_valid hd_disjIdx_valid hd_rule_arity_valid forbidden_constants

          intro e e_mem
          rcases e_mem with ⟨f, f_mem, e_eq⟩
          simp only [inner_backtracking, List.unattach_cons, List.mem_toSet, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list, List.mem_append] at f_mem
          simp only [List.map_cons, List.unattach_cons, List.mem_toSet, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list, List.mem_append]
          cases f_mem with
          | inl f_mem =>
            apply Or.inl
            specialize ih hd (by apply sub; simp) hd_ruleIds_valid hd_disjIdx_valid hd_rule_arity_valid forbidden_constants forbidden_constants_subsumes_term.left forbidden_constants_subsumes_rules inner_g inner_g_id (fun c => if c ∈ t_res.snd then fresh_constant_remapping c else c)
              (by have : t_res.snd.map (fun c => if c ∈ t_res.snd then fresh_constant_remapping c else c) = t_res.snd.map fresh_constant_remapping := by
                    rw [List.map_inj_left]
                    intro d d_mem
                    simp [d_mem]
                  unfold backtrackFacts
                  rw [this]
                  rw [fresh_constant_remapping_h.left]
                  rfl)
            rw [← List.mem_toSet]
            apply ih
            exists f
            constructor
            . rw [List.mem_toSet]; exact f_mem
            . rw [e_eq]
              apply ConstantMapping.apply_fact_congr_left
              intro d d_mem
              cases PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh f f_mem d d_mem with
              | inl d_mem =>
                have : d ∉ inner_backtracking.snd := by
                  intro contra
                  apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d contra
                  apply forbidden_constants_subsumes_rules
                  exact d_mem
                simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
                simp only [inner_backtracking, List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list] at this
                rw [List.mem_append] at this
                split
                case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
                case isFalse heq => rfl
              | inr d_mem =>
                cases d_mem with
                | inl d_mem =>
                  have : d ∉ inner_backtracking.snd := by
                    intro contra
                    apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d contra
                    apply forbidden_constants_subsumes_term.left
                    exact d_mem
                  simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
                  simp only [inner_backtracking, List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list] at this
                  rw [List.mem_append] at this
                  split
                  case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
                  case isFalse heq => rfl
                | inr d_mem =>
                  have : d ∈ inner_backtracking.snd := by
                    simp only [inner_backtracking, List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list]
                    rw [List.mem_append]
                    apply Or.inl
                    exact d_mem
                  simp only [StrictConstantMapping.toConstantMapping, backtrackFacts, t_res, d_mem, this, ↓reduceIte]
          | inr f_mem =>
            apply Or.inr

            let new_inner_g : StrictConstantMapping sig := fun c => if c ∈ t_res.snd then fresh_constant_remapping c else inner_g c

            have new_inner_g_is_fresh_constant_remapping_in_t_res : t_res.snd.map new_inner_g = t_res.snd.map fresh_constant_remapping := by
              rw [List.map_inj_left]
              intro d d_mem
              simp only [new_inner_g]
              simp [d_mem]

            have new_inner_g_is_inner_g_on_forbidden_constants : (forbidden_constants.map new_inner_g) = forbidden_constants.map inner_g := by
              rw [List.map_inj_left]
              intro d d_mem
              unfold new_inner_g
              have : d ∉ t_res.snd := by
                intro contra
                apply GroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
                exact d_mem
              simp [this]

            have new_inner_g_on_tl : tl.unattach.map (StrictConstantMapping.toConstantMapping new_inner_g).apply_pre_ground_term = tl.unattach.map inner_g.toConstantMapping.apply_pre_ground_term := by
              rw [List.map_inj_left]
              intro t t_mem
              apply ConstantMapping.apply_pre_ground_term_congr_left
              intro d d_mem
              simp only [StrictConstantMapping.toConstantMapping, new_inner_g]
              have : d ∉ t_res.snd := by
                intro contra
                apply GroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
                apply forbidden_constants_subsumes_term.right
                rw [List.mem_unattach] at t_mem
                rcases t_mem with ⟨h, t_mem⟩
                rw [List.mem_flatMap]
                exists ⟨t, h⟩
              simp [this]

            specialize inner_ih (by apply List.subset_of_cons_subset; exact sub) (forbidden_constants ++ t_res.snd) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_term.right) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_rules) new_inner_g
              (by intro d d_mem
                  unfold new_inner_g
                  have : d ∉ t_res.snd := by
                    intro contra
                    apply PreGroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
                    apply forbidden_constants_subsumes_rules
                    exact d_mem
                  simp only [this, ↓reduceIte]
                  apply inner_g_id
                  exact d_mem)
              (by rw [fresh_constant_remapping_h.right]
                  rw [List.map_append, new_inner_g_is_fresh_constant_remapping_in_t_res, new_inner_g_is_inner_g_on_forbidden_constants, fresh_constant_remapping_h.left]
                  simp only [new_inner_g_on_tl])
            rw [List.map_append, new_inner_g_is_fresh_constant_remapping_in_t_res, new_inner_g_is_inner_g_on_forbidden_constants, fresh_constant_remapping_h.left] at inner_ih
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
                have : d ∉ inner_backtracking.snd := by
                  intro contra
                  apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d contra
                  apply forbidden_constants_subsumes_rules
                  exact d_mem
                simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
                simp only [inner_backtracking, List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list] at this
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
                  have : d ∉ inner_backtracking.snd := by
                    intro contra
                    apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d contra
                    apply forbidden_constants_subsumes_term.right
                    rw [FiniteTree.mem_leavesList] at d_mem
                    rcases d_mem with ⟨t, t_mem, d_mem⟩
                    rw [List.mem_flatMap]
                    rw [FiniteTreeList.fromListToListIsId] at t_mem
                    rw [List.mem_unattach] at t_mem
                    rcases t_mem with ⟨h, t_mem⟩
                    exists ⟨t, h⟩
                  simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
                  simp only [inner_backtracking, List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list] at this
                  rw [List.mem_append] at this
                  split
                  case isTrue heq => apply False.elim; apply this; apply Or.inr; exact heq
                  case isFalse heq =>
                    unfold new_inner_g
                    split
                    case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
                    case isFalse heq => rfl
                | inr d_mem =>
                  have : d ∈ inner_backtracking.snd := by
                    simp only [inner_backtracking, List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list]
                    rw [List.mem_append]
                    apply Or.inr
                    exact d_mem
                  simp only [StrictConstantMapping.toConstantMapping, t_res, d_mem, this, ↓reduceIte]

      let rule := rl.get_by_id func.ruleId term_ruleIds_valid.left
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

      let trg_base : PreTrigger sig := GroundTerm.backtrackTrigger rl (.func func ts arity_ok) (by exists func, ts, arity_ok) term_ruleIds_valid term_rule_arity_valid forbidden_constants

      let trg1 : PreTrigger sig := GroundTerm.backtrackTrigger rl
        (g.toConstantMapping.apply_ground_term (.func func ts arity_ok))
        (by exists func, (ts.map g.toConstantMapping.apply_ground_term), (by rw [List.length_map]; exact arity_ok); rw [ConstantMapping.apply_ground_term_func])
        (by apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity; exact term_ruleIds_valid)
        (by apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity; exact term_rule_arity_valid)
        (forbidden_constants.map g)

      let trg2 : PreTrigger sig := {
        rule := trg_base.rule,
        subs := (StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then fresh_constant_remapping c else g c)).apply_ground_term ∘ trg_base.subs,
      }

      have strong_equiv : trg1.strong_equiv trg2 := by
        unfold PreTrigger.strong_equiv
        constructor
        . rfl
        . intro v v_mem
          simp only [trg1, trg2, trg_base, backtrackTrigger, PreGroundTerm.backtrackTrigger]
          simp only [GroundTerm.func, ConstantMapping.apply_ground_term, StrictConstantMapping.toConstantMapping, FiniteTree.mapLeaves]
          cases Decidable.em (v ∈ rule.frontier) with
          | inl v_mem_frontier =>
            simp only [Function.comp_apply, rule, v_mem_frontier, ↓reduceDIte]
            simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, StrictConstantMapping.toConstantMapping]
            simp only [FiniteTree.mapLeavesList_fromList_eq_fromList_map, FiniteTreeList.fromListToListIsId, List.getElem_map, Subtype.mk.injEq]
            apply FiniteTree.mapLeavesEqIfMapEqOnLeaves
            rw [List.map_inj_left]
            intro d d_mem
            have : d ∉ backtracking.snd := by
              intro contra
              apply backtrackFacts_fresh_constants_not_forbidden d contra
              apply forbidden_constants_subsumes_term
              rw [GroundTerm.constants_func]
              rw [List.getElem_unattach] at d_mem
              apply List.mem_flatMap_of_mem _ (by unfold constants; exact d_mem)
              apply List.getElem_mem
            simp [this]
          | inr v_mem_frontier =>
            have v_mem_pure_body : v ∈ pure_body_vars := by
              simp only [pure_body_vars, Rule.pure_body_vars, List.mem_filter, FunctionFreeConjunction.vars]
              constructor
              . unfold FunctionFreeConjunction.vars at v_mem
                exact v_mem
              . apply decide_eq_true; exact v_mem_frontier
            simp only [rule] at v_mem_frontier
            simp only [pure_body_vars, rule] at v_mem_pure_body
            simp only [Function.comp_apply, v_mem_frontier, v_mem_pure_body, ↓reduceDIte]
            simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, StrictConstantMapping.toConstantMapping]
            simp only [GroundTerm.const, FiniteTree.mapLeaves, Subtype.mk.injEq, FiniteTree.leaf.injEq]
            have : fresh_consts_for_pure_body_vars.val[pure_body_vars.idxOf v]'(by rw [fresh_consts_for_pure_body_vars.property.left]; apply List.idxOf_lt_length_of_mem; exact v_mem_pure_body) ∈ backtracking.snd := by
              simp only [backtracking, backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.func]
              apply List.mem_append_right
              apply List.getElem_mem
            simp only [fresh_consts_for_pure_body_vars, pure_body_vars, rule] at this
            simp only [this, ↓reduceIte]
            simp only [backtracking, backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.func, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, StrictConstantMapping.toConstantMapping, FiniteTree.mapLeaves] at fresh_constant_remapping_h
            rw [List.map_append] at fresh_constant_remapping_h
            have right := (List.append_args_eq_of_append_eq_of_same_length (by
              apply List.append_left_same_length_of_append_eq_append_of_right_same_length fresh_constant_remapping_h
              rw [List.length_map]
              simp only [PreGroundTerm.backtrackTrigger]
              rw [(rule.fresh_consts_for_pure_body_vars forbidden_constants).property.left]
              rw [(rule.fresh_consts_for_pure_body_vars (forbidden_constants.map g)).property.left]
            ) fresh_constant_remapping_h).right
            simp only [PreGroundTerm.backtrackTrigger] at right
            simp only [← right]
            rw [List.getElem_map]

      intro e e_mem
      rcases e_mem with ⟨f, f_mem, e_eq⟩
      simp only [List.mem_toSet, backtracking, backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.func] at f_mem
      rw [List.mem_append] at f_mem
      simp only [List.mem_toSet, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.func]
      rw [List.mem_append]
      cases f_mem with
      | inl f_mem =>
        apply Or.inl
        rw [List.mem_append] at f_mem
        rw [List.mem_append]
        cases f_mem with
        | inl f_mem =>
          apply Or.inl
          simp only [PreGroundTerm.backtrackTrigger, PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list] at f_mem
          simp only [PreGroundTerm.backtrackTrigger, PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
          rw [List.mem_map] at f_mem
          rcases f_mem with ⟨a, a_mem, f_eq⟩
          rw [List.mem_map]
          exists a
          constructor
          . exact a_mem
          . rw [e_eq, ← f_eq]
            rw [← ConstantMapping.apply_fact.eq_def]
            rw [ConstantMapping.apply_fact_eq_groundTermMapping_applyFact]
            rw [← GroundSubstitution.apply_function_free_atom_compose]
            . apply PreTrigger.subs_apply_function_free_atom_eq_of_strong_equiv strong_equiv
              exact a_mem
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
          have func_disjIdx_lt : func.disjunctIndex < rule.head.length := term_disjIdx_valid.left
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

        have new_g_on_ts : (List.map new_g.toConstantMapping.apply_pre_ground_term ts.unattach) = (List.map g.toConstantMapping.apply_pre_ground_term ts.unattach) := by
          rw [List.map_inj_left]
          intro t t_mem
          apply ConstantMapping.apply_pre_ground_term_congr_left
          intro d d_mem
          simp only [StrictConstantMapping.toConstantMapping, new_g]
          have : d ∉ fresh_consts_for_pure_body_vars.val := by
            intro contra
            apply fresh_consts_for_pure_body_vars.property.right.right d contra
            apply forbidden_constants_subsumes_term
            rw [List.mem_unattach] at t_mem
            rcases t_mem with ⟨h, t_mem⟩
            rw [GroundTerm.constants_func]
            rw [List.mem_flatMap]
            exists ⟨t, h⟩
          simp [this]

        apply Or.inr
        rw [← List.mem_toSet]
        simp only [FiniteTree.mapLeavesList_fromList_eq_fromList_map]
        specialize theorem_for_ts ts (by simp)
          (forbidden_constants ++ fresh_consts_for_pure_body_vars)
          (by apply List.subset_append_of_subset_left; rw [GroundTerm.constants_func] at forbidden_constants_subsumes_term; exact forbidden_constants_subsumes_term)
          (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_rules)
          new_g
          (by intro d d_mem
              unfold new_g
              have : d ∉ fresh_consts_for_pure_body_vars.val := by
                intro contra
                apply fresh_consts_for_pure_body_vars.property.right.right d contra
                apply forbidden_constants_subsumes_rules
                exact d_mem
              simp only [this, ↓reduceDIte]
              apply g_id
              exact d_mem)
          fresh_constant_remapping
          (by simp only [backtracking, backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.func, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves] at fresh_constant_remapping_h
              rw [List.map_append] at fresh_constant_remapping_h
              have fresh_constant_remapping_h := (List.append_args_eq_of_append_eq_of_same_length (by
                apply List.append_left_same_length_of_append_eq_append_of_right_same_length fresh_constant_remapping_h
                rw [List.length_map]
                simp only [PreGroundTerm.backtrackTrigger]
                rw [(rule.fresh_consts_for_pure_body_vars forbidden_constants).property.left]
                rw [(rule.fresh_consts_for_pure_body_vars (forbidden_constants.map g)).property.left]
              ) fresh_constant_remapping_h).left
              simp only [PreGroundTerm.backtrackTrigger] at fresh_constant_remapping_h
              rw [fresh_constant_remapping_h]
              simp only [FiniteTree.mapLeavesList_fromList_eq_fromList_map]
              rw [List.map_append, new_g_on_forbidden_constants_is_g, new_g_on_fresh_is_fresh2]
              simp only [new_g_on_ts]
              rfl)
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
              apply GroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
              apply forbidden_constants_subsumes_rules
              exact d_mem
            simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
            simp only [backtracking, backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.func] at this
            rw [List.mem_append] at this
            split
            case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
            case isFalse heq =>
              unfold new_g
              split
              case isTrue heq => apply False.elim; apply this; apply Or.inr; exact heq
              case isFalse heq => rfl
          | inr d_mem =>
            cases d_mem with
            | inl d_mem =>
              have : d ∉ backtracking.snd := by
                intro contra
                apply GroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
                apply forbidden_constants_subsumes_term
                simp only [GroundTerm.constants, GroundTerm.func, FiniteTree.leaves]
                exact d_mem
              simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
              simp only [backtracking, backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.func] at this
              rw [List.mem_append] at this
              split
              case isTrue heq => apply False.elim; apply this; apply Or.inl; exact heq
              case isFalse heq =>
                unfold new_g
                split
                case isTrue heq => apply False.elim; apply this; apply Or.inr; exact heq
                case isFalse heq => rfl
            | inr d_mem =>
              have : d ∈ backtracking.snd := by
                simp only [backtracking, backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.func]
                rw [List.mem_append]
                apply Or.inl
                exact d_mem
              simp only [PreGroundTerm.backtrackTrigger] at d_mem
              simp only [StrictConstantMapping.toConstantMapping, fresh_consts_for_pure_body_vars, rule, d_mem, this, ↓reduceIte]
  theorem GroundTerm.backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (terms : List (GroundTerm sig))
      (terms_ruleIds_valid : ∀ t ∈ terms, t.skolem_ruleIds_valid rl)
      (terms_disjIdx_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_disjIdx_valid rl (terms_ruleIds_valid t mem))
      (terms_rule_arity_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_rule_arity_valid rl (terms_ruleIds_valid t mem))
      (forbidden_constants : List sig.C)
      (forbidden_constants_subsumes_terms : terms.flatMap GroundTerm.constants ⊆ forbidden_constants)
      (forbidden_constants_subsumes_rules : (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants) :
      let backtracking := (backtrackFacts_list rl terms terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants)
      ∀ (g : StrictConstantMapping sig), (∀ d, (d ∈ rl.rules.flatMap Rule.constants) -> g d = d) ->
        ∃ (fresh_constant_remapping : StrictConstantMapping sig),
        (∀ d ∉ backtracking.snd, fresh_constant_remapping d = d) ∧
        ((StrictConstantMapping.toConstantMapping (fun c => if c ∈ backtracking.snd then fresh_constant_remapping c else g c)).apply_fact_set backtracking.fst.toSet ⊆
        (backtrackFacts_list rl (terms.map g.toConstantMapping.apply_ground_term)
          (by intro t t_mem; rw [List.mem_map] at t_mem; rcases t_mem with ⟨t', t'_mem, t_eq⟩; rw [← t_eq]; apply StrictConstantMapping.apply_ground_term_preserves_ruleId_validity; apply terms_ruleIds_valid; exact t'_mem)
          (by intro t t_mem; rw [List.mem_map] at t_mem; rcases t_mem with ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_ground_term_preserves_disjIdx_validity; apply terms_disjIdx_valid; exact t'_mem)
          (by intro t t_mem; rw [List.mem_map] at t_mem; rcases t_mem with ⟨t', t'_mem, t_eq⟩; simp only [← t_eq]; apply StrictConstantMapping.apply_ground_term_preserves_rule_arity_validity; apply terms_rule_arity_valid; exact t'_mem)
          (forbidden_constants.map g)
        ).fst.toSet) := by
    intro backtracking g g_id
    induction terms generalizing forbidden_constants g with
    | nil =>
      exists id
      constructor
      . intros; simp
      . intro e e_mem
        rcases e_mem with ⟨f, f_mem, e_eq⟩
        simp [backtracking, backtrackFacts_list, List.mem_toSet] at f_mem
    | cons hd tl ih =>
      rw [List.flatMap_cons, List.append_subset] at forbidden_constants_subsumes_terms

      rcases backtrackFacts_under_constant_mapping_exists_fresh_constant_remapping rl hd (by apply terms_ruleIds_valid; simp) (by apply terms_disjIdx_valid; simp) (by apply terms_rule_arity_valid; simp) forbidden_constants forbidden_constants_subsumes_terms.left g with ⟨fresh_remapping_hd, fresh_remapping_hd_h⟩

      have fresh_remapping_hd_h' := GroundTerm.backtrackFacts_under_constant_mapping_subset_of_composing_with_subs rl hd (by apply terms_ruleIds_valid; simp) (by apply terms_disjIdx_valid; simp) (by apply terms_rule_arity_valid; simp) forbidden_constants forbidden_constants_subsumes_terms.left forbidden_constants_subsumes_rules g g_id fresh_remapping_hd fresh_remapping_hd_h.right

      let hd_res := backtrackFacts rl hd (by apply terms_ruleIds_valid; simp) (by apply terms_disjIdx_valid; simp) (by apply terms_rule_arity_valid; simp) forbidden_constants
      let new_g : StrictConstantMapping sig := fun c => if c ∈ hd_res.snd then fresh_remapping_hd c else g c

      rcases ih (by intro t t_mem; apply terms_ruleIds_valid; rw [List.mem_cons]; apply Or.inr; exact t_mem) (by intro t t_mem; apply terms_disjIdx_valid; rw [List.mem_cons]; apply Or.inr; exact t_mem) (by intro t t_mem; apply terms_rule_arity_valid; rw [List.mem_cons]; apply Or.inr; exact t_mem) (forbidden_constants ++ hd_res.snd) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_terms.right) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_rules) new_g
        (by intro d d_mem
            unfold new_g
            have : d ∉ hd_res.snd := by
              intro contra
              apply PreGroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
              apply forbidden_constants_subsumes_rules
              exact d_mem
            simp only [this, ↓reduceIte]
            apply g_id
            exact d_mem) with ⟨fresh_remapping_tl, fresh_remapping_tl_h⟩

      let fresh_constant_remapping : StrictConstantMapping sig := fun c => if c ∈ hd_res.snd then fresh_remapping_hd c else fresh_remapping_tl c

      exists fresh_constant_remapping
      constructor
      . intro d d_nmem
        unfold fresh_constant_remapping
        cases Decidable.em (d ∈ hd_res.snd) with
        | inl d_mem =>
          simp only [d_mem]
          apply fresh_remapping_hd_h.left
          intro contra
          apply d_nmem
          simp only [backtracking, backtrackFacts_list]
          rw [List.mem_append]
          apply Or.inl
          exact contra
        | inr d_mem =>
          simp only [d_mem, ↓reduceIte]
          apply fresh_remapping_tl_h.left
          intro contra
          apply d_nmem
          simp only [backtracking, backtrackFacts_list]
          rw [List.mem_append]
          apply Or.inr
          exact contra
      . intro e e_mem
        rcases e_mem with ⟨f, f_mem, e_eq⟩
        simp only [List.mem_toSet, backtracking, backtrackFacts_list, List.mem_append] at f_mem
        simp only [List.mem_toSet, List.map_cons, backtrackFacts_list, List.mem_append]
        cases f_mem with
        | inl f_mem =>
          apply Or.inl
          rw [← List.mem_toSet]
          apply fresh_remapping_hd_h'
          exists f
          constructor
          . rw [List.mem_toSet]; exact f_mem
          . rw [e_eq]
            apply ConstantMapping.apply_fact_congr_left
            intro d d_mem
            cases backtrackFacts_constants_in_rules_or_term_or_fresh f f_mem d d_mem with
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
                  apply forbidden_constants_subsumes_terms.left
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
                simp only [StrictConstantMapping.toConstantMapping, fresh_constant_remapping, hd_res, d_mem, this, ↓reduceIte]
        | inr f_mem =>
          apply Or.inr

          have fresh_remapping_tl_h := fresh_remapping_tl_h.right

          have new_g_is_fresh_constant_remapping_in_hd_res : hd_res.snd.map new_g = hd_res.snd.map fresh_constant_remapping := by
            rw [List.map_inj_left]
            intro d d_mem
            simp only [new_g, fresh_constant_remapping]
            simp [d_mem]

          have new_g_is_g_on_forbidden_constants : (forbidden_constants.map new_g) = forbidden_constants.map g := by
            rw [List.map_inj_left]
            intro d d_mem
            unfold new_g
            have : d ∉ hd_res.snd := by
              intro contra
              apply GroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
              exact d_mem
            simp [this]

          have new_g_on_tl : tl.map (StrictConstantMapping.toConstantMapping new_g).apply_ground_term = tl.map g.toConstantMapping.apply_ground_term := by
            rw [List.map_inj_left]
            intro t t_mem
            apply ConstantMapping.apply_ground_term_congr_left
            intro d d_mem
            simp only [StrictConstantMapping.toConstantMapping, new_g]
            have : d ∉ hd_res.snd := by
              intro contra
              apply GroundTerm.backtrackFacts_fresh_constants_not_forbidden d contra
              apply forbidden_constants_subsumes_terms.right
              rw [List.mem_flatMap]
              exists t
            simp [this]

          have fresh_constant_remapping_is_fresh_remapping_hd_in_hd_res : hd_res.snd.map fresh_constant_remapping = hd_res.snd.map fresh_remapping_hd := by
            rw [List.map_inj_left]
            intro d d_mem
            simp only [fresh_constant_remapping]
            simp [d_mem]

          rw [List.map_append, new_g_is_fresh_constant_remapping_in_hd_res, new_g_is_g_on_forbidden_constants, fresh_constant_remapping_is_fresh_remapping_hd_in_hd_res, fresh_remapping_hd_h.right] at fresh_remapping_tl_h
          simp only [new_g_on_tl] at fresh_remapping_tl_h

          rw [← List.mem_toSet]
          apply fresh_remapping_tl_h
          exists f
          constructor
          . rw [List.mem_toSet]; exact f_mem
          . rw [e_eq]
            apply ConstantMapping.apply_fact_congr_left
            intro d d_mem
            cases backtrackFacts_list_constants_in_rules_or_term_or_fresh f f_mem d d_mem with
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
                have : d ∉ hd_res.snd := by
                  intro contra
                  apply backtrackFacts_fresh_constants_not_forbidden d contra
                  apply forbidden_constants_subsumes_rules
                  exact d_mem
                simp [new_g, this]
            | inr d_mem =>
              cases d_mem with
              | inl d_mem =>
                have : d ∉ backtracking.snd := by
                  intro contra
                  apply backtrackFacts_list_fresh_constants_not_forbidden d contra
                  apply forbidden_constants_subsumes_terms.right
                  exact d_mem
                simp only [StrictConstantMapping.toConstantMapping, this, ↓reduceIte]
                simp only [backtracking, backtrackFacts_list] at this
                rw [List.mem_append] at this
                split
                case isTrue heq => apply False.elim; apply this; apply Or.inr; exact heq
                case isFalse heq =>
                  have : d ∉ hd_res.snd := by
                    intro contra
                    apply backtrackFacts_fresh_constants_not_forbidden d contra
                    apply forbidden_constants_subsumes_terms.right
                    exact d_mem
                  simp [new_g, this]
              | inr d_mem =>
                have : d ∈ backtracking.snd := by
                  simp only [backtracking, backtrackFacts_list]
                  rw [List.mem_append]
                  apply Or.inr
                  exact d_mem
                simp only [StrictConstantMapping.toConstantMapping, fresh_constant_remapping, hd_res, d_mem, this, ↓reduceIte]
                have : d ∉ hd_res.snd := by
                  intro contra
                  apply backtrackFacts_list_fresh_constants_not_forbidden d d_mem
                  rw [List.mem_append]
                  apply Or.inr
                  exact contra
                unfold hd_res at this
                simp [this]

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
        ({rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig}.backtrackFacts rl (trg.compose_strict_constant_mapping_preserves_ruleId_validity g rl trg_ruleIds_valid) (trg.compose_strict_constant_mapping_preserves_disjIdx_validity g rl trg_ruleIds_valid trg_disjIdx_valid) (trg.compose_strict_constant_mapping_preserves_rule_arity_validity g rl trg_ruleIds_valid trg_rule_arity_valid)).fst.toSet) := by
    intro backtracking g g_id
    let forbidden_constants := trg.mapped_body.flatMap Fact.constants ++ rl.rules.flatMap Rule.constants
    rcases GroundTerm.backtrackFacts_list_under_constant_mapping_subset_of_composing_with_subs rl (trg.mapped_body.flatMap GeneralizedAtom.terms) trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid forbidden_constants (by apply List.subset_append_of_subset_left; intro d d_mem; rw [List.mem_flatMap] at d_mem; rcases d_mem with ⟨t, t_mem, d_mem⟩; rw [List.mem_flatMap] at t_mem; rcases t_mem with ⟨f, f_mem, t_mem⟩; rw [List.mem_flatMap]; exists f; constructor; exact f_mem; unfold Fact.constants; rw [List.mem_flatMap]; exists t) (by apply List.subset_append_of_subset_right; simp) g g_id with ⟨fresh_constant_remapping, fresh_constant_remapping_h⟩
    exists fresh_constant_remapping
    constructor
    . exact fresh_constant_remapping_h.left
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
            simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, StrictConstantMapping.toConstantMapping, GroundTerm.const, Subtype.mk.injEq, FiniteTree.mapLeaves, FiniteTree.leaf.injEq]
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
        have : (trg.mapped_body.flatMap GeneralizedAtom.terms).map g.toConstantMapping.apply_ground_term = { rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig }.mapped_body.flatMap GeneralizedAtom.terms := by
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
            simp only [StrictConstantMapping.toConstantMapping, GroundTerm.const, Subtype.mk.injEq, FiniteTree.leaf.injEq]
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
        simp only [this] at fresh_constant_remapping_h
        have : forbidden_constants.map g = ({ rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs : PreTrigger sig }.mapped_body.flatMap Fact.constants) ++ rl.rules.flatMap Rule.constants := by
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
        rw [this] at fresh_constant_remapping_h
        rw [← List.mem_toSet]
        apply fresh_constant_remapping_h.right
        exists f

  theorem ChaseBranch.backtracking_of_term_in_node [GetFreshInhabitant sig.C] [Inhabited sig.C] (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      ∀ (rl : RuleList sig), (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) ->
      ∀ (term : GroundTerm sig), (term_mem : term ∈ node.facts.val.terms) ->
      ∀ (forbidden_constants : List sig.C),
        term.constants ⊆ forbidden_constants ->
        (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants ->
      ∃ (g : ConstantMapping sig),
        g.apply_fact_set (term.backtrackFacts rl (cb.term_ruleIds_valid i node eq rl rl_rs_eq term term_mem) (cb.term_disjIdx_valid i node eq rl rl_rs_eq term term_mem) (cb.term_rule_arity_valid i node eq rl rl_rs_eq term term_mem) forbidden_constants).fst.toSet ⊆ node.facts.val ∧
        (∀ (d : sig.C), d ∈ forbidden_constants -> g d = .const d) := by
    intro rl rl_rs_eq term term_mem forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules
    let backtracking := term.backtrackFacts rl (cb.term_ruleIds_valid i node eq rl rl_rs_eq term term_mem) (cb.term_disjIdx_valid i node eq rl rl_rs_eq term term_mem) (cb.term_rule_arity_valid i node eq rl rl_rs_eq term term_mem) forbidden_constants
    induction i generalizing node term forbidden_constants with
    | zero =>
      rw [cb.database_first] at eq
      injection eq with eq
      rw [← eq] at term_mem
      simp only at term_mem
      unfold FactSet.terms at term_mem
      rcases term_mem with ⟨f, f_mem, term_mem⟩
      rcases kb.db.toFactSet.property.right f f_mem term term_mem with ⟨_, t_eq⟩
      exists fun c => .const c
      constructor
      . intro f' f'_mem
        rcases f'_mem with ⟨f'', f''_mem, f'_mem⟩
        rw [List.mem_toSet] at f''_mem
        simp only [t_eq, GroundTerm.backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.const] at f''_mem
        simp at f''_mem
      . simp
    | succ i ih =>
      rw [cb.origin_trg_result_yields_next_node_facts i node eq] at term_mem
      unfold FactSet.terms at term_mem
      rcases term_mem with ⟨f, f_mem, term_mem⟩
      cases f_mem with
      | inl f_mem =>
        rcases ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) term (by exists f) forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules with ⟨g, g_h⟩
        exists g
        constructor
        . rw [cb.origin_trg_result_yields_next_node_facts i node eq]
          apply Set.subset_union_of_subset_left
          exact g_h.left
        . exact g_h.right
      | inr f_mem =>
        let origin := node.origin.get (cb.origin_isSome i eq)
        have origin_active := cb.origin_trg_is_active i node eq

        have origin_ruleIds_valid := (cb.trigger_ruleIds_valid_of_loaded i (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) rl rl_rs_eq origin.fst.val origin_active.left)
        have origin_disjIdx_valid := (cb.trigger_disjIdx_valid_of_loaded i (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) rl rl_rs_eq origin.fst.val origin_active.left)
        have origin_rule_arity_valid := (cb.trigger_rule_arity_valid_of_loaded i (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) rl rl_rs_eq origin.fst.val origin_active.left)

        rw [List.mem_toSet] at f_mem
        let voc_for_term := origin.fst.val.var_or_const_for_result_term origin.snd f_mem term_mem
        have voc_for_term_apply := origin.fst.val.apply_on_var_or_const_for_result_term_is_term origin.snd f_mem term_mem

        cases voc_eq : voc_for_term with
        | const c =>
          exists fun c => .const c
          constructor
          . intro f' f'_mem
            rcases f'_mem with ⟨f'', f''_mem, f'_mem⟩
            have : backtracking.fst = [] := by
              unfold backtracking
              unfold voc_for_term at voc_eq
              rw [voc_eq, PreTrigger.apply_to_var_or_const_for_const] at voc_for_term_apply
              simp only [← voc_for_term_apply, GroundTerm.backtrackFacts, PreGroundTerm.backtrackFacts, GroundTerm.const]
            rw [this] at f''_mem
            simp [List.mem_toSet] at f''_mem
          . simp
        | var v =>
          cases Decidable.em (v ∈ origin.fst.val.rule.frontier) with
          | inl v_frontier =>
            -- TODO: pretty much same as IH application above... can we unify this?
            rcases ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) term (by
              rcases Rule.frontier_occurs_in_body _ _ v_frontier with ⟨a, a_mem, v_mem⟩
              exists origin.fst.val.subs.apply_function_free_atom a
              constructor
              . apply origin_active.left; rw [List.mem_toSet]; simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]; rw [List.mem_map]; exists a
              . simp only [TermMapping.apply_generalized_atom]
                rw [List.mem_map]
                exists voc_for_term
                constructor
                . rw [voc_eq]; exact v_mem
                . rw [voc_eq]
                  unfold voc_for_term at voc_eq
                  rw [← voc_for_term_apply, voc_eq, PreTrigger.apply_to_var_or_const_frontier_var]
                  . simp [GroundSubstitution.apply_var_or_const]
                  . exact v_frontier
            ) forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules with ⟨g, g_h⟩
            exists g
            constructor
            . rw [cb.origin_trg_result_yields_next_node_facts i node eq]
              apply Set.subset_union_of_subset_left
              exact g_h.left
            . exact g_h.right
          | inr v_frontier =>
            unfold voc_for_term at voc_eq
            rw [voc_eq, PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_frontier] at voc_for_term_apply

            have func_term_ruleIds_valid := origin.fst.val.skolem_ruleIds_valid_for_functional_term rl (by rw [rl_rs_eq]; exact origin.fst.property) origin_ruleIds_valid origin.snd.val v
            have func_term_disjIdx_valid := origin.fst.val.skolem_disjIdx_valid_for_functional_term rl (by rw [rl_rs_eq]; exact origin.fst.property) origin_ruleIds_valid origin_disjIdx_valid origin.snd.val v (by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)
            have func_term_rule_arity_valid := origin.fst.val.skolem_rule_arity_valid_for_functional_term rl (by rw [rl_rs_eq]; exact origin.fst.property) origin_ruleIds_valid origin_rule_arity_valid origin.snd.val v

            let mapped_frontier := origin.fst.val.rule.frontier.map origin.fst.val.subs

            have : ∀ sublist, (sub : sublist ⊆ mapped_frontier) -> ∀ forbidden_constants, (sublist.flatMap GroundTerm.constants ⊆ forbidden_constants) -> (rl.rules.flatMap Rule.constants ⊆ forbidden_constants) -> ∃ (g : ConstantMapping sig),
                (g.apply_fact_set (PreGroundTerm.backtrackFacts_list rl (FiniteTreeList.fromList sublist.unattach)
                  (by rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]; intro t t_mem; rw [FiniteTreeList.fromListToListIsId, List.mem_unattach] at t_mem; rcases t_mem with ⟨h, _⟩; exact h)
                  (by have := func_term_ruleIds_valid.right
                      rw [GroundTerm.skolem_ruleIds_valid_list] at this
                      rw [GroundTerm.skolem_ruleIds_valid_list]
                      intro t t_mem
                      apply this
                      apply sub
                      exact t_mem)
                  (by have := func_term_disjIdx_valid.right
                      rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact func_term_ruleIds_valid.right)] at this
                      rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by
                        have := func_term_ruleIds_valid.right
                        rw [GroundTerm.skolem_ruleIds_valid_list] at this
                        intro t t_mem
                        apply this
                        apply sub
                        exact t_mem
                      )]
                      intro t t_mem
                      apply this
                      apply sub
                      exact t_mem)
                  (by have := func_term_rule_arity_valid.right
                      rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact func_term_ruleIds_valid.right)] at this
                      rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by
                        have := func_term_ruleIds_valid.right
                        rw [GroundTerm.skolem_ruleIds_valid_list] at this
                        intro t t_mem
                        apply this
                        apply sub
                        exact t_mem
                      )]
                      intro t t_mem
                      apply this
                      apply sub
                      exact t_mem)
                  forbidden_constants).fst.toSet ⊆ node.facts.val) ∧
                (∀ (d : sig.C), d ∈ forbidden_constants → g d = .const d) := by
              intro sublist sub forbidden_constants forbidden_constants_subsumes_term forbidden_constants_subsumes_rules
              induction sublist generalizing forbidden_constants with
              | nil =>
                exists fun c => .const c
                constructor
                . intro _ e_mem
                  simp only [List.unattach_nil, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list] at e_mem
                  rcases e_mem with ⟨_, f_mem, _⟩
                  simp [List.mem_toSet] at f_mem
                . intros; rfl
              | cons hd tl inner_ih =>
                rw [List.flatMap_cons, List.append_subset] at forbidden_constants_subsumes_term

                rcases ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) hd (by
                  rw [List.cons_subset] at sub
                  unfold mapped_frontier at sub
                  rw [List.mem_map] at sub
                  rcases sub.left with ⟨v, v_mem, hd_eq⟩
                  rcases Rule.frontier_occurs_in_body _ _ v_mem with ⟨a, a_mem, v_mem⟩
                  exists origin.fst.val.subs.apply_function_free_atom a
                  constructor
                  . apply origin_active.left; rw [List.mem_toSet]; simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]; rw [List.mem_map]; exists a
                  . simp only [TermMapping.apply_generalized_atom]
                    rw [List.mem_map]
                    exists .var v
                ) forbidden_constants forbidden_constants_subsumes_term.left forbidden_constants_subsumes_rules with ⟨g_hd, g_hd_h⟩
                let t_res := PreGroundTerm.backtrackFacts rl hd.val hd.property
                  (by have := func_term_ruleIds_valid.right
                      rw [GroundTerm.skolem_ruleIds_valid_list] at this
                      apply this
                      exact (List.cons_subset.mp sub).left)
                  (by have := func_term_disjIdx_valid.right
                      rw [GroundTerm.skolem_disjIdx_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact func_term_ruleIds_valid.right)] at this
                      apply this
                      exact (List.cons_subset.mp sub).left)
                  (by have := func_term_rule_arity_valid.right
                      rw [GroundTerm.skolem_rule_arity_valid_list _ _ (by rw [← GroundTerm.skolem_ruleIds_valid_list]; exact func_term_ruleIds_valid.right)] at this
                      apply this
                      exact (List.cons_subset.mp sub).left)
                  forbidden_constants
                rcases inner_ih (by apply List.subset_of_cons_subset; exact sub) (forbidden_constants ++ t_res.snd) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_term.right) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_rules) with ⟨g_tl, g_tl_h⟩
                let g : ConstantMapping sig := fun c => if c ∈ t_res.snd then g_hd c else g_tl c
                exists g
                constructor
                . intro f f_mem
                  rcases f_mem with ⟨f', f'_mem, f_eq⟩
                  rw [List.mem_toSet] at f'_mem
                  simp only [List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.backtrackFacts_list] at f'_mem
                  rw [List.mem_append] at f'_mem
                  cases f'_mem with
                  | inl f'_mem =>
                    have : g.apply_fact f' = g_hd.apply_fact f' := by
                      apply ConstantMapping.apply_fact_congr_left
                      intro d d_mem
                      unfold g
                      cases Decidable.em (d ∈ t_res.snd) with
                      | inl d_mem' => simp only [d_mem', ↓reduceIte]
                      | inr d_mem' =>
                        have : d ∈ forbidden_constants := by
                          have := PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh f' f'_mem d d_mem
                          cases this with
                          | inl d_mem'' => apply forbidden_constants_subsumes_rules; exact d_mem''
                          | inr d_mem'' =>
                            cases d_mem'' with
                            | inr d_mem'' => apply False.elim; apply d_mem'; exact d_mem''
                            | inl d_mem'' =>
                              apply forbidden_constants_subsumes_term.left
                              exact d_mem''
                        simp only [d_mem', ↓reduceIte]
                        rw [g_hd_h.right]
                        rw [g_tl_h.right]
                        . rw [List.mem_append]; apply Or.inl; exact this
                        . exact this
                    rw [f_eq, ← ConstantMapping.apply_fact.eq_def, this]
                    rw [cb.origin_trg_result_yields_next_node_facts i node eq]
                    apply Or.inl
                    apply g_hd_h.left
                    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
                    rw [List.mem_toSet]
                    exact f'_mem
                  | inr f'_mem =>
                    have : g.apply_fact f' = g_tl.apply_fact f' := by
                      apply ConstantMapping.apply_fact_congr_left
                      intro d d_mem
                      unfold g
                      cases Decidable.em (d ∈ t_res.snd) with
                      | inr d_mem' => simp only [d_mem', ↓reduceIte]
                      | inl d_mem' =>
                        apply False.elim
                        have d_not_forbidden : d ∉ forbidden_constants := PreGroundTerm.backtrackFacts_fresh_constants_not_forbidden d d_mem'
                        have := PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f' f'_mem d d_mem
                        cases this with
                        | inl d_mem'' => apply d_not_forbidden; apply forbidden_constants_subsumes_rules; exact d_mem''
                        | inr d_mem'' =>
                          cases d_mem'' with
                          | inl d_mem'' =>
                            apply d_not_forbidden
                            apply forbidden_constants_subsumes_term.right
                            rw [FiniteTree.mem_leavesList] at d_mem''
                            rcases d_mem'' with ⟨t, t_mem, d_mem''⟩
                            rw [FiniteTreeList.fromListToListIsId, List.mem_unattach] at t_mem
                            rcases t_mem with ⟨h, t_mem⟩
                            rw [List.mem_flatMap]
                            exists ⟨t, h⟩
                          | inr d_mem'' =>
                            apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d d_mem''
                            rw [List.mem_append]
                            apply Or.inr
                            exact d_mem'

                    rw [f_eq, ← ConstantMapping.apply_fact.eq_def, this]
                    apply g_tl_h.left
                    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
                    rw [List.mem_toSet]
                    exact f'_mem
                . intro d d_mem
                  unfold g
                  split
                  . apply g_hd_h.right; exact d_mem
                  . apply g_tl_h.right; rw [List.mem_append]; apply Or.inl; exact d_mem

            let rule := rl.get_by_id origin.fst.val.rule.id (by exists origin.fst.val.rule; constructor; rw [rl_rs_eq]; exact origin.fst.property; rfl)
            let pure_body_vars := rule.pure_body_vars
            let fresh_consts_for_pure_body_vars := rule.fresh_consts_for_pure_body_vars forbidden_constants
            let backtrack_trigger : PreTrigger sig := origin.fst.val.backtrackTrigger_for_functional_term rl (by rw [rl_rs_eq]; exact origin.fst.property) origin_ruleIds_valid origin_rule_arity_valid forbidden_constants origin.snd.val v

            have triggers_equiv : backtrack_trigger.equiv origin.fst.val := by apply origin.fst.val.backtrackTrigger_for_functional_term_equiv

            rcases this mapped_frontier (by simp) (forbidden_constants ++ fresh_consts_for_pure_body_vars)
              (by apply List.subset_append_of_subset_left
                  intro d d_mem
                  apply forbidden_constants_subsumes_term
                  rw [← voc_for_term_apply]
                  simp only [PreTrigger.functional_term_for_var]
                  rw [GroundTerm.constants_func]
                  exact d_mem)
              (by apply List.subset_append_of_subset_left
                  exact forbidden_constants_subsumes_rules)
              with ⟨g_mapped_frontier, g_mapped_frontier_h⟩

            let g : ConstantMapping sig := fun c =>
              if mem : c ∈ fresh_consts_for_pure_body_vars.val
              then
                let idx := fresh_consts_for_pure_body_vars.val.idxOf c
                have : idx < pure_body_vars.length := by
                  rw [← fresh_consts_for_pure_body_vars.property.left]
                  apply List.idxOf_lt_length_of_mem
                  exact mem
                origin.fst.val.subs pure_body_vars[idx]
              else g_mapped_frontier c

            have triggers_strong_equiv : origin.fst.val.strong_equiv { rule := backtrack_trigger.rule, subs := g.apply_ground_term ∘ backtrack_trigger.subs } := by
              unfold PreTrigger.strong_equiv
              constructor
              . rw [triggers_equiv.left]
              . intro v v_mem
                cases Decidable.em (v ∈ backtrack_trigger.rule.frontier) with
                | inl v_mem' =>
                  simp only [Function.comp_apply]
                  rw [triggers_equiv.right v v_mem']
                  apply Eq.symm
                  apply ConstantMapping.apply_ground_term_eq_self_of_id_on_constants
                  intro d d_mem
                  have d_mem' : d ∈ forbidden_constants := by
                    apply forbidden_constants_subsumes_term
                    rw [← voc_for_term_apply]
                    simp only [PreTrigger.functional_term_for_var]
                    rw [GroundTerm.constants_func]
                    rw [List.mem_flatMap]
                    exists origin.fst.val.subs v
                    constructor
                    . apply List.mem_map_of_mem; rw [← triggers_equiv.left]; exact v_mem'
                    . exact d_mem
                  have : d ∉ fresh_consts_for_pure_body_vars.val := by intro contra; apply fresh_consts_for_pure_body_vars.property.right.right; exact contra; exact d_mem'
                  simp only [g, this, ↓reduceDIte]
                  rw [g_mapped_frontier_h.right]
                  rw [List.mem_append]; apply Or.inl; exact d_mem'
                | inr v_mem' =>
                  have v_mem'' : v ∈ pure_body_vars := by
                    simp only [pure_body_vars, Rule.pure_body_vars, List.mem_filter]
                    rw [← triggers_equiv.left] at v_mem
                    constructor
                    . exact v_mem
                    . apply decide_eq_true; exact v_mem'
                  simp only [backtrack_trigger, PreTrigger.backtrackTrigger_for_functional_term, GroundTerm.backtrackTrigger, PreGroundTerm.backtrackTrigger, PreTrigger.functional_term_for_var, GroundTerm.func]
                  simp only [backtrack_trigger, PreTrigger.backtrackTrigger_for_functional_term, GroundTerm.backtrackTrigger, PreGroundTerm.backtrackTrigger, PreTrigger.functional_term_for_var, GroundTerm.func] at v_mem'
                  simp only [Function.comp_apply, v_mem', ↓reduceDIte]
                  simp only [pure_body_vars, rule] at v_mem''
                  simp only [v_mem'', ↓reduceDIte]
                  simp only [ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
                  unfold g
                  have : fresh_consts_for_pure_body_vars.val[pure_body_vars.idxOf v]'(by unfold pure_body_vars; rw [fresh_consts_for_pure_body_vars.property.left]; apply List.idxOf_lt_length_of_mem; exact v_mem'') ∈ fresh_consts_for_pure_body_vars.val := by apply List.getElem_mem
                  conv at this => right; simp only [fresh_consts_for_pure_body_vars, pure_body_vars, rule]
                  simp only [this, ↓reduceDIte]
                  rw [Subtype.mk.injEq]
                  rw [Rule.fresh_consts_pure_body_vars_roundtrip]
                  exact v_mem''

            have mapped_body_eq := PreTrigger.mapped_body_eq_of_strong_equiv triggers_strong_equiv
            have mapped_head_eq : origin.fst.val.mapped_head[origin.snd.val] = { rule := backtrack_trigger.rule, subs := g.apply_ground_term ∘ backtrack_trigger.subs : PreTrigger sig }.mapped_head[origin.snd.val]'(by rw [← PreTrigger.result_eq_of_equiv _ _ (PreTrigger.equiv_of_strong_equiv _ _ triggers_strong_equiv)]; exact origin.snd.isLt) := by simp only [PreTrigger.result_eq_of_equiv _ _ (PreTrigger.equiv_of_strong_equiv _ _ triggers_strong_equiv)]

            have g_id_on_rule_constants : ∀ c, c ∈ backtrack_trigger.rule.constants -> g c = .const c := by
              intro d d_mem
              have d_mem' : d ∈ forbidden_constants := by
                apply forbidden_constants_subsumes_rules
                rw [List.mem_flatMap]
                exists backtrack_trigger.rule
                constructor
                . rw [triggers_equiv.left, rl_rs_eq]; exact origin.fst.property
                . exact d_mem
              have d_not_mem : d ∉ fresh_consts_for_pure_body_vars.val := by
                intro contra
                apply fresh_consts_for_pure_body_vars.property.right.right
                . exact contra
                . exact d_mem'
              simp only [g, d_not_mem, ↓reduceDIte]
              apply g_mapped_frontier_h.right
              rw [List.mem_append]
              apply Or.inl
              exact d_mem'

            exists g
            constructor
            . intro e e_mem
              rcases e_mem with ⟨f, f_mem, e_eq⟩
              rw [List.mem_toSet] at f_mem
              simp only [← voc_for_term_apply] at f_mem
              simp only [PreTrigger.functional_term_for_var, GroundTerm.func, GroundTerm.backtrackFacts, PreGroundTerm.backtrackFacts] at f_mem


              rw [List.mem_append] at f_mem
              cases f_mem with
              | inl f_mem =>
                rw [cb.origin_trg_result_yields_next_node_facts i node eq]

                rw [List.mem_append] at f_mem
                cases f_mem with
                | inl f_mem =>
                  apply Or.inl
                  rw [e_eq]
                  apply origin_active.left
                  rw [List.mem_toSet]

                  rw [mapped_body_eq]
                  simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
                  simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list] at f_mem
                  rw [List.mem_map]
                  rw [List.mem_map] at f_mem
                  rcases f_mem with ⟨a, a_mem, f_eq⟩
                  exists a
                  constructor
                  . exact a_mem
                  . rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose, ← ConstantMapping.apply_fact_eq_groundTermMapping_applyFact, ← f_eq]
                    . rfl
                    . intro d d_mem
                      rw [ConstantMapping.apply_ground_term_constant]
                      apply g_id_on_rule_constants
                      unfold Rule.constants
                      rw [List.mem_append]
                      apply Or.inl
                      unfold FunctionFreeConjunction.consts
                      rw [List.mem_flatMap]
                      exists a
                | inr f_mem =>
                  apply Or.inr
                  rw [List.mem_toSet, e_eq]
                  simp only [ChaseNode.origin_result]
                  rw [mapped_head_eq]
                  simp only [PreTrigger.mapped_head]
                  simp only [PreTrigger.mapped_head] at f_mem
                  rw [List.getElem_map, List.mem_map]
                  rw [List.getElem_map, List.mem_map] at f_mem
                  rcases f_mem with ⟨a, a_mem, f_eq⟩
                  exists a
                  constructor
                  . exact a_mem
                  . rw [← ConstantMapping.apply_fact_swap_apply_to_function_free_atom, ← f_eq]
                    . rfl
                    . intro d d_mem
                      apply g_id_on_rule_constants
                      unfold Rule.constants
                      rw [List.mem_append]
                      apply Or.inr
                      simp only [List.getElem_zipIdx] at a_mem
                      rw [List.mem_flatMap]
                      exists backtrack_trigger.rule.head[origin.snd.val]'(by rw [triggers_equiv.left, ← PreTrigger.length_mapped_head]; exact origin.snd.isLt)
                      constructor
                      . apply List.getElem_mem
                      . unfold FunctionFreeConjunction.consts
                        rw [List.mem_flatMap]
                        exists a
              | inr f_mem =>
                apply g_mapped_frontier_h.left
                rw [e_eq]
                have : g.apply_fact f = g_mapped_frontier.apply_fact f := by
                  apply ConstantMapping.apply_fact_congr_left
                  intro d d_mem
                  cases Decidable.em (d ∈ fresh_consts_for_pure_body_vars.val) with
                  | inr d_mem' => simp only [g, d_mem', ↓reduceDIte]
                  | inl d_mem' =>
                    apply False.elim
                    have d_not_forbidden : d ∉ forbidden_constants := fresh_consts_for_pure_body_vars.property.right.right d d_mem'
                    have := PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f f_mem d d_mem
                    cases this with
                    | inl d_mem'' => apply d_not_forbidden; apply forbidden_constants_subsumes_rules; exact d_mem''
                    | inr d_mem'' =>
                      cases d_mem'' with
                      | inl d_mem'' =>
                        apply d_not_forbidden
                        apply forbidden_constants_subsumes_term
                        rw [← voc_for_term_apply]
                        simp only [PreTrigger.functional_term_for_var]
                        rw [GroundTerm.constants_func]
                        rw [FiniteTree.mem_leavesList] at d_mem''
                        rcases d_mem'' with ⟨t, t_mem, d_mem''⟩
                        rw [FiniteTreeList.fromListToListIsId, List.mem_unattach] at t_mem
                        rcases t_mem with ⟨h, t_mem⟩
                        rw [List.mem_flatMap]
                        exists ⟨t, h⟩
                      | inr d_mem'' =>
                        apply PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d d_mem''
                        rw [List.mem_append]
                        apply Or.inr
                        exact d_mem'
                rw [← ConstantMapping.apply_fact.eq_def, this]
                apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
                rw [List.mem_toSet]
                exact f_mem
            . intro d d_mem
              have d_nmem : d ∉ fresh_consts_for_pure_body_vars.val := by
                intro contra
                apply fresh_consts_for_pure_body_vars.property.right.right
                . exact contra
                . exact d_mem
              simp only [g, d_nmem, ↓reduceDIte]
              apply g_mapped_frontier_h.right
              rw [List.mem_append]
              apply Or.inl
              exact d_mem

  theorem ChaseBranch.backtracking_of_term_list_in_node [GetFreshInhabitant sig.C] [Inhabited sig.C] (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      ∀ (rl : RuleList sig), (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) ->
      ∀ (terms : List (GroundTerm sig)), (terms_mem : terms.toSet ⊆ node.facts.val.terms) ->
      ∀ (forbidden_constants : List sig.C),
        (terms.flatMap GroundTerm.constants) ⊆ forbidden_constants ->
        (rl.rules.flatMap Rule.constants) ⊆ forbidden_constants ->
      ∃ (g : ConstantMapping sig),
        g.apply_fact_set (GroundTerm.backtrackFacts_list rl terms (by intro t t_mem; apply cb.term_ruleIds_valid i node eq rl rl_rs_eq t; apply terms_mem; rw [List.mem_toSet]; exact t_mem) (by intro t t_mem; apply cb.term_disjIdx_valid i node eq rl rl_rs_eq t; apply terms_mem; rw [List.mem_toSet]; exact t_mem) (by intro t t_mem; apply cb.term_rule_arity_valid i node eq rl rl_rs_eq t; apply terms_mem; rw [List.mem_toSet]; exact t_mem) forbidden_constants).fst.toSet ⊆ node.facts.val ∧
        (∀ (d : sig.C), d ∈ forbidden_constants -> g d = .const d) := by
    intro rl rl_rs_eq terms terms_mem forbidden_constants forbidden_constants_subsumes_terms forbidden_constants_subsumes_rules
    induction terms generalizing forbidden_constants with
    | nil =>
      exists ConstantMapping.id
      constructor
      . simp only [GroundTerm.backtrackFacts_list]
        intro _ e_mem
        rcases e_mem with ⟨_, f_mem, _⟩
        rw [List.mem_toSet] at f_mem
        simp at f_mem
      . intros; rfl
    | cons hd tl ih =>
      rw [List.flatMap_cons, List.append_subset] at forbidden_constants_subsumes_terms

      have hd_mem : hd ∈ node.facts.val.terms := by apply terms_mem; simp [List.mem_toSet]

      rcases cb.backtracking_of_term_in_node i node eq rl rl_rs_eq hd hd_mem forbidden_constants forbidden_constants_subsumes_terms.left forbidden_constants_subsumes_rules with ⟨g_hd, g_hd_h⟩

      let result_for_hd := GroundTerm.backtrackFacts rl hd (cb.term_ruleIds_valid i node eq rl rl_rs_eq hd hd_mem) (cb.term_disjIdx_valid i node eq rl rl_rs_eq hd hd_mem) (cb.term_rule_arity_valid i node eq rl rl_rs_eq hd hd_mem) forbidden_constants

      rcases ih (by intro t t_mem; rw [List.mem_toSet] at t_mem; apply terms_mem; simp [List.mem_toSet, t_mem]) (forbidden_constants ++ result_for_hd.snd) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_terms.right) (by apply List.subset_append_of_subset_left; exact forbidden_constants_subsumes_rules) with ⟨g_tl, g_tl_h⟩

      let g : ConstantMapping sig := fun c => if c ∈ result_for_hd.snd then g_hd c else g_tl c
      exists g
      constructor
      . intro f f_mem
        rcases f_mem with ⟨f', f'_mem, f_eq⟩
        rw [List.mem_toSet] at f'_mem
        simp only [GroundTerm.backtrackFacts_list] at f'_mem
        rw [List.mem_append] at f'_mem
        cases f'_mem with
        | inl f'_mem =>
          have : g.apply_fact f' = g_hd.apply_fact f' := by
            apply ConstantMapping.apply_fact_congr_left
            intro d d_mem
            unfold g
            cases Decidable.em (d ∈ result_for_hd.snd) with
            | inl d_mem' => simp only [d_mem', ↓reduceIte]
            | inr d_mem' =>
              have : d ∈ forbidden_constants := by
                have := PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh f' f'_mem d d_mem
                cases this with
                | inl d_mem'' => apply forbidden_constants_subsumes_rules; exact d_mem''
                | inr d_mem'' =>
                  cases d_mem'' with
                  | inr d_mem'' => apply False.elim; apply d_mem'; exact d_mem''
                  | inl d_mem'' =>
                    apply forbidden_constants_subsumes_terms.left
                    exact d_mem''
              simp only [d_mem', ↓reduceIte]
              rw [g_hd_h.right]
              rw [g_tl_h.right]
              . rw [List.mem_append]; apply Or.inl; exact this
              . exact this
          rw [f_eq, ← ConstantMapping.apply_fact.eq_def, this]
          apply g_hd_h.left
          apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
          rw [List.mem_toSet]
          exact f'_mem
        | inr f'_mem =>
          have : g.apply_fact f' = g_tl.apply_fact f' := by
            apply ConstantMapping.apply_fact_congr_left
            intro d d_mem
            unfold g
            cases Decidable.em (d ∈ result_for_hd.snd) with
            | inr d_mem' => simp only [d_mem', ↓reduceIte]
            | inl d_mem' =>
              apply False.elim
              have d_not_forbidden : d ∉ forbidden_constants := GroundTerm.backtrackFacts_fresh_constants_not_forbidden d d_mem'
              have := GroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f' f'_mem d d_mem
              cases this with
              | inl d_mem'' => apply d_not_forbidden; apply forbidden_constants_subsumes_rules; exact d_mem''
              | inr d_mem'' =>
                cases d_mem'' with
                | inl d_mem'' =>
                  apply d_not_forbidden
                  apply forbidden_constants_subsumes_terms.right
                  exact d_mem''
                | inr d_mem'' =>
                  apply GroundTerm.backtrackFacts_list_fresh_constants_not_forbidden d d_mem''
                  rw [List.mem_append]
                  apply Or.inr
                  exact d_mem'

          rw [f_eq, ← ConstantMapping.apply_fact.eq_def, this]
          apply g_tl_h.left
          apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
          rw [List.mem_toSet]
          exact f'_mem
      . intro d d_mem
        unfold g
        split
        . apply g_hd_h.right; exact d_mem
        . apply g_tl_h.right; rw [List.mem_append]; apply Or.inl; exact d_mem

  theorem ChaseBranch.backtracking_of_loaded_trigger_in_node [GetFreshInhabitant sig.C] [Inhabited sig.C] (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      ∀ (rl : RuleList sig), (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) ->
      ∀ (trg : PreTrigger sig), (trg_loaded : trg.loaded node.facts) ->
      ∃ (g : ConstantMapping sig),
        g.apply_fact_set (trg.backtrackFacts rl (cb.trigger_ruleIds_valid_of_loaded i node eq rl rl_rs_eq trg trg_loaded) (cb.trigger_disjIdx_valid_of_loaded i node eq rl rl_rs_eq trg trg_loaded) (cb.trigger_rule_arity_valid_of_loaded i node eq rl rl_rs_eq trg trg_loaded)).fst.toSet ⊆ node.facts.val ∧
        (∀ (d : sig.C), d ∈ ((trg.mapped_body.flatMap Fact.constants).toSet ∪ kb.rules.constants) -> g d = .const d) := by
    intro rl rl_rs_eq trg trg_loaded
    have := cb.backtracking_of_term_list_in_node i node eq rl rl_rs_eq (trg.mapped_body.flatMap GeneralizedAtom.terms)
      (by intro t t_mem
          rw [List.mem_toSet, List.mem_flatMap] at t_mem
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          exists f
          constructor
          . apply trg_loaded; rw [List.mem_toSet]; exact f_mem
          . exact t_mem)
      (trg.mapped_body.flatMap Fact.constants ++ rl.rules.flatMap Rule.constants)
      (by apply List.subset_append_of_subset_left
          unfold Fact.constants
          intro d d_mem
          rw [List.mem_flatMap] at d_mem
          rcases d_mem with ⟨t, t_mem, d_mem⟩
          rw [List.mem_flatMap] at t_mem
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          rw [List.mem_flatMap]
          exists f
          constructor
          . exact f_mem
          . rw [List.mem_flatMap]
            exists t)
      (by apply List.subset_append_of_subset_right
          apply List.Subset.refl)

    rcases this with ⟨g, g_h⟩
    exists g
    constructor
    . intro f f_mem
      rcases f_mem with ⟨f', f'_mem, f_eq⟩
      rw [List.mem_toSet] at f'_mem
      unfold PreTrigger.backtrackFacts at f'_mem
      rw [List.mem_append] at f'_mem
      cases f'_mem with
      | inl f'_mem =>
        have : g.apply_fact f' = f' := by
          apply ConstantMapping.apply_fact_eq_self_of_id_on_constants
          intro d d_mem
          apply g_h.right
          rw [List.mem_append]
          apply Or.inl
          rw [List.mem_flatMap]
          exists f'
        rw [f_eq, ← ConstantMapping.apply_fact.eq_def, this]
        apply trg_loaded
        rw [List.mem_toSet]
        exact f'_mem
      | inr f'_mem =>
        apply g_h.left
        exists f'
    . intro d d_mem
      apply g_h.right
      rw [List.mem_append]
      cases d_mem with
      | inl d_mem => apply Or.inl; rw [List.mem_toSet] at d_mem; exact d_mem
      | inr d_mem =>
        apply Or.inr
        rcases d_mem with ⟨r, r_mem, d_mem⟩
        rw [List.mem_flatMap]
        exists r
        rw [rl_rs_eq]
        constructor
        . exact r_mem
        . exact d_mem

end InterplayWithBacktracking

