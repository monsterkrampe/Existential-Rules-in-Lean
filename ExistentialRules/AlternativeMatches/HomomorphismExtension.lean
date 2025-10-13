import ExistentialRules.AlternativeMatches.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace ChaseBranch

  noncomputable def extend_hom_to_next_step_internal (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.facts cb.result) (node' : ChaseNode obs kb.rules) (node_k_succ : cb.branch.infinite_list (k + 1) = node') :
      { h' : GroundTermMapping sig // (∀ t, t ∈ node.facts.val.terms -> h' t = h t) ∧ h'.isHomomorphism node'.facts cb.result } :=
    have : exists_trigger_opt_fs obs kb.rules node (cb.branch.infinite_list (k + 1)) := by
      have trg_ex := cb.triggers_exist k
      rw [node_k] at trg_ex
      simp only [Option.is_none_or] at trg_ex
      cases trg_ex with
      | inr trg_ex => unfold not_exists_trigger_opt_fs at trg_ex; rw [node_k_succ] at trg_ex; simp at trg_ex
      | inl trg_ex => exact trg_ex
    let trg := Classical.choose this
    have ⟨trg_active, trg_res⟩ := Classical.choose_spec this
    let disj_index := Classical.choose trg_res
    have trg_res := Classical.choose_spec trg_res

    let disj_index' : Fin trg.val.rule.head.length := ⟨disj_index.val, by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt⟩

    let trg' : PreTrigger sig := ⟨trg.val.rule, h ∘ trg.val.subs⟩
    have trg'_loaded : trg'.loaded cb.result := by
      apply Set.subset_trans (b := h.applyFactSet node.facts)
      . apply PreTrigger.term_mapping_preserves_loadedness
        . exact hom.left
        . exact trg_active.left
      . apply hom.right
    have trg'_satisfied : trg'.satisfied_for_disj cb.result disj_index' := by
      unfold PreTrigger.satisfied_for_disj
      have modelsRule : cb.result.modelsRule trg'.rule := by
        have modelsKb := ChaseBranch.result_models_kb cb
        exact modelsKb.right trg'.rule trg.property
      specialize modelsRule trg'.subs trg'_loaded
      rcases modelsRule with ⟨i, s', s'_frontier, s'_contains⟩
      exists s'
      constructor
      . exact s'_frontier
      . -- kb.isDeterministic is required here
        have : i = disj_index' := by
          have isLt := i.isLt
          have := det trg'.rule trg.property
          unfold Rule.isDeterministic at this
          rw [decide_eq_true_iff] at this
          simp [this] at isLt
          have isLt' := disj_index'.isLt
          have := det trg.val.rule trg.property
          unfold Rule.isDeterministic at this
          rw [decide_eq_true_iff] at this
          simp [this] at isLt'
          rw [Fin.ext_iff]
          rw [isLt, isLt']
        rw [this] at s'_contains
        exact s'_contains

    let subs := Classical.choose trg'_satisfied
    have ⟨subs_frontier, subs_contained⟩ := Classical.choose_spec trg'_satisfied

    let h' : GroundTermMapping sig := fun t =>
      match ((trg.val.rule.head.get disj_index').vars.find? (fun v => (¬ v ∈ trg.val.rule.frontier) ∧ (trg.val.apply_to_var_or_const disj_index.val (VarOrConst.var v) = t))) with
      | none => h t
      | some v => subs v

    have h'_is_id_on_const : h'.isIdOnConstants := by
      intro term
      cases eq : term with
      | func _ _ => simp [GroundTerm.func]
      | const c =>
        simp only [GroundTerm.const]
        unfold h'
        rw [List.find?_eq_none.mpr]
        . simp; exact GroundTermMapping.apply_constant_is_id_of_isIdOnConstants hom.left c
        . simp
          intro v _ not_frontier contra
          simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, not_frontier, GroundTerm.func] at contra

    have h'_is_subs_on_head_vars : ∀ v, v ∈ (trg.val.rule.head.get disj_index').vars -> (h' (trg.val.apply_to_var_or_const disj_index.val (VarOrConst.var v))) = subs v := by
      intro v v_mem
      cases Decidable.em (v ∈ trg.val.rule.frontier) with
      | inl v_frontier =>
        simp only [subs]
        rw [subs_frontier _ v_frontier]
        simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, VarOrConst.skolemize, GroundSubstitution.apply_skolem_term, v_frontier]
        unfold h'
        rw [List.find?_eq_none.mpr]
        simp [trg']
        intro u u_mem
        simp
        intro u_frontier contra
        have u_result_not_in_frontier_image := trg.val.result_term_not_in_frontier_image_of_var_not_in_frontier ⟨disj_index, by rw [← PreTrigger.length_mapped_head]; exact disj_index.isLt⟩ u u_frontier
        apply u_result_not_in_frontier_image
        rw [contra]
        simp
        exists v
      | inr v_frontier =>
        unfold h'
        rw [List.find?_eq_some_iff_append.mpr]
        simp
        constructor
        . exact v_frontier
        . rw [List.mem_iff_append_and_not_in_first] at v_mem
          rcases v_mem with ⟨as, bs, v_mem, v_not_in_as⟩
          exists as
          constructor
          . exists bs
          . intro u u_mem
            apply Or.inr
            intro contra
            have vars_eq := trg.val.apply_to_var_or_const_injective_of_not_in_frontier disj_index' v_frontier _ (Eq.symm contra)
            rw [VarOrConst.var.injEq] at vars_eq
            rw [vars_eq] at v_not_in_as
            contradiction

    have h'_is_h_on_terms_in_node : ∀ t, t ∈ node.facts.val.terms -> h' t = h t := by
      intro t t_mem
      unfold h'
      rw [List.find?_eq_none.mpr]
      simp
      intro v v_head v_not_frontier contra
      have : trg.val.mapped_head[disj_index.val].toSet ⊆ node.facts := by
        apply cb.funcTermForExisVarInChaseMeansTriggerResultOccurs _ node_k trg disj_index v_not_frontier
        unfold FactSet.terms at t_mem
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        exists f
        constructor
        . exact f_mem
        . rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_not_frontier] at contra; rw [contra]; exact t_mem
      have trg_obs := obs.contains_trg_result_implies_cond disj_index this
      have not_obs := trg_active.right
      contradiction

    ⟨h', by
      constructor
      . exact h'_is_h_on_terms_in_node
      . rw [← trg_res] at node_k_succ
        injection node_k_succ with node_k_succ
        rw [← node_k_succ]
        constructor
        . exact h'_is_id_on_const
        . unfold GroundTermMapping.applyFactSet
          intro f f_mem
          rcases f_mem with ⟨f, f_mem, f_eq⟩
          cases f_mem with
          | inl f_mem => apply hom.right; exists f; constructor; exact f_mem; rw [f_eq]; apply TermMapping.apply_generalized_atom_congr_left; intro t t_mem; apply h'_is_h_on_terms_in_node; exists f
          | inr f_mem =>
            rw [f_eq]
            apply subs_contained
            have : (subs.apply_function_free_conj trg'.rule.head[disj_index'.val]).toSet = h'.applyFactSet trg.val.mapped_head[disj_index.val].toSet := by
              -- TODO: show something like List.map_toSet_eq_toSet_map
              apply Set.ext
              intro f
              rw [List.mem_toSet]
              unfold GroundTermMapping.applyFactSet
              unfold TermMapping.apply_generalized_atom_set
              unfold GroundSubstitution.apply_function_free_conj
              unfold TermMapping.apply_generalized_atom_list
              unfold PreTrigger.mapped_head
              simp
              constructor
              . intro pre
                rcases pre with ⟨a, a_mem, a_eq⟩
                exists trg.val.apply_to_function_free_atom disj_index.val a
                constructor
                . rw [List.mem_toSet]; simp; exists a
                . rw [← a_eq]
                  simp [PreTrigger.apply_to_function_free_atom, TermMapping.apply_generalized_atom]
                  intro voc voc_mem
                  cases voc with
                  | const c => simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize]; apply Eq.symm; exact h'_is_id_on_const (GroundTerm.const c)
                  | var v =>
                    rw [h'_is_subs_on_head_vars]
                    simp [GroundSubstitution.apply_var_or_const]
                    unfold FunctionFreeConjunction.vars
                    simp
                    exists a
                    constructor
                    . exact a_mem
                    . unfold FunctionFreeAtom.variables
                      apply VarOrConst.mem_filterVars_of_var
                      exact voc_mem
              . intro pre
                rcases pre with ⟨b, b_mem, b_eq⟩
                rw [List.mem_toSet] at b_mem
                simp at b_mem
                rcases b_mem with ⟨a, a_mem, a_eq⟩
                exists a
                constructor
                . exact a_mem
                . rw [b_eq, ← a_eq]
                  rw [← Function.comp_apply (f := h'.apply_generalized_atom)]
                  rw [← TermMapping.apply_generalized_atom_compose]
                  apply TermMapping.apply_generalized_atom_congr_left
                  intro voc voc_mem
                  cases voc with
                  | const c => simp [PreTrigger.apply_to_var_or_const, PreTrigger.skolemize_var_or_const, GroundSubstitution.apply_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize]; rw [h'_is_id_on_const (GroundTerm.const c)]
                  | var v =>
                    rw [Function.comp_apply]
                    rw [h'_is_subs_on_head_vars]
                    simp [GroundSubstitution.apply_var_or_const]
                    unfold FunctionFreeConjunction.vars
                    simp
                    exists a
                    constructor
                    . exact a_mem
                    . unfold FunctionFreeAtom.variables
                      apply VarOrConst.mem_filterVars_of_var
                      exact voc_mem
            rw [this]
            exists f
    ⟩

  noncomputable def extend_hom_to_next_step (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.facts cb.result) :
      GroundTermMapping sig :=
    match eq : cb.branch.infinite_list (k + 1) with
    | .none => h
    | .some node' =>
      (extend_hom_to_next_step_internal cb det k node node_k h hom node' eq).val

  theorem extend_hom_to_next_step_eq (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.facts cb.result) :
      extend_hom_to_next_step cb det k node node_k h hom = match eq : cb.branch.infinite_list (k + 1) with
      | .none => h
      | .some node' => (extend_hom_to_next_step_internal cb det k node node_k h hom node' eq).val := by
    unfold extend_hom_to_next_step
    simp

  theorem extended_hom_same_on_next_extensions (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.facts cb.result) : ∀ t, t ∈ node.facts.val.terms -> extend_hom_to_next_step cb det k node node_k h hom t = h t := by
    intro t t_mem
    rw [extend_hom_to_next_step_eq]
    split
    . rfl
    case h_2 node' eq =>
      let result := extend_hom_to_next_step_internal cb det k node node_k h hom node' eq
      rw [result.property.left]
      exact t_mem

  theorem extended_hom_isHomomorphism_on_next_extensions (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.facts cb.result) : (cb.branch.infinite_list (k + 1)).is_none_or (fun node' => (extend_hom_to_next_step cb det k node node_k h hom).isHomomorphism node'.facts cb.result) := by
    rw [extend_hom_to_next_step_eq]
    split
    case h_1 eq => simp [eq, Option.is_none_or]
    case h_2 node' eq =>
      simp [eq, Option.is_none_or]
      let result := extend_hom_to_next_step_internal cb det k node node_k h hom node' eq
      exact result.property.right

  noncomputable def extend_hom_to_any_following_step (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.facts cb.result) : (step_width : Nat) ->
    { h' : GroundTermMapping sig // (cb.branch.infinite_list (k+step_width)).is_none_or (fun node' => h'.isHomomorphism node'.facts cb.result) }
  | .zero => ⟨h, by simp [node_k, Option.is_none_or]; exact hom⟩
  | .succ step_width =>
    let prev_hom := extend_hom_to_any_following_step cb det k node node_k h hom step_width

    match eq : cb.branch.infinite_list (k + step_width) with
    | .none =>
      ⟨prev_hom.val, by
        cases eq2 : cb.branch.infinite_list (k + (step_width + 1)) with
        | none => simp [Option.is_none_or]
        | some _ =>
          have no_holes := cb.branch.no_holes (k + (step_width + 1))
          rw [eq2] at no_holes
          simp at no_holes
          specialize no_holes ⟨k + step_width, by simp⟩
          rw [eq] at no_holes
          simp at no_holes
      ⟩
    | .some node' =>
      ⟨extend_hom_to_next_step cb det (k + step_width) node' eq prev_hom.val (by
        have property := prev_hom.property
        simp only [eq, Option.is_none_or] at property
        exact property
      ), by apply extended_hom_isHomomorphism_on_next_extensions⟩

  theorem extended_hom_same_on_all_following_extensions (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (node : ChaseNode obs kb.rules) (node_k : cb.branch.infinite_list k = some node) (h : GroundTermMapping sig) (hom : h.isHomomorphism node.facts cb.result) : ∀ (i j : Nat), (cb.branch.infinite_list (k + i)).is_none_or (fun node' => ∀ t, t ∈ node'.facts.val.terms -> (extend_hom_to_any_following_step cb det k node node_k h hom (i + j)).val t = (extend_hom_to_any_following_step cb det k node node_k h hom i).val t) := by
    intro i j
    simp [Option.is_none_or]
    split
    . simp
    case h_2 _ _ node' eq =>
      simp only
      induction j with
      | zero => intros; rfl
      | succ j ih =>
        intro t _ t_mem
        specialize ih t _ t_mem
        conv => left; unfold extend_hom_to_any_following_step
        simp
        split
        . simp; exact ih
        case h_2 _ eq2 =>
          simp
          rw [extended_hom_same_on_next_extensions]
          . exact ih
          . have all_following := cb.stepIsSubsetOfAllFollowing (k + i) _ eq j
            rw [← Nat.add_assoc] at eq2
            rw [eq2] at all_following
            simp only [Option.is_none_or] at all_following
            unfold FactSet.terms
            rcases t_mem with ⟨f, f_mem, t_mem⟩
            exists f
            constructor
            . apply all_following; exact f_mem
            . exact t_mem

  theorem hom_for_step_extendable_result (cb : ChaseBranch obs kb) (det : kb.isDeterministic) (k : Nat) (h : GroundTermMapping sig) :
      (cb.branch.infinite_list k).is_none_or (fun node => h.isHomomorphism node.facts cb.result ->
      ∃ (h' : GroundTermMapping sig), (∀ t, t ∈ node.facts.val.terms -> h' t = h t) ∧ h'.isHomomorphism cb.result cb.result) := by
    cases eq : cb.branch.infinite_list k with
    | none => simp [Option.is_none_or]
    | some node =>
      rw [Option.is_none_or]
      intro hom

      let target_h (i : Nat) := extend_hom_to_any_following_step cb det k node eq h hom i

      let global_h : GroundTermMapping sig := fun t =>
        let dec := Classical.propDecidable (∃ f, f ∈ cb.result ∧ t ∈ f.terms)
        match dec with
          | Decidable.isTrue p =>
            let hfl := (Classical.choose_spec p).left
            let i := Classical.choose hfl
            if i ≤ k then h t else (target_h (i-k)).val t
          | Decidable.isFalse _ => t

      have id_on_const : ∀ (c : sig.C), global_h (GroundTerm.const c) = (GroundTerm.const c) := by
        intro c
        simp [global_h]
        split
        case h_1 _ ex_f _ =>
          let hfl := (Classical.choose_spec ex_f).left
          let i := Classical.choose hfl
          split
          . exact hom.left (GroundTerm.const c)
          case isFalse lt =>
            simp at lt
            have i_spec := Classical.choose_spec hfl
            cases eq2 : cb.branch.infinite_list i with
            | none => rw [eq2] at i_spec; simp [Option.is_some_and] at i_spec
            | some node' =>
              have target_hom := (target_h (i-k)).property
              have : cb.branch.infinite_list (k + (i - k)) = cb.branch.infinite_list i := by rw [Nat.add_sub_of_le (Nat.le_of_lt lt)]
              simp only [this] at target_hom
              simp only [eq2, Option.is_none_or] at target_hom
              exact target_hom.left (GroundTerm.const c)
        . rfl

      have apply_uniform_in_step : ∀ i, (cb.branch.infinite_list i).is_none_or (fun node => ∀ f, f ∈ node.facts.val -> global_h.applyFact f = (target_h (i - k)).val.applyFact f) := by
        intro i
        cases eq2 : cb.branch.infinite_list i with
        | none => simp [Option.is_none_or]
        | some node' =>
          simp [Option.is_none_or]
          intro f f_mem
          apply TermMapping.apply_generalized_atom_congr_left
          intro t t_mem
          simp only [global_h]
          split
          case h_2 _ n_ex _ =>
            apply False.elim
            apply n_ex
            exists f
            constructor
            . have subset_result := cb.stepIsSubsetOfResult i
              rw [eq2] at subset_result; simp [Option.is_none_or] at subset_result
              apply subset_result
              exact f_mem
            . exact t_mem
          case h_1 _ ex _ =>
            let j := Classical.choose (Classical.choose_spec ex).left
            have j_spec := Classical.choose_spec (Classical.choose_spec ex).left
            have spec := Classical.choose_spec ex
            cases eq3 : cb.branch.infinite_list j with
            | none => rw [eq3] at j_spec; simp [Option.is_some_and] at j_spec
            | some node'' =>
              rw [eq3] at j_spec; simp [Option.is_some_and] at j_spec
              split
              case isTrue le =>
                unfold target_h
                have target_h_same := extended_hom_same_on_all_following_extensions cb det k node eq h hom 0 (i - k)
                simp [eq, Option.is_none_or] at target_h_same
                specialize target_h_same t
                have : 0 + (i - k) = i - k := by simp
                rw [this] at target_h_same
                rw [target_h_same]
                . unfold extend_hom_to_any_following_step
                  simp
                . have all_following := cb.stepIsSubsetOfAllFollowing j _ eq3 (k - j)
                  rw [Nat.add_sub_of_le le] at all_following
                  rw [eq] at all_following; simp only [Option.is_none_or] at all_following
                  unfold FactSet.terms
                  exists (Classical.choose ex)
                  constructor
                  . apply all_following; exact j_spec
                  . exact spec.right
              case isFalse gt =>
                simp at gt
                cases Decidable.em (i ≤ j) with
                | inl le2 =>
                  cases Decidable.em (i ≤ k) with
                  | inl le3 =>
                    have target_h_same := extended_hom_same_on_all_following_extensions cb det k node eq h hom 0 (j - k)
                    simp [eq, Option.is_none_or] at target_h_same
                    specialize target_h_same t
                    have : 0 + (j - k) = j - k := by simp
                    rw [this] at target_h_same
                    rw [target_h_same]
                    . rw [Nat.sub_eq_zero_of_le le3]
                    . have all_following := cb.stepIsSubsetOfAllFollowing i _ eq2 (k - i)
                      rw [Nat.add_sub_of_le le3] at all_following
                      rw [eq] at all_following; simp only [Option.is_none_or] at all_following
                      unfold FactSet.terms
                      exists f
                      constructor
                      . apply all_following; exact f_mem
                      . exact t_mem
                  | inr gt3 =>
                    simp at gt3
                    have target_h_same := extended_hom_same_on_all_following_extensions cb det k node eq h hom (i - k) (j - i)
                    simp only [Nat.add_sub_of_le (Nat.le_of_lt gt3), eq2, Option.is_none_or] at target_h_same
                    specialize target_h_same t
                    have : (i - k + (j - i)) = j - k := by omega
                    rw [this] at target_h_same
                    rw [target_h_same]
                    exists f
                | inr gt2 =>
                  simp at gt2
                  have target_h_same := extended_hom_same_on_all_following_extensions cb det k node eq h hom (j - k) (i - j)
                  have : cb.branch.infinite_list (k + (j - k)) = cb.branch.infinite_list j := by rw [Nat.add_sub_of_le (Nat.le_of_lt gt)]
                  simp only [this] at target_h_same
                  simp only [eq3, Option.is_none_or] at target_h_same
                  specialize target_h_same t
                  have : (j - k + (i - j)) = i - k := by omega
                  rw [this] at target_h_same
                  rw [target_h_same]
                  exists Classical.choose ex
                  constructor
                  . exact j_spec
                  . exact spec.right

      exists global_h
      constructor
      . intro t t_mem
        unfold global_h
        have ex_f : ∃ f, f ∈ cb.result ∧ t ∈ f.terms := by
          unfold FactSet.terms at t_mem
          rcases t_mem with ⟨f, f_mem, f_eq⟩
          exists f
          constructor
          . have sub_result := cb.stepIsSubsetOfResult k
            simp [eq, Option.is_none_or] at sub_result
            apply sub_result
            exact f_mem
          . exact f_eq
        simp
        split
        . split
          . rfl
          case isFalse lt =>
            let hfl := (Classical.choose_spec ex_f).left
            let i := Classical.choose hfl
            have target_h_same := extended_hom_same_on_all_following_extensions cb det k node eq h hom 0 (i - k)
            simp [eq, Option.is_none_or] at target_h_same
            specialize target_h_same t.val t.property t_mem
            have : 0 + (i - k) = i - k := by simp
            unfold target_h
            rw [← this, target_h_same]
            unfold extend_hom_to_any_following_step
            simp
        . contradiction
      . constructor
        . intro t
          cases eq : t with
          | func _ _ => simp [GroundTerm.func]
          | const c =>
            exact id_on_const c
        . intro f f_mem
          unfold GroundTermMapping.applyFactSet at f_mem
          rcases f_mem with ⟨f_arg, f_arg_mem, f_eq⟩
          unfold ChaseBranch.result at f_arg_mem
          rcases f_arg_mem with ⟨n, f_arg_mem⟩
          cases eq2 : cb.branch.infinite_list n with
          | none => simp [eq2, Option.is_some_and] at f_arg_mem
          | some node' =>
            simp [eq2, Option.is_some_and] at f_arg_mem
            have := apply_uniform_in_step n
            rw [eq2, Option.is_none_or] at this
            specialize this _ f_arg_mem
            unfold GroundTermMapping.applyFact at this
            rw [this] at f_eq
            rw [f_eq]
            have target_h_property := (target_h (n-k)).property
            cases Decidable.em (n ≤ k) with
            | inl le =>
              simp [Nat.sub_eq_zero_of_le le] at target_h_property
              rw [eq, Option.is_none_or] at target_h_property
              apply target_h_property.right
              apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
              have all_following := cb.stepIsSubsetOfAllFollowing n _ eq2 (k - n)
              rw [Nat.add_sub_of_le le] at all_following
              rw [eq] at all_following
              simp only [Option.is_none_or] at all_following
              apply all_following
              exact f_arg_mem
            | inr gt =>
              simp at gt
              simp only [Nat.add_sub_of_le (Nat.le_of_lt gt), eq2, Option.is_none_or] at target_h_property
              apply target_h_property.right
              apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
              exact f_arg_mem

end ChaseBranch

