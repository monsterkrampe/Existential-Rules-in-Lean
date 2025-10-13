import ExistentialRules.ChaseSequence.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

abbrev InductiveHomomorphismResult (ct : ChaseTree obs kb) (m : FactSet sig) (depth : Nat) := {pair : (List Nat) × (GroundTermMapping sig) // pair.1.length = depth ∧ (ct.tree.get pair.1).is_none_or (fun fs => pair.2.isHomomorphism fs.facts m) }

noncomputable def inductive_homomorphism_with_prev_node_and_trg (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) (trg_ex : exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst)) : InductiveHomomorphismResult ct m (prev_depth + 1) :=
  let prev_path := prev_result.val.fst
  let prev_hom := prev_result.val.snd
  let prev_cond := prev_result.property
  have prev_hom_is_homomorphism : prev_hom.isHomomorphism prev_node_unwrapped.facts m := by
    have prev_cond_r := prev_cond.right
    rw [prev_node_eq] at prev_cond_r
    simp [Option.is_none_or] at prev_cond_r
    exact prev_cond_r

  let trg := Classical.choose trg_ex
  let trg_spec := Classical.choose_spec trg_ex
  let trg_active_for_current_step := trg_spec.left
  let trg_result_used_for_next_chase_step := trg_spec.right

  let trg_variant_for_m : RTrigger obs kb.rules := {
    val := {
      rule := trg.val.rule
      subs := fun t => prev_hom (trg.val.subs t)
    }
    property := trg.property
  }
  have trg_variant_loaded_for_m : trg_variant_for_m.val.loaded m := by
    have : trg_variant_for_m.val.loaded (prev_hom.applyFactSet prev_node_unwrapped.facts) := by
      apply PreTrigger.term_mapping_preserves_loadedness
      . exact prev_hom_is_homomorphism.left
      . exact trg_active_for_current_step.left
    apply Set.subset_trans
    . exact this
    . exact prev_hom_is_homomorphism.right
  have trg_variant_satisfied_on_m : trg_variant_for_m.val.satisfied m := by
    have m_models_rule : m.modelsRule trg_variant_for_m.val.rule := by exact m_is_model.right trg.val.rule trg.property
    unfold FactSet.modelsRule at m_models_rule
    apply m_models_rule
    apply trg_variant_loaded_for_m

  let head_index_for_m_subs := Classical.choose trg_variant_satisfied_on_m
  let h_head_index_for_m_subs := Classical.choose_spec trg_variant_satisfied_on_m
  let obs_for_m_subs := Classical.choose h_head_index_for_m_subs
  let h_obs_at_head_index_for_m_subs := Classical.choose_spec h_head_index_for_m_subs

  let result_index_for_trg : Fin trg.val.mapped_head.length := ⟨head_index_for_m_subs.val, by unfold PreTrigger.mapped_head; simp; exact head_index_for_m_subs.isLt⟩

  let next_hom : GroundTermMapping sig := fun t =>
    match t.val with
    | FiniteTree.leaf _ => t
    | FiniteTree.inner _ _ =>
      let t_in_step_j_dec := Classical.propDecidable (∃ f, f ∈ prev_node_unwrapped.facts.val ∧ t ∈ f.terms)
      match t_in_step_j_dec with
      | Decidable.isTrue _ => prev_hom t
      | Decidable.isFalse _ =>
        let t_in_trg_result_dec := Classical.propDecidable (∃ f, f ∈ (trg.val.mapped_head[result_index_for_trg.val]) ∧ t ∈ f.terms)
        match t_in_trg_result_dec with
        | Decidable.isFalse _ => t
        | Decidable.isTrue t_in_trg_result =>
          let f := Classical.choose t_in_trg_result
          let f_spec := Classical.choose_spec t_in_trg_result
          let v_for_t := trg.val.var_or_const_for_result_term result_index_for_trg f_spec.left f_spec.right
          obs_for_m_subs.apply_var_or_const v_for_t

  have next_hom_id_const : next_hom.isIdOnConstants := by
    intro term
    cases eq : term with
    | const c => simp [GroundTerm.const, next_hom]
    | func _ _ => simp [GroundTerm.func]

  ⟨(head_index_for_m_subs.val::prev_path, next_hom), by
    have prev_cond_r := prev_cond.right
    rw [prev_node_eq] at prev_cond_r
    rw [Option.is_none_or] at prev_cond_r

    constructor
    . simp only [List.length_cons, Nat.add_right_cancel_iff]; exact prev_cond.left
    rw [Option.is_none_or_iff]
    intro next_node next_node_eq
    constructor
    . exact next_hom_id_const
    have next_node_results_from_trg : next_node.facts = prev_node_unwrapped.facts.val ∪ trg.val.mapped_head[result_index_for_trg.val].toSet := by
      have length_eq_helper_1 : trg.val.rule.head.length = trg.val.mapped_head.zipIdx_with_lt.attach.length := by
        rw [List.length_attach, List.length_zipIdx_with_lt]
        unfold PreTrigger.mapped_head
        rw [List.length_map, List.length_zipIdx]
      have length_eq_helper_2 : trg_variant_for_m.val.rule.head.length = (ct.tree.children prev_path).length := by
        rw [← trg_result_used_for_next_chase_step, List.length_map]
        exact length_eq_helper_1
      rw [List.map_eq_iff] at trg_result_used_for_next_chase_step
      specialize trg_result_used_for_next_chase_step head_index_for_m_subs.val
      have index_valid : head_index_for_m_subs < (ct.tree.children prev_path).length := by rw [← length_eq_helper_2]; exact head_index_for_m_subs.isLt
      rw [List.getElem?_eq_getElem (l:=ct.tree.children prev_path) (i:=head_index_for_m_subs) index_valid] at trg_result_used_for_next_chase_step
      rw [List.getElem?_eq_getElem (l:=trg.val.mapped_head.zipIdx_with_lt.attach) (i:=head_index_for_m_subs) (by rw [← length_eq_helper_1]; exact head_index_for_m_subs.isLt)] at trg_result_used_for_next_chase_step
      rw [Option.map_some] at trg_result_used_for_next_chase_step
      injection trg_result_used_for_next_chase_step with trg_result_used_for_next_chase_step
      have : some (ct.tree.children prev_path)[head_index_for_m_subs.val] = some next_node := by
        rw [ct.tree.getElem_children_eq_get prev_path ⟨head_index_for_m_subs.val, index_valid⟩]
        exact next_node_eq
      injection this with this
      rw [this] at trg_result_used_for_next_chase_step
      rw [trg_result_used_for_next_chase_step]
      rw [List.getElem_attach]
      simp only
      rw [List.get_eq_getElem, List.zipIdx_with_lt_getElem_fst_eq_getElem]
    rw [next_node_results_from_trg]

    intro mapped_fact fact_in_chase

    rcases fact_in_chase with ⟨fact, fact_in_chase, rw_aux⟩
    rw [rw_aux]

    cases fact_in_chase with
    | inl fact_in_prev_step =>
      apply prev_cond_r.right
      exists fact
      constructor
      . exact fact_in_prev_step
      . apply TermMapping.apply_generalized_atom_congr_left
        intro ground_term _
        have : ∃ f, f ∈ prev_node_unwrapped.facts.val ∧ ground_term ∈ f.terms := by
          exists fact
        cases eq : ground_term with
        | const c =>
          apply Eq.symm
          apply GroundTermMapping.apply_constant_is_id_of_isIdOnConstants prev_cond_r.left c
        | func _ _ =>
          simp only [GroundTerm.func, next_hom]
          split
          . rfl
          . simp only [eq, GroundTerm.func] at this
            contradiction
    | inr fact_in_trg_result =>
      apply h_obs_at_head_index_for_m_subs.right
      rw [List.mem_toSet]
      rw [List.mem_toSet] at fact_in_trg_result
      unfold GroundSubstitution.apply_function_free_conj
      unfold TermMapping.apply_generalized_atom_list
      rw [List.mem_map]
      exists (trg.val.atom_for_result_fact result_index_for_trg fact_in_trg_result)
      constructor
      . unfold trg_variant_for_m
        unfold PreTrigger.atom_for_result_fact
        apply List.getElem_mem
      . simp only
        conv => right; rw [← trg.val.apply_on_atom_for_result_fact_is_fact result_index_for_trg fact_in_trg_result]
        rw [← PreTrigger.apply_subs_for_atom_eq]
        rw [← Function.comp_apply (f := TermMapping.apply_generalized_atom next_hom)]
        rw [← GroundTermMapping.applyFact.eq_def, ← GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants _ _ next_hom_id_const]
        apply TermMapping.apply_generalized_atom_congr_left
        intro voc voc_mem
        cases voc with
        | const c => simp [GroundSubstitution.apply_var_or_const]
        | var v =>
          rw [GroundSubstitution.apply_var_or_const_compose_of_isIdOnConstants _ _ next_hom_id_const]
          simp only [Function.comp_apply, GroundSubstitution.apply_var_or_const]
          cases Decidable.em (v ∈ trg.val.rule.frontier) with
          | inl v_front =>
            rw [h_obs_at_head_index_for_m_subs.left v v_front]
            unfold PreTrigger.subs_for_mapped_head
            rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ v_front]
            unfold trg_variant_for_m
            simp only
            cases eq_v : trg.val.subs v with
            | const c =>
              unfold GroundTerm.const
              unfold next_hom
              simp only
              apply GroundTermMapping.apply_constant_is_id_of_isIdOnConstants
              exact prev_hom_is_homomorphism.left
            | func func ts arity_ok =>
              unfold GroundTerm.func
              unfold next_hom
              simp only
              have h : ∃ f, f ∈ prev_node_unwrapped.facts.val ∧ (GroundTerm.func func ts arity_ok) ∈ f.terms := by
                rcases trg.val.rule.frontier_occurs_in_body v v_front with ⟨body_atom, v_front'⟩
                exists trg.val.subs.apply_function_free_atom body_atom
                constructor
                . apply trg_active_for_current_step.left
                  rw [List.mem_toSet]
                  apply List.mem_map_of_mem
                  exact v_front'.left
                . rw [← eq_v]
                  unfold GroundSubstitution.apply_function_free_atom
                  unfold TermMapping.apply_generalized_atom
                  rw [List.mem_map]
                  exists VarOrConst.var v
                  simp [GroundSubstitution.apply_var_or_const, v_front'.right]

              have : Classical.propDecidable (∃ f, f ∈ prev_node_unwrapped.facts.val ∧ (GroundTerm.func func ts arity_ok) ∈ f.terms) = isTrue h := by cases Classical.propDecidable (∃ f, f ∈ prev_node_unwrapped.facts.val ∧ (GroundTerm.func func ts arity_ok) ∈ f.terms) <;> trivial
              unfold GroundTerm.func at this
              rw [this]
          | inr v_front =>
            unfold PreTrigger.subs_for_mapped_head
            rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
            unfold PreTrigger.functional_term_for_var
            unfold next_hom

            have h : ¬ ∃ f, f ∈ prev_node_unwrapped.facts.val ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms := by
              intro contra
              apply trg_active_for_current_step.right
              apply obs.contains_trg_result_implies_cond result_index_for_trg
              apply ChaseTree.funcTermForExisVarInChaseMeansTriggerResultOccurs
              . exact prev_node_eq
              . exact v_front
              . exact contra
            have : Classical.propDecidable (∃ f, f ∈ prev_node_unwrapped.facts.val ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms) = isFalse h := by cases Classical.propDecidable (∃ f, f ∈ prev_node_unwrapped.facts.val ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms) <;> trivial
            unfold PreTrigger.functional_term_for_var at this
            rw [this]

            have h : ∃ f, f ∈ (trg.val.mapped_head[result_index_for_trg.val]) ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms := by
              exists fact
              constructor
              . exact fact_in_trg_result
              . rw [← trg.val.apply_on_atom_for_result_fact_is_fact result_index_for_trg fact_in_trg_result]
                rw [← trg.val.apply_to_var_or_const_non_frontier_var _ _ v_front]
                unfold PreTrigger.apply_to_function_free_atom
                apply List.mem_map_of_mem
                exact voc_mem

            have : Classical.propDecidable (∃ f, f ∈ (trg.val.mapped_head[result_index_for_trg.val]) ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms) = isTrue h := by cases Classical.propDecidable (∃ f, f ∈ (trg.val.mapped_head[result_index_for_trg.val]) ∧ (trg.val.functional_term_for_var result_index_for_trg.val v) ∈ f.terms) <;> trivial
            unfold PreTrigger.functional_term_for_var at this
            rw [this]
            simp only [GroundTerm.func]

            have spec := Classical.choose_spec h
            have : trg.val.var_or_const_for_result_term result_index_for_trg spec.left spec.right = VarOrConst.var v := by
              have : (trg.val.apply_to_var_or_const result_index_for_trg.val (trg.val.var_or_const_for_result_term result_index_for_trg spec.left spec.right)) = trg.val.apply_to_var_or_const result_index_for_trg.val (VarOrConst.var v) := by
                rw [PreTrigger.apply_on_var_or_const_for_result_term_is_term]
                rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
              apply Eq.symm
              apply trg.val.apply_to_var_or_const_injective_of_not_in_frontier ⟨result_index_for_trg.val, by rw [← PreTrigger.length_mapped_head]; exact result_index_for_trg.isLt⟩ v_front
              rw [this]
            rw [this]
            simp only [GroundSubstitution.apply_var_or_const]
            rfl
  ⟩

noncomputable def inductive_homomorphism_with_prev_node (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) : InductiveHomomorphismResult ct m (prev_depth + 1) :=
  let trg_ex_dec := Classical.propDecidable (exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst))
  match trg_ex_dec with
  | .isFalse _ =>
    let ⟨(prev_path, prev_hom), prev_cond⟩ := prev_result
    -- just prepending zero here as it does not really matter which index we append but the length must match
    ⟨(0::prev_path, prev_hom), by
      constructor
      . simp; exact prev_cond.left
      . have : ct.tree.get (0::prev_path) = none := by
          apply FiniteDegreeTree.each_successor_none_of_children_empty
          let triggers_exist := ct.triggers_exist prev_path
          rw [prev_node_eq] at triggers_exist
          simp [Option.is_none_or] at triggers_exist
          cases triggers_exist with
          | inl _ => contradiction
          | inr hr => unfold not_exists_trigger_list at hr; exact hr.right
        rw [this]
        simp [Option.is_none_or]
    ⟩
  | .isTrue trg_ex =>
    inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex

noncomputable def inductive_homomorphism (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) : (depth : Nat) ->
  InductiveHomomorphismResult ct m depth
| .zero => ⟨([], id), by
  simp [Option.is_none_or]; rw [ct.database_first]; simp
  constructor
  . unfold GroundTermMapping.isIdOnConstants; intro gt; cases gt <;> simp [GroundTerm.const, GroundTerm.func]
  . intro el
    intro el_in_set
    cases el_in_set with | intro f hf =>
      apply m_is_model.left
      have : f = el := by have hfr := hf.right; rw [hfr]; simp [TermMapping.apply_generalized_atom]
      rw [this] at hf
      exact hf.left
⟩
| .succ j =>
  let prev_path := (inductive_homomorphism ct m m_is_model j).val.fst
  let prev_hom := (inductive_homomorphism ct m m_is_model j).val.snd
  let prev_cond := (inductive_homomorphism ct m m_is_model j).property
  let prev_node := ct.tree.get prev_path

  match prev_node_eq : prev_node with
  | .none =>
    -- just prepending zero here as it does not really matter which index we append but the length must match
    ⟨(0::prev_path, prev_hom), by
      constructor
      . simp; exact prev_cond.left
      . have : ct.tree.get (0::prev_path) = none := by
          apply Option.decidableEqNone.byContradiction
          intro contra
          apply ct.tree.tree.no_orphans _ contra ⟨prev_path, by exists [0]⟩
          simp [prev_node] at prev_node_eq
          unfold FiniteDegreeTree.get at prev_node_eq
          unfold PossiblyInfiniteTree.get at prev_node_eq
          simp
          exact prev_node_eq
        rw [this]
        simp [Option.is_none_or]
    ⟩
  | .some prev_node_unwrapped =>
    inductive_homomorphism_with_prev_node ct m m_is_model j ⟨⟨prev_path, prev_hom⟩, prev_cond⟩ prev_node_unwrapped prev_node_eq
termination_by depth => depth

theorem inductive_homomorphism_with_prev_node_and_trg_path_not_empty (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) (trg_ex : exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst)) : (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex).val.1 ≠ [] := by
  unfold inductive_homomorphism_with_prev_node_and_trg
  simp

theorem inductive_homomorphism_with_prev_node_path_not_empty (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) : (inductive_homomorphism_with_prev_node ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq).val.1 ≠ [] := by
  unfold inductive_homomorphism_with_prev_node
  simp only
  split
  . simp
  apply inductive_homomorphism_with_prev_node_and_trg_path_not_empty

theorem inductive_homomorphism_path_not_empty {ct : ChaseTree obs kb} : ∀ n, (inductive_homomorphism ct m m_is_model (n+1)).val.1 ≠ [] := by
  intro n
  unfold inductive_homomorphism
  simp only
  split
  . simp
  apply inductive_homomorphism_with_prev_node_path_not_empty

theorem inductive_homomorphism_with_prev_node_and_trg_path_extends_prev (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) (trg_ex : exists_trigger_list obs kb.rules prev_node_unwrapped (ct.tree.children prev_result.val.fst)) : (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex).val.1 = ((inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq trg_ex).val.1.head (by apply inductive_homomorphism_with_prev_node_and_trg_path_not_empty)) :: prev_result.val.fst := by
  unfold inductive_homomorphism_with_prev_node_and_trg
  simp

theorem inductive_homomorphism_with_prev_node_path_extends_prev (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) (prev_depth : Nat) (prev_result : InductiveHomomorphismResult ct m prev_depth) (prev_node_unwrapped : ChaseNode obs kb.rules) (prev_node_eq : ct.tree.get prev_result.val.fst = some prev_node_unwrapped) : (inductive_homomorphism_with_prev_node ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq).val.1 = ((inductive_homomorphism_with_prev_node ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq).val.1.head (by apply inductive_homomorphism_with_prev_node_path_not_empty)) :: prev_result.val.fst := by
  conv => left; rw [List.head_cons_tail_of_ne_nil (inductive_homomorphism_with_prev_node_path_not_empty ct m m_is_model prev_depth prev_result prev_node_unwrapped prev_node_eq)]
  rw [List.cons.injEq]
  constructor
  . rfl
  . unfold inductive_homomorphism_with_prev_node
    simp only
    split
    . rfl
    . rw [inductive_homomorphism_with_prev_node_and_trg_path_extends_prev]
      rfl

theorem inductive_homomorphism_path_extends_prev {ct : ChaseTree obs kb} : ∀ n, (inductive_homomorphism ct m m_is_model (n+1)).val.1 = ((inductive_homomorphism ct m m_is_model (n+1)).val.1.head (by apply inductive_homomorphism_path_not_empty)) :: (inductive_homomorphism ct m m_is_model n).val.1 := by
  intro n
  conv => left; rw [List.head_cons_tail_of_ne_nil (inductive_homomorphism_path_not_empty n)]
  rw [List.cons.injEq]
  constructor
  . rfl
  . conv => left; unfold inductive_homomorphism
    simp only
    split
    . rfl
    . rw [inductive_homomorphism_with_prev_node_path_extends_prev]
      rfl

theorem inductive_homomorphism_path_extends_all_prev {ct : ChaseTree obs kb} : ∀ n d, (inductive_homomorphism ct m m_is_model (n+d)).val.1 = ((inductive_homomorphism ct m m_is_model (n+d)).val.1.take d) ++ (inductive_homomorphism ct m m_is_model n).val.1 := by
  intro n d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc]
    rw [inductive_homomorphism_path_extends_prev (n+d)]
    simp
    exact ih

theorem inductive_homomorphism_with_prev_node_and_trg_latest_index_lt_trg_result_length
  {ct : ChaseTree obs kb}
  (prev_step : Nat)
  (prev_node : ChaseNode obs kb.rules)
  (prev_ex : some prev_node = ct.tree.get (inductive_homomorphism ct m m_is_model prev_step).val.1)
  (trg_ex : exists_trigger_list obs kb.rules prev_node (ct.tree.children (inductive_homomorphism ct m m_is_model prev_step).val.1))
  : (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_step _ _ (Eq.symm prev_ex) trg_ex).val.1.head (by apply inductive_homomorphism_with_prev_node_and_trg_path_not_empty) < (Classical.choose trg_ex).val.mapped_head.length := by
    let prev_result := inductive_homomorphism ct m m_is_model prev_step
    let prev_hom := prev_result.val.snd
    let prev_cond := prev_result.property
    have prev_hom_is_homomorphism : prev_hom.isHomomorphism prev_node.facts m := by
      have prev_cond_r := prev_cond.right
      simp only [prev_result] at prev_cond_r
      rw [← prev_ex] at prev_cond_r
      simp [Option.is_none_or] at prev_cond_r
      exact prev_cond_r

    let trg := Classical.choose trg_ex
    let trg_spec := Classical.choose_spec trg_ex
    let trg_active_for_current_step := trg_spec.left

    let trg_variant_for_m : RTrigger obs kb.rules := {
      val := {
        rule := trg.val.rule
        subs := fun t => prev_hom (trg.val.subs t)
      }
      property := trg.property
    }
    have trg_variant_loaded_for_m : trg_variant_for_m.val.loaded m := by
      have : trg_variant_for_m.val.loaded (prev_hom.applyFactSet prev_node.facts) := by
        apply PreTrigger.term_mapping_preserves_loadedness
        . exact prev_hom_is_homomorphism.left
        . exact trg_active_for_current_step.left
      apply Set.subset_trans
      . exact this
      . exact prev_hom_is_homomorphism.right
    have trg_variant_satisfied_on_m : trg_variant_for_m.val.satisfied m := by
      have m_models_rule : m.modelsRule trg_variant_for_m.val.rule := by exact m_is_model.right trg.val.rule trg.property
      unfold FactSet.modelsRule at m_models_rule
      apply m_models_rule
      apply trg_variant_loaded_for_m

    let head_index_for_m_subs := Classical.choose trg_variant_satisfied_on_m

    have : (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_step (inductive_homomorphism ct m m_is_model prev_step) prev_node (by rw [prev_ex]) trg_ex).val.fst = head_index_for_m_subs.val :: prev_result.val.fst := by
      unfold inductive_homomorphism_with_prev_node_and_trg
      simp [head_index_for_m_subs, prev_result]
    simp [this]
    have isLt := head_index_for_m_subs.isLt
    simp only [trg_variant_for_m, trg] at isLt
    simp only [← PreTrigger.length_mapped_head] at isLt
    simp
    exact isLt

theorem inductive_homomorphism_latest_index_lt_trg_result_length
  {ct : ChaseTree obs kb}
  (prev_step : Nat)
  (prev_node : ChaseNode obs kb.rules)
  (prev_ex : some prev_node = ct.tree.get (inductive_homomorphism ct m m_is_model prev_step).val.1)
  (trg_ex : exists_trigger_list obs kb.rules prev_node (ct.tree.children (inductive_homomorphism ct m m_is_model prev_step).val.1))
  : (inductive_homomorphism ct m m_is_model (prev_step+1)).val.1.head (by apply inductive_homomorphism_path_not_empty) < (Classical.choose trg_ex).val.mapped_head.length := by

    have : inductive_homomorphism ct m m_is_model (prev_step + 1) = inductive_homomorphism_with_prev_node ct m m_is_model prev_step (inductive_homomorphism ct m m_is_model prev_step) prev_node (by rw [prev_ex]) := by
      conv => left; unfold inductive_homomorphism
      simp
      split
      case h_1 heq => rw [heq] at prev_ex; contradiction
      case h_2 heq =>
        rw [heq] at prev_ex
        injection prev_ex with prev_ex
        simp [← prev_ex]
    simp [this]

    have : inductive_homomorphism_with_prev_node ct m m_is_model prev_step (inductive_homomorphism ct m m_is_model prev_step) prev_node (by rw [prev_ex]) = inductive_homomorphism_with_prev_node_and_trg ct m m_is_model prev_step (inductive_homomorphism ct m m_is_model prev_step) prev_node (Eq.symm prev_ex) trg_ex := by
      conv => left; unfold inductive_homomorphism_with_prev_node
      simp
      split
      case h_1 _ h _ => apply False.elim; apply h; apply trg_ex
      case h_2 => simp
    simp [this]

    apply inductive_homomorphism_with_prev_node_and_trg_latest_index_lt_trg_result_length
    exact prev_ex

theorem inductive_homomorphism_tree_get_path_none_means_layer_empty {ct : ChaseTree obs kb} : ∀ n, ct.tree.get (inductive_homomorphism ct m m_is_model (n+1)).val.fst = none -> ct.tree.children (inductive_homomorphism ct m m_is_model n).val.fst = [] := by
  intro n succ_none
  unfold inductive_homomorphism at succ_none
  simp at succ_none
  split at succ_none
  . simp at succ_none; apply ct.tree.children_empty_of_first_successor_none; exact succ_none
  case h_2 _ heq =>
    unfold inductive_homomorphism_with_prev_node at succ_none
    simp at succ_none
    split at succ_none
    . simp at succ_none; apply ct.tree.children_empty_of_first_successor_none; exact succ_none
    case h_2 _ ex _ =>
      let child_index : Fin (ct.tree.children (inductive_homomorphism ct m m_is_model n).val.fst).length := ⟨
        (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model n _ _ heq ex).val.1.head (by apply inductive_homomorphism_with_prev_node_and_trg_path_not_empty),
        by
          let trg_spec := Classical.choose_spec ex
          rw [← trg_spec.right]
          simp
          rw [List.length_zipIdx_with_lt]
          apply inductive_homomorphism_with_prev_node_and_trg_latest_index_lt_trg_result_length
          rw [heq]
      ⟩

      let child := (ct.tree.children (inductive_homomorphism ct m m_is_model n).val.fst)[child_index.val]
      have : some child = ct.tree.get (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model n _ _ heq ex).val.fst := by
        simp only [child]
        rw [ct.tree.getElem_children_eq_get _ child_index]
        have : child_index.val :: (inductive_homomorphism ct m m_is_model n).val.fst = (inductive_homomorphism_with_prev_node_and_trg ct m m_is_model n _ _ heq ex).val.fst := by rw [inductive_homomorphism_with_prev_node_and_trg_path_extends_prev]
        rw [this]

      rw [← this] at succ_none
      contradiction

theorem inductive_homomorphism_same_on_terms_in_next_step (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) : ∀ i, (ct.tree.get (inductive_homomorphism ct m m_is_model i).val.fst).is_none_or (fun node => ∀ f t, f ∈ node.facts.val ∧ t ∈ f.terms -> (inductive_homomorphism ct m m_is_model i).val.snd t = (inductive_homomorphism ct m m_is_model i.succ).val.snd t) := by
  intro i
  cases eq : ct.tree.get (inductive_homomorphism ct m m_is_model i).val.fst with
  | none => simp [Option.is_none_or]
  | some node =>
    intro f t precondition
    conv => rhs; unfold inductive_homomorphism; simp
    split
    case h_1 _ => simp
    case h_2 heq =>
      unfold inductive_homomorphism_with_prev_node
      simp
      split
      . simp
      . unfold inductive_homomorphism_with_prev_node_and_trg
        simp
        split
        case h_1 c c_eq =>
          have c_eq : t = GroundTerm.const c := by apply Subtype.eq; exact c_eq
          rw [c_eq]
          have property := (inductive_homomorphism ct m m_is_model i).property.right
          rw [eq] at property; simp [Option.is_none_or] at property
          exact GroundTermMapping.apply_constant_is_id_of_isIdOnConstants property.left c
        case h_2 ft =>
          split
          case h_1 _ ex_f _ => rfl
          case h_2 _ n_ex_f _ =>
            apply False.elim; apply n_ex_f; exists f; constructor
            . rw [heq] at eq; injection eq with eq; rw [eq]; exact precondition.left
            . exact precondition.right

theorem inductive_homomorphism_same_on_all_following_terms (ct : ChaseTree obs kb) (m : FactSet sig) (m_is_model : m.modelsKb kb) : ∀ i, (ct.tree.get (inductive_homomorphism ct m m_is_model i).val.fst).is_none_or (fun node => ∀ j f t, f ∈ node.facts.val ∧ t ∈ f.terms -> (inductive_homomorphism ct m m_is_model i).val.snd t = (inductive_homomorphism ct m m_is_model (i+j)).val.snd t) := by
  intro i
  cases eq : ct.tree.get (inductive_homomorphism ct m m_is_model i).val.fst with
  | none => simp [Option.is_none_or]
  | some node =>
    intro j f t
    induction j with
    | zero => intros; rfl
    | succ j ih =>
      intro precond
      rw [ih precond]
      have next_step := inductive_homomorphism_same_on_terms_in_next_step ct m m_is_model (i + j)
      cases eq2 : ct.tree.get (inductive_homomorphism ct m m_is_model (i+j)).val.fst with
      | none =>
        conv => right; unfold inductive_homomorphism
        simp
        split
        case h_1 _ => simp
        case h_2 heq => rw [heq] at eq2; contradiction
      | some node2 =>
        rw [eq2] at next_step; simp [Option.is_none_or] at next_step
        specialize next_step f t
        apply next_step
        . have subset_following := ct.stepIsSubsetOfAllFollowing (inductive_homomorphism ct m m_is_model i).val.fst node eq ((inductive_homomorphism ct m m_is_model (i+j)).val.fst.take j)
          rw [← inductive_homomorphism_path_extends_all_prev i j] at subset_following
          rw [eq2] at subset_following
          simp only [Option.is_none_or] at subset_following
          apply subset_following
          exact precond.left
        . exact precond.right

theorem chaseTreeResultIsUniversal (ct : ChaseTree obs kb) : ∀ (m : FactSet sig), m.modelsKb kb -> ∃ (fs : FactSet sig) (h : GroundTermMapping sig), fs ∈ ct.result ∧ h.isHomomorphism fs m := by
  intro m m_is_model

  let inductive_homomorphism_shortcut := inductive_homomorphism ct m m_is_model

  let indices : InfiniteList Nat := fun n => (inductive_homomorphism_shortcut (n + 1)).val.1.head (by apply inductive_homomorphism_path_not_empty)

  have indices_aux_result : ∀ n, (indices.take n).reverse = (inductive_homomorphism_shortcut n).val.1 := by
    intro n
    induction n with
    | zero =>
      simp [inductive_homomorphism_shortcut]
      unfold inductive_homomorphism
      unfold InfiniteList.take
      simp
    | succ n ih =>
      unfold InfiniteList.take
      rw [List.reverse_append]
      simp
      rw [inductive_homomorphism_path_extends_prev]
      simp
      constructor
      . simp only [indices, inductive_homomorphism_shortcut]
      . exact ih

  let path : Nat -> Option (ChaseNode obs kb.rules) := fun n => (ct.tree.get (inductive_homomorphism_shortcut n).val.1)
  let nodes : PossiblyInfiniteList (ChaseNode obs kb.rules) := {
    infinite_list := path
    no_holes := by
      intro n path_not_none m
      simp only [path]
      simp only [path] at path_not_none
      unfold FiniteDegreeTree.get at path_not_none
      unfold PossiblyInfiniteTree.get at path_not_none
      have no_orphans := ct.tree.tree.no_orphans
        (inductive_homomorphism_shortcut n).val.1
        path_not_none
        ⟨(inductive_homomorphism_shortcut m).val.1, by
          exists ((indices.skip m).take (n - m)).reverse
          rw [← indices_aux_result m]
          rw [← List.reverse_append]
          rw [InfiniteList.combine_skip_take]
          exact indices_aux_result n
        ⟩
      exact no_orphans
  }
  have nodes_is_tree_branch : nodes ∈ ct.tree.branches := by
    exists indices
    constructor
    . constructor
      . rfl
      . intro n eq_none
        rw [indices_aux_result] at eq_none
        rw [indices_aux_result]
        apply FiniteDegreeTree.each_successor_none_of_children_empty
        apply inductive_homomorphism_tree_get_path_none_means_layer_empty n
        exact eq_none
    . simp only [nodes, path]
      unfold PossiblyInfiniteTree.branch_for_address
      unfold InfiniteTreeSkeleton.branch_for_address
      simp only [PossiblyInfiniteList.eq_iff_same_on_all_indices]
      intro n
      rw [indices_aux_result]
      rfl

  let branch : ChaseBranch obs kb := ct.chase_branch_for_tree_branch nodes nodes_is_tree_branch
  let result := branch.result

  let global_h : GroundTermMapping sig := fun t =>
    let dec := Classical.propDecidable (∃ f, f ∈ result ∧ t ∈ f.terms)
    match dec with
      | Decidable.isTrue p =>
        let hfl := (Classical.choose_spec p).left
        let i := Classical.choose hfl
        let target_h := (inductive_homomorphism_shortcut i).val.2
        target_h t
      | Decidable.isFalse _ => t

  have : ∀ i, (branch.branch.infinite_list i).is_none_or (fun chase_node => ∀ f, f ∈ chase_node.facts.val -> global_h.applyFact f = (inductive_homomorphism_shortcut i).val.snd.applyFact f) := by
    intro i
    rw [Option.is_none_or_iff]
    intro node eq
    intro f f_in_node
    apply TermMapping.apply_generalized_atom_congr_left
    intro t t_mem
    simp only [global_h]
    split
    case h_2 _ n_ex _ =>
      apply False.elim
      apply n_ex
      exists f
      constructor
      . have subset_result := branch.stepIsSubsetOfResult i
        rw [eq] at subset_result; simp [Option.is_none_or] at subset_result
        apply subset_result
        exact f_in_node
      . exact t_mem
    case h_1 _ ex _ =>
      let j := Classical.choose (Classical.choose_spec ex).left
      let j_spec := Classical.choose_spec (Classical.choose_spec ex).left
      cases Nat.le_total i j with
      | inl i_le_j =>
        have j_is_i_plus_k := Nat.le.dest i_le_j
        cases j_is_i_plus_k with | intro k hk =>
          simp [j] at hk
          rw [← hk]
          apply Eq.symm
          simp only [inductive_homomorphism_shortcut]
          have same_all_following := inductive_homomorphism_same_on_all_following_terms ct m m_is_model i
          simp only [ChaseTree.chase_branch_for_tree_branch, branch, nodes, path, inductive_homomorphism_shortcut] at eq
          rw [eq] at same_all_following; simp [Option.is_none_or] at same_all_following
          apply same_all_following
          exact f_in_node
          exact t_mem
      | inr j_le_i =>
        have i_is_j_plus_k := Nat.le.dest j_le_i
        cases i_is_j_plus_k with | intro k hk =>
          rw [← hk]
          simp only [inductive_homomorphism_shortcut]
          have same_all_following := inductive_homomorphism_same_on_all_following_terms ct m m_is_model j
          cases eq2 : branch.branch.infinite_list j with
          | none => rw [eq2] at j_spec; simp [Option.is_some_and] at j_spec
          | some _ =>
            rw [eq2] at j_spec; simp [Option.is_some_and] at j_spec
            simp only [ChaseTree.chase_branch_for_tree_branch, branch, nodes, path, inductive_homomorphism_shortcut] at eq2
            rw [eq2] at same_all_following; simp [Option.is_none_or] at same_all_following
            apply same_all_following
            exact j_spec
            exact (Classical.choose_spec ex).right

  exists result
  exists global_h
  constructor
  . exists branch
  . constructor
    . intro gt
      split
      case h_1 _ c =>
        simp only [global_h]
        split
        case h_1 _ p _ =>
          let hfl := (Classical.choose_spec p).left
          let i := Classical.choose hfl
          let i_spec := Classical.choose_spec hfl
          have property := (inductive_homomorphism_shortcut i).property.right
          simp only [ChaseTree.chase_branch_for_tree_branch, branch, nodes, path] at i_spec
          cases eq : ct.tree.get (inductive_homomorphism_shortcut i).val.fst with
          | none => rw [eq] at i_spec; simp [Option.is_some_and] at i_spec
          | some node =>
            rw [eq] at property; simp [Option.is_none_or] at property
            exact GroundTermMapping.apply_constant_is_id_of_isIdOnConstants property.left c
        . trivial
      . trivial
    . intro f hf
      simp only [result] at hf
      unfold ChaseBranch.result at hf
      unfold GroundTermMapping.applyFactSet at hf
      cases hf with | intro e he =>
        let ⟨hel, her⟩ := he
        cases hel with | intro n hn =>
          simp only [ChaseTree.chase_branch_for_tree_branch, branch, nodes] at hn
          rw [her]
          specialize this n
          simp only [ChaseTree.chase_branch_for_tree_branch, branch, nodes] at this
          cases eq : path n with
          | none => rw [eq] at hn; simp [Option.is_some_and] at hn
          | some node =>
            rw [eq] at hn; simp [Option.is_some_and] at hn
            rw [eq] at this; simp [Option.is_none_or] at this
            specialize this e hn
            unfold GroundTermMapping.applyFact at this
            rw [this]
            have property := (inductive_homomorphism_shortcut n).property.right
            simp only [path] at eq
            rw [eq] at property; simp [Option.is_none_or] at property
            have : (inductive_homomorphism_shortcut n).val.snd.applyFactSet node.facts ⊆ m := property.right
            apply this
            exists e

