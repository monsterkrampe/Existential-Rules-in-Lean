import ExistentialRules.AlternativeMatches.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

abbrev InductiveHomomorphismExtensionResult {obs : ObsoletenessCondition sig} {rules : RuleSet sig} (cd : ChaseDerivation obs rules) (h : GroundTermMapping sig) :=
  { pair : (ChaseDerivation obs rules) × (GroundTermMapping sig) // pair.fst <:+ cd ∧ (∀ t ∈ cd.head.facts.terms, pair.snd t = h t) ∧ pair.snd.isHomomorphism pair.fst.head.facts cd.result }

namespace ChaseBranch

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  noncomputable def extend_hom_to_next_step_of_next_eq_some
      (cb : ChaseBranch obs kb) (det : kb.rules.isDeterministic)
      (cd : ChaseDerivation obs kb.rules) (suffix : cd <:+ cb.toChaseDerivation)
      (h : GroundTermMapping sig) (hom : h.isHomomorphism cd.head.facts cd.result)
      (next : ChaseNode obs kb.rules) (next_eq : cd.next = some next) :
      InductiveHomomorphismExtensionResult cd h :=
    let origin := next.origin.get (cd.isSome_origin_next next_eq)
    have origin_trg_active := cd.active_trigger_origin_next next_eq
    let disj : Fin origin.fst.val.rule.head.length := ⟨origin.snd.val, by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt⟩
    let trg' : PreTrigger sig := ⟨origin.fst.val.rule, h ∘ origin.fst.val.subs⟩
    have trg'_loaded : trg'.loaded cd.result := by
      apply Set.subset_trans _ hom.right
      apply PreTrigger.term_mapping_preserves_loadedness
      . exact hom.left
      . exact origin_trg_active.left
    have trg'_satisfied : trg'.satisfied_for_disj cd.result ⟨disj.val, disj.isLt⟩ := by
      have modelsRule : cd.result.modelsRule trg'.rule := by
        exact cd.result_models_rules trg'.rule origin.fst.property
      specialize modelsRule trg'.subs trg'_loaded
      rcases modelsRule with ⟨i, s', s'_frontier, s'_contains⟩
      exists s'
      constructor
      . exact s'_frontier
      . -- kb.isDeterministic is required here
        have : i.val = disj.val := by
          have isLt := i.isLt
          have := det trg'.rule origin.fst.property
          unfold Rule.isDeterministic at this
          rw [decide_eq_true_iff] at this
          simp only [this, Nat.lt_one_iff] at isLt
          have isLt' := disj.isLt
          have := det origin.fst.val.rule origin.fst.property
          unfold Rule.isDeterministic at this
          rw [decide_eq_true_iff] at this
          simp only [this, Nat.lt_one_iff] at isLt'
          rw [isLt, isLt']
        simp only [List.get_eq_getElem, this] at s'_contains
        exact s'_contains

    let subs := Classical.choose trg'_satisfied
    have ⟨subs_frontier, subs_contained⟩ := Classical.choose_spec trg'_satisfied

    let h' : GroundTermMapping sig := fun t =>
      if t_mem : t ∈ origin.fst.val.fresh_terms_for_head_disjunct disj.val disj.isLt then
        subs (origin.fst.val.existential_var_for_fresh_term disj.val disj.isLt t t_mem)
      else
        h t

    have h'_is_id_on_const : h'.isIdOnConstants := by
      intro c
      have : ¬ .const c ∈ origin.fst.val.fresh_terms_for_head_disjunct disj.val disj.isLt := by
        apply PreTrigger.constant_not_mem_fresh_terms_for_head_disjunct
      simp only [h', this, ↓reduceDIte]
      exact hom.left

    have h'_is_subs_on_head_vars : ∀ v, v ∈ (origin.fst.val.rule.head[disj.val]).vars -> (h' (origin.fst.val.subs_for_mapped_head origin.snd v)) = subs v := by
      intro v v_mem
      simp only [PreTrigger.subs_for_mapped_head]
      cases Decidable.em (v ∈ origin.fst.val.rule.frontier) with
      | inl v_frontier =>
        rw [origin.fst.val.apply_to_var_or_const_frontier_var _ _ v_frontier]
        have : ¬ origin.fst.val.subs v ∈ origin.fst.val.fresh_terms_for_head_disjunct disj.val disj.isLt := by
          apply PreTrigger.frontier_term_not_mem_fresh_terms_for_head_disjunct
          apply List.mem_map_of_mem
          exact v_frontier
        simp only [h', this, ↓reduceDIte]
        simp only [subs, subs_frontier _ v_frontier]
        rfl
      | inr v_frontier =>
        rw [origin.fst.val.apply_to_var_or_const_non_frontier_var _ _ v_frontier]
        have v_exis : v ∈ origin.fst.val.rule.existential_vars_for_head_disjunct disj.val disj.isLt := by
          simp only [Rule.existential_vars_for_head_disjunct, List.mem_filter, decide_eq_true_iff]
          exact ⟨v_mem, v_frontier⟩
        have : origin.fst.val.functional_term_for_var origin.snd.val v ∈ origin.fst.val.fresh_terms_for_head_disjunct disj.val disj.isLt := by
          apply List.mem_map_of_mem; exact v_exis
        simp only [h', this, ↓reduceDIte]
        rw [PreTrigger.existential_var_for_fresh_term_after_functional_term_for_var]
        exact v_exis

    have h'_is_h_on_terms_in_node : ∀ t ∈ cd.head.facts.terms, h' t = h t := by
      intro t t_mem
      have : ¬ t ∈ origin.fst.val.fresh_terms_for_head_disjunct disj.val disj.isLt := by
        intro contra
        apply origin_trg_active.right
        apply obs.contains_trg_result_implies_cond origin.snd
        apply cb.result_of_trigger_introducing_functional_term_occurs_in_chase ⟨cd.head, by apply ChaseDerivation.mem_of_mem_suffix suffix; exact cd.head_mem⟩ t_mem
        exact contra
      simp [h', this]

    ⟨(cd.tail (by simp [next_eq]), h'), by
      constructor
      . exact PossiblyInfiniteList.IsSuffix_tail
      constructor
      . exact h'_is_h_on_terms_in_node
      . simp only [cd.head_tail', next_eq, Option.get_some]
        constructor
        . exact h'_is_id_on_const
        . rw [cd.facts_next next_eq]
          rintro f' ⟨f, f_mem, f'_eq⟩
          rw [f'_eq]
          cases f_mem with
          | inl f_mem => apply hom.right; exists f; constructor; exact f_mem; apply TermMapping.apply_generalized_atom_congr_left; intro t t_mem; apply h'_is_h_on_terms_in_node; exists f
          | inr f_mem =>
            apply subs_contained
            have : (subs.apply_function_free_conj trg'.rule.head[disj.val]).toSet = h'.applyFactSet origin.fst.val.mapped_head[disj.val].toSet := by
              simp only [TermMapping.apply_generalized_atom_set_toSet]
              apply congrArg
              rw [← PreTrigger.apply_subs_for_mapped_head_eq, ← GroundSubstitution.apply_function_free_conj_compose]
              . apply List.map_congr_left
                intro a a_mem
                apply TermMapping.apply_generalized_atom_congr_left
                intro voc voc_mem
                cases voc with
                | const d => simp [GroundSubstitution.apply_var_or_const]
                | var v =>
                  simp only [GroundSubstitution.apply_var_or_const, Function.comp_apply]
                  rw [h'_is_subs_on_head_vars]
                  rw [FunctionFreeConjunction.mem_vars]
                  exists a
              . intros; exact h'_is_id_on_const
            rw [this]
            apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
            exact f_mem
    ⟩

  theorem node_is_next_in_extend_hom_to_next_step_next_eq_some
      {cb : ChaseBranch obs kb} {det : kb.rules.isDeterministic}
      {cd : ChaseDerivation obs kb.rules} {suffix : cd <:+ cb.toChaseDerivation}
      {h : GroundTermMapping sig} {hom : h.isHomomorphism cd.head.facts cd.result}
      {next : ChaseNode obs kb.rules} {next_eq : cd.next = some next} :
      (extend_hom_to_next_step_of_next_eq_some cb det cd suffix h hom next next_eq).val.fst = cd.tail (by simp [next_eq]) := by
    simp only [extend_hom_to_next_step_of_next_eq_some]
    split
    rfl

  theorem hom_extends_prev_in_extend_hom_to_next_step_of_next_eq_some
      {cb : ChaseBranch obs kb} {det : kb.rules.isDeterministic}
      {cd : ChaseDerivation obs kb.rules} {suffix : cd <:+ cb.toChaseDerivation}
      {h : GroundTermMapping sig} {hom : h.isHomomorphism cd.head.facts cd.result}
      {next : ChaseNode obs kb.rules} {next_eq : cd.next = some next} :
      ∀ t ∈ cd.head.facts.terms, (extend_hom_to_next_step_of_next_eq_some cb det cd suffix h hom next next_eq).val.snd t = h t := by
    exact (extend_hom_to_next_step_of_next_eq_some cb det cd suffix h hom next next_eq).property.right.left

  noncomputable def extend_hom_to_next_step
      (cb : ChaseBranch obs kb) (det : kb.rules.isDeterministic)
      (cd : ChaseDerivation obs kb.rules) (suffix : cd <:+ cb.toChaseDerivation)
      (h : GroundTermMapping sig)
      (prev_res : InductiveHomomorphismExtensionResult cd h) :
      Option (InductiveHomomorphismExtensionResult cd h) :=
    prev_res.val.fst.next.attach.map (fun next =>
      let step := extend_hom_to_next_step_of_next_eq_some cb det prev_res.val.fst (PossiblyInfiniteList.IsSuffix_trans prev_res.property.left suffix) prev_res.val.snd (by rw [ChaseDerivation.result_suffix prev_res.property.left]; exact prev_res.property.right.right) next.val next.property
      ⟨step.val, by
        constructor
        . exact PossiblyInfiniteList.IsSuffix_trans step.property.left prev_res.property.left
        constructor
        . intro t t_mem
          rw [← prev_res.property.right.left _ t_mem]
          apply step.property.right.left
          apply FactSet.terms_subset_of_subset
          . apply cd.facts_node_subset_every_mem; apply ChaseDerivation.mem_of_mem_suffix prev_res.property.left; apply ChaseDerivation.head_mem
          . exact t_mem
        . simp only [← ChaseDerivation.result_suffix prev_res.property.left]; exact step.property.right.right⟩
    )

  theorem node_is_next_in_extend_hom_to_next_step
      {cb : ChaseBranch obs kb} {det : kb.rules.isDeterministic}
      {cd : ChaseDerivation obs kb.rules} {suffix : cd <:+ cb.toChaseDerivation}
      {h : GroundTermMapping sig}
      {prev_res : InductiveHomomorphismExtensionResult cd h} :
      ∀ {pair}, (pair_mem : pair ∈ extend_hom_to_next_step cb det cd suffix h prev_res) -> pair.val.fst = prev_res.val.fst.tail (by
        simp only [extend_hom_to_next_step, Option.mem_def, Option.map_attach_eq_pmap, Option.pmap_eq_some_iff] at pair_mem
        rcases pair_mem with ⟨_, pair_mem, _⟩
        simp [pair_mem]) := by
    intro pair pair_mem
    simp only [extend_hom_to_next_step, Option.mem_def, Option.map_attach_eq_pmap, Option.pmap_eq_some_iff] at pair_mem
    rcases pair_mem with ⟨next, next_eq, _, pair_eq⟩
    simp only [pair_eq]
    rw [node_is_next_in_extend_hom_to_next_step_next_eq_some]

  theorem hom_extends_prev_in_extend_hom_to_next_step
      {cb : ChaseBranch obs kb} {det : kb.rules.isDeterministic}
      {cd : ChaseDerivation obs kb.rules} {suffix : cd <:+ cb.toChaseDerivation}
      {h : GroundTermMapping sig}
      {prev_res : InductiveHomomorphismExtensionResult cd h} :
      ∀ t ∈ prev_res.val.fst.head.facts.terms, ∀ pair ∈ extend_hom_to_next_step cb det cd suffix h prev_res, pair.val.snd t = prev_res.val.snd t := by
    intro t t_mem pair pair_mem
    simp only [extend_hom_to_next_step, Option.mem_def, Option.map_attach_eq_pmap, Option.pmap_eq_some_iff] at pair_mem
    rcases pair_mem with ⟨next, next_eq, _, pair_eq⟩
    rw [pair_eq]
    rw [hom_extends_prev_in_extend_hom_to_next_step_of_next_eq_some]
    exact t_mem

  theorem hom_for_node_extendable_to_result
      {cb : ChaseBranch obs kb} (det : kb.rules.isDeterministic)
      {node : ChaseNode obs kb.rules} (node_mem : node ∈ cb.toChaseDerivation)
      {h : GroundTermMapping sig} (hom : h.isHomomorphism node.facts cb.result) :
      ∃ (h' : GroundTermMapping sig), (∀ t ∈ node.facts.terms, h' t = h t) ∧ h'.isHomomorphism cb.result cb.result := by
    rcases cb.subderivation_of_node_mem node_mem with ⟨deriv_for_node, deriv_for_node_head, deriv_suffix⟩
    let start : Option (InductiveHomomorphismExtensionResult deriv_for_node h) := some ⟨(deriv_for_node, h), by
      constructor
      . exact PossiblyInfiniteList.IsSuffix_refl
      constructor
      . intros; rfl
      . simp only [deriv_for_node_head, ChaseDerivation.result_suffix deriv_suffix]; exact hom
    ⟩
    let pairs := PossiblyInfiniteList.generate start (extend_hom_to_next_step cb det deriv_for_node deriv_suffix h) id

    have pairs_get?_succ : ∀ i, pairs.get? i.succ = (pairs.get? i).bind (extend_hom_to_next_step cb det deriv_for_node deriv_suffix h) := by
      intro i; simp only [pairs, PossiblyInfiniteList.get?_generate, Option.map_id, id_eq]; rfl

    have derivs_suffix_of_each_other : ∀ (i k : Nat), ∀ pair ∈ pairs.get? i, ∀ pair2 ∈ pairs.get? (i+k), pair2.val.fst <:+ pair.val.fst := by
      intro i k pair pair_mem pair2 pair2_mem
      induction k generalizing pair2 with
      | zero => rw [Nat.add_zero, pair_mem, Option.mem_def, Option.some_inj] at pair2_mem; rw [pair2_mem]; exact PossiblyInfiniteList.IsSuffix_refl
      | succ k ih =>
        rw [← Nat.add_assoc, pairs_get?_succ] at pair2_mem
        rw [Option.mem_def, Option.bind_eq_some_iff] at pair2_mem
        rcases pair2_mem with ⟨prev_pair, prev_pair_mem, pair2_mem⟩
        apply PossiblyInfiniteList.IsSuffix_trans _ (ih prev_pair prev_pair_mem)
        rw [node_is_next_in_extend_hom_to_next_step pair2_mem]
        exact PossiblyInfiniteList.IsSuffix_tail

    have homs_extend_each_other : ∀ (i k : Nat), ∀ pair ∈ pairs.get? i, ∀ pair2 ∈ pairs.get? (i+k), ∀ t ∈ pair.val.fst.head.facts.terms, pair.val.snd t = pair2.val.snd t := by
      intro i k pair pair_mem pair2 pair2_mem t t_mem
      induction k generalizing pair2 with
      | zero => rw [Nat.add_zero, pair_mem, Option.mem_def, Option.some_inj] at pair2_mem; rw [pair2_mem]
      | succ k ih =>
        rw [← Nat.add_assoc, pairs_get?_succ] at pair2_mem
        rw [Option.mem_def, Option.bind_eq_some_iff] at pair2_mem
        rcases pair2_mem with ⟨prev_pair, prev_pair_mem, pair2_mem⟩
        rw [ih prev_pair prev_pair_mem]
        apply Eq.symm; apply hom_extends_prev_in_extend_hom_to_next_step
        . apply FactSet.terms_subset_of_subset (pair.val.fst.facts_node_subset_every_mem prev_pair.val.fst.head (by
            apply ChaseDerivation.mem_of_mem_suffix (derivs_suffix_of_each_other i k pair pair_mem prev_pair prev_pair_mem); exact ChaseDerivation.head_mem))
          exact t_mem
        . exact pair2_mem

    have each_node_in_some_pair : ∀ node ∈ deriv_for_node, ∃ pair ∈ pairs, node = pair.val.fst.head := by
      intro node node_mem
      let node : deriv_for_node.Node := ⟨node, node_mem⟩
      show ∃ pair ∈ pairs, node.val = pair.val.fst.head
      induction node using ChaseDerivation.mem_rec with
      | head => exists start.get (by simp [start]); constructor; apply PossiblyInfiniteList.head_mem; simp [pairs, PossiblyInfiniteList.head_generate]; simp [start]
      | step cd2 suffix ih next next_mem =>
        rcases ih with ⟨pair, ⟨i, pair_mem⟩, head_eq⟩
        rw [← PossiblyInfiniteList.get?.eq_def] at pair_mem
        have : cd2 = pair.val.fst := by
          apply ChaseDerivation.eq_of_suffix_of_head_mem
          . apply ChaseDerivation.suffix_of_suffix_of_suffix_of_head_mem
            . apply derivs_suffix_of_each_other 0 i (start.get (by simp [start])) (by rw [← PossiblyInfiniteList.head_eq]; simp [pairs, PossiblyInfiniteList.head_generate])
              rw [Nat.zero_add, pair_mem]
              simp
            . exact suffix
            . simp only at head_eq; rw [head_eq]; exact ChaseDerivation.head_mem
          . rw [← head_eq]; exact ChaseDerivation.head_mem
        exists (pairs.get? i.succ).get (by
          rw [pairs_get?_succ, pair_mem, Option.bind_some]
          simp only [extend_hom_to_next_step, Option.isSome_map, Option.isSome_attach]
          rw [← this, next_mem]; simp)
        constructor
        . exists i.succ; simp [PossiblyInfiniteList.get?]
        . simp only [pairs_get?_succ, pair_mem, Option.bind_some]
          rw [node_is_next_in_extend_hom_to_next_step (prev_res := pair)]
          . rw [Option.mem_def] at next_mem; rw [ChaseDerivation.head_tail']; simp [← this, next_mem]
          . apply Option.get_mem
          . exact det
          . exact deriv_suffix

    have each_result_terms_occurs_in_some_pair : ∀ t ∈ deriv_for_node.result.terms, ∃ pair ∈ pairs, t ∈ pair.val.fst.head.facts.terms := by
      intro t t_mem
      rcases t_mem with ⟨f, ⟨node, node_mem, f_mem⟩, t_mem⟩
      rcases each_node_in_some_pair node node_mem with ⟨pair, pair_mem, node_eq⟩
      exists pair; simp only [pair_mem, true_and]
      rw [← node_eq]; exists f

    let global_h : GroundTermMapping sig := fun t =>
      let t_mem := t ∈ deriv_for_node.result.terms
      have t_mem_dec := Classical.propDecidable t_mem
      if t_mem_true : t_mem then
        have pair_mem := each_result_terms_occurs_in_some_pair _ t_mem_true
        let pair := Classical.choose pair_mem
        pair.val.snd t
      else
        t

    have global_agrees_with_h : (∀ t ∈ node.facts.terms, global_h t = h t) := by
      intro t t_mem
      rw [← deriv_for_node_head] at t_mem
      have : t ∈ deriv_for_node.result.terms := by apply FactSet.terms_subset_of_subset (deriv_for_node.facts_node_subset_result _ ChaseDerivation.head_mem); exact t_mem
      simp only [global_h, this, ↓reduceDIte]
      let pair := Classical.choose (each_result_terms_occurs_in_some_pair _ this)
      apply pair.property.right.left
      exact t_mem

    have global_id_const : global_h.isIdOnConstants := by
      intro c
      simp only [global_h]
      split
      case isFalse _ => rfl
      case isTrue t_mem_true =>
        let pair := Classical.choose (each_result_terms_occurs_in_some_pair _ t_mem_true)
        exact pair.property.right.right.left

    have global_h_eq_each_hom : ∀ pair ∈ pairs, ∀ f ∈ pair.val.fst.head.facts, global_h.applyFact f = pair.val.snd.applyFact f := by
      intro pair pair_mem f f_mem
      apply TermMapping.apply_generalized_atom_congr_left
      intro t t_mem
      simp only [global_h]
      split
      case a.isFalse not_mem =>
        apply False.elim
        apply not_mem
        exists f; simp only [t_mem, and_true]
        apply deriv_for_node.facts_node_subset_result pair.val.fst.head
        . apply ChaseDerivation.mem_of_mem_suffix pair.property.left; exact ChaseDerivation.head_mem
        . exact f_mem
      case a.isTrue t_mem_true =>
        have spec := Classical.choose_spec (each_result_terms_occurs_in_some_pair _ t_mem_true)
        rcases spec.left with ⟨i, spec_l⟩
        rcases pair_mem with ⟨j, pair_mem⟩
        rw [Option.eq_some_iff_get_eq] at spec_l
        rcases spec_l with ⟨_, spec_l⟩
        rw [← spec_l]
        rw [Option.eq_some_iff_get_eq] at pair_mem
        rcases pair_mem with ⟨_, pair_mem⟩
        rw [← pair_mem]
        cases Nat.le_total i j with
        | inl i_le_j =>
          rcases Nat.le.dest i_le_j with ⟨k, i_le_j⟩
          conv => right; fun; right; right; left; rw [← i_le_j]
          apply homs_extend_each_other i k
          . simp [PossiblyInfiniteList.get?]
          . simp [PossiblyInfiniteList.get?]
          . rw [spec_l]; exact spec.right
        | inr j_le_i =>
          rcases Nat.le.dest j_le_i with ⟨k, j_le_i⟩
          conv => left; fun; right; right; left; rw [← j_le_i]
          apply Eq.symm
          apply homs_extend_each_other j k
          . simp [PossiblyInfiniteList.get?]
          . simp [PossiblyInfiniteList.get?]
          . rw [pair_mem]; exists f

    have global_h_hom : ∀ node ∈ deriv_for_node, global_h.applyFactSet node.facts ⊆ deriv_for_node.result := by
      intro node node_mem
      rcases each_node_in_some_pair node node_mem with ⟨pair, pair_mem, node_eq⟩
      rintro f' ⟨f, f_mem, f'_eq⟩
      rw [node_eq] at f_mem
      rw [f'_eq, ← GroundTermMapping.applyFact.eq_def, global_h_eq_each_hom pair pair_mem f f_mem]
      apply pair.property.right.right.right; apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set; exact f_mem

    exists global_h
    constructor
    . exact global_agrees_with_h
    constructor
    . exact global_id_const
    . rw [← ChaseDerivation.result_suffix deriv_suffix]
      rintro f' ⟨f, ⟨node, node_mem, f_mem⟩, f'_eq⟩
      rw [f'_eq]
      apply global_h_hom node node_mem
      apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
      exact f_mem

end ChaseBranch

