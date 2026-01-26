import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts.GroundTerm

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace PreTrigger

  def skolem_ruleIds_valid (rl : RuleList sig) (trg : PreTrigger sig) : Prop := ∀ t ∈ trg.mapped_body.flatMap GeneralizedAtom.terms, t.skolem_ruleIds_valid rl
  def skolem_disjIdx_valid (rl : RuleList sig) (trg : PreTrigger sig) (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl) : Prop :=
    ∀ t, (h : t ∈ trg.mapped_body.flatMap GeneralizedAtom.terms) -> t.skolem_disjIdx_valid rl (trg_ruleIds_valid t h)
  def skolem_rule_arity_valid (rl : RuleList sig) (trg : PreTrigger sig) (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl) : Prop :=
    ∀ t, (h : t ∈ trg.mapped_body.flatMap GeneralizedAtom.terms) -> t.skolem_rule_arity_valid rl (trg_ruleIds_valid t h)

  theorem skolem_ruleIds_valid_of_strong_equiv {rl : RuleList sig} {trg trg2 : PreTrigger sig} (strong_equiv : trg.strong_equiv trg2) (trg_valid : trg.skolem_ruleIds_valid rl) : trg2.skolem_ruleIds_valid rl := by
    unfold skolem_ruleIds_valid; rw [← PreTrigger.mapped_body_eq_of_strong_equiv strong_equiv]; exact trg_valid

  theorem skolem_disjIdx_valid_of_strong_equiv {rl : RuleList sig} {trg trg2 : PreTrigger sig} (strong_equiv : trg.strong_equiv trg2) (h : trg.skolem_ruleIds_valid rl) (trg_valid : trg.skolem_disjIdx_valid rl h) : trg2.skolem_disjIdx_valid rl (PreTrigger.skolem_ruleIds_valid_of_strong_equiv strong_equiv h) := by
    unfold skolem_disjIdx_valid; simp only [← PreTrigger.mapped_body_eq_of_strong_equiv strong_equiv]; exact trg_valid

  theorem skolem_rule_arity_valid_of_strong_equiv {rl : RuleList sig} {trg trg2 : PreTrigger sig} (strong_equiv : trg.strong_equiv trg2) (h : trg.skolem_ruleIds_valid rl) (trg_valid : trg.skolem_rule_arity_valid rl h) : trg2.skolem_rule_arity_valid rl (PreTrigger.skolem_ruleIds_valid_of_strong_equiv strong_equiv h) := by
    unfold skolem_rule_arity_valid; simp only [← PreTrigger.mapped_body_eq_of_strong_equiv strong_equiv]; exact trg_valid

  theorem skolem_ruleIds_valid_for_functional_term
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (rule_mem : trg.rule ∈ rl.rules)
      (body_valid : trg.skolem_ruleIds_valid rl) :
      ∀ i v, (trg.functional_term_for_var i v).skolem_ruleIds_valid rl := by
    intro i v
    simp only [GroundTerm.skolem_ruleIds_valid, PreGroundTerm.skolem_ruleIds_valid, PreTrigger.functional_term_for_var, GroundTerm.func]
    constructor
    . exists trg.rule
    . intro t t_mem
      rw [List.mem_unattach] at t_mem
      rcases t_mem with ⟨h, t_mem⟩
      rw [List.mem_map] at t_mem
      rcases t_mem with ⟨v, v_mem, t_eq⟩
      apply body_valid ⟨t, h⟩
      rw [PreTrigger.mem_terms_mapped_body_iff]
      apply Or.inr
      exists v; constructor
      . apply Rule.frontier_subset_vars_body; exact v_mem
      . exact t_eq

  theorem skolem_disjIdx_valid_for_functional_term
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (rule_mem : trg.rule ∈ rl.rules)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (body_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid) :
      ∀ i v, (i < trg.rule.head.length) -> (trg.functional_term_for_var i v).skolem_disjIdx_valid rl (trg.skolem_ruleIds_valid_for_functional_term rl rule_mem trg_ruleIds_valid i v) := by
    intro i v i_lt
    simp only [GroundTerm.skolem_disjIdx_valid, PreGroundTerm.skolem_disjIdx_valid, GroundTerm.func, functional_term_for_var]
    constructor
    . unfold SkolemFS.disjunctIndex_valid
      rw [rl.get_by_id_self _ rule_mem]
      exact i_lt
    . have func_ruleIds_valid := trg.skolem_ruleIds_valid_for_functional_term rl rule_mem trg_ruleIds_valid i v
      intro t t_mem
      rw [List.mem_unattach] at t_mem
      rcases t_mem with ⟨h, t_mem⟩
      rw [List.mem_map] at t_mem
      rcases t_mem with ⟨v, v_mem, t_eq⟩
      apply body_valid ⟨t, h⟩
      rw [PreTrigger.mem_terms_mapped_body_iff]
      apply Or.inr
      exists v; constructor
      . apply Rule.frontier_subset_vars_body; exact v_mem
      . exact t_eq

  theorem skolem_rule_arity_valid_for_functional_term
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (rule_mem : trg.rule ∈ rl.rules)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (body_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid) :
      ∀ i v, (trg.functional_term_for_var i v).skolem_rule_arity_valid rl (trg.skolem_ruleIds_valid_for_functional_term rl rule_mem trg_ruleIds_valid i v) := by
    intro i v
    simp only [GroundTerm.skolem_rule_arity_valid, PreGroundTerm.skolem_rule_arity_valid, GroundTerm.func, functional_term_for_var]
    constructor
    . unfold SkolemFS.arity_valid
      rw [rl.get_by_id_self _ rule_mem]
    . have func_ruleIds_valid := trg.skolem_ruleIds_valid_for_functional_term rl rule_mem trg_ruleIds_valid i v
      intro t t_mem
      rw [List.mem_unattach] at t_mem
      rcases t_mem with ⟨h, t_mem⟩
      rw [List.mem_map] at t_mem
      rcases t_mem with ⟨v, v_mem, t_eq⟩
      apply body_valid ⟨t, h⟩
      rw [PreTrigger.mem_terms_mapped_body_iff]
      apply Or.inr
      exists v; constructor
      . apply Rule.frontier_subset_vars_body; exact v_mem
      . exact t_eq

  theorem skolem_ruleIds_valid_for_fresh_term
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (rule_mem : trg.rule ∈ rl.rules)
      (body_valid : trg.skolem_ruleIds_valid rl) :
      ∀ i lt t, t ∈ trg.fresh_terms_for_head_disjunct i lt -> t.skolem_ruleIds_valid rl := by
    intro i lt t t_mem
    simp only [PreTrigger.fresh_terms_for_head_disjunct, List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
    rw [← t_mem]; apply skolem_ruleIds_valid_for_functional_term; exact rule_mem; exact body_valid

  theorem skolem_disjIdx_valid_for_fresh_term
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (rule_mem : trg.rule ∈ rl.rules)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (body_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid) :
      ∀ i lt t, (t_mem : t ∈ trg.fresh_terms_for_head_disjunct i lt) -> t.skolem_disjIdx_valid rl (skolem_ruleIds_valid_for_fresh_term rl trg rule_mem trg_ruleIds_valid i lt t t_mem) := by
    intro i lt t t_mem
    simp only [PreTrigger.fresh_terms_for_head_disjunct, List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
    simp only [← t_mem]; apply skolem_disjIdx_valid_for_functional_term; exact rule_mem; exact body_valid; exact lt

  theorem skolem_rule_arity_valid_for_fresh_term
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (rule_mem : trg.rule ∈ rl.rules)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (body_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid) :
      ∀ i lt t, (t_mem : t ∈ trg.fresh_terms_for_head_disjunct i lt) -> t.skolem_rule_arity_valid rl (skolem_ruleIds_valid_for_fresh_term rl trg rule_mem trg_ruleIds_valid i lt t t_mem) := by
    intro i lt t t_mem
    simp only [PreTrigger.fresh_terms_for_head_disjunct, List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
    simp only [← t_mem]; apply skolem_rule_arity_valid_for_functional_term; exact rule_mem; exact body_valid

  -- TODO: for the following we should be able to use skolem_ruleIds_valid_for_fresh_term and the like but this is currently tricky since we cannot simply use PreTrigger.mem_terms_mapped_head_iff because of the flatten call.
  theorem skolem_ruleIds_remain_valid_in_head (rl : RuleList sig) (trg : PreTrigger sig) (rule_mem : trg.rule ∈ rl.rules) (body_valid : trg.skolem_ruleIds_valid rl) :
      ∀ t ∈ trg.mapped_head.flatten.flatMap GeneralizedAtom.terms, t.skolem_ruleIds_valid rl := by
    intro t t_mem
    rw [List.mem_flatMap] at t_mem
    rcases t_mem with ⟨f, f_mem, t_mem⟩
    rw [List.mem_flatten] at f_mem
    rcases f_mem with ⟨l, l_mem, f_mem⟩
    let disj_idx : Fin trg.mapped_head.length := ⟨trg.mapped_head.idxOf l, by apply List.idxOf_lt_length_of_mem; exact l_mem⟩
    let voc : VarOrConst sig := trg.var_or_const_for_result_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem
    rw [← trg.apply_on_var_or_const_for_result_term_is_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem]
    cases eq : voc with
    | const c =>
      unfold voc at eq
      rw [eq, trg.apply_to_var_or_const_for_const disj_idx.val _]
      apply GroundTerm.skolem_ruleIds_valid_const
    | var v =>
      cases Decidable.em (v ∈ trg.rule.frontier) with
      | inl mem_frontier =>
        unfold voc at eq
        rw [eq, trg.apply_to_var_or_const_frontier_var disj_idx.val _ mem_frontier]
        apply body_valid
        rw [PreTrigger.mem_terms_mapped_body_iff]
        apply Or.inr
        exists v; constructor
        . apply Rule.frontier_subset_vars_body; exact mem_frontier
        . rfl
      | inr mem_frontier =>
        unfold voc at eq
        rw [eq, trg.apply_to_var_or_const_non_frontier_var disj_idx.val _ mem_frontier]
        apply skolem_ruleIds_valid_for_functional_term
        . exact rule_mem
        . exact body_valid

  theorem skolem_disjIdx_remains_valid_in_head
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (rule_mem : trg.rule ∈ rl.rules)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (body_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid) :
      ∀ t, (t_mem : t ∈ trg.mapped_head.flatten.flatMap GeneralizedAtom.terms) -> t.skolem_disjIdx_valid rl (trg.skolem_ruleIds_remain_valid_in_head rl rule_mem trg_ruleIds_valid t t_mem) := by
    intro t t_mem
    rw [List.mem_flatMap] at t_mem
    rcases t_mem with ⟨f, f_mem, t_mem⟩
    rw [List.mem_flatten] at f_mem
    rcases f_mem with ⟨l, l_mem, f_mem⟩
    let disj_idx : Fin trg.mapped_head.length := ⟨trg.mapped_head.idxOf l, by apply List.idxOf_lt_length_of_mem; exact l_mem⟩

    cases t with
    | const c => apply GroundTerm.skolem_disjIdx_valid_const
    | func fs ts arity_ok =>
      cases Decidable.em ((GroundTerm.func fs ts arity_ok) ∈ trg.rule.frontier.map trg.subs) with
      | inl t_mem_frontier =>
        rw [List.mem_map] at t_mem_frontier
        rcases t_mem_frontier with ⟨v, v_mem, v_eq⟩
        apply body_valid
        rw [PreTrigger.mem_terms_mapped_body_iff]
        apply Or.inr
        exists v; constructor
        . apply Rule.frontier_subset_vars_body; exact v_mem
        . exact v_eq
      | inr t_mem_frontier =>
        let voc : VarOrConst sig := trg.var_or_const_for_result_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem
        have voc_eq := trg.apply_on_var_or_const_for_result_term_is_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem
        cases eq : voc with
        | const c =>
          unfold voc at eq
          rw [eq, trg.apply_to_var_or_const_for_const disj_idx.val _] at voc_eq
          simp [GroundTerm.const, GroundTerm.func] at voc_eq
        | var v =>
          unfold voc at eq
          rw [eq] at voc_eq
          cases Decidable.em (v ∈ trg.rule.frontier) with
          | inl v_mem_frontier =>
            rw [trg.apply_to_var_or_const_frontier_var disj_idx.val _ v_mem_frontier] at voc_eq
            apply False.elim
            apply t_mem_frontier
            rw [List.mem_map]
            exists v
          | inr v_mem_frontier =>
            rw [trg.apply_to_var_or_const_non_frontier_var disj_idx.val _ v_mem_frontier] at voc_eq
            simp only [← voc_eq]
            apply skolem_disjIdx_valid_for_functional_term
            . exact rule_mem
            . exact body_valid
            . rw [← PreTrigger.length_mapped_head]; exact disj_idx.isLt

  theorem skolem_rule_arity_remains_valid_in_head
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (rule_mem : trg.rule ∈ rl.rules)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (body_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid) :
      ∀ t, (t_mem : t ∈ trg.mapped_head.flatten.flatMap GeneralizedAtom.terms) -> t.skolem_rule_arity_valid rl (trg.skolem_ruleIds_remain_valid_in_head rl rule_mem trg_ruleIds_valid t t_mem) := by
    intro t t_mem
    rw [List.mem_flatMap] at t_mem
    rcases t_mem with ⟨f, f_mem, t_mem⟩
    rw [List.mem_flatten] at f_mem
    rcases f_mem with ⟨l, l_mem, f_mem⟩
    let disj_idx : Fin trg.mapped_head.length := ⟨trg.mapped_head.idxOf l, by apply List.idxOf_lt_length_of_mem; exact l_mem⟩

    cases t with
    | const c => apply GroundTerm.skolem_rule_arity_valid_const
    | func fs ts arity_ok =>
      cases Decidable.em ((GroundTerm.func fs ts arity_ok) ∈ trg.rule.frontier.map trg.subs) with
      | inl t_mem_frontier =>
        rw [List.mem_map] at t_mem_frontier
        rcases t_mem_frontier with ⟨v, v_mem, v_eq⟩
        apply body_valid
        rw [PreTrigger.mem_terms_mapped_body_iff]
        apply Or.inr
        exists v; constructor
        . apply Rule.frontier_subset_vars_body; exact v_mem
        . exact v_eq
      | inr t_mem_frontier =>
        let voc : VarOrConst sig := trg.var_or_const_for_result_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem
        have voc_eq := trg.apply_on_var_or_const_for_result_term_is_term disj_idx (by rw [List.getElem_idxOf_of_mem l_mem]; exact f_mem) t_mem
        cases eq : voc with
        | const c =>
          unfold voc at eq
          rw [eq, trg.apply_to_var_or_const_for_const disj_idx.val _] at voc_eq
          simp [GroundTerm.const, GroundTerm.func] at voc_eq
        | var v =>
          unfold voc at eq
          rw [eq] at voc_eq
          cases Decidable.em (v ∈ trg.rule.frontier) with
          | inl v_mem_frontier =>
            rw [trg.apply_to_var_or_const_frontier_var disj_idx.val _ v_mem_frontier] at voc_eq
            apply False.elim
            apply t_mem_frontier
            rw [List.mem_map]
            exists v
          | inr v_mem_frontier =>
            rw [trg.apply_to_var_or_const_non_frontier_var disj_idx.val _ v_mem_frontier] at voc_eq
            simp only [← voc_eq]
            apply skolem_rule_arity_valid_for_functional_term
            . exact rule_mem
            . exact body_valid

  def backtrackTrigger_for_functional_term
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (trg_rule_mem : trg.rule ∈ rl.rules)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (trg_rule_arity_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid)
      (forbidden_constants : List sig.C)
      (i : Nat) (v : sig.V) :
      PreTrigger sig :=
    ((trg.functional_term_for_var i v).backtrackTrigger rl (by
      cases eq : trg.functional_term_for_var i v with
      | const _ => simp [functional_term_for_var, GroundTerm.func, GroundTerm.const] at eq
      | func func ts arity_ok => exists func, ts, arity_ok
    ) (by apply trg.skolem_ruleIds_valid_for_functional_term; exact trg_rule_mem; exact trg_ruleIds_valid) (by apply trg.skolem_rule_arity_valid_for_functional_term; exact trg_rule_mem; exact trg_rule_arity_valid) forbidden_constants)

  theorem backtrackTrigger_for_functional_term_equiv
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (trg_rule_mem : trg.rule ∈ rl.rules)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (trg_rule_arity_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid)
      (forbidden_constants : List sig.C) :
      ∀ i v, (trg.backtrackTrigger_for_functional_term rl trg_rule_mem trg_ruleIds_valid trg_rule_arity_valid forbidden_constants i v).equiv trg := by
    intro i v
    simp only [backtrackTrigger_for_functional_term, PreTrigger.functional_term_for_var, GroundTerm.backtrackTrigger, GroundTerm.func, PreGroundTerm.backtrackTrigger]
    simp only [PreTrigger.equiv]
    constructor
    . apply RuleList.get_by_id_self; exact trg_rule_mem
    . intro u u_mem
      simp only [u_mem, ↓reduceDIte]
      rw [Subtype.mk.injEq]
      rw [List.getElem_unattach, List.getElem_map]
      conv => left; right; right; left; rw [RuleList.get_by_id_self _ _ trg_rule_mem]
      rw [List.getElem_idxOf_of_mem]
      rw [RuleList.get_by_id_self _ _ trg_rule_mem] at u_mem
      exact u_mem

  def backtrackFacts
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (trg : PreTrigger sig)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (trg_disjIdx_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid)
      (trg_rule_arity_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid) : (List (Fact sig)) × (List sig.C) :=
    let forbidden_constants := trg.mapped_body.flatMap Fact.constants ++ rl.rules.flatMap Rule.constants
    let backtrack_result := GroundTerm.backtrackFacts_list rl (trg.mapped_body.flatMap GeneralizedAtom.terms) trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid forbidden_constants
    (trg.mapped_body ++ backtrack_result.fst, backtrack_result.snd)

  theorem backtrackFacts_eq_of_strong_equiv
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (trg trg2 : PreTrigger sig)
      (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
      (trg_disjIdx_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid)
      (trg_rule_arity_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid)
      (strong_equiv : trg.strong_equiv trg2) :
      trg.backtrackFacts rl trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid =
        trg2.backtrackFacts rl
          (PreTrigger.skolem_ruleIds_valid_of_strong_equiv strong_equiv trg_ruleIds_valid)
          (PreTrigger.skolem_disjIdx_valid_of_strong_equiv strong_equiv trg_ruleIds_valid trg_disjIdx_valid)
          (PreTrigger.skolem_rule_arity_valid_of_strong_equiv strong_equiv trg_ruleIds_valid trg_rule_arity_valid) := by
    unfold backtrackFacts
    simp only [PreTrigger.mapped_body_eq_of_strong_equiv strong_equiv]

end PreTrigger

