import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace PreGroundTerm

  def skolem_ruleIds_valid (rl : RuleList sig) : PreGroundTerm sig -> Prop
  | .leaf _ => True
  | .inner func ts => func.ruleId_valid rl ∧ ∀ t ∈ ts, PreGroundTerm.skolem_ruleIds_valid rl t

  def skolem_disjIdx_valid
      (rl : RuleList sig)
      (term : PreGroundTerm sig)
      (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term) : Prop :=
    match term with
    | .leaf _ => True
    | .inner func ts =>
      have : func.ruleId_valid rl ∧ ∀ t ∈ ts, PreGroundTerm.skolem_ruleIds_valid rl t := by unfold PreGroundTerm.skolem_ruleIds_valid at term_ruleIds_valid; exact term_ruleIds_valid
      func.disjunctIndex_valid rl this.left ∧ ∀ t, (t_mem : t ∈ ts) -> PreGroundTerm.skolem_disjIdx_valid rl t (this.right t t_mem)

  def skolem_rule_arity_valid
      (rl : RuleList sig)
      (term : PreGroundTerm sig)
      (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term) : Prop :=
    match term with
    | .leaf _ => True
    | .inner func ts =>
      have : func.ruleId_valid rl ∧ ∀ t ∈ ts, PreGroundTerm.skolem_ruleIds_valid rl t := by unfold PreGroundTerm.skolem_ruleIds_valid at term_ruleIds_valid; exact term_ruleIds_valid
      func.arity_valid rl this.left ∧ ∀ t, (t_mem : t ∈ ts) -> PreGroundTerm.skolem_rule_arity_valid rl t (this.right t t_mem)

  def backtrackTrigger
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (term : PreGroundTerm sig)
      (term_is_func : ∃ func ts, term = .inner func ts)
      (term_arity_ok : PreGroundTerm.arity_ok term)
      (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term)
      (term_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid rl term term_ruleIds_valid)
      (forbidden_constants : List sig.C) :
      PreTrigger sig :=
    match term with
    | .leaf c => by simp at term_is_func -- contradiction
    | .inner func ts =>
      let rule : Rule sig := rl.get_by_id func.ruleId (by unfold PreGroundTerm.skolem_ruleIds_valid at term_ruleIds_valid; exact term_ruleIds_valid.left)
      let fresh_consts_for_pure_body_vars := rule.fresh_consts_for_pure_body_vars forbidden_constants

      let subs : GroundSubstitution sig := fun x =>
        if mem : x ∈ rule.frontier
        then
          let idx := rule.frontier.idxOf x
          have : idx < ts.length := by
            unfold arity_ok at term_arity_ok
            unfold skolem_rule_arity_valid at term_rule_arity_valid
            have := LawfulBEq.eq_of_beq (Bool.and_eq_true_iff.mp term_arity_ok).left
            rw [this, term_rule_arity_valid.left]
            apply List.idxOf_lt_length_of_mem
            exact mem
          ⟨ts[idx], by
            unfold arity_ok at term_arity_ok
            have := (Bool.and_eq_true_iff.mp term_arity_ok).right
            rw [List.all_eq_true] at this
            apply this ⟨ts[idx], by apply List.getElem_mem⟩
            apply List.mem_attach
          ⟩
        else
          if mem : x ∈ rule.pure_body_vars
          then
            let idx := rule.pure_body_vars.idxOf x
            have : idx < fresh_consts_for_pure_body_vars.val.length := by
              rw [fresh_consts_for_pure_body_vars.property.left]
              apply List.idxOf_lt_length_of_mem
              exact mem
            GroundTerm.const fresh_consts_for_pure_body_vars.val[idx]
          else
            -- it should not matter what we return here so we also do NOT need to make sure that this does not collide with other constants
            GroundTerm.const default

      { rule, subs }

  -- This is not nicely possible without a mutual definition. The _list version is quite involved itself.
  mutual

    def backtrackFacts
        [GetFreshInhabitant sig.C]
        [Inhabited sig.C]
        (rl : RuleList sig)
        (term : PreGroundTerm sig)
        (term_arity_ok : PreGroundTerm.arity_ok term)
        (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term)
        (term_disjIdx_valid : PreGroundTerm.skolem_disjIdx_valid rl term term_ruleIds_valid)
        (term_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid rl term term_ruleIds_valid)
        (forbidden_constants : List sig.C) :
        -- we return the backtracked facts and all the constants that have been freshly introduced (as a basis for picking other fresh ones)
        (List (Fact sig)) × (List sig.C) :=
      match term with
      | .leaf c => ([], [])
      | .inner func ts =>
        have term_arity_ok' : ts.length == func.arity && ts.attach.all (fun ⟨t, _⟩ => arity_ok t) := by unfold arity_ok at term_arity_ok; exact term_arity_ok
        have term_ruleIds_valid' : func.ruleId_valid rl ∧ ∀ t ∈ ts, PreGroundTerm.skolem_ruleIds_valid rl t := by unfold skolem_ruleIds_valid at term_ruleIds_valid; exact term_ruleIds_valid
        have term_disjIdx_valid' : func.disjunctIndex_valid rl term_ruleIds_valid'.left ∧ ∀ t, (t_mem : t ∈ ts) -> PreGroundTerm.skolem_disjIdx_valid rl t (term_ruleIds_valid'.right t t_mem) := by unfold skolem_disjIdx_valid at term_disjIdx_valid; exact term_disjIdx_valid
        have term_rule_arity_valid' : func.arity_valid rl term_ruleIds_valid'.left ∧ ∀ t, (t_mem : t ∈ ts) -> PreGroundTerm.skolem_rule_arity_valid rl t (term_ruleIds_valid'.right t t_mem) := by unfold skolem_rule_arity_valid at term_rule_arity_valid; exact term_rule_arity_valid

        let trg : PreTrigger sig := backtrackTrigger rl (.inner func ts) (by exists func, ts) term_arity_ok term_ruleIds_valid term_rule_arity_valid forbidden_constants
        let disjIdx := func.disjunctIndex
        have : disjIdx < trg.mapped_head.length := by rw [PreTrigger.length_mapped_head]; unfold trg; unfold backtrackTrigger; exact term_disjIdx_valid'.left

        let fresh_consts_for_pure_body_vars := trg.rule.fresh_consts_for_pure_body_vars forbidden_constants

        let res_ts := backtrackFacts_list rl ts (by
          intro t t_mem
          have := (Bool.and_eq_true_iff.mp term_arity_ok').right
          rw [List.all_eq_true] at this
          apply this ⟨t, t_mem⟩
          apply List.mem_attach
        ) term_ruleIds_valid'.right term_disjIdx_valid'.right term_rule_arity_valid'.right (forbidden_constants ++ fresh_consts_for_pure_body_vars)

        ((trg.mapped_body ++ trg.mapped_head[disjIdx]) ++ res_ts.fst, fresh_consts_for_pure_body_vars.val ++ res_ts.snd)

    def backtrackFacts_list
        [GetFreshInhabitant sig.C]
        [Inhabited sig.C]
        (rl : RuleList sig)
        (terms : List (PreGroundTerm sig))
        (terms_arity_ok : ∀ t ∈ terms, PreGroundTerm.arity_ok t)
        (terms_ruleIds_valid : ∀ t ∈ terms, PreGroundTerm.skolem_ruleIds_valid rl t)
        (terms_disjIdx_valid : ∀ t, (t_mem : t ∈ terms) -> PreGroundTerm.skolem_disjIdx_valid rl t (terms_ruleIds_valid t t_mem))
        (terms_rule_arity_valid : ∀ t, (t_mem : t ∈ terms) -> PreGroundTerm.skolem_rule_arity_valid rl t (terms_ruleIds_valid t t_mem))
        (forbidden_constants : List sig.C) :
        (List (Fact sig)) × (List sig.C) :=
      match terms with
      | .nil => ([], [])
      | .cons hd tl =>
        let res_hd := backtrackFacts rl hd (terms_arity_ok hd (by simp)) (terms_ruleIds_valid hd (by simp)) (terms_disjIdx_valid hd (by simp)) (terms_rule_arity_valid hd (by simp)) forbidden_constants
        let res_tl := backtrackFacts_list rl tl (by intro t t_mem; apply terms_arity_ok; simp [t_mem]) (by intro t t_mem; apply terms_ruleIds_valid; simp [t_mem])  (by intro t t_mem; apply terms_disjIdx_valid; simp [t_mem]) (by intro t t_mem; apply terms_rule_arity_valid; simp [t_mem]) (forbidden_constants ++ res_hd.snd)
        (res_hd.fst ++ res_tl.fst, res_hd.snd ++ res_tl.snd)

  end

  theorem backtrackFacts_list_nil
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {rl : RuleList sig}
      {forbidden_constants : List sig.C} :
      backtrackFacts_list rl [] (by simp) (by simp) (by simp) (by simp) forbidden_constants = ([], []) := by simp [backtrackFacts_list]

  theorem backtrackFacts_list_cons
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {rl : RuleList sig}
      {term : PreGroundTerm sig}
      {terms : List (PreGroundTerm sig)}
      {terms_arity_ok : ∀ t ∈ (term :: terms), PreGroundTerm.arity_ok t}
      {terms_ruleIds_valid : ∀ t ∈ (term :: terms), PreGroundTerm.skolem_ruleIds_valid rl t}
      {terms_disjIdx_valid : ∀ t, (t_mem : t ∈ (term :: terms)) -> PreGroundTerm.skolem_disjIdx_valid rl t (terms_ruleIds_valid t t_mem)}
      {terms_rule_arity_valid : ∀ t, (t_mem : t ∈ (term :: terms)) -> PreGroundTerm.skolem_rule_arity_valid rl t (terms_ruleIds_valid t t_mem)}
      {forbidden_constants : List sig.C} :
      backtrackFacts_list rl (term :: terms) terms_arity_ok terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants =
        let res_t := backtrackFacts rl term (by apply terms_arity_ok; simp) (by apply terms_ruleIds_valid; simp) (by apply terms_disjIdx_valid; simp) (by apply terms_rule_arity_valid; simp) forbidden_constants
        let res_ts := backtrackFacts_list rl terms
          (by intro t t_mem; apply terms_arity_ok; simp [t_mem])
          (by intro t t_mem; apply terms_ruleIds_valid; simp [t_mem])
          (by intro t t_mem; apply terms_disjIdx_valid; simp [t_mem])
          (by intro t t_mem; apply terms_rule_arity_valid; simp [t_mem])
          (forbidden_constants ++ res_t.snd)
        (res_t.fst ++ res_ts.fst, res_t.snd ++ res_ts.snd) := by rfl

  -- It's good to have this as mutual since we need the result on lists anyway.
  mutual

    theorem backtrackFacts_fresh_constants_not_forbidden
        [GetFreshInhabitant sig.C]
        [Inhabited sig.C]
        {rl : RuleList sig}
        {term : PreGroundTerm sig}
        {term_arity_ok : PreGroundTerm.arity_ok term}
        {term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term}
        {term_disjIdx_valid : PreGroundTerm.skolem_disjIdx_valid rl term term_ruleIds_valid}
        {term_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid rl term term_ruleIds_valid}
        {forbidden_constants : List sig.C} :
        ∀ c ∈ (PreGroundTerm.backtrackFacts rl term term_arity_ok term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants).snd, c ∉ forbidden_constants := by
      intro c c_mem
      cases term with
      | leaf _ => simp [backtrackFacts] at c_mem
      | inner func ts =>
        simp only [backtrackFacts] at c_mem
        rw [List.mem_append] at c_mem
        cases c_mem with
        | inl c_mem =>
          let trg : PreTrigger sig := backtrackTrigger rl (.inner func ts) (by exists func, ts) term_arity_ok term_ruleIds_valid term_rule_arity_valid forbidden_constants
          let fresh_consts_for_pure_body_vars := trg.rule.fresh_consts_for_pure_body_vars forbidden_constants
          apply fresh_consts_for_pure_body_vars.property.right.right
          exact c_mem
        | inr c_mem => intro contra; apply backtrackFacts_list_fresh_constants_not_forbidden c c_mem; simp [contra]

    theorem backtrackFacts_list_fresh_constants_not_forbidden
        [GetFreshInhabitant sig.C]
        [Inhabited sig.C]
        {rl : RuleList sig}
        {terms : List (PreGroundTerm sig)}
        {terms_arity_ok : ∀ t ∈ terms, PreGroundTerm.arity_ok t}
        {terms_ruleIds_valid : ∀ t ∈ terms, PreGroundTerm.skolem_ruleIds_valid rl t}
        {terms_disjIdx_valid : ∀ t, (t_mem : t ∈ terms) -> PreGroundTerm.skolem_disjIdx_valid rl t (terms_ruleIds_valid t t_mem)}
        {terms_rule_arity_valid : ∀ t, (t_mem : t ∈ terms) -> PreGroundTerm.skolem_rule_arity_valid rl t (terms_ruleIds_valid t t_mem)}
        {forbidden_constants : List sig.C} :
        ∀ c ∈ (PreGroundTerm.backtrackFacts_list rl terms terms_arity_ok terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).snd, c ∉ forbidden_constants := by
      intro c c_mem
      cases terms with
      | nil => simp [backtrackFacts_list_nil] at c_mem
      | cons hd tl =>
        rw [backtrackFacts_list_cons] at c_mem
        rw [List.mem_append] at c_mem
        cases c_mem with
        | inl c_mem => exact backtrackFacts_fresh_constants_not_forbidden c c_mem
        | inr c_mem =>
          intro contra
          apply backtrackFacts_list_fresh_constants_not_forbidden c c_mem
          simp [contra]

  end

  mutual

    theorem backtrackFacts_constants_in_rules_or_term_or_fresh
        [GetFreshInhabitant sig.C]
        [Inhabited sig.C]
        {rl : RuleList sig}
        {term : PreGroundTerm sig}
        {term_arity_ok : PreGroundTerm.arity_ok term}
        {term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term}
        {term_disjIdx_valid : PreGroundTerm.skolem_disjIdx_valid rl term term_ruleIds_valid}
        {term_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid rl term term_ruleIds_valid}
        {forbidden_constants : List sig.C} :
        ∀ f ∈ (PreGroundTerm.backtrackFacts rl term term_arity_ok term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants).fst,
        ∀ c ∈ f.constants,
          c ∈ (rl.rules.flatMap Rule.constants) ∨ c ∈ term.leaves ∨ c ∈ (PreGroundTerm.backtrackFacts rl term term_arity_ok term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants).snd := by
      intro f f_mem c c_mem
      cases term with
      | leaf _ => simp [backtrackFacts] at f_mem
      | inner func ts =>
        simp only [backtrackFacts] at f_mem
        rw [List.mem_append] at f_mem
        cases f_mem with
        | inl f_mem =>
          let trg := backtrackTrigger rl (.inner func ts) (by exists func, ts) term_arity_ok term_ruleIds_valid term_rule_arity_valid forbidden_constants
          rw [List.mem_append] at f_mem
          cases f_mem with
          | inl f_mem =>
            unfold Fact.constants at c_mem
            rw [List.mem_flatMap] at c_mem
            rcases c_mem with ⟨t, t_mem, c_mem⟩
            have t_mem : t ∈ trg.mapped_body.flatMap GeneralizedAtom.terms := by rw [List.mem_flatMap]; exists f
            rw [PreTrigger.mem_terms_mapped_body_iff] at t_mem
            cases t_mem with
            | inl t_mem =>
              rcases t_mem with ⟨d, d_mem, t_eq⟩
              apply Or.inl
              rw [List.mem_flatMap]
              exists trg.rule
              constructor
              . simp only [trg, backtrackTrigger]
                apply RuleList.get_by_id_mem
              . unfold Rule.constants
                rw [List.mem_append]
                apply Or.inl
                rw [← t_eq, GroundTerm.constants_const, List.mem_singleton] at c_mem
                rw [c_mem]
                exact d_mem
            | inr t_mem =>
              rcases t_mem with ⟨v, v_mem, t_eq⟩
              simp only [trg, backtrackTrigger] at t_eq
              cases Decidable.em (v ∈ trg.rule.frontier) with
              | inl v_mem_frontier =>
                apply Or.inr
                apply Or.inl
                simp only [trg, backtrackTrigger] at v_mem_frontier
                simp only [v_mem_frontier, ↓reduceDIte] at t_eq
                rw [← t_eq] at c_mem
                simp only [GroundTerm.constants] at c_mem
                simp only [FiniteTree.leaves]
                rw [List.mem_flatMap]
                exists t.val
                rw [← t_eq]
                constructor
                . apply List.getElem_mem
                . exact c_mem
              | inr v_not_mem_frontier =>
                have v_mem_pure_body_vars : v ∈ trg.rule.pure_body_vars := by
                  simp only [Rule.pure_body_vars, List.mem_filter]
                  constructor
                  . exact v_mem
                  . apply decide_eq_true; exact v_not_mem_frontier
                apply Or.inr
                apply Or.inr
                simp only [trg, backtrackTrigger] at v_not_mem_frontier
                simp only [v_not_mem_frontier, ↓reduceDIte] at t_eq
                simp only [trg, backtrackTrigger] at v_mem_pure_body_vars
                simp only [v_mem_pure_body_vars, ↓reduceDIte] at t_eq
                rw [← t_eq] at c_mem
                rw [GroundTerm.constants_const, List.mem_singleton] at c_mem
                simp only [backtrackFacts]
                rw [List.mem_append]
                apply Or.inl
                rw [c_mem]
                apply List.getElem_mem
          | inr f_mem =>
            have disjIdx_lt : func.disjunctIndex < trg.mapped_head.length := by rw [PreTrigger.length_mapped_head]; unfold skolem_disjIdx_valid at term_disjIdx_valid; apply term_disjIdx_valid.left
            have c_mem : c ∈ FactSet.constants trg.mapped_head[func.disjunctIndex].toSet := by exists f
            have c_mem := trg.mapped_head_constants_subset ⟨func.disjunctIndex, disjIdx_lt⟩ c c_mem
            rw [List.mem_toSet, List.mem_append] at c_mem
            cases c_mem with
            | inl c_mem =>
              apply Or.inr
              apply Or.inl
              rw [List.mem_flatMap] at c_mem
              rcases c_mem with ⟨t, t_mem, c_mem⟩
              rw [List.mem_map] at t_mem
              rcases t_mem with ⟨v, v_mem, t_eq⟩
              unfold PreTrigger.subs_for_mapped_head at t_eq
              rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ v v_mem] at t_eq
              simp only [trg, backtrackTrigger] at v_mem
              simp only [trg, backtrackTrigger, v_mem, ↓reduceDIte] at t_eq
              rw [← t_eq] at c_mem
              simp only [GroundTerm.constants] at c_mem
              simp only [FiniteTree.leaves]
              rw [List.mem_flatMap]
              exists t.val
              rw [← t_eq]
              constructor
              . apply List.getElem_mem
              . exact c_mem
            | inr c_mem =>
              apply Or.inl
              rw [List.mem_flatMap]
              exists trg.rule
              constructor
              . simp only [trg, backtrackTrigger]
                apply RuleList.get_by_id_mem
              . unfold Rule.constants
                rw [List.mem_append]
                apply Or.inr
                rw [List.mem_flatMap]
                exists trg.rule.head[func.disjunctIndex]'(by rw [← PreTrigger.length_mapped_head]; exact disjIdx_lt)
                constructor
                . apply List.getElem_mem
                . exact c_mem
        | inr f_mem =>
          simp only [FiniteTree.leaves, PreGroundTerm.backtrackFacts]
          cases PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f f_mem c c_mem with
          | inl c_mem => apply Or.inl; exact c_mem
          | inr c_mem =>
            apply Or.inr
            cases c_mem with
            | inl c_mem => apply Or.inl; exact c_mem
            | inr c_mem => apply Or.inr; rw [List.mem_append]; apply Or.inr; exact c_mem

    theorem backtrackFacts_list_constants_in_rules_or_term_or_fresh
        [GetFreshInhabitant sig.C]
        [Inhabited sig.C]
        {rl : RuleList sig}
        {terms : List (PreGroundTerm sig)}
        {terms_arity_ok : ∀ t ∈ terms, PreGroundTerm.arity_ok t}
        {terms_ruleIds_valid : ∀ t ∈ terms, PreGroundTerm.skolem_ruleIds_valid rl t}
        {terms_disjIdx_valid : ∀ t, (t_mem : t ∈ terms) -> PreGroundTerm.skolem_disjIdx_valid rl t (terms_ruleIds_valid t t_mem)}
        {terms_rule_arity_valid : ∀ t, (t_mem : t ∈ terms) -> PreGroundTerm.skolem_rule_arity_valid rl t (terms_ruleIds_valid t t_mem)}
        {forbidden_constants : List sig.C} :
        ∀ f ∈ (PreGroundTerm.backtrackFacts_list rl terms terms_arity_ok terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).fst,
        ∀ c ∈ f.constants,
          c ∈ (rl.rules.flatMap Rule.constants) ∨ c ∈ terms.flatMap FiniteTree.leaves ∨ c ∈ (PreGroundTerm.backtrackFacts_list rl terms terms_arity_ok terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).snd := by
      intro f f_mem c c_mem
      cases terms with
      | nil => simp [backtrackFacts_list] at f_mem
      | cons hd tl =>
        simp only [backtrackFacts_list] at f_mem
        rw [List.mem_append] at f_mem
        cases f_mem with
        | inl f_mem =>
          cases PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh f f_mem c c_mem with
          | inl c_mem => apply Or.inl; exact c_mem
          | inr c_mem =>
            apply Or.inr
            cases c_mem with
            | inl c_mem => apply Or.inl; rw [List.flatMap_cons, List.mem_append]; apply Or.inl; exact c_mem
            | inr c_mem => apply Or.inr; simp only [backtrackFacts_list]; rw [List.mem_append]; apply Or.inl; exact c_mem
        | inr f_mem =>
          cases PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f f_mem c c_mem with
          | inl c_mem => apply Or.inl; exact c_mem
          | inr c_mem =>
            apply Or.inr
            cases c_mem with
            | inl c_mem => apply Or.inl; rw [List.flatMap_cons, List.mem_append]; apply Or.inr; exact c_mem
            | inr c_mem => apply Or.inr; simp only [backtrackFacts_list]; rw [List.mem_append]; apply Or.inr; exact c_mem

  end

end PreGroundTerm

