import BasicLeanDatastructures.GetFreshInhabitant
import ExistentialRules.ChaseSequence.Termination.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

def SkolemFS.ruleId_valid (sfs : SkolemFS sig) (rl : RuleList sig) : Prop :=
  ∃ r ∈ rl.rules, r.id = sfs.ruleId

def SkolemFS.disjunctIndex_valid (sfs : SkolemFS sig) (rl : RuleList sig) (ruleId_valid : sfs.ruleId_valid rl) : Prop :=
  sfs.disjunctIndex < (rl.get_by_id sfs.ruleId ruleId_valid).head.length

def SkolemFS.arity_valid (sfs : SkolemFS sig) (rl : RuleList sig) (ruleId_valid : sfs.ruleId_valid rl) : Prop :=
  sfs.arity = (rl.get_by_id sfs.ruleId ruleId_valid).frontier.length

mutual

  def PreGroundTerm.skolem_ruleIds_valid (rl : RuleList sig) : FiniteTree (SkolemFS sig) sig.C -> Prop
  | .leaf _ => True
  | .inner func ts => func.ruleId_valid rl ∧ PreGroundTerm.skolem_ruleIds_valid_list rl ts

  def PreGroundTerm.skolem_ruleIds_valid_list (rl : RuleList sig) : FiniteTreeList (SkolemFS sig) sig.C -> Prop
  | .nil => True
  | .cons t ts => PreGroundTerm.skolem_ruleIds_valid rl t ∧ PreGroundTerm.skolem_ruleIds_valid_list rl ts

end

mutual

  def PreGroundTerm.skolem_disjIdx_valid
      (rl : RuleList sig)
      (term : FiniteTree (SkolemFS sig) sig.C)
      (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term) : Prop :=
    match term with
    | .leaf _ => True
    | .inner func ts => func.disjunctIndex_valid rl term_ruleIds_valid.left ∧ PreGroundTerm.skolem_disjIdx_valid_list rl ts term_ruleIds_valid.right

  def PreGroundTerm.skolem_disjIdx_valid_list
      (rl : RuleList sig)
      (terms : FiniteTreeList (SkolemFS sig) sig.C)
      (terms_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl terms) : Prop :=
    match terms with
    | .nil => True
    | .cons t ts => PreGroundTerm.skolem_disjIdx_valid rl t terms_ruleIds_valid.left ∧ PreGroundTerm.skolem_disjIdx_valid_list rl ts terms_ruleIds_valid.right

end

mutual

  def PreGroundTerm.skolem_rule_arity_valid
      (rl : RuleList sig)
      (term : FiniteTree (SkolemFS sig) sig.C)
      (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term) : Prop :=
    match term with
    | .leaf _ => True
    | .inner func ts => func.arity_valid rl term_ruleIds_valid.left ∧ PreGroundTerm.skolem_rule_arity_valid_list rl ts term_ruleIds_valid.right

  def PreGroundTerm.skolem_rule_arity_valid_list
      (rl : RuleList sig)
      (terms : FiniteTreeList (SkolemFS sig) sig.C)
      (terms_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl terms) : Prop :=
    match terms with
    | .nil => True
    | .cons t ts => PreGroundTerm.skolem_rule_arity_valid rl t terms_ruleIds_valid.left ∧ PreGroundTerm.skolem_rule_arity_valid_list rl ts terms_ruleIds_valid.right

end

def GroundTerm.skolem_ruleIds_valid (rl : RuleList sig) (term : GroundTerm sig) : Prop := PreGroundTerm.skolem_ruleIds_valid rl term.val
def GroundTerm.skolem_disjIdx_valid (rl : RuleList sig) (term : GroundTerm sig) (term_ruleIds_valid : term.skolem_ruleIds_valid rl) : Prop :=
  PreGroundTerm.skolem_disjIdx_valid rl term.val term_ruleIds_valid
def GroundTerm.skolem_rule_arity_valid (rl : RuleList sig) (term : GroundTerm sig) (term_ruleIds_valid : term.skolem_ruleIds_valid rl) : Prop :=
  PreGroundTerm.skolem_rule_arity_valid rl term.val term_ruleIds_valid

theorem GroundTerm.skolem_ruleIds_valid_const (rl : RuleList sig) (c : sig.C) : (GroundTerm.const c).skolem_ruleIds_valid rl := by
  simp [skolem_ruleIds_valid, PreGroundTerm.skolem_ruleIds_valid, GroundTerm.const]
theorem GroundTerm.skolem_disjIdx_valid_const (rl : RuleList sig) (c : sig.C) : (GroundTerm.const c).skolem_disjIdx_valid rl (skolem_ruleIds_valid_const rl c) := by
  simp [skolem_disjIdx_valid, PreGroundTerm.skolem_disjIdx_valid, GroundTerm.const]
theorem GroundTerm.skolem_rule_arity_valid_const (rl : RuleList sig) (c : sig.C) : (GroundTerm.const c).skolem_rule_arity_valid rl (skolem_ruleIds_valid_const rl c) := by
  simp [skolem_rule_arity_valid, PreGroundTerm.skolem_rule_arity_valid, GroundTerm.const]

theorem GroundTerm.skolem_ruleIds_valid_list (rl : RuleList sig) (ts : List (GroundTerm sig)) : PreGroundTerm.skolem_ruleIds_valid_list rl (FiniteTreeList.fromList ts.unattach) ↔ ∀ t ∈ ts, t.skolem_ruleIds_valid rl := by
  induction ts with
  | nil => simp [FiniteTreeList.fromList, PreGroundTerm.skolem_ruleIds_valid_list]
  | cons hd tl ih =>
    simp only [List.unattach, List.map_cons, FiniteTreeList.fromList, PreGroundTerm.skolem_ruleIds_valid_list]
    simp only [List.unattach] at ih
    rw [ih]
    constructor
    . intro h
      intro t
      rw [List.mem_cons]
      intro t_mem
      cases t_mem with
      | inl t_mem => rw [t_mem]; exact h.left
      | inr t_mem => apply h.right; exact t_mem
    . intro h
      constructor
      . apply h; simp
      . intro t t_mem; apply h; simp [t_mem]

theorem GroundTerm.skolem_disjIdx_valid_list (rl : RuleList sig) (ts : List (GroundTerm sig)) (ruleIds_valid : ∀ t ∈ ts, t.skolem_ruleIds_valid rl) : PreGroundTerm.skolem_disjIdx_valid_list rl (FiniteTreeList.fromList ts.unattach) (by rw [GroundTerm.skolem_ruleIds_valid_list]; exact ruleIds_valid) ↔ ∀ t, (t_mem : t ∈ ts) -> t.skolem_disjIdx_valid rl (ruleIds_valid t t_mem) := by
  induction ts with
  | nil => simp [FiniteTreeList.fromList, PreGroundTerm.skolem_disjIdx_valid_list]
  | cons hd tl ih =>
    specialize ih (by intro t t_mem; apply ruleIds_valid; simp [t_mem])
    simp only [List.unattach, List.map_cons, FiniteTreeList.fromList, PreGroundTerm.skolem_disjIdx_valid_list]
    simp only [List.unattach] at ih
    rw [ih]
    constructor
    . intro h
      intro t t_mem
      rw [List.mem_cons] at t_mem
      cases t_mem with
      | inl t_mem => simp only [t_mem]; exact h.left
      | inr t_mem => apply h.right; exact t_mem
    . intro h
      constructor
      . apply h; simp
      . intro t t_mem; apply h; simp [t_mem]

theorem GroundTerm.skolem_rule_arity_valid_list (rl : RuleList sig) (ts : List (GroundTerm sig)) (ruleIds_valid : ∀ t ∈ ts, t.skolem_ruleIds_valid rl) : PreGroundTerm.skolem_rule_arity_valid_list rl (FiniteTreeList.fromList ts.unattach) (by rw [GroundTerm.skolem_ruleIds_valid_list]; exact ruleIds_valid) ↔ ∀ t, (t_mem : t ∈ ts) -> t.skolem_rule_arity_valid rl (ruleIds_valid t t_mem) := by
  induction ts with
  | nil => simp [FiniteTreeList.fromList, PreGroundTerm.skolem_rule_arity_valid_list]
  | cons hd tl ih =>
    specialize ih (by intro t t_mem; apply ruleIds_valid; simp [t_mem])
    simp only [List.unattach, List.map_cons, FiniteTreeList.fromList, PreGroundTerm.skolem_rule_arity_valid_list]
    simp only [List.unattach] at ih
    rw [ih]
    constructor
    . intro h
      intro t t_mem
      rw [List.mem_cons] at t_mem
      cases t_mem with
      | inl t_mem => simp only [t_mem]; exact h.left
      | inr t_mem => apply h.right; exact t_mem
    . intro h
      constructor
      . apply h; simp
      . intro t t_mem; apply h; simp [t_mem]

def Rule.fresh_consts_for_pure_body_vars [GetFreshInhabitant sig.C] (r : Rule sig) (forbidden_constants : List sig.C) :=
  GetFreshInhabitant.fresh_n forbidden_constants r.pure_body_vars.length

def Rule.length_fresh_consts_for_pure_body_vars [GetFreshInhabitant sig.C] {r : Rule sig} {forbidden_constants : List sig.C} : (r.fresh_consts_for_pure_body_vars forbidden_constants).val.length = r.pure_body_vars.length := (r.fresh_consts_for_pure_body_vars forbidden_constants).property.left

theorem Rule.fresh_consts_for_pure_body_vars_idx_retained [GetFreshInhabitant sig.C] {r : Rule sig} {forbidden_constants : List sig.C} {v : sig.V} {v_mem : v ∈ r.pure_body_vars} : (r.fresh_consts_for_pure_body_vars forbidden_constants).val.idxOf ((r.fresh_consts_for_pure_body_vars forbidden_constants).val[r.pure_body_vars.idxOf v]'(by rw [(r.fresh_consts_for_pure_body_vars forbidden_constants).property.left, List.idxOf_lt_length_iff]; exact v_mem)) = r.pure_body_vars.idxOf v := by
  rw [List.idxOf_getElem]
  exact (r.fresh_consts_for_pure_body_vars forbidden_constants).property.right.left

theorem Rule.fresh_consts_pure_body_vars_roundtrip [GetFreshInhabitant sig.C] {r : Rule sig} {forbidden_constants : List sig.C} {v : sig.V} {v_mem : v ∈ r.pure_body_vars} : r.pure_body_vars[(r.fresh_consts_for_pure_body_vars forbidden_constants).val.idxOf ((r.fresh_consts_for_pure_body_vars forbidden_constants).val[r.pure_body_vars.idxOf v]'(by rw [(r.fresh_consts_for_pure_body_vars forbidden_constants).property.left, List.idxOf_lt_length_iff]; exact v_mem))]'(by rw [fresh_consts_for_pure_body_vars_idx_retained, List.idxOf_lt_length_iff]; exact v_mem; exact v_mem) = v := by
  rw [List.getElem_eq_getElem_of_idx_eq]
  . rw [List.getElem_idxOf_of_mem]
    exact v_mem
  . apply fresh_consts_for_pure_body_vars_idx_retained
    exact v_mem

def PreGroundTerm.backtrackTrigger
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (rl : RuleList sig)
    (term : FiniteTree (SkolemFS sig) sig.C)
    (term_is_func : ∃ func ts, term = .inner func ts)
    (term_arity_ok : PreGroundTerm.arity_ok term)
    (term_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid rl term)
    (term_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid rl term term_ruleIds_valid)
    (forbidden_constants : List sig.C) :
    PreTrigger sig :=
  match term with
  | .leaf c => by simp at term_is_func -- contradiction
  | .inner func ts =>
    let rule : Rule sig := rl.get_by_id func.ruleId term_ruleIds_valid.left
    let fresh_consts_for_pure_body_vars := rule.fresh_consts_for_pure_body_vars forbidden_constants

    let subs : GroundSubstitution sig := fun x =>
      if mem : x ∈ rule.frontier
      then
        let idx := rule.frontier.idxOf x
        have : idx < ts.toList.length := by
          have := LawfulBEq.eq_of_beq (Bool.and_eq_true_iff.mp term_arity_ok).left
          rw [this, term_rule_arity_valid.left]
          apply List.idxOf_lt_length_of_mem
          exact mem
        ⟨ts.toList[idx], by
          have := (PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem ts).mpr (Bool.and_eq_true_iff.mp term_arity_ok).right
          apply this
          simp
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

mutual

  def PreGroundTerm.backtrackFacts
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (term : FiniteTree (SkolemFS sig) sig.C)
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
      let trg : PreTrigger sig := backtrackTrigger rl (.inner func ts) (by exists func, ts) term_arity_ok term_ruleIds_valid term_rule_arity_valid forbidden_constants
      let disjIdx := func.disjunctIndex
      have : disjIdx < trg.mapped_head.length := by rw [PreTrigger.length_mapped_head]; unfold trg; unfold backtrackTrigger; exact term_disjIdx_valid.left

      let fresh_consts_for_pure_body_vars := trg.rule.fresh_consts_for_pure_body_vars forbidden_constants

      let recursive_result := PreGroundTerm.backtrackFacts_list rl ts (Bool.and_eq_true_iff.mp term_arity_ok).right term_ruleIds_valid.right term_disjIdx_valid.right term_rule_arity_valid.right (forbidden_constants ++ fresh_consts_for_pure_body_vars)

      ((trg.mapped_body ++ trg.mapped_head[disjIdx]) ++ recursive_result.fst, recursive_result.snd ++ fresh_consts_for_pure_body_vars.val)

  def PreGroundTerm.backtrackFacts_list
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (terms : FiniteTreeList (SkolemFS sig) sig.C)
      (terms_arity_ok : PreGroundTerm.arity_ok_list terms)
      (terms_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl terms)
      (terms_disjIdx_valid : PreGroundTerm.skolem_disjIdx_valid_list rl terms terms_ruleIds_valid)
      (terms_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid_list rl terms terms_ruleIds_valid)
      (forbidden_constants : List sig.C) : (List (Fact sig)) × (List sig.C) :=
    match terms with
    | .nil => ([], [])
    | .cons t ts =>
      let t_res := PreGroundTerm.backtrackFacts rl t (Bool.and_eq_true_iff.mp terms_arity_ok).left terms_ruleIds_valid.left terms_disjIdx_valid.left terms_rule_arity_valid.left forbidden_constants

      let ts_res := PreGroundTerm.backtrackFacts_list rl ts (Bool.and_eq_true_iff.mp terms_arity_ok).right terms_ruleIds_valid.right terms_disjIdx_valid.right terms_rule_arity_valid.right (forbidden_constants ++ t_res.snd)
      (t_res.fst ++ ts_res.fst, t_res.snd ++ ts_res.snd)

end

mutual

  theorem PreGroundTerm.backtrackFacts_fresh_constants_not_forbidden
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {rl : RuleList sig}
      {term : FiniteTree (SkolemFS sig) sig.C}
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
      | inl c_mem => have := backtrackFacts_list_fresh_constants_not_forbidden c c_mem; intro contra; apply this; rw [List.mem_append]; apply Or.inl; exact contra
      | inr c_mem =>
        let trg : PreTrigger sig := backtrackTrigger rl (.inner func ts) (by exists func, ts) term_arity_ok term_ruleIds_valid term_rule_arity_valid forbidden_constants
        let fresh_consts_for_pure_body_vars := trg.rule.fresh_consts_for_pure_body_vars forbidden_constants
        apply fresh_consts_for_pure_body_vars.property.right.right
        exact c_mem

  theorem PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {rl : RuleList sig}
      {terms : FiniteTreeList (SkolemFS sig) sig.C}
      {terms_arity_ok : PreGroundTerm.arity_ok_list terms}
      {terms_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl terms}
      {terms_disjIdx_valid : PreGroundTerm.skolem_disjIdx_valid_list rl terms terms_ruleIds_valid}
      {terms_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid_list rl terms terms_ruleIds_valid}
      {forbidden_constants : List sig.C} :
      ∀ c ∈ (PreGroundTerm.backtrackFacts_list rl terms terms_arity_ok terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).snd, c ∉ forbidden_constants := by
    intro c c_mem
    cases terms with
    | nil => simp [backtrackFacts_list] at c_mem
    | cons hd tl =>
      simp only [backtrackFacts_list] at c_mem
      rw [List.mem_append] at c_mem
      cases c_mem with
      | inl c_mem => exact backtrackFacts_fresh_constants_not_forbidden c c_mem
      | inr c_mem => have := backtrackFacts_list_fresh_constants_not_forbidden c c_mem; intro contra; apply this; rw [List.mem_append]; apply Or.inl; exact contra

end

mutual

  theorem PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {rl : RuleList sig}
      {term : FiniteTree (SkolemFS sig) sig.C}
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
          have t_mem : t ∈ trg.mapped_body.flatMap Fact.terms := by rw [List.mem_flatMap]; exists f
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
              rw [FiniteTree.mem_leavesList]
              exists ts.toList[trg.rule.frontier.idxOf v]'(by
                have := LawfulBEq.eq_of_beq (Bool.and_eq_true_iff.mp term_arity_ok).left
                rw [this, term_rule_arity_valid.left]
                apply List.idxOf_lt_length_of_mem
                exact v_mem_frontier)
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
              apply Or.inr
              rw [c_mem]
              apply List.getElem_mem
        | inr f_mem =>
          have disjIdx_lt : func.disjunctIndex < trg.mapped_head.length := by rw [PreTrigger.length_mapped_head]; apply term_disjIdx_valid.left
          have c_mem : c ∈ FactSet.constants trg.mapped_head[func.disjunctIndex].toSet := by
            exists f
            constructor
            . rw [List.mem_toSet]; exact f_mem
            . exact c_mem
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
            rw [FiniteTree.mem_leavesList]
            exists ts.toList[trg.rule.frontier.idxOf v]'(by
              have := LawfulBEq.eq_of_beq (Bool.and_eq_true_iff.mp term_arity_ok).left
              rw [this, term_rule_arity_valid.left]
              apply List.idxOf_lt_length_of_mem
              exact v_mem)
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
          | inr c_mem => apply Or.inr; rw [List.mem_append]; apply Or.inl; exact c_mem

  theorem PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {rl : RuleList sig}
      {terms : FiniteTreeList (SkolemFS sig) sig.C}
      {terms_arity_ok : PreGroundTerm.arity_ok_list terms}
      {terms_ruleIds_valid : PreGroundTerm.skolem_ruleIds_valid_list rl terms}
      {terms_disjIdx_valid : PreGroundTerm.skolem_disjIdx_valid_list rl terms terms_ruleIds_valid}
      {terms_rule_arity_valid : PreGroundTerm.skolem_rule_arity_valid_list rl terms terms_ruleIds_valid}
      {forbidden_constants : List sig.C} :
      ∀ f ∈ (PreGroundTerm.backtrackFacts_list rl terms terms_arity_ok terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).fst,
      ∀ c ∈ f.constants,
        c ∈ (rl.rules.flatMap Rule.constants) ∨ c ∈ FiniteTree.leavesList terms ∨ c ∈ (PreGroundTerm.backtrackFacts_list rl terms terms_arity_ok terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).snd := by
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
          | inl c_mem => apply Or.inl; unfold FiniteTree.leavesList; rw [List.mem_append]; apply Or.inl; exact c_mem
          | inr c_mem => apply Or.inr; simp only [backtrackFacts_list]; rw [List.mem_append]; apply Or.inl; exact c_mem
      | inr f_mem =>
        cases PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f f_mem c c_mem with
        | inl c_mem => apply Or.inl; exact c_mem
        | inr c_mem =>
          apply Or.inr
          cases c_mem with
          | inl c_mem => apply Or.inl; unfold FiniteTree.leavesList; rw [List.mem_append]; apply Or.inr; exact c_mem
          | inr c_mem => apply Or.inr; simp only [backtrackFacts_list]; rw [List.mem_append]; apply Or.inr; exact c_mem

end

namespace GroundTerm

  def backtrackTrigger
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (term : GroundTerm sig)
      (term_is_func : ∃ func ts arity_ok, term = GroundTerm.func func ts arity_ok)
      (term_ruleIds_valid : term.skolem_ruleIds_valid rl)
      (term_rule_arity_valid : term.skolem_rule_arity_valid rl term_ruleIds_valid)
      (forbidden_constants : List sig.C) : PreTrigger sig :=
    PreGroundTerm.backtrackTrigger rl term.val (by rcases term_is_func with ⟨func, ts, _, eq⟩; exists func, FiniteTreeList.fromList ts.unattach; rw [eq]; rfl) term.property term_ruleIds_valid term_rule_arity_valid forbidden_constants

  def backtrackFacts
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (term : GroundTerm sig)
      (term_ruleIds_valid : term.skolem_ruleIds_valid rl)
      (term_disjIdx_valid : term.skolem_disjIdx_valid rl term_ruleIds_valid)
      (term_rule_arity_valid : term.skolem_rule_arity_valid rl term_ruleIds_valid)
      (forbidden_constants : List sig.C) : (List (Fact sig)) × (List sig.C) :=
    PreGroundTerm.backtrackFacts rl term.val term.property term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants

  def backtrackFacts_list
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (rl : RuleList sig)
      (terms : List (GroundTerm sig))
      (terms_ruleIds_valid : ∀ t ∈ terms, t.skolem_ruleIds_valid rl)
      (terms_disjIdx_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_disjIdx_valid rl (terms_ruleIds_valid t mem))
      (terms_rule_arity_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_rule_arity_valid rl (terms_ruleIds_valid t mem))
      (forbidden_constants : List sig.C) : (List (Fact sig)) × (List sig.C) :=
    match terms with
    | .nil => ([], [])
    | .cons hd tl =>
      have hd_mem : hd ∈ hd :: tl := by simp
      let result_for_hd := hd.backtrackFacts rl (terms_ruleIds_valid hd hd_mem) (terms_disjIdx_valid hd hd_mem) (terms_rule_arity_valid hd hd_mem) forbidden_constants

      let recursive_result := backtrackFacts_list rl tl
        (by intro t t_mem; apply terms_ruleIds_valid; simp [t_mem])
        (by intro t t_mem; apply terms_disjIdx_valid; simp [t_mem])
        (by intro t t_mem; apply terms_rule_arity_valid; simp [t_mem])
        (forbidden_constants ++ result_for_hd.snd)

      (result_for_hd.fst ++ recursive_result.fst, result_for_hd.snd ++ recursive_result.snd)

  theorem backtrackFacts_fresh_constants_not_forbidden
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {rl : RuleList sig}
      {term : GroundTerm sig}
      {term_ruleIds_valid : GroundTerm.skolem_ruleIds_valid rl term}
      {term_disjIdx_valid : GroundTerm.skolem_disjIdx_valid rl term term_ruleIds_valid}
      {term_rule_arity_valid : GroundTerm.skolem_rule_arity_valid rl term term_ruleIds_valid}
      {forbidden_constants : List sig.C} :
      ∀ c ∈ (GroundTerm.backtrackFacts rl term term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants).snd, c ∉ forbidden_constants := by
    intro c c_mem
    unfold backtrackFacts at c_mem
    apply PreGroundTerm.backtrackFacts_fresh_constants_not_forbidden
    exact c_mem

  theorem backtrackFacts_list_fresh_constants_not_forbidden
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {rl : RuleList sig}
      {terms : List (GroundTerm sig)}
      {terms_ruleIds_valid : ∀ t ∈ terms, t.skolem_ruleIds_valid rl}
      {terms_disjIdx_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_disjIdx_valid rl (terms_ruleIds_valid t mem)}
      {terms_rule_arity_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_rule_arity_valid rl (terms_ruleIds_valid t mem)}
      {forbidden_constants : List sig.C} :
      ∀ c ∈ (GroundTerm.backtrackFacts_list rl terms terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).snd, c ∉ forbidden_constants := by
    intro c c_mem
    induction terms generalizing forbidden_constants with
    | nil => simp [backtrackFacts_list] at c_mem
    | cons hd tl ih =>
      simp only [backtrackFacts_list] at c_mem
      rw [List.mem_append] at c_mem
      cases c_mem with
      | inl c_mem => apply backtrackFacts_fresh_constants_not_forbidden; exact c_mem
      | inr c_mem =>
        specialize ih c_mem
        intro contra
        apply ih
        rw [List.mem_append]
        apply Or.inl
        exact contra

  theorem backtrackFacts_constants_in_rules_or_term_or_fresh
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {rl : RuleList sig}
      {term : GroundTerm sig}
      {term_ruleIds_valid : GroundTerm.skolem_ruleIds_valid rl term}
      {term_disjIdx_valid : GroundTerm.skolem_disjIdx_valid rl term term_ruleIds_valid}
      {term_rule_arity_valid : GroundTerm.skolem_rule_arity_valid rl term term_ruleIds_valid}
      {forbidden_constants : List sig.C} :
      ∀ f ∈ (GroundTerm.backtrackFacts rl term term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants).fst,
      ∀ c ∈ f.constants,
        c ∈ (rl.rules.flatMap Rule.constants) ∨ c ∈ term.constants ∨ c ∈ (GroundTerm.backtrackFacts rl term term_ruleIds_valid term_disjIdx_valid term_rule_arity_valid forbidden_constants).snd := by
    intro f f_mem c c_mem
    unfold backtrackFacts at f_mem
    cases PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh f f_mem c c_mem with
    | inl c_mem => apply Or.inl; exact c_mem
    | inr c_mem =>
      apply Or.inr
      cases c_mem with
      | inl c_mem => apply Or.inl; exact c_mem
      | inr c_mem => apply Or.inr; exact c_mem

  theorem backtrackFacts_list_constants_in_rules_or_term_or_fresh
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {rl : RuleList sig}
      {terms : List (GroundTerm sig)}
      {terms_ruleIds_valid : ∀ t ∈ terms, t.skolem_ruleIds_valid rl}
      {terms_disjIdx_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_disjIdx_valid rl (terms_ruleIds_valid t mem)}
      {terms_rule_arity_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_rule_arity_valid rl (terms_ruleIds_valid t mem)}
      {forbidden_constants : List sig.C} :
      ∀ f ∈ (GroundTerm.backtrackFacts_list rl terms terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).fst,
      ∀ c ∈ f.constants,
        c ∈ (rl.rules.flatMap Rule.constants) ∨ c ∈ terms.flatMap GroundTerm.constants ∨ c ∈ (GroundTerm.backtrackFacts_list rl terms terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants).snd := by
    intro f f_mem c c_mem
    induction terms generalizing forbidden_constants with
    | nil => simp [backtrackFacts_list] at f_mem
    | cons hd tl ih =>
      simp only [backtrackFacts_list] at f_mem
      rw [List.mem_append] at f_mem
      cases f_mem with
      | inl f_mem =>
        cases backtrackFacts_constants_in_rules_or_term_or_fresh f f_mem c c_mem with
        | inl c_mem => apply Or.inl; exact c_mem
        | inr c_mem =>
          apply Or.inr
          cases c_mem with
          | inl c_mem => apply Or.inl; rw [List.flatMap_cons, List.mem_append]; apply Or.inl; exact c_mem
          | inr c_mem => apply Or.inr; simp only [backtrackFacts_list]; rw [List.mem_append]; apply Or.inl; exact c_mem
      | inr f_mem =>
        cases ih f_mem with
        | inl c_mem => apply Or.inl; exact c_mem
        | inr c_mem =>
          apply Or.inr
          cases c_mem with
          | inl c_mem => apply Or.inl; rw [List.flatMap_cons, List.mem_append]; apply Or.inr; exact c_mem
          | inr c_mem => apply Or.inr; simp only [backtrackFacts_list]; rw [List.mem_append]; apply Or.inr; exact c_mem

end GroundTerm

def PreTrigger.skolem_ruleIds_valid (rl : RuleList sig) (trg : PreTrigger sig) : Prop := ∀ t ∈ trg.mapped_body.flatMap Fact.terms, t.skolem_ruleIds_valid rl
def PreTrigger.skolem_disjIdx_valid (rl : RuleList sig) (trg : PreTrigger sig) (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl) : Prop :=
  ∀ t, (h : t ∈ trg.mapped_body.flatMap Fact.terms) -> t.skolem_disjIdx_valid rl (trg_ruleIds_valid t h)
def PreTrigger.skolem_rule_arity_valid (rl : RuleList sig) (trg : PreTrigger sig) (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl) : Prop :=
  ∀ t, (h : t ∈ trg.mapped_body.flatMap Fact.terms) -> t.skolem_rule_arity_valid rl (trg_ruleIds_valid t h)

theorem PreTrigger.skolem_ruleIds_valid_of_strong_equiv {rl : RuleList sig} {trg trg2 : PreTrigger sig} (strong_equiv : trg.strong_equiv trg2) (trg_valid : trg.skolem_ruleIds_valid rl) : trg2.skolem_ruleIds_valid rl := by
  unfold skolem_ruleIds_valid; rw [← PreTrigger.mapped_body_eq_of_strong_equiv strong_equiv]; exact trg_valid

theorem PreTrigger.skolem_disjIdx_valid_of_strong_equiv {rl : RuleList sig} {trg trg2 : PreTrigger sig} (strong_equiv : trg.strong_equiv trg2) (h : trg.skolem_ruleIds_valid rl) (trg_valid : trg.skolem_disjIdx_valid rl h) : trg2.skolem_disjIdx_valid rl (PreTrigger.skolem_ruleIds_valid_of_strong_equiv strong_equiv h) := by
  unfold skolem_disjIdx_valid; simp only [← PreTrigger.mapped_body_eq_of_strong_equiv strong_equiv]; exact trg_valid

theorem PreTrigger.skolem_rule_arity_valid_of_strong_equiv {rl : RuleList sig} {trg trg2 : PreTrigger sig} (strong_equiv : trg.strong_equiv trg2) (h : trg.skolem_ruleIds_valid rl) (trg_valid : trg.skolem_rule_arity_valid rl h) : trg2.skolem_rule_arity_valid rl (PreTrigger.skolem_ruleIds_valid_of_strong_equiv strong_equiv h) := by
  unfold skolem_rule_arity_valid; simp only [← PreTrigger.mapped_body_eq_of_strong_equiv strong_equiv]; exact trg_valid

theorem PreTrigger.skolem_ruleIds_valid_for_functional_term
    (rl : RuleList sig)
    (trg : PreTrigger sig)
    (rule_mem : trg.rule ∈ rl.rules)
    (body_valid : trg.skolem_ruleIds_valid rl) :
    ∀ i v, (trg.functional_term_for_var i v).skolem_ruleIds_valid rl := by
  intro i v
  simp only [GroundTerm.skolem_ruleIds_valid, PreGroundTerm.skolem_ruleIds_valid, PreTrigger.functional_term_for_var, GroundTerm.func]
  constructor
  . exists trg.rule
  . rw [GroundTerm.skolem_ruleIds_valid_list rl (trg.rule.frontier.map trg.subs)]
    intro t t_mem
    rw [List.mem_map] at t_mem
    rcases t_mem with ⟨v, v_mem, t_eq⟩
    apply body_valid
    rcases trg.rule.frontier_occurs_in_body v v_mem with ⟨a, a_mem, hd_mem⟩
    rw [List.mem_flatMap]
    exists trg.subs.apply_function_free_atom a
    constructor
    . apply List.mem_map_of_mem; exact a_mem
    . unfold GroundSubstitution.apply_function_free_atom
      rw [List.mem_map]
      exists VarOrConst.var v

theorem PreTrigger.skolem_disjIdx_valid_for_functional_term
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
    rw [GroundTerm.skolem_disjIdx_valid_list rl (trg.rule.frontier.map trg.subs) (by rw [← GroundTerm.skolem_ruleIds_valid_list rl (trg.rule.frontier.map trg.subs)]; exact func_ruleIds_valid.right)]
    intro t t_mem
    rw [List.mem_map] at t_mem
    rcases t_mem with ⟨v, v_mem, t_eq⟩
    apply body_valid
    rcases trg.rule.frontier_occurs_in_body v v_mem with ⟨a, a_mem, hd_mem⟩
    rw [List.mem_flatMap]
    exists trg.subs.apply_function_free_atom a
    constructor
    . apply List.mem_map_of_mem; exact a_mem
    . unfold GroundSubstitution.apply_function_free_atom
      rw [List.mem_map]
      exists VarOrConst.var v

theorem PreTrigger.skolem_rule_arity_valid_for_functional_term
    (rl : RuleList sig)
    (trg : PreTrigger sig)
    (rule_mem : trg.rule ∈ rl.rules)
    (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
    (body_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid) :
    ∀ i v, (trg.functional_term_for_var i v).skolem_rule_arity_valid rl (trg.skolem_ruleIds_valid_for_functional_term rl rule_mem trg_ruleIds_valid i v) := by
  intro i v
  simp only [GroundTerm.func, functional_term_for_var]
  constructor
  . unfold SkolemFS.arity_valid
    rw [rl.get_by_id_self _ rule_mem]
  . have func_ruleIds_valid := trg.skolem_ruleIds_valid_for_functional_term rl rule_mem trg_ruleIds_valid i v
    rw [GroundTerm.skolem_rule_arity_valid_list rl (trg.rule.frontier.map trg.subs) (by rw [← GroundTerm.skolem_ruleIds_valid_list rl (trg.rule.frontier.map trg.subs)]; exact func_ruleIds_valid.right)]
    intro t t_mem
    rw [List.mem_map] at t_mem
    rcases t_mem with ⟨v, v_mem, t_eq⟩
    apply body_valid
    rcases trg.rule.frontier_occurs_in_body v v_mem with ⟨a, a_mem, hd_mem⟩
    rw [List.mem_flatMap]
    exists trg.subs.apply_function_free_atom a
    constructor
    . apply List.mem_map_of_mem; exact a_mem
    . unfold GroundSubstitution.apply_function_free_atom
      rw [List.mem_map]
      exists VarOrConst.var v

theorem PreTrigger.skolem_ruleIds_remain_valid_in_head (rl : RuleList sig) (trg : PreTrigger sig) (rule_mem : trg.rule ∈ rl.rules) (body_valid : trg.skolem_ruleIds_valid rl) :
    ∀ t ∈ trg.mapped_head.flatten.flatMap Fact.terms, t.skolem_ruleIds_valid rl := by
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
      rcases trg.rule.frontier_occurs_in_body v mem_frontier with ⟨a, a_mem, v_mem⟩
      rw [List.mem_flatMap]
      exists trg.subs.apply_function_free_atom a
      constructor
      . apply List.mem_map_of_mem; exact a_mem
      . unfold GroundSubstitution.apply_function_free_atom
        rw [List.mem_map]
        exists VarOrConst.var v
    | inr mem_frontier =>
      unfold voc at eq
      rw [eq, trg.apply_to_var_or_const_non_frontier_var disj_idx.val _ mem_frontier]
      apply skolem_ruleIds_valid_for_functional_term
      . exact rule_mem
      . exact body_valid

theorem PreTrigger.skolem_disjIdx_remains_valid_in_head
    (rl : RuleList sig)
    (trg : PreTrigger sig)
    (rule_mem : trg.rule ∈ rl.rules)
    (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
    (body_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid) :
    ∀ t, (t_mem : t ∈ trg.mapped_head.flatten.flatMap Fact.terms) -> t.skolem_disjIdx_valid rl (trg.skolem_ruleIds_remain_valid_in_head rl rule_mem trg_ruleIds_valid t t_mem) := by
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
      rcases trg.rule.frontier_occurs_in_body v v_mem with ⟨a, a_mem, v_mem⟩
      rw [List.mem_flatMap]
      exists trg.subs.apply_function_free_atom a
      constructor
      . apply List.mem_map_of_mem; exact a_mem
      . unfold GroundSubstitution.apply_function_free_atom
        rw [List.mem_map]
        exists VarOrConst.var v
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

theorem PreTrigger.skolem_rule_arity_remains_valid_in_head
    (rl : RuleList sig)
    (trg : PreTrigger sig)
    (rule_mem : trg.rule ∈ rl.rules)
    (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
    (body_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid) :
    ∀ t, (t_mem : t ∈ trg.mapped_head.flatten.flatMap Fact.terms) -> t.skolem_rule_arity_valid rl (trg.skolem_ruleIds_remain_valid_in_head rl rule_mem trg_ruleIds_valid t t_mem) := by
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
      rcases trg.rule.frontier_occurs_in_body v v_mem with ⟨a, a_mem, v_mem⟩
      rw [List.mem_flatMap]
      exists trg.subs.apply_function_free_atom a
      constructor
      . apply List.mem_map_of_mem; exact a_mem
      . unfold GroundSubstitution.apply_function_free_atom
        rw [List.mem_map]
        exists VarOrConst.var v
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

def PreTrigger.backtrackTrigger_for_functional_term
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

theorem PreTrigger.backtrackTrigger_for_functional_term_equiv
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
    simp only [FiniteTreeList.fromListToListIsId]
    rw [List.getElem_unattach, List.getElem_map]
    conv => left; right; right; left; rw [RuleList.get_by_id_self _ _ trg_rule_mem]
    rw [List.getElem_idxOf_of_mem]
    rw [RuleList.get_by_id_self _ _ trg_rule_mem] at u_mem
    exact u_mem

def PreTrigger.backtrackFacts
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (rl : RuleList sig)
    (trg : PreTrigger sig)
    (trg_ruleIds_valid : trg.skolem_ruleIds_valid rl)
    (trg_disjIdx_valid : trg.skolem_disjIdx_valid rl trg_ruleIds_valid)
    (trg_rule_arity_valid : trg.skolem_rule_arity_valid rl trg_ruleIds_valid) : (List (Fact sig)) × (List sig.C) :=
  let forbidden_constants := trg.mapped_body.flatMap Fact.constants ++ rl.rules.flatMap Rule.constants
  let backtrack_result := GroundTerm.backtrackFacts_list rl (trg.mapped_body.flatMap Fact.terms) trg_ruleIds_valid trg_disjIdx_valid trg_rule_arity_valid forbidden_constants
  (trg.mapped_body ++ backtrack_result.fst, backtrack_result.snd)

theorem PreTrigger.backtrackFacts_eq_of_strong_equiv
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

theorem ChaseBranch.term_ruleIds_valid (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
    ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) -> ∀ (term : GroundTerm sig), term ∈ node.fact.val.terms -> term.skolem_ruleIds_valid rl := by
  intro rl rl_rs_eq term term_mem
  induction i generalizing node term with
  | zero =>
    rw [cb.database_first] at eq
    injection eq with eq
    rw [← eq] at term_mem
    simp only at term_mem
    unfold FactSet.terms at term_mem
    rcases term_mem with ⟨f, f_mem, term_mem⟩
    rcases kb.db.toFactSet.property.right f f_mem term term_mem with ⟨_, t_eq⟩
    rw [t_eq]
    apply GroundTerm.skolem_ruleIds_valid_const
  | succ i ih =>
    rw [cb.origin_trg_result_yields_next_node_fact i node eq] at term_mem
    unfold FactSet.terms at term_mem
    rcases term_mem with ⟨f, f_mem, term_mem⟩
    cases f_mem with
    | inl f_mem => apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq); exists f
    | inr f_mem =>
      let origin := node.origin.get (cb.origin_isSome i eq)
      rw [List.mem_toSet] at f_mem
      apply PreTrigger.skolem_ruleIds_remain_valid_in_head rl origin.fst.val (by rw [rl_rs_eq]; exact origin.fst.property)
      . intro t t_mem
        rw [List.mem_flatMap] at t_mem
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) t
        exists f
        constructor
        . have := cb.origin_trg_is_active i node eq
          apply this.left
          rw [List.mem_toSet]
          exact f_mem
        . exact t_mem
      . rw [List.mem_flatMap]
        exists f
        constructor
        . apply List.mem_flatten_of_mem
          . exact List.getElem_mem origin.snd.isLt
          . exact f_mem
        . exact term_mem

theorem ChaseBranch.trigger_ruleIds_valid_of_loaded (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
    ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) -> ∀ (trg : PreTrigger sig), trg.loaded node.fact -> trg.skolem_ruleIds_valid rl := by
  intro rl rl_rs_eq trg trg_loaded
  intro t t_mem_body
  rw [List.mem_flatMap] at t_mem_body
  rcases t_mem_body with ⟨f, f_mem, t_mem⟩
  specialize trg_loaded f (by rw [List.mem_toSet]; exact f_mem)
  apply cb.term_ruleIds_valid i node eq rl rl_rs_eq
  exists f

theorem ChaseBranch.term_disjIdx_valid_aux (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
    ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) -> ∀ (term : GroundTerm sig), term ∈ node.fact.val.terms -> (h : term.skolem_ruleIds_valid rl) -> term.skolem_disjIdx_valid rl h := by
  intro rl rl_rs_eq term term_mem term_ruleIds_valid
  induction i generalizing node term with
  | zero =>
    rw [cb.database_first] at eq
    injection eq with eq
    rw [← eq] at term_mem
    simp only at term_mem
    unfold FactSet.terms at term_mem
    rcases term_mem with ⟨f, f_mem, term_mem⟩
    rcases kb.db.toFactSet.property.right f f_mem term term_mem with ⟨_, t_eq⟩
    simp only [t_eq]
    apply GroundTerm.skolem_disjIdx_valid_const
  | succ i ih =>
    rw [cb.origin_trg_result_yields_next_node_fact i node eq] at term_mem
    unfold FactSet.terms at term_mem
    rcases term_mem with ⟨f, f_mem, term_mem⟩
    cases f_mem with
    | inl f_mem => apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq); exists f
    | inr f_mem =>
      let origin := node.origin.get (cb.origin_isSome i eq)
      have origin_active := cb.origin_trg_is_active i node eq
      have origin_trg_valid := cb.trigger_ruleIds_valid_of_loaded i (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) rl rl_rs_eq origin.fst.val origin_active.left
      rw [List.mem_toSet] at f_mem
      apply PreTrigger.skolem_disjIdx_remains_valid_in_head rl origin.fst.val (by rw [rl_rs_eq]; exact origin.fst.property) origin_trg_valid
      . intro t t_mem
        rw [List.mem_flatMap] at t_mem
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) t
        exists f
        constructor
        . have := cb.origin_trg_is_active i node eq
          apply this.left
          rw [List.mem_toSet]
          exact f_mem
        . exact t_mem
      . rw [List.mem_flatMap]
        exists f
        constructor
        . apply List.mem_flatten_of_mem
          . exact List.getElem_mem origin.snd.isLt
          . exact f_mem
        . exact term_mem

theorem ChaseBranch.term_disjIdx_valid (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (term : GroundTerm sig) (term_mem : term ∈ node.fact.val.terms) : term.skolem_disjIdx_valid rl (cb.term_ruleIds_valid i node eq rl rl_rs_eq term term_mem) := cb.term_disjIdx_valid_aux i node eq rl rl_rs_eq term term_mem (cb.term_ruleIds_valid i node eq rl rl_rs_eq term term_mem)

theorem ChaseBranch.trigger_disjIdx_valid_of_loaded (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (trg : PreTrigger sig) (trg_loaded : trg.loaded node.fact) : trg.skolem_disjIdx_valid rl (cb.trigger_ruleIds_valid_of_loaded i node eq rl rl_rs_eq trg trg_loaded) := by
  intro t t_mem_body
  rw [List.mem_flatMap] at t_mem_body
  rcases t_mem_body with ⟨f, f_mem, t_mem⟩
  specialize trg_loaded f (by rw [List.mem_toSet]; exact f_mem)
  apply cb.term_disjIdx_valid i node eq rl rl_rs_eq
  exists f

theorem ChaseBranch.term_rule_arity_valid_aux (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
    ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) -> ∀ (term : GroundTerm sig), term ∈ node.fact.val.terms -> (h : term.skolem_ruleIds_valid rl) -> term.skolem_rule_arity_valid rl h := by
  intro rl rl_rs_eq term term_mem term_ruleIds_valid
  induction i generalizing node term with
  | zero =>
    rw [cb.database_first] at eq
    injection eq with eq
    rw [← eq] at term_mem
    simp only at term_mem
    unfold FactSet.terms at term_mem
    rcases term_mem with ⟨f, f_mem, term_mem⟩
    rcases kb.db.toFactSet.property.right f f_mem term term_mem with ⟨_, t_eq⟩
    simp only [t_eq]
    apply GroundTerm.skolem_rule_arity_valid_const
  | succ i ih =>
    rw [cb.origin_trg_result_yields_next_node_fact i node eq] at term_mem
    unfold FactSet.terms at term_mem
    rcases term_mem with ⟨f, f_mem, term_mem⟩
    cases f_mem with
    | inl f_mem => apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq); exists f
    | inr f_mem =>
      let origin := node.origin.get (cb.origin_isSome i eq)
      have origin_active := cb.origin_trg_is_active i node eq
      have origin_trg_valid := cb.trigger_ruleIds_valid_of_loaded i (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) rl rl_rs_eq origin.fst.val origin_active.left
      rw [List.mem_toSet] at f_mem
      apply PreTrigger.skolem_rule_arity_remains_valid_in_head rl origin.fst.val (by rw [rl_rs_eq]; exact origin.fst.property) origin_trg_valid
      . intro t t_mem
        rw [List.mem_flatMap] at t_mem
        rcases t_mem with ⟨f, f_mem, t_mem⟩
        apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) t
        exists f
        constructor
        . have := cb.origin_trg_is_active i node eq
          apply this.left
          rw [List.mem_toSet]
          exact f_mem
        . exact t_mem
      . rw [List.mem_flatMap]
        exists f
        constructor
        . apply List.mem_flatten_of_mem
          . exact List.getElem_mem origin.snd.isLt
          . exact f_mem
        . exact term_mem

theorem ChaseBranch.term_rule_arity_valid (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (term : GroundTerm sig) (term_mem : term ∈ node.fact.val.terms) : term.skolem_rule_arity_valid rl (cb.term_ruleIds_valid i node eq rl rl_rs_eq term term_mem) := cb.term_rule_arity_valid_aux i node eq rl rl_rs_eq term term_mem (cb.term_ruleIds_valid i node eq rl rl_rs_eq term term_mem)

theorem ChaseBranch.trigger_rule_arity_valid_of_loaded (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (trg : PreTrigger sig) (trg_loaded : trg.loaded node.fact) : trg.skolem_rule_arity_valid rl (cb.trigger_ruleIds_valid_of_loaded i node eq rl rl_rs_eq trg trg_loaded) := by
  intro t t_mem_body
  rw [List.mem_flatMap] at t_mem_body
  rcases t_mem_body with ⟨f, f_mem, t_mem⟩
  specialize trg_loaded f (by rw [List.mem_toSet]; exact f_mem)
  apply cb.term_rule_arity_valid i node eq rl rl_rs_eq
  exists f

