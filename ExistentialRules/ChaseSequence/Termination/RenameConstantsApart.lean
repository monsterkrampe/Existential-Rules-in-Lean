import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts

variable {sig : Signature} [DecidableEq sig.V]


mutual

  def PreGroundTerm.rename_constants_apart
      [GetFreshRepresentant sig.C]
      (term : FiniteTree (SkolemFS sig) sig.C)
      (forbidden_constants : List sig.C) : FiniteTree (SkolemFS sig) sig.C :=
    match term with
    | .leaf _ => .leaf (GetFreshRepresentant.fresh forbidden_constants)
    | .inner func ts =>
      let recursive_result := PreGroundTerm.rename_constants_apart_list ts forbidden_constants
      .inner func recursive_result

  def PreGroundTerm.rename_constants_apart_list
      [GetFreshRepresentant sig.C]
      (terms : FiniteTreeList (SkolemFS sig) sig.C)
      (forbidden_constants : List sig.C) : FiniteTreeList (SkolemFS sig) sig.C :=
    match terms with
    | .nil => .nil
    | .cons t ts =>
      let t_res := PreGroundTerm.rename_constants_apart t forbidden_constants
      let ts_res := PreGroundTerm.rename_constants_apart_list ts (forbidden_constants ++ t_res.leaves)
      .cons t_res ts_res

end

mutual

  theorem PreGroundTerm.rename_constants_apart_leaves_fresh
      [GetFreshRepresentant sig.C]
      (term : FiniteTree (SkolemFS sig) sig.C)
      (forbidden_constants : List sig.C) :
      ∀ e, e ∈ (PreGroundTerm.rename_constants_apart term forbidden_constants).leaves -> e ∉ forbidden_constants := by
    cases term with
    | leaf c =>
      intro e e_mem
      simp only [rename_constants_apart, FiniteTree.leaves, List.mem_singleton] at e_mem
      have prop := (GetFreshRepresentant.fresh forbidden_constants).property
      rw [e_mem]
      exact prop
    | inner func ts =>
      intro e e_mem
      simp only [FiniteTree.leaves, rename_constants_apart] at e_mem
      apply rename_constants_apart_leaves_fresh_list
      exact e_mem

  theorem PreGroundTerm.rename_constants_apart_leaves_fresh_list
      [GetFreshRepresentant sig.C]
      (terms : FiniteTreeList (SkolemFS sig) sig.C)
      (forbidden_constants : List sig.C) :
      ∀ e, e ∈ FiniteTree.leavesList (PreGroundTerm.rename_constants_apart_list terms forbidden_constants) -> e ∉ forbidden_constants := by
    cases terms with
    | nil => simp [rename_constants_apart_list, FiniteTree.leavesList]
    | cons hd tl =>
      intro e e_mem
      simp only [FiniteTree.leavesList, rename_constants_apart_list] at e_mem
      rw [List.mem_append] at e_mem
      cases e_mem with
      | inl e_mem => apply rename_constants_apart_leaves_fresh; exact e_mem
      | inr e_mem =>
        have := rename_constants_apart_leaves_fresh_list tl _ e e_mem
        intro contra
        apply this
        rw [List.mem_append]
        apply Or.inl
        exact contra

end

variable [DecidableEq sig.P] [DecidableEq sig.C]

mutual

  theorem PreGroundTerm.rename_constants_apart_preserves_ruleId_validity [GetFreshRepresentant sig.C] (term : FiniteTree (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, PreGroundTerm.skolem_ruleIds_valid rl term -> PreGroundTerm.skolem_ruleIds_valid rl (PreGroundTerm.rename_constants_apart term forbidden_constants) := by
    intro rl valid
    cases term with
    | leaf _ => simp [rename_constants_apart, skolem_ruleIds_valid]
    | inner func ts =>
      simp only [rename_constants_apart, skolem_ruleIds_valid] at *
      constructor
      . exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_ruleId_validity_list; exact valid.right

  theorem PreGroundTerm.rename_constants_apart_preserves_ruleId_validity_list [GetFreshRepresentant sig.C] (terms : FiniteTreeList (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, PreGroundTerm.skolem_ruleIds_valid_list rl terms -> PreGroundTerm.skolem_ruleIds_valid_list rl (PreGroundTerm.rename_constants_apart_list terms forbidden_constants) := by
    intro rl valid
    cases terms with
    | nil => simp [rename_constants_apart_list, skolem_ruleIds_valid_list]
    | cons hd tl =>
      simp only [rename_constants_apart_list, skolem_ruleIds_valid_list] at *
      constructor
      . apply PreGroundTerm.rename_constants_apart_preserves_ruleId_validity; exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_ruleId_validity_list; exact valid.right

end

mutual

  theorem PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity [GetFreshRepresentant sig.C] (term : FiniteTree (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid rl term) -> PreGroundTerm.skolem_disjIdx_valid rl term h -> PreGroundTerm.skolem_disjIdx_valid rl (PreGroundTerm.rename_constants_apart term forbidden_constants) (PreGroundTerm.rename_constants_apart_preserves_ruleId_validity term forbidden_constants rl h) := by
    intro rl _ valid
    cases term with
    | leaf _ => simp [rename_constants_apart, skolem_disjIdx_valid]
    | inner func ts =>
      simp only [rename_constants_apart, skolem_disjIdx_valid] at *
      constructor
      . exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity_list; exact valid.right

  theorem PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity_list [GetFreshRepresentant sig.C] (terms : FiniteTreeList (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid_list rl terms) -> PreGroundTerm.skolem_disjIdx_valid_list rl terms h -> PreGroundTerm.skolem_disjIdx_valid_list rl (PreGroundTerm.rename_constants_apart_list terms forbidden_constants) (PreGroundTerm.rename_constants_apart_preserves_ruleId_validity_list terms forbidden_constants rl h) := by
    intro rl _ valid
    cases terms with
    | nil => simp [rename_constants_apart_list, skolem_disjIdx_valid_list]
    | cons hd tl =>
      simp only [rename_constants_apart_list, skolem_disjIdx_valid_list] at *
      constructor
      . apply PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity; exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity_list; exact valid.right

end

mutual

  theorem PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity [GetFreshRepresentant sig.C] (term : FiniteTree (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid rl term) -> PreGroundTerm.skolem_rule_arity_valid rl term h -> PreGroundTerm.skolem_rule_arity_valid rl (PreGroundTerm.rename_constants_apart term forbidden_constants) (PreGroundTerm.rename_constants_apart_preserves_ruleId_validity term forbidden_constants rl h) := by
    intro rl _ valid
    cases term with
    | leaf _ => simp [rename_constants_apart, skolem_rule_arity_valid]
    | inner func ts =>
      simp only [rename_constants_apart, skolem_rule_arity_valid] at *
      constructor
      . exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity_list; exact valid.right

  theorem PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity_list [GetFreshRepresentant sig.C] (terms : FiniteTreeList (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid_list rl terms) -> PreGroundTerm.skolem_rule_arity_valid_list rl terms h -> PreGroundTerm.skolem_rule_arity_valid_list rl (PreGroundTerm.rename_constants_apart_list terms forbidden_constants) (PreGroundTerm.rename_constants_apart_preserves_ruleId_validity_list terms forbidden_constants rl h) := by
    intro rl _ valid
    cases terms with
    | nil => simp [rename_constants_apart_list, skolem_rule_arity_valid_list]
    | cons hd tl =>
      simp only [rename_constants_apart_list, skolem_rule_arity_valid_list] at *
      constructor
      . apply PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity; exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity_list; exact valid.right

end

def GroundTerm.rename_constants_apart
    [GetFreshRepresentant sig.C]
    (term : GroundTerm sig)
    (forbidden_constants : List sig.C) : GroundTerm sig :=
  ⟨PreGroundTerm.rename_constants_apart term.val forbidden_constants, by
    induction term generalizing forbidden_constants with
    | const c => simp [GroundTerm.const, PreGroundTerm.rename_constants_apart, PreGroundTerm.arity_ok]
    | func f ts arity_ok ih =>
      unfold PreGroundTerm.arity_ok
      unfold PreGroundTerm.rename_constants_apart
      simp only [GroundTerm.func, Bool.and_eq_true, beq_iff_eq]
      constructor
      . have : ∀ (l : List (GroundTerm sig)), (PreGroundTerm.rename_constants_apart_list (FiniteTreeList.fromList l.unattach) forbidden_constants).toList.length = l.length := by
          intro l
          induction l generalizing forbidden_constants with
          | nil => simp only [List.unattach_nil, FiniteTreeList.fromList, PreGroundTerm.rename_constants_apart_list, FiniteTreeList.toList, List.length_nil]
          | cons hd tl ih' =>
            simp only [List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.rename_constants_apart_list, FiniteTreeList.toList, List.length_cons, ih']
        rw [this]
        exact arity_ok
      . rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]
        have : ∀ (l : List (GroundTerm sig)), (∀ e ∈ l, e ∈ ts) -> (∀ t, t ∈ (PreGroundTerm.rename_constants_apart_list (FiniteTreeList.fromList l.unattach) forbidden_constants).toList -> PreGroundTerm.arity_ok t) := by
          intro l
          induction l generalizing forbidden_constants with
          | nil => intro _ _ contra; simp [FiniteTreeList.fromList, PreGroundTerm.rename_constants_apart_list, FiniteTreeList.toList] at contra
          | cons hd tl ih' =>
            intro h t t_mem
            simp only [List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.rename_constants_apart_list, FiniteTreeList.toList, List.mem_cons] at t_mem
            cases t_mem with
            | inl t_mem => rw [t_mem]; apply ih; apply h; simp
            | inr t_mem =>
              apply ih'
              . intro e e_mem; apply h; simp [e_mem]
              . exact t_mem
        apply this ts
        simp
  ⟩

omit [DecidableEq sig.P] in theorem GroundTerm.rename_constants_apart_constants_fresh
    [GetFreshRepresentant sig.C]
    (term : GroundTerm sig)
    (forbidden_constants : List sig.C) :
    ∀ c, c ∈ (term.rename_constants_apart forbidden_constants).constants -> c ∉ forbidden_constants := by
  intro c c_mem
  apply PreGroundTerm.rename_constants_apart_leaves_fresh
  exact c_mem

theorem GroundTerm.rename_constants_apart_preserves_ruleId_validity [GetFreshRepresentant sig.C] (term : GroundTerm sig) (forbidden_constants : List sig.C) :
    ∀ rl, GroundTerm.skolem_ruleIds_valid rl term -> GroundTerm.skolem_ruleIds_valid rl (GroundTerm.rename_constants_apart term forbidden_constants) := by
  intro rl valid
  simp only [rename_constants_apart, skolem_ruleIds_valid] at *
  apply PreGroundTerm.rename_constants_apart_preserves_ruleId_validity
  exact valid

theorem GroundTerm.rename_constants_apart_preserves_disjIdx_validity [GetFreshRepresentant sig.C] (term : GroundTerm sig) (forbidden_constants : List sig.C) :
    ∀ rl, (h : GroundTerm.skolem_ruleIds_valid rl term) -> GroundTerm.skolem_disjIdx_valid rl term h -> GroundTerm.skolem_disjIdx_valid rl (GroundTerm.rename_constants_apart term forbidden_constants) (GroundTerm.rename_constants_apart_preserves_ruleId_validity term forbidden_constants rl h) := by
  intro rl _ valid
  simp only [rename_constants_apart, skolem_ruleIds_valid] at *
  apply PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity
  exact valid

theorem GroundTerm.rename_constants_apart_preserves_rule_arity_validity [GetFreshRepresentant sig.C] (term : GroundTerm sig) (forbidden_constants : List sig.C) :
    ∀ rl, (h : GroundTerm.skolem_ruleIds_valid rl term) -> GroundTerm.skolem_rule_arity_valid rl term h -> GroundTerm.skolem_rule_arity_valid rl (GroundTerm.rename_constants_apart term forbidden_constants) (GroundTerm.rename_constants_apart_preserves_ruleId_validity term forbidden_constants rl h) := by
  intro rl _ valid
  simp only [rename_constants_apart, skolem_ruleIds_valid] at *
  apply PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity
  exact valid

def GroundSubstitution.rename_constants_apart_for_vars [GetFreshRepresentant sig.C] (subs : GroundSubstitution sig) (forbidden_constants : List sig.C) : List sig.V -> GroundSubstitution sig
| .nil => subs
| .cons hd tl =>
  let renamed_term_for_hd := (subs hd).rename_constants_apart forbidden_constants
  let new_forbidden := forbidden_constants ++ renamed_term_for_hd.constants
  fun v => if v = hd then renamed_term_for_hd else
    subs.rename_constants_apart_for_vars new_forbidden tl v

omit [DecidableEq sig.P] in theorem GroundSubstitution.rename_constants_apart_for_vars_constants_fresh
    [GetFreshRepresentant sig.C]
    (subs : GroundSubstitution sig)
    (forbidden_constants : List sig.C)
    (vars : List sig.V) :
    ∀ v ∈ vars, ∀ c ∈ (subs.rename_constants_apart_for_vars forbidden_constants vars v).constants, c ∉ forbidden_constants := by
  induction vars generalizing forbidden_constants with
  | nil => intros; contradiction
  | cons hd tl ih =>
    intro v v_mem c c_mem
    cases Decidable.em (v = hd) with
    | inl v_eq_hd =>
      simp only [rename_constants_apart_for_vars, v_eq_hd, ↓reduceIte] at c_mem
      apply GroundTerm.rename_constants_apart_constants_fresh
      exact c_mem
    | inr v_neq_hd =>
      have v_mem : v ∈ tl := by cases v_mem; contradiction; assumption
      simp only [rename_constants_apart_for_vars, v_neq_hd, ↓reduceIte] at c_mem
      let new_forbidden := forbidden_constants ++ ((subs hd).rename_constants_apart forbidden_constants).constants
      specialize ih new_forbidden v v_mem c c_mem
      intro contra
      apply ih
      simp [new_forbidden, contra]

theorem GroundSubstitution.rename_constants_apart_for_vars_preserves_ruleId_validity [GetFreshRepresentant sig.C] (subs : GroundSubstitution sig) (forbidden_constants : List sig.C) (vars : List sig.V) :
    ∀ rl, ∀ v ∈ vars, (subs v).skolem_ruleIds_valid rl -> (subs.rename_constants_apart_for_vars forbidden_constants vars v).skolem_ruleIds_valid rl := by
  intro rl v
  induction vars generalizing forbidden_constants with
  | nil => intros; contradiction
  | cons hd tl ih =>
    intro v_mem
    rw [List.mem_cons] at v_mem
    cases Decidable.em (v = hd) with
    | inl v_eq =>
      simp only [rename_constants_apart_for_vars, v_eq, ↓reduceIte]
      apply GroundTerm.rename_constants_apart_preserves_ruleId_validity
    | inr v_neq =>
      simp only [rename_constants_apart_for_vars, v_neq, ↓reduceIte]
      apply ih
      cases v_mem with
      | inl v_mem => contradiction
      | inr v_mem => exact v_mem

theorem GroundSubstitution.rename_constants_apart_for_vars_preserves_disjIdx_validity [GetFreshRepresentant sig.C] (subs : GroundSubstitution sig) (forbidden_constants : List sig.C) (vars : List sig.V) :
    ∀ rl, ∀ v, (v_mem : v ∈ vars) -> (h : (subs v).skolem_ruleIds_valid rl) -> (subs v).skolem_disjIdx_valid rl h -> (subs.rename_constants_apart_for_vars forbidden_constants vars v).skolem_disjIdx_valid rl (subs.rename_constants_apart_for_vars_preserves_ruleId_validity forbidden_constants vars rl v v_mem h) := by
  intro rl v
  induction vars generalizing forbidden_constants with
  | nil => intros; contradiction
  | cons hd tl ih =>
    intro v_mem
    rw [List.mem_cons] at v_mem
    cases Decidable.em (v = hd) with
    | inl v_eq =>
      simp only [rename_constants_apart_for_vars, v_eq, ↓reduceIte]
      apply GroundTerm.rename_constants_apart_preserves_disjIdx_validity
    | inr v_neq =>
      simp only [rename_constants_apart_for_vars, v_neq, ↓reduceIte]
      apply ih
      cases v_mem with
      | inl v_mem => contradiction
      | inr v_mem => exact v_mem

theorem GroundSubstitution.rename_constants_apart_for_vars_preserves_rule_arity_validity [GetFreshRepresentant sig.C] (subs : GroundSubstitution sig) (forbidden_constants : List sig.C) (vars : List sig.V) :
    ∀ rl, ∀ v, (v_mem : v ∈ vars) -> (h : (subs v).skolem_ruleIds_valid rl) -> (subs v).skolem_rule_arity_valid rl h -> (subs.rename_constants_apart_for_vars forbidden_constants vars v).skolem_rule_arity_valid rl (subs.rename_constants_apart_for_vars_preserves_ruleId_validity forbidden_constants vars rl v v_mem h) := by
  intro rl v
  induction vars generalizing forbidden_constants with
  | nil => intros; contradiction
  | cons hd tl ih =>
    intro v_mem
    rw [List.mem_cons] at v_mem
    cases Decidable.em (v = hd) with
    | inl v_eq =>
      simp only [rename_constants_apart_for_vars, v_eq, ↓reduceIte]
      apply GroundTerm.rename_constants_apart_preserves_rule_arity_validity
    | inr v_neq =>
      simp only [rename_constants_apart_for_vars, v_neq, ↓reduceIte]
      apply ih
      cases v_mem with
      | inl v_mem => contradiction
      | inr v_mem => exact v_mem


def PreTrigger.rename_constants_apart [GetFreshRepresentant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) : PreTrigger sig :=
  ⟨trg.rule, trg.subs.rename_constants_apart_for_vars forbidden_constants trg.rule.body.vars.eraseDupsKeepRight⟩

theorem PreTrigger.rename_constants_apart_preserves_ruleId_validity [GetFreshRepresentant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) :
    ∀ rl, PreTrigger.skolem_ruleIds_valid rl trg -> PreTrigger.skolem_ruleIds_valid rl (PreTrigger.rename_constants_apart trg forbidden_constants) := by
  intro rl valid
  unfold skolem_ruleIds_valid at *
  intro t t_mem
  rw [mem_terms_mapped_body_iff] at t_mem
  cases t_mem with
  | inl t_mem =>
    rcases t_mem with ⟨c, c_mem, t_eq⟩
    rw [← t_eq]
    apply GroundTerm.skolem_ruleIds_valid_const
  | inr t_mem =>
    rcases t_mem with ⟨v, v_mem, t_eq⟩
    rw [← t_eq]
    apply trg.subs.rename_constants_apart_for_vars_preserves_ruleId_validity forbidden_constants trg.rule.body.vars.eraseDupsKeepRight rl v
    . rw [List.mem_eraseDupsKeepRight]; exact v_mem
    . apply valid
      rw [mem_terms_mapped_body_iff]
      apply Or.inr
      exists v

theorem PreTrigger.rename_constants_apart_preserves_disjIdx_validity [GetFreshRepresentant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) :
    ∀ rl, (h : PreTrigger.skolem_ruleIds_valid rl trg) -> PreTrigger.skolem_disjIdx_valid rl trg h -> PreTrigger.skolem_disjIdx_valid rl (PreTrigger.rename_constants_apart trg forbidden_constants) (PreTrigger.rename_constants_apart_preserves_ruleId_validity trg forbidden_constants rl h) := by
  intro rl h valid
  unfold skolem_disjIdx_valid at *
  intro t t_mem
  rw [mem_terms_mapped_body_iff] at t_mem
  cases t_mem with
  | inl t_mem =>
    rcases t_mem with ⟨c, c_mem, t_eq⟩
    simp only [← t_eq]
    apply GroundTerm.skolem_disjIdx_valid_const
  | inr t_mem =>
    rcases t_mem with ⟨v, v_mem, t_eq⟩
    simp only [← t_eq]
    apply trg.subs.rename_constants_apart_for_vars_preserves_disjIdx_validity forbidden_constants trg.rule.body.vars.eraseDupsKeepRight rl v
    . rw [List.mem_eraseDupsKeepRight]; exact v_mem
    . apply valid
      rw [mem_terms_mapped_body_iff]
      apply Or.inr
      exists v

theorem PreTrigger.rename_constants_apart_preserves_rule_arity_validity [GetFreshRepresentant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) :
    ∀ rl, (h : PreTrigger.skolem_ruleIds_valid rl trg) -> PreTrigger.skolem_rule_arity_valid rl trg h -> PreTrigger.skolem_rule_arity_valid rl (PreTrigger.rename_constants_apart trg forbidden_constants) (PreTrigger.rename_constants_apart_preserves_ruleId_validity trg forbidden_constants rl h) := by
  intro rl h valid
  unfold skolem_rule_arity_valid at *
  intro t t_mem
  rw [mem_terms_mapped_body_iff] at t_mem
  cases t_mem with
  | inl t_mem =>
    rcases t_mem with ⟨c, c_mem, t_eq⟩
    simp only [← t_eq]
    apply GroundTerm.skolem_rule_arity_valid_const
  | inr t_mem =>
    rcases t_mem with ⟨v, v_mem, t_eq⟩
    simp only [← t_eq]
    apply trg.subs.rename_constants_apart_for_vars_preserves_rule_arity_validity forbidden_constants trg.rule.body.vars.eraseDupsKeepRight rl v
    . rw [List.mem_eraseDupsKeepRight]; exact v_mem
    . apply valid
      rw [mem_terms_mapped_body_iff]
      apply Or.inr
      exists v

