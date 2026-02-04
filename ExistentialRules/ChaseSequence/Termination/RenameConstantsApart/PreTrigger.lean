import ExistentialRules.ChaseSequence.Termination.RenameConstantsApart.GroundTerm

/-!
# Renaming Constants apart in a GroundSubstitution and PreTrigger

We lift the `PreGroundTerm.rename_constants_apart` functionality to `GroundSubstitution` and `PreTrigger`.
This pretty much happens in the obvious way and apart from being technical, this is not interesting.
-/

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundSubstitution

def rename_constants_apart_for_vars [GetFreshInhabitant sig.C] (subs : GroundSubstitution sig) (forbidden_constants : List sig.C) : List sig.V -> GroundSubstitution sig
| .nil => subs
| .cons hd tl =>
  let renamed_term_for_hd := (subs hd).rename_constants_apart forbidden_constants
  let new_forbidden := forbidden_constants ++ renamed_term_for_hd.constants
  fun v => if v = hd then renamed_term_for_hd else
    subs.rename_constants_apart_for_vars new_forbidden tl v

theorem rename_constants_apart_for_vars_constants_fresh
    [GetFreshInhabitant sig.C]
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

variable [DecidableEq sig.P]

theorem rename_constants_apart_for_vars_preserves_ruleId_validity [GetFreshInhabitant sig.C] (subs : GroundSubstitution sig) (forbidden_constants : List sig.C) (vars : List sig.V) :
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

theorem rename_constants_apart_for_vars_preserves_disjIdx_validity [GetFreshInhabitant sig.C] (subs : GroundSubstitution sig) (forbidden_constants : List sig.C) (vars : List sig.V) :
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

theorem rename_constants_apart_for_vars_preserves_rule_arity_validity [GetFreshInhabitant sig.C] (subs : GroundSubstitution sig) (forbidden_constants : List sig.C) (vars : List sig.V) :
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

end GroundSubstitution

namespace PreTrigger

variable [DecidableEq sig.P]

def rename_constants_apart [GetFreshInhabitant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) : PreTrigger sig :=
  ⟨trg.rule, trg.subs.rename_constants_apart_for_vars forbidden_constants trg.rule.body.vars.eraseDupsKeepRight⟩

theorem rename_constants_apart_constants_fresh
    [GetFreshInhabitant sig.C]
    (trg : PreTrigger sig)
    (forbidden_constants : List sig.C) :
    ∀ c ∈ (trg.rule.body.vars.eraseDupsKeepRight.map (trg.rename_constants_apart forbidden_constants).subs).flatMap GroundTerm.constants, c ∉ forbidden_constants := by
  intro c c_mem
  rw [List.mem_flatMap] at c_mem
  rcases c_mem with ⟨t, t_mem, c_mem⟩
  rw [List.mem_map] at t_mem
  rcases t_mem with ⟨v, v_mem, t_eq⟩
  apply trg.subs.rename_constants_apart_for_vars_constants_fresh forbidden_constants trg.rule.body.vars.eraseDupsKeepRight v v_mem
  rw [← t_eq] at c_mem
  exact c_mem

theorem rename_constants_apart_preserves_ruleId_validity [GetFreshInhabitant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) :
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

theorem rename_constants_apart_preserves_disjIdx_validity [GetFreshInhabitant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) :
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

theorem rename_constants_apart_preserves_rule_arity_validity [GetFreshInhabitant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) :
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

end PreTrigger

