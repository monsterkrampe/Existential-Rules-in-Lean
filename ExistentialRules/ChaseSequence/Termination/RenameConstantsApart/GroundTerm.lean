import ExistentialRules.ChaseSequence.Termination.RenameConstantsApart.PreGroundTerm

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

def GroundTerm.rename_constants_apart
    [GetFreshInhabitant sig.C]
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
      . rw [PreGroundTerm.rename_constants_apart.length_foldl_list, List.length_unattach]; exact arity_ok
      . rw [List.all_eq_true]
        intro ⟨t, t_mem⟩ _
        simp only
        rcases PreGroundTerm.rename_constants_apart.mem_foldl_list_implies t_mem with ⟨t', new_consts, t'_mem, t_eq⟩
        rw [List.mem_unattach] at t'_mem
        rcases t'_mem with ⟨h, t'_mem⟩
        rw [t_eq]
        apply ih ⟨t', h⟩
        exact t'_mem
  ⟩

theorem GroundTerm.rename_constants_apart_constants_fresh
    [GetFreshInhabitant sig.C]
    (term : GroundTerm sig)
    (forbidden_constants : List sig.C) :
    ∀ c, c ∈ (term.rename_constants_apart forbidden_constants).constants -> c ∉ forbidden_constants := by
  intro c c_mem
  apply PreGroundTerm.rename_constants_apart_leaves_fresh
  exact c_mem

variable [DecidableEq sig.P]

theorem GroundTerm.rename_constants_apart_preserves_ruleId_validity [GetFreshInhabitant sig.C] (term : GroundTerm sig) (forbidden_constants : List sig.C) :
    ∀ rl, GroundTerm.skolem_ruleIds_valid rl term -> GroundTerm.skolem_ruleIds_valid rl (GroundTerm.rename_constants_apart term forbidden_constants) := by
  intro rl valid
  simp only [rename_constants_apart, skolem_ruleIds_valid] at *
  apply PreGroundTerm.rename_constants_apart_preserves_ruleId_validity
  exact valid

theorem GroundTerm.rename_constants_apart_preserves_disjIdx_validity [GetFreshInhabitant sig.C] (term : GroundTerm sig) (forbidden_constants : List sig.C) :
    ∀ rl, (h : GroundTerm.skolem_ruleIds_valid rl term) -> GroundTerm.skolem_disjIdx_valid rl term h -> GroundTerm.skolem_disjIdx_valid rl (GroundTerm.rename_constants_apart term forbidden_constants) (GroundTerm.rename_constants_apart_preserves_ruleId_validity term forbidden_constants rl h) := by
  intro rl _ valid
  simp only [rename_constants_apart] at *
  apply PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity
  exact valid

theorem GroundTerm.rename_constants_apart_preserves_rule_arity_validity [GetFreshInhabitant sig.C] (term : GroundTerm sig) (forbidden_constants : List sig.C) :
    ∀ rl, (h : GroundTerm.skolem_ruleIds_valid rl term) -> GroundTerm.skolem_rule_arity_valid rl term h -> GroundTerm.skolem_rule_arity_valid rl (GroundTerm.rename_constants_apart term forbidden_constants) (GroundTerm.rename_constants_apart_preserves_ruleId_validity term forbidden_constants rl h) := by
  intro rl _ valid
  simp only [rename_constants_apart] at *
  apply PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity
  exact valid

