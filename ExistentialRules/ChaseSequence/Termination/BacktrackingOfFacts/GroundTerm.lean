import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts.PreGroundTerm

/-!
# Backtracking Facts for a GroundTerm

We mainly lift the machinery around `PreGroundTerm.backtrackFacts` to `GroundTerm`.
We spare the doc comments on the individual definitions and theorems.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundTerm

def skolem_ruleIds_valid (rl : RuleList sig) (term : GroundTerm sig) : Prop := PreGroundTerm.skolem_ruleIds_valid rl term.val
def skolem_disjIdx_valid (rl : RuleList sig) (term : GroundTerm sig) (term_ruleIds_valid : term.skolem_ruleIds_valid rl) : Prop :=
  PreGroundTerm.skolem_disjIdx_valid rl term.val term_ruleIds_valid
def skolem_rule_arity_valid (rl : RuleList sig) (term : GroundTerm sig) (term_ruleIds_valid : term.skolem_ruleIds_valid rl) : Prop :=
  PreGroundTerm.skolem_rule_arity_valid rl term.val term_ruleIds_valid

theorem skolem_ruleIds_valid_const (rl : RuleList sig) (c : sig.C) : (GroundTerm.const c).skolem_ruleIds_valid rl := by
  simp [skolem_ruleIds_valid, PreGroundTerm.skolem_ruleIds_valid, GroundTerm.const]
theorem skolem_disjIdx_valid_const (rl : RuleList sig) (c : sig.C) : (GroundTerm.const c).skolem_disjIdx_valid rl (skolem_ruleIds_valid_const rl c) := by
  simp [skolem_disjIdx_valid, PreGroundTerm.skolem_disjIdx_valid, GroundTerm.const]
theorem skolem_rule_arity_valid_const (rl : RuleList sig) (c : sig.C) : (GroundTerm.const c).skolem_rule_arity_valid rl (skolem_ruleIds_valid_const rl c) := by
  simp [skolem_rule_arity_valid, PreGroundTerm.skolem_rule_arity_valid, GroundTerm.const]

def backtrackTrigger
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (rl : RuleList sig)
    (term : GroundTerm sig)
    (term_is_func : ∃ func ts arity_ok, term = GroundTerm.func func ts arity_ok)
    (term_ruleIds_valid : term.skolem_ruleIds_valid rl)
    (term_rule_arity_valid : term.skolem_rule_arity_valid rl term_ruleIds_valid)
    (forbidden_constants : List sig.C) : PreTrigger sig :=
  PreGroundTerm.backtrackTrigger rl term.val (by rcases term_is_func with ⟨func, ts, _, eq⟩; exists func, ts.unattach; rw [eq]; rfl) term.property term_ruleIds_valid term_rule_arity_valid forbidden_constants

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

theorem backtrackFacts_list_eq
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    {rl : RuleList sig}
    {terms : List (GroundTerm sig)}
    {terms_ruleIds_valid : ∀ t ∈ terms, t.skolem_ruleIds_valid rl}
    {terms_disjIdx_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_disjIdx_valid rl (terms_ruleIds_valid t mem)}
    {terms_rule_arity_valid : ∀ t, (mem : t ∈ terms) -> t.skolem_rule_arity_valid rl (terms_ruleIds_valid t mem)}
    {forbidden_constants : List sig.C} :
    backtrackFacts_list rl terms terms_ruleIds_valid terms_disjIdx_valid terms_rule_arity_valid forbidden_constants =
      PreGroundTerm.backtrackFacts_list rl terms.unattach (by simp only [List.mem_unattach]; rintro _ ⟨h, _⟩; exact h) (by simp only [List.mem_unattach]; rintro _ ⟨_, t_mem⟩; exact terms_ruleIds_valid _ t_mem) (by simp only [List.mem_unattach]; rintro _ ⟨_, t_mem⟩; exact terms_disjIdx_valid _ t_mem) (by simp only [List.mem_unattach]; rintro _ ⟨_, t_mem⟩; exact terms_rule_arity_valid _ t_mem) forbidden_constants := by
  induction terms generalizing forbidden_constants with
  | nil => simp [backtrackFacts_list, List.unattach_nil, PreGroundTerm.backtrackFacts_list_nil]
  | cons hd tl ih =>
    unfold backtrackFacts_list
    simp only [List.unattach_cons]
    rw [PreGroundTerm.backtrackFacts_list_cons]
    rw [ih]
    rfl

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
  unfold backtrackFacts
  exact PreGroundTerm.backtrackFacts_fresh_constants_not_forbidden

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
  rw [backtrackFacts_list_eq]
  exact PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden

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
  unfold backtrackFacts
  exact PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh

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
  have : terms.flatMap GroundTerm.constants = terms.unattach.flatMap FiniteTree.leaves := by rw [List.flatMap_unattach]; rfl
  rw [backtrackFacts_list_eq, this]
  exact PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh

end GroundTerm

