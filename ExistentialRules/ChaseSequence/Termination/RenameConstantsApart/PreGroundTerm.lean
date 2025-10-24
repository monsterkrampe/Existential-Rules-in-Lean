import BasicLeanDatastructures.GetFreshInhabitant
import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

def PreGroundTerm.rename_constants_apart
    [GetFreshInhabitant sig.C]
    (term : PreGroundTerm sig)
    (forbidden_constants : List sig.C) : PreGroundTerm sig :=
  match term with
  | .leaf _ => .leaf (GetFreshInhabitant.fresh forbidden_constants)
  | .inner func ts => .inner func (foldl_list ts forbidden_constants)
where
  foldl_list (ts : List (PreGroundTerm sig)) (forbidden_constants : List sig.C) : List (PreGroundTerm sig) :=
    foldl_list_with_init ts forbidden_constants []
  foldl_list_with_init (ts : List (PreGroundTerm sig)) (forbidden_constants : List sig.C) (init : List (PreGroundTerm sig)) : List (PreGroundTerm sig) :=
    ts.foldl (fun acc t => acc ++ [PreGroundTerm.rename_constants_apart t (forbidden_constants ++ acc.flatMap FiniteTree.leaves)]) init

theorem PreGroundTerm.rename_constants_apart.length_foldl_list_with_init
    [GetFreshInhabitant sig.C]
    {ts : List (PreGroundTerm sig)}
    {forbidden_constants : List sig.C}
    {init : List (PreGroundTerm sig)} :
    (foldl_list_with_init ts forbidden_constants init).length = init.length + ts.length := by
  unfold foldl_list_with_init
  induction ts generalizing forbidden_constants init with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, ih]
    conv => right; rw [List.length_cons, Nat.add_comm tl.length, ← Nat.add_assoc]
    simp

theorem PreGroundTerm.rename_constants_apart.foldl_list_with_init_eq
    [GetFreshInhabitant sig.C]
    {ts : List (PreGroundTerm sig)}
    {forbidden_constants : List sig.C}
    {init : List (PreGroundTerm sig)} :
    foldl_list_with_init ts forbidden_constants init = init ++ foldl_list_with_init ts (forbidden_constants ++ init.flatMap FiniteTree.leaves) [] := by
  unfold foldl_list_with_init
  induction ts generalizing forbidden_constants init with
  | nil => simp
  | cons hd tl ih =>
    conv => left; rw [List.foldl_cons, ih]
    conv => right; rw [List.foldl_cons, ih]
    simp

theorem PreGroundTerm.rename_constants_apart.length_foldl_list
    [GetFreshInhabitant sig.C]
    {ts : List (PreGroundTerm sig)}
    {forbidden_constants : List sig.C} :
    (foldl_list ts forbidden_constants).length = ts.length := by
  unfold foldl_list
  rw [length_foldl_list_with_init]
  simp

theorem PreGroundTerm.rename_constants_apart.foldl_list_cons
    [GetFreshInhabitant sig.C]
    {t : PreGroundTerm sig}
    {ts : List (PreGroundTerm sig)}
    {forbidden_constants : List sig.C} :
    foldl_list (t :: ts) forbidden_constants = (rename_constants_apart t forbidden_constants) :: foldl_list ts (forbidden_constants ++ (rename_constants_apart t forbidden_constants).leaves) := by
  conv => left; unfold foldl_list; unfold foldl_list_with_init
  rw [List.foldl_cons]
  rw [← rename_constants_apart.foldl_list_with_init.eq_def]
  rw [rename_constants_apart.foldl_list_with_init_eq]
  simp [rename_constants_apart.foldl_list]

theorem PreGroundTerm.rename_constants_apart.mem_foldl_list_implies
    [GetFreshInhabitant sig.C]
    {ts : List (PreGroundTerm sig)}
    {forbidden_constants : List sig.C} :
    ∀ {t}, t ∈ foldl_list ts forbidden_constants -> ∃ t' new_consts, t' ∈ ts ∧ t = rename_constants_apart t' (forbidden_constants ++ new_consts) := by
  intro t t_mem
  induction ts generalizing forbidden_constants with
  | nil => simp [rename_constants_apart.foldl_list, rename_constants_apart.foldl_list_with_init] at t_mem
  | cons hd tl ih =>
    rw [foldl_list_cons, List.mem_cons] at t_mem
    cases t_mem with
    | inl t_mem => exists hd, []; simp [t_mem]
    | inr t_mem =>
      rcases ih t_mem with ⟨t', new_consts, ih⟩
      exists t', (hd.rename_constants_apart forbidden_constants).leaves ++ new_consts
      simp [ih]

theorem PreGroundTerm.rename_constants_apart_leaves_fresh
    [GetFreshInhabitant sig.C]
    {term : FiniteTree (SkolemFS sig) sig.C}
    {forbidden_constants : List sig.C} :
    ∀ {e}, e ∈ (PreGroundTerm.rename_constants_apart term forbidden_constants).leaves -> e ∉ forbidden_constants := by
  induction term generalizing forbidden_constants with
  | leaf c =>
    intro e e_mem
    simp only [rename_constants_apart, FiniteTree.leaves, List.mem_singleton] at e_mem
    have prop := (GetFreshInhabitant.fresh forbidden_constants).property
    rw [e_mem]
    exact prop
  | inner func ts ih =>
    intro e e_mem
    simp only [FiniteTree.leaves, rename_constants_apart] at e_mem
    rw [List.mem_flatMap] at e_mem
    rcases e_mem with ⟨t, t_mem, e_mem⟩
    rcases rename_constants_apart.mem_foldl_list_implies t_mem with ⟨t', new_consts, t'_mem, t_eq⟩
    rw [t_eq] at e_mem
    intro contra
    apply ih t' t'_mem e_mem
    simp [contra]

variable [DecidableEq sig.P]

theorem PreGroundTerm.rename_constants_apart_preserves_ruleId_validity
    [GetFreshInhabitant sig.C]
    {term : FiniteTree (SkolemFS sig) sig.C}
    {forbidden_constants : List sig.C} :
    ∀ {rl}, PreGroundTerm.skolem_ruleIds_valid rl term -> PreGroundTerm.skolem_ruleIds_valid rl (PreGroundTerm.rename_constants_apart term forbidden_constants) := by
  intro rl valid
  induction term generalizing forbidden_constants with
  | leaf _ => simp [rename_constants_apart, skolem_ruleIds_valid]
  | inner func ts ih =>
    simp only [rename_constants_apart, skolem_ruleIds_valid] at *
    constructor
    . exact valid.left
    . intro t t_mem
      rcases rename_constants_apart.mem_foldl_list_implies t_mem with ⟨t', new_consts, t'_mem, t_eq⟩
      rw [t_eq]
      apply ih
      . exact t'_mem
      . apply valid.right; exact t'_mem

theorem PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity
    [GetFreshInhabitant sig.C]
    {term : FiniteTree (SkolemFS sig) sig.C}
    {forbidden_constants : List sig.C} :
    ∀ {rl}, (h : PreGroundTerm.skolem_ruleIds_valid rl term) -> PreGroundTerm.skolem_disjIdx_valid rl term h -> PreGroundTerm.skolem_disjIdx_valid rl (PreGroundTerm.rename_constants_apart term forbidden_constants) (PreGroundTerm.rename_constants_apart_preserves_ruleId_validity h) := by
  intro rl _ valid
  induction term generalizing forbidden_constants with
  | leaf _ => simp [rename_constants_apart, skolem_disjIdx_valid]
  | inner func ts ih =>
    simp only [rename_constants_apart, skolem_disjIdx_valid] at *
    constructor
    . exact valid.left
    . intro t t_mem
      rcases rename_constants_apart.mem_foldl_list_implies t_mem with ⟨t', new_consts, t'_mem, t_eq⟩
      simp only [t_eq]
      apply ih
      . exact t'_mem
      . apply valid.right; exact t'_mem

theorem PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity
    [GetFreshInhabitant sig.C]
    {term : FiniteTree (SkolemFS sig) sig.C}
    {forbidden_constants : List sig.C} :
    ∀ {rl}, (h : PreGroundTerm.skolem_ruleIds_valid rl term) -> PreGroundTerm.skolem_rule_arity_valid rl term h -> PreGroundTerm.skolem_rule_arity_valid rl (PreGroundTerm.rename_constants_apart term forbidden_constants) (PreGroundTerm.rename_constants_apart_preserves_ruleId_validity h) := by
  intro rl _ valid
  induction term generalizing forbidden_constants with
  | leaf _ => simp [rename_constants_apart, skolem_rule_arity_valid]
  | inner func ts ih =>
    simp only [rename_constants_apart, skolem_rule_arity_valid] at *
    constructor
    . exact valid.left
    . intro t t_mem
      rcases rename_constants_apart.mem_foldl_list_implies t_mem with ⟨t', new_consts, t'_mem, t_eq⟩
      simp only [t_eq]
      apply ih
      . exact t'_mem
      . apply valid.right; exact t'_mem

