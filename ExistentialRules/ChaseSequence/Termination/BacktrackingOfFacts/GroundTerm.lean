/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts.PreGroundTerm

/-!
# Backtracking Facts for a GroundTerm

We mainly lift the machinery around `PreGroundTerm.backtrackFacts` to `GroundTerm`.
We spare the doc comments on the individual definitions and theorems.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace GroundTerm

@[expose]
def backtrackTrigger
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (term : GroundTerm sig)
    (term_is_func : ∃ func ts arity_ok, term = GroundTerm.func func ts arity_ok)
    (forbidden_constants : List sig.C) : PreTrigger sig :=
  PreGroundTerm.backtrackTrigger term.val (by rcases term_is_func with ⟨func, ts, _, eq⟩; exists func, ts.unattach; rw [eq]; rfl) term.property forbidden_constants

  @[expose]
def backtrackFacts
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (term : GroundTerm sig)
    (forbidden_constants : List sig.C) : (List (Fact sig)) × (List sig.C) :=
  PreGroundTerm.backtrackFacts term.val term.property forbidden_constants

@[expose]
def backtrackFacts_list
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (terms : List (GroundTerm sig))
    (forbidden_constants : List sig.C) : (List (Fact sig)) × (List sig.C) :=
  match terms with
  | .nil => ([], [])
  | .cons hd tl =>
    have hd_mem : hd ∈ hd :: tl := by simp
    let result_for_hd := hd.backtrackFacts forbidden_constants
    let recursive_result := backtrackFacts_list tl (forbidden_constants ++ result_for_hd.snd)
    (result_for_hd.fst ++ recursive_result.fst, result_for_hd.snd ++ recursive_result.snd)

theorem backtrackFacts_list_eq
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    {terms : List (GroundTerm sig)}
    {forbidden_constants : List sig.C} :
    backtrackFacts_list terms forbidden_constants =
      PreGroundTerm.backtrackFacts_list terms.unattach (by simp only [List.mem_unattach]; rintro _ ⟨h, _⟩; exact h) forbidden_constants := by
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
    {term : GroundTerm sig}
    {forbidden_constants : List sig.C} :
    ∀ c ∈ (GroundTerm.backtrackFacts term forbidden_constants).snd, c ∉ forbidden_constants := by
  unfold backtrackFacts
  exact PreGroundTerm.backtrackFacts_fresh_constants_not_forbidden

theorem backtrackFacts_list_fresh_constants_not_forbidden
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    {terms : List (GroundTerm sig)}
    {forbidden_constants : List sig.C} :
    ∀ c ∈ (GroundTerm.backtrackFacts_list terms forbidden_constants).snd, c ∉ forbidden_constants := by
  rw [backtrackFacts_list_eq]
  exact PreGroundTerm.backtrackFacts_list_fresh_constants_not_forbidden

theorem backtrackFacts_constants_in_rules_or_term_or_fresh
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    {term : GroundTerm sig}
    {forbidden_constants : List sig.C} :
    ∀ f ∈ (GroundTerm.backtrackFacts term forbidden_constants).fst,
    ∀ c ∈ f.constants,
      c ∈ (term.rules.flatMap Rule.constants) ∨ c ∈ term.constants ∨ c ∈ (GroundTerm.backtrackFacts term forbidden_constants).snd := by
  unfold backtrackFacts GroundTerm.rules
  rw [List.flatMap_map]
  exact PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh

theorem backtrackFacts_list_constants_in_rules_or_term_or_fresh
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    {terms : List (GroundTerm sig)}
    {forbidden_constants : List sig.C} :
    ∀ f ∈ (GroundTerm.backtrackFacts_list terms forbidden_constants).fst,
    ∀ c ∈ f.constants,
      c ∈ ((terms.flatMap GroundTerm.rules).flatMap (Rule.constants)) ∨ c ∈ terms.flatMap GroundTerm.constants ∨ c ∈ (GroundTerm.backtrackFacts_list terms forbidden_constants).snd := by
  rw [backtrackFacts_list_eq]
  have : terms.flatMap GroundTerm.constants = terms.unattach.flatMap FiniteTree.leaves := by rw [List.flatMap_unattach]; rfl
  rw [this]
  have : terms.flatMap GroundTerm.rules = (terms.unattach.flatMap FiniteTree.innerLabels).map SkolemFS.rule := by rw [List.flatMap_unattach, List.map_flatMap]; rfl
  rw [this, List.flatMap_map]
  exact PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh

end GroundTerm

