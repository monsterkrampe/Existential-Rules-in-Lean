/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts.GroundTerm

/-!
# Backtracking Facts for a PreTrigger

We mainly lift the machinery around `PreGroundTerm.backtrackFacts` to `PreTrigger`.
The interesting parts are `PreTrigger.backtrackFacts` and `PreTrigger.backtrackFacts_eq_of_strong_equiv`.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace PreTrigger

@[expose]
def backtrackTrigger_for_functional_term
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (trg : PreTrigger sig)
    (forbidden_constants : List sig.C)
    (i : Nat) (lt : i < trg.rule.head.length)
    (v : sig.V) (v_exis : v ∈ trg.rule.existential_vars_for_head_disjunct i lt) :
    PreTrigger sig :=
  ((trg.functional_term_for_var i lt v v_exis).backtrackTrigger (by
    cases eq : trg.functional_term_for_var i lt v v_exis with
    | const _ => simp [functional_term_for_var, GroundTerm.func, GroundTerm.const] at eq
    | func func ts arity_ok => exists func, ts, arity_ok
  ) forbidden_constants)

theorem backtrackTrigger_for_functional_term_equiv
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (trg : PreTrigger sig)
    (forbidden_constants : List sig.C) :
    ∀ i lt v v_exis, (trg.backtrackTrigger_for_functional_term forbidden_constants i lt v v_exis).equiv trg := by
  intro i lt v v_exis
  simp only [backtrackTrigger_for_functional_term, PreTrigger.functional_term_for_var, GroundTerm.backtrackTrigger, GroundTerm.func, PreGroundTerm.backtrackTrigger]
  simp only [PreTrigger.equiv, true_and]
  intro u u_mem
  simp only [u_mem, ↓reduceDIte, PreTrigger.mapped_frontier]
  rw [Subtype.mk.injEq]
  rw [List.getElem_unattach, List.getElem_map]
  rw [List.getElem_idxOf_of_mem]
  exact u_mem

/-- When backtracking a trigger, the "affected" rules are either the rule of the trigger itself or a rule in one of the Skolem terms. -/
@[expose]
def affected_rules_for_backtracking (trg : PreTrigger sig) : (List (Rule sig)) :=
  trg.rule :: (trg.mapped_body.flatMap GeneralizedAtom.terms).flatMap GroundTerm.rules

/-- The affected rules of two `PreTrigger`s are the same if they are strongly equivalent, i.e. they have the same rule and the same mapped body. -/
theorem affected_rules_for_backtracking_eq_of_strong_equiv
    (trg trg2 : PreTrigger sig)
    (strong_equiv : trg.strong_equiv trg2) :
    trg.affected_rules_for_backtracking = trg2.affected_rules_for_backtracking := by
  unfold affected_rules_for_backtracking
  simp only [PreTrigger.mapped_body_eq_of_strong_equiv strong_equiv, strong_equiv.left]

/-- When backtracking a trigger, we forbid the following from being used a fresh constants: all constants that occur in the mapped body or constants in `affected_rules_for_backtracking`.  -/
@[expose]
def initial_forbidden_constants_for_backtracking (trg : PreTrigger sig) : (List sig.C) :=
  trg.mapped_body.flatMap Fact.constants ++ trg.affected_rules_for_backtracking.flatMap Rule.constants

/-- The backtracking of a `PreTrigger` consists of its mapped body and the backtrackings of all `GroundTerm`s that occur in its mapped body. -/
@[expose]
def backtrackFacts
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (trg : PreTrigger sig) : (List (Fact sig)) × (List sig.C) :=
  let backtrack_result := GroundTerm.backtrackFacts_list (trg.mapped_body.flatMap GeneralizedAtom.terms) trg.initial_forbidden_constants_for_backtracking
  (trg.mapped_body ++ backtrack_result.fst, backtrack_result.snd)

/-- The backtracking of two `PreTrigger`s is the same if they are strongly equivalent, i.e. they have the same rule and the same mapped body. -/
theorem backtrackFacts_eq_of_strong_equiv
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (trg trg2 : PreTrigger sig)
    (strong_equiv : trg.strong_equiv trg2) :
    trg.backtrackFacts = trg2.backtrackFacts := by
  unfold backtrackFacts
  simp only [PreTrigger.mapped_body_eq_of_strong_equiv strong_equiv, initial_forbidden_constants_for_backtracking, affected_rules_for_backtracking_eq_of_strong_equiv _ _ strong_equiv]

end PreTrigger

