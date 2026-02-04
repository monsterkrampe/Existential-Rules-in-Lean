import BasicLeanDatastructures.GetFreshInhabitant
import ExistentialRules.ChaseSequence.Termination.Basic

/-!
# Backtracking Facts for a Trigger

For DMFA/RMFA-like conditions, we need to be able to backtrack which facts are necessarily present when a trigger is loaded.
This file starts with very basic auxiliary definitions for this endeavor.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace Rule

/-- For a rule, we need to be able to obtain a fresh constant for each variable that only occurs in the body. This is doen using the `GetFreshInhabitant` typeclass. -/
def fresh_consts_for_pure_body_vars [GetFreshInhabitant sig.C] (r : Rule sig) (forbidden_constants : List sig.C) :=
  GetFreshInhabitant.fresh_n forbidden_constants r.pure_body_vars.length

/-- The number of fresh constants obtained matches the number of variables. -/
theorem length_fresh_consts_for_pure_body_vars [GetFreshInhabitant sig.C] {r : Rule sig} {forbidden_constants : List sig.C} :
    (r.fresh_consts_for_pure_body_vars forbidden_constants).val.length = r.pure_body_vars.length :=
  (r.fresh_consts_for_pure_body_vars forbidden_constants).property.left

/-- For each variable, the index of the fresh constant introduced for this variable matches the index of the variable. -/
theorem fresh_consts_for_pure_body_vars_idx_retained
    [GetFreshInhabitant sig.C] {r : Rule sig} {forbidden_constants : List sig.C} {v : sig.V} {v_mem : v ∈ r.pure_body_vars} :
    (r.fresh_consts_for_pure_body_vars forbidden_constants).val.idxOf ((r.fresh_consts_for_pure_body_vars forbidden_constants).val[r.pure_body_vars.idxOf v]'(by rw [(r.fresh_consts_for_pure_body_vars forbidden_constants).property.left, List.idxOf_lt_length_iff]; exact v_mem)) = r.pure_body_vars.idxOf v := by
  rw [List.idxOf_getElem]
  exact (r.fresh_consts_for_pure_body_vars forbidden_constants).property.right.left

/-- Getting the variable at the index of the corresponding fresh constant returns the original variable. -/
theorem fresh_consts_pure_body_vars_roundtrip
    [GetFreshInhabitant sig.C] {r : Rule sig} {forbidden_constants : List sig.C} {v : sig.V} {v_mem : v ∈ r.pure_body_vars} :
    r.pure_body_vars[(r.fresh_consts_for_pure_body_vars forbidden_constants).val.idxOf ((r.fresh_consts_for_pure_body_vars forbidden_constants).val[r.pure_body_vars.idxOf v]'(by rw [(r.fresh_consts_for_pure_body_vars forbidden_constants).property.left, List.idxOf_lt_length_iff]; exact v_mem))]'(by rw [fresh_consts_for_pure_body_vars_idx_retained, List.idxOf_lt_length_iff]; exact v_mem; exact v_mem) = v := by
  rw [List.getElem_eq_getElem_of_idx_eq]
  . rw [List.getElem_idxOf_of_mem]
    exact v_mem
  . apply fresh_consts_for_pure_body_vars_idx_retained
    exact v_mem

end Rule

namespace SkolemFS

/-- The rule id of a `SkolemFS` (Skolem Function Symbol) is valid if there is a rule with this id. -/
def ruleId_valid (sfs : SkolemFS sig) (rl : RuleList sig) : Prop :=
  ∃ r ∈ rl.rules, r.id = sfs.ruleId

/-- The disjunct index of a `SkolemFS` (Skolem Function Symbol) if the rule corresponding the its rule id indeed has enough head disjuncts. -/
def disjunctIndex_valid (sfs : SkolemFS sig) (rl : RuleList sig) (ruleId_valid : sfs.ruleId_valid rl) : Prop :=
  sfs.disjunctIndex < (rl.get_by_id sfs.ruleId ruleId_valid).head.length

/-- The arity of a `SkolemFS` (Skolem Function Symbol) is valid if it matches the frontier length of the rule corresponding to its rule id. -/
def arity_valid (sfs : SkolemFS sig) (rl : RuleList sig) (ruleId_valid : sfs.ruleId_valid rl) : Prop :=
  sfs.arity = (rl.get_by_id sfs.ruleId ruleId_valid).frontier.length

end SkolemFS

