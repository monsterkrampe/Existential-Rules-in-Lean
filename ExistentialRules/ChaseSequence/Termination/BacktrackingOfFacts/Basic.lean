import BasicLeanDatastructures.GetFreshInhabitant
import ExistentialRules.ChaseSequence.Termination.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

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

def SkolemFS.ruleId_valid (sfs : SkolemFS sig) (rl : RuleList sig) : Prop :=
  ∃ r ∈ rl.rules, r.id = sfs.ruleId

def SkolemFS.disjunctIndex_valid (sfs : SkolemFS sig) (rl : RuleList sig) (ruleId_valid : sfs.ruleId_valid rl) : Prop :=
  sfs.disjunctIndex < (rl.get_by_id sfs.ruleId ruleId_valid).head.length

def SkolemFS.arity_valid (sfs : SkolemFS sig) (rl : RuleList sig) (ruleId_valid : sfs.ruleId_valid rl) : Prop :=
  sfs.arity = (rl.get_by_id sfs.ruleId ruleId_valid).frontier.length

