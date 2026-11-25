/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.List.AllListsOfLength
import BasicLeanDatastructures.List.EraseDupsKeepRight
public import ExistentialRules.AtomsAndRules.Database
public import ExistentialRules.Triggers.RTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

open CustomBasicDatastructures

/-!
# Critical Instance

The critical instance is a special database that connects all constants from a rule set plus additional constants
in all possible ways with the predicates from the rule set.
Traditionally, the list of additional constants only consists of a single one, often called "*".
However, we allow arbitrary lists.
No trigger can ever be active on this Database, which might come in handy in proofs where such a Database needs to be found.
In a way, the critical instance also generalized all databases. With this idea in mind, it also forms the basis for MFA-like termination checks.
-/

public section

namespace RuleSet

/--
The `generalizedCriticalInstance` consists of all facts that can be build from predicates in the rule set and
constants from the ruleset plus the all the constants that we pass to this function.
-/
def generalizedCriticalInstance (rs : RuleSet sig) (finite : rs.finite) (additional_consts : List sig.C) : Database sig :=
  ⟨fun f => f.predicate ∈ rs.predicates ∧ ∀ t, t ∈ f.terms -> (t ∈ additional_consts ∨ t ∈ rs.constants), by
    -- TODO: this is very close to part of the proof of FactSet.finite_of_preds_finite_of_terms_finite
    -- but we cannot use it since our set is not Set (Fact sig) but Set (FunctionFreeFact sig)...
    -- maybe we can generalize this someday

    have preds_finite := rs.predicates_finite_of_finite finite
    rcases preds_finite with ⟨l_preds, _, preds_eq⟩
    have consts_finite := rs.constants_finite_of_finite finite
    rcases consts_finite with ⟨l_consts, _, consts_eq⟩

    exists (l_preds.flatMap (fun p =>
      (all_lists_of_length (additional_consts ++ l_consts) (sig.arity p)).attach.map (fun ⟨ts, mem⟩ =>
        {
          predicate := p
          terms := ts
          arity_ok := ((mem_all_lists_of_length (additional_consts ++ l_consts) (sig.arity p) ts).mp mem).left
        }
      )
    )).eraseDupsKeepRight

    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro f
      rw [List.mem_eraseDupsKeepRight]
      simp only [List.mem_flatMap, List.mem_map, List.mem_attach, true_and, Subtype.exists]
      constructor
      . intro h
        rcases h with ⟨pred, pred_mem, ts, ts_mem, f_eq⟩
        rw [← f_eq]
        constructor
        . rw [preds_eq] at pred_mem
          exact pred_mem
        . rw [mem_all_lists_of_length] at ts_mem
          intro t t_mem
          rw [← consts_eq]
          rw [← List.mem_append]
          apply ts_mem.right
          exact t_mem
      . intro h
        rcases h with ⟨pred_mem, ts_mem⟩
        exists f.predicate
        constructor
        . rw [preds_eq]; exact pred_mem
        . exists f.terms
          exists (by
            rw [mem_all_lists_of_length]
            constructor
            . exact f.arity_ok
            . intro t t_mem; rw [List.mem_append]; rw [consts_eq]; apply ts_mem; exact t_mem
          )
  ⟩

/--
Constants in the `generalizedCriticalInstance` are either in the additional constants or they come from the rule set.
One should think that this is not only a subset relation but an equality.
However this only holds if there is at least one predicate in the rule set that has arity at least one.
Intuitively this should be true for any interesting rule set but technically we do not demand this anywhere.
-/
theorem generalizedCriticalInstance_constants {rs : RuleSet sig} {finite : rs.finite} {additional_consts : List sig.C} :
    (rs.generalizedCriticalInstance finite additional_consts).constants.val ⊆ additional_consts.toSet ∪ rs.constants := by
  intro c; rw [Set.mem_union_iff, List.mem_toSet]
  intro ⟨f, f_mem, c_mem⟩; apply f_mem.right; exact c_mem

/-- As mentioned above, we show equality of the set of constants by demanding that a predicate of arity ≠ 0 exists in the rule set. -/
theorem generalizedCriticalInstance_constants_eq_of_predicate_with_arity_ne_zero {rs : RuleSet sig} {finite : rs.finite} {additional_consts : List sig.C} :
    (∃ p ∈ rs.predicates, sig.arity p ≠ 0) ->
    (rs.generalizedCriticalInstance finite additional_consts).constants.val = additional_consts.toSet ∪ rs.constants := by
  intro ⟨p, p_mem, arity_ne_zero⟩
  apply Set.ext
  intro c; constructor
  . apply generalizedCriticalInstance_constants
  . rw [Set.mem_union_iff, List.mem_toSet]; intro c_mem
    exists {predicate := p, terms := List.replicate (sig.arity p) c, arity_ok := by simp}
    constructor
    . constructor; exact p_mem
      intro d d_mem; rw [List.eq_of_mem_replicate d_mem]; exact c_mem
    . simp [arity_ne_zero]

/-- If the constants of a `FunctionFreeFact` all occur in the critical instance, then so does the `FunctionFreeFact`. -/
theorem functionFreeFact_mem_generalizedCriticalInstance_of_constants_mem {rs : RuleSet sig} {finite : rs.finite} {additional_consts : List sig.C} :
    ∀ f : FunctionFreeFact sig, f.predicate ∈ rs.predicates -> f.terms.toSet ⊆ additional_consts.toSet ∪ rs.constants ->
    f ∈ (rs.generalizedCriticalInstance finite additional_consts).val := by
  intro f pred_mem terms_sub
  constructor; exact pred_mem
  intro t t_mem; specialize terms_sub t; simp only [Set.mem_union_iff, List.mem_toSet] at terms_sub; exact terms_sub t_mem

/-- Every trigger using only constants from the critical instance is loaded. -/
theorem generalizedCriticalInstance_trigger_loaded
    {obs : ObsolescenceCondition} {rs : RuleSet sig} {finite : rs.finite} {additional_consts : List sig.C} :
    ∀ trg : RTrigger obs rs, FactSet.terms trg.val.mapped_body.toSet ⊆ (additional_consts.toSet ∪ rs.constants).map .const ->
    trg.val.loaded (rs.generalizedCriticalInstance finite additional_consts).toFactSet.val := by
  intro trg terms_sub
  intro f f_mem
  have terms_constants : ∀ t ∈ f.terms, ∃ c ∈ (additional_consts.toSet ∪ rs.constants), t = .const c := by
    intro t t_mem; specialize terms_sub t (by exists f)
    rw [Set.mem_map] at terms_sub; rcases terms_sub with ⟨c, c_mem, t_eq⟩
    exists c; grind
  suffices f.isFunctionFree by
    exists f.toFunctionFreeFact this; constructor
    . apply functionFreeFact_mem_generalizedCriticalInstance_of_constants_mem
      . simp only [Fact.toFunctionFreeFact]
        simp only [List.mem_toSet, PreTrigger.mapped_body, TermMapping.mem_apply_generalized_atom_list] at f_mem
        rcases f_mem with ⟨a, a_mem, f_eq⟩; rw [f_eq]
        simp only [TermMapping.apply_generalized_atom]
        exists trg.val.rule; constructor; exact trg.property
        apply List.mem_append_left
        apply List.mem_map_of_mem
        exact a_mem
      . intro c c_mem; simp only [List.mem_toSet, Fact.toFunctionFreeFact, List.map_attach_eq_pmap, List.mem_pmap] at c_mem
        rcases c_mem with ⟨t, t_mem, c_eq⟩
        rcases terms_constants t t_mem with ⟨d, d_mem, t_eq⟩
        simp only [← c_eq, t_eq, GroundTerm.toConst_const]
        exact d_mem
    . simp
  intro t t_mem; rcases terms_constants t t_mem with ⟨c, _, eq⟩; exists c

/--
No trigger is active on the critical instance if it features at least one head disjunct without existentials.
As soon as one is loaded, it is also obsolete.
-/
theorem generalizedCriticalInstance_no_trigger_with_datalog_head_active
    {obs : ObsolescenceCondition} {rs : RuleSet sig} {finite : rs.finite} {additional_consts : List sig.C} :
    ∀ trg : RTrigger obs rs, (∃ i lt, trg.val.rule.existential_vars_for_head_disjunct i lt = []) -> ¬ trg.val.active (rs.generalizedCriticalInstance finite additional_consts).toFactSet.val := by
  intro trg ⟨i, lt, no_exis⟩ ⟨loaded, contra⟩; apply contra
  apply obs.contains_trg_result_implies_cond i lt
  intro f f_mem
  have terms_constants : ∀ t ∈ f.terms, ∃ c ∈ (additional_consts.toSet ∪ rs.constants), t = .const c := by
    intro t t_mem
    rw [List.mem_toSet] at f_mem
    have t_mem : t ∈ (trg.val.mapped_head[i]'(by grind)).flatMap GeneralizedAtom.terms := List.mem_flatMap_of_mem f_mem t_mem
    rw [PreTrigger.mem_terms_mapped_head_iff _ _ lt] at t_mem
    cases t_mem with
    | inl t_mem => rcases t_mem with ⟨c, c_mem, t_eq⟩; exists c; constructor; apply Set.mem_union_of_mem_right; apply RuleSet.head_constants_subset_constants; exists trg.val.rule; constructor; exact trg.property; apply List.mem_flatMap_of_mem (List.getElem_mem lt) c_mem; exact Eq.symm t_eq
    | inr t_mem =>
    cases t_mem with
    | inr t_mem => rcases PreTrigger.mem_fresh_terms _ t_mem with ⟨v, v_mem, _⟩; simp [no_exis] at v_mem
    | inl t_mem =>
      rw [List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_eq⟩
      have v_mem_body : v ∈ trg.val.rule.body.vars := by
        apply trg.val.rule.frontier_subset_vars_body; rw [Rule.mem_frontier_iff_mem_frontier_for_head]; exact ⟨_, _, v_mem⟩
      have t_mem_db := FactSet.terms_subset_of_subset loaded t (by rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]; apply Or.inr; exists v)
      rcases t_mem_db with ⟨f, f_mem, t_mem_db⟩
      rcases (rs.generalizedCriticalInstance finite additional_consts).toFactSet.property.right f f_mem t t_mem_db with ⟨c, t_eq⟩
      exists c; constructor
      . rcases f_mem with ⟨f, f_mem, f_eq⟩
        apply rs.generalizedCriticalInstance_constants
        exists f; constructor; exact f_mem
        simp only [t_eq, ← f_eq, FunctionFreeFact.toFact, List.mem_map] at t_mem_db
        rcases t_mem_db with ⟨d, d_mem, d_eq⟩
        rw [GroundTerm.const.injEq] at d_eq
        rw [← d_eq]; exact d_mem
      . exact t_eq
  suffices f.isFunctionFree by
    exists f.toFunctionFreeFact this; constructor
    . apply functionFreeFact_mem_generalizedCriticalInstance_of_constants_mem
      . simp only [Fact.toFunctionFreeFact]
        simp only [List.mem_toSet, ← trg.val.apply_subs_for_mapped_head_eq i lt, TermMapping.mem_apply_generalized_atom_list] at f_mem
        rcases f_mem with ⟨a, a_mem, f_eq⟩; rw [f_eq]
        simp only [TermMapping.apply_generalized_atom]
        exists trg.val.rule; constructor; exact trg.property
        apply List.mem_append_right
        apply List.mem_flatMap_of_mem (List.getElem_mem lt)
        apply List.mem_map_of_mem
        exact a_mem
      . intro c c_mem; simp only [List.mem_toSet, Fact.toFunctionFreeFact, List.map_attach_eq_pmap, List.mem_pmap] at c_mem
        rcases c_mem with ⟨t, t_mem, c_eq⟩
        rcases terms_constants t t_mem with ⟨d, d_mem, t_eq⟩
        simp only [← c_eq, t_eq, GroundTerm.toConst_const]
        exact d_mem
    . simp
  intro t t_mem; rcases terms_constants t t_mem with ⟨c, _, eq⟩; exists c

/--
For RestrictedObsolescence, no trigger with non-empty head can ever be active if at least one constant is in the critical instance.
-/
theorem generalizedCriticalInstance_no_trigger_active_for_restrictedObsolescence
    {rs : RuleSet sig} {finite : rs.finite} {additional_consts : List sig.C} :
    (∃ c, c ∈ additional_consts.toSet ∪ rs.constants) ->
    ∀ trg : RTrigger RestrictedObsolescence rs, trg.val.rule.head ≠ [] -> ¬ trg.val.active (rs.generalizedCriticalInstance finite additional_consts).toFactSet.val := by
  intro ⟨c, c_mem⟩ trg head_ne ⟨loaded, contra⟩; apply contra
  simp only [RestrictedObsolescence]
  let subs : GroundSubstitution sig := fun v => if v ∈ trg.val.rule.frontier then trg.val.subs v else .const c
  have lt : 0 < trg.val.rule.head.length := by apply List.ne_nil_iff_length_pos.mp; exact head_ne
  exists 0, lt
  exists subs; constructor
  . intro _ mem_front; simp [subs, mem_front]
  . intro f f_mem
    have terms_constants : ∀ t ∈ f.terms, ∃ c ∈ (additional_consts.toSet ∪ rs.constants), t = .const c := by
      intro t t_mem
      simp only [List.mem_toSet, TermMapping.mem_apply_generalized_atom_list] at f_mem
      rcases f_mem with ⟨a, a_mem, f_mem⟩
      simp only [f_mem, TermMapping.apply_generalized_atom] at t_mem
      rw [List.mem_map] at t_mem; rcases t_mem with ⟨voc, voc_mem, t_mem⟩
      cases voc with
      | const c =>
        exists c; constructor; apply Set.mem_union_of_mem_right; apply RuleSet.head_constants_subset_constants; exists trg.val.rule; constructor; exact trg.property; apply List.mem_flatten_of_mem (List.mem_map_of_mem (List.getElem_mem lt)); apply List.mem_flatMap_of_mem a_mem; grind; rw [← t_mem]; simp [GroundSubstitution.apply_var_or_const]
      | var v =>
        simp only [GroundSubstitution.apply_var_or_const] at t_mem
        cases Decidable.em (v ∈ trg.val.rule.frontier) with
        | inr v_front => exists c; constructor; exact c_mem; rw [← t_mem]; simp [subs, v_front]
        | inl v_front =>
          have t_mem_db := FactSet.terms_subset_of_subset loaded t (by rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]; apply Or.inr; exists v; constructor; apply Rule.frontier_subset_vars_body; exact v_front; rw [← t_mem]; simp [subs, v_front])
          rcases t_mem_db with ⟨f, f_mem, t_mem_db⟩
          rcases (rs.generalizedCriticalInstance finite additional_consts).toFactSet.property.right f f_mem t t_mem_db with ⟨c, t_eq⟩
          exists c; constructor
          . rcases f_mem with ⟨f, f_mem, f_eq⟩
            apply rs.generalizedCriticalInstance_constants
            exists f; constructor; exact f_mem
            simp only [t_eq, ← f_eq, FunctionFreeFact.toFact, List.mem_map] at t_mem_db
            rcases t_mem_db with ⟨d, d_mem, d_eq⟩
            rw [GroundTerm.const.injEq] at d_eq
            rw [← d_eq]; exact d_mem
          . exact t_eq
    suffices f.isFunctionFree by
      exists f.toFunctionFreeFact this; constructor
      . apply functionFreeFact_mem_generalizedCriticalInstance_of_constants_mem
        . simp only [Fact.toFunctionFreeFact]
          simp only [List.mem_toSet, TermMapping.mem_apply_generalized_atom_list] at f_mem
          rcases f_mem with ⟨a, a_mem, f_eq⟩; rw [f_eq]
          simp only [TermMapping.apply_generalized_atom]
          exists trg.val.rule; constructor; exact trg.property
          apply List.mem_append_right
          apply List.mem_flatMap_of_mem (List.getElem_mem lt)
          apply List.mem_map_of_mem
          exact a_mem
        . intro c c_mem; simp only [List.mem_toSet, Fact.toFunctionFreeFact, List.map_attach_eq_pmap, List.mem_pmap] at c_mem
          rcases c_mem with ⟨t, t_mem, c_eq⟩
          rcases terms_constants t t_mem with ⟨d, d_mem, t_eq⟩
          simp only [← c_eq, t_eq, GroundTerm.toConst_const]
          exact d_mem
      . simp
    intro t t_mem; rcases terms_constants t t_mem with ⟨c, _, eq⟩; exists c

end RuleSet

