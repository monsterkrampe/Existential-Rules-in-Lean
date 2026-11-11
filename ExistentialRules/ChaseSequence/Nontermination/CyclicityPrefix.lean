/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.Function.Composition
public import ExistentialRules.ChaseSequence.Nontermination.CyclicitySequence
public import ExistentialRules.ChaseSequence.Nontermination.RepeatableUnblockability
public import ExistentialRules.ChaseSequence.Nontermination.RepeatingConstantMappings

open CustomBasicDatastructures

/-!
# Cyclicity Prefixes

This is section 5 of the [RPC] paper.
A `CyclicityPrefix` is a finite sequence of triggers that are all unblockable according to a `RepeatableUnblockability` condition.
This allows to repeat the prefix indefinitely, which yields a `CyclicitySequence`. This is of course something that we need to prove here.
Then the existence of a `CyclicityPrefix` directly implies that the underlying `RuleSet.neverTerminates`.
-/

public section

/-- We can extend a signature with a type for fresh constants by setting the constants to be a Sum type of the original constants and the fresh type. -/
abbrev Signature.withFreshConstants (sig : Signature) (Fresh : Type u) : Signature := {
  Preds := sig.Preds
  V := sig.V
  C := Sum sig.C Fresh
}

instance {sig : Signature} {Fresh : Type u} [Inhabited sig.C] : Inhabited (sig.withFreshConstants Fresh).C where
  default := .inl default

/-- In particular, we can simply use the variables as fresh constants. Think of this as constants that just happen to have the same name as the variables. -/
abbrev Signature.withFreshConstantsForVars (sig : Signature) : Signature := sig.withFreshConstants sig.V

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- This turns a `VarOrConst` into the constant Sum type of `Signature.withFreshConstants`. -/
def VarOrConst.toConst_withFreshConstantsForVars : TermMapping (VarOrConst sig) sig.withFreshConstantsForVars.C
| .const c => .inl c
| .var v => .inr v

/-- Change the constant of a `VarOrConst` into the Sum type of `Signature.withFreshConstants`. -/
def VarOrConst.cast_withFreshConstantsForVars : TermMapping (VarOrConst sig) (VarOrConst sig.withFreshConstantsForVars)
| .const c => .const (.inl c)
| .var v => .var v

/-- Calling `VarOrConst.filterConsts` after `cast_withFreshConstantsForVars` can be simplified to simply mapping over the original filtered constants. -/
@[simp, grind =]
theorem VarOrConst.filterConsts_after_cast_withFreshConstantsForVars {l : List (VarOrConst sig)} :
    VarOrConst.filterConsts (l.map VarOrConst.cast_withFreshConstantsForVars) = (VarOrConst.filterConsts l).map .inl := by
  induction l with
  | nil => simp [VarOrConst.filterConsts]
  | cons hd tl ih =>
    simp only [List.map_cons, VarOrConst.filterConsts]
    cases hd <;> (simp [VarOrConst.cast_withFreshConstantsForVars]; exact ih)

/-- Calling `VarOrConst.filterVars` after `cast_withFreshConstantsForVars` is the same as only calling `VarOrConst.filterVars`. -/
@[simp, grind =]
theorem VarOrConst.filterVars_after_cast_withFreshConstantsForVars {l : List (VarOrConst sig)} :
    VarOrConst.filterVars (l.map VarOrConst.cast_withFreshConstantsForVars) = VarOrConst.filterVars l := by
  induction l with
  | nil => simp [VarOrConst.filterVars]
  | cons hd tl ih =>
    simp only [List.map_cons, VarOrConst.filterVars]
    cases hd <;> (simp [VarOrConst.cast_withFreshConstantsForVars]; exact ih)

variable [DecidableEq sig.P]

/-- Then applying `cast_withFreshConstantsForVars` to a conjunction, the variables remain unchanged. -/
theorem FunctionFreeConjunction.vars_cast_withFreshConstantsForVars {conj : FunctionFreeConjunction sig} :
    FunctionFreeConjunction.vars (VarOrConst.cast_withFreshConstantsForVars.apply_generalized_atom_list conj) = conj.vars := by
  simp only [FunctionFreeConjunction.vars, TermMapping.apply_generalized_atom_list]
  rw [List.flatMap_map]
  congr
  apply funext
  intro a
  simp [FunctionFreeAtom.variables, TermMapping.apply_generalized_atom]

/-- Change the constant of a `Rule` into the Sum type of `Signature.withFreshConstants`. -/
def Rule.cast_withFreshConstantsForVars (r : Rule sig) : Rule sig.withFreshConstantsForVars where
  body := VarOrConst.cast_withFreshConstantsForVars.apply_generalized_atom_list r.body
  head := r.head.map VarOrConst.cast_withFreshConstantsForVars.apply_generalized_atom_list

/-- The constants of the cast rule are exactly the constants of the original rule (mapped to the left part of the sum type). -/
theorem Rule.constants_cast_withFreshConstantsForVars {r : Rule sig} :
    r.cast_withFreshConstantsForVars.constants = r.constants.map .inl := by
  simp only [Rule.constants, cast_withFreshConstantsForVars]
  rw [List.map_append, List.map_flatMap, List.flatMap_map]
  suffices ∀ conj : FunctionFreeConjunction sig, FunctionFreeConjunction.consts (VarOrConst.cast_withFreshConstantsForVars.apply_generalized_atom_list conj) = conj.consts.map .inl by simp [this]
  intro conj
  simp only [FunctionFreeConjunction.consts, TermMapping.apply_generalized_atom_list]
  rw [List.map_flatMap, List.flatMap_map]
  congr
  apply funext
  intro a
  simp [FunctionFreeAtom.constants, TermMapping.apply_generalized_atom]

/-- The length of the `Rule.head` is not changed by `cast_withFreshConstantsForVars`.  -/
@[simp, grind =]
theorem Rule.length_head_cast_withFreshConstantsForVars {r : Rule sig} :
    r.cast_withFreshConstantsForVars.head.length = r.head.length := by
  simp [cast_withFreshConstantsForVars]

/-- When calling `Rule.cast_withFreshConstantsForVars`, the variables in each head disjunct remain untouched. -/
theorem Rule.vars_head_disjunct_cast_withFreshConstantsForVars {r : Rule sig} :
    ∀ {i : Nat} (lt : i < r.head.length),
    (r.cast_withFreshConstantsForVars.head[i]'(by grind)).vars = r.head[i].vars := by
  intro i lt; simp [cast_withFreshConstantsForVars, FunctionFreeConjunction.vars_cast_withFreshConstantsForVars]

/-- When calling `Rule.cast_withFreshConstantsForVars`, the variables in the body remain untouched. -/
@[simp, grind =]
theorem Rule.vars_body_cast_withFreshConstantsForVars {r : Rule sig} :
    r.cast_withFreshConstantsForVars.body.vars = r.body.vars := by
  simp [cast_withFreshConstantsForVars, FunctionFreeConjunction.vars_cast_withFreshConstantsForVars]

/-- The frontier of the cast rule remains unchanged. -/
@[simp, grind =]
theorem Rule.frontier_cast_withFreshConstantsForVars {r : Rule sig} : r.cast_withFreshConstantsForVars.frontier = r.frontier := by
  simp only [Rule.frontier]
  rw [vars_body_cast_withFreshConstantsForVars]
  congr
  apply funext; intro v
  simp only [List.any_eq, decide_eq_decide]
  simp only [List.exists_mem_iff_exists_getElem]
  constructor
  . intro ⟨i, lt, h⟩; rw [vars_head_disjunct_cast_withFreshConstantsForVars (by grind)] at h; exact ⟨_, _, h⟩
  . intro ⟨i, lt, h⟩; exists i, (by grind); rw [vars_head_disjunct_cast_withFreshConstantsForVars (by grind)]; exact h

/-- The cast rule isDatalog if and only if the original rule isDatalog. -/
@[simp, grind =]
theorem Rule.isDatalog_cast_withFreshConstantsForVars {r : Rule sig} : r.cast_withFreshConstantsForVars.isDatalog ↔ r.isDatalog := by
  simp only [Rule.isDatalog]
  rw [vars_body_cast_withFreshConstantsForVars]
  simp only [List.all_eq, decide_eq_true_eq]
  simp only [List.forall_mem_iff_forall_getElem]
  constructor
  . intro h i lt; specialize h i (by grind); rw [vars_head_disjunct_cast_withFreshConstantsForVars (by grind)] at h; exact h
  . intro h i lt; specialize h i (by grind); rw [vars_head_disjunct_cast_withFreshConstantsForVars (by grind)]; exact h

/-- Change the constant of a `RuleSet` into the Sum type of `Signature.withFreshConstants`. -/
def RuleSet.cast_withFreshConstantsForVars (rs : RuleSet sig) : RuleSet sig.withFreshConstantsForVars :=
  rs.map Rule.cast_withFreshConstantsForVars

/-- The constants of the cast rule set are exactly the constants of the original rule set (mapped to the left part of the sum type). -/
theorem RuleSet.constants_cast_withFreshConstantsForVars {rs : RuleSet sig} :
    rs.cast_withFreshConstantsForVars.constants = rs.constants.map .inl := by
  apply Set.ext
  intro c; rw [Set.mem_map]
  simp only [cast_withFreshConstantsForVars]
  constructor
  . intro ⟨r, r_mem, c_mem⟩
    rw [Set.mem_map] at r_mem; rcases r_mem with ⟨r', r'_mem, r_mem⟩
    rw [← r_mem, Rule.constants_cast_withFreshConstantsForVars, List.mem_map] at c_mem
    rcases c_mem with ⟨d, d_mem, c_mem⟩
    exists d; constructor; exists r'; exact c_mem
  . intro ⟨d, ⟨r, r_mem, d_mem⟩, c_eq⟩
    exists r.cast_withFreshConstantsForVars; constructor; exact Set.mem_map_of_mem r_mem
    rw [Rule.constants_cast_withFreshConstantsForVars, ← c_eq]
    exact List.mem_map_of_mem d_mem

/-- The `body_database` of a rule is the body where each variable is replaced by a fresh constant.
We achieve this by extending the signature and mapping all terms in the body using `VarOrConst.cast_withFreshConstantsForVars`. -/
def Rule.body_database (r : Rule sig) : Database sig.withFreshConstantsForVars :=
  ⟨(VarOrConst.toConst_withFreshConstantsForVars.apply_generalized_atom_list r.body).toSet, List.finite_toSet _⟩

/-- The `body_kb` consists of the cast rule set and the `body_database`. -/
def Rule.body_kb (r : Rule sig) (rules : RuleSet sig) : KnowledgeBase sig.withFreshConstantsForVars :=
  { rules := rules.cast_withFreshConstantsForVars, db := r.body_database }

/-- The trigger for a rule that matches its `body_database`. -/
def Rule.body_database_trigger (r : Rule sig) : PreTrigger sig.withFreshConstantsForVars where
  rule := r.cast_withFreshConstantsForVars
  subs := .const ∘ .inr

/-- The mapped_body of the `body_database_trigger` is exactly the `body_database`. -/
theorem Rule.mapped_body_body_database_trigger {r : Rule sig} : r.body_database_trigger.mapped_body.toSet = r.body_database.toFactSet := by
  unfold body_database body_database_trigger
  apply Set.ext; intro f
  simp only [PreTrigger.mapped_body, List.mem_toSet, TermMapping.mem_apply_generalized_atom_list]
  simp only [cast_withFreshConstantsForVars, TermMapping.mem_apply_generalized_atom_list]
  simp only [Database.toFactSet, List.mem_toSet]
  simp only [TermMapping.apply_generalized_atom_list, List.mem_map]
  constructor
  . intro ⟨b, ⟨a, a_mem, b_eq⟩, f_eq⟩
    exists VarOrConst.toConst_withFreshConstantsForVars.apply_generalized_atom a; constructor
    . exists a
    . rw [f_eq, b_eq]
      rw [FunctionFreeFact.toFact_eq]
      rw [← TermMapping.apply_generalized_atom_compose', ← TermMapping.apply_generalized_atom_compose']
      apply TermMapping.apply_generalized_atom_congr_left
      intro t t_mem
      cases t <;> simp [VarOrConst.cast_withFreshConstantsForVars, VarOrConst.toConst_withFreshConstantsForVars, GroundSubstitution.apply_var_or_const]
  . intro ⟨b, ⟨a, a_mem, b_eq⟩, f_eq⟩
    exists VarOrConst.cast_withFreshConstantsForVars.apply_generalized_atom a; constructor
    . exists a
    . rw [← f_eq, ← b_eq]
      rw [FunctionFreeFact.toFact_eq]
      rw [← TermMapping.apply_generalized_atom_compose', ← TermMapping.apply_generalized_atom_compose']
      apply TermMapping.apply_generalized_atom_congr_left
      intro t t_mem
      cases t <;> simp [VarOrConst.cast_withFreshConstantsForVars, VarOrConst.toConst_withFreshConstantsForVars, GroundSubstitution.apply_var_or_const]

/-- The `body_database_trigger` is loaded for the `body_database`. -/
theorem Rule.body_database_trigger_loaded {r : Rule sig} : r.body_database_trigger.loaded r.body_database.toFactSet.val := by
  unfold PreTrigger.loaded
  rw [mapped_body_body_database_trigger]
  exact Set.subset_refl

/-- The mapped_frontier of the `body_database_trigger` results from turning every frontier variable into its unique constant. -/
theorem Rule.mapped_frontier_body_database_trigger {r : Rule sig} :
    r.body_database_trigger.mapped_frontier = r.frontier.map (.const ∘ .inr) := by
  simp [body_database_trigger, PreTrigger.mapped_frontier]

/-- The `ChaseNodeOrigin` for a rule that matches its `body_database`. -/
def Rule.body_database_origin
    (obs : ObsolescenceCondition sig.withFreshConstantsForVars)
    (rules : RuleSet sig)
    (hc : HeadChoice sig.withFreshConstantsForVars)
    (r : Rule sig)
    (r_mem : r ∈ rules) :
    ChaseNodeOrigin obs rules.cast_withFreshConstantsForVars :=
  let trg := r.body_database_trigger
  ⟨⟨Trigger.fromPreTrigger trg obs, by simp only [trg, RuleSet.cast_withFreshConstantsForVars, Rule.body_database_trigger]; apply Set.mem_map_of_mem; exact r_mem⟩, hc r.body_database_trigger⟩

/-- The `body_database_origin` adheres to the head choice. -/
theorem Rule.body_database_origin_adheres_to_headChoice
    {obs : ObsolescenceCondition sig.withFreshConstantsForVars}
    {rules : RuleSet sig}
    {hc : HeadChoice sig.withFreshConstantsForVars}
    {r : Rule sig}
    {r_mem : r ∈ rules} :
    (r.body_database_origin obs rules hc r_mem).adheres_to_headChoice hc := by
  simp only [body_database_origin, ChaseNodeOrigin.adheres_to_headChoice]
  congr

/-- For a signature `withFreshConstantsForVars`, we can turn a `GroundSubstitution` into a `ConstantMapping`. -/
def GroundSubstitution.toConstantMapping_for_sig_withFreshConstantsForVars (subs : GroundSubstitution sig.withFreshConstantsForVars) :
    ConstantMapping sig.withFreshConstantsForVars
| .inl c => .const (.inl c) -- we leave original constants untouched
| .inr v => subs v

/--
Applying `GroundSubstitution.toConstantMapping_for_sig_withFreshConstantsForVars` after turning a variable into its unique constant behaves the same as the original substitution.
-/
theorem GroundSubstitution.toConstantMapping_for_sig_withFreshConstantsForVars_after_toConst_withFreshConstantsForVars_eq_subs
    {subs : GroundSubstitution sig.withFreshConstantsForVars} :
    subs.toConstantMapping_for_sig_withFreshConstantsForVars ∘ .inr = subs := by
  apply funext; simp [toConstantMapping_for_sig_withFreshConstantsForVars]

/--
We define a structure, which is almost a `CyclicityPrefix` (missing some last conditions).
We split this mainly to add some auxiliary definitions that we can use to express the remaining conditions more easily.
-/
structure PreCyclicityPrefix
    [Inhabited sig.C]
    (obs : ObsolescenceCondition sig.withFreshConstantsForVars)
    {rules : RuleSet sig}
    {hc : HeadChoice sig.withFreshConstantsForVars}
    (hc_consistent : hc.consistent_for_same_rule)
    {rule : Rule sig}
    (rule_mem : rule ∈ rules)
    (rule_hc_exis : rule.body_database_trigger.rule.existential_vars_for_head_disjunct (hc rule.body_database_trigger).val (hc rule.body_database_trigger).isLt ≠ []) where
  body_database_trigger_unblockable : (Trigger.fromPreTrigger rule.body_database_trigger obs).kbUnblockable (rule.body_kb rules) hc
  -- this list does not include the initial database trigger
  triggers : FiniteTriggerList obs rules.cast_withFreshConstantsForVars
  -- the first conditions are also found in the `CyclicityDerivation`; `growing` and `unblockable` are missing though
  adheres_to_headChoice : triggers.adheres_to_headChoice hc
  triggers_loaded : triggers.loaded (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet)
  -- from here things are different
  ex_last_trigger : ∃ last ∈ triggers.getLast?, last.fst.val.rule = rule.cast_withFreshConstantsForVars

namespace PreCyclicityPrefix

variable [Inhabited sig.C] {obs : ObsolescenceCondition sig.withFreshConstantsForVars} {rules : RuleSet sig} {hc : HeadChoice sig.withFreshConstantsForVars} {hc_consistent : hc.consistent_for_same_rule} {rule : Rule sig} {rule_mem : rule ∈ rules} {rule_hc_exis : rule.body_database_trigger.rule.existential_vars_for_head_disjunct (hc rule.body_database_trigger).val (hc rule.body_database_trigger).isLt ≠ []}

/-- The triggers are not empty. -/
theorem triggers_ne_nil {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} : cp.triggers ≠ [] := by
  rcases cp.ex_last_trigger with ⟨_, mem, _⟩
  intro contra; simp [contra] at mem

/-- We can cast the triggers into a `FiniteNonEmptyTriggerList`. -/
def to_FiniteNonEmptyTriggerList (cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis) :
    FiniteNonEmptyTriggerList obs rules.cast_withFreshConstantsForVars :=
  NonEmptyList.from_ne_nil cp.triggers cp.triggers_ne_nil

/-- Since the trigger list is not empty, we can get the last trigger. -/
def last_trigger (cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis) :
    ChaseNodeOrigin obs rules.cast_withFreshConstantsForVars :=
  cp.triggers.getLast cp.triggers_ne_nil

/-- The `last_trigger` occurs in `triggers`. -/
theorem last_trigger_mem {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} : cp.last_trigger ∈ cp.triggers := by simp [last_trigger]

/-- The `ex_last_trigger` property expressed for the `last_trigger` shortcut. -/
theorem rule_last_trigger {cp : PreCyclicityPrefix obc hc_consistent rule_mem rule_hc_exis} :
    cp.last_trigger.fst.val.rule = rule.cast_withFreshConstantsForVars := by
  rcases cp.ex_last_trigger with ⟨last, mem, h⟩
  suffices last = cp.last_trigger by rw [← this]; exact h
  apply Eq.symm
  apply List.getLast_of_mem_getLast?
  exact mem

/--
In the end, we want to repeat the prefix using a constant mapping expressing the mapping from the database trigger to the last trigger.
This mapping is what is defined here.
-/
def constantMappingForRepetition (cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis) :
    ConstantMapping sig.withFreshConstantsForVars :=
  cp.last_trigger.fst.val.subs.toConstantMapping_for_sig_withFreshConstantsForVars

/-- The `constantMappingForRepetition` and repetitions thereof do not alter constants occurring in rules. -/
theorem constantMappingForRepetition_on_rule_constants {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis}
    {c : sig.withFreshConstantsForVars.C}
    (c_mem : c ∈ rules.cast_withFreshConstantsForVars.constants) : ∀ n, cp.constantMappingForRepetition.repeat_fun n c = .const c := by
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    rw [ConstantMapping.repeat_succ, Function.comp_apply, ih, ConstantMapping.apply_ground_term_constant]
    simp only [constantMappingForRepetition, GroundSubstitution.toConstantMapping_for_sig_withFreshConstantsForVars]
    suffices ∃ d, c = .inl d by rcases this with ⟨_, eq⟩; simp [eq]
    rw [RuleSet.constants_cast_withFreshConstantsForVars, Set.mem_map] at c_mem
    rcases c_mem with ⟨d, _, c_eq⟩
    exists d; rw [c_eq]

/-- The `last_trigger` os exactly the initial database trigger with the `constantMappingForRepetition` applied. (Because this is essentially how the `constantMappingForRepetition` is defined.) -/
theorem last_trigger_eq {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.last_trigger.fst.val = rule.body_database_trigger.extend_with_groundTermMapping cp.constantMappingForRepetition.apply_ground_term := by
  rw [PreTrigger.mk.injEq]; constructor
  . simp [rule_last_trigger, Rule.body_database_trigger]
  . simp only [PreTrigger.extend_with_groundTermMapping, Rule.body_database_trigger]
    suffices cp.constantMappingForRepetition.apply_ground_term ∘ .const = cp.constantMappingForRepetition by
      rw [← Function.comp_assoc, this]
      simp only [constantMappingForRepetition]
      rw [GroundSubstitution.toConstantMapping_for_sig_withFreshConstantsForVars_after_toConst_withFreshConstantsForVars_eq_subs]
    apply funext; simp

/-- The `last_trigger` result is the result of the initial trigger with the `constantMappingForRepetition` applied afterwards. -/
theorem result_last_trigger {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.last_trigger.result = (rule.body_database_origin obs rules hc rule_mem).result.map cp.constantMappingForRepetition.apply_fact := by
  have adheres := cp.adheres_to_headChoice cp.last_trigger cp.last_trigger_mem
  rw [ChaseNodeOrigin.result_eq_of_adheres_to_headChoice adheres]
  rw [last_trigger_eq]
  simp only [ChaseNodeOrigin.result, Rule.body_database_origin, PreTrigger.output_for_headChoice]
  suffices (hc (rule.body_database_trigger.extend_with_groundTermMapping cp.constantMappingForRepetition.apply_ground_term)).val = (hc rule.body_database_trigger).val by
    simp only [this]
    apply List.ext_getElem
    . simp [PreTrigger.mapped_head]
    intro j lt1 lt2
    simp only [List.getElem_map, PreTrigger.mapped_head]
    rw [ConstantMapping.apply_fact_swap_apply_to_function_free_atom]
    . simp
    . simp only [Trigger.rule_fromPreTrigger, List.getElem_attach, List.getElem_zipIdx, Nat.zero_add]
      intro d d_mem; rw [← cp.constantMappingForRepetition.repeat_once]; apply constantMappingForRepetition_on_rule_constants
      exists rule.body_database_trigger.rule; constructor
      . apply Set.mem_map_of_mem; exact rule_mem
      . apply Rule.head_constants_subset_constants
        apply List.mem_flatMap_of_mem
        . exact List.getElem_mem (hc rule.body_database_trigger).isLt
        apply List.mem_flatMap_of_mem
        . apply List.getElem_mem (n := j); grind
        . exact d_mem
  apply hc_consistent; simp

/-- The `last_trigger` is loaded for the fact set immediately preceeding it. -/
theorem last_trigger_loaded {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.last_trigger.fst.val.loaded (FiniteTriggerList.result (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet) cp.triggers.dropLast) := by
  simp only [last_trigger, List.getLast_eq_getElem, List.dropLast_eq_take]
  have lt : cp.triggers.length - 1 < cp.triggers.length := by
    apply Nat.pred_lt_self; grind [cp.triggers_ne_nil]
  have loaded := cp.triggers_loaded
  unfold FiniteTriggerList.loaded at loaded; rw [FiniteTriggerList.trigger_property_holds_iff] at loaded
  specialize loaded lt
  exact loaded

/--
Returns the ith repetition of the trigger list obtained by extending the triggers with the `constantMappingForRepetition` i times.
This is used for constructing an infinite list of finite trigger lists.
-/
def ithRepetition (cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis) (i : Nat) :
    FiniteNonEmptyTriggerList obs rules.cast_withFreshConstantsForVars :=
  let trgs : FiniteTriggerList obs rules.cast_withFreshConstantsForVars :=
    cp.triggers.map (fun orig => ⟨
      orig.fst.extend_with_groundTermMapping
        (cp.constantMappingForRepetition.repeat_fun i).apply_ground_term,
      orig.snd⟩)
  NonEmptyList.from_ne_nil trgs (by
    suffices cp.triggers = cp.to_FiniteNonEmptyTriggerList.toList by
      simp only [trgs, this]
      intro contra
      apply cp.to_FiniteNonEmptyTriggerList.toList_ne_nil
      exact List.eq_nil_of_map_eq_nil contra
    simp [to_FiniteNonEmptyTriggerList])

/-- The 0-th repetition is the original trigger list. -/
theorem ithRepetition_zero {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} : cp.ithRepetition 0 = cp.to_FiniteNonEmptyTriggerList := by
  simp only [ithRepetition, to_FiniteNonEmptyTriggerList]
  congr
  apply List.map_id''
  intro _; rw [ConstantMapping.repeat_zero, ConstantMapping.apply_ground_term_id]; constructor

/-- Every following repetition results from extending the triggers with a single application of the `constantMappingForRepetition`. -/
theorem ithRepetition_succ {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} {i : Nat} :
    cp.ithRepetition i.succ = NonEmptyList.from_ne_nil ((cp.ithRepetition i).toList.map (fun orig => ⟨
      orig.fst.extend_with_groundTermMapping cp.constantMappingForRepetition.apply_ground_term,
      orig.snd
    ⟩)) (by simpa using NonEmptyList.toList_ne_nil) := by
  simp only [ithRepetition, NonEmptyList.toList_from_ne_nil, List.map_map]
  congr
  rw [ConstantMapping.repeat_succ, ConstantMapping.apply_ground_term_compose]
  rfl

/-- The length of every repetition matches the length of the original trigger list. -/
@[simp, grind =]
theorem length_ithRepetition {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} {i : Nat} : (cp.ithRepetition i).toList.length = cp.triggers.length := by
  simp [ithRepetition]

/-- The result of a trigger in the ithRepetition can be obtained by applying the constant mapping to the original trigger result. -/
theorem result_ithRepetition {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} {i : Nat} : ∀ {j : Nat} (lt : j < cp.triggers.length),
    ((cp.ithRepetition i).toList[j]'(by grind)).result = cp.triggers[j].result.map (cp.constantMappingForRepetition.repeat_fun i).apply_fact := by
  intro j lt
  suffices ((cp.ithRepetition i).toList[j]'(by grind)).result = (cp.triggers[j].fst.extend_with_groundTermMapping (cp.constantMappingForRepetition.repeat_fun i).apply_ground_term).val.mapped_head[cp.triggers[j].snd] by
    rw [this]
    simp only [ChaseNodeOrigin.result]
    apply List.ext_getElem
    . simp [PreTrigger.mapped_head]
    intro k lt1 lt2
    simp only [PreTrigger.mapped_head, Trigger.rule_fromPreTrigger, PreTrigger.rule_extend_with_groundTermMapping, Fin.getElem_fin, List.getElem_map, List.getElem_attach, List.getElem_zipIdx, Nat.zero_add, Trigger.toPreTrigger_after_fromPreTrigger, List.map_map, Function.comp_apply]
    simp only [← ConstantMapping.apply_fact.eq_def (cp.constantMappingForRepetition.repeat_fun i)]
    rw [ConstantMapping.apply_fact_swap_apply_to_function_free_atom]
    intro d d_mem
    apply constantMappingForRepetition_on_rule_constants
    exists cp.triggers[j].fst.val.rule; constructor; exact cp.triggers[j].fst.property
    apply Rule.head_constants_subset_constants
    apply List.mem_flatMap_of_mem
    . exact List.getElem_mem cp.triggers[j].snd.isLt
    apply List.mem_flatMap_of_mem
    . apply List.getElem_mem (n := k); grind
    . exact d_mem
  simp only [ithRepetition, NonEmptyList.toList_from_ne_nil]
  simp only [List.getElem_map, ChaseNodeOrigin.result]
  apply List.getElem_eq_getElem_of_idx_eq
  rw [List.getElem_map]

/-- We can arrange the i-th repetitions into an infinite list. -/
def infiniteList_of_finiteLists (cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis) :
    InfiniteList (FiniteNonEmptyTriggerList obs rules.cast_withFreshConstantsForVars) :=
  fun i => cp.ithRepetition i

/-- Each repetition adheres to the headChoice. -/
theorem infiniteList_of_finiteLists_adheres {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} : ∀ l ∈ cp.infiniteList_of_finiteLists,
    FiniteTriggerList.adheres_to_headChoice l.toList hc := by
  intro l l_mem orig orig_mem
  simp only [InfiniteList.mem_iff, InfiniteList.compute_get, infiniteList_of_finiteLists, ithRepetition] at l_mem
  rcases l_mem with ⟨_, l_mem⟩
  rw [← l_mem, NonEmptyList.toList_from_ne_nil] at orig_mem
  rw [List.mem_map] at orig_mem; rcases orig_mem with ⟨orig', orig'_mem, orig_eq⟩
  rw [← orig_eq]; simp only [ChaseNodeOrigin.adheres_to_headChoice]
  rw [cp.adheres_to_headChoice orig' orig'_mem]
  apply hc_consistent; simp

/-- Each repetition is loaded. -/
theorem infiniteList_of_finiteLists_loaded {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    ∀ i, FiniteTriggerList.loaded (InfiniteTriggerList.startForFiniteList cp.infiniteList_of_finiteLists (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet) i) (cp.infiniteList_of_finiteLists.get i).toList := by
  suffices ∀ i j, (GroundTermMapping.applyFactSet (cp.constantMappingForRepetition.repeat_fun i).apply_ground_term (FiniteTriggerList.result (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet) (cp.triggers.take j))) ⊆ FiniteTriggerList.result (InfiniteTriggerList.startForFiniteList cp.infiniteList_of_finiteLists (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet) i) ((cp.infiniteList_of_finiteLists.get i).toList.take j) by
    intro i
    unfold FiniteTriggerList.loaded
    rw [FiniteTriggerList.trigger_property_holds_iff]
    intro j j_lt
    apply Set.subset_trans _ (this i j)
    simp only [infiniteList_of_finiteLists, InfiniteList.compute_get, ithRepetition, NonEmptyList.toList_from_ne_nil, List.getElem_map]
    apply PreTrigger.extend_with_groundTermMapping_loaded_of_loaded
    . intro d d_mem
      rw [ConstantMapping.apply_ground_term_constant]
      apply constantMappingForRepetition_on_rule_constants
      exists (cp.triggers[j]'(by grind)).fst.val.rule; constructor; exact (cp.triggers[j]'(by grind)).fst.property
      exact Rule.body_constants_subset_constants _ d_mem
    . have triggers_loaded := cp.triggers_loaded
      unfold FiniteTriggerList.loaded at triggers_loaded
      rw [FiniteTriggerList.trigger_property_holds_iff] at triggers_loaded
      exact triggers_loaded _
  intro i
  induction i with
  | zero =>
    intro j; simp only [InfiniteTriggerList.startForFiniteList]
    rw [ConstantMapping.repeat_zero, ConstantMapping.apply_ground_term_id, GroundTermMapping.applyFactSet_id]
    simp only [infiniteList_of_finiteLists, InfiniteList.compute_get, ithRepetition_zero, to_FiniteNonEmptyTriggerList, NonEmptyList.toList_from_ne_nil]
    apply Set.subset_refl
  | succ i ih_i =>
    intro j
    induction j with
    | zero =>
      simp only [List.take_zero, FiniteTriggerList.result_nil]
      simp only [InfiniteTriggerList.startForFiniteList]

      specialize ih_i cp.triggers.length
      have : cp.triggers.length = (cp.infiniteList_of_finiteLists.get i).toList.length := by simp [infiniteList_of_finiteLists, InfiniteList.compute_get]
      simp only [List.take_length] at ih_i; rw [this, List.take_length] at ih_i
      apply Set.subset_trans _ ih_i
      rw [ConstantMapping.repeat_succ', ConstantMapping.apply_ground_term_compose]
      simp only [GroundTermMapping.applyFactSet, TermMapping.apply_generalized_atom_set_compose, Function.comp_apply]
      apply TermMapping.apply_generalized_atom_set_subset_of_subset

      rw [TermMapping.apply_generalized_atom_set_union, Set.union_subset_iff_both_subset]
      constructor
      . rw [← List.dropLast_concat_getLast cp.triggers_ne_nil]
        rw [FiniteTriggerList.result_append]
        apply Set.subset_trans _ (FiniteTriggerList.start_sub_result (l := [cp.triggers.getLast _]))
        apply Set.subset_trans _ cp.last_trigger_loaded
        rw [last_trigger_eq]
        rw [PreTrigger.mapped_body_extend_with_groundTermMapping_eq]
        . rw [← TermMapping.apply_generalized_atom_list.eq_def, ← TermMapping.apply_generalized_atom_set_toSet]
          rw [Rule.mapped_body_body_database_trigger]
          exact Set.subset_refl
        . intro d d_mem
          rw [ConstantMapping.apply_ground_term_constant, ← cp.constantMappingForRepetition.repeat_once]
          apply constantMappingForRepetition_on_rule_constants
          exists rule.cast_withFreshConstantsForVars; constructor
          . apply Set.mem_map_of_mem; exact rule_mem
          . apply Rule.body_constants_subset_constants; exact d_mem
      . apply Set.subset_trans _ (FiniteTriggerList.each_trg_result_sub_result cp.last_trigger cp.last_trigger_mem)
        rw [result_last_trigger, TermMapping.apply_generalized_atom_set_toSet]
        exact Set.subset_refl
    | succ j ih_j =>
      simp only [List.take_add_one, FiniteTriggerList.result_append]
      cases Decidable.em (j < cp.triggers.length) with
      | inr j_not_lt =>
        have j_not_lt' : ¬ j < (cp.infiniteList_of_finiteLists.get (i+1)).toList.length := by
          simpa [infiniteList_of_finiteLists, InfiniteList.compute_get, ithRepetition] using j_not_lt
        simpa [j_not_lt, j_not_lt'] using ih_j
      | inl j_lt =>
        have j_lt' : j < (cp.infiniteList_of_finiteLists.get (i+1)).toList.length := by
          simpa [infiniteList_of_finiteLists, InfiniteList.compute_get, ithRepetition] using j_lt
        simp only [j_lt, j_lt', getElem?_pos, Option.toList_some, FiniteTriggerList.result_singleton]
        unfold GroundTermMapping.applyFactSet
        rw [TermMapping.apply_generalized_atom_set_union]
        rw [Set.union_subset_iff_both_subset]; constructor
        . apply Set.subset_union_of_subset_left; exact ih_j
        . apply Set.subset_union_of_subset_right
          simp only [infiniteList_of_finiteLists, InfiniteList.compute_get]
          rw [result_ithRepetition j_lt]
          rw [TermMapping.apply_generalized_atom_set_toSet]
          apply Set.subset_refl

/-- Then, we can turn the infinite list of i-th repetitions into a single infinite list and also prepend the initial trigger. -/
def infiniteTriggerList (cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis) : InfiniteTriggerList obs rules.cast_withFreshConstantsForVars :=
  InfiniteList.cons (rule.body_database_origin obs rules hc rule_mem) (InfiniteTriggerList.fromFiniteLists cp.infiniteList_of_finiteLists)

/-- The `infiniteTriggerList` adheres to the head choice because the `PreCyclicityPrefix` does. -/
theorem infiniteTriggerList_adheres {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.infiniteTriggerList.adheres_to_headChoice hc := by
  unfold infiniteTriggerList
  intro orig orig_mem
  cases InfiniteList.mem_cons.mp orig_mem with
  | inl orig_mem => rw [orig_mem]; exact Rule.body_database_origin_adheres_to_headChoice
  | inr orig_mem =>
    apply InfiniteTriggerList.fromFiniteLists_headChoice_preserved _ orig orig_mem
    exact infiniteList_of_finiteLists_adheres

/-- The `infiniteTriggerList` is loaded because the `PreCyclicityPrefix` is. -/
theorem infiniteTriggerList_loaded {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.infiniteTriggerList.loaded rule.body_database.toFactSet.val := by
  unfold infiniteTriggerList
  apply (InfiniteTriggerList.trigger_property_holds_iff_holds_for_head_and_tail (property := fun orig => orig.fst.val.loaded)).mpr
  simp only [InfiniteList.head_cons, InfiniteList.tail_cons]
  constructor
  . exact Rule.body_database_trigger_loaded
  . apply InfiniteTriggerList.fromFiniteLists_loadedness_preserved
    exact cp.infiniteList_of_finiteLists_loaded

/-- The infinite list of triggers can be turned into a regularChaseDerivationSkeleton. -/
def infiniteRegularChaseDerivationSkeleton (cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis) :
    RegularChaseDerivationSkeleton obs rules.cast_withFreshConstantsForVars :=
  cp.infiniteTriggerList.to_regularChaseDerivationSkeleton rule.body_database.toFactSet.val

/-- Since the `infiniteRegularChaseDerivationSkeleton` is infinite, every suffix has a next value. -/
theorem infiniteRegularChaseDerivationSkeleton_next_some_of_suffix {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} {cd2 : RegularChaseDerivationSkeleton obs rules.cast_withFreshConstantsForVars} (suffix : cd2 <:+ cp.infiniteRegularChaseDerivationSkeleton) :
    cd2.next.isSome := by
  rw [ChaseDerivationSkeleton.IsSuffix_iff] at suffix; rcases suffix with ⟨m, suffix⟩
  simp [← suffix, infiniteRegularChaseDerivationSkeleton, InfiniteTriggerList.to_regularChaseDerivationSkeleton, ChaseDerivationSkeleton.next, PossiblyInfiniteList.head_eq]

/-- A shortcut for unwrapping the next element of the `infiniteRegularChaseDerivationSkeleton`. -/
def infiniteRegularChaseDerivationSkeleton_next (cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis) : RegularChaseNode obs rules.cast_withFreshConstantsForVars := cp.infiniteRegularChaseDerivationSkeleton.next.get (infiniteRegularChaseDerivationSkeleton_next_some_of_suffix PossiblyInfiniteList.IsSuffix_refl)

/-- The above shortcut behaves as expected. -/
theorem infiniteRegularChaseDerivationSkeleton_next_def {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.infiniteRegularChaseDerivationSkeleton.next = some cp.infiniteRegularChaseDerivationSkeleton_next := by
  simp [infiniteRegularChaseDerivationSkeleton_next]

/-- The head of the `infiniteRegularChaseDerivationSkeleton` is the `Rule.body_database` of the initial rule. -/
theorem infiniteRegularChaseDerivationSkeleton_head_eq_body_database {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.infiniteRegularChaseDerivationSkeleton.head.facts = rule.body_database.toFactSet.val := by
  simp [infiniteRegularChaseDerivationSkeleton, InfiniteTriggerList.to_regularChaseDerivationSkeleton, ChaseDerivationSkeleton.head, PossiblyInfiniteList.head_eq]

/-- The head of the `infiniteRegularChaseDerivationSkeleton` has no origin. -/
theorem infiniteRegularChaseDerivationSkeleton_origin_head_eq_none {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.infiniteRegularChaseDerivationSkeleton.head.origin = none := by
  simp [infiniteRegularChaseDerivationSkeleton, InfiniteTriggerList.to_regularChaseDerivationSkeleton, ChaseDerivationSkeleton.head, PossiblyInfiniteList.head_eq, ← RegularChaseNode.origin_eq]

/-- The "next" node of the `infiniteRegularChaseDerivationSkeleton` is the result of `Rule.body_database_origin` of the initial rule. -/
theorem infiniteRegularChaseDerivationSkeleton_next_eq {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.infiniteRegularChaseDerivationSkeleton_next = { facts := (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet), origin := rule.body_database_origin obs rules hc rule_mem, facts_contain_origin_result := by intro orig orig_mem; rw [Option.mem_some] at orig_mem; rw [← orig_mem]; apply Set.subset_union_of_subset_right; exact Set.subset_refl } := by
  simp only [infiniteRegularChaseDerivationSkeleton_next, infiniteRegularChaseDerivationSkeleton, InfiniteTriggerList.to_regularChaseDerivationSkeleton, ChaseDerivationSkeleton.next, PossiblyInfiniteList.head_eq, infiniteTriggerList, PossiblyInfiniteList.get?_tail, PossiblyInfiniteList.get?_from_infiniteList, Option.get_some]
  rw [RegularChaseNode.mk.injEq]; constructor
  . rw [InfiniteTriggerList.facts_get_to_ChaseNode_list, InfiniteTriggerList.factSet_at_succ']; simp
  . rw [← RegularChaseNode.origin_eq]; simp

/-- The "next" node of the `infiniteRegularChaseDerivationSkeleton` is the result of `Rule.body_database_origin` of the initial rule. -/
theorem infiniteRegularChaseDerivationSkeleton_facts_next_eq_result_body_database_origin {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.infiniteRegularChaseDerivationSkeleton_next.facts =
    (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet) := by
  rw [infiniteRegularChaseDerivationSkeleton_next_eq]

/-- The head of the `infiniteRegularChaseDerivationSkeleton` contains only finitely many facts because the head is the rule database. -/
theorem infiniteRegularChaseDerivationSkeleton_head_finite {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.infiniteRegularChaseDerivationSkeleton.head.facts.finite := by
  rw [infiniteRegularChaseDerivationSkeleton_head_eq_body_database]; exact rule.body_database.toFactSet.property.left

/-- Every node in the `infiniteRegularChaseDerivationSkeleton` has a finite fact set. -/
theorem infiniteRegularChaseDerivationSkeleton_facts_finite_of_mem {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    ∀ node ∈ cp.infiniteRegularChaseDerivationSkeleton, node.facts.finite := by
  intro node node_mem
  rw [RegularChaseDerivationSkeleton.facts_node_eq_union_initial_and_generated node_mem]
  apply Set.union_finite_of_both_finite
  . exact infiniteRegularChaseDerivationSkeleton_head_finite
  . exact RegularChaseDerivationSkeleton.generatedFacts_finite_of_mem node_mem

/-- The head of the `infiniteRegularChaseDerivationSkeleton` is not empty because there is at least one existential variable in the initial rule. -/
theorem infiniteRegularChaseDerivationSkeleton_terms_next_not_empty {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.infiniteRegularChaseDerivationSkeleton_next.facts.terms ≠ ∅ := by
  rw [infiniteRegularChaseDerivationSkeleton_facts_next_eq_result_body_database_origin]
  rcases List.exists_mem_of_ne_nil _ rule_hc_exis with ⟨v, v_mem⟩
  suffices rule.body_database_trigger.functional_term_for_var (hc rule.body_database_trigger).val (hc rule.body_database_trigger).isLt v v_mem ∈ FactSet.terms (rule.body_database_origin obs rules hc rule_mem).result.toSet by
    intro contra; rw [Set.ext_iff] at contra
    specialize contra (rule.body_database_trigger.functional_term_for_var (hc rule.body_database_trigger).val (hc rule.body_database_trigger).isLt v v_mem)
    conv at contra => right; simp only [EmptyCollection.emptyCollection, Membership.mem]
    rw [← contra]
    rw [FactSet.terms_union]
    apply Set.mem_union_of_mem_right
    exact this
  simp only [FactSet.mem_terms_toSet, ChaseNodeOrigin.result, Rule.body_database_origin, Trigger.fromPreTrigger]
  rw [rule.body_database_trigger.mem_terms_mapped_head_iff _ (hc rule.body_database_trigger).isLt]
  apply Or.inr; apply Or.inr
  apply PreTrigger.mem_fresh_terms_of_functional_for_exis_var

/-- Every node in the `infiniteRegularChaseDerivationSkeleton` has a non-empty fact set. -/
theorem infiniteRegularChaseDerivationSkeleton_terms_not_empty_of_mem {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    ∀ node ∈ cp.infiniteRegularChaseDerivationSkeleton.tail (by simp [infiniteRegularChaseDerivationSkeleton_next_def]), node.facts.terms ≠ ∅ := by
  intro node node_mem
  rw [RegularChaseDerivationSkeleton.facts_node_eq_union_initial_and_generated node_mem]
  intro contra
  apply cp.infiniteRegularChaseDerivationSkeleton_terms_next_not_empty
  apply Set.ext
  intro e
  conv => right; simp only [EmptyCollection.emptyCollection, Membership.mem]
  rw [iff_false]
  intro e_mem
  rw [Set.ext_iff] at contra
  specialize contra e
  conv at contra => right; simp only [EmptyCollection.emptyCollection, Membership.mem]
  rw [iff_false] at contra
  apply contra; rw [FactSet.terms_union]; apply Set.mem_union_of_mem_left; exact e_mem

/-- The `infiniteRegularChaseDerivationSkeleton` also adheres to the head choice since the `infiniteTriggerList` does. (This holds by definition.) -/
theorem infiniteRegularChaseDerivationSkeleton_adheres {cp : PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis} :
    cp.infiniteRegularChaseDerivationSkeleton.adheres_to_headChoice hc := by
  intro node node_mem orig orig_mem
  apply cp.infiniteTriggerList_adheres
  simp only [infiniteRegularChaseDerivationSkeleton, InfiniteTriggerList.to_regularChaseDerivationSkeleton] at node_mem
  simp only [ChaseDerivationSkeleton.mem_iff, PossiblyInfiniteList.get?_from_infiniteList, Option.some_inj] at node_mem
  rcases node_mem with ⟨n, node_mem⟩
  rw [← node_mem] at orig_mem
  cases n with
  | zero => simp at orig_mem
  | succ n =>
    simp only [InfiniteTriggerList.origin_get_succ_to_ChaseNode_list, Option.mem_def, Option.some_inj] at orig_mem
    rw [← orig_mem]; exact InfiniteList.get_mem

end PreCyclicityPrefix

/-- The actual `CyclicityPrefix` definition based on `PreCyclicityPrefix` with extra conditions. -/
structure CyclicityPrefix
    [Inhabited sig.C]
    (obs : ObsolescenceCondition sig.withFreshConstantsForVars)
    (obs_propagates : obs.propagates_under_term_mapping_of_no_fresh_term_occurs)
    (unblk : RepeatableUnblockability obs)
    {rules : RuleSet sig}
    {hc : HeadChoice sig.withFreshConstantsForVars}
    (hc_consistent : hc.consistent_for_same_rule)
    {rule : Rule sig}
    (rule_mem : rule ∈ rules)
    (rule_hc_exis : rule.body_database_trigger.rule.existential_vars_for_head_disjunct (hc rule.body_database_trigger).val (hc rule.body_database_trigger).isLt ≠ [])
    extends PreCyclicityPrefix obs hc_consistent rule_mem rule_hc_exis where
  triggers_unblockable : ∀ orig ∈ triggers, unblk.trigger_unblockable rules.cast_withFreshConstantsForVars hc orig.fst.val
  -- The following is not stated as in the RPC paper but should mean the same thing. The paper states that the constantMappingForRepetition is reversible for each trigger in each repetition. This should be the same as demanding (what we state) that each repetition of the constantMappingForRepetition is reversible for the triggers in the original list. At least this is more convenient to use for us.
  constantMapping_reversible_in_each_step : ∀ i : Nat, ∀ orig ∈ toPreCyclicityPrefix.triggers,
    (toPreCyclicityPrefix.constantMappingForRepetition.repeat_fun i).isReversible orig.fst.val.termSkeleton.toSet

namespace CyclicityPrefix

variable [Inhabited sig.C] {obs : ObsolescenceCondition sig.withFreshConstantsForVars} {obs_propagates : obs.propagates_under_term_mapping_of_no_fresh_term_occurs} {unblk : RepeatableUnblockability obs} {rules : RuleSet sig} {hc : HeadChoice sig.withFreshConstantsForVars} {hc_consistent : hc.consistent_for_same_rule} {rule : Rule sig} {rule_mem : rule ∈ rules} {rule_hc_exis : rule.body_database_trigger.rule.existential_vars_for_head_disjunct (hc rule.body_database_trigger).val (hc rule.body_database_trigger).isLt ≠ []}

/-- Each non-Datalog trigger needs to have a functional term as part of its frontier. Otherwise it could not be unblockable. -/
theorem each_mapped_frontier_in_non_datalog_triggers_features_functional_term
    {cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis} :
    ∀ orig ∈ cp.triggers, orig.fst.val.rule.existential_vars_for_head_disjunct orig.snd.val orig.snd.isLt ≠ [] -> ∃ func ts arity_ok, .func func ts arity_ok ∈ orig.fst.val.mapped_frontier := by
  intro orig orig_mem hc_exis
  suffices ∃ t ∈ orig.fst.val.mapped_frontier, ∀ c, t ≠ .const c by
    rcases this with ⟨t, t_mem, not_const⟩
    cases t with
    | const c => exfalso; apply not_const c; rfl
    | func func ts arity_ok => exists func, ts, arity_ok
  apply Classical.byContradiction; intro contra
  simp only [not_exists, not_and, Classical.not_forall, ne_eq, Decidable.not_not] at contra
  apply RepeatableUnblockability.not_unblockable_of_hc_exis_of_frontier_only_constants obs_propagates (hc.consistent_for_equivalent_triggers_of_consistent_for_same_rule hc_consistent) orig.fst _ contra
  . exact cp.triggers_unblockable orig orig_mem
  . suffices orig.snd.val = (hc orig.fst.val).val by simp only [this] at hc_exis; exact hc_exis
    rw [cp.adheres_to_headChoice]; exact orig_mem

/--
Every functional term that occurs in the triggers of the `CyclicityPrefix` can only feature constants that occur in the frontier of the initial trigger.
This is the case since a functional term can only come from an existential rule. But by the above result, the frontier of this rule then needs to feature
a functional term from the original trigger, which in turn features all constants from the original frontier.
-/
theorem func_term_in_triggers_features_constants_from_initial_frontier {cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis} :
    ∀ i,
    ∀ t ∈ (FiniteTriggerList.result
      (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet)
      (cp.triggers.take i)).terms,
    ∀ func ts arity_ok, t = .func func ts arity_ok -> rule.frontier.map .inr ⊆ t.constants := by
  intro i
  induction i with
  | zero =>
    simp only [List.take_zero, FiniteTriggerList.result_nil, FactSet.terms_union, Set.mem_union_iff]
    intro t t_mem func ts arity_ok t_eq
    suffices t ∈ rule.body_database_trigger.fresh_terms_for_head_disjunct (hc rule.body_database_trigger).val (hc rule.body_database_trigger).isLt by
      suffices ts = rule.body_database_trigger.mapped_frontier by
        rw [t_eq, GroundTerm.constants_func, this, Rule.mapped_frontier_body_database_trigger, ← List.map_map, List.flatMap_map]; simp
      rcases PreTrigger.mem_fresh_terms _ this with ⟨_, _, t_eq2⟩
      rw [t_eq, GroundTerm.func.injEq] at t_eq2; exact t_eq2.right
    cases t_mem with
    | inl t_mem =>
      exfalso
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rcases rule.body_database.toFactSet.property.right f f_mem t t_mem with ⟨_, contra⟩
      rw [t_eq] at contra
      exact GroundTerm.func_neq_const contra
    | inr t_mem =>
    simp only [FactSet.mem_terms_toSet, ChaseNodeOrigin.result, Rule.body_database_origin, Trigger.fromPreTrigger] at t_mem
    rw [rule.body_database_trigger.mem_terms_mapped_head_iff _ (hc rule.body_database_trigger).isLt] at t_mem
    cases t_mem with
    | inl t_mem => exfalso; rcases t_mem with ⟨_, _, contra⟩; rw [t_eq] at contra; exact GroundTerm.func_neq_const (Eq.symm contra)
    | inr t_mem =>
    cases t_mem with
    | inl t_mem =>
      exfalso
      simp only [List.mem_map, Rule.body_database_trigger] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
      rw [t_eq] at t_mem
      exact GroundTerm.func_neq_const (Eq.symm t_mem)
    | inr t_mem => exact t_mem
  | succ i ih =>
    cases Decidable.em (i < cp.triggers.length) with
    | inr lt =>
      rw [List.take_of_length_le (by grind)]
      rw [List.take_of_length_le (by grind)] at ih
      exact ih
    | inl lt =>
      rw [List.take_succ_eq_append_getElem lt]
      rw [FiniteTriggerList.result_append, FiniteTriggerList.result_singleton]
      rw [FactSet.terms_union]
      intro t t_mem; rw [Set.mem_union_iff] at t_mem; cases t_mem with
      | inl t_mem => exact ih _ t_mem
      | inr t_mem =>
        rw [FactSet.mem_terms_toSet] at t_mem
        intro func ts arity_ok t_eq

        simp only [ChaseNodeOrigin.result] at t_mem
        rw [cp.triggers[i].fst.val.mem_terms_mapped_head_iff cp.triggers[i].snd.val cp.triggers[i].snd.isLt] at t_mem
        suffices ∃ func2 ts2 arity_ok2, .func func2 ts2 arity_ok2 ∈ cp.triggers[i].fst.val.mapped_frontier ∧ (.func func2 ts2 arity_ok2 = t ∨ .func func2 ts2 arity_ok2 ∈ ts) by
          rcases this with ⟨func2, ts2, arity_ok2, t2_mem, t2_eq_t_or_mem_ts⟩
          suffices (GroundTerm.func func2 ts2 arity_ok2).constants ⊆ t.constants by
            apply Set.subset_trans _ this
            apply ih _ _ func2 ts2 arity_ok2 rfl
            have triggers_loaded := cp.triggers_loaded
            unfold FiniteTriggerList.loaded at triggers_loaded
            rw [FiniteTriggerList.trigger_property_holds_iff] at triggers_loaded
            apply FactSet.terms_subset_of_subset (triggers_loaded lt)
            rw [FactSet.mem_terms_toSet]
            apply PreTrigger.mem_terms_mapped_body_of_mem_mapped_frontier
            exact t2_mem
          cases t2_eq_t_or_mem_ts with
          | inl t2_eq => rw [t2_eq]; exact Set.subset_refl
          | inr t2_mem_ts => intro c c_mem; rw [t_eq, GroundTerm.constants_func]; exact List.mem_flatMap_of_mem t2_mem_ts c_mem
        cases t_mem with
        | inl t_mem => rcases t_mem with ⟨_, _, contra⟩; simp only [t_eq] at contra; exfalso; exact GroundTerm.func_neq_const (Eq.symm contra)
        | inr t_mem => cases t_mem with
          | inl t_mem =>
            exists func, ts, arity_ok; rw [← t_eq]
            simp only [PreTrigger.mapped_frontier, true_or, and_true]
            rw [List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
            rw [← t_mem]; apply List.mem_map_of_mem
            rw [Rule.mem_frontier_iff_mem_frontier_for_head]
            exact ⟨_, _, v_mem⟩
          | inr t_mem =>
            rcases PreTrigger.mem_fresh_terms _ t_mem with ⟨v, v_mem, t_mem⟩
            suffices ∃ func2 ts2 arity_ok2, .func func2 ts2 arity_ok2 ∈ cp.triggers[i].fst.val.mapped_frontier by
              rcases this with ⟨func2, ts2, arity_ok2, t2_mem⟩; exists func2, ts2, arity_ok2; constructor; exact t2_mem
              apply Or.inr
              rw [t_eq, GroundTerm.func.injEq] at t_mem
              rw [t_mem.right]; exact t2_mem
            apply cp.each_mapped_frontier_in_non_datalog_triggers_features_functional_term
            . simp
            . intro contra; simp [contra] at v_mem

/--
There is a constant in the initial mapped frontier that is mapped to a functional term by `constantMappingForRepetition`
such that the constant occurs again in this functional term.
This is used to show that applying the mapping repeatedly will therefore grow the term indefinitely.
-/
theorem constantMappingForRepetition_on_some_initial_frontier_constant_contains_this_contant
    {cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis} :
    ∃ c ∈ rule.frontier.map .inr,
    ∃ func ts arity_ok, cp.constantMappingForRepetition c = .func func ts arity_ok ∧ c ∈ (GroundTerm.func func ts arity_ok).constants := by
  rcases cp.each_mapped_frontier_in_non_datalog_triggers_features_functional_term cp.last_trigger cp.last_trigger_mem (by
      suffices cp.last_trigger.snd.val = (hc rule.body_database_trigger).val by
        simp only [cp.rule_last_trigger, this]
        exact rule_hc_exis
      rw [cp.adheres_to_headChoice cp.last_trigger cp.last_trigger_mem]
      suffices cp.last_trigger.fst.val.rule = rule.body_database_trigger.rule by rw [hc_consistent this]
      rw [cp.rule_last_trigger]; simp [Rule.body_database_trigger])
    with ⟨func, ts, arity_ok, mem_mapped_frontier⟩
  have mem_mapped_frontier' := mem_mapped_frontier -- we copy the original form of the statement because we need it at the end of the proof
  rw [cp.last_trigger_eq, ← PreTrigger.apply_mapping_after_mapped_frontier] at mem_mapped_frontier
  simp only [Rule.mapped_frontier_body_database_trigger, List.map_map, List.mem_map] at mem_mapped_frontier
  rcases mem_mapped_frontier with ⟨v, v_mem, mem_mapped_frontier⟩
  exists .inr v; constructor; exact List.mem_map_of_mem v_mem
  exists func, ts, arity_ok; constructor
  . rw [← mem_mapped_frontier]; simp
  . apply cp.func_term_in_triggers_features_constants_from_initial_frontier (cp.triggers.length - 1) (.func func ts arity_ok) _ func ts arity_ok rfl (List.mem_map_of_mem v_mem)
    have loaded := cp.last_trigger_loaded
    rw [List.dropLast_eq_take] at loaded
    apply FactSet.terms_subset_of_subset loaded
    rw [FactSet.mem_terms_toSet]
    apply PreTrigger.mem_terms_mapped_body_of_mem_mapped_frontier
    exact mem_mapped_frontier'

/-- There is a term in the database origin result that keeps growing along the `constantMappingForRepetition`. -/
theorem constantMappingForRepetition_growing {cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis} :
    ∃ t ∈ (rule.body_database_origin obs rules hc rule_mem).result.flatMap GeneralizedAtom.terms,
    ∀ n, ((cp.constantMappingForRepetition.repeat_fun n).apply_ground_term t).depth ≥ n.succ := by
  rcases List.exists_mem_of_ne_nil _ rule_hc_exis with ⟨v, v_mem⟩
  exists rule.body_database_trigger.functional_term_for_var (hc rule.body_database_trigger).val (hc rule.body_database_trigger).isLt v v_mem
  simp only [ChaseNodeOrigin.result, Rule.body_database_origin, Trigger.fromPreTrigger]
  rw [rule.body_database_trigger.mem_terms_mapped_head_iff _ (hc rule.body_database_trigger).isLt]
  constructor
  . apply Or.inr; apply Or.inr
    exact PreTrigger.mem_fresh_terms_of_functional_for_exis_var v_mem
  . rcases cp.constantMappingForRepetition_on_some_initial_frontier_constant_contains_this_contant
      with ⟨c, c_mem_frontier, func, ts, arity_ok, map_c_eq, c_mem_func⟩
    suffices ∀ n, (cp.constantMappingForRepetition.repeat_fun n c).depth ≥ n by
      intro n; specialize this n
      simp only [PreTrigger.functional_term_for_var, ConstantMapping.apply_ground_term_func, GroundTerm.depth_func]
      rw [Nat.add_comm]; apply Nat.succ_le_succ
      apply Nat.le_trans this
      apply List.le_max?_getD_of_mem
      apply List.mem_map_of_mem
      rw [← (cp.constantMappingForRepetition.repeat_fun n).apply_ground_term_constant c]
      apply List.mem_map_of_mem
      rw [Rule.mapped_frontier_body_database_trigger, ← List.map_map]
      apply List.mem_map_of_mem
      exact c_mem_frontier
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ConstantMapping.repeat_succ', Function.comp_apply]
      rw [map_c_eq, ConstantMapping.apply_ground_term_func, GroundTerm.depth_func]
      rw [Nat.add_comm]; apply Nat.succ_le_succ
      apply Nat.le_trans ih
      suffices ∀ s, c ∈ s.constants ->
          (cp.constantMappingForRepetition.repeat_fun n c).depth ≤ ((cp.constantMappingForRepetition.repeat_fun n).apply_ground_term s).depth by
        rw [GroundTerm.constants_func, List.mem_flatMap] at c_mem_func; rcases c_mem_func with ⟨s, s_mem, c_mem_s⟩
        apply Nat.le_trans (this s c_mem_s)
        apply List.le_max?_getD_of_mem; apply List.mem_map_of_mem; apply List.mem_map_of_mem; exact s_mem
      intro s; induction s with
      | const d => grind
      | func func2 ts2 arity_ok2 ih2 =>
        rw [GroundTerm.constants_func, List.mem_flatMap, ConstantMapping.apply_ground_term_func, GroundTerm.depth_func]
        intro ⟨s2, s2_mem, c_mem_s2⟩
        rw [Nat.add_comm]; apply Nat.le_succ_of_le
        apply Nat.le_trans (ih2 s2 s2_mem c_mem_s2)
        apply List.le_max?_getD_of_mem; apply List.mem_map_of_mem; apply List.mem_map_of_mem; exact s2_mem

/-- For each n, the last trigger in the n-th sequence produces a term of depth at least n + 2. -/
theorem infiniteList_of_finiteLists_growing {cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis} :
    ∀ n, ∃ t ∈ ((cp.infiniteList_of_finiteLists.get n).toList.getLast (NonEmptyList.toList_ne_nil)).result.flatMap GeneralizedAtom.terms, t.depth ≥ n + 2 := by
  rcases cp.constantMappingForRepetition_growing with ⟨t, t_mem, t_depth_ge⟩
  intro n
  specialize t_depth_ge n.succ
  exists (cp.constantMappingForRepetition.repeat_fun n.succ).apply_ground_term t
  constructor
  . rw [List.getLast_eq_getElem]
    simp only [PreCyclicityPrefix.infiniteList_of_finiteLists, InfiniteList.compute_get]
    rw [PreCyclicityPrefix.result_ithRepetition (by rw [PreCyclicityPrefix.length_ithRepetition]; apply Nat.pred_lt_self; grind [cp.triggers_ne_nil])]
    simp only [PreCyclicityPrefix.length_ithRepetition]
    rw [← List.getLast_eq_getElem cp.triggers_ne_nil]
    rw [List.mem_flatMap] at t_mem; rcases t_mem with ⟨a, a_mem, t_mem⟩
    rw [← PreCyclicityPrefix.last_trigger.eq_def, PreCyclicityPrefix.result_last_trigger]
    simp only [List.flatMap_map, List.mem_flatMap]
    exists a; constructor; exact a_mem
    simp only [ConstantMapping.apply_fact]
    rw [← TermMapping.apply_generalized_atom_compose']
    rw [← ConstantMapping.apply_ground_term_compose]
    rw [← ConstantMapping.repeat_succ']
    simp only [TermMapping.apply_generalized_atom]
    exact List.mem_map_of_mem t_mem
  . exact t_depth_ge

/-- For each n, we can find a trigger in the generated infinite list that yields a term of depth at least n. -/
theorem infiniteTriggerList_growing {cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis} :
    ∀ n, ∃ trg ∈ cp.infiniteTriggerList, ∃ t ∈ trg.result.flatMap GeneralizedAtom.terms, t.depth ≥ n := by
  intro n; rcases cp.infiniteList_of_finiteLists_growing n with ⟨t, t_mem, t_depth_ge⟩
  exists (cp.infiniteList_of_finiteLists.get n).toList.getLast (NonEmptyList.toList_ne_nil)
  constructor
  . simp only [PreCyclicityPrefix.infiniteTriggerList]
    rw [InfiniteList.mem_cons]; apply Or.inr
    simp only [InfiniteTriggerList.fromFiniteLists]
    rw [InfiniteList.fromNonEmptyLists_mem_iff]
    exists cp.infiniteList_of_finiteLists.get n
    constructor
    . exact InfiniteList.get_mem
    . simp
  . exists t; grind

/-- For each number n, we can find a node in the generated chase derivation that has a term of depth at least n. -/
theorem infiniteRegularChaseDerivationSkeleton_growing {cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis} :
    ∀ n, ∃ node ∈ cp.infiniteRegularChaseDerivationSkeleton, ∃ t ∈ node.facts.terms, t.depth ≥ n := by
  intro n; rcases cp.infiniteTriggerList_growing n with ⟨trg, trg_mem, t, t_mem, t_depth_ge⟩
  rw [InfiniteList.mem_iff] at trg_mem; rcases trg_mem with ⟨i, trg_mem⟩
  exists (cp.infiniteRegularChaseDerivationSkeleton.branch.get? i.succ).get
    (by simp [PreCyclicityPrefix.infiniteRegularChaseDerivationSkeleton, InfiniteTriggerList.to_regularChaseDerivationSkeleton])
  constructor
  . rw [ChaseDerivationSkeleton.mem_iff]; exists i.succ; simp
  . exists t
    constructor
    . simp only [PreCyclicityPrefix.infiniteRegularChaseDerivationSkeleton, InfiniteTriggerList.to_regularChaseDerivationSkeleton, PossiblyInfiniteList.get?_from_infiniteList, Option.get_some]
      let node := (cp.infiniteTriggerList.to_chaseNode_list rule.body_database.toFactSet.val).get i.succ
      apply FactSet.terms_subset_of_subset (node.facts_contain_origin_result ((ChaseNode.origin node).get (by simp only [node]; rw [cp.infiniteTriggerList.origin_get_succ_to_ChaseNode_list]; simp)) (by simp [ChaseNode.origin]))
      rw [FactSet.mem_terms_toSet]
      simp only [node, InfiniteTriggerList.origin_get_succ_to_ChaseNode_list, Option.get_some]
      rw [trg_mem]; exact t_mem
    . exact t_depth_ge

/-- Every trigger in each repetition is unblockable. -/
theorem infiniteList_of_finiteLists_unblockable {cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis} :
    ∀ i, ∀ orig ∈ (cp.infiniteList_of_finiteLists.get i).toList, unblk.trigger_unblockable rules.cast_withFreshConstantsForVars hc orig.fst.val := by
  intro i orig orig_mem
  simp only [PreCyclicityPrefix.infiniteList_of_finiteLists, InfiniteList.compute_get, PreCyclicityPrefix.ithRepetition, NonEmptyList.toList_from_ne_nil, List.mem_map] at orig_mem
  rcases orig_mem with ⟨orig2, orig2_mem, orig_eq⟩
  simp only [← orig_eq]
  apply unblk.repeatable
  . apply cp.constantMapping_reversible_in_each_step; exact orig2_mem
  . apply cp.triggers_unblockable; exact orig2_mem

/-- Every trigger in the `PreCyclicityPrefix.infiniteTriggerList` is unblockable. -/
theorem infiniteTriggerList_unblockable {cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis} :
    ∀ orig ∈ cp.infiniteTriggerList, Trigger.kbUnblockable (rule.body_kb rules) hc orig.fst.val := by
  unfold PreCyclicityPrefix.infiniteTriggerList
  intro orig orig_mem
  cases InfiniteList.mem_cons.mp orig_mem with
  | inl orig_mem => rw [orig_mem]; exact cp.body_database_trigger_unblockable
  | inr orig_mem =>
    let property : ChaseNodeOrigin obs rules.cast_withFreshConstantsForVars -> FactSet sig.withFreshConstantsForVars -> Prop :=
      fun orig _ => Trigger.kbUnblockable (rule.body_kb rules) hc orig.fst.val
    have prop_holds : ∀ n, FiniteTriggerList.trigger_property_holds property (InfiniteTriggerList.startForFiniteList cp.infiniteList_of_finiteLists ∅ n) (cp.infiniteList_of_finiteLists.get n).toList := by
      intro n
      rw [FiniteTriggerList.trigger_property_holds_iff]
      intro i lt
      simp only [property]
      apply unblk.rsUnblockable_of_trigger_unblockable obs_propagates (hc.consistent_for_equivalent_triggers_of_consistent_for_same_rule hc_consistent)
      . apply cp.infiniteList_of_finiteLists_unblockable n; simp
      . simp [Rule.body_kb]
    have still_holds := InfiniteTriggerList.fromFiniteLists_trigger_property_preserved prop_holds
    rw [InfiniteList.mem_iff] at orig_mem; rcases orig_mem with ⟨n, orig_mem⟩
    specialize still_holds n
    rw [orig_mem] at still_holds
    exact still_holds

/-- By repeating the `CyclicityPrefix` indefinitely, we obtain a `CyclicityBranch`. -/
def to_cyclicityBranch (cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis) : CyclicityBranch obs (rule.body_kb rules) hc :=
  let deriv := cp.infiniteRegularChaseDerivationSkeleton
  {
    branch := deriv.branch,
    isSome_head := deriv.isSome_head,
    triggers_exist := deriv.triggers_exist
    adheres_to_headChoice := cp.infiniteRegularChaseDerivationSkeleton_adheres
    triggers_loaded := by
      intro cd2 suffix next next_mem
      rcases InfiniteTriggerList.suffix_of_to_regularChaseDerivationSkeleton_implies _ suffix with ⟨i, head_eq, next_props⟩
      specialize next_props next next_mem
      exists cp.infiniteTriggerList.get i; constructor; exact next_props.right
      rw [head_eq]
      exact cp.infiniteTriggerList_loaded i
    growing := by
      intro cd2 suffix
      have next_some : cd2.next.isSome := cp.infiniteRegularChaseDerivationSkeleton_next_some_of_suffix suffix
      let next := cd2.next.get next_some
      suffices ∃ t ∈ next.facts.terms, ∀ s ∈ next.facts.terms, s.depth ≤ t.depth by
        rcases this with ⟨t, t_mem, le_t⟩
        rcases cp.infiniteRegularChaseDerivationSkeleton_growing t.depth.succ with ⟨node2, node2_mem, t2, t2_mem, t2_depth_ge⟩
        cases RegularChaseDerivationSkeleton.mem_suffix_of_mem (cd1 := cd2.tail next_some) (PossiblyInfiniteList.IsSuffix_trans cd2.branch.IsSuffix_tail suffix) node2 node2_mem with
        | inl node2_sub =>
          simp only [ChaseDerivationSkeleton.head_tail'] at node2_sub
          specialize le_t t2 (by apply FactSet.terms_subset_of_subset node2_sub; exact t2_mem)
          grind
        | inr node2_mem =>
          exists node2; constructor; exact (cd2.tail next_some).mem_of_mem_suffix cd2.branch.IsSuffix_tail _ node2_mem; exists t2; constructor
          . intro contra; specialize le_t t2 (by apply FactSet.terms_subset_of_subset (RegularChaseDerivationSkeleton.facts_node_subset_every_mem _ (cd2.next_mem_of_mem _ (by simp [next]))); exact contra); grind
          . exact t2_mem
      suffices next.facts.finite by
        rcases FactSet.terms_finite_of_finite _ this with ⟨l_terms, _, terms_eq⟩
        exists l_terms.maxOn GroundTerm.depth (by
          intro contra
          apply cp.infiniteRegularChaseDerivationSkeleton_terms_not_empty_of_mem next (by
            rw [cp.infiniteRegularChaseDerivationSkeleton.mem_tail_iff (node := next)]
            exists cd2; constructor; exact suffix; simp only [next]; apply Eq.symm; apply Option.some_get)
          apply Set.ext; intro e
          conv => right; simp only [EmptyCollection.emptyCollection, Membership.mem]
          rw [iff_false, ← terms_eq, contra]
          simp)
        constructor
        . rw [← terms_eq]; exact List.maxOn_mem
        . intro s s_mem; apply List.le_apply_maxOn_of_mem; rw [terms_eq]; exact s_mem
      exact cp.infiniteRegularChaseDerivationSkeleton_facts_finite_of_mem _ (ChaseDerivationSkeleton.mem_of_mem_suffix suffix _ (cd2.next_mem_of_mem _ (by simp [next])))
    unblockable := by
      show ∀ node ∈ deriv, ∀ orig ∈ node.origin, (orig.fst.val.kbUnblockable (rule.body_kb rules) hc)
      intro node node_mem orig orig_mem
      simp only [deriv, PreCyclicityPrefix.infiniteRegularChaseDerivationSkeleton, InfiniteTriggerList.to_regularChaseDerivationSkeleton] at node_mem
      simp only [ChaseDerivationSkeleton.mem_iff, PossiblyInfiniteList.get?_from_infiniteList, Option.some_inj] at node_mem
      rcases node_mem with ⟨n, node_mem⟩
      rw [← node_mem, ← RegularChaseNode.origin_eq] at orig_mem
      cases n with
      | zero => simp at orig_mem
      | succ n =>
        simp only [InfiniteTriggerList.origin_get_succ_to_ChaseNode_list, Option.mem_def, Option.some_inj] at orig_mem
        rw [← orig_mem]
        apply cp.infiniteTriggerList_unblockable
        exact InfiniteList.get_mem
    database_first := ⟨cp.infiniteRegularChaseDerivationSkeleton_head_eq_body_database, cp.infiniteRegularChaseDerivationSkeleton_origin_head_eq_none⟩
  }

/-- If a rule set admist a `CyclicityPrefix`, then we can also build a `CyclicityBranch` and therefore we witness that the `RuleSet.neverTerminates`. -/
theorem neverTerminates_of_cyclicityBranch (cp : CyclicityPrefix obs obs_propagates unblk hc_consistent rule_mem rule_hc_exis) :
    rules.cast_withFreshConstantsForVars.neverTerminates obs (RegularChaseNode obs rules.cast_withFreshConstantsForVars) :=
  cp.to_cyclicityBranch.neverTerminates_of_cyclicityBranch

end CyclicityPrefix

