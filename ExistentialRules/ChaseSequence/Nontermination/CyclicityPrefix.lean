/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Nontermination.TermSkeleton
public import ExistentialRules.ChaseSequence.Nontermination.RepeatableUnblockability
public import ExistentialRules.ChaseSequence.Nontermination.ReversibleConstantMappings
public import ExistentialRules.Terms.Cyclic

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

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- This turns a `VarOrConst` into the constant Sum type of `Signature.withFreshConstants`. -/
def VarOrConst.toConst_withFreshConstantsForVars : TermMapping (VarOrConst sig) sig.withFreshConstantsForVars.C
| .const c => .inl c
| .var v => .inr v

/-- Change the constant of a `VarOrConst` into the Sum type of `Signature.withFreshConstants`. -/
def VarOrConst.cast_withFreshConstantsForVars : TermMapping (VarOrConst sig) (VarOrConst sig.withFreshConstantsForVars)
| .const c => .const (.inl c)
| .var v => .var v

/-- Change the constant of a `Rule` into the Sum type of `Signature.withFreshConstants`. -/
def Rule.cast_withFreshConstantsForVars (r : Rule sig) : Rule sig.withFreshConstantsForVars where
  body := VarOrConst.cast_withFreshConstantsForVars.apply_generalized_atom_list r.body
  head := r.head.map VarOrConst.cast_withFreshConstantsForVars.apply_generalized_atom_list

/-- Change the constant of a `RuleSet` into the Sum type of `Signature.withFreshConstants`. -/
def RuleSet.cast_withFreshConstantsForVars (rs : RuleSet sig) : RuleSet sig.withFreshConstantsForVars :=
  rs.map Rule.cast_withFreshConstantsForVars

/-- The `body_database` of a rule is the body where each variable is replaced by a fresh constant.
We achieve this by extending the signature and mapping all terms in the body using `VarOrConst.cast_withFreshConstantsForVars`. -/
def Rule.body_database (r : Rule sig) : Database sig.withFreshConstantsForVars :=
  ⟨(VarOrConst.toConst_withFreshConstantsForVars.apply_generalized_atom_list r.body).toSet, List.finite_toSet _⟩

/-- The trigger for a rule that matches its `body_database`. -/
def Rule.body_database_trigger (r : Rule sig) : PreTrigger sig.withFreshConstantsForVars where
  rule := r.cast_withFreshConstantsForVars
  subs := .const ∘ .inr

/-- The `body_database_trigger` is loaded for the `body_database`. -/
theorem Rule.body_database_trigger_loaded {r : Rule sig} : r.body_database_trigger.loaded r.body_database.toFactSet.val := by
  unfold body_database body_database_trigger
  intro f f_mem
  simp only [PreTrigger.mapped_body, List.mem_toSet, TermMapping.mem_apply_generalized_atom_list] at f_mem
  rcases f_mem with ⟨b, b_mem, f_mem⟩
  simp only [cast_withFreshConstantsForVars, TermMapping.mem_apply_generalized_atom_list] at b_mem
  rcases b_mem with ⟨a, a_mem, b_mem⟩
  simp only [Database.toFactSet, List.mem_toSet]
  exists VarOrConst.toConst_withFreshConstantsForVars.apply_generalized_atom a
  constructor
  . apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_list; exact a_mem
  . rw [f_mem, b_mem]
    rw [FunctionFreeFact.toFact_eq]
    rw [← TermMapping.apply_generalized_atom_compose', ← TermMapping.apply_generalized_atom_compose']
    apply TermMapping.apply_generalized_atom_congr_left
    intro t t_mem
    cases t <;> simp [VarOrConst.cast_withFreshConstantsForVars, VarOrConst.toConst_withFreshConstantsForVars, GroundSubstitution.apply_var_or_const]

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
We define a structure, which is almost a `CyclicityPrefix` (missing some last conditions).
We split this mainly to add some auxiliary definitions that we can use to express the remaining conditions more easily.
-/
structure PreCyclicityPrefix
    [Inhabited sig.C]
    (obs : ObsolescenceCondition sig.withFreshConstantsForVars)
    {rules : RuleSet sig}
    (hc : HeadChoice sig.withFreshConstantsForVars)
    {rule : Rule sig}
    (rule_mem : rule ∈ rules) where
  body_database_trigger_unblockable : (Trigger.fromPreTrigger rule.body_database_trigger obs).unblockable rules.cast_withFreshConstantsForVars hc
  -- this list does not include the initial database trigger
  triggers : FiniteTriggerList obs rules.cast_withFreshConstantsForVars
  -- the first conditions are also found in the `CyclicityDerivation`; `growing` and `unblockable` are missing though
  adheres_to_headChoice : triggers.adheres_to_headChoice hc
  triggers_loaded : triggers.loaded (rule.body_database.toFactSet.val ∪ (rule.body_database_origin obs rules hc rule_mem).result.toSet)
  -- from here things are different
  ex_last_trigger : ∃ last ∈ triggers.getLast?, last.fst.val.rule = rule.cast_withFreshConstantsForVars ∧
    ∃ term ∈ last.result.flatMap GeneralizedAtom.terms, PreGroundTerm.ruleCyclic rule.cast_withFreshConstantsForVars term.val

namespace PreCyclicityPrefix

variable [Inhabited sig.C] {obs : ObsolescenceCondition sig.withFreshConstantsForVars} {rules : RuleSet sig} {hc : HeadChoice sig.withFreshConstantsForVars} {rule : Rule sig} {rule_mem : rule ∈ rules}

/-- The triggers are not empty. -/
theorem triggers_ne_nil {cp : PreCyclicityPrefix obs hc rule_mem} : cp.triggers ≠ [] := by
  rcases cp.ex_last_trigger with ⟨_, mem, _⟩
  intro contra; simp [contra] at mem

/-- We can cast the triggers into a `FiniteNonEmptyTriggerList`. -/
def to_FiniteNonEmptyTriggerList (cp : PreCyclicityPrefix obs hc rule_mem) :
    FiniteNonEmptyTriggerList obs rules.cast_withFreshConstantsForVars :=
  NonEmptyList.from_ne_nil cp.triggers cp.triggers_ne_nil

/-- Since the trigger list is not empty, we can get the last trigger. -/
def last_trigger (cp : PreCyclicityPrefix obs hc rule_mem) : ChaseNodeOrigin obs rules.cast_withFreshConstantsForVars :=
  cp.triggers.getLast cp.triggers_ne_nil

/--
In the end, we want to repeat the prefix using a constant mapping expressing the mapping from the database trigger to the last trigger.
This mapping is what is defined here.
-/
def constantMappingForRepetition (cp : PreCyclicityPrefix obs hc rule_mem) : ConstantMapping sig.withFreshConstantsForVars :=
  cp.last_trigger.fst.val.subs.toConstantMapping_for_sig_withFreshConstantsForVars

end PreCyclicityPrefix

structure CyclicityPrefix
    [Inhabited sig.C]
    (obs : ObsolescenceCondition sig.withFreshConstantsForVars)
    (unblk : RepeatableUnblockability obs)
    {rules : RuleSet sig}
    (hc : HeadChoice sig.withFreshConstantsForVars)
    {rule : Rule sig}
    (rule_mem : rule ∈ rules)
    extends PreCyclicityPrefix obs hc rule_mem where
  triggers_unblockable : ∀ orig ∈ triggers, unblk.trigger_unblockable rules.cast_withFreshConstantsForVars hc orig.fst.val
  constantMapping_reversible_in_each_step : ∀ orig ∈ triggers, ∀ j : Nat,
    toPreCyclicityPrefix.constantMappingForRepetition.isReversible
      (orig.fst.val.extend_with_groundTermMapping
        (Function.repeat_fun toPreCyclicityPrefix.constantMappingForRepetition.apply_ground_term j)).termSkeleton.toSet

