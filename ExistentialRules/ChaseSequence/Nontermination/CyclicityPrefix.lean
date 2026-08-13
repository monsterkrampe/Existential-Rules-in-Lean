/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Nontermination.RepeatableUnblockability
public import ExistentialRules.ChaseSequence.Termination.Basic
public import ExistentialRules.Terms.Cyclic

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

/-- For a signature `withFreshConstantsForVars`, we can turn a `GroundSubstitution` into a `ConstantMapping`. -/
def GroundSubstitution.toConstantMapping_for_sig_withFreshConstantsForVars (subs : GroundSubstitution sig.withFreshConstantsForVars) :
    ConstantMapping sig.withFreshConstantsForVars
| .inl c => .const (.inl c) -- we leave original constants untouched
| .inr v => subs v

/-- We define a structure, which is almost a `CyclicityPrefix` (missing a few conditions). We do this mainly to add some auxiliary definitions that we can use to express the remaining conditions more easily. -/
structure PreCyclicityPrefix [Inhabited sig.C] (obs : ObsolescenceCondition sig.withFreshConstantsForVars) (rules : RuleSet sig) (hc : HeadChoice sig.withFreshConstantsForVars) (rule : Rule sig)
    extends RegularChaseDerivationSkeleton obs rules.cast_withFreshConstantsForVars where
  -- the first conditions are also found in the `CyclicityDerivation`; `growing` and `unblockable` are missing though
  adheres_to_headChoice : ChaseDerivationSkeleton.adheres_to_headChoice toChaseDerivationSkeleton hc
  triggers_loaded : ∀ cd2, cd2 <:+ toChaseDerivationSkeleton -> ∀ next ∈ cd2.next, ∃ orig ∈ next.origin, orig.fst.val.loaded cd2.head.facts
  -- from here things are different
  finite : toChaseDerivationSkeleton.terminates
  first_trigger : ∃ orig, ∃ (orig_mem : orig ∈ toChaseDerivationSkeleton.head.origin),
    orig.fst.val = rule.body_database_trigger ∧
    orig.fst.val.unblockable rules.cast_withFreshConstantsForVars hc ∧
    toChaseDerivationSkeleton.head.facts = rule.body_database.toFactSet.val ∪ (RegularChaseNode.regularChaseNodeInstance.origin_result toChaseDerivationSkeleton.head (by simp only [ChaseNode.origin]; rw [orig_mem]; simp)).toSet

namespace PreCyclicityPrefix

variable [Inhabited sig.C] {obs : ObsolescenceCondition sig.withFreshConstantsForVars} {rules : RuleSet sig} {hc : HeadChoice sig.withFreshConstantsForVars} {rule : Rule sig}

/-- Every node in the `PreCyclicityPrefix` must have an origin. -/
theorem isSome_origin_of_mem {cd : PreCyclicityPrefix obs rules hc rule} : ∀ node ∈ cd.toChaseDerivationSkeleton, node.origin.isSome := by
  intro node node_mem
  rw [cd.mem_iff_eq_head_or_mem_tail] at node_mem
  cases node_mem with
  | inl node_mem => rw [node_mem]; rcases cd.first_trigger with ⟨orig, orig_mem, _⟩; rw [orig_mem]; simp
  | inr node_mem => simp only [cd.mem_tail_iff] at node_mem; rcases node_mem with ⟨_, cd2, suf, mem⟩; apply cd2.isSome_origin_next; exact mem

/-- Obtain the origin of a node (which must exist). -/
def origin_of_mem {cd : PreCyclicityPrefix obs rules hc rule} {node : RegularChaseNode obs rules.cast_withFreshConstantsForVars}
    (node_mem : node ∈ cd.toChaseDerivationSkeleton) :=
  node.origin.get (cd.isSome_origin_of_mem node node_mem)

/-- The origin of the last node (the prefix is finite). -/
def last_origin (cd : PreCyclicityPrefix obs rules hc rule) := cd.origin_of_mem (cd.last_mem cd.finite)

/-- In the end, we want to repeat the prefix using a constant mapping expressing the mapping from the first to the last trigger. This mapping is what is defined here. -/
def constantMappingForRepetition (cd : PreCyclicityPrefix obs rules hc rule) : ConstantMapping sig.withFreshConstantsForVars :=
  cd.last_origin.fst.val.subs.toConstantMapping_for_sig_withFreshConstantsForVars

end PreCyclicityPrefix

/-- The actual `CyclicityPrefix` extending the `PreCyclicityPrefix` with the remaining conditions. -/
structure CyclicityPrefix [Inhabited sig.C] (obs : ObsolescenceCondition sig.withFreshConstantsForVars) (unblk : RepeatableUnblockability obs) (rules : RuleSet sig) (hc : HeadChoice sig.withFreshConstantsForVars) (rule : Rule sig)
    extends PreCyclicityPrefix obs rules hc rule where
  -- NOTE: we only demand unblockability on all triggers but the first one. This is indeed correct and necessary.
  triggers_unblockable : ∀ h, ∀ node ∈ toChaseDerivationSkeleton.tail h, ∀ orig ∈ node.origin, unblk.trigger_unblockable rules.cast_withFreshConstantsForVars hc orig.fst.val
  last_trigger : toPreCyclicityPrefix.last_origin.fst.val.rule = rule.cast_withFreshConstantsForVars ∧ ∃ term ∈ (toPreCyclicityPrefix.last_origin.fst.val.output_for_headChoice hc).flatMap GeneralizedAtom.terms, PreGroundTerm.ruleCyclic rule.cast_withFreshConstantsForVars term.val
  constantMapping_reversible_in_each_step : ∀ h, ∀ node ∈ toChaseDerivationSkeleton.tail h, ∀ orig ∈ node.origin, ∀ j : Nat,
    toPreCyclicityPrefix.constantMappingForRepetition.isReversible
      {rule := orig.fst.val.rule, subs := (toPreCyclicityPrefix.constantMappingForRepetition.apply_ground_term.repeat_fun j) ∘ orig.fst.val.subs : PreTrigger _}.termSkeleton.toSet

