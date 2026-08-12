/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Nontermination.RepeatableUnblockability
public import ExistentialRules.ChaseSequence.Termination.Basic

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

/-- In particular, we can simply use the variables as fresh constants. Think of this as constants that just happen to have the same name as the variables. -/
abbrev Signature.withFreshConstantsForVars (sig : Signature) : Signature := sig.withFreshConstants sig.V

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- This turns a `VarOrConst` into the constant Sum type of `Signature.withFreshConstants`. -/
def VarOrConst.cast_withFreshConstantsForVars : TermMapping (VarOrConst sig) sig.withFreshConstantsForVars.C
| .const c => .inl c
| .var v => .inr v

/-- The `body_database` of a rule is the body where each variable is replaced by a fresh constant.
We achieve this by extending the signature and mapping all terms in the body using `VarOrConst.cast_withFreshConstantsForVars`. -/
def Rule.body_database (r : Rule sig) : Database sig.withFreshConstantsForVars :=
  ⟨(VarOrConst.cast_withFreshConstantsForVars.apply_generalized_atom_list r.body).toSet, List.finite_toSet _⟩

