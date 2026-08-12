/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.Function.InjectiveSurjective
public import ExistentialRules.ChaseSequence.Termination.ConstantMappings.Basic

/-!
# Reversible Constant Mappings

Here, we define what it means for a `ConstantMapping` to be reversible.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace ConstantMapping

/-- This is Definition 10 from the [RPC] paper but we do not demand here that `ts` is closed under subterms. -/
def isReversible (g : ConstantMapping sig) (ts : Set (GroundTerm sig)) : Prop :=
  g.apply_ground_term.injectiveSet ts ∧
  ∀ c : sig.C, .const c ∈ ts -> ∀ s ∈ (g c).subterms,
    ∀ func_u ts_u arity_ok_u, GroundTerm.func func_u ts_u arity_ok_u ∈ ts ->
    g.apply_ground_term (GroundTerm.func func_u ts_u arity_ok_u) ≠ s

end ConstantMapping


