/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.Terms.GroundTerm
public import ExistentialRules.AtomsAndRules.Basic

/-!
# Facts

A `Fact` is a `GeneralizedAtom` with `GroundTerm`s.
-/

public section

abbrev Fact (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := GeneralizedAtom sig (GroundTerm sig)

namespace Fact

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The `Fact.constants` are the constants of all terms. -/
@[expose]
def constants (f : Fact sig) : List sig.C := f.terms.flatMap GroundTerm.constants

/-- The `Fact.function_symbols` are the function symbols of all terms. -/
@[expose]
def function_symbols (f : Fact sig) : List (SkolemFS sig) := f.terms.flatMap GroundTerm.functions

/-- A `Fact` is function free, if each term is a constant. -/
@[expose]
def isFunctionFree (f : Fact sig) : Prop := ∀ t, t ∈ f.terms -> ∃ c, t = GroundTerm.const c

end Fact

