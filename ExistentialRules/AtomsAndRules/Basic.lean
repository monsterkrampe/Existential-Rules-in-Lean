/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.Terms.Basic

/-!
# Atoms, Facts, Rules and the like

In this directory, we define the next layers of building blocks above terms.
This includes first and foremost `FunctionFreeAtom` and `Fact` but also
`Rule`, `RuleSet`, `Database` and `KnowledgeBase` to name a few.

The atom-like datastructures are all expressed in terms of a `GeneralizedAtom`. This will turn out convenient when defining substitutions and homomorphisms next since these can (for the most part) just be defines as generic mapping over `GeneralizedAtom`.
-/

public section

/-- A `GeneralizedAtom` consists of a predicate symbol and a list of terms of an arbitrary type such that the number of terms matches the predicate's arity. -/
structure GeneralizedAtom (sig : Signature) (T : Type u) [DecidableEq sig.P] where
  predicate : sig.P
  terms : List T
  arity_ok : terms.length = sig.arity predicate
deriving DecidableEq

/-- If two atoms have the same predicate, then they thave an equal number of terms-/
theorem GeneralizedAtom.length_terms_eq_of_predicate_eq
    {sig: Signature} {T : Type u} [DecidableEq sig.P] {a b : GeneralizedAtom sig T} :
    a.predicate = b.predicate -> a.terms.length = b.terms.length := by
  intro pred_eq;rw [GeneralizedAtom.arity_ok, pred_eq, GeneralizedAtom.arity_ok]

