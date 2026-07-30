/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.Terms.SkolemTerm
public import ExistentialRules.AtomsAndRules.Basic

/-!
# Atom

An `Atom` is simply a `GeneralizedAtom` using `SkolemTerm`s.
-/

public section

abbrev Atom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := GeneralizedAtom sig (SkolemTerm sig)

