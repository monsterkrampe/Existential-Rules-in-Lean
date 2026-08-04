/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.List.EraseDupsKeepRight
public import BasicLeanDatastructures.Set.Basic
public import BasicLeanDatastructures.Set.Finite

public import ExistentialRules.AtomsAndRules.Rule
public import ExistentialRules.Terms.SkolemTerm


/-!
# RuleSet
-/

public section

/-- A `RuleSet` is a `Set (Rule sig)`. -/
abbrev RuleSet (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := Set (Rule sig)

namespace RuleSet

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `RuleSet` is is deterministic if each rule is. -/
@[expose]
def isDeterministic (rs : RuleSet sig) : Prop := ∀ (r : Rule sig), r ∈ rs -> r.isDeterministic

/-- The predicate symbols of a `RuleSet` are the predicate symbols from all rules. -/
@[expose]
def predicates (rs : RuleSet sig) : Set sig.P := fun p => ∃ r, r ∈ rs ∧ p ∈ r.predicates

/-- The constants of a `RuleSet` are the constants from all rules. -/
@[expose]
def constants (rs : RuleSet sig) : Set sig.C := fun c => ∃ r, r ∈ rs ∧ c ∈ r.constants

/-- The head constants of a `RuleSet` are the head constants from all rules. -/
@[expose]
def head_constants (rs : RuleSet sig) : Set sig.C := fun c => ∃ r, r ∈ rs ∧ c ∈ r.head_constants

/-- The Skolem function symbols of a `RuleSet` are the Skolem function symbols from all rules. -/
@[expose]
def skolem_functions (rs : RuleSet sig) : Set (SkolemFS sig) := fun f => ∃ r, r ∈ rs ∧ f ∈ r.skolem_functions

/-- If the `RuleSet` is finite, so are the `RuleSet.predicates`. -/
@[grind ->]
theorem predicates_finite_of_finite (rs : RuleSet sig) : rs.finite -> rs.predicates.finite := by
  intro finite
  rcases finite with ⟨l, nodup, eq⟩
  exists (l.flatMap Rule.predicates).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro p
    rw [List.mem_eraseDupsKeepRight]
    unfold predicates
    simp only [List.mem_flatMap]
    constructor <;> (intro ⟨r, h⟩; exists r; grind)

/-- If the `RuleSet` is finite, so are the `RuleSet.constants`. -/
@[grind ->]
theorem constants_finite_of_finite (rs : RuleSet sig) : rs.finite -> rs.constants.finite := by
  intro finite
  rcases finite with ⟨l, nodup, eq⟩
  exists (l.flatMap Rule.constants).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro c
    rw [List.mem_eraseDupsKeepRight]
    unfold constants
    simp only [List.mem_flatMap]
    constructor <;> (intro ⟨r, h⟩; exists r; grind)

/-- If the `RuleSet` is finite, so are the `RuleSet.head_constants`. -/
@[grind ->]
theorem head_constants_finite_of_finite (rs : RuleSet sig) : rs.finite -> rs.head_constants.finite := by
  intro finite
  rcases finite with ⟨l, nodup, eq⟩
  exists (l.flatMap Rule.head_constants).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro c
    rw [List.mem_eraseDupsKeepRight]
    unfold head_constants
    simp only [List.mem_flatMap]
    constructor <;> (intro ⟨r, h⟩; exists r; grind)

/-- If the `RuleSet` is finite, so are the `RuleSet.skolem_functions`. -/
@[grind ->]
theorem skolem_functions_finite_of_finite (rs : RuleSet sig) : rs.finite -> rs.skolem_functions.finite := by
  intro finite
  rcases finite with ⟨l, nodup, eq⟩
  exists (l.flatMap Rule.skolem_functions).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro c
    rw [List.mem_eraseDupsKeepRight]
    unfold skolem_functions
    simp only [List.mem_flatMap]
    constructor <;> (intro ⟨r, h⟩; exists r; grind)

/-- The `RuleSet.head_constants` are a subset of the `RuleSet.constants`. -/
@[grind <-]
theorem head_constants_subset_constants (rs : RuleSet sig) : rs.head_constants ⊆ rs.constants := by
  intro c c_mem
  rcases c_mem with ⟨r, r_mem, c_mem⟩
  exists r
  constructor
  . exact r_mem
  . apply Rule.head_constants_subset_constants; exact c_mem

end RuleSet

