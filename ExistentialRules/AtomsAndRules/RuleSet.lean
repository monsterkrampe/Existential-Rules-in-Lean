/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import BasicLeanDatastructures.List.EraseDupsKeepRight
public import BasicLeanDatastructures.Set.Basic
public import BasicLeanDatastructures.Set.Finite

public import ExistentialRules.AtomsAndRules.Rule


/-!
# RuleSet and RuleList
-/

public section

/-- A `RuleSet` is a `Set (Rule sig)` where rules are uniquely identified by their id. -/
structure RuleSet (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  rules : Set (Rule sig)
  id_unique : ∀ r1 r2, r1 ∈ rules ∧ r2 ∈ rules ∧ r1.id = r2.id -> r1 = r2

/-- A `RuleList` is a `List (Rule sig)` where rules are uniquely identified by their id. -/
structure RuleList (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  rules : List (Rule sig)
  id_unique : ∀ r1 r2, r1 ∈ rules ∧ r2 ∈ rules ∧ r1.id = r2.id -> r1 = r2

namespace RuleSet

/-!
## RuleSet
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `RuleSet` is is deterministic if each rule is. -/
@[expose]
def isDeterministic (rs : RuleSet sig) : Prop := ∀ (r : Rule sig), r ∈ rs.rules -> r.isDeterministic

/-- The predicate symbols of a `RuleSet` are the predicate symbols from all rules. -/
@[expose]
def predicates (rs : RuleSet sig) : Set sig.P := fun p => ∃ r, r ∈ rs.rules ∧ p ∈ r.predicates

/-- The constants of a `RuleSet` are the constants from all rules. -/
@[expose]
def constants (rs : RuleSet sig) : Set sig.C := fun c => ∃ r, r ∈ rs.rules ∧ c ∈ r.constants

/-- The head constants of a `RuleSet` are the head constants from all rules. -/
@[expose]
def head_constants (rs : RuleSet sig) : Set sig.C := fun c => ∃ r, r ∈ rs.rules ∧ c ∈ r.head_constants

/-- The Skolem function symbols of a `RuleSet` are the Skolem function symbols from all rules. -/
@[expose]
def skolem_functions (rs : RuleSet sig) : Set (SkolemFS sig) := fun f => ∃ r, r ∈ rs.rules ∧ f ∈ r.skolem_functions

/-- If the `RuleSet` is finite, so are the `RuleSet.predicates`. -/
@[grind ->]
theorem predicates_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.predicates.finite := by
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
theorem constants_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.constants.finite := by
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
theorem head_constants_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.head_constants.finite := by
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
theorem skolem_functions_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.skolem_functions.finite := by
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

namespace RuleList

/-!
## RuleList
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- In a `RuleList`, we can obtain a rule based on its id. -/
def get_by_id (rl : RuleList sig) (id : Nat) (id_mem : ∃ r ∈ rl.rules, r.id = id) : Rule sig :=
  (rl.rules.find? (fun r => r.id = id)).get (by simp [id_mem])

/-- A rule that we get by id is in the `RuleList`. -/
theorem get_by_id_mem (rl : RuleList sig) (id : Nat) (id_mem : ∃ r ∈ rl.rules, r.id = id) : rl.get_by_id id id_mem ∈ rl.rules := by
  unfold get_by_id; apply List.get_find?_mem

/-- A rule that we get by id is indeed the rule that the id belongs to. -/
@[simp, grind =]
theorem get_by_id_self (rl : RuleList sig) (r : Rule sig) (mem : r ∈ rl.rules) : rl.get_by_id r.id (by exists r) = r := by
  apply rl.id_unique
  constructor
  . apply List.get_find?_mem
  constructor
  . exact mem
  . unfold get_by_id
    have eq : rl.rules.find? (fun r' => r'.id = r.id) = some ((rl.rules.find? (fun r' => r'.id = r.id)).get (by rw [List.find?_isSome]; exists r; constructor; exact mem; simp)) := by simp
    apply of_decide_eq_true
    apply List.find?_some eq

end RuleList

