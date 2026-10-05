/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.Function.Repetition
public import ExistentialRules.ChaseSequence.Termination.ConstantMappings.Basic

open CustomBasicDatastructures

/-!
# Repeating Constant Mappings

Just like arbitrary functions, we can repeat constant mappings.
However, the behavior here is special since constant mappings are not of the form A -> A but of the form sig.C -> GroundTerm sig.
We can still repeat them by using `ConstantMapping.apply_ground_term` for the repetition.
We could also define repetition directly using `Function.repeat_fun` with `ConstantMapping.apply_ground_term`
but this only gives us a `GroundTermMapping`.

Here, we specifically define `ConstantMapping.repeat_fun` instead, which is again a `ConstantMapping`.
We also prove that this can be translated into a call of `Function.repeat_fun` with `ConstantMapping.apply_ground_term`.

-/

public section

namespace ConstantMapping

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/--
We can repeat a constant mapping in the obvious way.
Note that we cannot directly use `Function.repeat_fun` since this could only give us a `GroundTermMapping` but not a `ConstantMapping`.
-/
def repeat_fun (g : ConstantMapping sig) (n : Nat) : ConstantMapping sig := fun c => (Function.repeat_fun g.apply_ground_term n) (.const c)

/-- As usual, repeating a mapping 0 times yields the id mapping. -/
@[simp, grind =]
theorem repeat_zero {g : ConstantMapping sig} : g.repeat_fun 0 = ConstantMapping.id := by
  apply funext; intro c; simp [repeat_fun, Function.repeat_zero]

/-- A n+1 times repetition is a n times repetition followed by applying the ground term version of the `ConstantMapping`. -/
theorem repeat_succ {g : ConstantMapping sig} {n : Nat} : g.repeat_fun n.succ = g.apply_ground_term ∘ (g.repeat_fun n) := by
  apply funext; intro t; simp only [repeat_fun, Function.comp_apply, Function.repeat_succ]

/-- `ConstantMapping.repeat_fun` can be expressed using `Function.repeat_fun` on `ConstantMapping.apply_ground_term`. -/
theorem apply_ground_term_repeat_fun_eq {g : ConstantMapping sig} {n : Nat} : (g.repeat_fun n).apply_ground_term = (Function.repeat_fun g.apply_ground_term n) := by
  apply funext; intro t
  induction n with
  | zero => simp [Function.repeat_zero]
  | succ n ih =>
    rw [repeat_succ, Function.repeat_succ]
    rw [apply_ground_term_compose]
    simp [ih]

/-- A n+1 times repetition is a single application followed by a n times repetition. -/
theorem repeat_succ' {g : ConstantMapping sig} {n : Nat} : g.repeat_fun n.succ = (g.repeat_fun n).apply_ground_term ∘ g := by
  apply funext; intro t; simp only [apply_ground_term_repeat_fun_eq, repeat_fun, Function.comp_apply, Nat.succ_eq_add_one, Function.repeat_add, Function.repeat_once, apply_ground_term_constant]

end ConstantMapping

