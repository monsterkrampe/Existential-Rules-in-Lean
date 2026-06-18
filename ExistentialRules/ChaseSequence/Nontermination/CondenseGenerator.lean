/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.Function.Repetition
import BasicLeanDatastructures.Nat

/-!

# Condense a Generator Function

Here we introduce functionality that allows to condense repeated function calls according to a certain mapper.
By that, we mean that if the generator produces a new value that is the same as the previous one under the mapper function, then the value is skipped.

-/

namespace Function

variable {α : Type u} {β : Type v} [DecidableEq α]

/-- An auxiliary definition for condensing a generator function. It requires that for each generated element there is a smallest number n, such that the n times repetition yields a different value under the mapper function. It is not really necessary that this n is the smallest since, as long as we know that any such n exists, we know that there also exists a smallest one. Still, the termination proof of this function is much simpler with the stronger claim. -/
def condense_generator_weak
    (generator : β -> β) (mapper : β -> α)
    (different_value_exists : ∀ b, ∃ n, mapper (generator.repeat_fun n b) ≠ mapper b ∧ ∀ m : Fin n, mapper (generator.repeat_fun m b) = mapper b)
    (b : β) : β :=
  if eq : mapper (generator b) = mapper b
  then
    have _termination : Classical.choose (different_value_exists (generator b)) < Classical.choose (different_value_exists b) := by
      have spec := Classical.choose_spec (different_value_exists b)
      have spec_next := Classical.choose_spec (different_value_exists (generator b))
      apply Decidable.byContradiction; intro contra
      apply spec.left
      rcases (Classical.choose (different_value_exists b)).exists_eq_succ_of_ne_zero (by intro contra; apply spec.left; rw [contra, Function.repeat_zero]) with ⟨prev, prev_eq⟩
      rw [prev_eq, Function.repeat_succ, generator.repeat_swap_one]
      rw [← eq]
      exact spec_next.right ⟨prev, by apply Nat.lt_of_succ_le; apply Nat.le_of_not_lt; rw [← prev_eq]; exact contra⟩
    condense_generator_weak generator mapper different_value_exists (generator b)
  else generator b
termination_by Classical.choose (different_value_exists b)

/-- We condense a generator function by skipping the values that yield the same value under a mapper function. To knwo that this terminates, we need a proof that eventually we will obtain a new value. Internally the recursion is implemented using an auxiliary function, which requires a slightly stronger proof but we can simply derive that one from the weaker claim given to this function. -/
public def condense_generator
    (generator : β -> β) (mapper : β -> α)
    (different_value_exists : ∀ b, ∃ n, mapper (generator.repeat_fun n b) ≠ mapper b)
    (b : β) : β :=
  have stronger_claim : ∀ b, ∃ n, mapper (generator.repeat_fun n b) ≠ mapper b ∧ ∀ m : Fin n, mapper (generator.repeat_fun m b) = mapper b := by
    intro b; specialize different_value_exists b
    rcases different_value_exists with ⟨n, h⟩
    rcases prop_for_nat_has_minimal_such_nat (fun m => mapper (generator.repeat_fun m b) ≠ mapper b) n h with ⟨n', strong_h⟩
    exists n'
    grind
  condense_generator_weak generator mapper stronger_claim b

/-- This unfolds the branch of the recursive definition where the values of the current and the next value are the same. In this case the next value is skipped. -/
public theorem condense_generator_of_next_eq
    {generator : β -> β} {mapper : β -> α}
    {different_value_exists : ∀ b, ∃ n, mapper (generator.repeat_fun n b) ≠ mapper b} :
    ∀ {b}, mapper (generator b) = mapper b ->
    condense_generator generator mapper different_value_exists b = condense_generator generator mapper different_value_exists (generator b) := by
  intro b eq
  unfold condense_generator
  conv => left; unfold condense_generator_weak
  simp [eq]

/-- This unfolds the branch of the recursive definition where the values of the current and the next value are not the same. In this case the condense_generator yields the same value as the original generator. -/
public theorem condense_generator_eq_generator_of_ne
    {generator : β -> β} {mapper : β -> α}
    {different_value_exists : ∀ b, ∃ n, mapper (generator.repeat_fun n b) ≠ mapper b} :
    ∀ b, mapper (generator b) ≠ mapper b -> condense_generator generator mapper different_value_exists b = generator b := by
  intro b eq
  unfold condense_generator
  conv => left; unfold condense_generator_weak
  simp [eq]

/-- The next value produced by `condense_generator` is guaranteed to be different from the current one under the mapper function. -/
public theorem condense_generator_next_ne
    {generator : β -> β} {mapper : β -> α}
    {different_value_exists : ∀ b, ∃ n, mapper (generator.repeat_fun n b) ≠ mapper b} :
    ∀ b, mapper (condense_generator generator mapper different_value_exists b) ≠ mapper b := by
  intro b
  unfold condense_generator
  fun_induction condense_generator_weak generator mapper _ b with
  | case2 b ne => exact ne
  | case1 b eq _ ih => rw [← eq]; exact ih

/-- Each value produced by `condense_generator` can be obtain from a suitable number of repetitions of the original generator. Note that this is true for the produced "carrier" value of the generator and not just for the value under the mapper function. The result simply holds since `condense_generator` is only skipping value from the generator but it cannot produce anything which would not eventually be produced by the generator as well. -/
public theorem condense_generator_eq_repeat_generator
    (generator : β -> β) (mapper : β -> α)
    (different_value_exists : ∀ b, ∃ n, mapper (generator.repeat_fun n b) ≠ mapper b) :
    ∀ b, ∃ n, condense_generator generator mapper different_value_exists b = generator.repeat_fun n b := by
  intro b
  unfold condense_generator
  fun_induction condense_generator_weak generator mapper _ b with
  | case2 b ne => exists 1
  | case1 b eq _ ih =>
    rcases ih with ⟨n, ih⟩
    exists n.succ
    rw [Function.repeat_succ, generator.repeat_swap_one]
    exact ih

end Function

