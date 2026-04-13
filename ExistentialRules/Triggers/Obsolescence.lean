/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.Triggers.Basic

/-!
# Obsolescence (Conditions)

For the chase, we need to be able to define when a trigger should not be applied even though it might be loaded.
In such a case (even when not loaded), we say that the trigger is "obsolete".
We make this decision based on a given `PreTrigger` and a `FactSet`.
Different chase variants use different notions of obsolescence.
For example the restricted (aka. standard) chase says that a trigger is obsolete when it is satisfied.
On the other hand, the Skolem chase says that a trigger is obsolete when its excat result is already present.
We aim to capture both of these notions and everything in-between using a generic `ObsolescenceCondition`
that conveys the necessary properties.

The condition itself is a function taking a `PreTrigger` and a `FactSet` returning a `Prop` indicating if the trigger is obsolete for the fact set or not.
Then, we require 4 conditions:

1. The condition is subset monotone. That is, if a trigger is obsolete for a fact set, it is also obsolete for all supersets.
2. If a trigger is obsolete then it is also satisfied.
3. If the exact trigger result already occurs in the fact set, then the trigger is obsolete.
4. Equivalent triggers are obsolete on exactly the same fact sets.

`RestrictedObsolescence` and `SkolemObsolescence` are the two extremes of what is allowed according to these conditions, `SkolemObsolescence` being the most liberal and `RestrictedObsolescence` being, quite expectedly, the most restricted.
-/

public section

/-- `LaxObsolescenceCondition` is a more liberal version of `ObsolescenceCondition` enforcing only subset monotonicity (i.e. condition 1 above). We use such a more liberal condition for MFA later. For the most part, you can completely ignore that this exists and only consider `ObsolescenceCondition`s instead. -/
structure LaxObsolescenceCondition (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  cond : PreTrigger sig -> FactSet sig -> Prop
  monotone : ∀ {trg} {A B : FactSet sig}, A ⊆ B -> cond trg A -> cond trg B

/-- An `ObsolescenceCondition` is a function from `PreTrigger` and `FactSet` into `Prop` with the 4 conditions mentioned above. -/
structure ObsolescenceCondition (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] extends LaxObsolescenceCondition sig where
  cond_implies_trg_is_satisfied : cond trg fs -> trg.satisfied fs
  contains_trg_result_implies_cond : ∀ {trg : PreTrigger sig} {fs} (disj_index : Fin trg.mapped_head.length),
    ((trg.mapped_head[disj_index.val]).toSet ⊆ fs) -> cond trg fs
  preserved_under_equiv : ∀ {trg trg2 : PreTrigger sig} {fs}, trg.equiv trg2 -> (cond trg fs ↔ cond trg2 fs)

instance {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] :
    Coe (ObsolescenceCondition sig) (LaxObsolescenceCondition sig) where
  coe obs := { cond := obs.cond, monotone := obs.monotone }

section SpecificConditions

/-!
## SpecificConditions

We briefly define the `ObsolescenceCondition`s for Skolem and restricted chase to show that these indeed have the 4 necessary properties. However, most definitions are still expressed in terms of the generic `ObsolescenceCondition` so the specific ones are rarely used throughout the code; only when results indeed do not hold for the generic case but only specific obsolescence conditions.
-/

/-- Obsolescence for the Skolem chase is indeed a `ObsolescenceCondition`, i.e. it has all 4 properties. According to this condition, a trigger is obsolete if its exact result, for one of the head disjuncts, already occurs in the fact set. -/
@[expose]
def SkolemObsolescence (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] : ObsolescenceCondition sig := {
  cond := fun (trg : PreTrigger sig) (fs : FactSet sig) => ∃ i : Fin trg.mapped_head.length, (trg.mapped_head[i.val]).toSet ⊆ fs
  monotone := by
    intro trg A B A_sub_B
    simp
    intro i head_sub_A
    exists i
    apply Set.subset_trans
    . exact head_sub_A
    . exact A_sub_B
  cond_implies_trg_is_satisfied := by
    intro trg fs h
    rcases h with ⟨i, h⟩
    exists ⟨i, by rw [← PreTrigger.length_mapped_head]; exact i.isLt⟩
    apply trg.satisfied_for_disj_of_mapped_head_contained
    exact h
  contains_trg_result_implies_cond := by
    intro trg F i result_in_F
    exists i
  preserved_under_equiv := by
    intro trg trg2 fs equiv
    have := PreTrigger.result_eq_of_equiv equiv
    constructor
    . rintro ⟨i, h⟩
      exists ⟨i.val, by rw [← this]; exact i.isLt⟩
      simp only [← this]
      exact h
    . rintro ⟨i, h⟩
      exists ⟨i.val, by rw [this]; exact i.isLt⟩
      simp only [this]
      exact h
}

/-- Obsolescence for the restricted chase is indeed a `ObsolescenceCondition`, i.e. it has all 4 properties. According to this condition, a trigger is obsolete if it is satisfied. -/
@[expose]
def RestrictedObsolescence (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] : ObsolescenceCondition sig := {
  cond := fun (trg : PreTrigger sig) (fs : FactSet sig) => trg.satisfied fs
  monotone := by
    intro trg A B A_sub_B
    simp [PreTrigger.satisfied, PreTrigger.satisfied_for_disj]
    intro i subs frontier_same_under_subs applied_head_sub_A
    exists i
    exists subs
    constructor
    . apply frontier_same_under_subs
    . apply Set.subset_trans
      . exact applied_head_sub_A
      . exact A_sub_B
  cond_implies_trg_is_satisfied := by intro _ _ h; exact h
  contains_trg_result_implies_cond := by
    intro trg fs i result_in_fs
    exists ⟨i.val, by rw [← PreTrigger.length_mapped_head]; exact i.isLt⟩
    apply trg.satisfied_for_disj_of_mapped_head_contained
    exact result_in_fs
  preserved_under_equiv := by
    intro trg trg2 fs equiv
    apply PreTrigger.satisfied_preserved_of_equiv
    exact equiv
}

end SpecificConditions

section Trigger

/-!
## (Proper) Triggers

A `Trigger` is a `PreTrigger` that has a fixed obsolescence condition.
We say that a `Trigger` is `active` if it is loaded and not obsolete.

`SkolemTrigger` and `RestrictedTrigger` are just defined as examples.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

structure Trigger (obsolete : LaxObsolescenceCondition sig) extends PreTrigger sig

def SkolemTrigger := Trigger (SkolemObsolescence sig : LaxObsolescenceCondition sig)
def RestrictedTrigger := Trigger (RestrictedObsolescence sig : LaxObsolescenceCondition sig)

variable {obs : LaxObsolescenceCondition sig}

instance : CoeOut (Trigger obs) (PreTrigger sig) where
  coe trigger := { rule := trigger.rule, subs := trigger.subs }

@[expose]
def Trigger.active (trg : Trigger obs) (F : FactSet sig) : Prop :=
  trg.loaded F ∧ ¬ (obs.cond trg F)

end Trigger

