/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.ChaseDerivationSkeleton
import BasicLeanDatastructures.WellFounded

open CustomBasicDatastructures

/-!
# Expressing Chase Sequences through Lists of Triggers

The triggers of a chase structure usually convey enough information to reconstruct the involved fact sets
when given an initial one.
Also, especially when constructing sequences it might be easier to only list the triggers instead of also
constructing the fact sets manually.
Therefore, we dedicate this file to a few auxiliary definitions and results to capture finite and
infinite lists of triggers (origins actually) that can be used to describe chase sequences.
As of now, we only relate these to `RegularChaseDerivation`s.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

section FiniteTriggerList

/-!
## Finite Trigger Lists
-/

/-- A finite list of origins (as you would expect). -/
abbrev FiniteTriggerList (obs : ObsolescenceCondition sig) (rules : RuleSet sig) := List (ChaseNodeOrigin obs rules)

namespace FiniteTriggerList

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

/-- The fact set resulting from applying all triggers from the list one after the other to an initial fact set. -/
def result (start : FactSet sig) : FiniteTriggerList obs rules -> FactSet sig
| .nil => start
| .cons hd tl => result (start ∪ hd.result.toSet) tl

/-- For the empty trigger list, the `result` is the staring fact set. -/
@[simp, grind =]
theorem result_nil {start : FactSet sig} : result start ([] : FiniteTriggerList obs rules) = start := by simp [result]

/-- This unfolds the `result` definition for cons trigger lists. -/
@[simp, grind =]
theorem result_cons {start : FactSet sig} {hd : ChaseNodeOrigin obs rules} {tl : FiniteTriggerList obs rules} :
  result start (hd :: tl) = result (start ∪ hd.result.toSet) tl := by simp [result]

/-- The result of a singleton `FiniteTriggerList` is the exactly the triggers result (plus the starting facts). -/
@[simp, grind =]
theorem result_singleton {start : FactSet sig} {orig : ChaseNodeOrigin obs rules} :
    result start [orig] = start ∪ orig.result.toSet := by
  simp [result]

/-- The result of an appended `FiniteTriggerList` can be obtained by computing the result of the second on top of the first's result. -/
@[simp, grind =]
theorem result_append {start : FactSet sig} {l1 l2 : FiniteTriggerList obs rules} :
    result start (l1 ++ l2) = l2.result (l1.result start) := by
  fun_induction result
  . simp
  . simpa [result]

/-- The result contains the starting fact set. -/
theorem start_sub_result {start : FactSet sig} {l : FiniteTriggerList obs rules} : start ⊆ l.result start := by
  induction l generalizing start with
  | nil => simpa [result] using Set.subset_refl
  | cons hd tl ih => apply Set.subset_trans _ ih; apply Set.subset_union_of_subset_left; exact Set.subset_refl

/-- The result contains each trigger's result. -/
theorem each_trg_result_sub_result {start : FactSet sig} {l : FiniteTriggerList obs rules} : ∀ orig ∈ l, orig.result.toSet ⊆ l.result start := by
  intro orig orig_mem
  induction l generalizing start with
  | nil => simp at orig_mem
  | cons hd tl ih =>
    rw [List.mem_cons] at orig_mem
    cases orig_mem with
    | inr orig_mem => apply ih; exact orig_mem
    | inl orig_mem =>
      unfold result
      apply Set.subset_trans _ start_sub_result
      rw [orig_mem]; apply Set.subset_union_of_subset_right; exact Set.subset_refl

/-- A trigger property holds for the list if it holds for each trigger with respect to the previous trigger result. (With property we mean things like loaded, active, and obsolete.) -/
def trigger_property_holds (property : ChaseNodeOrigin obs rules -> FactSet sig -> Prop) (start : FactSet sig) : FiniteTriggerList obs rules -> Prop
| .nil => True
| .cons hd tl => property hd start ∧ trigger_property_holds property (start ∪ hd.result.toSet) tl

/-- We can express `trigger_property_holds` in terms of list indices. -/
theorem trigger_property_holds_iff {property : ChaseNodeOrigin obs rules -> FactSet sig -> Prop} {start : FactSet sig} {l : FiniteTriggerList obs rules} :
    trigger_property_holds property start l ↔ ∀ {i : Nat} (lt : i < l.length), property l[i] (result start (l.take i)) := by
  induction l generalizing start with
  | nil => simp [trigger_property_holds]
  | cons hd tl ih =>
    simp only [trigger_property_holds]; rw [ih]
    constructor
    . intro ⟨h_hd, h_tl⟩ i lt
      cases i
      . apply h_hd
      . apply h_tl
    . intro h; constructor
      . have : 0 < (hd :: tl).length := by simp
        apply h this
      . intro i lt
        have : i.succ < (hd :: tl).length := by simpa using lt
        apply h this

/-- A trigger list is called loaded if each trigger is loaded with respect to the result of the previous one. -/
def loaded (start : FactSet sig) (l : FiniteTriggerList obs rules) : Prop := trigger_property_holds (fun orig => orig.fst.val.loaded) start l
/-- A trigger list is called active if each trigger is active with respect to the result of the previous one. -/
def active (start : FactSet sig) (l : FiniteTriggerList obs rules) : Prop := trigger_property_holds (fun orig => orig.fst.val.active) start l

end FiniteTriggerList

abbrev FiniteNonEmptyTriggerList (obs : ObsolescenceCondition sig) (rules : RuleSet sig) := NonEmptyList (ChaseNodeOrigin obs rules)

end FiniteTriggerList

section InfiniteTriggerList

/-!
## Infinite Trigger Lists
-/

/-- A infinite list of origins. -/
abbrev InfiniteTriggerList (obs : ObsolescenceCondition sig) (rules : RuleSet sig) := InfiniteList (ChaseNodeOrigin obs rules)

namespace InfiniteTriggerList

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

/-- The fact set at index $i$ is exactly the result of the finite trigger list up until $i$. -/
def factSet_at (l : InfiniteTriggerList obs rules) (start : FactSet sig) (i : Nat) : FactSet sig := FiniteTriggerList.result start (l.take i)

/-- The fact set at index 0 is the starting fact set. -/
@[simp, grind =]
theorem factSet_at_zero {l : InfiniteTriggerList obs rules} {start : FactSet sig} : l.factSet_at start 0 = start := by simp [factSet_at]

/-- The fact set at index i.succ results from taking the one at index i and addint the result of the trigger at index i. -/
@[simp, grind =]
theorem factSet_at_succ {l : InfiniteTriggerList obs rules} {start : FactSet sig} :
    ∀ {i : Nat}, l.factSet_at start i.succ = l.factSet_at start i ∪ (l.get i).result.toSet := by
  intro i; simp only [factSet_at]; rw [InfiniteList.take_succ']; simp

/-- We can turn the list of triggers into a list of `ChaseNode`s. -/
def to_chaseNode_list (l : InfiniteTriggerList obs rules) (start : FactSet sig) : InfiniteList (RegularChaseNode obs rules)
| .zero => { facts := start, origin := none, facts_contain_origin_result := by simp }
| .succ i => { facts := l.factSet_at start i.succ, origin := some (l.get i), facts_contain_origin_result := by intro orig orig_mem; apply FiniteTriggerList.each_trg_result_sub_result; rw [Option.mem_def, Option.some_inj] at orig_mem; rw [← orig_mem]; apply InfiniteList.get_mem_take_of_lt; simp}

/-- For `to_chaseNode_list`, the facts at index i are exactly `factSet_at` index i. -/
@[simp, grind =]
theorem facts_get_to_ChaseNode_list {l : InfiniteTriggerList obs rules} {start : FactSet sig} :
    ∀ {i : Nat}, ((l.to_chaseNode_list start).get i).facts = l.factSet_at start i := by
  intro i; cases i <;> simp [InfiniteList.compute_get, to_chaseNode_list]

/-- For `to_chaseNode_list`, the origin at index i.succ is exactly the list element at index i. -/
@[simp, grind =]
theorem origin_get_succ_to_ChaseNode_list {l : InfiniteTriggerList obs rules} {start : FactSet sig} :
    ∀ {i : Nat}, ChaseNode.origin ((l.to_chaseNode_list start).get i.succ) = some (l.get i) := by
  intro _; simp [ChaseNode.origin, InfiniteList.compute_get, to_chaseNode_list]

/-- Each `InfiniteTriggerList` can be turned into a `RegularChaseDerivationSkeleton` via `to_chaseNode_list`. -/
def to_regularChaseDerivationSkeleton (l : InfiniteTriggerList obs rules) (start : FactSet sig) : RegularChaseDerivationSkeleton obs rules where
  branch := PossiblyInfiniteList.from_infiniteList (l.to_chaseNode_list start)
  isSome_head := by rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_from_infiniteList]; simp
  triggers_exist := by
    intro l2 suffix before before_mem after after_mem
    rw [PossiblyInfiniteList.IsSuffix_iff] at suffix; rcases suffix with ⟨n, suffix⟩
    rw [← suffix, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_from_infiniteList, Option.mem_def, Option.some_inj] at before_mem
    rw [← suffix, PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_from_infiniteList, Option.mem_def, Option.some_inj] at after_mem
    rw [← before_mem, ← after_mem]
    exists (by simp [InfiniteList.compute_get, to_chaseNode_list, ChaseNode.origin])
    simp only [RegularChaseNode.ingoingFacts_eq, RegularChaseNode.outgoingFacts_eq]
    simp [ChaseNode.origin_result]

/-- A trigger property holds for the list if it holds for each trigger with respect to the previous trigger result. (With property we mean things like loaded, active, and obsolete.) -/
@[expose]
def trigger_property_holds (property : ChaseNodeOrigin obs rules -> FactSet sig -> Prop) (start : FactSet sig) (l : InfiniteTriggerList obs rules) : Prop :=
  ∀ i, property (l.get i) (l.factSet_at start i)

/-- A trigger list is called loaded if each trigger is loaded with respect to the result of the previous one. -/
def loaded (start : FactSet sig) (l : InfiniteTriggerList obs rules) : Prop := trigger_property_holds (fun orig => orig.fst.val.loaded) start l
/-- A trigger list is called active if each trigger is active with respect to the result of the previous one. -/
def active (start : FactSet sig) (l : InfiniteTriggerList obs rules) : Prop := trigger_property_holds (fun orig => orig.fst.val.active) start l

end InfiniteTriggerList

end InfiniteTriggerList

section InfiniteListOfFiniteTriggerLists

/-!
## Constructing an InfiniteTriggerList from an InfiniteList of FiniteTriggerLists
-/

namespace InfiniteTriggerList

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

/-- We convert an infinite list of `FiniteNonEmptyTriggerList`s into an `InfiniteTriggerList` by calling `InfiniteList.fromNonEmptyLists`. -/
def fromFiniteLists (ls : InfiniteList (FiniteNonEmptyTriggerList obs rules)) : InfiniteTriggerList obs rules := InfiniteList.fromNonEmptyLists ls

/-- For a infinite list of `FiniteNonEmptyTriggerList`, we can compute the starting fact set for each of the finite lists inductively. -/
def startForFiniteList (ls : InfiniteList (FiniteNonEmptyTriggerList obs rules)) (start : FactSet sig) : Nat -> FactSet sig
| .zero => start
| .succ n => FiniteTriggerList.result (startForFiniteList ls start n) (ls.get n).toList

/-- The `startForFiniteList` can equivalently be expressed by combining finitely many of the finite lists into one and then using `FiniteTriggerList.result`. -/
theorem startForFiniteList_eq {ls : InfiniteList (FiniteNonEmptyTriggerList obs rules)} {start : FactSet sig} :
    ∀ {n}, startForFiniteList ls start n = FiniteTriggerList.result start ((ls.take n).flatMap NonEmptyList.toList) := by
  intro n
  fun_induction startForFiniteList
  . simp
  . rw [InfiniteList.take_succ']; grind

/--
If a trigger property holds for each each trigger in each finite list in an infinite list of `FiniteNonEmptyTriggerList`s,
then the same property holds for the infinite list that we obtain through `fromFiniteLists`.
-/
theorem fromFiniteLists_trigger_property_preserved
    {ls : InfiniteList (FiniteNonEmptyTriggerList obs rules)}
    {property : ChaseNodeOrigin obs rules -> FactSet sig -> Prop}
    {start : FactSet sig} :
    (∀ n, FiniteTriggerList.trigger_property_holds property (startForFiniteList ls start n) (ls.get n).toList) ->
    trigger_property_holds property start (fromFiniteLists ls) := by
  intro holds_for_each
  intro i
  unfold factSet_at
  suffices ∃ (m j : Nat), (fromFiniteLists ls).take i.succ = (ls.take m).flatMap NonEmptyList.toList ++ (ls.get m).toList.take j.succ ∧
      (fromFiniteLists ls).take i.succ ≠ (ls.take m).flatMap NonEmptyList.toList ++ (ls.get m).toList.take j by
    rcases this with ⟨m, j, take_eq, minimal⟩
    have lt : j < (ls.get m).toList.length := by
      apply Decidable.byContradiction; intro contra; rw [Nat.not_lt] at contra
      apply minimal
      suffices (ls.get m).toList.take j = (ls.get m).toList.take j.succ by rw [this]; exact take_eq
      rw [List.take_of_length_le contra, List.take_of_length_le (Nat.le_succ_of_le contra)]
    rw [InfiniteList.take_succ', List.take_succ_eq_append_getElem lt] at take_eq
    rw [← List.append_assoc, List.append_eq_append_iff_of_size_eq_right (by rfl)] at take_eq
    rw [List.cons.injEq] at take_eq
    rw [take_eq.left, take_eq.right.left]

    specialize holds_for_each m
    rw [FiniteTriggerList.trigger_property_holds_iff] at holds_for_each
    specialize holds_for_each lt
    rw [FiniteTriggerList.result_append]
    rw [startForFiniteList_eq] at holds_for_each
    exact holds_for_each
  suffices ∃ (m j : Nat), (fromFiniteLists ls).take i.succ = (ls.take m).flatMap NonEmptyList.toList ++ (ls.get m).toList.take j.succ by
    rcases this with ⟨m, j, take_eq⟩
    rcases minimal_element_for_property_and_relation (fun j => (fromFiniteLists ls).take i.succ = (ls.take m).flatMap NonEmptyList.toList ++ (ls.get m).toList.take j.succ) j take_eq with ⟨j2, j2_prop, j2_min⟩
    exists m, j2; constructor; exact j2_prop
    cases j2 with
    | succ j2 => exact j2_min j2 j2.lt_succ_self
    | zero =>
      intro contra; rw [contra] at take_eq
      apply (ls.get m).toList_ne_nil
      rw [List.take_zero, List.append_cancel_left_eq] at take_eq
      cases List.take_eq_nil_iff.mp (Eq.symm take_eq); contradiction; assumption
  rcases ls.fromNonEmptyLists_take_eq' (n := i.succ) with ⟨m, j, take_eq⟩
  cases j with
  | succ j => exists m, j
  | zero =>
    cases m with
    | zero => simp [InfiniteList.take_succ] at take_eq
    | succ m =>
      suffices (ls.take m.succ).flatMap NonEmptyList.toList = (ls.take m).flatMap NonEmptyList.toList ++ (ls.get m).toList by
        exists m, (ls.get m).toList.length.pred
        unfold fromFiniteLists
        rw [take_eq, List.take_zero, List.append_nil, this, List.append_cancel_left_eq]
        rw [Nat.succ_pred (by intro contra; apply (ls.get m).toList_ne_nil; rw [← List.length_eq_zero_iff]; exact contra)]; simp
      rw [InfiniteList.take_succ']; simp

/-- By `fromFiniteLists_trigger_property_preserved`, trigger loadedness is preserved by the `fromFiniteLists` construction. -/
theorem fromFiniteLists_loadedness_preserved
    {ls : InfiniteList (FiniteNonEmptyTriggerList obs rules)} {start : FactSet sig} :
    (∀ n, FiniteTriggerList.loaded (startForFiniteList ls start n) (ls.get n).toList) ->
    (fromFiniteLists ls).loaded start := fromFiniteLists_trigger_property_preserved

/-- By `fromFiniteLists_trigger_property_preserved`, trigger activeness is preserved by the `fromFiniteLists` construction. -/
theorem fromFiniteLists_activeness_preserved
    {ls : InfiniteList (FiniteNonEmptyTriggerList obs rules)} {start : FactSet sig} :
    (∀ n, FiniteTriggerList.active (startForFiniteList ls start n) (ls.get n).toList) ->
    (fromFiniteLists ls).active start := fromFiniteLists_trigger_property_preserved

end InfiniteTriggerList

end InfiniteListOfFiniteTriggerLists

