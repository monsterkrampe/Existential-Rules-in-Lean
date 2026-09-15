/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.ChaseDerivationSkeleton

/-!
# Expressing Chase Sequences through Lists of Triggers

The triggers of a chase structure usually convey enough information to reconstruct the involved fact sets
when given an initial one.
Also, esspecially when constructing sequences it might be easier to only list the triggers instead of also
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
def trigger_property_holds (property : RTrigger obs rules -> FactSet sig -> Prop) (start : FactSet sig) : FiniteTriggerList obs rules -> Prop
| .nil => True
| .cons hd tl => property hd.fst start ∧ trigger_property_holds property (start ∪ hd.result.toSet) tl

/-- A trigger list is called loaded if each trigger is loaded with respect to the result of the previous one. -/
def loaded (start : FactSet sig) (l : FiniteTriggerList obs rules) : Prop := trigger_property_holds (fun trg => trg.val.loaded) start l
/-- A trigger list is called active if each trigger is active with respect to the result of the previous one. -/
def active (start : FactSet sig) (l : FiniteTriggerList obs rules) : Prop := trigger_property_holds (fun trg => trg.val.active) start l

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

/-- For `to_chaseNode_list`, the origin at index i.succ is exatly the list element at index i. -/
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
def trigger_property_holds (property : RTrigger obs rules -> FactSet sig -> Prop) (start : FactSet sig) (l : InfiniteTriggerList obs rules) : Prop :=
  ∀ i, property (l.get i).fst (l.factSet_at start i)

/-- A trigger list is called loaded if each trigger is loaded with respect to the result of the previous one. -/
def loaded (start : FactSet sig) (l : InfiniteTriggerList obs rules) : Prop := trigger_property_holds (fun trg => trg.val.loaded) start l
/-- A trigger list is called active if each trigger is active with respect to the result of the previous one. -/
def active (start : FactSet sig) (l : InfiniteTriggerList obs rules) : Prop := trigger_property_holds (fun trg => trg.val.active) start l

end InfiniteTriggerList

end InfiniteTriggerList

section InfiniteListOfFiniteTriggerLists

/-!
## Constructing an InfiniteTriggerList from an InfiniteList of FiniteTriggerLists
-/

namespace InfiniteTriggerList

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

def fromFiniteLists (ls : InfiniteList (FiniteNonEmptyTriggerList obs rules)) : InfiniteTriggerList obs rules := InfiniteList.fromNonEmptyLists ls

def startForFiniteList (ls : InfiniteList (FiniteNonEmptyTriggerList obs rules)) (start : FactSet sig) : Nat -> FactSet sig
| .zero => start
| .succ n => FiniteTriggerList.result (startForFiniteList ls start n) (ls.get n).toList

theorem trigger_property_preserved
    {ls : InfiniteList (FiniteNonEmptyTriggerList obs rules)}
    {property : RTrigger obs rules -> FactSet sig -> Prop}
    {start : FactSet sig} :
    (∀ n, FiniteTriggerList.trigger_property_holds property (startForFiniteList ls start n) (ls.get n).toList) ->
    trigger_property_holds property start (fromFiniteLists ls) := by
  intro holds_for_each
  intro i
  sorry

end InfiniteTriggerList

end InfiniteListOfFiniteTriggerLists

