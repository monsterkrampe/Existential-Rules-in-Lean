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

theorem each_trg_result_sub_result {start : FactSet sig} {l : FiniteTriggerList obs rules} : ∀ orig ∈ l, orig.result.toSet ⊆ l.result start := by sorry

/-- A trigger property holds for the list if it holds for each trigger with respect to the previous trigger result. (With property we mean things like loaded, active, and obsolete.) -/
def trigger_property_holds (property : RTrigger obs rules -> FactSet sig -> Prop) (start : FactSet sig) : FiniteTriggerList obs rules -> Prop
| .nil => True
| .cons hd tl => property hd.fst start ∧ trigger_property_holds property (start ∪ hd.result.toSet) tl

/-- A trigger list is called loaded if each trigger is loaded with respect to the result of the previous one. -/
def loaded (start : FactSet sig) (l : FiniteTriggerList obs rules) : Prop := trigger_property_holds (fun trg => trg.val.loaded) start l
/-- A trigger list is called active if each trigger is active with respect to the result of the previous one. -/
def active (start : FactSet sig) (l : FiniteTriggerList obs rules) : Prop := trigger_property_holds (fun trg => trg.val.active) start l

end FiniteTriggerList


/-!
## Infinite Trigger Lists
-/

/-- A infinite list of origins. -/
abbrev InfiniteTriggerList (obs : ObsolescenceCondition sig) (rules : RuleSet sig) := InfiniteList (ChaseNodeOrigin obs rules)

namespace InfiniteTriggerList

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

/-- The fact set at index $i$ is exactly the result of the finite trigger list up until $i$. -/
def factSet_at (l : InfiniteTriggerList obs rules) (start : FactSet sig) (i : Nat) : FactSet sig := FiniteTriggerList.result start (l.take i)

/-- We can turn the list of triggers into a list of `ChaseNode`s. -/
def to_chaseNode_list (l : InfiniteTriggerList obs rules) (start : FactSet sig) : InfiniteList (RegularChaseNode obs rules)
| .zero => { facts := start, origin := none, facts_contain_origin_result := by simp }
| .succ i => { facts := l.factSet_at start i.succ, origin := some (l.get i), facts_contain_origin_result := by intro orig orig_mem; apply FiniteTriggerList.each_trg_result_sub_result; sorry}

/-- A trigger property holds for the list if it holds for each trigger with respect to the previous trigger result. (With property we mean things like loaded, active, and obsolete.) -/
def trigger_property_holds (property : RTrigger obs rules -> FactSet sig -> Prop) (start : FactSet sig) (l : InfiniteTriggerList obs rules) : Prop :=
  ∀ i, property (l.get i).fst (l.factSet_at start i)

/-- A trigger list is called loaded if each trigger is loaded with respect to the result of the previous one. -/
def loaded (start : FactSet sig) (l : InfiniteTriggerList obs rules) : Prop := trigger_property_holds (fun trg => trg.val.loaded) start l
/-- A trigger list is called active if each trigger is active with respect to the result of the previous one. -/
def active (start : FactSet sig) (l : InfiniteTriggerList obs rules) : Prop := trigger_property_holds (fun trg => trg.val.active) start l

end InfiniteTriggerList

