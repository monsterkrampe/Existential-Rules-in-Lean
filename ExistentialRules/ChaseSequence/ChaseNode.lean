/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.Triggers.RTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-!
# Chase Node

The chase is a pretty simple procedure. From an initial fact set, it creates a new fact set by applying a trigger and it continues to do this until all triggers are obsolete.
In this process, we obtain a (potentially infinite) sequence of fact sets.
It can be very useful to also keep track of the associated triggers and this is why we capture both the fact set and used trigger of individual chase steps in a `ChaseNode`.

To be able to use `ChaseNode`s also for the core chase, we develop a general interface in form of a typeclass where the "ingoingFacts" describe all facts that initiate the new chase node, while the "outgoingFacts" describe the facts that are available going further. That is, in the core chase, the outgoingFacts are a core of the ingoingFacts. For other chase variants, ingoingFacts and outgoingFacts are the same.
-/

public section

/-- A `ChaseNode` may originate from the head disjunct of a trigger. Consequently, this datastructure captures a trigger and one of its head disjunct indices. -/
abbrev ChaseNodeOrigin (obs : ObsolescenceCondition sig) (rules : RuleSet sig) :=
  (trg : RTrigger (obs : LaxObsolescenceCondition sig) rules) × Fin trg.val.rule.head.length

namespace ChaseNodeOrigin

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

/-- The result of the origin is the trigger head disjunct indicated by the index in second position. -/
@[expose]
def result (orig : ChaseNodeOrigin obs rules) : List (Fact sig) := orig.fst.val.mapped_head[orig.snd.val]

/-- Two origins are equivalent if their triggers are equivalent and they have the same disjunct index. -/
@[expose]
def equiv (orig1 orig2 : ChaseNodeOrigin obs rules) : Prop :=
  orig1.fst.equiv orig2.fst ∧ orig1.snd.val = orig2.snd.val

/-- Two origins are strongly equivalent if their triggers are strongly equivalent and they have the same disjunct index. -/
@[expose]
def strong_equiv (orig1 orig2 : ChaseNodeOrigin obs rules) : Prop :=
  orig1.fst.strong_equiv orig2.fst ∧ orig1.snd.val = orig2.snd.val

/-- If two origins are strongly equivalent, then they are also equivalent. -/
theorem equiv_of_strong_equiv {orig1 orig2 : ChaseNodeOrigin obs rules} :
    orig1.strong_equiv orig2 -> orig1.equiv orig2 := by
  intro ⟨h, h2⟩; constructor; exact PreTrigger.equiv_of_strong_equiv h; exact h2

/-- Equivalent origins have the same result. -/
theorem result_eq_of_equiv {orig1 orig2 : ChaseNodeOrigin obs rules} :
    orig1.equiv orig2 -> orig1.result = orig2.result := by
  unfold result; intro ⟨h, h2⟩; simp only [h2, PreTrigger.result_eq_of_equiv h]

end ChaseNodeOrigin

/-- A `ChaseNode` corresponds to a chase step. It must contain two `FactSet`s of ingoingFacts and outgoingFacts and optionally an `RTrigger` and a head disjunct index indicating that the current `ChaseNode` was obtained by applying the specified trigger and picking the indicated head disjunct. It is optional since the initial fact set does not result from a trigger but on all following nodes, this value will be set (and we will prove that it is). For convenience, the chase node also directly includes a proof that the result of its origin is indeed contained in its fact set. -/
class ChaseNode (N : Type u) (obs : ObsolescenceCondition sig) (rules : RuleSet sig) where
  ingoingFacts : N -> FactSet sig
  outgoingFacts : N -> FactSet sig
  origin : N -> Option (ChaseNodeOrigin obs rules)
  facts_contain_origin_result : (node : N) -> ∀ orig ∈ (origin node), orig.result.toSet ⊆ ingoingFacts node

namespace ChaseNode

variable {N : Type u} {obs : ObsolescenceCondition sig} {rules : RuleSet sig} [CN : ChaseNode N obs rules]

/-- The `origin_result` denotes the facts that have been introduced for the chase node. That is, the mapped head index for the trigger stored in the origin field of the `ChaseNode`. -/
@[expose]
def origin_result (node : N) (isSome : (CN.origin node).isSome) : List (Fact sig) :=
  ((CN.origin node).get isSome).result

/-- An auxiliary theorem showing that the origin result equals the i-th mapped head of a trigger if the trigger and i match the origin. -/
theorem origin_result_eq {node : N} (isSome : (CN.origin node).isSome)
    {trg : PreTrigger sig} {i : Nat} (trg_eq : trg = ((CN.origin node).get isSome).fst.val) (i_eq : i = ((CN.origin node).get isSome).snd.val) :
    CN.origin_result node isSome = trg.mapped_head[i]'(by grind) := by
  simp only [trg_eq, i_eq]; rfl

/-- Two `ChaseNode`s are in a successor relation if the second one could be created from the first one by adding the origin result of the second one to the outgoign facts of the first one. We do not enforce trigger activeness here since we can easily enforce this in the `ChaseDerivation` later on. -/
@[expose]
def succ (n1 n2 : N) : Prop := ∃ (origSome : (CN.origin n2).isSome), CN.ingoingFacts n2 = (CN.outgoingFacts n1) ∪ (origin_result n2 origSome).toSet

/-- A list of `ChaseNode` may follow from another `ChaseNode` if the list corresponds to a trigger output. Here we directly enforce activeness as this would be convoluted to state afterwards. -/
@[expose]
def succ_list (n : N) (l : List N) : Prop := l ≠ [] -> ∃ (trg : RTrigger obs rules),
  (trg.val.active (CN.outgoingFacts n)) ∧
  (l.map (CN.ingoingFacts) = trg.val.mapped_head.map (CN.outgoingFacts n ∪ ·.toSet)) ∧
  (∀ n2 ∈ l, (CN.origin n2).map Sigma.fst = some trg) ∧
  (∀ pair ∈ l.zipIdx, (CN.origin pair.fst).map (fun p => p.snd.val) = some pair.snd)

/-- Every member of a `succ_list` has the `succ` property. -/
theorem succ_of_mem_succ_list {n : N} {l : List N} (s : CN.succ_list n l) : ∀ n2 ∈ l, CN.succ n n2 := by
  intro n2 n2_mem
  rcases s (by grind) with ⟨trg, act, facts_eq, orig_eq, idx_eq⟩
  specialize orig_eq n2 n2_mem
  rw [Option.map_eq_some_iff] at orig_eq; rcases orig_eq with ⟨orig, orig_eq, trg_eq⟩
  exists (Option.isSome_of_eq_some orig_eq)
  rw [List.mem_iff_getElem] at n2_mem; rcases n2_mem with ⟨i, lt, n2_mem⟩
  have lt' : i < trg.val.mapped_head.length := by
    have length_map : (l.map CN.ingoingFacts).length = l.length := by simp
    rw [← length_map, facts_eq, List.length_map] at lt
    exact lt
  suffices trg.val.mapped_head[i] = CN.origin_result n2 (Option.isSome_of_eq_some orig_eq) by
    have n2_map : CN.ingoingFacts n2 = (l.map CN.ingoingFacts)[i]'(by grind) := by rw [List.getElem_map, n2_mem]
    simp only [facts_eq, List.getElem_map] at n2_map
    rw [n2_map, this]
  apply Eq.symm; apply origin_result_eq
  . simp only [orig_eq, Option.get_some]; rw [trg_eq]
  . specialize idx_eq (n2, i) (by grind)
    rw [orig_eq, Option.map_some, Option.some_inj] at idx_eq; simp only at idx_eq
    rw [← idx_eq]
    grind

/-- A property expressing that the outgoingFacts facts of a chase node form a subset of the ingoingFacts. We require this general property in a couple of proofs and it trivially holds true for both the regular chase node and the core chase node.  -/
@[expose]
def out_sub_in : Prop := ∀ {n : N}, CN.outgoingFacts n ⊆ CN.ingoingFacts n

end ChaseNode

/-- The `RegularChaseNode` is the one we use for most chases (except the core chase). Here ingoingFacts and outgoingFacts are always the same. -/
structure RegularChaseNode (obs : ObsolescenceCondition sig) (rules : RuleSet sig) where
  facts : FactSet sig
  origin : Option (ChaseNodeOrigin obs rules)
  facts_contain_origin_result : ∀ orig ∈ origin, orig.result.toSet ⊆ facts

namespace RegularChaseNode

variable {obs : ObsolescenceCondition sig} {rules : RuleSet sig}

/-- The `RegularChaseNode` is a `ChaseNode` where ingoingFacts and outgoingFacts are the same. -/
instance regularChaseNodeInstance : ChaseNode (RegularChaseNode obs rules) obs rules where
  ingoingFacts := RegularChaseNode.facts
  outgoingFacts := RegularChaseNode.facts
  origin := RegularChaseNode.origin
  facts_contain_origin_result := RegularChaseNode.facts_contain_origin_result

theorem ingoingFacts_eq {node : RegularChaseNode obs rules} : regularChaseNodeInstance.ingoingFacts node = node.facts := by rfl
theorem outgoingFacts_eq {node : RegularChaseNode obs rules} : regularChaseNodeInstance.outgoingFacts node = node.facts := by rfl

/-- The `RegularChaseNode` has the `ChaseNode.out_sub_in` property. -/
theorem out_sub_in : regularChaseNodeInstance.out_sub_in (N := RegularChaseNode obs rules) := by
  intro node f; rw [ingoingFacts_eq, outgoingFacts_eq]; simp

end RegularChaseNode

