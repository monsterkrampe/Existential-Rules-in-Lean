/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.TreeDerivation

/-!
# Unblockability

Here we define what it means for a trigger to be unblockable and we also introduce overapproximations that can be used to witness unblockability.

THIS IS VERY MUCH WORK IN PROGRESS!
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A trigger is unblockable if its result necessarily occurs in every derivation where the trigger is loaded. In the introducing paper this is called g-unblockable. -/
@[expose]
def Trigger.unblockable
    {obs : ObsolescenceCondition sig}
    (trg : Trigger obs.toLaxObsolescenceCondition)
    (i : Nat)
    (lt : i < trg.rule.head.length)
    (rules : RuleSet sig) : Prop :=
  ∀ td : RegularTreeDerivation obs rules, ∀ node : td.NodeWithAddress, trg.loaded node.node.facts ->
  ∃ node2 : td.NodeWithAddress, node ≼ node2 ∧
  (trg.mapped_head[i]'(by grind)).toSet ⊆ node2.node.facts

