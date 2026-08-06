/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Nontermination.HeadChoice

/-!
# Unblockability

Here we define what it means for a trigger to be unblockable and we also introduce overapproximations that can be used to witness unblockability.

THIS IS VERY MUCH WORK IN PROGRESS!
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A trigger is unblockable for a given `HeadChoice` if, for every derivation, when the trigger is loaded in a node of the branch indicated by the `HeacChoice`, then the `HeadChoice` result of the trigger also occurs in that branch. In the introducing paper this is called g-unblockable. -/
@[expose]
def Trigger.unblockable
    {obs : ObsolescenceCondition sig}
    (trg : Trigger obs.toLaxObsolescenceCondition)
    (rules : RuleSet sig)
    (hc : HeadChoice sig) : Prop :=
  ∀ td : RegularTreeDerivation obs rules, ∀ node : (td.subderivation_for_headChoice hc).Node, trg.loaded node.val.facts ->
  ∃ node2 : (td.subderivation_for_headChoice hc).Node, node ≼ node2 ∧
  (trg.output_for_headChoice hc).toSet ⊆ node2.val.facts

