/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Nontermination.Unblockability
public import ExistentialRules.ChaseSequence.Nontermination.ReversibleConstantMappings
public import ExistentialRules.ChaseSequence.Nontermination.TermSkeleton

open CustomBasicDatastructures

/-!
# Repeatable Unblockability

Here we define a generic notion of `RepeatableUnblockability` that can be instatiated with specific notions later.
This is similar to how the `ObsoloscenceCondition` captures `SkolemObsolescence` and `RestrictedObsoloscence` at the same time.
The difference in the specific conditions is a key difference of RPC and DRPC.
-/

public section

/-- This is the function signature that our specific unblockability overapproximations will follow. -/
abbrev OverapproximationFunction (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] :=
  RuleSet sig -> HeadChoice sig -> PreTrigger sig -> FactSet sig

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace OverapproximationFunction

variable {obs : ObsolescenceCondition sig}

/-- A trigger is unblockable with respect to a specific overapproximation function
if it is deterministic Datalog or if it is not obsolete for the overapproxmiation. -/
def trigger_unblockable (overapprox : OverapproximationFunction sig)
    (rs : RuleSet sig) (hc : HeadChoice sig) (trg : Trigger obs.toLaxObsolescenceCondition) : Prop :=
  (trg.rule.isDatalog ∧ trg.rule.isDeterministic) ∨ ¬ obs.cond trg (overapprox rs hc trg)

/-- This rather involved condition makes sure that a trigger can be repeated in the sense that applying a reversible constant mapping after
the substitution yields a trigger that is unblockable, given that the original trigger was also unblockable.
This is the condition proven in Lemma 4 in the [RPC] paper. -/
@[expose]
def trigger_repeatable [Inhabited sig.C] (overapprox : OverapproximationFunction sig)
    (rs : RuleSet sig) (hc : HeadChoice sig) (trg : Trigger obs.toLaxObsolescenceCondition) : Prop :=
  ∀ (g : ConstantMapping sig), g.isReversible trg.termSkeleton.toSet ->
    (overapprox.trigger_unblockable rs hc trg) ->
    (overapprox.trigger_unblockable rs hc (trg.extend_with_groundTermMapping g.apply_ground_term))

end OverapproximationFunction

/-- A `RepeatableUnblockability` condition is an overapproximation function for that we know that the function result adheres to `is_rpc_overapproximation` and for that the `trigger_unblockable` property holds for each trigger. -/
structure RepeatableUnblockability [Inhabited sig.C] (obs : ObsolescenceCondition sig) where
  overapprox : OverapproximationFunction sig
  rpc_overapprox : ∀ rs hc (trg : Trigger obs.toLaxObsolescenceCondition), (overapprox rs hc trg.toPreTrigger).is_rpc_overapproximation rs hc trg
  repeatable : ∀ rs hc (trg : Trigger obs.toLaxObsolescenceCondition), overapprox.trigger_repeatable rs hc trg

namespace RepeatableUnblockability

variable [Inhabited sig.C] {obs : ObsolescenceCondition sig}

/-- We lift the `OverapproximationFunction.trigger_unblockable` property to `RepeatableUnblockability` in the obvious way. -/
@[expose]
def trigger_unblockable (unblk : RepeatableUnblockability obs) (rs : RuleSet sig) (hc : HeadChoice sig) (trg : Trigger obs.toLaxObsolescenceCondition) : Prop :=
  unblk.overapprox.trigger_unblockable rs hc trg

/-- If `RepeatableUnblockability.trigger_unblockable` holds for a trigger, then `Trigger.rsUnblockable` follows.
This is due to the `RepeatableUnblockability.rpc_overapprox` condition and follows mainly from `RTrigger.unblockable_of_not_obsolete_for_overapproximation`. -/
theorem rsUnblockable_of_trigger_unblockable
    (obs_propagates : obs.propagates_under_term_mapping_of_no_fresh_term_occurs)
    {unblk : RepeatableUnblockability obs}
    {rs : RuleSet sig} {hc : HeadChoice sig}
    (hc_consistent : hc.consistent_for_equivalent_triggers)
    (trg : RTrigger obs rs) :
    unblk.trigger_unblockable rs hc trg.val -> trg.val.rsUnblockable rs hc := by
  intro unblockable_for_condition
  cases unblockable_for_condition with
  | inl isDetDatalog => exact Trigger.rsUnblockable_of_isDatalog_of_isDeterministic isDetDatalog.left isDetDatalog.right
  | inr not_obs =>
    apply trg.rsUnblockable_of_not_obsolete_for_overapproximation obs_propagates hc_consistent (unblk.rpc_overapprox rs hc trg.val)
    exact not_obs

/--
As for general unblockability, if a trigger features at least one existentially quantified variable and
only constants as frontier terms, then it cannot be unblockable.
This follows directly from `Trigger.not_rsUnblockable_of_hc_exis_of_frontier_only_constants` and
the contraposition of `rsUnblockable_of_trigger_unblockable`.
-/
theorem not_unblockable_of_hc_exis_of_frontier_only_constants
    (obs_propagates : obs.propagates_under_term_mapping_of_no_fresh_term_occurs)
    {unblk : RepeatableUnblockability obs}
    {rs : RuleSet sig} {hc : HeadChoice sig}
    (hc_consistent : hc.consistent_for_equivalent_triggers)
    (trg : RTrigger obs rs)
    (hc_exis : trg.val.rule.existential_vars_for_head_disjunct (hc trg.val).val (hc trg.val).isLt ≠ [])
    (frontier_only_constants : ∀ t ∈ trg.val.mapped_frontier, ∃ c, t = .const c) :
    ¬ unblk.trigger_unblockable rs hc trg.val := by
  intro contra
  apply Trigger.not_rsUnblockable_of_hc_exis_of_frontier_only_constants hc_exis frontier_only_constants
  exact rsUnblockable_of_trigger_unblockable obs_propagates hc_consistent trg contra

end RepeatableUnblockability

