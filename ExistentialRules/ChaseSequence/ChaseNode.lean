import ExistentialRules.Triggers.RTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-!
# Chase Node

The chase is a pretty simple procedure. From an initial fact set, it creates a new fact set by applying a trigger and it continues to do this until all triggers are obsolete.
In this process, we obtain a (potentially infinite) sequence of fact sets.
It can be very useful to also keep track of the associated triggers and this is why we capture both the fact set and used trigger of individual chase steps in a `ChaseNode`.
-/

/-- A `ChaseNode` corresponds to a chase step. It must contain a `FactSet` and optionally an `RTrigger` and a head disjunct index indicating that the current `ChaseNode` was obtained by applying the specified trigger and picking the indicated head disjunct. It is optional since the initial fact set does not result from a trigger but on all following nodes, this value will be set (and we will prove that it is). For convenience, the chase node also directly includes a proof that the result of its origin is indeed contained in its fact set. -/
structure ChaseNode (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  facts : FactSet sig
  -- the origin is none only for the database
  origin : Option ((trg : RTrigger (obs : LaxObsoletenessCondition sig) rules) × Fin trg.val.mapped_head.length)
  facts_contain_origin_result : ∀ orig ∈ origin, orig.fst.val.mapped_head[orig.snd.val].toSet ⊆ facts

namespace ChaseNode

/-- The `origin_result` denotes the facts that have been introduced for the chase node. That is, the mapped head index for the trigger stored in the origin field of the `ChaseNode`. -/
def origin_result {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) (isSome : node.origin.isSome) :
    List (Fact sig) :=
  let origin := node.origin.get isSome
  origin.fst.val.mapped_head[origin.snd.val]

end ChaseNode

