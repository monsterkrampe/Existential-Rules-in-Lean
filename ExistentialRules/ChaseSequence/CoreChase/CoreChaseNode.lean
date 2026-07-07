/-
Copyright 2026 Henrik Tscherny, Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.Models.Cores
public import ExistentialRules.ChaseSequence.ChaseNode

/-!
# Core Chase Node

Similar to a `ChaseNode`, we define another elements of the core chase in a similar fashion.
Besides fact set and origin, these also store the core that the fact set is being condensed to. In principle any such core is allowed and we do not enforce a specific computation procedure.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The CoreChaseNode add a couple of fields on top of the RegularChaseNode but the `facts` field has a different meaning. This is why we duplicate the structure and not jsut extend it. We want to prevent that the `CoreChaseNode` is accidentally treated as a `RegularChaseNode`. -/
structure CoreChaseNode (rules : RuleSet sig) where
  facts : FactSet sig
  origin : Option ((trg : RTrigger (RestrictedObsolescence sig) rules) × Fin trg.val.mapped_head.length)
  facts_contain_origin_result : ∀ orig ∈ origin, orig.fst.val.mapped_head[orig.snd.val].toSet ⊆ facts
  core : FactSet sig
  isWeakCore : core.isWeakCore
  homSubset : core.homSubset facts

namespace CoreChaseNode

variable {rules : RuleSet sig}

/-- The `CoreChaseNode` is a `ChaseNode` where the outgoingFacts are a core of the ingoingFacts. -/
instance coreChaseNodeInstance : ChaseNode (CoreChaseNode rules) (RestrictedObsolescence sig) rules where
  ingoingFacts := CoreChaseNode.facts
  outgoingFacts := CoreChaseNode.core
  origin := CoreChaseNode.origin
  facts_contain_origin_result := CoreChaseNode.facts_contain_origin_result

theorem ingoingFacts_eq {node : CoreChaseNode rules} : coreChaseNodeInstance.ingoingFacts node = node.facts := by rfl
theorem outgoingFacts_eq {node : CoreChaseNode rules} : coreChaseNodeInstance.outgoingFacts node = node.core := by rfl

/-- The `CoreChaseNode` has the `ChaseNode.out_sub_in` property. -/
theorem out_sub_in : coreChaseNodeInstance.out_sub_in (N := CoreChaseNode rules) := by
  intro node f; rw [ingoingFacts_eq, outgoingFacts_eq]; exact node.homSubset.left f

end CoreChaseNode

