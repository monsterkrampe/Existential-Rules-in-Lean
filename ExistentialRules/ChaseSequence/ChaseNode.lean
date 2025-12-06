import ExistentialRules.Triggers.RTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

structure ChaseNode (obs : ObsoletenessCondition sig) (rules : RuleSet sig) where
  facts : { fs : FactSet sig // fs.finite }
  -- the origin is none only for the database
  origin : Option ((trg : RTrigger (obs : LaxObsoletenessCondition sig) rules) × Fin trg.val.mapped_head.length)
  facts_contain_origin_result : origin.is_none_or (fun origin => origin.fst.val.mapped_head[origin.snd.val].toSet ⊆ facts)

namespace ChaseNode

  def origin_result {obs : ObsoletenessCondition sig} (node : ChaseNode obs rules) (isSome : node.origin.isSome) :
      List (Fact sig) :=
    let origin := node.origin.get isSome
    origin.fst.val.mapped_head[origin.snd.val]

end ChaseNode

