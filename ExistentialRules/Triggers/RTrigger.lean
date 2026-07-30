/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.AtomsAndRules.RuleSet
public import ExistentialRules.Triggers.Obsolescence

/-!
# Ruleset Triggers

`Trigger`s are still not enough yet. We introduce one more layer on top, which we call `RTrigger` for Ruleset Trigger.
It makes sense that, when we want to chase a set of rules, we only consider triggers that feature rules that indeed occur in the rule set.
We capture this simply in a subtype.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : LaxObsolescenceCondition sig}

/-- An `RTrigger` for a `RuleSet` $R$ is a `Trigger` with a rule in $R$. -/
@[expose]
def RTrigger (obs : LaxObsolescenceCondition sig) (rs : RuleSet sig) := { trg : Trigger obs // trg.rule ∈ rs}

namespace RTrigger

/-- Two `RTrigger`s are equivalent if the underlying `PreTrigger`s are. -/
abbrev equiv {rs : RuleSet sig} (trg1 trg2 : RTrigger obs rs) : Prop := trg1.val.equiv trg2.val

end RTrigger

