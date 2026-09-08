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
abbrev RTrigger (obs : LaxObsolescenceCondition sig) (rs : RuleSet sig) := { trg : Trigger obs // trg.rule ∈ rs}

namespace RTrigger

/-- Two `RTrigger`s are equivalent if the underlying `PreTrigger`s are. -/
abbrev equiv {rs : RuleSet sig} (trg1 trg2 : RTrigger obs rs) : Prop := trg1.val.equiv trg2.val

/-- Lifting the definition from `PreTrigger`. -/
abbrev extend_with_groundTermMapping {rs : RuleSet sig} (trg : RTrigger obs rs) (h : GroundTermMapping sig) : RTrigger obs rs :=
  ⟨trg.val.extend_with_groundTermMapping h, trg.property⟩

/-- We can boil `extend_with_groundTermMapping` down to the `PreTrigger` version again. -/
@[simp, grind =]
theorem val_extend_with_groundTermMapping {rs : RuleSet sig} {trg : RTrigger obs rs} {h : GroundTermMapping sig} :
  (trg.extend_with_groundTermMapping h).val = PreTrigger.extend_with_groundTermMapping trg.val h := rfl

end RTrigger

