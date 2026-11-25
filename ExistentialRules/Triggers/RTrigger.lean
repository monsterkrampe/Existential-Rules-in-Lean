/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.AtomsAndRules.RuleSet
public import ExistentialRules.Triggers.Basic

/-!
# Ruleset Triggers

We introduce one more layer on top of `PreTrigger`s, which we call `RTrigger` for Ruleset Trigger.
It makes sense that, when we want to chase a set of rules, we only consider triggers that feature rules that indeed occur in the rule set.
We capture this simply in a subtype.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- An `RTrigger` for a `RuleSet` $R$ is a `Trigger` with a rule in $R$. -/
abbrev RTrigger (rs : RuleSet sig) := { trg : PreTrigger sig // trg.rule ∈ rs}

namespace RTrigger

/-- Two `RTrigger`s are equivalent if the underlying `PreTrigger`s are. -/
abbrev equiv {rs : RuleSet sig} (trg1 trg2 : RTrigger rs) : Prop := trg1.val.equiv trg2.val

/-- Two `RTrigger`s are strongly equivalent if the underlying `PreTrigger`s are. -/
abbrev strong_equiv {rs : RuleSet sig} (trg1 trg2 : RTrigger rs) : Prop := trg1.val.strong_equiv trg2.val

/-- Lifting the definition from `PreTrigger`. -/
abbrev extend_with_groundTermMapping {rs : RuleSet sig} (trg : RTrigger rs) (h : GroundTermMapping sig) : RTrigger rs :=
  ⟨trg.val.extend_with_groundTermMapping h, trg.property⟩

/-- We can boil `extend_with_groundTermMapping` down to the `PreTrigger` version again. -/
@[simp, grind =]
theorem val_extend_with_groundTermMapping {rs : RuleSet sig} {trg : RTrigger rs} {h : GroundTermMapping sig} :
  (trg.extend_with_groundTermMapping h).val = PreTrigger.extend_with_groundTermMapping trg.val h := rfl

end RTrigger

