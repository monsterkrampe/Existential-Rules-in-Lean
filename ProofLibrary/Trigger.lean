import ProofLibrary.List
import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.SubstitutionAndHomomorphismBasics

structure Trigger where
  rule : Rule
  subs : GroundSubstitution

namespace Trigger
  def loaded (trg : Trigger) (F : FactSet) : Prop :=
    let l : List Fact := SubsTarget.apply trg.subs trg.rule.body
    l ⊆ F

  def sactive (trg : Trigger) (F : FactSet) : Prop :=
    loaded trg F ∧ ¬ (
      let l : List Fact := SubsTarget.apply trg.subs (Rule.skolemize trg.rule).head
      l ⊆ F
    )

  def ractive (trg : Trigger) (F : FactSet) : Prop :=
    loaded trg F ∧ ¬ (
      ∃ s : GroundSubstitution,
        (∀ v, List.elem v (Rule.frontier trg.rule) → s v = trg.subs v) ∧
        (
          let l : List Fact := SubsTarget.apply s trg.rule.head
          l ⊆ F
        )
    )

  def result (trg : Trigger) : FactSet :=
    let l : List Fact := SubsTarget.apply trg.subs (Rule.skolemize trg.rule).head
    List.toSet l
end Trigger

namespace FactSet
  def modelsDb (fs : FactSet) (db : Database) : Prop :=
    db.toFactSet ⊆ fs

  def modelsRule (fs : FactSet) (rule : Rule) : Prop :=
    ∀ trg : Trigger,
      (trg.rule = rule ∧ trg.loaded fs)
      -> ¬ trg.ractive fs -- the rule is ractive iff it is not satisfied under FOL semantics

  def modelsRules (fs : FactSet) (rules : RuleSet) : Prop :=
    ∀ r, r ∈ rules -> fs.modelsRule r

  def modelsKb (fs : FactSet) (kb : KnowledgeBase) : Prop :=
    fs.modelsDb kb.db ∧ fs.modelsRules kb.rules
end FactSet
