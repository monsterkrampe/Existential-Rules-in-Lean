import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms

/-!
# Models

`FactSet`s can model rules, databases and knowledge bases in a first order logic sense.
Here, we briefly define what this formally means in terms of our definitions.
-/

namespace FactSet

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `FactSet` models a `Database` if the database is a subset of the fact set. -/
def modelsDb (fs : FactSet sig) (db : Database sig) : Prop :=
  db.toFactSet.val ⊆ fs

/-- A `FactSet` models a `Rule` if each substitution that matches the rule body in the fact set can be existended to a substitution for some head of the rule such that this mapped head is already contained in the fact set. The extension of the substitution intuitivly tries to find a suitable mapping for the existential variables that show that the rule is already satisfied (under FOL semantics). -/
def modelsRule (fs : FactSet sig) (rule : Rule sig) : Prop :=
  ∀ (s : GroundSubstitution sig),
    ((s.apply_function_free_conj rule.body).toSet ⊆ fs) ->
      ∃ (i : Fin rule.head.length) (s' : GroundSubstitution sig),
        (∀ v, v ∈ rule.frontier → s' v = s v) ∧
        ((s'.apply_function_free_conj (rule.head.get i)).toSet ⊆ fs)

/-- A `FactSet` models a `RuleSet` if it models each rule. -/
def modelsRules (fs : FactSet sig) (rules : RuleSet sig) : Prop :=
  ∀ r, r ∈ rules.rules -> fs.modelsRule r

/-- A `FactSet` models a `KnowledgeBase` if it models both the database and the rule set. -/
def modelsKb (fs : FactSet sig) (kb : KnowledgeBase sig) : Prop :=
  fs.modelsDb kb.db ∧ fs.modelsRules kb.rules

/-- A `FactSet` $F$ universally models a `KnowledgeBase` if it models the knowledge base but also, for each model $M$ of the knowledge base, we can find a homomorphism from $F$ into $M$. Intuitively, universal models are the *most general* models (but not necessarily the smallest ones). -/
def universallyModelsKb (fs : FactSet sig) (kb : KnowledgeBase sig) : Prop :=
  fs.modelsKb kb ∧
  (∀ (m : FactSet sig), m.modelsKb kb -> ∃ (h : GroundTermMapping sig), h.isHomomorphism fs m)

end FactSet

