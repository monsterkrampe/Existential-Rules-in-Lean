/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.AtomsAndRules.Database
public import ExistentialRules.AtomsAndRules.RuleSet

/-!
# KnowledgeBase

A `KnowledgeBase` is a pair of a `Database` and a `RuleSet`. Note that usually the `RuleSet` is enforced to be finite but we only restrict this in places where we really need this.
-/

public section

structure KnowledgeBase (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  db : Database sig
  rules : RuleSet sig

namespace KnowledgeBase

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `KnowledgeBase` is determinstic if the underlying `RuleSet` is. -/
@[expose]
def isDeterministic (kb : KnowledgeBase sig) : Prop := kb.rules.isDeterministic

end KnowledgeBase

