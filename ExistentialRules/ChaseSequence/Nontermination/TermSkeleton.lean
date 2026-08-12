/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Nontermination.BirthFacts

/-!
# TermSkeleton

The term skeleton of a trigger are all terms involved in its birth facts.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace PreTrigger

/-- All constants that occur directly in the image of the substution applied to the frontier variables.
This does NOT include constants occurring in functional terms. -/
def frontierConstants (trg : PreTrigger sig) : List sig.C :=
  trg.mapped_frontier.filterMap (fun t =>
    match t.val with
    | .leaf c => some c
    | _ => none
  )

/-- The `termSkeleton` of a `PreTrigger` consists of the terms of all birth facts as well as the `frontierConstants`. -/
def termSkeleton [Inhabited sig.C] (trg : PreTrigger sig) : List (GroundTerm sig) :=
  ((trg.birthFacts).flatMap GeneralizedAtom.terms) ++ (trg.frontierConstants.map GroundTerm.const)

end PreTrigger

