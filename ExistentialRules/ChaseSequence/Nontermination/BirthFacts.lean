/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.Triggers.Basic

/-!
# BirthFacts

The birth facts of a trigger are very similar to the backtracking done for the MFA-like conditions only that we
do not consider body atoms here. Therefore, we also do not need to introduce fresh constants. Overall this is all much simpler.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace PreGroundTerm

/-- For a functional `PreGroundTerm`, we can find a `PreTrigger` that introduces it (ignoring how pure body variables are mapped). -/
@[expose]
def birthTrigger
    [Inhabited sig.C]
    (term : PreGroundTerm sig)
    (term_is_func : ∃ func ts, term = .inner func ts)
    (term_arity_ok : PreGroundTerm.arity_ok term) :
    PreTrigger sig :=
  match term with
  | .leaf c => by simp at term_is_func -- contradiction
  | .inner func ts =>
    let subs : GroundSubstitution sig := fun x =>
      if mem : x ∈ func.rule.frontier
      then
        let idx := func.rule.frontier.idxOf x
        have : idx < ts.length := by
          unfold arity_ok at term_arity_ok
          have := LawfulBEq.eq_of_beq (Bool.and_eq_true_iff.mp term_arity_ok).left
          rw [this]; unfold SkolemFS.arity
          exact List.idxOf_lt_length_of_mem mem
        ⟨ts[idx], by
          unfold arity_ok at term_arity_ok
          have := (Bool.and_eq_true_iff.mp term_arity_ok).right
          rw [List.all_eq_true] at this
          apply this ⟨ts[idx], by apply List.getElem_mem⟩
          apply List.mem_attach
        ⟩
      else
        GroundTerm.const default

    { rule := func.rule, subs }


mutual

/-- For a `PreGroundTerm`, we can find the facts necessarily present when the term is "born". These are all facts in the head of the `birthTrigger` for the term as well as all `birthFacts` for the subterms (i.e. the children) or the term. -/
@[expose]
def birthFacts
    [Inhabited sig.C]
    (term : PreGroundTerm sig)
    (term_arity_ok : PreGroundTerm.arity_ok term) :
    List (Fact sig) :=
  match term with
  | .leaf c => []
  | .inner func ts =>
    have term_arity_ok' : ts.length == func.arity && ts.attach.all (fun ⟨t, _⟩ => arity_ok t) := by unfold arity_ok at term_arity_ok; exact term_arity_ok

    let trg : PreTrigger sig := birthTrigger (.inner func ts) (by exists func, ts) term_arity_ok
    let disjIdx := func.headIdx
    have : disjIdx < trg.mapped_head.length := by rw [PreTrigger.length_mapped_head]; exact func.headIdx_lt

    let res_ts := birthFacts_list ts (by
      intro t t_mem
      have := (Bool.and_eq_true_iff.mp term_arity_ok').right
      rw [List.all_eq_true] at this
      apply this ⟨t, t_mem⟩
      apply List.mem_attach
    )

    trg.mapped_head[disjIdx] ++ res_ts

/-- This is just an elaborate way of `flatMap`ping over the terms calling `birthFacts` for each. This way we do not have to show termination explicitely. -/
@[expose]
def birthFacts_list
    [Inhabited sig.C]
    (terms : List (PreGroundTerm sig))
    (terms_arity_ok : ∀ t ∈ terms, PreGroundTerm.arity_ok t) :
    List (Fact sig) :=
  match terms with
  | .nil => []
  | .cons hd tl =>
    let res_hd := birthFacts hd (terms_arity_ok hd (by simp))
    let res_tl := birthFacts_list tl (by intro t t_mem; apply terms_arity_ok; simp [t_mem])
    res_hd ++ res_tl

end

end PreGroundTerm

/-!
We lift the `PreGroundTerm` definitions to `GroundTerm`s.
-/

namespace GroundTerm

@[expose]
def birthTrigger
    [Inhabited sig.C]
    (term : GroundTerm sig)
    (term_is_func : ∃ func ts arity_ok, term = GroundTerm.func func ts arity_ok) :
    PreTrigger sig :=
  PreGroundTerm.birthTrigger term.val (by rcases term_is_func with ⟨func, ts, _, eq⟩; exists func, ts.unattach; rw [eq]; rfl) term.property

@[expose]
def birthFacts [Inhabited sig.C] (term : GroundTerm sig) : List (Fact sig) :=
  PreGroundTerm.birthFacts term.val term.property

@[expose]
def birthFacts_list [Inhabited sig.C] (terms : List (GroundTerm sig)) : List (Fact sig) :=
  terms.flatMap birthFacts

end GroundTerm


namespace PreTrigger

/-- The `PreTrigger.birthFacts` are simply the birth facts of all frontier terms. -/
@[expose]
def birthFacts [Inhabited sig.C] (trg : PreTrigger sig) : List (Fact sig) :=
  GroundTerm.birthFacts_list trg.mapped_frontier

end PreTrigger

