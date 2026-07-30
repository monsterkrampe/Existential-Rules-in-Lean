/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts.Basic

/-!
# Backtracking Facts for a PreGroundTerm

The main outcome of this file is `PreGroundTerm.backtrackFacts`, which returns facts necessarily involved in the derivation of a given functional term.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace PreGroundTerm

/-- For a functional `PreGroundTerm`, we can find a `PreTrigger` that introduces it (while putting fresh constants for body variables). -/
@[expose]
def backtrackTrigger
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    (term : PreGroundTerm sig)
    (term_is_func : ∃ func ts, term = .inner func ts)
    (term_arity_ok : PreGroundTerm.arity_ok term)
    (forbidden_constants : List sig.C) :
    PreTrigger sig :=
  match term with
  | .leaf c => by simp at term_is_func -- contradiction
  | .inner func ts =>
    let fresh_consts_for_pure_body_vars := func.rule.fresh_consts_for_pure_body_vars forbidden_constants

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
        if mem : x ∈ func.rule.pure_body_vars
        then
          let idx := func.rule.pure_body_vars.idxOf x
          have : idx < fresh_consts_for_pure_body_vars.val.length := by
            rw [fresh_consts_for_pure_body_vars.property.left]
            apply List.idxOf_lt_length_of_mem
            exact mem
          GroundTerm.const fresh_consts_for_pure_body_vars.val[idx]
        else
          -- it should not matter what we return here so we also do NOT need to make sure that this does not collide with other constants
          GroundTerm.const default

    { rule := func.rule, subs }

-- This is not nicely possible without a mutual definition. The _list version is quite involved itself.
mutual

  /-- For a `PreGroundTerm`, we can find the facts necessary to introduce this term. These are all facts in the body and head of the `backtrackTrigger` for the term as well as all `backtrackFacts` for the subterms (i.e. the children) or the term. Because we need to know which "fresh" constants have already been used, we also return those. Note that we also take a list of constants that are already forbidden. -/
  @[expose]
  def backtrackFacts
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (term : PreGroundTerm sig)
      (term_arity_ok : PreGroundTerm.arity_ok term)
      (forbidden_constants : List sig.C) :
      -- we return the backtracked facts and all the constants that have been freshly introduced (as a basis for picking other fresh ones)
      (List (Fact sig)) × (List sig.C) :=
    match term with
    | .leaf c => ([], [])
    | .inner func ts =>
      have term_arity_ok' : ts.length == func.arity && ts.attach.all (fun ⟨t, _⟩ => arity_ok t) := by unfold arity_ok at term_arity_ok; exact term_arity_ok

      let trg : PreTrigger sig := backtrackTrigger (.inner func ts) (by exists func, ts) term_arity_ok forbidden_constants
      let disjIdx := func.headIdx
      have : disjIdx < trg.mapped_head.length := by rw [PreTrigger.length_mapped_head]; exact func.headIdx_lt

      let fresh_consts_for_pure_body_vars := trg.rule.fresh_consts_for_pure_body_vars forbidden_constants

      let res_ts := backtrackFacts_list ts (by
        intro t t_mem
        have := (Bool.and_eq_true_iff.mp term_arity_ok').right
        rw [List.all_eq_true] at this
        apply this ⟨t, t_mem⟩
        apply List.mem_attach
      ) (forbidden_constants ++ fresh_consts_for_pure_body_vars)

      ((trg.mapped_body ++ trg.mapped_head[disjIdx]) ++ res_ts.fst, fresh_consts_for_pure_body_vars.val ++ res_ts.snd)

  @[expose]
  def backtrackFacts_list
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      (terms : List (PreGroundTerm sig))
      (terms_arity_ok : ∀ t ∈ terms, PreGroundTerm.arity_ok t)
      (forbidden_constants : List sig.C) :
      (List (Fact sig)) × (List sig.C) :=
    match terms with
    | .nil => ([], [])
    | .cons hd tl =>
      let res_hd := backtrackFacts hd (terms_arity_ok hd (by simp)) forbidden_constants
      let res_tl := backtrackFacts_list tl (by intro t t_mem; apply terms_arity_ok; simp [t_mem]) (forbidden_constants ++ res_hd.snd)
      (res_hd.fst ++ res_tl.fst, res_hd.snd ++ res_tl.snd)

end

theorem backtrackFacts_list_nil
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    {forbidden_constants : List sig.C} :
    backtrackFacts_list [] (by simp) forbidden_constants = ([], []) := by simp [backtrackFacts_list]

theorem backtrackFacts_list_cons
    [GetFreshInhabitant sig.C]
    [Inhabited sig.C]
    {term : PreGroundTerm sig}
    {terms : List (PreGroundTerm sig)}
    {terms_arity_ok : ∀ t ∈ (term :: terms), PreGroundTerm.arity_ok t}
    {forbidden_constants : List sig.C} :
    backtrackFacts_list (term :: terms) terms_arity_ok forbidden_constants =
      let res_t := backtrackFacts term (by apply terms_arity_ok; simp) forbidden_constants
      let res_ts := backtrackFacts_list terms (by intro t t_mem; apply terms_arity_ok; simp [t_mem]) (forbidden_constants ++ res_t.snd)
      (res_t.fst ++ res_ts.fst, res_t.snd ++ res_ts.snd) := by rfl

-- It's good to have this as mutual since we need the result on lists anyway.
mutual

  /-- The fresh constants are indeed not forbidden. -/
  theorem backtrackFacts_fresh_constants_not_forbidden
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {term : PreGroundTerm sig}
      {term_arity_ok : PreGroundTerm.arity_ok term}
      {forbidden_constants : List sig.C} :
      ∀ c ∈ (PreGroundTerm.backtrackFacts term term_arity_ok forbidden_constants).snd, c ∉ forbidden_constants := by
    intro c c_mem
    cases term with
    | leaf _ => simp [backtrackFacts] at c_mem
    | inner func ts =>
      simp only [backtrackFacts] at c_mem
      rw [List.mem_append] at c_mem
      cases c_mem with
      | inl c_mem =>
        let trg : PreTrigger sig := backtrackTrigger (.inner func ts) (by exists func, ts) term_arity_ok forbidden_constants
        let fresh_consts_for_pure_body_vars := trg.rule.fresh_consts_for_pure_body_vars forbidden_constants
        apply fresh_consts_for_pure_body_vars.property.right.right
        exact c_mem
      | inr c_mem => intro contra; apply backtrackFacts_list_fresh_constants_not_forbidden c c_mem; simp [contra]

  theorem backtrackFacts_list_fresh_constants_not_forbidden
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {terms : List (PreGroundTerm sig)}
      {terms_arity_ok : ∀ t ∈ terms, PreGroundTerm.arity_ok t}
      {forbidden_constants : List sig.C} :
      ∀ c ∈ (PreGroundTerm.backtrackFacts_list terms terms_arity_ok forbidden_constants).snd, c ∉ forbidden_constants := by
    intro c c_mem
    cases terms with
    | nil => simp [backtrackFacts_list_nil] at c_mem
    | cons hd tl =>
      rw [backtrackFacts_list_cons] at c_mem
      rw [List.mem_append] at c_mem
      cases c_mem with
      | inl c_mem => exact backtrackFacts_fresh_constants_not_forbidden c c_mem
      | inr c_mem =>
        intro contra
        apply backtrackFacts_list_fresh_constants_not_forbidden c c_mem
        simp [contra]

end

mutual

  /-- Each constant in `PreGroundTerm.backtrackFacts` is in the rule set, a leaf in the term, or a fresh constant. -/
  theorem backtrackFacts_constants_in_rules_or_term_or_fresh
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {term : PreGroundTerm sig}
      {term_arity_ok : PreGroundTerm.arity_ok term}
      {forbidden_constants : List sig.C} :
      ∀ f ∈ (PreGroundTerm.backtrackFacts term term_arity_ok forbidden_constants).fst,
      ∀ c ∈ f.constants,
        c ∈ (term.innerLabels.flatMap (Rule.constants ∘ SkolemFS.rule)) ∨ c ∈ term.leaves ∨ c ∈ (PreGroundTerm.backtrackFacts term term_arity_ok forbidden_constants).snd := by
    intro f f_mem c c_mem
    cases term with
    | leaf _ => simp [backtrackFacts] at f_mem
    | inner func ts =>
      simp only [backtrackFacts] at f_mem
      rw [List.mem_append] at f_mem
      cases f_mem with
      | inl f_mem =>
        let trg := backtrackTrigger (.inner func ts) (by exists func, ts) term_arity_ok forbidden_constants
        rw [List.mem_append] at f_mem
        cases f_mem with
        | inl f_mem =>
          unfold Fact.constants at c_mem
          rw [List.mem_flatMap] at c_mem
          rcases c_mem with ⟨t, t_mem, c_mem⟩
          have t_mem : t ∈ trg.mapped_body.flatMap GeneralizedAtom.terms := by rw [List.mem_flatMap]; exists f
          rw [PreTrigger.mem_terms_mapped_body_iff] at t_mem
          cases t_mem with
          | inl t_mem =>
            rcases t_mem with ⟨d, d_mem, t_eq⟩
            apply Or.inl
            rw [List.mem_flatMap]
            exists func
            constructor
            . simp [FiniteTree.innerLabels]
            . rw [Function.comp_apply]
              unfold Rule.constants
              rw [List.mem_append]
              apply Or.inl
              rw [← t_eq, GroundTerm.constants_const, List.mem_singleton] at c_mem
              rw [c_mem]
              exact d_mem
          | inr t_mem =>
            rcases t_mem with ⟨v, v_mem, t_eq⟩
            simp only [trg, backtrackTrigger] at t_eq
            cases Decidable.em (v ∈ trg.rule.frontier) with
            | inl v_mem_frontier =>
              apply Or.inr
              apply Or.inl
              simp only [trg, backtrackTrigger] at v_mem_frontier
              simp only [v_mem_frontier, ↓reduceDIte] at t_eq
              rw [← t_eq] at c_mem
              simp only [GroundTerm.constants] at c_mem
              simp only [FiniteTree.leaves]
              rw [List.mem_flatMap]
              exists t.val
              rw [← t_eq]
              constructor
              . apply List.getElem_mem
              . exact c_mem
            | inr v_not_mem_frontier =>
              have v_mem_pure_body_vars : v ∈ trg.rule.pure_body_vars := by
                simp only [Rule.pure_body_vars, List.mem_filter]
                constructor
                . exact v_mem
                . apply decide_eq_true; exact v_not_mem_frontier
              apply Or.inr
              apply Or.inr
              simp only [trg, backtrackTrigger] at v_not_mem_frontier
              simp only [v_not_mem_frontier, ↓reduceDIte] at t_eq
              simp only [trg, backtrackTrigger] at v_mem_pure_body_vars
              simp only [v_mem_pure_body_vars, ↓reduceDIte] at t_eq
              rw [← t_eq] at c_mem
              rw [GroundTerm.constants_const, List.mem_singleton] at c_mem
              simp only [backtrackFacts]
              rw [List.mem_append]
              apply Or.inl
              rw [c_mem]
              apply List.getElem_mem
        | inr f_mem =>
          have headIdx_lt : func.headIdx < trg.mapped_head.length := by rw [PreTrigger.length_mapped_head]; exact func.headIdx_lt
          have c_mem : c ∈ FactSet.constants trg.mapped_head[func.headIdx].toSet := by exists f; rw [List.mem_toSet]; exact ⟨f_mem, c_mem⟩
          have c_mem := trg.mapped_head_constants_subset func.headIdx func.headIdx_lt c c_mem
          rw [List.mem_toSet, List.mem_append] at c_mem
          cases c_mem with
          | inl c_mem =>
            apply Or.inr
            apply Or.inl
            rw [List.mem_flatMap] at c_mem
            rcases c_mem with ⟨t, t_mem, c_mem⟩
            rw [List.mem_map] at t_mem
            rcases t_mem with ⟨v, v_mem, t_eq⟩
            unfold PreTrigger.subs_for_mapped_head at t_eq
            rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ v v_mem] at t_eq
            simp only [trg, backtrackTrigger] at v_mem
            simp only [trg, backtrackTrigger, v_mem, ↓reduceDIte] at t_eq
            rw [← t_eq] at c_mem
            simp only [GroundTerm.constants] at c_mem
            simp only [FiniteTree.leaves]
            rw [List.mem_flatMap]
            exists t.val
            rw [← t_eq]
            constructor
            . apply List.getElem_mem
            . exact c_mem
          | inr c_mem =>
            apply Or.inl
            rw [List.mem_flatMap]
            exists func
            constructor
            . simp [FiniteTree.innerLabels]
            . rw [Function.comp_apply]
              unfold Rule.constants
              rw [List.mem_append]
              apply Or.inr
              rw [List.mem_flatMap]
              exists trg.rule.head[func.headIdx]'(func.headIdx_lt)
              constructor
              . apply List.getElem_mem
              . exact c_mem
      | inr f_mem =>
        simp only [FiniteTree.leaves, PreGroundTerm.backtrackFacts]
        cases PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f f_mem c c_mem with
        | inl c_mem => apply Or.inl; unfold FiniteTree.innerLabels; rw [List.flatMap_cons]; apply List.mem_append_right; exact c_mem
        | inr c_mem =>
          apply Or.inr
          cases c_mem with
          | inl c_mem => apply Or.inl; exact c_mem
          | inr c_mem => apply Or.inr; rw [List.mem_append]; apply Or.inr; exact c_mem

  theorem backtrackFacts_list_constants_in_rules_or_term_or_fresh
      [GetFreshInhabitant sig.C]
      [Inhabited sig.C]
      {terms : List (PreGroundTerm sig)}
      {terms_arity_ok : ∀ t ∈ terms, PreGroundTerm.arity_ok t}
      {forbidden_constants : List sig.C} :
      ∀ f ∈ (PreGroundTerm.backtrackFacts_list terms terms_arity_ok forbidden_constants).fst,
      ∀ c ∈ f.constants,
        c ∈ ((terms.flatMap FiniteTree.innerLabels).flatMap (Rule.constants ∘ SkolemFS.rule)) ∨ c ∈ terms.flatMap FiniteTree.leaves ∨ c ∈ (PreGroundTerm.backtrackFacts_list terms terms_arity_ok forbidden_constants).snd := by
    intro f f_mem c c_mem
    cases terms with
    | nil => simp [backtrackFacts_list] at f_mem
    | cons hd tl =>
      simp only [backtrackFacts_list] at f_mem
      rw [List.mem_append] at f_mem
      cases f_mem with
      | inl f_mem =>
        cases PreGroundTerm.backtrackFacts_constants_in_rules_or_term_or_fresh f f_mem c c_mem with
        | inl c_mem => apply Or.inl; rw [List.flatMap_cons, List.flatMap_append]; apply List.mem_append_left; exact c_mem
        | inr c_mem =>
          apply Or.inr
          cases c_mem with
          | inl c_mem => apply Or.inl; rw [List.flatMap_cons, List.mem_append]; apply Or.inl; exact c_mem
          | inr c_mem => apply Or.inr; simp only [backtrackFacts_list]; rw [List.mem_append]; apply Or.inl; exact c_mem
      | inr f_mem =>
        cases PreGroundTerm.backtrackFacts_list_constants_in_rules_or_term_or_fresh f f_mem c c_mem with
        | inl c_mem => apply Or.inl; rw [List.flatMap_cons, List.flatMap_append]; apply List.mem_append_right; exact c_mem
        | inr c_mem =>
          apply Or.inr
          cases c_mem with
          | inl c_mem => apply Or.inl; rw [List.flatMap_cons, List.mem_append]; apply Or.inr; exact c_mem
          | inr c_mem => apply Or.inr; simp only [backtrackFacts_list]; rw [List.mem_append]; apply Or.inr; exact c_mem

end

end PreGroundTerm

