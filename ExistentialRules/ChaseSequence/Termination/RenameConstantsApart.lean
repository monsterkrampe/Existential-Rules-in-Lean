import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]


mutual

  def PreGroundTerm.rename_constants_apart
      [GetFreshRepresentant sig.C]
      (term : FiniteTree (SkolemFS sig) sig.C)
      (forbidden_constants : List sig.C) : FiniteTree (SkolemFS sig) sig.C :=
    match term with
    | .leaf _ => .leaf (GetFreshRepresentant.fresh forbidden_constants)
    | .inner func ts =>
      let recursive_result := PreGroundTerm.rename_constants_apart_list ts forbidden_constants
      .inner func recursive_result

  def PreGroundTerm.rename_constants_apart_list
      [GetFreshRepresentant sig.C]
      (terms : FiniteTreeList (SkolemFS sig) sig.C)
      (forbidden_constants : List sig.C) : FiniteTreeList (SkolemFS sig) sig.C :=
    match terms with
    | .nil => .nil
    | .cons t ts =>
      let t_res := PreGroundTerm.rename_constants_apart t forbidden_constants
      let ts_res := PreGroundTerm.rename_constants_apart_list ts (forbidden_constants ++ t_res.leaves)
      .cons t_res ts_res

end

def GroundTerm.rename_constants_apart
    [GetFreshRepresentant sig.C]
    (term : GroundTerm sig)
    (forbidden_constants : List sig.C) : GroundTerm sig :=
  ⟨PreGroundTerm.rename_constants_apart term.val forbidden_constants, by
    induction term generalizing forbidden_constants with
    | const c => simp [GroundTerm.const, PreGroundTerm.rename_constants_apart, PreGroundTerm.arity_ok]
    | func f ts arity_ok ih =>
      unfold PreGroundTerm.arity_ok
      unfold PreGroundTerm.rename_constants_apart
      simp only [GroundTerm.func, Bool.and_eq_true, beq_iff_eq]
      constructor
      . have : ∀ (l : List (GroundTerm sig)), (PreGroundTerm.rename_constants_apart_list (FiniteTreeList.fromList l.unattach) forbidden_constants).toList.length = l.length := by
          intro l
          induction l generalizing forbidden_constants with
          | nil => simp only [List.unattach_nil, FiniteTreeList.fromList, PreGroundTerm.rename_constants_apart_list, FiniteTreeList.toList, List.length_nil]
          | cons hd tl ih' =>
            simp only [List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.rename_constants_apart_list, FiniteTreeList.toList, List.length_cons, ih']
        rw [this]
        exact arity_ok
      . rw [← PreGroundTerm.arity_ok_list_iff_arity_ok_each_mem]
        have : ∀ (l : List (GroundTerm sig)), (∀ e ∈ l, e ∈ ts) -> (∀ t, t ∈ (PreGroundTerm.rename_constants_apart_list (FiniteTreeList.fromList l.unattach) forbidden_constants).toList -> PreGroundTerm.arity_ok t) := by
          intro l
          induction l generalizing forbidden_constants with
          | nil => intro _ _ contra; simp [FiniteTreeList.fromList, PreGroundTerm.rename_constants_apart_list, FiniteTreeList.toList] at contra
          | cons hd tl ih' =>
            intro h t t_mem
            simp only [List.unattach_cons, FiniteTreeList.fromList, PreGroundTerm.rename_constants_apart_list, FiniteTreeList.toList, List.mem_cons] at t_mem
            cases t_mem with
            | inl t_mem => rw [t_mem]; apply ih; apply h; simp
            | inr t_mem =>
              apply ih'
              . intro e e_mem; apply h; simp [e_mem]
              . exact t_mem
        apply this ts
        simp
  ⟩


def PreTrigger.rename_constants_apart [GetFreshRepresentant sig.C] (trg : PreTrigger sig) : PreTrigger sig :=
  let renamed_apart_terms_for_body_vars : List (GroundTerm sig) := trg.rule.body.vars.foldl (fun acc v =>
    let forbidden_constants := acc.flatMap GroundTerm.constants
    acc ++ [(trg.subs v).rename_constants_apart forbidden_constants]
  ) []

  have length_preserved : ∀ (l : List sig.V) (init : List (GroundTerm sig)), (l.foldl (fun acc v =>
    let forbidden_constants := acc.flatMap GroundTerm.constants
    acc ++ [(trg.subs v).rename_constants_apart forbidden_constants]
  ) init).length = init.length + l.length := by
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih =>
      intro init
      rw [List.foldl_cons]
      rw [ih]
      rw [List.length_append, List.length_cons, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_assoc, Nat.add_comm 1]

  ⟨trg.rule, fun x =>
    if mem : x ∈ trg.rule.body.vars
    then
      let idx := trg.rule.body.vars.idxOf x
      have : idx < renamed_apart_terms_for_body_vars.length := by
        rw [length_preserved, List.length_nil, Nat.zero_add]
        apply List.idxOf_lt_length
        exact mem
      renamed_apart_terms_for_body_vars[idx]
    else trg.subs x -- it should not matter what we return here
  ⟩

