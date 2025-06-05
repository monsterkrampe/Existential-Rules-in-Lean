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

mutual

  theorem PreGroundTerm.rename_constants_apart_preserves_ruleId_validity [GetFreshRepresentant sig.C] (term : FiniteTree (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, PreGroundTerm.skolem_ruleIds_valid rl term -> PreGroundTerm.skolem_ruleIds_valid rl (PreGroundTerm.rename_constants_apart term forbidden_constants) := by
    intro rl valid
    cases term with
    | leaf _ => simp [rename_constants_apart, skolem_ruleIds_valid]
    | inner func ts =>
      simp only [rename_constants_apart, skolem_ruleIds_valid] at *
      constructor
      . exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_ruleId_validity_list; exact valid.right

  theorem PreGroundTerm.rename_constants_apart_preserves_ruleId_validity_list [GetFreshRepresentant sig.C] (terms : FiniteTreeList (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, PreGroundTerm.skolem_ruleIds_valid_list rl terms -> PreGroundTerm.skolem_ruleIds_valid_list rl (PreGroundTerm.rename_constants_apart_list terms forbidden_constants) := by
    intro rl valid
    cases terms with
    | nil => simp [rename_constants_apart_list, skolem_ruleIds_valid_list]
    | cons hd tl =>
      simp only [rename_constants_apart_list, skolem_ruleIds_valid_list] at *
      constructor
      . apply PreGroundTerm.rename_constants_apart_preserves_ruleId_validity; exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_ruleId_validity_list; exact valid.right

end

mutual

  theorem PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity [GetFreshRepresentant sig.C] (term : FiniteTree (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid rl term) -> PreGroundTerm.skolem_disjIdx_valid rl term h -> PreGroundTerm.skolem_disjIdx_valid rl (PreGroundTerm.rename_constants_apart term forbidden_constants) (PreGroundTerm.rename_constants_apart_preserves_ruleId_validity term forbidden_constants rl h) := by
    intro rl _ valid
    cases term with
    | leaf _ => simp [rename_constants_apart, skolem_disjIdx_valid]
    | inner func ts =>
      simp only [rename_constants_apart, skolem_disjIdx_valid] at *
      constructor
      . exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity_list; exact valid.right

  theorem PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity_list [GetFreshRepresentant sig.C] (terms : FiniteTreeList (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid_list rl terms) -> PreGroundTerm.skolem_disjIdx_valid_list rl terms h -> PreGroundTerm.skolem_disjIdx_valid_list rl (PreGroundTerm.rename_constants_apart_list terms forbidden_constants) (PreGroundTerm.rename_constants_apart_preserves_ruleId_validity_list terms forbidden_constants rl h) := by
    intro rl _ valid
    cases terms with
    | nil => simp [rename_constants_apart_list, skolem_disjIdx_valid_list]
    | cons hd tl =>
      simp only [rename_constants_apart_list, skolem_disjIdx_valid_list] at *
      constructor
      . apply PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity; exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity_list; exact valid.right

end

mutual

  theorem PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity [GetFreshRepresentant sig.C] (term : FiniteTree (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid rl term) -> PreGroundTerm.skolem_rule_arity_valid rl term h -> PreGroundTerm.skolem_rule_arity_valid rl (PreGroundTerm.rename_constants_apart term forbidden_constants) (PreGroundTerm.rename_constants_apart_preserves_ruleId_validity term forbidden_constants rl h) := by
    intro rl _ valid
    cases term with
    | leaf _ => simp [rename_constants_apart, skolem_rule_arity_valid]
    | inner func ts =>
      simp only [rename_constants_apart, skolem_rule_arity_valid] at *
      constructor
      . exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity_list; exact valid.right

  theorem PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity_list [GetFreshRepresentant sig.C] (terms : FiniteTreeList (SkolemFS sig) sig.C) (forbidden_constants : List sig.C) :
      ∀ rl, (h : PreGroundTerm.skolem_ruleIds_valid_list rl terms) -> PreGroundTerm.skolem_rule_arity_valid_list rl terms h -> PreGroundTerm.skolem_rule_arity_valid_list rl (PreGroundTerm.rename_constants_apart_list terms forbidden_constants) (PreGroundTerm.rename_constants_apart_preserves_ruleId_validity_list terms forbidden_constants rl h) := by
    intro rl _ valid
    cases terms with
    | nil => simp [rename_constants_apart_list, skolem_rule_arity_valid_list]
    | cons hd tl =>
      simp only [rename_constants_apart_list, skolem_rule_arity_valid_list] at *
      constructor
      . apply PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity; exact valid.left
      . apply PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity_list; exact valid.right

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

theorem GroundTerm.rename_constants_apart_preserves_ruleId_validity [GetFreshRepresentant sig.C] (term : GroundTerm sig) (forbidden_constants : List sig.C) :
    ∀ rl, GroundTerm.skolem_ruleIds_valid rl term -> GroundTerm.skolem_ruleIds_valid rl (GroundTerm.rename_constants_apart term forbidden_constants) := by
  intro rl valid
  simp only [rename_constants_apart, skolem_ruleIds_valid] at *
  apply PreGroundTerm.rename_constants_apart_preserves_ruleId_validity
  exact valid

theorem GroundTerm.rename_constants_apart_preserves_disjIdx_validity [GetFreshRepresentant sig.C] (term : GroundTerm sig) (forbidden_constants : List sig.C) :
    ∀ rl, (h : GroundTerm.skolem_ruleIds_valid rl term) -> GroundTerm.skolem_disjIdx_valid rl term h -> GroundTerm.skolem_disjIdx_valid rl (GroundTerm.rename_constants_apart term forbidden_constants) (GroundTerm.rename_constants_apart_preserves_ruleId_validity term forbidden_constants rl h) := by
  intro rl _ valid
  simp only [rename_constants_apart, skolem_ruleIds_valid] at *
  apply PreGroundTerm.rename_constants_apart_preserves_disjIdx_validity
  exact valid

theorem GroundTerm.rename_constants_apart_preserves_rule_arity_validity [GetFreshRepresentant sig.C] (term : GroundTerm sig) (forbidden_constants : List sig.C) :
    ∀ rl, (h : GroundTerm.skolem_ruleIds_valid rl term) -> GroundTerm.skolem_rule_arity_valid rl term h -> GroundTerm.skolem_rule_arity_valid rl (GroundTerm.rename_constants_apart term forbidden_constants) (GroundTerm.rename_constants_apart_preserves_ruleId_validity term forbidden_constants rl h) := by
  intro rl _ valid
  simp only [rename_constants_apart, skolem_ruleIds_valid] at *
  apply PreGroundTerm.rename_constants_apart_preserves_rule_arity_validity
  exact valid

def PreTrigger.rename_constants_apart [GetFreshRepresentant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) : PreTrigger sig :=
  let renamed_apart_terms_for_body_vars : List (GroundTerm sig) := trg.rule.body.vars.foldl (fun acc v =>
    let forbidden_constants_inner := acc.flatMap GroundTerm.constants
    acc ++ [(trg.subs v).rename_constants_apart (forbidden_constants ++ forbidden_constants_inner)]
  ) []

  have length_preserved : ∀ (l : List sig.V) (init : List (GroundTerm sig)), (l.foldl (fun acc v =>
    let forbidden_constants_inner := acc.flatMap GroundTerm.constants
    acc ++ [(trg.subs v).rename_constants_apart (forbidden_constants ++ forbidden_constants_inner)]
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

-- TODO: the following three proofs seem way too complicated; maybe I'm too tired already to see how to simplify; or it's really that bad...
theorem PreTrigger.rename_constants_apart_preserves_ruleId_validity [GetFreshRepresentant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) :
    ∀ rl, PreTrigger.skolem_ruleIds_valid rl trg -> PreTrigger.skolem_ruleIds_valid rl (PreTrigger.rename_constants_apart trg forbidden_constants) := by
  intro rl valid
  simp only [rename_constants_apart, skolem_ruleIds_valid] at *
  intro t t_mem
  rw [List.mem_flatMap] at t_mem
  rcases t_mem with ⟨f, f_mem, t_mem⟩
  simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj] at f_mem
  rw [List.mem_map] at f_mem
  simp only [GroundSubstitution.apply_function_free_atom] at f_mem
  rcases f_mem with ⟨a, a_mem, f_eq⟩
  rw [← f_eq] at t_mem
  simp only at t_mem
  rw [List.mem_map] at t_mem
  rcases t_mem with ⟨voc, voc_mem, t_eq⟩
  rw [← t_eq]
  cases voc with
  | const c =>
    simp only [GroundSubstitution.apply_var_or_const]
    apply GroundTerm.skolem_ruleIds_valid_const
  | var v =>
    have : v ∈ trg.rule.body.vars := by
      unfold FunctionFreeConjunction.vars
      rw [List.mem_flatMap]
      exists a
      constructor
      . exact a_mem
      . unfold FunctionFreeAtom.variables
        apply VarOrConst.mem_filterVars_of_var
        exact voc_mem
    simp only [GroundSubstitution.apply_var_or_const, this, ↓reduceDIte]

    have : ∀ (l : List sig.V) (subset : l ⊆ trg.rule.body.vars) (init : List (GroundTerm sig)) (init_valid : ∀ t ∈ init, t.skolem_ruleIds_valid rl) (t : GroundTerm sig), t ∈ (l.foldl (fun acc v =>
      let forbidden_constants_inner := acc.flatMap GroundTerm.constants
      acc ++ [(trg.subs v).rename_constants_apart (forbidden_constants ++ forbidden_constants_inner)]
    ) init) -> t.skolem_ruleIds_valid rl := by
      intro l
      induction l with
      | nil =>
        intro _ init init_valid t t_mem
        rw [List.foldl_nil] at t_mem
        apply init_valid
        exact t_mem
      | cons hd tl ih =>
        intro subset init init_valid t t_mem
        rw [List.foldl_cons] at t_mem
        apply ih _ _ _ t
        . exact t_mem
        . intro e e_mem; apply subset; simp [e_mem]
        . intro t t_mem
          rw [List.mem_append, List.mem_singleton] at t_mem
          cases t_mem with
          | inl t_mem => apply init_valid; exact t_mem
          | inr t_mem =>
            rw [t_mem]
            apply GroundTerm.rename_constants_apart_preserves_ruleId_validity
            apply valid
            specialize subset List.mem_cons_self
            unfold FunctionFreeConjunction.vars at subset
            rw [List.mem_flatMap] at subset
            rw [List.mem_flatMap]
            rcases subset with ⟨a, a_mem, hd_mem⟩
            exists trg.subs.apply_function_free_atom a
            constructor
            . apply List.mem_map_of_mem; exact a_mem
            . simp only [GroundSubstitution.apply_function_free_atom]
              unfold FunctionFreeAtom.variables at hd_mem
              rw [List.mem_map]
              exists VarOrConst.var hd
              constructor
              . apply VarOrConst.filterVars_occur_in_original_list; exact hd_mem
              . simp [GroundSubstitution.apply_var_or_const]

    apply this trg.rule.body.vars _ []
    . apply List.getElem_mem
    . simp
    . simp

theorem PreTrigger.rename_constants_apart_preserves_disjIdx_validity [GetFreshRepresentant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) :
    ∀ rl, (h : PreTrigger.skolem_ruleIds_valid rl trg) -> PreTrigger.skolem_disjIdx_valid rl trg h -> PreTrigger.skolem_disjIdx_valid rl (PreTrigger.rename_constants_apart trg forbidden_constants) (PreTrigger.rename_constants_apart_preserves_ruleId_validity trg forbidden_constants rl h) := by
  intro rl h valid
  simp only [rename_constants_apart, skolem_ruleIds_valid] at *
  intro t t_mem
  rw [List.mem_flatMap] at t_mem
  rcases t_mem with ⟨f, f_mem, t_mem⟩
  simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj] at f_mem
  rw [List.mem_map] at f_mem
  simp only [GroundSubstitution.apply_function_free_atom] at f_mem
  rcases f_mem with ⟨a, a_mem, f_eq⟩
  rw [← f_eq] at t_mem
  simp only at t_mem
  rw [List.mem_map] at t_mem
  rcases t_mem with ⟨voc, voc_mem, t_eq⟩
  simp only [← t_eq]
  cases voc with
  | const c =>
    simp only [GroundSubstitution.apply_var_or_const]
    apply GroundTerm.skolem_disjIdx_valid_const
  | var v =>
    have : v ∈ trg.rule.body.vars := by
      unfold FunctionFreeConjunction.vars
      rw [List.mem_flatMap]
      exists a
      constructor
      . exact a_mem
      . unfold FunctionFreeAtom.variables
        apply VarOrConst.mem_filterVars_of_var
        exact voc_mem
    simp only [GroundSubstitution.apply_var_or_const, this, ↓reduceDIte]

    have : ∀ (l : List sig.V) (subset : l ⊆ trg.rule.body.vars) (init : List (GroundTerm sig)) (init_h : ∀ t ∈ init, t.skolem_ruleIds_valid rl) (init_valid : ∀ t, (t_mem : t ∈ init) -> t.skolem_disjIdx_valid rl (init_h t t_mem)) (t : GroundTerm sig), (t_h : t.skolem_ruleIds_valid rl) -> t ∈ (l.foldl (fun acc v =>
      let forbidden_constants_inner := acc.flatMap GroundTerm.constants
      acc ++ [(trg.subs v).rename_constants_apart (forbidden_constants ++ forbidden_constants_inner)]
    ) init) -> t.skolem_disjIdx_valid rl t_h := by
      intro l
      induction l with
      | nil =>
        intro _ init init_h init_valid t t_h t_mem
        rw [List.foldl_nil] at t_mem
        apply init_valid
        exact t_mem
      | cons hd tl ih =>
        intro subset init init_h init_valid t t_h t_mem
        rw [List.foldl_cons] at t_mem
        apply ih _ _ _ _ t
        . exact t_mem
        . intro e e_mem; apply subset; simp [e_mem]
        . intro t t_mem
          rw [List.mem_append, List.mem_singleton] at t_mem
          cases t_mem with
          | inl t_mem => apply init_h; exact t_mem
          | inr t_mem =>
            simp only [t_mem]
            apply GroundTerm.rename_constants_apart_preserves_ruleId_validity
            apply h
            specialize subset List.mem_cons_self
            unfold FunctionFreeConjunction.vars at subset
            rw [List.mem_flatMap] at subset
            rw [List.mem_flatMap]
            rcases subset with ⟨a, a_mem, hd_mem⟩
            exists trg.subs.apply_function_free_atom a
            constructor
            . apply List.mem_map_of_mem; exact a_mem
            . simp only [GroundSubstitution.apply_function_free_atom]
              unfold FunctionFreeAtom.variables at hd_mem
              rw [List.mem_map]
              exists VarOrConst.var hd
              constructor
              . apply VarOrConst.filterVars_occur_in_original_list; exact hd_mem
              . simp [GroundSubstitution.apply_var_or_const]
        . intro t t_mem
          rw [List.mem_append, List.mem_singleton] at t_mem
          cases t_mem with
          | inl t_mem => apply init_valid; exact t_mem
          | inr t_mem =>
            simp only [t_mem]
            apply GroundTerm.rename_constants_apart_preserves_disjIdx_validity
            apply valid
            specialize subset List.mem_cons_self
            unfold FunctionFreeConjunction.vars at subset
            rw [List.mem_flatMap] at subset
            rw [List.mem_flatMap]
            rcases subset with ⟨a, a_mem, hd_mem⟩
            exists trg.subs.apply_function_free_atom a
            constructor
            . apply List.mem_map_of_mem; exact a_mem
            . simp only [GroundSubstitution.apply_function_free_atom]
              unfold FunctionFreeAtom.variables at hd_mem
              rw [List.mem_map]
              exists VarOrConst.var hd
              constructor
              . apply VarOrConst.filterVars_occur_in_original_list; exact hd_mem
              . simp [GroundSubstitution.apply_var_or_const]

    apply this trg.rule.body.vars _ []
    . apply List.getElem_mem
    . simp
    . simp
    . simp

theorem PreTrigger.rename_constants_apart_preserves_rule_arity_validity [GetFreshRepresentant sig.C] (trg : PreTrigger sig) (forbidden_constants : List sig.C) :
    ∀ rl, (h : PreTrigger.skolem_ruleIds_valid rl trg) -> PreTrigger.skolem_rule_arity_valid rl trg h -> PreTrigger.skolem_rule_arity_valid rl (PreTrigger.rename_constants_apart trg forbidden_constants) (PreTrigger.rename_constants_apart_preserves_ruleId_validity trg forbidden_constants rl h) := by
  intro rl h valid
  simp only [rename_constants_apart, skolem_ruleIds_valid] at *
  intro t t_mem
  rw [List.mem_flatMap] at t_mem
  rcases t_mem with ⟨f, f_mem, t_mem⟩
  simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj] at f_mem
  rw [List.mem_map] at f_mem
  simp only [GroundSubstitution.apply_function_free_atom] at f_mem
  rcases f_mem with ⟨a, a_mem, f_eq⟩
  rw [← f_eq] at t_mem
  simp only at t_mem
  rw [List.mem_map] at t_mem
  rcases t_mem with ⟨voc, voc_mem, t_eq⟩
  simp only [← t_eq]
  cases voc with
  | const c =>
    simp only [GroundSubstitution.apply_var_or_const]
    apply GroundTerm.skolem_rule_arity_valid_const
  | var v =>
    have : v ∈ trg.rule.body.vars := by
      unfold FunctionFreeConjunction.vars
      rw [List.mem_flatMap]
      exists a
      constructor
      . exact a_mem
      . unfold FunctionFreeAtom.variables
        apply VarOrConst.mem_filterVars_of_var
        exact voc_mem
    simp only [GroundSubstitution.apply_var_or_const, this, ↓reduceDIte]

    have : ∀ (l : List sig.V) (subset : l ⊆ trg.rule.body.vars) (init : List (GroundTerm sig)) (init_h : ∀ t ∈ init, t.skolem_ruleIds_valid rl) (init_valid : ∀ t, (t_mem : t ∈ init) -> t.skolem_rule_arity_valid rl (init_h t t_mem)) (t : GroundTerm sig), (t_h : t.skolem_ruleIds_valid rl) -> t ∈ (l.foldl (fun acc v =>
      let forbidden_constants_inner := acc.flatMap GroundTerm.constants
      acc ++ [(trg.subs v).rename_constants_apart (forbidden_constants ++ forbidden_constants_inner)]
    ) init) -> t.skolem_rule_arity_valid rl t_h := by
      intro l
      induction l with
      | nil =>
        intro _ init init_h init_valid t t_h t_mem
        rw [List.foldl_nil] at t_mem
        apply init_valid
        exact t_mem
      | cons hd tl ih =>
        intro subset init init_h init_valid t t_h t_mem
        rw [List.foldl_cons] at t_mem
        apply ih _ _ _ _ t
        . exact t_mem
        . intro e e_mem; apply subset; simp [e_mem]
        . intro t t_mem
          rw [List.mem_append, List.mem_singleton] at t_mem
          cases t_mem with
          | inl t_mem => apply init_h; exact t_mem
          | inr t_mem =>
            simp only [t_mem]
            apply GroundTerm.rename_constants_apart_preserves_ruleId_validity
            apply h
            specialize subset List.mem_cons_self
            unfold FunctionFreeConjunction.vars at subset
            rw [List.mem_flatMap] at subset
            rw [List.mem_flatMap]
            rcases subset with ⟨a, a_mem, hd_mem⟩
            exists trg.subs.apply_function_free_atom a
            constructor
            . apply List.mem_map_of_mem; exact a_mem
            . simp only [GroundSubstitution.apply_function_free_atom]
              unfold FunctionFreeAtom.variables at hd_mem
              rw [List.mem_map]
              exists VarOrConst.var hd
              constructor
              . apply VarOrConst.filterVars_occur_in_original_list; exact hd_mem
              . simp [GroundSubstitution.apply_var_or_const]
        . intro t t_mem
          rw [List.mem_append, List.mem_singleton] at t_mem
          cases t_mem with
          | inl t_mem => apply init_valid; exact t_mem
          | inr t_mem =>
            simp only [t_mem]
            apply GroundTerm.rename_constants_apart_preserves_rule_arity_validity
            apply valid
            specialize subset List.mem_cons_self
            unfold FunctionFreeConjunction.vars at subset
            rw [List.mem_flatMap] at subset
            rw [List.mem_flatMap]
            rcases subset with ⟨a, a_mem, hd_mem⟩
            exists trg.subs.apply_function_free_atom a
            constructor
            . apply List.mem_map_of_mem; exact a_mem
            . simp only [GroundSubstitution.apply_function_free_atom]
              unfold FunctionFreeAtom.variables at hd_mem
              rw [List.mem_map]
              exists VarOrConst.var hd
              constructor
              . apply VarOrConst.filterVars_occur_in_original_list; exact hd_mem
              . simp [GroundSubstitution.apply_var_or_const]

    apply this trg.rule.body.vars _ []
    . apply List.getElem_mem
    . simp
    . simp
    . simp

