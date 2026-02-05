import ExistentialRules.ChaseSequence.Termination.Basic

/-!
# Parallel Determinized Chase

The backbone of the (D/R)MFA computation is chase-like procedure combines all trigger results (for the different disjuncts) into a single fact set, thereby treating disjunctions as conjunctions. This is what we mean by "determinized". Furthermore, all active triggers are applied at once in a single step. This is what we mean by "parallel". The `parallelDeterminizedChase` will later be passed the `MfaObsoletenessCondition`s to define all the versions MFA/DMFA/RMFA. However, the definitions work with any `LaxObsoletenessCondition`. As for `ChaseBranch` and `ChaseDerivation`, the `parallelDeterminizedChase` is a more strict version of the `parallelDeterminizedDerivation` where the former forces the first fact set to be a `Database` (as part of a `KnowledgeBase`), while the latter accepts any `FactSet`.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-!
## parallelDeterminizedDerivation

We start with the more general definition, allowing to start from arbitrary `FactSet`s.
-/

/-- One step of the `parallelDeterminizedDerivation` adds the results of all active triggers to the previous fact set. The results for all disjuncts are combined in the procees. Activeness of the triggers is with respect to a given `LaxObsoletenessCondition`. -/
def parallelDeterminizedDerivation_step (rs : RuleSet sig) (obs : LaxObsoletenessCondition sig) (fs : FactSet sig) : FactSet sig :=
  fs ∪ fun f =>
    (∃ (trg : RTrigger obs rs),
      trg.val.active fs ∧
      ∃ (i : Fin trg.val.mapped_head.length), f ∈ trg.val.mapped_head[i.val])

/-- The `parallelDeterminizedDerivation` simply iterates the `parallelDeterminizedDerivation_step` on an initial `FactSet` using the `InfiniteList.iterate` function. -/
def parallelDeterminizedDerivation (rs : RuleSet sig) (obs : LaxObsoletenessCondition sig) (fs : FactSet sig) : InfiniteList (FactSet sig) :=
  InfiniteList.iterate fs (parallelDeterminizedDerivation_step rs obs)

/-- The `parallelDeterminizedDerivation_result` is the union of all `FactSet`s in the derivation. -/
def parallelDeterminizedDerivation_result (rs : RuleSet sig) (obs : LaxObsoletenessCondition sig) (start : FactSet sig) : FactSet sig := fun f => ∃ fs ∈ (parallelDeterminizedDerivation rs obs start), f ∈ fs

section ParallelDeterminizedDerivation

variable {rs : RuleSet sig} {obs : LaxObsoletenessCondition sig} {start : FactSet sig}

/-- The `parallelDeterminizedDerivation_head` is the starting `FactSet`. -/
theorem parallelDeterminizedDerivation_head : (parallelDeterminizedDerivation rs obs start).head = start := by rfl

/-- The head of the tail (i.e. the next element) results from performing one `parallelDeterminizedDerivation_step` on the starting `FactSet`. -/
theorem parallelDeterminizedDerivation_head_tail : (parallelDeterminizedDerivation rs obs start).tail.head = (parallelDeterminizedDerivation_step rs obs start) := by rfl

/-- Performing a `parallelDeterminizedDerivation_step` on a member again yields a member. -/
theorem parallelDeterminizedDerivation_step_mem_of_mem : ∀ fs ∈ (parallelDeterminizedDerivation rs obs start), (parallelDeterminizedDerivation_step rs obs fs) ∈ (parallelDeterminizedDerivation rs obs start) := by rintro _ ⟨n, mem⟩; exists n.succ; unfold parallelDeterminizedDerivation; rw [InfiniteList.get_succ_iterate, ← mem]; rfl

/-- Each suffix of a `parallelDeterminizedDerivation` is equal to the `parallelDeterminizedDerivation` that starts on the first element of the suffix. -/
theorem parallelDeterminizedDerivation_suffix :
    ∀ l2, l2 <:+ (parallelDeterminizedDerivation rs obs start) ->
    l2 = (parallelDeterminizedDerivation rs obs l2.head) := by
  rintro l2 ⟨n, suf⟩
  rw [← suf, InfiniteList.head_drop]
  apply InfiniteList.ext
  simp only [parallelDeterminizedDerivation]
  intro m
  rw [InfiniteList.get_drop, InfiniteList.get_add_iterate]

/-- This recursor allows proving properties of elements (i.e. `FactSet`s with a membership proof) in a `parallelDeterminizedDerivation` and can be used with the induction tactic. -/
theorem parallelDeterminizedDerivation_mem_rec
    {motive : (parallelDeterminizedDerivation rs obs start).Element -> Prop}
    (head : motive ⟨(parallelDeterminizedDerivation rs obs start).head, (parallelDeterminizedDerivation rs obs start).head_mem⟩)
    (step : ∀ elem, motive elem -> motive ⟨(parallelDeterminizedDerivation_step rs obs elem.val), parallelDeterminizedDerivation_step_mem_of_mem _ elem.property⟩)
    (a : (parallelDeterminizedDerivation rs obs start).Element) :
    motive a := by
  induction a using InfiniteList.mem_rec with
  | head => exact head
  | step l2 suf ih =>
    specialize step _ ih
    conv => right; left; rw [parallelDeterminizedDerivation_suffix _ suf, parallelDeterminizedDerivation_head_tail]
    exact step

/-- The starting fact set is a subset of each derivation member, -/
theorem parallelDeterminizedDerivation_facts_node_subset_every_mem : ∀ fs ∈ (parallelDeterminizedDerivation rs obs start), (parallelDeterminizedDerivation rs obs start).head ⊆ fs := by
  intro fs fs_mem
  let elem : (parallelDeterminizedDerivation rs obs start).Element := ⟨fs, fs_mem⟩
  show (parallelDeterminizedDerivation rs obs start).head ⊆ elem.val
  induction elem using parallelDeterminizedDerivation_mem_rec with
  | head => exact Set.subset_refl
  | step _ ih =>
    apply Set.subset_trans ih
    apply Set.subset_union_of_subset_left
    exact Set.subset_refl

/-- Each two `FactSet`s in a derivation must subsumes each other in (at least) one of two possible directions. -/
theorem parallelDeterminizedDerivation_subset_total : ∀ fs1 fs2, (fs1 ∈ (parallelDeterminizedDerivation rs obs start)) -> (fs2 ∈ (parallelDeterminizedDerivation rs obs start)) -> fs1 ⊆ fs2 ∨ fs2 ⊆ fs1 := by
  rintro fs1 fs2 ⟨n1, fs1_mem⟩ ⟨n2, fs2_mem⟩
  cases Nat.le_total n1 n2 with
  | inl le =>
    rcases Nat.exists_eq_add_of_le le with ⟨k, le⟩
    apply Or.inl
    have : (parallelDeterminizedDerivation rs obs fs1).head = fs1 := parallelDeterminizedDerivation_head
    rw [← this]
    apply parallelDeterminizedDerivation_facts_node_subset_every_mem
    exists k
    rw [← fs2_mem, le, ← fs1_mem]
    simp only [parallelDeterminizedDerivation, InfiniteList.get_add_iterate]
  | inr le =>
    rcases Nat.exists_eq_add_of_le le with ⟨k, le⟩
    apply Or.inr
    have : (parallelDeterminizedDerivation rs obs fs2).head = fs2 := parallelDeterminizedDerivation_head
    rw [← this]
    apply parallelDeterminizedDerivation_facts_node_subset_every_mem
    exists k
    rw [← fs1_mem, le, ← fs2_mem]
    simp only [parallelDeterminizedDerivation, InfiniteList.get_add_iterate]

/-- All predicates that occur in the derivation come from the rules or the starting fact set. -/
theorem parallelDeterminizedDerivation_predicates :
    ∀ fs ∈ (parallelDeterminizedDerivation rs obs start), fs.predicates ⊆ (rs.predicates ∪ start.predicates) := by
  intro fs fs_mem
  let elem : (parallelDeterminizedDerivation rs obs start).Element := ⟨fs, fs_mem⟩
  show elem.val.predicates ⊆ (rs.predicates ∪ start.predicates)
  induction elem using parallelDeterminizedDerivation_mem_rec with
  | head => apply Set.subset_union_of_subset_right; exact Set.subset_refl
  | step _ ih =>
    rintro p ⟨f, f_mem, p_mem⟩; cases f_mem with
    | inl f_mem => apply ih; exists f
    | inr f_mem =>
      rcases f_mem with ⟨trg, trg_act, f_mem⟩
      unfold PreTrigger.mapped_head at f_mem
      rcases f_mem with ⟨i, f_mem⟩
      rw [List.getElem_map, List.mem_map] at f_mem
      rcases f_mem with ⟨a, a_mem, f_mem⟩
      rw [List.get_eq_getElem, List.getElem_zipIdx] at a_mem
      apply Or.inl
      exists trg.val.rule
      constructor
      . exact trg.property
      . unfold Rule.predicates
        rw [List.mem_append]
        apply Or.inr
        rw [List.mem_flatMap]
        exists trg.val.rule.head[i]
        constructor
        . simp
        . unfold FunctionFreeConjunction.predicates
          rw [List.mem_map]
          exists a
          constructor
          . exact a_mem
          . rw [← p_mem, ← f_mem]
            rfl

/-- All constants that occur in the derivation come from the rule heads or the starting fact set. -/
theorem parallelDeterminizedDerivation_constants :
    ∀ fs ∈ (parallelDeterminizedDerivation rs obs start), fs.constants ⊆ (rs.head_constants ∪ start.constants) := by
  intro fs fs_mem
  let elem : (parallelDeterminizedDerivation rs obs start).Element := ⟨fs, fs_mem⟩
  show elem.val.constants ⊆ (rs.head_constants ∪ start.constants)
  induction elem using parallelDeterminizedDerivation_mem_rec with
  | head => apply Set.subset_union_of_subset_right; exact Set.subset_refl
  | step _ ih =>
    unfold parallelDeterminizedDerivation_step
    rw [FactSet.constants_union]
    rintro c c_mem; cases c_mem with
    | inl c_mem => apply ih; exact c_mem
    | inr c_mem =>
      rcases c_mem with ⟨f, ⟨trg, trg_act, ⟨i, f_mem⟩⟩, c_mem⟩
      have c_mem : c ∈ FactSet.constants (trg.val.mapped_head[i.val]).toSet := by unfold FactSet.constants; exists f
      apply Set.subset_trans (trg.val.mapped_head_constants_subset i)
      . intro c c_mem
        rw [List.mem_toSet, List.mem_append] at c_mem
        cases c_mem with
        | inl c_mem =>
          apply ih
          rw [List.mem_flatMap] at c_mem
          rcases c_mem with ⟨t, t_mem, c_mem⟩
          rw [List.mem_map] at t_mem
          rcases t_mem with ⟨v, v_mem, t_mem⟩
          rcases FunctionFreeConjunction.mem_vars.mp (trg.val.rule.frontier_subset_vars_body v_mem) with ⟨a, a_mem, v_mem'⟩
          exists trg.val.subs.apply_function_free_atom a
          constructor
          . apply trg_act.left
            rw [List.mem_toSet]
            unfold PreTrigger.mapped_body
            unfold GroundSubstitution.apply_function_free_conj
            apply List.mem_map_of_mem
            exact a_mem
          . unfold Fact.constants
            rw [List.mem_flatMap]
            exists t
            constructor
            . unfold GroundSubstitution.apply_function_free_atom
              unfold TermMapping.apply_generalized_atom
              rw [List.mem_map]
              exists VarOrConst.var v
              constructor
              . exact v_mem'
              . unfold PreTrigger.subs_for_mapped_head at t_mem
                rw [PreTrigger.apply_to_var_or_const_frontier_var] at t_mem
                . exact t_mem
                . exact v_mem
            . exact c_mem
        | inr c_mem =>
          apply Or.inl
          exists trg.val.rule
          constructor
          . exact trg.property
          . unfold Rule.head_constants
            rw [List.mem_flatMap]
            exists trg.val.rule.head[i.val]'(by rw [← PreTrigger.length_mapped_head]; exact i.isLt)
            constructor
            . apply List.get_mem
            . exact c_mem
      . exact c_mem

/-- All function symbols that occur in the derivation come from the rule set's skolem functions or the starting fact set. -/
theorem parallelDeterminizedDerivation_functions :
    ∀ fs ∈ (parallelDeterminizedDerivation rs obs start), fs.function_symbols ⊆ (rs.skolem_functions ∪ start.function_symbols) := by
  intro fs fs_mem
  let elem : (parallelDeterminizedDerivation rs obs start).Element := ⟨fs, fs_mem⟩
  show elem.val.function_symbols ⊆ (rs.skolem_functions ∪ start.function_symbols)
  induction elem using parallelDeterminizedDerivation_mem_rec with
  | head =>
    intro func func_mem
    unfold FactSet.function_symbols at func_mem
    rcases func_mem with ⟨f, f_mem, func_mem⟩
    apply Or.inr
    exists f
  | step _ ih =>
    intro func func_mem
    rcases func_mem with ⟨f, f_mem, func_mem⟩
    cases f_mem with
    | inl f_mem => apply ih; exists f
    | inr f_mem =>
      rcases f_mem with ⟨trg, trg_act, ⟨i, f_mem⟩⟩
      unfold Fact.function_symbols at func_mem
      rw [List.mem_flatMap] at func_mem
      rcases func_mem with ⟨t, t_mem, func_mem⟩

      have t_mem : t ∈ trg.val.mapped_head[i.val].flatMap GeneralizedAtom.terms := by rw [List.mem_flatMap]; exists f
      rw [PreTrigger.mem_terms_mapped_head_iff] at t_mem
      cases t_mem with
      | inl t_mem =>
        rcases t_mem with ⟨_, _, t_mem⟩
        rw [← t_mem] at func_mem
        simp [GroundTerm.functions_const] at func_mem
      | inr t_mem =>
      cases t_mem with
      | inl t_mem =>
        apply ih
        rw [List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
        simp only [Rule.frontier_for_head, List.mem_filter] at v_mem
        rcases FunctionFreeConjunction.mem_vars.mp v_mem.left with ⟨body_atom, body_atom_mem, v_mem⟩
        exists (trg.val.subs.apply_function_free_atom body_atom)
        constructor
        . apply trg_act.left
          rw [List.mem_toSet]
          simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
          rw [List.mem_map]
          exists body_atom
        . unfold Fact.function_symbols
          rw [List.mem_flatMap]
          exists t
          constructor
          . unfold GroundSubstitution.apply_function_free_atom
            unfold TermMapping.apply_generalized_atom
            rw [List.mem_map]
            exists VarOrConst.var v
          . exact func_mem
      | inr t_mem =>
        rcases PreTrigger.mem_fresh_terms _ t_mem with ⟨v, v_mem, t_mem⟩
        rw [t_mem, GroundTerm.functions_func, List.mem_cons] at func_mem
        cases func_mem with
        | inl func_mem =>
          apply Or.inl
          exists trg.val.rule; constructor
          . exact trg.property
          . unfold Rule.skolem_functions
            rw [List.mem_flatMap]
            exists (trg.val.rule.head[i.val]'(by rw [← PreTrigger.length_mapped_head]; exact i.isLt), i)
            constructor
            . rw [List.mem_zipIdx_iff_getElem?]
              simp
            . rw [func_mem]
              apply List.mem_map_of_mem
              exact v_mem
        | inr func_mem =>
          apply ih
          simp only [List.mem_flatMap, List.mem_map] at func_mem; rcases func_mem with ⟨t, ⟨v, v_mem, t_mem⟩, func_mem⟩
          rcases FunctionFreeConjunction.mem_vars.mp (Rule.frontier_subset_vars_body v_mem) with ⟨body_atom, body_atom_mem, frontier_var_mem⟩
          exists (trg.val.subs.apply_function_free_atom body_atom)
          constructor
          . apply trg_act.left
            rw [List.mem_toSet]
            simp only [PreTrigger.mapped_body, GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
            rw [List.mem_map]
            exists body_atom
          . unfold Fact.function_symbols
            rw [List.mem_flatMap]
            exists (trg.val.subs v)
            constructor
            . unfold GroundSubstitution.apply_function_free_atom
              unfold TermMapping.apply_generalized_atom
              rw [List.mem_map]
              exists VarOrConst.var v
            . rw [← t_mem] at func_mem
              exact func_mem

/-- All predicates in the derivation result come from the rules or the starting fact set. -/
theorem parallelDeterminizedDerivation_result_predicates :
    (parallelDeterminizedDerivation_result rs obs start).predicates ⊆ (rs.predicates ∪ start.predicates) := by
  rintro p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  apply parallelDeterminizedDerivation_predicates _ fs_mem
  exists f

/-- All constants in the derivation result come from the rule heads or the starting fact set. -/
theorem parallelDeterminizedDerivation_result_constants :
    (parallelDeterminizedDerivation_result rs obs start).constants ⊆ (rs.head_constants ∪ start.constants) := by
  rintro p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  apply parallelDeterminizedDerivation_constants _ fs_mem
  exists f

/-- All function symbols in the derivation result come from the rule set's skolem functions or the starting fact set. -/
theorem parallelDeterminizedDerivation_result_functions :
    (parallelDeterminizedDerivation_result rs obs start).function_symbols ⊆
    (rs.skolem_functions ∪ start.function_symbols) := by
  rintro p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  apply parallelDeterminizedDerivation_functions _ fs_mem
  exists f

end ParallelDeterminizedDerivation

/-!
## parallelDeterminizedChase

A `parallelDeterminizedChase` fixes a `KnowledgeBase` and start a `parallelDeterminizedDerivation` on the knowledge base's database.
Some of the above theorems thereby can be refined. For example, function symbols can now only be skolem functions as the database only has constants as terms.
-/

/-- A `parallelDeterminizedChase` is a special `parallelDeterminizedDerivation` starting on a database from a `KnowledgeBase`. -/
def parallelDeterminizedChase (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) : InfiniteList (FactSet sig) := parallelDeterminizedDerivation kb.rules obs kb.db.toFactSet.val

/-- The `parallelDeterminizedChase_result` is simply the result of the underlying derivation. -/
def parallelDeterminizedChase_result (kb : KnowledgeBase sig) (obs : LaxObsoletenessCondition sig) : FactSet sig := parallelDeterminizedDerivation_result kb.rules obs kb.db.toFactSet.val

section ParallelDeterminizedChase

variable {kb : KnowledgeBase sig} {obs : LaxObsoletenessCondition sig}

/-- All constants in the chase come from the rule heads or the database. -/
theorem parallelDeterminizedChase_constants :
    ∀ fs ∈ (parallelDeterminizedChase kb obs), fs.constants ⊆ (kb.rules.head_constants ∪ kb.db.constants) := by
  intro _ fs_mem
  rw [← Database.toFactSet_constants_same]
  apply parallelDeterminizedDerivation_constants
  exact fs_mem

/-- All function symbols in the chase come from the rule set's skolem functions. -/
theorem parallelDeterminizedChase_functions :
    ∀ fs ∈ (parallelDeterminizedChase kb obs), fs.function_symbols ⊆ kb.rules.skolem_functions := by
  intro _ fs_mem _ func_mem
  cases parallelDeterminizedDerivation_functions _ fs_mem _ func_mem with
  | inl func_mem => exact func_mem
  | inr func_mem =>
    unfold FactSet.function_symbols at func_mem
    rcases func_mem with ⟨f, f_mem, func_mem⟩
    unfold Fact.function_symbols at func_mem
    rw [List.mem_flatMap] at func_mem
    rcases func_mem with ⟨t, t_mem, func_mem⟩
    cases eq : t with
    | const c => simp [eq, GroundTerm.functions_const] at func_mem
    | func _ _ =>
      have func_free := kb.db.toFactSet.property.right
      specialize func_free f f_mem t t_mem
      rcases func_free with ⟨c, t_eq⟩
      rw [t_eq] at eq
      simp [GroundTerm.const, GroundTerm.func] at eq

/-- All constants in the chase result come from the rule heads or the database. -/
theorem parallelDeterminizedChase_result_constants :
    (parallelDeterminizedChase_result kb obs).constants ⊆ (kb.rules.head_constants ∪ kb.db.constants) := by
  rintro p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  rw [← parallelDeterminizedChase.eq_def] at fs_mem
  apply parallelDeterminizedChase_constants _ fs_mem
  exists f

/-- All function symbols in the chase result come from the rule set's skolem functions. -/
theorem parallelDeterminizedChase_result_functions :
    (parallelDeterminizedChase_result kb obs).function_symbols ⊆ kb.rules.skolem_functions := by
  rintro p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  rw [← parallelDeterminizedChase.eq_def] at fs_mem
  apply parallelDeterminizedChase_functions _ fs_mem
  exists f

end ParallelDeterminizedChase

