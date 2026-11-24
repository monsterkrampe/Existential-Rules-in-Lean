/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.HeadChoice

open CustomBasicDatastructures

/-!
# Parallel Determinized Chase

This is a very generic definition of an always infinite chase-like procedure.
In each step, we take all active trigger at once (in "parallel"). Activeness is dictated by a `LaxObsolescenceCondition`.
Then for each of these triggers, we either take its result according to some head choice or, if no head choice is provided, we take the union of the results of all head disjuncts, thereby treating disjunctions as conjunctions. This is what we mean by "determinized".
As for `ChaseBranch` and `ChaseDerivation`, the `parallelDeterminizedChase` is a more strict version of the `parallelDeterminizedDerivation` where the former forces the first fact set to be a `Database` (as part of a `KnowledgeBase`), while the latter accepts any `FactSet`.

This procedure builds the backbone of the (D/R)MFA computation. The `parallelDeterminizedChase` will later be passed the `MfaObsolescenceCondition`s to define all the versions MFA/DMFA/RMFA. The head choice is always "none" in these cases.

At the same time, we want to use the procedure also for the definition of RPC-like conditions, where a head choice needs to be involved.
Furthermore, we may also use the procedure for unblockability checks (related to RPC) but this requires further generalization by adding the possibility to map the remap the terms in trigger results. This is now also added. In all other cases, we simply pass the id mapping.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-!
## parallelDeterminizedDerivation

We start with the more general definition, allowing to start from arbitrary `FactSet`s.
-/

/-- One step of the `parallelDeterminizedDerivation` adds the results of all active triggers to the previous fact set. The results for all disjuncts are combined in the procees. Activeness of the triggers is with respect to a given `LaxObsolescenceCondition`. -/
@[expose]
def parallelDeterminizedDerivation_step
    (rs : RuleSet sig) (obs : LaxObsolescenceCondition sig) (hc_opt : Option (HeadChoice sig)) (remapping : GroundTermMapping sig) (fs : FactSet sig) :
    FactSet sig :=
  fs ∪ remapping.applyFactSet (fun f =>
    (∃ (trg : RTrigger obs rs),
      trg.val.active fs ∧
      -- This is basically an if condition. If there is a HeadChoice given, we need to behave accordingly.
      (∀ hc ∈ hc_opt, f ∈ trg.val.mapped_head[(hc trg.val).val]) ∧
      -- If none is given, we act is all disjunctions where conjunctions, i.e. f is allowed to occur in any disjunct.
      (hc_opt = none -> ∃ (i : Nat) (lt : i < trg.val.rule.head.length), f ∈ trg.val.mapped_head[i]'(by grind))))

/-- Often, when we know that a fact is in a parallelDeterminizedDerivation_step, we only care that it occurs in some disjunct of a trigger result, not about that this index coincides with the head choice. This theorem expresses exactly this simplification. -/
theorem parallelDeterminizedDerivation_step_subset
    {rs : RuleSet sig} {obs : LaxObsolescenceCondition sig} {hc_opt : Option (HeadChoice sig)} {remapping : GroundTermMapping sig} {fs : FactSet sig} :
    parallelDeterminizedDerivation_step rs obs hc_opt remapping fs ⊆ fs ∪ remapping.applyFactSet (fun f => ∃ (trg : RTrigger obs rs), trg.val.active fs ∧ ∃ (i : Nat) (lt : i < trg.val.rule.head.length), f ∈ trg.val.mapped_head[i]'(by grind)) := by
  intro f f_mem
  cases f_mem with
  | inl f_mem => exact Or.inl f_mem
  | inr f_mem =>
    apply Or.inr
    rcases TermMapping.mem_apply_generalized_atom_set.mp f_mem with ⟨f', ⟨trg, active, with_hc, without_hc⟩, f_mem⟩
    apply TermMapping.mem_apply_generalized_atom_set.mpr; exists f'; simp only [f_mem, and_true]
    cases hc_opt with
    | none => exists trg; exact ⟨active, without_hc rfl⟩
    | some hc => exists trg, active, (hc trg.val).val, (hc trg.val).isLt; apply with_hc; simp

/-- When the head choice is none, we can rewrite the `parallelDeterminizedDerivation_step` definition as follows. -/
theorem parallelDeterminizedDerivation_step_hc_none
    {rs : RuleSet sig} {obs : LaxObsolescenceCondition sig} {remapping : GroundTermMapping sig} {fs : FactSet sig} :
    parallelDeterminizedDerivation_step rs obs none remapping fs = fs ∪ remapping.applyFactSet (fun f => ∃ (trg : RTrigger obs rs), trg.val.active fs ∧ ∃ (i : Nat) (lt : i < trg.val.rule.head.length), f ∈ trg.val.mapped_head[i]'(by grind)) := by
  simp [parallelDeterminizedDerivation_step]

/-- When a head choice is present, we can rewrite the `parallelDeterminizedDerivation_step` definition as follows. -/
theorem parallelDeterminizedDerivation_step_hc_some
    {rs : RuleSet sig} {obs : LaxObsolescenceCondition sig} {hc : HeadChoice sig} {remapping : GroundTermMapping sig} {fs : FactSet sig} :
    parallelDeterminizedDerivation_step rs obs (some hc) remapping fs = fs ∪ remapping.applyFactSet (fun f => ∃ (trg : RTrigger obs rs), trg.val.active fs ∧ f ∈ trg.val.mapped_head[(hc trg.val).val]) := by
  simp [parallelDeterminizedDerivation_step]

/-- The `parallelDeterminizedDerivation` simply iterates the `parallelDeterminizedDerivation_step` on an initial `FactSet` using the `InfiniteList.iterate` function. -/
def parallelDeterminizedDerivation
    (rs : RuleSet sig) (obs : LaxObsolescenceCondition sig) (hc_opt : Option (HeadChoice sig)) (remapping : GroundTermMapping sig) (fs : FactSet sig) :
    InfiniteList (FactSet sig) :=
  InfiniteList.iterate fs (parallelDeterminizedDerivation_step rs obs hc_opt remapping)

/-- The `parallelDeterminizedDerivation_result` is the union of all `FactSet`s in the derivation. -/
@[expose]
def parallelDeterminizedDerivation_result
    (rs : RuleSet sig) (obs : LaxObsolescenceCondition sig) (hc_opt : Option (HeadChoice sig)) (remapping : GroundTermMapping sig)
    (start : FactSet sig) : FactSet sig :=
  fun f => ∃ fs ∈ (parallelDeterminizedDerivation rs obs hc_opt remapping start), f ∈ fs

section ParallelDeterminizedDerivation

variable {rs : RuleSet sig} {obs : LaxObsolescenceCondition sig} {hc_opt : Option (HeadChoice sig)} {remapping : GroundTermMapping sig} {start : FactSet sig}

/-- The `parallelDeterminizedDerivation_head` is the starting `FactSet`. -/
@[simp, grind =]
theorem parallelDeterminizedDerivation_head : (parallelDeterminizedDerivation rs obs hc_opt remapping start).head = start := by
  unfold parallelDeterminizedDerivation; simp

/-- The head of the tail (i.e. the next element) results from performing one `parallelDeterminizedDerivation_step` on the starting `FactSet`. -/
@[simp, grind =]
theorem parallelDeterminizedDerivation_head_tail :
    (parallelDeterminizedDerivation rs obs hc_opt remapping start).tail.head = (parallelDeterminizedDerivation_step rs obs hc_opt remapping start) := by
  unfold parallelDeterminizedDerivation
  rw [InfiniteList.head_eq, InfiniteList.get_tail, InfiniteList.get_succ_iterate, Function.repeat_zero]

/-- Performing a `parallelDeterminizedDerivation_step` on a member again yields a member. -/
@[grind <-]
theorem parallelDeterminizedDerivation_step_mem_of_mem :
    ∀ fs ∈ (parallelDeterminizedDerivation rs obs hc_opt remapping start),
    (parallelDeterminizedDerivation_step rs obs hc_opt remapping fs) ∈ (parallelDeterminizedDerivation rs obs hc_opt remapping start) := by
  intro _ ⟨n, mem⟩; exists n.succ
  unfold parallelDeterminizedDerivation; rw [InfiniteList.get_succ_iterate, ← mem]
  unfold parallelDeterminizedDerivation; rw [InfiniteList.get_iterate]

/-- Each suffix of a `parallelDeterminizedDerivation` is equal to the `parallelDeterminizedDerivation` that starts on the first element of the suffix. -/
theorem parallelDeterminizedDerivation_suffix :
    ∀ l2, l2 <:+ (parallelDeterminizedDerivation rs obs hc_opt remapping start) ->
    l2 = (parallelDeterminizedDerivation rs obs hc_opt remapping l2.head) := by
  intro l2
  rw [InfiniteList.IsSuffix_iff]
  intro ⟨n, suf⟩
  rw [← suf, InfiniteList.head_drop]
  apply InfiniteList.ext
  simp only [parallelDeterminizedDerivation]
  intro m
  rw [InfiniteList.get_drop, InfiniteList.get_add_iterate]

/-- This recursor allows proving properties of elements (i.e. `FactSet`s with a membership proof) in a `parallelDeterminizedDerivation` and can be used with the induction tactic. -/
theorem parallelDeterminizedDerivation_mem_rec
    {motive : (parallelDeterminizedDerivation rs obs hc_opt remapping start).Element -> Prop}
    (head : motive ⟨(parallelDeterminizedDerivation rs obs hc_opt remapping start).head,
      (parallelDeterminizedDerivation rs obs hc_opt remapping start).head_mem⟩)
    (step : ∀ elem, motive elem ->
      motive ⟨(parallelDeterminizedDerivation_step rs obs hc_opt remapping elem.val), parallelDeterminizedDerivation_step_mem_of_mem _ elem.property⟩)
    (a : (parallelDeterminizedDerivation rs obs hc_opt remapping start).Element) :
    motive a := by
  induction a using InfiniteList.mem_rec with
  | head => exact head
  | step l2 suf ih =>
    specialize step _ ih
    conv => right; left; rw [parallelDeterminizedDerivation_suffix _ suf, parallelDeterminizedDerivation_head_tail]
    exact step

/-- The starting fact set is a subset of each derivation member, -/
@[grind <-]
theorem parallelDeterminizedDerivation_facts_node_subset_every_mem :
    ∀ fs ∈ (parallelDeterminizedDerivation rs obs hc_opt remapping start), (parallelDeterminizedDerivation rs obs hc_opt remapping start).head ⊆ fs := by
  intro fs fs_mem
  let elem : (parallelDeterminizedDerivation rs obs hc_opt remapping start).Element := ⟨fs, fs_mem⟩
  show (parallelDeterminizedDerivation rs obs hc_opt remapping start).head ⊆ elem.val
  induction elem using parallelDeterminizedDerivation_mem_rec with
  | head => exact Set.subset_refl
  | step _ ih =>
    apply Set.subset_trans ih
    apply Set.subset_union_of_subset_left
    exact Set.subset_refl

/-- Each two `FactSet`s in a derivation must subsumes each other in (at least) one of two possible directions. -/
theorem parallelDeterminizedDerivation_subset_total :
    ∀ fs1 fs2, (fs1 ∈ (parallelDeterminizedDerivation rs obs hc_opt remapping start)) ->
    (fs2 ∈ (parallelDeterminizedDerivation rs obs hc_opt remapping start)) ->
    fs1 ⊆ fs2 ∨ fs2 ⊆ fs1 := by
  rintro fs1 fs2 ⟨n1, fs1_mem⟩ ⟨n2, fs2_mem⟩
  cases Nat.le_total n1 n2 with
  | inl le =>
    rcases Nat.exists_eq_add_of_le le with ⟨k, le⟩
    apply Or.inl
    have : (parallelDeterminizedDerivation rs obs hc_opt remapping fs1).head = fs1 := parallelDeterminizedDerivation_head
    rw [← this]
    apply parallelDeterminizedDerivation_facts_node_subset_every_mem
    exists k
    rw [← fs2_mem, le, ← fs1_mem]
    simp only [parallelDeterminizedDerivation, InfiniteList.get_add_iterate]
  | inr le =>
    rcases Nat.exists_eq_add_of_le le with ⟨k, le⟩
    apply Or.inr
    have : (parallelDeterminizedDerivation rs obs hc_opt remapping fs2).head = fs2 := parallelDeterminizedDerivation_head
    rw [← this]
    apply parallelDeterminizedDerivation_facts_node_subset_every_mem
    exists k
    rw [← fs1_mem, le, ← fs2_mem]
    simp only [parallelDeterminizedDerivation, InfiniteList.get_add_iterate]

/-- All predicates that occur in the derivation come from the rules or the starting fact set. -/
theorem parallelDeterminizedDerivation_predicates :
    ∀ fs ∈ (parallelDeterminizedDerivation rs obs hc_opt remapping start), fs.predicates ⊆ (rs.predicates ∪ start.predicates) := by
  intro fs fs_mem
  let elem : (parallelDeterminizedDerivation rs obs hc_opt remapping start).Element := ⟨fs, fs_mem⟩
  show elem.val.predicates ⊆ (rs.predicates ∪ start.predicates)
  induction elem using parallelDeterminizedDerivation_mem_rec with
  | head => apply Set.subset_union_of_subset_right; simpa using Set.subset_refl
  | step _ ih =>
    rintro p ⟨f, f_mem, p_mem⟩; cases parallelDeterminizedDerivation_step_subset _ f_mem with
    | inl f_mem => apply ih; exists f
    | inr f_mem =>
      rcases TermMapping.mem_apply_generalized_atom_set.mp f_mem with ⟨f', ⟨trg, trg_act, f_mem⟩, f_eq⟩
      unfold PreTrigger.mapped_head at f_mem
      rcases f_mem with ⟨i, lt, f_mem⟩
      rw [List.getElem_map, List.getElem_attach, List.mem_map] at f_mem
      rcases f_mem with ⟨a, a_mem, f_mem⟩
      simp only [List.getElem_zipIdx] at a_mem
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
          . rw [← p_mem, f_eq, ← f_mem]; rfl

/-- All constants that occur in the derivation come from the rule heads or the starting fact set or the fresh constants introduced by the remapping.
While this is a quite general claim, the assump on the remapping is quite strong. However, I think for our use cases, this should be fine. -/
theorem parallelDeterminizedDerivation_constants :
    ∀ (freshConsts : Set sig.C), (∀ t, remapping t ≠ t -> ∃ c ∈ freshConsts, remapping t = .const c) ->
    ∀ fs ∈ (parallelDeterminizedDerivation rs obs hc_opt remapping start), fs.constants ⊆ (rs.head_constants ∪ start.constants ∪ freshConsts) := by
  intro freshConsts non_id_is_fresh fs fs_mem
  let elem : (parallelDeterminizedDerivation rs obs hc_opt remapping start).Element := ⟨fs, fs_mem⟩
  show elem.val.constants ⊆ (rs.head_constants ∪ start.constants ∪ freshConsts)
  induction elem using parallelDeterminizedDerivation_mem_rec with
  | head => apply Set.subset_union_of_subset_left; apply Set.subset_union_of_subset_right; simpa using Set.subset_refl
  | step _ ih =>
    apply Set.subset_trans (FactSet.constants_subset_of_subset parallelDeterminizedDerivation_step_subset)
    rw [FactSet.constants_union]
    rintro c c_mem; cases c_mem with
    | inl c_mem => apply ih; exact c_mem
    | inr c_mem =>
      rcases FactSet.mem_constants_iff_mem_terms.mp c_mem with ⟨t, t_mem, c_mem⟩
      rw [GroundTermMapping.terms_applyFactSet, Set.mem_map] at t_mem
      rcases t_mem with ⟨s, ⟨f, ⟨trg, trg_act, ⟨i, lt, f_mem⟩⟩, s_mem⟩, t_mem⟩
      cases Decidable.em (s = t) with
      | inl s_eq_t =>
        have c_mem : c ∈ FactSet.constants (trg.val.mapped_head[i]'(by grind)).toSet := by
          simp only [FactSet.mem_constants_iff_mem_terms, FactSet.mem_terms_toSet]; exists t; constructor; rw [← s_eq_t]; exact List.mem_flatMap_of_mem f_mem s_mem; exact c_mem
        apply Set.subset_trans (trg.val.mapped_head_constants_subset i lt)
        . intro c c_mem
          rw [List.mem_toSet, List.mem_append] at c_mem
          cases c_mem with
          | inl c_mem =>
            apply ih
            rw [List.mem_flatMap] at c_mem
            rcases c_mem with ⟨t, t_mem, c_mem⟩
            apply FactSet.constants_subset_of_subset trg_act.left
            rw [FactSet.mem_constants_iff_mem_terms]; exists t; constructor
            . rw [FactSet.mem_terms_toSet]; apply PreTrigger.mem_terms_mapped_body_of_mem_mapped_frontier; exact t_mem
            . exact c_mem
          | inr c_mem =>
            apply Or.inl; apply Or.inl
            exists trg.val.rule
            constructor
            . exact trg.property
            . unfold Rule.head_constants
              rw [List.mem_flatMap]
              exists trg.val.rule.head[i]
              constructor
              . apply List.get_mem
              . exact c_mem
        . exact c_mem
      | inr s_ne_t =>
        apply Or.inr
        rcases non_id_is_fresh s (by intro contra; apply s_ne_t; rw [← t_mem, contra]) with ⟨d, d_mem, d_eq⟩
        rw [← t_mem, d_eq, GroundTerm.constants_const, List.mem_singleton] at c_mem
        rw [c_mem]; exact d_mem

/-- A special case of the above theorem with the id remapping. -/
theorem parallelDeterminizedDerivation_constants_with_id_remapping :
    ∀ fs ∈ (parallelDeterminizedDerivation rs obs hc_opt id start), fs.constants ⊆ (rs.head_constants ∪ start.constants) := by
  intro fs fs_mem c c_mem
  suffices c ∈ rs.head_constants ∪ start.constants ∪ ∅ by rw [Set.mem_union_iff] at this; cases this; assumption; contradiction
  apply parallelDeterminizedDerivation_constants _ _ fs fs_mem c c_mem
  simp

/-- All function symbols that occur in the derivation come from the rule set's skolem functions or the starting fact set.
As for the general result on constants, this is using a strong (but slightly weaker) assumption on the remapping,
namely that every term is either mapped to itself or to a constant. Here, we do not care where this constant comes from. -/
theorem parallelDeterminizedDerivation_functions :
    (∀ t, remapping t ≠ t -> ∃ c, remapping t = .const c) ->
    ∀ fs ∈ (parallelDeterminizedDerivation rs obs hc_opt remapping start), fs.function_symbols ⊆ (rs.skolem_functions ∪ start.function_symbols) := by
  intro non_id_is_const fs fs_mem
  let elem : (parallelDeterminizedDerivation rs obs hc_opt remapping start).Element := ⟨fs, fs_mem⟩
  show elem.val.function_symbols ⊆ (rs.skolem_functions ∪ start.function_symbols)
  induction elem using parallelDeterminizedDerivation_mem_rec with
  | head =>
    intro func func_mem
    unfold FactSet.function_symbols at func_mem
    rcases func_mem with ⟨f, f_mem, func_mem⟩
    simp only [parallelDeterminizedDerivation_head] at f_mem
    apply Or.inr
    exists f
  | step _ ih =>
    intro func func_mem
    rcases func_mem with ⟨f, f_mem, func_mem⟩
    cases parallelDeterminizedDerivation_step_subset _ f_mem with
    | inl f_mem => apply ih; exists f
    | inr f_mem =>
      rcases TermMapping.mem_apply_generalized_atom_set.mp f_mem with ⟨f', ⟨trg, trg_act, ⟨i, lt, f'_mem⟩⟩, f_mem⟩
      simp only [f_mem, Fact.function_symbols, TermMapping.apply_generalized_atom, List.flatMap_map, List.mem_flatMap] at func_mem
      rcases func_mem with ⟨t, t_mem, func_mem⟩
      cases Decidable.em (remapping t = t) with
      | inr ne => rcases non_id_is_const t ne with ⟨c, t_eq⟩; simp [t_eq] at func_mem
      | inl eq =>
      rw [eq] at func_mem
      have t_mem : t ∈ (trg.val.mapped_head[i]'(by grind)).flatMap GeneralizedAtom.terms := by rw [List.mem_flatMap]; exists f'
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
            exists ⟨(trg.val.rule.head[i], i), by rw [List.mk_mem_zipIdx_iff_getElem?]; simp⟩
            constructor
            . simp
            . rw [func_mem, List.map_attach_eq_pmap]
              apply List.mem_pmap_of_mem
              exact v_mem
        | inr func_mem =>
          apply ih
          simp only [List.mem_flatMap] at func_mem; rcases func_mem with ⟨t, t_mem, func_mem⟩
          have t_mem_body := trg.val.mem_terms_mapped_body_of_mem_mapped_frontier _ t_mem
          rw [List.mem_flatMap] at t_mem_body; rcases t_mem_body with ⟨f, f_mem, t_mem⟩
          exists f
          constructor
          . apply trg_act.left; rw [List.mem_toSet]; exact f_mem
          . exact List.mem_flatMap_of_mem t_mem func_mem

/-- A special case of the above theorem with the id remapping. -/
theorem parallelDeterminizedDerivation_functions_with_id_remapping :
    ∀ fs ∈ (parallelDeterminizedDerivation rs obs hc_opt id start), fs.function_symbols ⊆ (rs.skolem_functions ∪ start.function_symbols) := by
  apply parallelDeterminizedDerivation_functions; simp

/-- All predicates in the derivation result come from the rules or the starting fact set. -/
theorem parallelDeterminizedDerivation_result_predicates :
    (parallelDeterminizedDerivation_result rs obs hc_opt remapping start).predicates ⊆ (rs.predicates ∪ start.predicates) := by
  rintro p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  apply parallelDeterminizedDerivation_predicates _ fs_mem
  exists f

/-- All constants in the derivation result come from the rule heads or the starting fact set or the fresh constants introduced by the remapping. -/
theorem parallelDeterminizedDerivation_result_constants :
    ∀ (freshConsts : Set sig.C), (∀ t, remapping t ≠ t -> ∃ c ∈ freshConsts, remapping t = .const c) ->
    (parallelDeterminizedDerivation_result rs obs hc_opt remapping start).constants ⊆ (rs.head_constants ∪ start.constants ∪ freshConsts) := by
  rintro freshConsts non_id_is_fresh p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  apply parallelDeterminizedDerivation_constants freshConsts non_id_is_fresh _ fs_mem
  exists f

/-- A special case of the above theorem with the id remapping. -/
theorem parallelDeterminizedDerivation_result_constants_with_id_remapping :
    (parallelDeterminizedDerivation_result rs obs hc_opt id start).constants ⊆ (rs.head_constants ∪ start.constants) := by
  rintro p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  apply parallelDeterminizedDerivation_constants_with_id_remapping _ fs_mem
  exists f

/-- All function symbols in the derivation result come from the rule set's skolem functions or the starting fact set. -/
theorem parallelDeterminizedDerivation_result_functions :
    (∀ t, remapping t ≠ t -> ∃ c, remapping t = .const c) ->
    (parallelDeterminizedDerivation_result rs obs hc_opt remapping start).function_symbols ⊆
    (rs.skolem_functions ∪ start.function_symbols) := by
  rintro non_id_is_const p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  apply parallelDeterminizedDerivation_functions non_id_is_const _ fs_mem
  exists f

/-- A special case of the above theorem with the id remapping. -/
theorem parallelDeterminizedDerivation_result_functions_with_id_remapping :
    (parallelDeterminizedDerivation_result rs obs hc_opt id start).function_symbols ⊆
    (rs.skolem_functions ∪ start.function_symbols) := by
  rintro p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  apply parallelDeterminizedDerivation_functions_with_id_remapping _ fs_mem
  exists f

end ParallelDeterminizedDerivation

/-!
## parallelDeterminizedChase

A `parallelDeterminizedChase` fixes a `KnowledgeBase` and start a `parallelDeterminizedDerivation` on the knowledge base's database.
Some of the above theorems thereby can be refined. For example, function symbols can now only be skolem functions as the database only has constants as terms.
-/

/-- A `parallelDeterminizedChase` is a special `parallelDeterminizedDerivation` starting on a database from a `KnowledgeBase`. -/
@[expose]
def parallelDeterminizedChase
    (kb : KnowledgeBase sig) (obs : LaxObsolescenceCondition sig) (hc_opt : Option (HeadChoice sig)) (remapping : GroundTermMapping sig) :
    InfiniteList (FactSet sig) :=
  parallelDeterminizedDerivation kb.rules obs hc_opt remapping kb.db.toFactSet.val

/-- The `parallelDeterminizedChase_result` is simply the result of the underlying derivation. -/
@[expose]
def parallelDeterminizedChase_result
    (kb : KnowledgeBase sig) (obs : LaxObsolescenceCondition sig) (hc_opt : Option (HeadChoice sig)) (remapping : GroundTermMapping sig) :
    FactSet sig :=
  parallelDeterminizedDerivation_result kb.rules obs hc_opt remapping kb.db.toFactSet.val

section ParallelDeterminizedChase

variable {kb : KnowledgeBase sig} {obs : LaxObsolescenceCondition sig} {hc_opt : Option (HeadChoice sig)} {remapping : GroundTermMapping sig}

/-- All constants in the chase come from the rule heads or the database or the fresh constants introduced by the remapping. -/
theorem parallelDeterminizedChase_constants :
    ∀ (freshConsts : Set sig.C), (∀ t, remapping t ≠ t -> ∃ c ∈ freshConsts, remapping t = .const c) ->
    ∀ fs ∈ (parallelDeterminizedChase kb obs hc_opt remapping), fs.constants ⊆ (kb.rules.head_constants ∪ kb.db.constants ∪ freshConsts) := by
  rw [← Database.toFactSet_constants_same]
  apply parallelDeterminizedDerivation_constants

/-- A special case of the above theorem with the id remapping. -/
theorem parallelDeterminizedChase_constants_with_id_remapping :
    ∀ fs ∈ (parallelDeterminizedChase kb obs hc_opt id), fs.constants ⊆ (kb.rules.head_constants ∪ kb.db.constants) := by
  rw [← Database.toFactSet_constants_same]
  apply parallelDeterminizedDerivation_constants_with_id_remapping

/-- All function symbols in the chase come from the rule set's skolem functions. -/
theorem parallelDeterminizedChase_functions :
    (∀ t, remapping t ≠ t -> ∃ c, remapping t = .const c) ->
    ∀ fs ∈ (parallelDeterminizedChase kb obs hc_opt remapping), fs.function_symbols ⊆ kb.rules.skolem_functions := by
  intro non_id_is_const _ fs_mem _ func_mem
  cases parallelDeterminizedDerivation_functions non_id_is_const _ fs_mem _ func_mem with
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

/-- A special case of the above theorem with the id remapping. -/
theorem parallelDeterminizedChase_functions_with_id_remapping :
    ∀ fs ∈ (parallelDeterminizedChase kb obs hc_opt id), fs.function_symbols ⊆ kb.rules.skolem_functions := by
  apply parallelDeterminizedChase_functions; simp

/-- All constants in the chase result come from the rule heads or the database or the fresh constants introduced by the remapping. -/
theorem parallelDeterminizedChase_result_constants :
    ∀ (freshConsts : Set sig.C), (∀ t, remapping t ≠ t -> ∃ c ∈ freshConsts, remapping t = .const c) ->
    (parallelDeterminizedChase_result kb obs hc_opt remapping).constants ⊆ (kb.rules.head_constants ∪ kb.db.constants ∪ freshConsts) := by
  rintro freshConsts non_id_is_fresh p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  rw [← parallelDeterminizedChase.eq_def] at fs_mem
  apply parallelDeterminizedChase_constants freshConsts non_id_is_fresh _ fs_mem
  exists f

/-- A special case of the above theorem with the id remapping. -/
theorem parallelDeterminizedChase_result_constants_with_id_remapping :
    (parallelDeterminizedChase_result kb obs hc_opt id).constants ⊆ (kb.rules.head_constants ∪ kb.db.constants) := by
  rintro p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  rw [← parallelDeterminizedChase.eq_def] at fs_mem
  apply parallelDeterminizedChase_constants_with_id_remapping _ fs_mem
  exists f

/-- All function symbols in the chase result come from the rule set's skolem functions. -/
theorem parallelDeterminizedChase_result_functions :
    (∀ t, remapping t ≠ t -> ∃ c, remapping t = .const c) ->
    (parallelDeterminizedChase_result kb obs hc_opt remapping).function_symbols ⊆ kb.rules.skolem_functions := by
  rintro non_id_is_const p ⟨f, ⟨fs, fs_mem, f_mem⟩, p_mem⟩
  rw [← parallelDeterminizedChase.eq_def] at fs_mem
  apply parallelDeterminizedChase_functions non_id_is_const _ fs_mem
  exists f

/-- A special case of the above theorem with the id remapping. -/
theorem parallelDeterminizedChase_result_functions_with_id_remapping :
    (parallelDeterminizedChase_result kb obs hc_opt id).function_symbols ⊆ kb.rules.skolem_functions := by
  apply parallelDeterminizedChase_result_functions; simp

end ParallelDeterminizedChase

