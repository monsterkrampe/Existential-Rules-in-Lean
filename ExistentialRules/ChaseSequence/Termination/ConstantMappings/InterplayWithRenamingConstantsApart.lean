import ExistentialRules.ChaseSequence.Termination.ConstantMappings.SkolemTermValidityPreserved

/-!
# Interaction of Strict Constant Mappings and Renaming Constant Apart

For `PreGroundTerm`, `GroundTerm`, `GroundSubstitution`, and `PreTrigger`, we do the following things:

1. We define what it means for them to have the `same_skeleton`, which is the case if their only difference is the naming of constants in terms (but their structure is the same),
2. we show that applying a `StrictConstantMapping` yields something that has the same skeleton,
3. we show that for two things with the same skeleton, we can find a `StrictConstantMapping` that maps the renamed apart version of the first thing to the second one while mapping each constant to itself that does not occur in the renamed apart version.
-/

namespace PreGroundTerm

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

-- TODO maybe replace mutual recursion by demanding equal length and then equality on each index? this does not sound much nicer though...

mutual

  def same_skeleton (term term2 : PreGroundTerm sig) : Prop :=
    match term with
    | .leaf _ => match term2 with | .leaf _ => True | .inner _ _ => False
    | .inner func ts => match term2 with | .leaf _ => False | .inner func' ts' => func = func' ∧ same_skeleton_list ts ts'

  def same_skeleton_list (terms terms2 : List (PreGroundTerm sig)) : Prop :=
    match terms with
    | .nil => match terms2 with | .nil => True | .cons _ _ => False
    | .cons hd tl => match terms2 with | .nil => False | .cons hd' tl' => same_skeleton hd hd' ∧ same_skeleton_list tl tl'

end

mutual

  theorem same_skeleton_refl (term : PreGroundTerm sig) : same_skeleton term term := by
    cases term with
    | leaf => simp [same_skeleton]
    | inner func ts => simp only [same_skeleton, true_and]; apply same_skeleton_list_refl

  theorem same_skeleton_list_refl (terms : List (PreGroundTerm sig)) : same_skeleton_list terms terms := by
    cases terms with
    | nil => simp [same_skeleton_list]
    | cons hd tl => simp only [same_skeleton_list]; constructor; apply same_skeleton_refl; apply same_skeleton_list_refl

end

mutual

  theorem same_skeleton_symm (term term2 : PreGroundTerm sig) : same_skeleton term term2 -> same_skeleton term2 term := by
    cases term with
    | leaf => cases term2 <;> simp [same_skeleton]
    | inner func ts => cases term2; simp [same_skeleton]; simp only [same_skeleton]; intro h; constructor; rw [h.left]; apply same_skeleton_list_symm; exact h.right

  theorem same_skeleton_list_symm (terms terms2 : List (PreGroundTerm sig)) : same_skeleton_list terms terms2 -> same_skeleton_list terms2 terms := by
    cases terms with
    | nil => cases terms2 <;> simp [same_skeleton_list]
    | cons hd tl => cases terms2; simp [same_skeleton_list]; simp only [same_skeleton_list]; intro h; constructor; apply same_skeleton_symm; exact h.left; apply same_skeleton_list_symm; exact h.right

end

variable [DecidableEq sig.P]

mutual

  theorem same_skeleton_under_strict_constant_mapping (term : PreGroundTerm sig) (g : StrictConstantMapping sig) : same_skeleton term (g.toConstantMapping.apply_pre_ground_term term) := by
    cases term with
    | leaf => simp [same_skeleton, ConstantMapping.apply_pre_ground_term, StrictConstantMapping.toConstantMapping, GroundTerm.const, FiniteTree.mapLeaves]
    | inner func ts => simp only [same_skeleton, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, true_and]; apply same_skeleton_list_under_strict_constant_mapping

  theorem same_skeleton_list_under_strict_constant_mapping (terms : List (PreGroundTerm sig)) (g : StrictConstantMapping sig) : same_skeleton_list terms (terms.map g.toConstantMapping.apply_pre_ground_term) := by
    cases terms with
    | nil => simp [same_skeleton_list]
    | cons hd tl => simp only [same_skeleton_list]; constructor; apply same_skeleton_under_strict_constant_mapping; apply same_skeleton_list_under_strict_constant_mapping

end

mutual

  theorem exists_strict_constant_mapping_to_reverse_renaming [GetFreshInhabitant sig.C] (term term2 : PreGroundTerm sig) (terms_same_skeleton : same_skeleton term term2) (forbidden_constants : List sig.C) :
      ∃ (g : StrictConstantMapping sig),
        g.toConstantMapping.apply_pre_ground_term (PreGroundTerm.rename_constants_apart term forbidden_constants) = term2 ∧
        (∀ d, d ∉ (PreGroundTerm.rename_constants_apart term forbidden_constants).leaves -> g d = d) := by
    cases term with
    | leaf c =>
      cases term2 with
      | leaf c' =>
        exists (fun d => if GetFreshInhabitant.fresh forbidden_constants = d then c' else d); simp [PreGroundTerm.rename_constants_apart, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, GroundTerm.const]
        simp only [FiniteTree.leaves, List.mem_singleton]
        intro _ contra1 contra2
        rw [contra2] at contra1
        simp at contra1
      | inner _ _ => simp [same_skeleton] at terms_same_skeleton
    | inner func ts =>
      cases term2 with
      | leaf _ => simp [same_skeleton] at terms_same_skeleton
      | inner func' ts' =>
        simp only [same_skeleton] at terms_same_skeleton
        rcases exists_strict_constant_mapping_to_reverse_renaming_list ts ts' terms_same_skeleton.right forbidden_constants with ⟨g, g_eq, g_id⟩
        exists g
        simp only [PreGroundTerm.rename_constants_apart, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves]
        rw [FiniteTree.inner.injEq]
        constructor
        . constructor
          . exact terms_same_skeleton.left
          . exact g_eq
        . unfold FiniteTree.leaves; exact g_id

  theorem exists_strict_constant_mapping_to_reverse_renaming_list [GetFreshInhabitant sig.C] (terms terms2 : List (PreGroundTerm sig)) (terms_same_skeleton : same_skeleton_list terms terms2) (forbidden_constants : List sig.C) :
      ∃ (g : StrictConstantMapping sig),
        (PreGroundTerm.rename_constants_apart.foldl_list terms forbidden_constants).map (fun term => g.toConstantMapping.apply_pre_ground_term term) = terms2 ∧
        (∀ d, d ∉ (PreGroundTerm.rename_constants_apart.foldl_list terms forbidden_constants).flatMap FiniteTree.leaves -> g d = d) := by
    cases terms with
    | nil =>
      cases terms2 with
      | nil => exists id; simp [rename_constants_apart.foldl_list, rename_constants_apart.foldl_list_with_init]
      | cons _ _ => simp [same_skeleton_list] at terms_same_skeleton
    | cons hd tl =>
      cases terms2 with
      | nil => simp [same_skeleton_list] at terms_same_skeleton
      | cons hd' tl' =>
        simp only [same_skeleton_list] at terms_same_skeleton
        let hd_res := PreGroundTerm.rename_constants_apart hd forbidden_constants

        rcases exists_strict_constant_mapping_to_reverse_renaming hd hd' terms_same_skeleton.left forbidden_constants with ⟨h, h_eq, h_id⟩

        rcases exists_strict_constant_mapping_to_reverse_renaming_list tl tl' terms_same_skeleton.right (forbidden_constants ++ hd_res.leaves) with ⟨g, g_eq, g_id⟩

        exists (fun d => if d ∈ hd_res.leaves then h d else g d)
        rw [rename_constants_apart.foldl_list_cons, List.map_cons, List.cons_eq_cons]
        constructor
        . constructor
          . conv => right; rw [← h_eq]
            unfold ConstantMapping.apply_pre_ground_term
            apply FiniteTree.mapLeaves_eq_of_map_leaves_eq
            rw [List.map_inj_left]
            intro d d_mem
            simp [StrictConstantMapping.toConstantMapping, GroundTerm.const, hd_res, d_mem]
          . conv => right; rw [← g_eq]
            rw [List.map_inj_left]
            intro t t_mem
            unfold ConstantMapping.apply_pre_ground_term
            apply FiniteTree.mapLeaves_eq_of_map_leaves_eq
            rw [List.map_inj_left]
            intro d d_mem
            have : ¬ d ∈ hd_res.leaves := by
              intro contra
              rcases rename_constants_apart.mem_foldl_list_implies t_mem with ⟨t', new_consts, t'_mem, t_eq⟩
              rw [t_eq] at d_mem
              apply rename_constants_apart_leaves_fresh d_mem
              rw [List.mem_append]
              apply Or.inl
              rw [List.mem_append]
              apply Or.inr
              exact contra
            simp [StrictConstantMapping.toConstantMapping, GroundTerm.const, this]
        . intro d d_mem
          rw [List.flatMap_cons, List.mem_append] at d_mem
          cases Decidable.em (d ∈ hd_res.leaves) with
          | inl d_mem' => apply False.elim; apply d_mem; apply Or.inl; exact d_mem'
          | inr d_mem' => simp only [d_mem', ↓reduceIte]; apply g_id; intro contra; apply d_mem; apply Or.inr; exact contra

end

end PreGroundTerm

namespace GroundTerm

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

def same_skeleton (term term2 : GroundTerm sig) : Prop := PreGroundTerm.same_skeleton term.val term2.val

theorem same_skeleton_refl (term : GroundTerm sig) : term.same_skeleton term := by unfold same_skeleton; apply PreGroundTerm.same_skeleton_refl

theorem same_skeleton_symm (term term2 : GroundTerm sig) : term.same_skeleton term2 -> term2.same_skeleton term := by unfold same_skeleton; apply PreGroundTerm.same_skeleton_symm

variable [DecidableEq sig.P]

theorem same_skeleton_under_strict_constant_mapping (term : GroundTerm sig) (g : StrictConstantMapping sig) : term.same_skeleton (g.toConstantMapping.apply_ground_term term) := by unfold same_skeleton; apply PreGroundTerm.same_skeleton_under_strict_constant_mapping

theorem exists_strict_constant_mapping_to_reverse_renaming [GetFreshInhabitant sig.C] (term term2 : GroundTerm sig) (terms_same_skeleton : same_skeleton term term2) (forbidden_constants : List sig.C) :
    ∃ (g : StrictConstantMapping sig),
      g.toConstantMapping.apply_ground_term (term.rename_constants_apart forbidden_constants) = term2 ∧
      (∀ d, d ∉ (term.rename_constants_apart forbidden_constants).constants -> g d = d) := by
  unfold rename_constants_apart
  unfold ConstantMapping.apply_ground_term
  rcases PreGroundTerm.exists_strict_constant_mapping_to_reverse_renaming term.val term2.val terms_same_skeleton forbidden_constants with ⟨g, g_eq⟩
  exists g
  rw [Subtype.mk.injEq]
  exact g_eq

end GroundTerm

namespace GroundSubstitution

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

def same_skeleton_for_vars (subs subs2 : GroundSubstitution sig) : List sig.V -> Prop
| .nil => True
| .cons hd tl => (subs hd).same_skeleton (subs2 hd) ∧ subs.same_skeleton_for_vars subs2 tl

theorem same_skeleton_for_vars_refl (subs : GroundSubstitution sig) (vars : List sig.V) : subs.same_skeleton_for_vars subs vars := by
  induction vars with
  | nil => simp [same_skeleton_for_vars]
  | cons hd tl ih => unfold same_skeleton_for_vars; constructor; apply GroundTerm.same_skeleton_refl; exact ih

theorem same_skeleton_for_vars_symm (subs subs2 : GroundSubstitution sig) (vars : List sig.V) : subs.same_skeleton_for_vars subs2 vars -> subs2.same_skeleton_for_vars subs vars := by
  induction vars with
  | nil => simp [same_skeleton_for_vars]
  | cons hd tl ih => unfold same_skeleton_for_vars; intro h; constructor; apply GroundTerm.same_skeleton_symm; exact h.left; apply ih; exact h.right

variable [DecidableEq sig.P]

theorem same_skeleton_for_vars_under_strict_constant_mapping (subs : GroundSubstitution sig) (vars : List sig.V) (g : StrictConstantMapping sig) : subs.same_skeleton_for_vars (g.toConstantMapping.apply_ground_term ∘ subs) vars := by
  induction vars with
  | nil => simp [same_skeleton_for_vars]
  | cons hd tl ih => unfold same_skeleton_for_vars; constructor; apply GroundTerm.same_skeleton_under_strict_constant_mapping; exact ih

-- NOTE: induction over vars for rename_constants_apart_for_vars does not work nicely without assuming that the vars do not contain duplicates
theorem exists_strict_constant_mapping_to_reverse_renaming_for_vars [GetFreshInhabitant sig.C] (subs subs2 : GroundSubstitution sig) (vars : List sig.V) (vars_nodup : vars.Nodup) (subs_same_skeleton : same_skeleton_for_vars subs subs2 vars) (forbidden_constants : List sig.C) :
    ∃ (g : StrictConstantMapping sig),
      (∀ v ∈ vars, g.toConstantMapping.apply_ground_term (subs.rename_constants_apart_for_vars forbidden_constants vars v) = subs2 v) ∧
      (∀ d, d ∉ ((vars.map (subs.rename_constants_apart_for_vars forbidden_constants vars)).flatMap GroundTerm.constants) -> g d = d) := by
  induction vars generalizing forbidden_constants with
  | nil => exists id; simp
  | cons hd tl ih =>
    simp only [same_skeleton_for_vars] at subs_same_skeleton
    have g_ex_hd := GroundTerm.exists_strict_constant_mapping_to_reverse_renaming (subs hd) (subs2 hd) subs_same_skeleton.left forbidden_constants
    rcases g_ex_hd with ⟨g_hd, g_hd_h⟩

    let renamed_term_for_hd := (subs hd).rename_constants_apart forbidden_constants
    let new_forbidden := forbidden_constants ++ renamed_term_for_hd.constants
    have g_ex_tl := ih (List.nodup_cons.mp vars_nodup).right subs_same_skeleton.right new_forbidden
    rcases g_ex_tl with ⟨g_tl, g_tl_h⟩

    let g : StrictConstantMapping sig := fun d =>
      if d ∈ renamed_term_for_hd.constants then g_hd d else g_tl d

    have g_aux : g.toConstantMapping.apply_ground_term renamed_term_for_hd = g_hd.toConstantMapping.apply_ground_term renamed_term_for_hd := by
      simp only [g, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, Subtype.mk.injEq]
      apply FiniteTree.mapLeaves_eq_of_map_leaves_eq
      rw [List.map_inj_left]
      intro d d_mem
      simp only [Function.comp_apply, GroundTerm.const]
      simp [GroundTerm.constants, d_mem]

    have g_aux2 : ∀ v ∈ tl, g.toConstantMapping.apply_ground_term (subs.rename_constants_apart_for_vars new_forbidden tl v) = g_tl.toConstantMapping.apply_ground_term (subs.rename_constants_apart_for_vars new_forbidden tl v) := by
      intro v v_mem
      simp only [g, StrictConstantMapping.toConstantMapping, ConstantMapping.apply_ground_term, ConstantMapping.apply_pre_ground_term, Subtype.mk.injEq]
      apply FiniteTree.mapLeaves_eq_of_map_leaves_eq
      rw [List.map_inj_left]
      intro d d_mem
      simp only [Function.comp_apply, GroundTerm.const]
      have d_nmem : d ∉ renamed_term_for_hd.constants := by
        have : d ∉ new_forbidden := by
          apply subs.rename_constants_apart_for_vars_constants_fresh new_forbidden tl v v_mem
          exact d_mem
        intro contra
        apply this
        simp [new_forbidden, contra]
      simp [d_nmem]

    exists g
    constructor
    . intro v v_mem
      rw [List.mem_cons] at v_mem
      unfold rename_constants_apart_for_vars
      cases Decidable.em (v = hd) with
      | inl v_eq_hd =>
        simp only [v_eq_hd, ↓reduceIte]
        rw [g_aux]
        exact g_hd_h.left
      | inr v_neq_hd =>
        have v_mem : v ∈ tl := by cases v_mem; contradiction; assumption
        simp only [v_neq_hd, ↓reduceIte]
        rw [g_aux2 _ v_mem]
        exact g_tl_h.left _ v_mem
    . intro d d_nmem
      simp only [rename_constants_apart_for_vars, List.map_cons, List.flatMap_cons, ↓reduceIte] at d_nmem
      have : d ∉ renamed_term_for_hd.constants := by
        intro contra
        apply d_nmem
        rw [List.mem_append]
        apply Or.inl
        exact contra
      simp only [g, this, ↓reduceIte]
      apply g_tl_h.right
      intro contra
      apply d_nmem
      rw [List.mem_append]
      apply Or.inr

      rw [List.mem_flatMap] at contra
      rcases contra with ⟨t, t_mem, d_mem⟩
      rw [List.mem_map] at t_mem
      rcases t_mem with ⟨v, v_mem, t_eq⟩
      have v_neq : v ≠ hd := by
        intro contra
        apply (List.nodup_cons.mp vars_nodup).left
        rw [← contra]
        exact v_mem
      rw [List.mem_flatMap]
      exists t
      constructor
      . rw [List.mem_map]
        exists v
        constructor
        . exact v_mem
        . simp only [v_neq, ↓reduceIte]
          rw [← t_eq]
      . exact d_mem

end GroundSubstitution

namespace PreTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

def same_skeleton (trg trg2 : PreTrigger sig) : Prop :=
  trg.rule = trg2.rule ∧
  trg.subs.same_skeleton_for_vars trg2.subs trg.rule.body.vars.eraseDupsKeepRight

theorem same_skeleton_refl (trg : PreTrigger sig) : trg.same_skeleton trg := by unfold same_skeleton; simp [GroundSubstitution.same_skeleton_for_vars_refl]

theorem same_skeleton_symm (trg trg2 : PreTrigger sig) : trg.same_skeleton trg2 -> trg2.same_skeleton trg := by
  unfold same_skeleton
  intro h
  constructor
  . rw [h.left]
  . apply GroundSubstitution.same_skeleton_for_vars_symm
    rw [← h.left]
    exact h.right

-- TODO: also show transitivity (but I think as of now we do not need it)

theorem same_skeleton_under_strict_constant_mapping (trg : PreTrigger sig) (g : StrictConstantMapping sig) : trg.same_skeleton {rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ trg.subs} := by
  unfold same_skeleton
  simp [GroundSubstitution.same_skeleton_for_vars_under_strict_constant_mapping]

theorem exists_strict_constant_mapping_to_reverse_renaming [GetFreshInhabitant sig.C] (trg trg2 : PreTrigger sig) (trgs_same_skeleton : same_skeleton trg trg2) (forbidden_constants : List sig.C) :
    ∃ (g : StrictConstantMapping sig),
      { rule := trg.rule, subs := g.toConstantMapping.apply_ground_term ∘ (trg.rename_constants_apart forbidden_constants).subs : PreTrigger sig }.strong_equiv trg2 ∧
      (∀ d, d ∉ (trg.rule.body.vars.eraseDupsKeepRight.map (trg.rename_constants_apart forbidden_constants).subs).flatMap GroundTerm.constants -> g d = d) := by
  rcases trg.subs.exists_strict_constant_mapping_to_reverse_renaming_for_vars trg2.subs trg.rule.body.vars.eraseDupsKeepRight trg.rule.body.vars.nodup_eraseDupsKeepRight trgs_same_skeleton.right forbidden_constants with ⟨g, g_h⟩
  exists g
  constructor
  . constructor
    . exact trgs_same_skeleton.left
    . intro v v_mem
      simp only [rename_constants_apart, Function.comp_apply]
      apply g_h.left
      rw [List.mem_eraseDupsKeepRight]
      exact v_mem
  . intro d d_nmem
    apply g_h.right
    exact d_nmem

end PreTrigger

