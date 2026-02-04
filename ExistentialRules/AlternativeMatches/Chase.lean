import ExistentialRules.AlternativeMatches.Basic
import ExistentialRules.AlternativeMatches.HomomorphismExtension
import ExistentialRules.Models.Cores

/-!
# Alternative Matches and the Chase

In this file, we relate alternative matches to `ChaseDerivation` and `ChaseBranch`.
All of this considers the deterministic setting, i.e. only rule sets where each rule has exactly one head disjunct.
One of the main result is `result_isStrongCore_of_noAltMatch`, which states
that the result of a `ChaseBranch` without alternative matches is always a strong core.
-/

namespace GroundTermMapping

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]
variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

/-- A `GroundTermMapping` is an alternative for a `ChaseDerivation` and a `FactSet` if it is an alternative match into the fact set for the trigger is used to derive `ChaseDerivation.next`. -/
def is_alt_match_for_chase_derivation_and_fs (h : GroundTermMapping sig) (cd : ChaseDerivation obs rules) (fs : FactSet sig) : Prop :=
  ∃ (next : ChaseNode obs rules) (next_mem : next ∈ cd.next),
    let origin := next.origin.get (cd.isSome_origin_next next_mem)
    h.isAlternativeMatch origin.fst.val origin.snd fs

end GroundTermMapping

namespace ChaseDerivation

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]
variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

/-- A `ChaseDerivation` has an alternative match into a `FactSet` simply if there is a `GroundTermMapping` that is such an alternative match for `ChaseDerivation.next`. -/
def has_alt_match_for_next_and_fs (cd : ChaseDerivation obs rules) (fs : FactSet sig) : Prop :=
  ∃ (h : GroundTermMapping sig), h.is_alt_match_for_chase_derivation_and_fs cd fs

/-- More generally, a `ChaseDerivation` has an alternative match into a `FactSet` if one of its subderivations has an alternative match for `ChaseDerivation.next` (according to the above definition) into the fact set. -/
def has_alt_match_for_fs (cd : ChaseDerivation obs rules) (fs : FactSet sig) : Prop :=
  ∃ cd2 : ChaseDerivation obs rules, cd2 <:+ cd ∧ cd2.has_alt_match_for_next_and_fs fs

/-- Finally, a `ChaseDerivation` has an alternative match, if it has an alternative match into its own result. -/
def has_alt_match (cd : ChaseDerivation obs rules) : Prop := cd.has_alt_match_for_fs cd.result

end ChaseDerivation

namespace ChaseBranch

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

/-- If a `ChaseBranch` has no alternative match (into its own result), then the result is a weak core. -/
theorem result_isWeakCore_of_noAltMatch {cb : ChaseBranch obs kb} (det : kb.isDeterministic) :
    ¬ cb.has_alt_match -> cb.result.isWeakCore := by
  intro noAltMatch h_0 h_0_hom
  apply Classical.byContradiction
  intro contra
  rw [Classical.not_and_iff_not_or_not] at contra

  have : ∀ node : cb.Node,
    ∃ (h_k : GroundTermMapping sig),
      (h_k.isHomomorphism cb.result cb.result) ∧
      ((∀ (f : Fact sig),
        (∀ (t : GroundTerm sig), t ∈ f.terms -> t ∈ cb.result.terms) -> ¬ f ∈ cb.result -> h_0.applyFact f ∈ cb.result ->
          h_k.applyFact f ∈ cb.result) ∧
            (∀ s t, s ∈ cb.result.terms -> t ∈ cb.result.terms -> s ≠ t -> h_0 s = h_0 t -> h_k s = h_k t)) ∧
      (∀ t, t ∈ node.val.facts.terms -> h_k t = t) := by
    intro node
    induction node using cb.mem_rec with
    | head =>
      exists h_0
      constructor
      . exact h_0_hom
      . constructor
        . constructor
          . simp
          . simp
        . intro t t_mem
          simp at t_mem
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          rw [cb.database_first'] at f_mem

          have isFunctionFree := kb.db.toFactSet.property.right
          specialize isFunctionFree _ f_mem
          specialize isFunctionFree t t_mem
          rcases isFunctionFree with ⟨c, t_eq⟩
          rw [t_eq]

          exact h_0_hom.left
    | step cd2 suffix ih next next_mem =>
      rcases ih with ⟨h_k, h_k_hom, retains, identity⟩

      have origin_isSome := cd2.isSome_origin_next next_mem
      have origin_trg_active := cd2.active_trigger_origin_next next_mem
      let origin := next.origin.get origin_isSome

      let trg_res_terms := (FactSet.terms (next.origin_result origin_isSome).toSet)

      have identity_frontier : ∀ t ∈ List.map (next.origin.get origin_isSome).fst.val.subs (next.origin.get origin_isSome).fst.val.rule.frontier, h_k t = t := by
        intro t t_mem
        apply identity
        rw [List.mem_map] at t_mem
        rcases t_mem with ⟨v, v_mem, v_eq⟩
        apply FactSet.terms_subset_of_subset origin_trg_active.left
        rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
        apply Or.inr
        exists v; constructor
        . exact Rule.frontier_subset_vars_body v_mem
        . exact v_eq

      have h_surj_on_trg_res : h_k.surjective_for_domain_and_image_set trg_res_terms trg_res_terms := by
        apply Classical.byContradiction
        intro not_surj
        apply noAltMatch
        exists cd2
        constructor
        . exact suffix
        exists h_k, next, next_mem
        constructor
        . constructor
          . exact h_k_hom.left
          . apply Set.subset_trans _ h_k_hom.right
            apply TermMapping.apply_generalized_atom_set_subset_of_subset
            rw [← ChaseDerivation.result_suffix suffix]
            apply Set.subset_trans _ (cd2.facts_node_subset_result next (cd2.next_mem_of_mem _ next_mem))
            rw [cd2.facts_next next_mem]
            apply Set.subset_union_of_subset_right
            apply Set.subset_refl
        constructor
        . exact identity_frontier
        . unfold Function.surjective_for_domain_and_image_set at not_surj
          simp only [Classical.not_forall, not_exists, not_and] at not_surj
          rcases not_surj with ⟨t, t_mem, no_arg_for_t⟩
          have no_arg_for_t_with_t := no_arg_for_t t t_mem
          simp only [trg_res_terms, FactSet.mem_terms_toSet, ChaseNode.origin_result] at t_mem
          rw [PreTrigger.mem_terms_mapped_head_iff] at t_mem
          cases t_mem with
          | inl t_mem => apply False.elim; apply no_arg_for_t_with_t; rcases t_mem with ⟨_, _, t_eq⟩; rw [← t_eq]; exact h_k_hom.left
          | inr t_mem =>
          cases t_mem with
          | inl t_mem =>
            apply False.elim; apply no_arg_for_t_with_t
            apply identity_frontier
            rw [List.mem_map] at t_mem
            rw [List.mem_map]
            rcases t_mem with ⟨v, v_mem, t_mem⟩
            exists v; simp only [t_mem, and_true]
            rw [Rule.mem_frontier_iff_mem_frontier_for_head]
            exact ⟨_, v_mem⟩
          | inr t_mem =>
          exists t
          constructor
          . exact t_mem
          . intro t_mem_image
            rw [List.mem_map] at t_mem_image
            rcases t_mem_image with ⟨t', t'_mem, t_mem_image⟩
            apply no_arg_for_t t' _ t_mem_image
            simp only [trg_res_terms, FactSet.mem_terms_toSet, ChaseNode.origin_result]
            rw [PreTrigger.mem_terms_mapped_head_iff]
            apply Or.inr; apply Or.inr
            exact t'_mem

      have h_surj_on_step : h_k.surjective_for_domain_and_image_set next.facts.terms next.facts.terms := by
        rw [cd2.facts_next next_mem, FactSet.terms_union]
        intro t t_mem
        cases t_mem with
        | inl t_mem => exists t; constructor; apply Or.inl; exact t_mem; apply identity; exact t_mem
        | inr t_mem =>
          rcases h_surj_on_trg_res t t_mem with ⟨s, s_mem, s_eq⟩
          exists s
          constructor
          . apply Or.inr; exact s_mem
          . exact s_eq

      have node_terms_finite := next.facts.terms_finite_of_finite (cb.facts_finite_of_mem ⟨next, (cd2.mem_of_mem_suffix suffix _ (cd2.next_mem_of_mem _ next_mem))⟩)
      rcases node_terms_finite with ⟨l_terms, l_terms_nodup, l_terms_eq⟩

      rw [h_k.surjective_set_list_equiv _ _ l_terms_eq _ _ l_terms_eq] at h_surj_on_step

      have h_inj_on_step : h_k.injective_for_domain_list l_terms := Function.injective_of_surjective_of_nodup h_k l_terms l_terms_nodup h_surj_on_step
      have h_closed_on_step : ∀ t, t ∈ l_terms -> h_k t ∈ l_terms := Function.closed_of_injective_of_surjective_of_nodup h_k l_terms l_terms_nodup h_inj_on_step h_surj_on_step

      have inv_ex := h_k.exists_repetition_that_is_inverse_of_surj l_terms h_surj_on_step
      rcases inv_ex with ⟨repetition_number, inv_prop⟩
      let inv := h_k.repeat_hom repetition_number

      have inv_hom : inv.isHomomorphism next.facts cb.result := by
        constructor
        . apply h_k.repeat_hom_id_on_const
          exact h_k_hom.left
        . have is_hom := h_k.repeat_hom_isHomomorphism cb.result h_k_hom repetition_number
          apply Set.subset_trans _ is_hom.right
          apply inv.apply_generalized_atom_set_subset_of_subset
          rw [← ChaseDerivation.result_suffix suffix]
          exact (cd2.facts_node_subset_result next (cd2.next_mem_of_mem _ next_mem))

      rcases cb.hom_for_node_extendable_to_result det (cd2.mem_of_mem_suffix suffix _ (cd2.next_mem_of_mem _ next_mem)) inv_hom with ⟨extended_inv, extended_inv_eq, extended_inv_hom⟩

      exists extended_inv ∘ h_k
      constructor
      . apply GroundTermMapping.isHomomorphism_compose _ _ _ cb.result _
        . exact h_k_hom
        . exact extended_inv_hom
      constructor
      . constructor
        . intro f terms_mem f_mem apply_mem
          unfold GroundTermMapping.applyFact
          rw [TermMapping.apply_generalized_atom_compose, Function.comp_apply]
          apply extended_inv_hom.right
          apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
          exact retains.left f terms_mem f_mem apply_mem
        . intro s t s_mem t_mem neq h_0_eq
          simp
          rw [retains.right s t s_mem t_mem neq h_0_eq]
      . intro t t_mem
        simp
        rw [extended_inv_eq]
        . rw [← l_terms_eq] at t_mem
          unfold inv
          rw [inv_prop t t_mem]
        . rw [← l_terms_eq]
          rw [← l_terms_eq] at t_mem
          apply h_closed_on_step
          exact t_mem

  cases contra with
  | inl not_strong =>
    apply not_strong
    unfold GroundTermMapping.strong
    intro f f_dom f_mem apply_f_mem

    have step_ex : ∃ node ∈ cb.toChaseDerivation, ∀ t, t ∈ f.terms -> t ∈ node.facts.terms := by
      have f_dom : f.terms.toSet ⊆ cb.result.terms := by intro _ mem; rw [List.mem_toSet] at mem; apply f_dom; exact mem
      rcases FactSet.list_of_facts_for_list_of_terms f_dom with ⟨l, l_sub, ts_sub⟩
      rcases cb.facts_mem_some_node_of_mem_result _ l_sub with ⟨node, node_mem, l_sub⟩
      exists node; simp only [node_mem, true_and]
      intro t t_mem
      apply FactSet.terms_subset_of_subset l_sub
      rw [FactSet.mem_terms_toSet]
      apply ts_sub; exact t_mem

    rcases step_ex with ⟨node, node_mem, step_ex⟩
    specialize this ⟨node, node_mem⟩
    rcases this with ⟨h_k, _, retains, identity⟩
    have retains := retains.left f f_dom f_mem apply_f_mem

    have : h_k.applyFact f = f := by
      apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
      intro t t_mem
      apply identity
      apply step_ex
      exact t_mem
    apply f_mem
    rw [← this]
    exact retains
  | inr not_inj =>
    apply not_inj
    intro s t s_mem t_mem image_eq
    apply Classical.byContradiction
    intro neq

    rcases s_mem with ⟨f_s, ⟨node_s, node_s_mem, f_s_mem⟩, s_mem⟩
    rcases t_mem with ⟨f_t, ⟨node_t, node_t_mem, f_t_mem⟩, t_mem⟩
    cases cb.predecessor_total ⟨node_s, node_s_mem⟩ ⟨node_t, node_t_mem⟩ with
    | inl pred =>
      rcases this ⟨node_t, node_t_mem⟩ with ⟨h_k, _, ⟨_, retains⟩, identity⟩
      specialize retains s t
        (by exists f_s; constructor; exists node_s; exact s_mem)
        (by exists f_t; constructor; exists node_t; exact t_mem)
        neq image_eq
      have id_s := identity s (by
        exists f_s
        constructor
        . apply cb.facts_node_subset_of_prec pred
          exact f_s_mem
        . exact s_mem
      )
      have id_t := identity t (by exists f_t)
      rw [id_s, id_t] at retains
      apply neq
      apply retains
    | inr pred =>
      rcases this ⟨node_s, node_s_mem⟩ with ⟨h_k, _, ⟨_, retains⟩, identity⟩
      specialize retains s t
        (by exists f_s; constructor; exists node_s; exact s_mem)
        (by exists f_t; constructor; exists node_t; exact t_mem)
        neq image_eq
      have id_s := identity s (by exists f_s)
      have id_t := identity t (by
        exists f_t
        constructor
        . apply cb.facts_node_subset_of_prec pred
          exact f_t_mem
        . exact t_mem
      )
      rw [id_s, id_t] at retains
      apply neq
      apply retains

/-- If a `ChaseBranch` has an alternative match (into its own result), then there is an non-trivial endomorphism on the result, i.e. an endomorphism that is not the identity. -/
theorem non_id_endomorphism_of_altMatch {cb : ChaseBranch obs kb} (det : kb.isDeterministic) (altMatch : cb.has_alt_match) :
    ∃ (endo : GroundTermMapping sig), endo.isHomomorphism cb.result cb.result ∧ ∃ t, endo t ≠ t := by
  rcases altMatch with ⟨cd, suffix, h_alt, next, next_mem, altMatch⟩

  have ts_finite := cd.head.facts.terms_finite_of_finite (cb.facts_finite_of_mem ⟨cd.head, ChaseDerivation.mem_of_mem_suffix suffix _ cd.head_mem⟩)
  rcases ts_finite with ⟨ts, nodup, eq_ts⟩

  let h : GroundTermMapping sig := fun t => if t ∈ ts then t else h_alt t
  have hom : h.isHomomorphism next.facts cb.result := by
    constructor
    . intro c; unfold h; split; rfl; exact altMatch.left.left
    rw [cd.facts_next next_mem]
    rintro f ⟨f', f'_mem, f_eq⟩
    cases f'_mem with
    | inl f'_mem =>
      have : f = f' := by
        rw [f_eq]; apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
        intro t t_mem
        have : t ∈ ts := by rw [eq_ts]; exists f'
        simp [h, this]
      rw [this, ← ChaseDerivation.result_suffix suffix]; apply cd.facts_node_subset_result _ cd.head_mem _ f'_mem
    | inr f'_mem =>
      apply altMatch.left.right
      have : f = h_alt.applyFact f' := by
        rw [f_eq]; apply TermMapping.apply_generalized_atom_congr_left
        intro t t_mem
        have t_mem : t ∈ (next.origin_result (cd.isSome_origin_next next_mem)).flatMap GeneralizedAtom.terms := by rw [List.mem_flatMap]; exists f'
        simp only [ChaseNode.origin_result, PreTrigger.mem_terms_mapped_head_iff] at t_mem
        cases t_mem with
        | inl t_mem => rcases t_mem with ⟨_, _, t_mem⟩; rw [← t_mem]; unfold h; split <;> simp [altMatch.left.left]
        | inr t_mem =>
        cases t_mem with
        | inl t_mem =>
          have t_mem : t ∈ (next.origin.get (cd.isSome_origin_next next_mem)).fst.val.rule.frontier.map (next.origin.get (cd.isSome_origin_next next_mem)).fst.val.subs := by
            rw [List.mem_map] at t_mem; rw [List.mem_map]; rcases t_mem with ⟨v, v_mem, t_mem⟩; exists v; simp only [t_mem, and_true]
            rw [Rule.mem_frontier_iff_mem_frontier_for_head]; exact ⟨_, v_mem⟩
          unfold h; split <;> simp [altMatch.right.left _ t_mem]
        | inr t_mem =>
          have : ¬ t ∈ ts := by
            intro contra; rw [eq_ts] at contra
            apply (cd.active_trigger_origin_next next_mem).right
            apply obs.contains_trg_result_implies_cond
            let head : cb.Node := ⟨cd.head, ChaseDerivation.mem_of_mem_suffix suffix _ cd.head_mem⟩
            exact cb.result_of_trigger_introducing_functional_term_occurs_in_chase head contra t_mem
          simp [h, this]
      rw [this]; apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set; exact f'_mem

  rcases cb.hom_for_node_extendable_to_result det (cd.mem_of_mem_suffix suffix _ (cd.next_mem_of_mem _ next_mem)) hom with ⟨ext, same_as_before, ext_hom⟩
  exists ext
  constructor
  . exact ext_hom
  . rcases altMatch with ⟨h_alt_hom, same_on_frontier, n, n_mem, n_not_mem_mapped⟩
    exists n
    rw [same_as_before n (by
      apply FactSet.terms_subset_of_subset (next.facts_contain_origin_result (next.origin.get (cd.isSome_origin_next next_mem)) (by simp))
      rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_head_iff]
      apply Or.inr; apply Or.inr; exact n_mem)]
    have : ¬ n ∈ ts := by
      intro contra; rw [eq_ts] at contra
      apply (cd.active_trigger_origin_next next_mem).right
      apply obs.contains_trg_result_implies_cond
      let head : cb.Node := ⟨cd.head, ChaseDerivation.mem_of_mem_suffix suffix _ cd.head_mem⟩
      exact cb.result_of_trigger_introducing_functional_term_occurs_in_chase head contra n_mem
    simp only [h, this, ↓reduceIte]
    intro contra
    apply n_not_mem_mapped
    rw [List.mem_map]
    exists n

/-- This is more of a lemma quite technical unfortunately. Take a `ChaseBranch`, a `FactSet` and a homomorphism $h$ from the chase result into the fact set that is at the same time an endomorphism on the fact set. If there is a term $t$ in the chase result such that no non-zero repetition of $h$ maps $t$ to itself, then the chase branch must have an alternative match for the fact set. Intuitively this is because $t$ is apparently a redundant term. -/
theorem altMatch_of_some_not_reaches_self (cb : ChaseBranch obs kb) (fs : FactSet sig) (h : GroundTermMapping sig)
    (hom_res : h.isHomomorphism cb.result fs) (hom_fs : h.isHomomorphism fs fs)
    (t : GroundTerm sig) (t_mem : t ∈ cb.result.terms) (t_not_reaches_self : ∀ j, 1 ≤ j -> (h.repeat_hom j) t ≠ t) :
    cb.has_alt_match_for_fs fs := by

  let term_property (ts : Set (GroundTerm sig)) (t : GroundTerm sig) := ∀ j, 1 ≤ j -> (h.repeat_hom j) t ≠ t
  let node_property (node : cb.Node) := ∃ t, t ∈ node.val.facts.terms ∧ term_property node.val.facts.terms t

  have : ∃ node, node_property node ∧ ∀ node2, node2 ≺ node -> ¬ node_property node2 := by
    rcases t_mem with ⟨f, f_mem, t_mem⟩
    rcases f_mem with ⟨node, node_mem, f_mem⟩
    apply ChaseDerivation.prop_for_node_has_minimal_such_node node_property ⟨node, node_mem⟩
    unfold node_property
    exists t
    constructor
    . exists f
    . exact t_not_reaches_self
  rcases this with ⟨node, prop_node, smallest⟩

  cases cb.mem_iff_eq_head_or_mem_tail.mp node.property with
  | inl eq_head =>
    apply False.elim
    rcases prop_node with ⟨t, t_mem, prop_t⟩
    specialize prop_t 1 (by simp)
    simp only [GroundTermMapping.repeat_hom, Function.comp_id] at prop_t
    cases t with
    | const c => apply prop_t; exact hom_fs.left
    | func func ts arity_ok =>
      have isFunctionFree := kb.db.toFactSet.property.right
      simp only [eq_head, cb.database_first'] at t_mem
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      specialize isFunctionFree _ f_mem _ t_mem
      rcases isFunctionFree with ⟨_, contra⟩
      simp [GroundTerm.func, GroundTerm.const] at contra
  | inr mem_tail =>
    rcases mem_tail with ⟨next_some, mem_tail⟩; rw [cb.mem_tail_iff] at mem_tail; rcases mem_tail with ⟨cd2, suffix, next_eq⟩
    exists cd2; simp only [suffix, true_and]

    specialize smallest ⟨cd2.head, by apply cd2.mem_of_mem_suffix suffix; exact cd2.head_mem⟩ (by
      have : ⟨cd2.head, cd2.head_mem⟩ ≺ ⟨node.val, cd2.next_mem_of_mem _ next_eq⟩ := cd2.head_strict_prec_next next_eq
      exact ChaseDerivation.strict_predecessor_of_suffix suffix this)
    simp only [node_property, term_property, not_exists, not_and, Classical.not_forall, ne_eq, Decidable.not_not] at smallest

    have : ∃ l, 1 ≤ l ∧ ∀ s, s ∈ cd2.head.facts.terms -> (h.repeat_hom l) s = s := by
      have head_finite := cb.facts_finite_of_mem ⟨cd2.head, by apply cd2.mem_of_mem_suffix suffix; exact cd2.head_mem⟩
      have l_terms_finite := cd2.head.facts.terms_finite_of_finite head_finite
      rcases l_terms_finite with ⟨l_terms, _, l_terms_eq⟩
      rcases h.repeat_globally_of_each_repeats l_terms (by
        intro s s_mem; rw [l_terms_eq] at s_mem
        rcases smallest s s_mem with ⟨l, l_le, eq⟩
        exists l) with ⟨l, l_le, aux⟩
      exists l
      constructor
      . exact l_le
      . intro s s_mem
        rw [← l_terms_eq] at s_mem
        apply aux
        exact s_mem

    rcases this with ⟨l, l_le, hom_id⟩

    have prop_node : ∃ t, t ∈ node.val.facts.terms ∧ ∃ k, ∀ j, k ≤ j -> ∀ s, s ∈ node.val.facts.terms -> (h.repeat_hom j) s ≠ t := by
      apply Classical.byContradiction
      intro contra
      simp at contra
      have node_finite := cb.facts_finite_of_mem node
      have l_terms_finite := node.val.facts.terms_finite_of_finite node_finite
      rcases l_terms_finite with ⟨l_terms, l_terms_nodup, l_terms_eq⟩
      have reaches_self := h.repeat_each_reaches_self_of_each_reachable l_terms (by
        intro t t_mem
        rw [l_terms_eq] at t_mem
        specialize contra t _ t_mem 1
        rcases contra with ⟨k, k_le, s, s_arity_ok, s_mem, s_eq⟩
        exists k
        constructor
        . exact k_le
        . exists ⟨s, s_arity_ok⟩
          rw [l_terms_eq]
          constructor
          . exact s_mem
          . exact s_eq
      )
      rcases prop_node with ⟨t, t_mem, prop_step⟩
      specialize reaches_self t (by rw [l_terms_eq]; exact t_mem)
      rcases reaches_self with ⟨l, l_le, reaches_self⟩
      apply prop_step l
      . exact l_le
      . exact reaches_self

    rcases prop_node with ⟨t, t_mem, k, prop_node⟩

    exists (h.repeat_hom ((k + 1) * l)) -- we just need a multiple of l >= k
    have hom_res' : (h.repeat_hom ((k + 1) * l)).isHomomorphism cb.result fs := by
      have : (k + 1) * l = ((k + 1) * l - 1) + 1 := by
        rw [Nat.sub_one_add_one]
        apply Nat.mul_ne_zero
        . simp
        . apply Nat.ne_zero_of_lt; apply Nat.lt_of_succ_le; exact l_le
      have : h.repeat_hom ((k + 1) * l) = h.repeat_hom (((k + 1) * l) - 1) ∘ h := by
        apply funext
        intro t
        simp
        have eq : h t = (h.repeat_hom 1) t := by simp [GroundTermMapping.repeat_hom]
        rw [eq, ← h.repeat_hom_add]
        rw [← this]
      rw [this]
      apply GroundTermMapping.isHomomorphism_compose h _ cb.result fs fs
      . exact hom_res
      . apply h.repeat_hom_isHomomorphism; exact hom_fs
    exists node.val, next_eq
    constructor
    . constructor
      . exact hom_res'.left
      . have eq_origin : node.val.origin = some (node.val.origin.get (cd2.isSome_origin_next next_eq)) := by simp
        have origin_res_in_facts := node.val.facts_contain_origin_result _ eq_origin
        apply Set.subset_trans (b := (h.repeat_hom ((k + 1) * l)).applyFactSet node.val.facts)
        . exact ((h.repeat_hom ((k + 1) * l)).apply_generalized_atom_set_subset_of_subset _ _ origin_res_in_facts)
        . apply Set.subset_trans (b := (h.repeat_hom ((k + 1) * l)).applyFactSet cb.result)
          . apply TermMapping.apply_generalized_atom_set_subset_of_subset
            apply cb.facts_node_subset_result
            exact node.property
          . apply hom_res'.right
    constructor
    . intro t t_mem
      rw [Nat.mul_comm]
      apply h.repeat_hom_cycle_mul
      apply hom_id
      apply FactSet.terms_subset_of_subset (cd2.active_trigger_origin_next next_eq).left
      rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
      apply Or.inr
      rw [List.mem_map] at t_mem
      rcases t_mem with ⟨v, v_mem, t_mem⟩
      exists v; constructor
      . apply Rule.frontier_subset_vars_body; exact v_mem
      . exact t_mem
    . exists t
      constructor
      . have t_mem' := t_mem
        rw [cd2.facts_next next_eq, FactSet.terms_union] at t_mem
        have not_mem_head : ¬ t ∈ cd2.head.facts.terms := by
          intro t_mem
          apply prop_node ((k + 1) * l) _ t
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          . exact t_mem'
          . rw [Nat.mul_comm]; apply h.repeat_hom_cycle_mul; apply hom_id; exact t_mem
          . apply Nat.le_trans; apply Nat.le_succ; apply Nat.le_mul_of_pos_right; apply Nat.lt_of_succ_le; exact l_le
        cases t_mem with
        | inl t_mem => apply False.elim; apply not_mem_head; exact t_mem
        | inr t_mem =>
          rw [FactSet.mem_terms_toSet] at t_mem
          simp only [ChaseNode.origin_result, PreTrigger.mem_terms_mapped_head_iff] at t_mem
          cases t_mem with
          | inl t_mem =>
            rcases t_mem with ⟨c, c_mem, t_mem⟩
            apply False.elim
            apply prop_node k (by simp) t t_mem'
            rw [← t_mem]
            exact (h.repeat_hom_isHomomorphism fs hom_fs k).left
          | inr t_mem =>
          cases t_mem with
          | inl t_mem =>
            apply False.elim
            apply not_mem_head
            apply FactSet.terms_subset_of_subset (cd2.active_trigger_origin_next next_eq).left
            rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]; apply Or.inr
            rw [List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
            exists v; simp only [t_mem, and_true]
            apply Rule.frontier_subset_vars_body
            rw [Rule.mem_frontier_iff_mem_frontier_for_head]
            exact ⟨_, v_mem⟩
          | inr t_mem => exact t_mem
      . intro t_mem; rw [List.mem_map] at t_mem; rcases t_mem with ⟨s, s_mem, t_eq⟩
        apply prop_node ((k + 1) * l) _ s
        . rw [cd2.facts_next next_eq, FactSet.terms_union]; apply Or.inr
          rw [FactSet.mem_terms_toSet]
          simp only [ChaseNode.origin_result, PreTrigger.mem_terms_mapped_head_iff]
          apply Or.inr; apply Or.inr
          exact s_mem
        . exact t_eq
        . apply Nat.le_trans; apply Nat.le_succ; apply Nat.le_mul_of_pos_right; apply Nat.lt_of_succ_le; exact l_le

/-- For a `ChaseBranch` without alternative match, every endomorphism on the result is surjective. This is shown by contradiction using `altMatch_of_some_not_reaches_self`. -/
theorem every_endo_surjective_of_noAltMatch (cb : ChaseBranch obs kb) : ¬ cb.has_alt_match -> ∀ (h : GroundTermMapping sig),
    h.isHomomorphism cb.result cb.result -> h.surjective_for_domain_and_image_set cb.result.terms cb.result.terms := by
  intro noAltMatch h endo
  apply Classical.byContradiction
  intro contra
  unfold Function.surjective_for_domain_and_image_set at contra
  simp at contra
  rcases contra with ⟨t, t_arity_ok, t_mem, contra⟩

  apply noAltMatch
  apply cb.altMatch_of_some_not_reaches_self cb.result h endo endo ⟨t, t_arity_ok⟩ t_mem

  intro j j_le eq
  apply contra ((h.repeat_hom (j-1)) ⟨t, t_arity_ok⟩)
  . have hom := h.repeat_hom_isHomomorphism cb.result endo (j-1)
    rcases t_mem with ⟨f, f_mem, t_mem⟩
    exists (h.repeat_hom (j-1)).applyFact f
    constructor
    . apply hom.right
      apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
      exact f_mem
    . simp only [GroundTermMapping.applyFact, TermMapping.apply_generalized_atom, List.mem_map]
      exists ⟨t, t_arity_ok⟩
  . have repeat_add := h.repeat_hom_add 1 (j - 1) ⟨t, t_arity_ok⟩
    conv at repeat_add => right; simp [GroundTermMapping.repeat_hom]
    rw [← repeat_add]
    rw [Nat.add_comm, Nat.sub_one_add_one (Nat.ne_zero_of_lt (Nat.lt_of_succ_le j_le))]
    exact eq

/-- From `result_isWeakCore_of_noAltMatch` and `every_endo_surjective_of_noAltMatch`, we get that the result of a `ChaseBranch` without alternative matches is a strong core. -/
theorem result_isStrongCore_of_noAltMatch (cb : ChaseBranch obs kb) (det : kb.isDeterministic) : ¬ cb.has_alt_match -> cb.result.isStrongCore := by
  unfold FactSet.isStrongCore
  intro noAltMatch h endo
  have ⟨strong, inj⟩ := cb.result_isWeakCore_of_noAltMatch det noAltMatch h endo
  constructor
  . exact strong
  constructor
  . exact inj
  . apply every_endo_surjective_of_noAltMatch
    . exact noAltMatch
    . exact endo

/-!
The following is a quite technical result, which is designed to act as a lemma for further theorems that we did not formalize yet. To give a teaser, there are related to interleaving the restricted and core chase, basically using the restricted chase as long as alternative matches can be avoided and only in the end falling back to computing the rest with the core chase.

Take a `ChaseBranch` and a `FactSet` $F$ that is a superset of the chase result. Furthermore assume that the chase branch has no alternative match in $F$.
For every homomorphic subset of $F$, we know that it must still be a superset of the chase result.
On a higher level, imagine that $F$ is some fact set that might be computed using a core chase that started on the previous chase result.
Then by this result we know that the core computation of the core chase will never remove a term that was introduced by our initial restricted chase branch.
Part of the proof again uses `altMatch_of_some_not_reaches_self`.

Personal note: When I was thinking about this theorem on paper, I ended up confusing myself again and again doubting if this even holds.
Finally, I had enough of it and invested (a lot of) time to formalize this in Lean and get some peace of mind.
Of course it still remains to show the theorems where this would actually be used.
-/

theorem core_superset_of_chase_result
    (cb : ChaseBranch obs kb) (fs : FactSet sig) (fs_super : cb.result ⊆ fs) (noAltMatch : ¬ cb.has_alt_match_for_fs fs) :
    ∀ (sub_fs : FactSet sig), sub_fs.homSubset fs -> cb.result ⊆ sub_fs := by
  intro sub_fs sub_fs_sub
  rcases sub_fs_sub with ⟨sub_fs_sub, h, hom⟩

  apply Classical.byContradiction
  intro not_subsumes

  have hom_fs : h.isHomomorphism fs fs := by
    constructor
    . exact hom.left
    . exact Set.subset_trans hom.right sub_fs_sub

  have hom_sub_fs : h.isHomomorphism sub_fs sub_fs := by
    constructor
    . exact hom.left
    . apply Set.subset_trans _ hom.right
      apply TermMapping.apply_generalized_atom_set_subset_of_subset; exact sub_fs_sub

  have : ∃ t, t ∈ cb.result.terms ∧ ∀ j, 1 ≤ j -> (h.repeat_hom j) t ≠ t := by
    apply Classical.byContradiction
    intro contra
    simp at contra
    apply not_subsumes

    intro f f_mem
    rcases f_mem with ⟨node, node_mem, f_mem⟩

    have : ∃ j, 1 ≤ j ∧ ∀ t, t ∈ node.facts.terms -> (h.repeat_hom j) t = t := by
      have terms_finite := node.facts.terms_finite_of_finite (cb.facts_finite_of_mem ⟨node, node_mem⟩)
      rcases terms_finite with ⟨terms, terms_nodup, terms_eq⟩
      have repeats_globally := h.repeat_globally_of_each_repeats terms (by
        intro s s_mem
        apply contra
        rw [terms_eq] at s_mem
        rcases s_mem with ⟨f, f_mem, s_mem⟩
        exists f; constructor
        . exists node
        . exact s_mem
      )
      rcases repeats_globally with ⟨j, j_le, repeats_globally⟩
      exists j
      constructor
      . exact j_le
      . intro t t_mem
        apply repeats_globally
        rw [terms_eq]
        exact t_mem
    rcases this with ⟨j, j_le, each_repeats⟩

    have : (h.repeat_hom j).applyFact f = f := by
      simp [GroundTermMapping.applyFact]
      have : f.terms.map (h.repeat_hom j) = f.terms := by
        apply List.map_id_of_id_on_all_mem
        intro t t_mem
        apply each_repeats
        exists f
      simp only [TermMapping.apply_generalized_atom, this]
    rw [← this]
    have : (h.repeat_hom j).isHomomorphism fs sub_fs := by
      have : h.repeat_hom j = h.repeat_hom (j-1) ∘ h := by
        apply funext
        intro t
        simp
        have : h t = h.repeat_hom 1 t := by simp [GroundTermMapping.repeat_hom]
        rw [this, ← h.repeat_hom_add]
        rw [Nat.sub_one_add_one (Nat.ne_zero_of_lt (Nat.lt_of_succ_le j_le))]
      rw [this]
      apply GroundTermMapping.isHomomorphism_compose h (h.repeat_hom (j-1)) fs sub_fs sub_fs
      . exact hom
      . apply h.repeat_hom_isHomomorphism; exact hom_sub_fs
    apply this.right
    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
    apply fs_super
    exists node

  rcases this with ⟨t, t_mem, not_repeats⟩

  apply noAltMatch
  apply cb.altMatch_of_some_not_reaches_self fs h _ _ t t_mem
  . exact not_repeats
  . constructor
    . exact hom.left
    . apply Set.subset_trans (b := h.applyFactSet fs)
      . apply TermMapping.apply_generalized_atom_set_subset_of_subset
        exact fs_super
      . apply hom_fs.right
  . exact hom_fs

end ChaseBranch

