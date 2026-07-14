/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import BasicLeanDatastructures.Function.InjectiveSurjective
public import BasicLeanDatastructures.Function.Repetition
public import BasicLeanDatastructures.List.EraseDupsKeepRight
public import ExistentialRules.Models.Basic

/-!
# Cores

In this file, we define cores of fact sets. Namely, we define `FactSet.isWeakCore` and `FactSet.isStrongCore`.
`FactSet`s that are models and cores are interesting since there are (intuitively speaking) the smallest possible models.
Under certain condition, the chase is able to produce a core directly, which is very desirable since the result of the chase is also always a universal model.
But this is discussed in other files. Here, we are only concerned with the definition of cores on `FactSet`s and some of their properties.
-/

public section

namespace GroundTermMapping

/-!
## Strong GroundTermMappings (and Homomorphisms)

Intuitively, a homomorphism is `strong` if it not only retains membership but also non-membership.
We define being `strong` as a standalone property for `GroundTermMapping`s
without requiring any additional properties for the underlying `GroundTermMapping`.
-/

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

/-- A `GroundTermMapping` is strong for `FactSet`s $A$ and $B$ if each element not in $A$, its mapping is not in $B$. However, we only demand this for elements that only feature terms from a given domain because we do not want to care about the mapping of terms outside the domain. -/
@[expose]
def strong (h : GroundTermMapping sig) (domain : Set (GroundTerm sig)) (A B : FactSet sig) : Prop :=
  ∀ (e : Fact sig), (∀ t, t ∈ e.terms -> t ∈ domain) -> ¬ e ∈ A -> ¬ (h.applyFact e) ∈ B

/-- If the composition of two mappings is strong from $A$ to $C$ and the second mapping is a homomorphism from $B$ to $C$, then the first mapping is strong from $A$ to $B$. -/
@[grind ->]
theorem strong_of_compose_strong (g h : GroundTermMapping sig) (domain : Set (GroundTerm sig)) (A B C : FactSet sig) :
    h.isHomomorphism B C -> GroundTermMapping.strong (h ∘ g) domain A C -> g.strong domain A B := by
  intro h_hom compose_strong
  intro e e_dom e_not_mem_a e_mem_b
  apply compose_strong e
  . exact e_dom
  . exact e_not_mem_a
  . apply h_hom.right (GroundTermMapping.applyFact (h ∘ g) e)
    rw [GroundTermMapping.mem_applyFactSet]
    exists (g.applyFact e)
    constructor
    . exact e_mem_b
    . simp

end GroundTermMapping

namespace GroundTermMapping

/-!
## Repetition of GroundTermMappings (and Homomorphisms)

Since homomorphisms are functions over terms, we can repeat them.
Here, we show some nice properties of repeated homomorphisms and endomorphisms in particular.
For example, we prove that a repeated endomorphisms is again an endomorphisms.
-/

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- Repeating a mapping retains the `GroundTermMapping.isIdOnConstants` property. -/
theorem repeat_id_on_const {h : GroundTermMapping sig} (idOnConst : h.isIdOnConstants) : ∀ i, GroundTermMapping.isIdOnConstants (h.repeat_fun i) := by
  intro i
  fun_induction h.repeat_fun i with
  | case1 => intro c; simp
  | case2 i ih => intro c; rw [Function.comp_apply, ih, idOnConst]

variable [DecidableEq sig.P]

/-- Repeating a mapping retains the `GroundTermMapping.isHomomorphism` property at least for endomorphisms. -/
theorem repeat_isHomomorphism {h : GroundTermMapping sig} {fs : FactSet sig} (hom : h.isHomomorphism fs fs) :
    ∀ i, GroundTermMapping.isHomomorphism (h.repeat_fun i) fs fs := by
  intro i
  constructor
  . exact repeat_id_on_const hom.left i
  . fun_induction h.repeat_fun i with
    | case1 =>
      intro f f_mem
      rw [GroundTermMapping.mem_applyFactSet] at f_mem
      rcases f_mem with ⟨f', f'_mem, f_eq⟩
      suffices f = f' by rw [this]; exact f'_mem
      rw [f_eq]
      unfold GroundTermMapping.applyFact
      unfold TermMapping.apply_generalized_atom
      simp
    | case2 i ih =>
      unfold applyFactSet
      rw [TermMapping.apply_generalized_atom_set_compose, Function.comp_apply]
      intro f f_mem
      apply hom.right
      apply h.apply_generalized_atom_set_subset_of_subset
      . exact ih
      . exact f_mem

end GroundTermMapping

namespace FactSet

/-!
## Cores Definitions and some of their Properties

Here, we finally define `isWeakCore` and `isStrongCore` and show some of their relations and additional properties. This also involves some more theorems about homomorphisms.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `FactSet` is a weak core if every endomorphisms on the fact set is strong and injective. -/
@[expose]
def isWeakCore (fs : FactSet sig) : Prop :=
  ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs.terms fs fs ∧ h.injectiveSet fs.terms

/-- A `FactSet` is a strong core if every endomorphisms on the fact set is strong, injective, and surjective. (By definition, every strong core is a weak core.) -/
@[expose]
def isStrongCore (fs : FactSet sig) : Prop :=
  ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs.terms fs fs ∧ h.injectiveSet fs.terms ∧ h.surjectiveSet fs.terms fs.terms

/-- We say that a fact set $C$ is a homomorphic subset of another fact set $F$ if $C$ is a subset of $F$ and there is a homomorphism from $F$ to $C$. -/
@[expose]
def homSubset (c fs : FactSet sig) : Prop := c ⊆ fs ∧ (∃ (h : GroundTermMapping sig), h.isHomomorphism fs c)

/-- For a homomorphism on a finite fact set, injectivity implies surjectivity. -/
@[grind ->]
theorem hom_surjective_of_finite_of_injective (fs : FactSet sig) (finite : fs.finite) :
    ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.injectiveSet fs.terms ->
    h.surjectiveSet fs.terms fs.terms := by
  rcases finite with ⟨l, finite⟩
  intro h isHom inj

  let terms_list := (l.map GeneralizedAtom.terms).flatten.eraseDupsKeepRight
  have nodup_terms_list : terms_list.Nodup := by apply List.nodup_eraseDupsKeepRight
  have mem_terms_list : ∀ e, e ∈ fs.terms ↔ e ∈ terms_list := by
    simp only [terms_list]
    intro e
    rw [List.mem_eraseDupsKeepRight]
    unfold FactSet.terms
    simp only [List.mem_flatten, List.mem_map]
    constructor
    . intro h
      rcases h with ⟨f, f_mem, e_mem⟩
      exists f.terms
      constructor
      . exists f; rw [finite.right f]; constructor; exact f_mem; rfl
      . exact e_mem
    . intro h
      rcases h with ⟨ts, h, ts_mem⟩
      rcases h with ⟨f, f_mem, eq⟩
      exists f
      rw [eq]
      rw [← finite.right f]
      constructor <;> assumption
  have closed : h.closedList terms_list := by
    simp only [terms_list]
    intro e
    rw [List.mem_eraseDupsKeepRight]
    rw [List.mem_eraseDupsKeepRight]
    simp only [List.mem_flatten, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro f f_mem e_in_f
    let f' := h.applyFact f
    have f'_mem : f' ∈ fs := by
      apply isHom.right
      rw [GroundTermMapping.mem_applyFactSet]
      exists f
      constructor
      . rw [finite.right] at f_mem
        exact f_mem
      . rfl
    exists f'.terms
    constructor
    . exists f'
      constructor
      . rw [finite.right]; exact f'_mem
      . rfl
    . simp only [f', TermMapping.apply_generalized_atom]
      rw [List.mem_map]
      exists e

  rw [Function.surjective_set_list_equiv mem_terms_list mem_terms_list]
  rw [← Function.injective_iff_surjective_of_nodup_of_closed nodup_terms_list closed]
  rw [← Function.injective_set_list_equiv mem_terms_list]
  exact inj

/-- For a homomorphism on a finite fact set, injectivity implies that the homomorphisms is also strong. -/
@[grind ->]
theorem hom_strong_of_finite_of_injective (fs : FactSet sig) (finite : fs.finite) :
    ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.injectiveSet fs.terms -> h.strong fs.terms fs fs := by
  intro h isHom inj

  intro f ts_mem f_not_mem apply_mem
  apply f_not_mem

  have surj := fs.hom_surjective_of_finite_of_injective finite h isHom inj

  have terms_finite := fs.terms_finite_of_finite finite
  rcases terms_finite with ⟨terms, nodup, equiv⟩
  have equiv' : ∀ e, e ∈ fs.terms ↔ e ∈ terms := by intro _; rw [equiv]

  rw [h.surjective_set_list_equiv equiv' equiv'] at surj
  have ex_inv := h.exists_repetition_that_is_inverse_of_surj terms surj
  rcases ex_inv with ⟨k, inv⟩
  have inv_hom : GroundTermMapping.isHomomorphism (h.repeat_fun k) fs fs := h.repeat_isHomomorphism isHom k

  suffices GroundTermMapping.applyFact (h.repeat_fun k) (h.applyFact f) = f by
    rw [← this]; apply inv_hom.right; apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set; exact apply_mem
  unfold GroundTermMapping.applyFact
  rw [← TermMapping.apply_generalized_atom_compose']
  apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
  intro t t_mem
  rw [Function.comp_apply]
  apply inv
  rw [equiv]
  apply ts_mem
  exact t_mem

/-- For finite fact sets, `isWeakCore` implies `isStrongCore`. That means that `isWeakCore` and `isStrongCore` are equivalent on finite fact sets. -/
@[grind ->]
theorem isStrongCore_of_isWeakCore_of_finite (fs : FactSet sig) (weakCore : fs.isWeakCore) (finite : fs.finite) : fs.isStrongCore := by
  rcases finite with ⟨l, finite⟩
  unfold isStrongCore
  intro h isHom
  specialize weakCore h isHom
  rcases weakCore with ⟨strong, injective⟩
  constructor
  . exact strong
  constructor
  . exact injective
  . apply hom_surjective_of_finite_of_injective
    . exists l
    . exact isHom
    . exact injective

/-- Each `homSubset` of a finite core is equal to that core. -/
theorem homSubset_eq_self_of_isWeakCore_of_finite {fs1 fs2 : FactSet sig} (homSub : fs1.homSubset fs2) (core : fs2.isWeakCore) (fin : fs2.finite) : fs1 = fs2 := by
  apply Set.ext; intro f; constructor; exact homSub.left f
  intro f_mem
  have strong_core := fs2.isStrongCore_of_isWeakCore_of_finite core fin
  rcases homSub.right with ⟨h, hom⟩
  have h_endo : h.isHomomorphism fs2 fs2 := by constructor; exact hom.left; exact Set.subset_trans hom.right homSub.left
  have h_endo' : h.isHomomorphism fs1 fs1 := by
    constructor; exact hom.left; apply Set.subset_trans _ hom.right; apply TermMapping.apply_generalized_atom_set_subset_of_subset; exact homSub.left
  have h_surj := (strong_core h h_endo).right.right
  rcases fs2.terms_finite_of_finite fin with ⟨terms, _, terms_eq⟩
  have terms_eq : ∀ t, t ∈ fs2.terms ↔ t ∈ terms := by intro _; rw [terms_eq]
  rw [Function.surjective_set_list_equiv terms_eq terms_eq] at h_surj
  rcases h.exists_repetition_that_is_inverse_of_surj terms h_surj with ⟨k, inv⟩
  suffices GroundTermMapping.applyFact (h.repeat_fun k ∘ h) f = f by
    have compose_hom : GroundTermMapping.isHomomorphism (h.repeat_fun k ∘ h) fs2 fs1 := by
      apply GroundTermMapping.isHomomorphism_compose; exact hom; apply GroundTermMapping.repeat_isHomomorphism; exact h_endo'
    apply compose_hom.right; rw [← this]; apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set; exact f_mem
  apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
  intro t t_mem
  apply inv
  rw [← terms_eq]
  exists f

/-- Given two fact sets A,B of which one is a weak and one is a strong core, if there are homomorphisms from A to B and B to A, then there exists an isomorphism from A to B, i.e. a strong homomorphisms that is injective and surjective. -/
theorem every_weakCore_isomorphic_to_strongCore_of_hom_both_ways
    (sc : FactSet sig) (sc_strong : sc.isStrongCore)
    (wc : FactSet sig) (wc_weak : wc.isWeakCore)
    (h_sc_wc h_wc_sc : GroundTermMapping sig) (h_sc_wc_hom : h_sc_wc.isHomomorphism sc wc) (h_wc_sc_hom : h_wc_sc.isHomomorphism wc sc) :
    ∃ (iso : GroundTermMapping sig), iso.isHomomorphism wc sc ∧ iso.strong wc.terms wc sc ∧ iso.injectiveSet wc.terms ∧ iso.surjectiveSet wc.terms sc.terms := by

  specialize wc_weak (h_sc_wc ∘ h_wc_sc) (by
    apply GroundTermMapping.isHomomorphism_compose
    . exact h_wc_sc_hom
    . exact h_sc_wc_hom
  )

  specialize sc_strong (h_wc_sc ∘ h_sc_wc) (by
    apply GroundTermMapping.isHomomorphism_compose
    . exact h_sc_wc_hom
    . exact h_wc_sc_hom
  )

  exists h_wc_sc
  constructor
  . exact h_wc_sc_hom
  constructor
  -- strong since h_sc_wc ∘ h_wc_sc is strong
  . apply GroundTermMapping.strong_of_compose_strong h_wc_sc h_sc_wc wc.terms wc sc wc h_sc_wc_hom
    exact wc_weak.left
  constructor
  -- injective since h_sc_wc ∘ h_wc_sc is injective
  . exact Function.injectiveSet_of_injectiveSet_compose wc_weak.right
  -- surjective since h_wc_sc ∘ h_sc_wc is surjective
  . apply Function.surjectiveSet_of_surjectiveSet_of_superset
    . exact Function.surjectiveSet_of_surjectiveSet_compose sc_strong.right.right
    . intro t t_mem_image
      simp only [Function.imageSet, Set.mem_map] at t_mem_image
      rcases t_mem_image with ⟨arg, arg_mem, arg_eq⟩
      rcases arg_mem with ⟨f, f_mem, f_eq⟩
      exists (h_sc_wc.applyFact f)
      constructor
      . apply h_sc_wc_hom.right
        rw [GroundTermMapping.mem_applyFactSet]
        exists f
      . unfold GroundTermMapping.applyFact
        unfold TermMapping.apply_generalized_atom
        rw [List.mem_map]
        exists arg

/-- Strong cores of fact sets are unique up to isomorphism. That is, consider a fact set $F$. A strong core $C$ for $F$ is a strong core that is also a homomorphic subset of $F$. Now every (other) homomorphic subset $C'$ of $F$ that is at least a weak core has an isomorphism into $C$. -/
theorem strongCore_unique_up_to_isomorphism_with_respect_to_weak_cores
    (fs : FactSet sig)
    (sc : FactSet sig) (sub_sc : sc.homSubset fs) (sc_strong : sc.isStrongCore)
    (wc : FactSet sig) (sub_wc : wc.homSubset fs) (wc_weak : wc.isWeakCore) :
    ∃ (iso : GroundTermMapping sig), iso.isHomomorphism wc sc ∧ iso.strong wc.terms wc sc ∧ iso.injectiveSet wc.terms ∧ iso.surjectiveSet wc.terms sc.terms := by

  rcases sub_sc with ⟨sub_sc, h_fs_sc, h_fs_sc_hom⟩
  rcases sub_wc with ⟨sub_wc, h_fs_wc, h_fs_wc_hom⟩

  have h_sc_wc_hom : h_fs_wc.isHomomorphism sc wc := by
    constructor
    . exact h_fs_wc_hom.left
    . apply Set.subset_trans (b := h_fs_wc.applyFactSet fs)
      . apply TermMapping.apply_generalized_atom_set_subset_of_subset
        exact sub_sc
      . exact h_fs_wc_hom.right

  have h_wc_sc_hom : h_fs_sc.isHomomorphism wc sc := by
    constructor
    . exact h_fs_sc_hom.left
    . apply Set.subset_trans (b := h_fs_sc.applyFactSet fs)
      . apply TermMapping.apply_generalized_atom_set_subset_of_subset
        exact sub_wc
      . exact h_fs_sc_hom.right

  exact every_weakCore_isomorphic_to_strongCore_of_hom_both_ways sc sc_strong wc wc_weak h_fs_wc h_fs_sc h_sc_wc_hom h_wc_sc_hom

/-- Consider a `KnowledgeBase` and a universal model of the KB that is a strong core. Then every (other) universal model that is at least a weak core, is isomorphism to the strong core. -/
theorem every_universal_weakCore_isomorphic_to_universal_strongCore
    {kb : KnowledgeBase sig}
    (sc : FactSet sig) (sc_universal : sc.universallyModelsKb kb) (sc_strong : sc.isStrongCore)
    (wc : FactSet sig) (wc_universal : wc.universallyModelsKb kb) (wc_weak : wc.isWeakCore) :
    ∃ (iso : GroundTermMapping sig), iso.isHomomorphism wc sc ∧ iso.strong wc.terms wc sc ∧ iso.injectiveSet wc.terms ∧ iso.surjectiveSet wc.terms sc.terms := by

  rcases sc_universal.right wc wc_universal.left with ⟨h_sc_wc, h_sc_wc_hom⟩
  rcases wc_universal.right sc sc_universal.left with ⟨h_wc_sc, h_wc_sc_hom⟩

  exact every_weakCore_isomorphic_to_strongCore_of_hom_both_ways sc sc_strong wc wc_weak h_sc_wc h_wc_sc h_sc_wc_hom h_wc_sc_hom

/-- Given a model of a `KnowledgeBase`, every strong core of the model is also a model. In general, this does *not* hold for weak cores (in the infinite setting). -/
theorem strong_core_of_model_is_model
    {kb : KnowledgeBase sig}
    (fs : FactSet sig) (fs_model : fs.modelsKb kb)
    (sc : FactSet sig) (sc_sub : sc.homSubset fs) (sc_strong : sc.isStrongCore) :
    sc.modelsKb kb := by

  rcases sc_sub with ⟨sc_sub, h_fs_sc, h_fs_sc_hom⟩

  have h_fs_sc_endo_sc : h_fs_sc.isHomomorphism sc sc := by
    constructor
    . exact h_fs_sc_hom.left
    . apply Set.subset_trans (b := h_fs_sc.applyFactSet fs)
      . apply TermMapping.apply_generalized_atom_set_subset_of_subset
        exact sc_sub
      . exact h_fs_sc_hom.right

  specialize sc_strong h_fs_sc h_fs_sc_endo_sc

  -- TODO: extract this into a general result; check which properties we really need and want here
  have ex_inv : ∃ (inv : GroundTermMapping sig), (∀ t, t ∈ sc.terms -> (h_fs_sc (inv t)) = t) ∧ inv.isHomomorphism sc sc := by
    let inv : GroundTermMapping sig := fun t =>
      have dev := Classical.propDecidable (t ∈ sc.terms)
      if t_mem : t ∈ sc.terms
      then
        Classical.choose (sc_strong.right.right t t_mem)
      else
        t

    have inv_id : (∀ t, t ∈ sc.terms -> (h_fs_sc (inv t)) = t) := by
      intro t t_mem
      unfold inv
      simp only [t_mem, ↓reduceDIte]
      have spec := Classical.choose_spec (sc_strong.right.right t t_mem)
      exact spec.right
    exists inv

    constructor
    . exact inv_id
    . constructor
      . intro c
        unfold inv
        cases Classical.em (GroundTerm.const c ∈ sc.terms) with
        | inr n_mem => simp [n_mem]
        | inl mem =>
          simp only [mem, ↓reduceDIte]
          have spec := Classical.choose_spec (sc_strong.right.right (GroundTerm.const c) mem)
          apply sc_strong.right.left
          . exact spec.left
          . exact mem
          . rw [spec.right, h_fs_sc_hom.left]
      . intro f f_mem
        rw [GroundTermMapping.mem_applyFactSet] at f_mem
        rcases f_mem with ⟨f', f'_mem, f_eq⟩
        have strong := sc_strong.left
        unfold GroundTermMapping.strong at strong
        apply Classical.byContradiction
        intro contra
        apply strong f
        . intro t t_mem
          rw [f_eq] at t_mem
          unfold GroundTermMapping.applyFact TermMapping.apply_generalized_atom at t_mem
          rw [List.mem_map] at t_mem
          rcases t_mem with ⟨t', t'_mem, t_eq⟩
          have t'_mem : t' ∈ sc.terms := by exists f'
          have spec := Classical.choose_spec (sc_strong.right.right t' t'_mem)
          rw [← t_eq]
          unfold inv
          simp only [t'_mem, ↓reduceDIte]
          exact spec.left
        . exact contra
        . rw [f_eq]
          unfold GroundTermMapping.applyFact
          rw [← TermMapping.apply_generalized_atom_compose']
          have : TermMapping.apply_generalized_atom (h_fs_sc ∘ inv) f' = f' := by
            apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
            intro t t_mem
            rw [Function.comp_apply, inv_id]
            exists f'
          rw [this]
          exact f'_mem
  rcases ex_inv with ⟨inv, inv_id, inv_hom⟩

  constructor
  . intro f f_mem
    have : h_fs_sc.applyFact f = f := by
      have prop := kb.db.toFactSet.property.right
      unfold FactSet.isFunctionFree at prop
      unfold Fact.isFunctionFree at prop
      specialize prop f f_mem
      apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
      intro t t_mem
      rcases (prop t t_mem) with ⟨c, t_eq⟩
      rw [t_eq]
      exact h_fs_sc_hom.left
    rw [← this]
    apply h_fs_sc_hom.right
    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
    apply fs_model.left
    exact f_mem
  . intro r r_mem
    intro subs loaded

    have fs_models_rule := fs_model.right r r_mem (inv ∘ subs)
    specialize fs_models_rule (by
      apply Set.subset_trans (b := inv.applyFactSet sc)
      . intro f f_mem
        unfold GroundSubstitution.apply_function_free_conj at f_mem
        unfold TermMapping.apply_generalized_atom_list at f_mem
        rw [List.mem_toSet, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_eq⟩
        rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants _ _ inv_hom.left] at f_eq
        rw [← f_eq]
        apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
        apply loaded
        unfold GroundSubstitution.apply_function_free_conj
        unfold TermMapping.apply_generalized_atom_list
        rw [List.mem_toSet, List.mem_map]
        exists a
      . apply Set.subset_trans (b := sc)
        . exact inv_hom.right
        . exact sc_sub
    )
    rcases fs_models_rule with ⟨i, subs', frontier_mapping, sub_mapping⟩

    exists i
    exists (h_fs_sc ∘ subs')
    constructor
    . intro v v_mem
      rw [Function.comp_apply]
      rw [frontier_mapping v v_mem]
      rw [Function.comp_apply]
      rw [inv_id _ (by
        unfold Rule.frontier at v_mem
        rw [List.mem_filter] at v_mem
        have v_mem := v_mem.left
        rw [FunctionFreeConjunction.mem_vars] at v_mem
        rcases v_mem with ⟨a, a_mem, v_mem⟩
        exists subs.apply_function_free_atom a
        constructor
        . apply loaded
          unfold GroundSubstitution.apply_function_free_conj
          unfold TermMapping.apply_generalized_atom_list
          rw [List.mem_toSet, List.mem_map]
          exists a
        . unfold GroundSubstitution.apply_function_free_atom
          unfold TermMapping.apply_generalized_atom
          rw [List.mem_map]
          exists VarOrConst.var v
      )]
    . apply Set.subset_trans (b := h_fs_sc.applyFactSet fs)
      . intro f f_mem
        unfold GroundSubstitution.apply_function_free_conj at f_mem
        unfold TermMapping.apply_generalized_atom_list at f_mem
        rw [List.mem_toSet, List.mem_map] at f_mem
        rcases f_mem with ⟨a, a_mem, f_eq⟩
        rw [← GroundSubstitution.apply_function_free_atom.eq_def, GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants _ _ h_fs_sc_hom.left] at f_eq
        rw [← f_eq]
        apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
        apply sub_mapping
        unfold GroundSubstitution.apply_function_free_conj
        unfold TermMapping.apply_generalized_atom_list
        rw [List.mem_toSet, List.mem_map]
        exists a
      . exact h_fs_sc_hom.right

/-- Building on top of the previous theorem, a strong core of a universal model is not only a model but also universal. -/
theorem strong_core_of_universal_model_is_universal_model
    {kb : KnowledgeBase sig}
    (fs : FactSet sig) (fs_univ_model : fs.universallyModelsKb kb)
    (sc : FactSet sig) (sc_sub : sc.homSubset fs) (sc_strong : sc.isStrongCore) :
    sc.universallyModelsKb kb := by
  constructor
  . exact strong_core_of_model_is_model fs fs_univ_model.left sc sc_sub sc_strong
  . intro m m_model
    rcases fs_univ_model.right m m_model with ⟨h, h_hom⟩
    exists h
    constructor
    . exact h_hom.left
    . apply Set.subset_trans (b := h.applyFactSet fs)
      . apply TermMapping.apply_generalized_atom_set_subset_of_subset
        exact sc_sub.left
      . exact h_hom.right

end FactSet

