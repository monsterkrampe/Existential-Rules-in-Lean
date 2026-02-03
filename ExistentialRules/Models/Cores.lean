import ExistentialRules.Models.Basic

/-!
# Cores

In this file, we define cores of fact sets. Namely, we define `FactSet.isWeakCore` and `FactSet.isStrongCore`.
`FactSet`s that are models and cores are interesting since there are (intuitively speaking) the smallest possible models.
Under certain condition, the chase is able to produce a core directly, which is very desirable since the result of the chase is also always a universal model.
But this is discussed in other files. Here, we are only concerned with the definition of cores on `FactSet`s and some of their properties.
-/

/-!
## Some Auxiliary Definitions and Theorems on Lists and Functions

Before we can go into the actual definitions, we need a lot of machinery, mainly about functions to be able to state properties like injectivity and surjectivity possibly only about a list of set of elements and not the whole domain of the function.
-/

namespace List

/-!
### Auxiliary Theorems on Lists
-/

/-- If a list is duplicate free and the sublist of another list, then the second list is at least as long as the first. -/
theorem length_le_of_nodup_of_all_mem [DecidableEq α] (as bs : List α) (nodup : as.Nodup) (all_mem : ∀ e, e ∈ as -> e ∈ bs) : as.length ≤ bs.length := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    let bs_without_a := bs.erase a
    simp only [nodup_cons] at nodup
    specialize ih
      bs_without_a
      nodup.right
      (by intro c c_mem; rw [List.mem_erase_of_ne]; apply all_mem; simp [c_mem]; intro contra; rw [contra] at c_mem; apply nodup.left; exact c_mem)
    rw [List.length_erase_of_mem (by apply all_mem; simp)] at ih
    rw [Nat.le_sub_one_iff_lt (by apply List.length_pos_of_mem; apply all_mem a; simp)] at ih
    apply Nat.succ_le_of_lt
    exact ih

/-- If a list is duplicate free and the sublist of another list that has the same length, then both lists have exactly the same elements. -/
theorem equiv_of_nodup_of_length_eq_of_all_mem [DecidableEq α] (as bs : List α) (nodup : as.Nodup) (eq_length : as.length = bs.length) (all_mem : ∀ e, e ∈ as -> e ∈ bs) : ∀ e, e ∈ as ↔ e ∈ bs := by
  intro e
  constructor
  . apply all_mem
  . intro mem_bs
    induction as generalizing bs e with
    | nil => cases bs; simp at mem_bs; simp at eq_length
    | cons a as ih =>
      let bs_without_a := bs.erase a
      simp only [nodup_cons] at nodup
      specialize ih
        bs_without_a
        nodup.right
        (by rw [List.length_erase_of_mem, ← eq_length]; simp; apply all_mem; simp)
        (by intro c c_mem; rw [List.mem_erase_of_ne]; apply all_mem; simp [c_mem]; intro contra; rw [contra] at c_mem; apply nodup.left; exact c_mem)
      cases Decidable.em (e = a) with
      | inl eq => simp [eq]
      | inr neq =>
        simp only [mem_cons]; apply Or.inr
        apply ih
        rw [List.mem_erase_of_ne]
        exact mem_bs
        exact neq

end List

namespace Function

/-!
### Injectivity and Surjectivity

We define what it means for a function to be injective or surjective restricted to a given domain and image, given as either a list or set.
Intuitively, results involving the list versions most likely have an implicit requirement for domain and image being finite whereas results stated for the set version do not have this requirement.

We found our more suitable than using `Function.Injective` and `Function.Sufjective` because this would require us to consider appropriate subtypes and also since there barely seem to be theorems in the standard library (outside Mathlib).
We might rework those definitions in the future though. I think a couple of (small) things can be cleaned up here but this is not the highest priprity.
Maybe this should even move to the BasicLeanDatastructures repo since there are really just general results over functions.
-/

/-- The image of a function for a given domain set. -/
def image_set (f : α -> β) (A : Set α) : Set β := A.map f

/-- A function is injective on a given domain set if for each two elements of the given domain, the mapping of both elements being the same implies the elements being the same. -/
def injective_for_domain_set (f : α -> β) (domain : Set α) : Prop := ∀ a a', a ∈ domain -> a' ∈ domain -> f a = f a' -> a = a'

/-- A function is surjective on a given domain set and image set if for each element of the image, there exists an element in the domain that maps to the desired image element. -/
def surjective_for_domain_and_image_set (f : α -> β) (domain : Set α) (image : Set β) : Prop := ∀ b, b ∈ image -> ∃ a, a ∈ domain ∧ f a = b

/-- The image of a function for a given domain list. -/
def image [DecidableEq β] (f : α -> β) (l : List α) : List β := (l.map f).eraseDupsKeepRight

/-- A function is injective on a given domain list if for each two elements of the given domain, the mapping of both elements being the same implies the elements being the same. -/
def injective_for_domain_list (f : α -> β) (domain : List α) : Prop := ∀ a a', a ∈ domain -> a' ∈ domain -> f a = f a' -> a = a'

/-- A function is surjective on a given domain list and image list if for each element of the image, there exists an element in the domain that maps to the desired image element. -/
def surjective_for_domain_and_image_list (f : α -> β) (domain : List α) (image : List β) : Prop := ∀ b, b ∈ image -> ∃ a, a ∈ domain ∧ f a = b

/-- If the composition of two mappings is injective, then the first one must be injective. -/
theorem injective_of_injective_compose (f : α -> β) (g : β -> γ) (domain : Set α) :
    injective_for_domain_set (g ∘ f) domain -> injective_for_domain_set f domain := by
  intro inj a a' a_dom a'_dom image_eq
  apply inj a a' a_dom a'_dom
  simp [image_eq]

/-- If a mapping is surjective for a domain and image, then the same holds for any superset of the domain. -/
theorem surjective_of_surjective_from_subset (f : α -> β) (domain : Set α) (image : Set β) :
    f.surjective_for_domain_and_image_set domain image ->
    ∀ domain', domain ⊆ domain' -> f.surjective_for_domain_and_image_set domain' image := by
  intro surj dom' dom'_sub b b_mem
  rcases surj b b_mem with ⟨a, a_mem, a_eq⟩
  exists a
  constructor
  . apply dom'_sub; exact a_mem
  . exact a_eq

/-- If the composition of two mappings is surjective for a domain and image, then the second one must be surjective on the same image and the domain that is the image of the first function. -/
theorem surjective_of_surjective_compose (f : α -> β) (g : β -> γ) (domain : Set α) (image : Set γ) :
    surjective_for_domain_and_image_set (g ∘ f) domain image ->
    surjective_for_domain_and_image_set g (f.image_set domain) image := by
  intro surj b b_mem
  rcases surj b b_mem with ⟨a, a_mem, a_eq⟩
  exists f a
  constructor
  . exists a
  . exact a_eq

/-- The injectivity definitions for set and list are interchangeable. -/
theorem injective_set_list_equiv (f : α -> β) (domain_set : Set α) (domain_list : List α) (eq : ∀ e, e ∈ domain_list ↔ e ∈ domain_set) : f.injective_for_domain_set domain_set ↔ f.injective_for_domain_list domain_list := by
  constructor
  . intro h a a' a_mem a'_mem f_eq
    apply h
    . rw [← eq]; assumption
    . rw [← eq]; assumption
    . exact f_eq
  . intro h a a' a_mem a'_mem f_eq
    apply h
    . rw [eq]; assumption
    . rw [eq]; assumption
    . exact f_eq

/-- The surjectivity definitions for set and list are interchangeable. -/
theorem surjective_set_list_equiv (f : α -> β)
    (domain_set : Set α) (domain_list : List α) (eq_domain : ∀ e, e ∈ domain_list ↔ e ∈ domain_set)
    (image_set : Set β) (image_list : List β) (eq_image : ∀ e, e ∈ image_list ↔ e ∈ image_set) :
    f.surjective_for_domain_and_image_set domain_set image_set ↔ f.surjective_for_domain_and_image_list domain_list image_list := by
  constructor
  . intro h b b_mem
    specialize h b (by rw [← eq_image]; exact b_mem)
    rcases h with ⟨a, a_mem, a_eq⟩
    exists a
    constructor
    . rw [eq_domain]; exact a_mem
    . exact a_eq
  . intro h b b_mem
    specialize h b (by rw [eq_image]; exact b_mem)
    rcases h with ⟨a, a_mem, a_eq⟩
    exists a
    constructor
    . rw [← eq_domain]; exact a_mem
    . exact a_eq

/-- If a mapping is injective on a domain of the form `hd::tl`, then it is injective on `tl`. -/
theorem injective_for_domain_list_cons (f : α -> β) (hd : α) (tl : List α) : f.injective_for_domain_list (hd::tl) -> f.injective_for_domain_list tl := by
  intro h a a' a_mem a'_mem eq
  apply h
  . simp [a_mem]
  . simp [a'_mem]
  . exact eq

/-- The mapping of each domain element occurs in the `image`. -/
theorem mapping_mem_image_of_mem [DecidableEq β] (f : α -> β) (domain : List α) : ∀ a, a ∈ domain -> f a ∈ (image f domain) := by
  intro a a_mem; apply (List.mem_eraseDupsKeepRight _ _).mpr; apply List.mem_map_of_mem; exact a_mem

/-- The `image` has no duplicates. -/
theorem nodup_image [DecidableEq β] (f : α -> β) (domain : List α) : (image f domain).Nodup := by apply List.nodup_eraseDupsKeepRight

/-- The `image` has at most as many elements as the domain. -/
theorem length_image [DecidableEq β] (f : α -> β) (domain : List α) : (image f domain).length ≤ domain.length := by
  have : domain.length = (domain.map f).length := by rw [List.length_map]
  rw [this]
  apply List.length_le_of_nodup_of_all_mem
  . apply nodup_image
  . simp [image, List.mem_eraseDupsKeepRight]

/-- Every mapping is always surjective on its own `image`. -/
theorem surjective_on_own_image [DecidableEq β] (f : α -> β) (domain : List α) : f.surjective_for_domain_and_image_list domain (image f domain) := by
  intro b b_mem; simp only [image, List.mem_eraseDupsKeepRight, List.mem_map] at b_mem; exact b_mem

/-- If a mapping is closed, then its image is fully contained in its domain. -/
theorem image_contained_of_closed [DecidableEq α] (f : α -> α) (domain : List α) (closed : ∀ e, e ∈ domain -> f e ∈ domain) : ∀ e, e ∈ image f domain -> e ∈ domain := by
  intro b b_mem
  rcases surjective_on_own_image f domain b b_mem with ⟨a, a_mem, a_eq⟩
  rw [← a_eq]
  apply closed
  exact a_mem

/-- Given a mapping and a domain list without duplicates, the mapping in injective on the domain if and only if the `image` contains the same number of elements as the domain.  -/
theorem injective_iff_length_image_eq_of_nodup [DecidableEq β] (f : α -> β) (domain : List α) (nodup : domain.Nodup) : f.injective_for_domain_list domain ↔ (image f domain).length = domain.length := by
  -- TODO: we can probably shorten this proof a lot by proving appropriate results about List.eraseDupsKeepRight
  constructor
  . intro inj
    induction domain with
    | nil => simp [image, List.eraseDupsKeepRight]
    | cons hd tl ih =>
      cases Decidable.em (f hd ∈ image f tl) with
      | inl hd_mem =>
        apply False.elim
        simp only [List.nodup_cons] at nodup
        apply nodup.left
        rcases surjective_on_own_image f tl (f hd) hd_mem with ⟨a, a_mem, a_eq⟩
        specialize inj a hd (by simp [a_mem]) (by simp) a_eq
        rw [← inj]
        exact a_mem
      | inr hd_not_mem =>
        simp only [image, List.mem_eraseDupsKeepRight] at hd_not_mem
        simp only [image, List.map_cons, List.eraseDupsKeepRight, hd_not_mem, ↓reduceIte, List.length_cons, Nat.add_right_cancel_iff]
        apply ih
        . simp only [List.nodup_cons] at nodup; exact nodup.right
        . apply injective_for_domain_list_cons; exact inj
  . intro length_eq
    induction domain with
    | nil => simp [injective_for_domain_list]
    | cons hd tl ih =>
      cases Decidable.em (f hd ∈ image f tl) with
      | inl hd_mem =>
        simp only [image, List.mem_eraseDupsKeepRight] at hd_mem
        simp only [image, List.map_cons, List.eraseDupsKeepRight, hd_mem, ↓reduceIte, List.length_cons] at length_eq
        have contra := length_image f tl
        simp only [image, length_eq] at contra
        simp [Nat.succ_le_iff] at contra
      | inr hd_not_mem =>
        simp only [image, List.mem_eraseDupsKeepRight] at hd_not_mem
        simp only [image, List.map_cons, List.eraseDupsKeepRight, hd_not_mem, ↓reduceIte, List.length_cons, Nat.add_right_cancel_iff] at length_eq
        intro a a' a_mem a'_mem eq
        rw [List.mem_cons] at a_mem
        rw [List.mem_cons] at a'_mem
        cases a_mem with
        | inl a_mem => cases a'_mem with
          | inl a'_mem => rw [a_mem, a'_mem]
          | inr a'_mem =>
            apply False.elim
            apply hd_not_mem
            rw [← a_mem, eq]
            apply List.mem_map_of_mem
            exact a'_mem
        | inr a_mem => cases a'_mem with
          | inl a'_mem =>
            apply False.elim
            apply hd_not_mem
            rw [← a'_mem, ← eq]
            apply List.mem_map_of_mem
            exact a_mem
          | inr a'_mem =>
            simp only [List.nodup_cons] at nodup
            specialize ih nodup.right length_eq
            apply ih <;> assumption

/-- A mapping is surjective on a given domain and image if and only if the given image is contained in the actual image of the mapping. -/
theorem surjective_on_target_iff_all_in_image [DecidableEq β] (f : α -> β) (domain : List α) (target_image : List β) : f.surjective_for_domain_and_image_list domain target_image ↔ ∀ b, b ∈ target_image -> b ∈ image f domain := by
  constructor
  . intro surj b b_mem
    specialize surj b b_mem
    rcases surj with ⟨a, a_mem, a_eq⟩
    rw [← a_eq]
    apply mapping_mem_image_of_mem
    exact a_mem
  . intro h b b_mem
    apply surjective_on_own_image
    apply h
    exact b_mem

/-- Given a single list without duplicates that represents both domain and image, if a mapping is surjective, then it is injective. -/
theorem injective_of_surjective_of_nodup [DecidableEq α] (f : α -> α) (l : List α) (nodup : l.Nodup) : f.surjective_for_domain_and_image_list l l -> f.injective_for_domain_list l := by
  intro surj
  rw [surjective_on_target_iff_all_in_image] at surj
  rw [injective_iff_length_image_eq_of_nodup _ _ nodup]
  rw [Nat.eq_iff_le_and_ge]
  constructor
  . exact length_image f l
  . exact List.length_le_of_nodup_of_all_mem l (image f l) nodup surj

/-- Given a single list without duplicates that represents both domain and image, if a mapping closed on the list, then the mapping is injective if and only if it is surjective. -/
theorem injective_iff_surjective_of_nodup_of_closed [DecidableEq α] (f : α -> α) (l : List α) (nodup : l.Nodup) (closed : ∀ e, e ∈ l -> f e ∈ l) : f.injective_for_domain_list l ↔ f.surjective_for_domain_and_image_list l l := by
  constructor
  . intro inj

    have : ∀ e, e ∈ image f l ↔ e ∈ l := by
      apply List.equiv_of_nodup_of_length_eq_of_all_mem
      . apply nodup_image
      . rw [injective_iff_length_image_eq_of_nodup] at inj
        rw [inj]
        exact nodup
      . intro e e_mem
        apply image_contained_of_closed
        . exact closed
        . exact e_mem

    rw [surjective_on_target_iff_all_in_image]
    intro b
    apply (this b).mpr
  . apply injective_of_surjective_of_nodup; exact nodup

/-- Given a single list without duplicates that represents both domain and image, if a mapping both injective and surjective, then is must be closed on the list. -/
theorem closed_of_injective_of_surjective_of_nodup [DecidableEq α] (f : α -> α) (l : List α) (nodup : l.Nodup) : f.injective_for_domain_list l -> f.surjective_for_domain_and_image_list l l -> ∀ e, e ∈ l -> f e ∈ l := by
  intro inj surj
  intro e e_mem
  rw [List.equiv_of_nodup_of_length_eq_of_all_mem l (image f l) nodup]
  . apply mapping_mem_image_of_mem; exact e_mem
  . rw [(injective_iff_length_image_eq_of_nodup f l nodup).mp inj]
  . exact (surjective_on_target_iff_all_in_image f l l).mp surj

end Function

namespace GroundTermMapping

/-!
## Strong GroundTermMappings (and Homomorphisms)

Intuitively, a homomorphism is `strong` if it not only retains membership but also non-membership.
We define being `strong` as a standalone property for `GroundTermMapping`s
without requiring any additional properties for the underlying `GroundTermMapping`.
-/

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V] [DecidableEq sig.P]

/-- A `GroundTermMapping` is strong for `FactSet`s A and B if each element not in A, its mapping is not in B. However, we only demand this for elements that only feature terms from a given domain because we do not want to care about the mapping of terms outside the domain. -/
def strong (h : GroundTermMapping sig) (domain : Set (GroundTerm sig)) (A B : FactSet sig) : Prop :=
  ∀ (e : Fact sig), (∀ t, t ∈ e.terms -> t ∈ domain) -> ¬ e ∈ A -> ¬ (h.applyFact e) ∈ B

/-- If the composition of two mappings is strong from A to C and the second mapping is a homomorphism from B to C, then the first mapping is strong from A to B. -/
theorem strong_of_compose_strong (g h : GroundTermMapping sig) (domain : Set (GroundTerm sig)) (A B C : FactSet sig) :
    h.isHomomorphism B C -> GroundTermMapping.strong (h ∘ g) domain A C -> g.strong domain A B := by
  intro h_hom compose_strong
  intro e e_dom e_not_mem_a e_mem_b
  apply compose_strong e
  . exact e_dom
  . exact e_not_mem_a
  . apply h_hom.right (GroundTermMapping.applyFact (h ∘ g) e)
    exists (g.applyFact e)
    constructor
    . exact e_mem_b
    . unfold applyFact
      rw [TermMapping.apply_generalized_atom_compose]
      simp

end GroundTermMapping

namespace GroundTermMapping

-- TODO: I think a lot of the following can be generalized to arbitrary Functions

/-!
## Repetition of GroundTermMappings (and Homomorphisms)

In general, we can define what it means to apply a function a given number of times.
This is particularly useful for `GroundTermMapping`s that are endomorphisms, i.e. homomorphisms from one structure into the same structure.
We can show some nice properties for such repetitions. For example, a repeated endomorphisms is still an endomorphisms.
-/

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- Repetition of a `GroundTermMapping` defined in the obvious way. Repeating zero times is defined as the id function. -/
def repeat_hom (h : GroundTermMapping sig) : Nat -> GroundTermMapping sig
| .zero => id
| .succ j => h ∘ (h.repeat_hom j)

/-- It does not mapper if we apply add one more repetition on the left or the right. -/
theorem repeat_hom_swap (h : GroundTermMapping sig) (i : Nat) : ∀ t, h (h.repeat_hom i t) = (h.repeat_hom i) (h t) := by
  intro t
  induction i with
  | zero => unfold repeat_hom; simp
  | succ i ih => unfold repeat_hom; simp [ih]

/-- A (n+m)-times repetition can be split into the composition of an m-times repetition followed by an n-times repetition. -/
theorem repeat_hom_add (h : GroundTermMapping sig) (n m : Nat) : ∀ t, h.repeat_hom (n + m) t = h.repeat_hom n (h.repeat_hom m t) := by
  intro t
  induction m with
  | zero => simp [repeat_hom]
  | succ m ih =>
    conv => left; unfold repeat_hom
    conv => right; right; unfold repeat_hom
    simp [ih, h.repeat_hom_swap]

/-- If some repetition maps a term to itself, then each multiple of the repetition count must also map the term to itself. -/
theorem repeat_hom_cycle_mul (h : GroundTermMapping sig) (t : GroundTerm sig) (n : Nat) : h.repeat_hom n t = t -> ∀ m, h.repeat_hom (n * m) t = t := by
  intro cycle m
  induction m with
  | zero => simp [repeat_hom]
  | succ m ih =>
    rw [Nat.mul_add]
    rw [repeat_hom_add]
    simp [cycle, ih]

/-- If some repetition maps a term to itself, then for each other term that is part of the loop, the same number of repetitions also maps that one to itself. -/
theorem repeat_hom_move_cycle (h : GroundTermMapping sig) (t : GroundTerm sig) (n : Nat) : h.repeat_hom n t = t -> ∀ s m, h.repeat_hom m t = s -> h.repeat_hom n s = s := by
  intro cycle s m reaches_s
  induction m generalizing t with
  | zero => simp only [repeat_hom, id_eq] at reaches_s; rw [← reaches_s]; exact cycle
  | succ m ih =>
    apply ih (h t)
    . rw [← h.repeat_hom_swap]
      rw [cycle]
    . simp only [repeat_hom, Function.comp_apply] at reaches_s
      rw [h.repeat_hom_swap] at reaches_s
      exact reaches_s

/-- Consider a list of terms. If each term is reachable by some number of repetitions from some term, then for each term there is a number of repetition that maps the term to itself. Intuitively this holds by a pigeonhole principle: If for each term you need to pick a term from that you can reach it, but only finitely many terms are available, then eventually you need to complete a cycle. -/
theorem repeat_each_reaches_self_of_each_reachable
    (h : GroundTermMapping sig)
    (ts : List (GroundTerm sig))
    (each_reachable : ∀ t, t ∈ ts -> ∃ k, 1 ≤ k ∧ ∃ s, s ∈ ts ∧ (h.repeat_hom k) s = t) :
    (∀ s, s ∈ ts -> ∃ l, 1 ≤ l ∧ (h.repeat_hom l) s = s) := by
  induction ts with
  | nil => simp
  | cons hd tl ih =>
    specialize ih (by
      intro t t_mem
      have each_reachable_for_t := each_reachable t (by simp [t_mem])
      rcases each_reachable_for_t with ⟨k, k_le, s, s_mem, s_eq⟩
      simp only [List.mem_cons] at s_mem
      cases s_mem with
      | inr s_mem => exists k; constructor; exact k_le; exists s
      | inl s_mem =>
        have each_reachable_for_s := each_reachable s (by simp [s_mem])
        rcases each_reachable_for_s with ⟨l, l_le, u, u_mem, u_eq⟩
        simp only [List.mem_cons] at u_mem
        cases u_mem with
        | inl u_mem =>
          exists (((k / l) + 1) * l)
          constructor
          .
            rw [Nat.add_mul]
            apply Nat.le_trans
            . exact k_le
            . apply Nat.le_of_lt
              simp
              -- NOTE: taken from https://github.com/leanprover-community/mathlib4/blob/3f813de52d8cffaa73e27edd62364eec90eac633/Mathlib/Data/Nat/Defs.lean#L473-L474
              rw [← Nat.succ_mul, ← Nat.div_lt_iff_lt_mul (by apply Nat.lt_of_succ_le; exact l_le)]; exact Nat.lt_succ_self _
          . exists t
            constructor
            . exact t_mem
            . apply h.repeat_hom_move_cycle s
              . rw [Nat.mul_comm]
                apply h.repeat_hom_cycle_mul
                rw [u_mem, ← s_mem] at u_eq
                exact u_eq
              . exact s_eq
        | inr u_mem =>
          exists (k + l)
          constructor
          . apply Nat.le_add_right_of_le; exact k_le
          . exists u
            constructor
            . exact u_mem
            . rw [GroundTermMapping.repeat_hom_add]
              rw [u_eq, s_eq]
    )

    intro s s_mem
    simp only [List.mem_cons] at s_mem
    cases s_mem with
    | inl s_mem =>
      specialize each_reachable s (by rw [s_mem]; simp)
      rcases each_reachable with ⟨k, k_le, t, t_mem, t_eq⟩
      simp only [List.mem_cons] at t_mem
      cases t_mem with
      | inl t_mem => exists k; constructor; exact k_le; rw [t_mem, ← s_mem] at t_eq; exact t_eq
      | inr t_mem =>
        specialize ih t t_mem
        rcases ih with ⟨l, l_le, ih⟩
        exists l
        constructor
        . exact l_le
        . apply h.repeat_hom_move_cycle t
          . exact ih
          . exact t_eq
    | inr s_mem =>
      apply ih
      exact s_mem

/-- If each term from a finite list is mapped to itself after some number of repetitions, then there is a global repetition number that maps each term to itself. Basically any common multiple of the individual repetition numbers works. -/
theorem repeat_globally_of_each_repeats
    (h : GroundTermMapping sig)
    (ts : List (GroundTerm sig))
    (each_repeats : ∀ s, s ∈ ts -> ∃ l, 1 ≤ l ∧ (h.repeat_hom l) s = s) :
    ∃ l, 1 ≤ l ∧ ∀ s, s ∈ ts -> (h.repeat_hom l) s = s := by
  induction ts with
  | nil => exists 1; simp
  | cons hd tl ih =>
    specialize ih (by intro s s_mem; apply each_repeats; simp [s_mem])
    rcases ih with ⟨l_ih, l_ih_le, ih⟩
    rcases each_repeats hd (by simp) with ⟨l_hd, l_hd_le, each_repeats⟩
    exists l_hd * l_ih
    constructor
    . apply Nat.le_trans; exact l_hd_le; apply Nat.le_mul_of_pos_right; apply Nat.lt_of_succ_le; exact l_ih_le
    . intro s s_mem
      simp only [List.mem_cons] at s_mem
      cases s_mem with
      | inl s_mem => rw [s_mem, h.repeat_hom_cycle_mul]; exact each_repeats
      | inr s_mem => specialize ih s s_mem; rw [Nat.mul_comm, h.repeat_hom_cycle_mul]; exact ih

/-- If a mapping is surjective for a given list of terms, then there exists a repetition count $k$ such that $k+1$ map each term from the list to itself. Note that we use $k+1$ repetitions as otherwise the result would be trivial for zero repetitions, which are the id by definition. -/
theorem exists_repetition_that_is_inverse_of_surj (h : GroundTermMapping sig) (ts : List (GroundTerm sig)) (surj : h.surjective_for_domain_and_image_list ts ts) : ∃ k, ∀ t, t ∈ ts -> (h.repeat_hom k) (h t) = t := by
  have each_repeats := h.repeat_each_reaches_self_of_each_reachable ts (by
    intro t t_mem
    exists 1
    constructor
    . simp
    . simp only [repeat_hom]
      apply surj t t_mem
  )
  have repeats_globally := h.repeat_globally_of_each_repeats ts each_repeats

  rcases repeats_globally with ⟨k, le, repeats_globally⟩

  exists k-1
  intro t t_mem
  have repeat_add := h.repeat_hom_add (k-1) 1 t
  conv at repeat_add => right; right; simp [repeat_hom]
  rw [← repeat_add]
  rw [Nat.sub_one_add_one]
  . apply repeats_globally; exact t_mem
  . apply Nat.ne_zero_of_lt; apply Nat.lt_of_succ_le; exact le

/-- Repeating a mapping retains the `isIdOnConstants` property. -/
theorem repeat_hom_id_on_const (h : GroundTermMapping sig) (idOnConst : h.isIdOnConstants) : ∀ i, (h.repeat_hom i).isIdOnConstants := by
  intro i
  induction i with
  | zero => unfold repeat_hom; intro c; simp
  | succ i ih =>
    intro c
    unfold repeat_hom
    rw [Function.comp_apply, ih, idOnConst]

variable [DecidableEq sig.P]

/-- Repeating a mapping retains the `isHomomorphism` property at least for endomorphisms. -/
theorem repeat_hom_isHomomorphism (h : GroundTermMapping sig) (fs : FactSet sig) (hom : h.isHomomorphism fs fs) : ∀ i, (h.repeat_hom i).isHomomorphism fs fs := by
  intro i
  constructor
  . apply repeat_hom_id_on_const; exact hom.left
  . induction i with
    | zero =>
      simp only [repeat_hom]
      intro f f_mem
      rcases f_mem with ⟨f', f'_mem, f_eq⟩
      have : f = f' := by
        unfold TermMapping.apply_generalized_atom at f_eq
        rw [f_eq]; simp
      rw [this]
      exact f'_mem
    | succ i ih =>
      unfold repeat_hom
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
def isWeakCore (fs : FactSet sig) : Prop :=
  ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs.terms fs fs ∧ h.injective_for_domain_set fs.terms

/-- A `FactSet` is a strong core if every endomorphisms on the fact set is strong, injective, and surjective. (By definition, every strong core is a weak core.) -/
def isStrongCore (fs : FactSet sig) : Prop :=
  ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.strong fs.terms fs fs ∧ h.injective_for_domain_set fs.terms ∧ h.surjective_for_domain_and_image_set fs.terms fs.terms

/-- We say that a fact set $C$ is a homomorphic subset of another fact set $F$ if $C$ is a subset of $F$ and there is a homomorphism from $F$ to $C$. -/
def homSubset (c fs : FactSet sig) : Prop := c ⊆ fs ∧ (∃ (h : GroundTermMapping sig), h.isHomomorphism fs c)

/-- For a homomorphism on a finite fact set, injectivity implies surjectivity. -/
theorem hom_surjective_of_finite_of_injective (fs : FactSet sig) (finite : fs.finite) : ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.injective_for_domain_set fs.terms -> h.surjective_for_domain_and_image_set fs.terms fs.terms := by
  rcases finite with ⟨l, finite⟩
  intro h isHom inj

  let terms_list := (l.map GeneralizedAtom.terms).flatten.eraseDupsKeepRight
  have nodup_terms_list : terms_list.Nodup := by apply List.nodup_eraseDupsKeepRight
  have mem_terms_list : ∀ e, e ∈ terms_list ↔ e ∈ fs.terms := by
    simp only [terms_list]
    intro e
    rw [List.mem_eraseDupsKeepRight]
    unfold FactSet.terms
    simp only [List.mem_flatten, List.mem_map]
    constructor
    . intro h
      rcases h with ⟨ts, h, ts_mem⟩
      rcases h with ⟨f, f_mem, eq⟩
      exists f
      rw [eq]
      rw [← finite.right f]
      constructor <;> assumption
    . intro h
      rcases h with ⟨f, f_mem, e_mem⟩
      exists f.terms
      constructor
      . exists f; rw [finite.right f]; constructor; exact f_mem; rfl
      . exact e_mem
  have closed : ∀ e, e ∈ terms_list -> h e ∈ terms_list := by
    simp only [terms_list]
    intro e
    rw [List.mem_eraseDupsKeepRight]
    rw [List.mem_eraseDupsKeepRight]
    simp only [List.mem_flatten, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro f f_mem e_in_f
    let f' := h.applyFact f
    have f'_mem : f' ∈ fs := by
      apply isHom.right
      unfold GroundTermMapping.applyFactSet
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

  rw [Function.surjective_set_list_equiv h fs.terms terms_list mem_terms_list fs.terms terms_list mem_terms_list]
  rw [← Function.injective_iff_surjective_of_nodup_of_closed h terms_list nodup_terms_list closed]
  rw [← Function.injective_set_list_equiv h fs.terms terms_list mem_terms_list]
  exact inj

/-- For a homomorphism on a finite fact set, injectivity implies that the homomorphisms is also strong. -/
theorem hom_strong_of_finite_of_injective (fs : FactSet sig) (finite : fs.finite) : ∀ (h : GroundTermMapping sig), h.isHomomorphism fs fs -> h.injective_for_domain_set fs.terms -> h.strong fs.terms fs fs := by
  intro h isHom inj

  intro f ts_mem f_not_mem apply_mem
  apply f_not_mem

  have surj := fs.hom_surjective_of_finite_of_injective finite h isHom inj

  have terms_finite := fs.terms_finite_of_finite finite
  rcases terms_finite with ⟨terms, nodup, equiv⟩

  rw [h.surjective_set_list_equiv fs.terms terms equiv fs.terms terms equiv] at surj
  have ex_inv := h.exists_repetition_that_is_inverse_of_surj terms surj
  rcases ex_inv with ⟨k, inv⟩
  have inv_hom : (h.repeat_hom k).isHomomorphism fs fs := h.repeat_hom_isHomomorphism fs isHom k

  have : (h.repeat_hom k).applyFact (h.applyFact f) = f := by
    unfold GroundTermMapping.applyFact
    rw [← TermMapping.apply_generalized_atom_compose']
    apply TermMapping.apply_generalized_atom_eq_self_of_id_on_terms
    intro t t_mem
    rw [Function.comp_apply]
    apply inv
    rw [equiv]
    apply ts_mem
    exact t_mem
  rw [← this]

  apply inv_hom.right
  apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
  exact apply_mem

/-- For finite fact sets, `isWeakCore` implies `isStrongCore`. That means that `isWeakCore` and `isStrongCore` are equivalent on finite fact sets. -/
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
    . unfold Set.finite; exists l
    . exact isHom
    . exact injective

/-- Given two fact sets A,B of which one is a weak and one is a strong core, if there are homomorphisms from A to B and B to A, then there exists an isomorphism from A to B, i.e. a strong homomorphisms that is injective and surjective. -/
theorem every_weakCore_isomorphic_to_strongCore_of_hom_both_ways
    (sc : FactSet sig) (sc_strong : sc.isStrongCore)
    (wc : FactSet sig) (wc_weak : wc.isWeakCore)
    (h_sc_wc h_wc_sc : GroundTermMapping sig) (h_sc_wc_hom : h_sc_wc.isHomomorphism sc wc) (h_wc_sc_hom : h_wc_sc.isHomomorphism wc sc) :
    ∃ (iso : GroundTermMapping sig), iso.isHomomorphism wc sc ∧ iso.strong wc.terms wc sc ∧ iso.injective_for_domain_set wc.terms ∧ iso.surjective_for_domain_and_image_set wc.terms sc.terms := by

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
  . apply Function.injective_of_injective_compose h_wc_sc h_sc_wc
    exact wc_weak.right
  -- surjective since h_wc_sc ∘ h_sc_wc is surjective
  . apply Function.surjective_of_surjective_from_subset
    . apply Function.surjective_of_surjective_compose h_sc_wc h_wc_sc sc.terms
      exact sc_strong.right.right
    . intro t t_mem_image
      rcases t_mem_image with ⟨arg, arg_mem, arg_eq⟩
      rcases arg_mem with ⟨f, f_mem, f_eq⟩
      exists (h_sc_wc.applyFact f)
      constructor
      . apply h_sc_wc_hom.right
        exists f
      . unfold GroundTermMapping.applyFact
        unfold TermMapping.apply_generalized_atom
        rw [List.mem_map]
        exists arg; simp [f_eq, arg_eq]

/-- Strong cores of fact sets are unique up to isomorphism. That is, consider a fact set $F$. A strong core $C$ for $F$ is a strong core that is also a homomorphic subset of $F$. Now every (other) homomorphic subset $C'$ of $F$ that is at least a weak core has an isomorphism into $C$. -/
theorem strongCore_unique_up_to_isomorphism_with_respect_to_weak_cores
    (fs : FactSet sig)
    (sc : FactSet sig) (sub_sc : sc.homSubset fs) (sc_strong : sc.isStrongCore)
    (wc : FactSet sig) (sub_wc : wc.homSubset fs) (wc_weak : wc.isWeakCore) :
    ∃ (iso : GroundTermMapping sig), iso.isHomomorphism wc sc ∧ iso.strong wc.terms wc sc ∧ iso.injective_for_domain_set wc.terms ∧ iso.surjective_for_domain_and_image_set wc.terms sc.terms := by

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
    ∃ (iso : GroundTermMapping sig), iso.isHomomorphism wc sc ∧ iso.strong wc.terms wc sc ∧ iso.injective_for_domain_set wc.terms ∧ iso.surjective_for_domain_and_image_set wc.terms sc.terms := by

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
        rcases f_mem with ⟨f', f'_mem, f_eq⟩
        have strong := sc_strong.left
        unfold GroundTermMapping.strong at strong
        apply Classical.byContradiction
        intro contra
        apply strong f
        . intro t t_mem
          rw [f_eq] at t_mem
          unfold TermMapping.apply_generalized_atom at t_mem
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
        unfold FunctionFreeConjunction.vars at v_mem
        rw [List.mem_flatMap] at v_mem
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
          constructor
          . unfold FunctionFreeAtom.variables at v_mem
            apply VarOrConst.filterVars_occur_in_original_list
            exact v_mem
          . rfl
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

