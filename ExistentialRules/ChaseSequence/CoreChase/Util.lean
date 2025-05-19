import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteList.PossiblyInfiniteList

theorem contrapose (A B : Prop) : A → B ↔ ¬ B → ¬ A := by grind


theorem min_le_of_mem_set (x : Nat) (S : Set Nat) (x_in : x ∈ S) : ∃ m : Nat, m ∈ S ∧ ∀ n : Nat, n ∈ S → m ≤ n := by

    let S' := (fun n => S (n + 1))

    induction x generalizing S with
    | zero =>
        exists 0, x_in
        intro n n_in
        exact Nat.zero_le n

    | succ x ih =>
        by_cases c : 0 ∈ S

        exists 0, c
        intro n n_in
        exact Nat.zero_le n

        have x_in' : S' x := by exact x_in

        rcases ih S' x_in' with ⟨m, hm, hmin⟩
        exists (m+1), hm
        intro n n_in
        cases n with
        | zero =>
            contradiction
        | succ n =>
            exact Nat.add_le_add_right (hmin n n_in) 1

-- well-ordering principle
theorem wop (S : Set Nat) (S_non_empty : ∃ (n : Nat), n ∈ S) : ∃ (m : Nat), m ∈ S ∧ ∀ (n : Nat), n ∈ S → m ≤ n := by
  rcases S_non_empty with ⟨n, h⟩
  exact min_le_of_mem_set n S h


/-
  l = [x1, x2, x3, x4]

  y1 = f init x1
  y2 = f y1 x2
  y3 = f y2 x3

  foldl_save_hist l init f = [init, (f init x1), (f (f init x1) x2), (f (f (f init x1) x2) x3)]

  foldl_save_hist l init f = [init, y1, y2, y3]
-/


-- foldl_save_hist variant for function returning options, if none is returned by f the argument is not applied and the previous element which was some is returned
def foldl_save_hist_opt (l : List α) (init_elem : β) (f : β → α → Option β) : List β :=
  let (_, history) :=
  l.foldl
    (fun (state, hist) t =>
      match (f state t) with
        | some s' => (s', hist.concat s')
        | none    => (state, hist)
      )
    (init_elem, [init_elem])
history

def foldl_save_hist_opt_nodup [DecidableEq β] (l : List α) (init_elem : β) (f : β → α → Option β) : List β :=
  let (_, history) :=
    l.foldl
      (fun (state, history) t =>
        let next := (f state t).getD state
        if next = state then
          (state, history)
        else
          (next, history.concat next))
      (init_elem, [init_elem])
  history

def foldl_save_hist_opt_nodup_trace [DecidableEq β](l : List α) (init : β) (f : β → α → Option β) : List (β × Option α) :=
  (l.foldl
    (fun
      | (state, hist), o =>
        if (f state o).getD state = state then
          (state, hist)
        else
          ((f state o).getD state,
           hist ++ [((f state o).getD state, some o)]))
    (init, [(init, none)])).2


def test_fun (a b : Nat) : Option (Nat) :=
    if (a > b) then a - b else none

#eval foldl_save_hist_opt [5, 20, 20, 1, 10, 5, 0, 1] 20 test_fun

#eval foldl_save_hist_opt_nodup [10, 5, 8, 3] 20 test_fun

#eval foldl_save_hist_opt_nodup_trace [5, 20, 20, 1, 10, 5, 0, 1] 20 test_fun


@[grind =]
theorem head_concat (l : List β) (x : β) (h : l ≠ []) :
  (l.concat x).head? = l.head? := by
  cases l with
  | nil =>
    contradiction
  | cons hd tl =>
    simp [List.concat]

theorem foldl_save_hist_opt_nodup_head_eq [DecidableEq β] (l : List α) (init_elem : β) (f : β → α → Option β) :
(foldl_save_hist_opt_nodup l init_elem f).head? = some init_elem := by
  unfold foldl_save_hist_opt_nodup
  have h : ∀ (l : List α) (state : β) (hist : List β),
    hist.head? = some init_elem → (l.foldl (fun (state, hist) t =>
      let next := (f state t).getD state
      if next = state then
        (state, hist)
      else
        (next, hist.concat next))
      (state, hist)).snd.head? = some init_elem := by
        intro l
        induction l with
          | nil =>
            grind
          | cons hd tl ih =>
            grind

  exact h l init_elem [init_elem] rfl


@[grind =]
theorem head?_eraseDups [DecidableEq α] (l : List α) (h : l ≠ []) :
  (l.eraseDups).head? = l.head? := by
    induction l with
      | nil =>
        contradiction
      | cons x xs =>
        simp only [List.head?_cons]
        grind


@[grind .]
theorem foldl_save_hist_opt_nodup_trace_adjacent_ne [DecidableEq β] (l : List α) (init : β) (f : β → α → Option β) (n : Nat) (h : n + 1 < (foldl_save_hist_opt_nodup_trace l init f).length) :
  (foldl_save_hist_opt_nodup_trace l init f)[n] ≠ (foldl_save_hist_opt_nodup_trace l init f)[n+1] := by
    intro contra
    let hist := foldl_save_hist_opt_nodup_trace l init f
    have hist_eq : hist[n] = hist[n+1] := contra

    have hstep :
      ∃ (state next : β) (o : Option α),
        hist[n] = (state, o) ∧
        hist[n+1] = (next, o) ∧
        next ≠ state := by

      have : ∃ (state next : β) (o : Option α),
        (foldl_save_hist_opt_nodup_trace l init f)[n]'(Nat.lt_of_succ_lt h) = (state, o) ∧
        (foldl_save_hist_opt_nodup_trace l init f)[n+1]'(by exact Nat.lt_of_succ_le h) = (next, o) ∧
        next ≠ state := by
          induction l generalizing n with
          | nil =>
            exists init
          | cons hd tl ih =>
            sorry
      exact this
    grind

namespace Function

theorem id_is_injective (A : Set α) : Function.injectiveSet id A := by
  intro a b a_in b_in eq
  simp at eq
  exact eq

theorem id_is_surjective (A : Set α) : Function.surjectiveSet id A A := by
  intro a a_in
  exists a

end Function


namespace Option

  @[grind .]
  theorem isSomeIffNeqNone (o : Option α) : o.isSome ↔ o ≠ none := by
    constructor
    grind
    intro h
    unfold Option.isSome
    split
    next => grind
    next => grind

  theorem NeqNoneIfIsSome (o : Option α) (a : α) : o = some a →  o ≠ none := by
    intro h
    exact (isSomeIffNeqNone o).mp (Option.isSome_of_mem h)

  @[simp, grind]
  def castToMemIfNotNone (o : Option α) (not_none : o ≠ none) : α :=
    match o with
      | some o => o
      | none => by contradiction

  @[simp, grind]
  def castToMemIfIsSome (o : Option α) (is_some : o.isSome) : α :=
    match o with
      | some o => o
      | none => by contradiction

  @[simp]
  def castisSomeIfEqSome (o : Option α) (a : α) : (o = some a) → o.isSome := by apply Option.isSome_of_mem

  @[simp, grind .]
  theorem isNone_and_isSome_False (o : Option α) : o.isNone ∧ o.isSome → False := by
    simp_all

end Option


namespace Set

  @[grind .]
  theorem subsetOfFiniteIsFinite [DecidableEq α] (A B : Set α) (b_fin : B.finite) (sub : A ⊆ B) : A.finite := by
    exact Set.finite_of_subset_finite b_fin sub

  @[grind .]
  theorem unionOfFinteIsFinte [DecidableEq α] (A B : Set α) : A.finite ∧ B.finite ↔ (A ∪ B).finite := by
    constructor
    intro ⟨⟨al, al_nodup, al_eq⟩, ⟨bl, bl_nodup, bl_eq⟩⟩
    have dec := Classical.propDecidable
    exists (al ++ bl).eraseDupsKeepRight
    constructor
    exact List.nodup_eraseDupsKeepRight (al ++ bl)
    intro e
    rw [List.mem_eraseDupsKeepRight]
    constructor
    intro in_albl
    rw [List.mem_append] at in_albl
    rcases in_albl with in_a | in_b
    specialize al_eq e
    left
    rw [← al_eq]
    exact in_a
    specialize bl_eq e
    right
    rw [← bl_eq]
    exact in_b
    intro in_ab
    rw [@List.mem_append]
    rcases in_ab with in_a | in_b
    specialize al_eq e
    left
    rw [al_eq]
    exact in_a
    specialize bl_eq e
    right
    rw [bl_eq]
    exact in_b
    intro ab_fin
    have a_sub : A ⊆ (A ∪ B) := by exact Set.subset_union_of_subset_left fun e a => a
    have b_sub : B ⊆ (A ∪ B) := by exact Set.subset_union_of_subset_right B A B fun e a => a
    constructor
    exact subsetOfFiniteIsFinite A (A ∪ B) ab_fin a_sub
    exact subsetOfFiniteIsFinite B (A ∪ B) ab_fin b_sub

  @[grind .]
  theorem union_iff (A B : Set α) (e : α) : e ∈ A ∪ B ↔ e ∈ A ∨ e ∈ B := by
    exact Eq.to_iff rfl

  @[grind =]
  theorem unionSym (A B : Set α) : A ∪ B = B ∪ A := by
    apply Set.ext
    intro e
    grind

  @[grind .]
  theorem exListOfSetIfFin (S : Set α) (fin : S.finite) : ∃ (l : List α), ∀ e, e ∈ l ↔ e ∈ S := by
    rcases fin with ⟨l, l_nodup, l_eq⟩
    exact Exists.intro l l_eq

end Set

namespace PossiblyInfiniteList

  def singleton (a : α) : PossiblyInfiniteList α :=
    {
      infinite_list := fun n =>
      match n with
        | .zero     => some a
        | .succ _   => none
      no_holes := by
        intro n h
        rfl
    }

  @[grind .]
  theorem singleton_none_at_gt_zero (n : Nat) (gt : n > 0) : ((PossiblyInfiniteList.singleton α).infinite_list n).isNone := by
    unfold singleton
    simp only [Option.isNone_iff_eq_none]
    grind

  def prefixUpTo (l : PossiblyInfiniteList α) (n : Nat) : List α :=
    (List.range (n + 1)).filterMap (fun i => (l.infinite_list i))

end PossiblyInfiniteList

namespace InfiniteList

  def insert_at (l : InfiniteList α) (n : Nat) (a : α) : InfiniteList α :=
    fun m =>
      if m < n then
        l m
      else if m = n then
        a
      else
        l (m - 1)

end InfiniteList


namespace List

  @[grind .]
  theorem range'_allElementsInRange (b : Nat) (idx_l : List Nat) (idx_l_eq : (idx_l = List.range' 1 b)) : ∀ n, n ∈ idx_l → n ≥ 1 ∧ n ≤ b := by
    intro n h
    grind

  @[grind .]
  theorem range_head_eq (l : List Nat) (n : Nat) (l_eq : l = List.range (n + 1)) : l.head (by grind) = 0 := by grind

  theorem mem_map_iff_mem_map_eraseDupsKeepRight (l : List α) (h : α → β) (e : β) [DecidableEq α] : e ∈ List.map h l ↔ e ∈ List.map h l.eraseDupsKeepRight := by
    repeat rw [List.mem_map]
    apply exists_congr
    intro f
    rw [List.mem_eraseDupsKeepRight]

  theorem length_lt_of_proper_subset [DecidableEq α] (l sub : List α) (sub_nodup : sub.Nodup) (subset : sub ⊆ l) (neq : sub.toSet ≠ l.toSet) : sub.length < l.length := by
    induction sub generalizing l with
      | nil =>
        exact List.length_lt_of_drop_ne_nil fun a => neq (congrArg List.toSet (id (Eq.symm a)))
      | cons hd tl ih =>
        have hd_in_l : hd ∈ l := by
          apply subset
          left
        have subset' : (hd :: tl).toSet ⊆ l.toSet := Set.subset_trans subset fun e a => a
        have hd_nin_tl : ¬ hd ∈ tl := by
          rw [List.nodup_cons] at sub_nodup
          exact sub_nodup.1
        have tl_nodup : tl.Nodup := by
          unfold List.Nodup
          exact List.Pairwise.of_cons sub_nodup
        have tl_sub_lerase : tl ⊆ (l.erase hd) := by
          intro e e_in_tl
          refine (List.mem_erase_of_ne ?_).mpr ?_
          have e_in_hdtl : e ∈ (hd :: tl) := by exact List.mem_cons_of_mem hd e_in_tl
          by_cases c : (e = hd)
          unfold List.Nodup at sub_nodup
          exact ne_of_mem_of_not_mem e_in_tl hd_nin_tl
          exact c
          have : e ∈ (hd :: tl) := by exact List.mem_cons_of_mem hd e_in_tl
          apply subset
          exact this

        have lerase_len_lt : (l.erase hd).length = l.length - 1 := by
          exact List.length_erase_of_mem hd_in_l
        have tl_neq_lerase : tl.toSet ≠ (l.erase hd).toSet := by
          intro contra
          apply neq
          apply Set.ext
          intro e
          repeat rw [List.mem_toSet]
          rw [Set.ext_iff] at contra
          specialize contra e
          repeat rw [List.mem_toSet] at contra
          rw [List.mem_cons]
          constructor
          . intro e_mem
            cases e_mem with
            | inl e_mem => rw [e_mem]; exact hd_in_l
            | inr e_mem =>
              rw [← List.mem_erase_of_ne]
              . rw [← contra]; exact e_mem
              . intro contra
                apply hd_nin_tl
                rw [← contra]
                exact e_mem
          . intro e_mem
            cases Decidable.em (e = hd) with
            | inl e_eq_hd => apply Or.inl; exact e_eq_hd
            | inr e_neq_hd =>
              apply Or.inr
              rw [contra]
              rw [List.mem_erase_of_ne]
              . exact e_mem
              . exact e_neq_hd

        specialize ih (l.erase hd) tl_nodup tl_sub_lerase tl_neq_lerase
        have tl_len_eq_hdtl_len_lt : tl.length = (hd::tl).length -1 := by rfl
        rw [lerase_len_lt, tl_len_eq_hdtl_len_lt] at ih
        exact Nat.succ_lt_of_lt_pred ih

end List
