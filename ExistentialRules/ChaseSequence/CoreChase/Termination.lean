import ExistentialRules.ChaseSequence.ChaseBranch
import ExistentialRules.Models.Basic
import ExistentialRules.Models.Cores
import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic
import ExistentialRules.Models.Basic
import ExistentialRules.Triggers.Basic
import ExistentialRules.AtomsAndFacts.Basic
import ExistentialRules.AtomsAndFacts.SubstitutionsAndHomomorphisms
import ExistentialRules.ChaseSequence.Termination.Basic
import ExistentialRules.ChaseSequence.Universality

import ExistentialRules.ChaseSequence.Deterministic

import ExistentialRules.ChaseSequence.CoreChase.Basic
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseNode
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch
import ExistentialRules.ChaseSequence.CoreChase.Triggers

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


namespace CoreChaseBranch

  def terminates (cb : CoreChaseBranch kb) : Prop :=
    ∃ n, (cb.branch.infinite_list n = none)

  def terminatesAtStep (cb : CoreChaseBranch kb) (n : Nat) : Prop :=
    (cb.branch.infinite_list n) ≠ none ∧ (cb.branch.infinite_list (n+1) = none)

  def terminates' (cb : CoreChaseBranch kb) : Prop :=
    ∃ n, terminatesAtStep cb n

  @[grind .]
  theorem terminates_if_terminates' (cb : CoreChaseBranch kb) : cb.terminates' → cb.terminates := by
    intro ⟨n, a, b⟩
    exists (n + 1)

  @[grind .]
  theorem terminates'_if_terminates_non_empty (cb : CoreChaseBranch kb) (non_empty : ∃ m, (cb.branch.infinite_list m).isSome) : cb.terminates → cb.terminates' := by
    intro ⟨n, a⟩
    rcases non_empty with ⟨m, c⟩
    -- n yielded from terminates, thus (n ≥ m)
    induction d : (n - m) generalizing n with
      | zero =>
        have ngt : m > n ∨ m = n := by grind
        cases ngt with
          | inl case =>
            have := cb.branch.get?_eq_none_of_le_of_eq_none a m (Nat.le_of_lt case)
            simp only [PossiblyInfiniteList.get?, InfiniteList.get] at this
            rw [this] at c
            simp at c
          | inr case =>
            rw [case] at c
            grind

      | succ n' ih =>
        specialize ih (n' + m)
        by_cases case : (cb.branch.infinite_list (n' + m) = none)
        grind
        have x : n = (n' + m) + 1 := by grind
        exists n' + m
        unfold terminatesAtStep
        constructor
        exact case
        grind

  def lastElementIndexRec  (cb : CoreChaseBranch kb) (ter' : cb.terminates') (n : Nat) : Nat :=
    match eq : cb.branch.infinite_list n with
      | none => n - 1
      | some cn =>
        have : Classical.choose ter' + 1 - (n + 1) < Classical.choose ter' + 1 - n := by
          apply Nat.sub_succ_lt_self
          let n_max := Classical.choose ter'
          have not_none := Classical.choose_spec ter'
          have lt : n ≤ n_max := by
            apply Classical.byContradiction
            intro contra
            have gt : n > n_max := by grind
            have lt_is_some : ∀ m, m ≤ n → cb.branch.infinite_list m ≠ none := by
              intro m leq
              rcases not_none with ⟨x, y⟩
              subst n_max
              rw [Option.isSome_eq_isSome.mp rfl] at y
              have := cb.branch.no_holes' (Classical.choose ter' + 1) y
              have := leq_some_if_some cb n (by exact Option.isSome_of_mem eq) m leq
              exact Option.isSome_iff_ne_none.mp this
            apply lt_is_some (n_max + 1)
            exact gt
            exact not_none.right
          exact Nat.lt_add_one_of_le lt
        lastElementIndexRec cb ter' (n+1)
      termination_by Classical.choose ter' + 1 - n

  def lastElementIndex (cb : CoreChaseBranch kb) (ter' : cb.terminates') : Nat := lastElementIndexRec cb ter' 0

  @[grind .]
  theorem lastElementIndex_eq_terminatesAtStep_index_leq (cb : CoreChaseBranch kb) (n : Nat) (term_at_n : cb.terminatesAtStep n) : ∀ m, m ≤ n → lastElementIndexRec cb (by exists n) m = n := by
    intro m m_leq
    have ter : cb.terminates := terminates_if_terminates' cb (Exists.intro n term_at_n)
    rcases term_at_n with ⟨lhs, rhs⟩
    have ter' : cb.terminates' := Exists.intro n ⟨lhs, rhs⟩
    unfold lastElementIndexRec
    induction d : (n - m) generalizing m with
      | zero =>
        have eq : m = n := by grind
        rw [eq]
        split
        next => contradiction
        next =>
          unfold lastElementIndexRec
          split
          next => simp
          next x cn heq =>
            rw [rhs] at heq
            contradiction
      | succ n' ih =>
        specialize ih (m + 1) (by grind) (by grind)
        -- m = - n' - 1 + n < n
        split
        next => grind
        next x cn heq =>
          unfold lastElementIndexRec
          rw [ih]

  @[grind .]
  theorem lastElementIndex_eq_terminatesAtStep_eq (cb : CoreChaseBranch kb) (n : Nat) (term_at_n : cb.terminatesAtStep n) : lastElementIndex cb (by exists n) = n := by
    apply lastElementIndex_eq_terminatesAtStep_index_leq
    exact term_at_n
    exact Nat.zero_le n

  @[grind .]
  theorem terminatesAtStep_lastElementIndex (cb : CoreChaseBranch kb) (ter' : cb.terminates') : cb.terminatesAtStep (lastElementIndex cb ter') := by
    rcases ter' with ⟨n, is_some, is_none⟩
    grind

  @[grind .]
  theorem some_at_lastElementIndex (cb : CoreChaseBranch kb) (ter' : cb.terminates') : cb.branch.infinite_list (cb.lastElementIndex ter') ≠ none := by
    rcases ter' with ⟨n, term_at_n⟩
    have := lastElementIndex_eq_terminatesAtStep_eq cb n term_at_n
    rw [this]
    exact term_at_n.left

  def lastNode (cb : CoreChaseBranch kb) (ter' : cb.terminates') : CoreChaseNode kb.rules :=
      have := some_at_lastElementIndex cb ter'
    (cb.branch.infinite_list (lastElementIndex cb ter')).get (by
      exact Option.isSome_iff_ne_none.mpr this
      )

  def result (cb : CoreChaseBranch kb) (ter' : cb.terminates') : FactSet sig :=
    ((cb.branch.infinite_list (lastElementIndex cb ter')).get (by
      have := some_at_lastElementIndex cb ter'
      exact Option.isSome_iff_ne_none.mpr this
      )).core

  @[grind .]
  theorem terminating_index_eq (cb : CoreChaseBranch kb) (m n : Nat) : ((cb.branch.infinite_list n) ≠ none ∧ (cb.branch.infinite_list (n+1) = none) ∧ (cb.branch.infinite_list m) ≠ none ∧ (cb.branch.infinite_list (m+1) = none)) → m = n := by
    rintro ⟨h1, h2, h3, h4⟩
    apply Classical.byContradiction
    intro contra
    have : m > n ∨ m < n := by exact Nat.lt_or_gt_of_ne fun a => contra (id (Eq.symm a))
    rcases this with gt | lt
    have : ∃ k, n + k = m := by
      apply Nat.le.dest
      apply Nat.le_of_lt
      exact gt
    rcases this with ⟨k, add⟩
    induction k with
      | zero =>
        simp only [Nat.add_zero] at add
        rw [add] at contra
        contradiction
      | succ k ih =>
        apply h3
        rw [← add]
        rw [← Nat.add_assoc]
        grind

    have : ∃ k, m + k = n := by
      apply Nat.le.dest
      apply Nat.le_of_lt
      exact lt
    rcases this with ⟨k, add⟩
    induction k with
      | zero =>
        simp only [Nat.add_zero] at add
        rw [add] at contra
        contradiction
      | succ k ih =>
        apply h1
        rw [← add]
        rw [← Nat.add_assoc]
        grind

  @[grind .]
  theorem terminating_has_last_index (cb : CoreChaseBranch kb) : cb.terminates ↔ ∃ n, (cb.branch.infinite_list n) ≠ none ∧ ∀ m, m > n -> cb.branch.infinite_list m = none := by
    unfold CoreChaseBranch.terminates
    constructor
    . intro h
      rcases h with ⟨n, h⟩
      induction n with
      | zero =>
        have := cb.database_first
        grind
      | succ n ih =>
        cases eq : cb.branch.infinite_list n with
        | none => apply ih; exact eq
        | some _ =>
          exists n
          rw [eq]
          simp only [ne_eq, reduceCtorEq, not_false_eq_true, gt_iff_lt, true_and]
          intro m n_lt_m
          have : n+1 ≤ m := by apply Nat.succ_le_of_lt; exact n_lt_m
          rw [Nat.le_iff_lt_or_eq] at this
          cases this with
          | inr n_eq_m => rw [← n_eq_m]; exact h
          | inl n_lt_m =>
            have no_holes := cb.branch.no_holes
            grind

    . intro h
      rcases h with ⟨n, _, h⟩
      exists n+1
      apply h
      simp only [gt_iff_lt, Nat.lt_add_one]

  @[grind .]
  theorem ex_lastNode_if_terminates' (cb : CoreChaseBranch kb) (ter' : cb.terminates') : ∃ cn, cn = cb.lastNode ter' := by
    exists cb.lastNode ter'

  @[grind .]
  theorem ex_result_if_terminates' (cb : CoreChaseBranch kb) (ter' : cb.terminates') : ∃ fs, fs = cb.result ter' := by
    exists cb.result ter'

  @[grind .]
  theorem result_isWeakCore (cb : CoreChaseBranch kb) (ter' : cb.terminates') : (cb.result ter').isWeakCore := by
    unfold CoreChaseBranch.result
    have : ∃ cn, cn = cb.lastNode ter' := by exact ex_lastNode_if_terminates' cb ter'
    rcases this with ⟨cn, cn_last⟩
    unfold lastNode at cn_last
    rw [← cn_last]
    rcases cn with ⟨_,_,_,is_core,_,_,_⟩
    exact is_core

  @[grind .]
    theorem gt_of_terminatesAtStep_index_none (cb : CoreChaseBranch kb) (n : Nat) (term_at_n : cb.terminatesAtStep n) : ∀ m, m > n → cb.branch.infinite_list m = none := by
      intro m gt
      rcases term_at_n with ⟨is_some, is_none⟩
      grind

  @[grind .]
  theorem ex_lastNode_at_lastElementIndex_if_terminates' (cb : CoreChaseBranch kb) (ter' : cb.terminates') : ∃ last_cn, cb.branch.infinite_list (cb.lastElementIndex ter') = some last_cn := by
    exists cb.lastNode ter'
    unfold lastNode
    exact Option.eq_some_of_isSome (by
      have := some_at_lastElementIndex cb ter'
      exact Option.isSome_iff_ne_none.mpr this
      )

  theorem neq_terminates'_if_all_some (cb : CoreChaseBranch kb) : (∀ (n : Nat), (cb.branch.infinite_list n).isSome) → ¬ cb.terminates' := by
    intro all_some ⟨n, ⟨n_some, n_succ_none⟩⟩
    specialize all_some (n + 1)
    rw [Option.isSome_iff_ne_none] at all_some
    contradiction

  @[grind .]
  theorem neq_terminates_iff_all_some (cb : CoreChaseBranch kb) : (∀ (n : Nat), (cb.branch.infinite_list n).isSome) ↔ ¬ cb.terminates := by
    constructor
    intro all_some ⟨n, n_none⟩
    specialize all_some n
    rw [Option.isSome_iff_ne_none] at all_some
    contradiction
    unfold terminates
    intro n_ter
    simp only [not_exists, ne_eq] at n_ter
    intro n
    specialize n_ter n
    rw [Option.isSome_iff_ne_none]
    exact n_ter

  -- this one or the one below this is superfluous
  @[grind .]
  theorem result_finite_if_terminates' (cb : CoreChaseBranch kb) (ter' : cb.terminates') : Set.finite (cb.result ter') := by
    have : ∃ cn, cn = cb.lastNode ter' := by exact ex_lastNode_if_terminates' cb ter'
    rcases this with ⟨cn, cn_eq⟩
    rcases ter' with ⟨n, term_at_n⟩
    exact CoreChaseNode.core_finite ((cb.branch.infinite_list (cb.lastElementIndex (Exists.intro n term_at_n))).get (by
      have := lastElementIndex cb (Exists.intro n term_at_n)
      exact Option.isSome_iff_ne_none.mpr (some_at_lastElementIndex cb (Exists.intro n term_at_n))
      ))

  @[grind .]
  theorem result_isSome (cb : CoreChaseBranch kb) (ter' : cb.terminates') : cb.branch.infinite_list (cb.lastElementIndex ter') = some (cb.lastNode ter') := by
    unfold lastElementIndex lastNode
    exact Option.eq_some_of_isSome (by
      have := some_at_lastElementIndex cb ter'
      exact Option.isSome_iff_ne_none.mpr this
      )

  @[grind .]
  theorem ex_hom_result_if_isSome (cb : CoreChaseBranch kb) (ter' : cb.terminates') (m : Nat) (cn cn_res : CoreChaseNode kb.rules)
    (cn_eq : cn ∈ cb.branch.get? m) (cn_res_eq : cn_res ∈ cb.branch.get? (cb.lastElementIndex ter')) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism cn.fs cn_res.core := by
        rcases ter' with ⟨n, term_at_n⟩
        have ter'_eq : cb.lastElementIndex (Exists.intro n term_at_n : ∃ n, cb.terminatesAtStep n) = n := lastElementIndex_eq_terminatesAtStep_eq cb n term_at_n
        simp only [ter'_eq] at cn_res_eq
        by_cases case : m < n
        · have := ex_hom_core_geq_core cb m cn cn_eq
          specialize this (n - m)
          have eq : m + (n - m) = n := by grind
          rw [← eq] at cn_res_eq
          specialize this cn_res cn_res_eq
          rcases this with ⟨gtm_cn_core_cn_res_core, gtm_cn_core_cn_res_core_hom⟩
          rcases cn.core_sse.right with ⟨gtm_cn_fs_cn_core, gtm_cn_fs_cn_core_hom⟩
          exists (gtm_cn_core_cn_res_core ∘ gtm_cn_fs_cn_core)
          exact GroundTermMapping.isHomomorphism_compose gtm_cn_fs_cn_core gtm_cn_core_cn_res_core cn.fs
              cn.core cn_res.core gtm_cn_fs_cn_core_hom gtm_cn_core_cn_res_core_hom
        · have case : m = n ∨ m > n:= Nat.eq_or_lt_of_not_lt case
          cases case with
            | inl eq =>
              have : cn = cn_res := by grind
              rw [this]
              exact ex_hom_fs_core cb n cn_res cn_res_eq
            | inr gt =>
              have contra := lastElementIndex_eq_terminatesAtStep_index_leq cb n term_at_n m
              unfold lastElementIndex at ter'_eq
              have := gt_of_terminatesAtStep_index_none cb n term_at_n m gt
              grind

  @[grind .]
  theorem succ_lastElementIndex_is_none (cb : CoreChaseBranch kb) (ter' : cb.terminates') : cb.branch.infinite_list ((cb.lastElementIndex ter') + 1) = none := by
    apply Classical.byContradiction
    rcases ter' with ⟨n_ter, n_ter_at⟩
    intro contra
    induction n_ter with
      | zero =>
        grind
      | succ n_ter ih =>
        grind

  @[grind .]
  theorem db_sub_result (cb : CoreChaseBranch kb) (ter' : cb.terminates') : (kb.db.toFactSet.val ⊆ cb.result ter') := by
    let init_node := (cb.branch.infinite_list 0).get (Option.isSome_of_mem cb.database_first)
    rcases (ex_lastNode_at_lastElementIndex_if_terminates' cb ter') with ⟨last_node, last_node_eq⟩
    have t := cb.db_fs_sub_geq_core (cb.lastElementIndex ter') init_node last_node (Option.get_mem (Option.isSome_of_mem cb.database_first))
    intro f f_in
    let := cb.database_first
    have eq : init_node.fs = kb.db.toFactSet.val := by
      have dbf := cb.database_first
      have eq : init_node = cb.branch.get? 0 := Option.some_get (Option.isSome_of_mem cb.database_first)
      grind

    specialize t last_node_eq f (by simp_all)
    rw [result]
    simp_all

  @[grind .]
  theorem result_ModelsKb (cb : CoreChaseBranch kb) (ter' : cb.terminates') : (cb.result ter').modelsKb kb := by
    constructor
    intro f f_in
    have := cb.db_sub_result ter'
    exact this f f_in

    intro r r_in gs sub
    apply Classical.byContradiction
    intro subs_not_obsolete
    let trg : Trigger obs.toLaxObsolescenceCondition := ⟨r, gs⟩
    have trg_loaded : trg.loaded (cb.result ter') := by apply sub
    have trg_not_obsolete : ¬ obs.cond trg (cb.result ter') := by
      intro contra
      have obs_impl_sat := obs.cond_implies_trg_is_satisfied contra
      apply subs_not_obsolete
      rcases obs_impl_sat with ⟨i, s', obs_impl_sat⟩
      exists i

    have trg_act : trg.active (cb.result ter') := by
      unfold Trigger.active
      exact not_imp.mp fun a => subs_not_obsolete (a sub)
    have ex_next_node := cb.ex_next_if_ex_active_trigger (cb.lastElementIndex ter') (cb.lastNode ter') (result_isSome cb ter') ⟨trg, r_in⟩ trg_act

    rcases ex_next_node with ⟨cn_contra,  cn_contra_eq⟩
    have succ_none := succ_lastElementIndex_is_none cb ter'
    have eq : cb.branch.infinite_list (cb.lastElementIndex ter' + 1) = some cn_contra := Option.mem_def.mp cn_contra_eq
    rw [succ_none] at eq
    contradiction

end CoreChaseBranch
