import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.KoenigsLemma

import ExistentialRules.ChaseSequence.Basic

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

section Definitions

  namespace ChaseBranch
    def terminates (branch : ChaseBranch obs kb) : Prop := branch.branch.finite
  end ChaseBranch

  namespace ChaseTree
    def terminates (ct : ChaseTree obs kb) : Prop := ∀ branch, branch ∈ ct.branches -> branch.terminates
  end ChaseTree

  namespace KnowledgeBase
    def terminates (kb : KnowledgeBase sig) (obs : ObsoletenessCondition sig) : Prop := ∀ (ct : ChaseTree obs kb), ct.terminates
  end KnowledgeBase

  namespace RuleSet
    def terminates (rs : RuleSet sig) (obs : ObsoletenessCondition sig) : Prop := ∀ (db : Database sig), { rules := rs, db := db : KnowledgeBase sig }.terminates obs
  end RuleSet

end Definitions

section GeneralResults

  namespace ChaseBranch

    theorem terminating_has_last_index (branch : ChaseBranch obs kb) : branch.terminates ↔ ∃ n, (branch.branch.get? n).isSome ∧ ∀ m, m > n -> branch.branch.get? m = none := by
      unfold ChaseBranch.terminates
      constructor
      . rintro ⟨n, h⟩
        induction n with
        | zero => rw [← PossiblyInfiniteList.head_drop, PossiblyInfiniteList.drop_zero, branch.database_first] at h; simp at h
        | succ n ih =>
          cases eq : branch.branch.get? n with
          | none => apply ih; exact eq
          | some _ =>
            exists n
            simp only [eq, Option.isSome_some, true_and]
            intro m lt
            apply PossiblyInfiniteList.get?_eq_none_of_le_of_eq_none
            . exact h
            . exact Nat.succ_le_of_lt lt
      . rintro ⟨n, _, h⟩
        exists n+1
        apply h
        simp

    theorem terminates_iff_result_finite (branch : ChaseBranch obs kb) : branch.terminates ↔ branch.result.finite := by
      constructor
      . intro h
        rcases (terminating_has_last_index branch).mp h with ⟨n, h⟩
        rw [Option.isSome_iff_exists] at h
        rcases h.left with ⟨node, eq⟩
        rcases node.facts.property with ⟨l, _, l_eq⟩
        apply Set.finite_of_list_with_same_elements l
        intro f; rw [l_eq]
        constructor
        . have := branch.stepIsSubsetOfResult n
          simp only [eq, Option.is_none_or] at this
          apply this
        . rintro ⟨m, h⟩
          rw [Option.is_some_and_iff] at h
          rcases h with ⟨node2, eq2, f_mem⟩
          have le : m ≤ n := by
            apply Decidable.byContradiction
            intro contra; have contra := Nat.lt_of_not_le contra
            rw [h.right m contra] at eq2; simp at eq2
          have := branch.stepIsSubsetOfAllFollowing m node2 eq2 (n-m)
          simp only [PossiblyInfiniteList.get?_drop, Nat.add_sub_of_le le, eq, Option.is_none_or] at this
          apply this
          exact f_mem
      . rintro ⟨l, _, l_eq⟩
        have : ∀ (l : List (Fact sig)), (∀ e, e ∈ l -> ∃ n, (branch.branch.get? n).is_some_and (fun fs => e ∈ fs.facts.val)) ->
            (∃ n, (branch.branch.get? n).is_some_and (fun fs => ∀ e, e ∈ l -> e ∈ fs.facts.val)) := by
          intro l
          induction l with
          | nil => simp only [List.not_mem_nil, false_implies, implies_true, forall_const]; exists 0; rw [← PossiblyInfiniteList.head_drop, PossiblyInfiniteList.drop_zero, branch.database_first]; simp [Option.is_some_and]
          | cons hd tl ih =>
            intro h
            specialize ih (by intro _ e_mem; apply h; simp [e_mem])
            simp only [Option.is_some_and_iff] at ih
            rcases ih with ⟨n_ih, _, eq_n_ih, ih⟩
            specialize h hd (by simp)
            simp only [Option.is_some_and_iff] at h
            rcases h with ⟨n_hd, _, eq_n_hd, h⟩
            exists max n_ih n_hd
            cases Decidable.em (n_ih ≤ n_hd) with
            | inl n_ih_le_n_hd =>
              rw [Nat.max_eq_right n_ih_le_n_hd]
              rw [eq_n_hd]; simp [Option.is_some_and]
              constructor
              . exact h
              . have subs_following := ChaseBranch.stepIsSubsetOfAllFollowing branch n_ih _ eq_n_ih (n_hd - n_ih)
                rw [PossiblyInfiniteList.get?_drop, Nat.add_sub_of_le n_ih_le_n_hd] at subs_following
                rw [eq_n_hd] at subs_following
                simp only [Option.is_none_or] at subs_following
                intro e e_mem_tl
                apply subs_following
                apply ih
                exact e_mem_tl
            | inr n_ih_not_le_n_hd =>
              have n_hd_le_n_ih : n_hd ≤ n_ih := by apply Nat.le_of_lt; apply Nat.lt_of_not_le; exact n_ih_not_le_n_hd
              rw [Nat.max_eq_left n_hd_le_n_ih]
              rw [eq_n_ih]; simp [Option.is_some_and]
              constructor
              . have subs_following := ChaseBranch.stepIsSubsetOfAllFollowing branch n_hd _ eq_n_hd (n_ih - n_hd)
                rw [PossiblyInfiniteList.get?_drop, Nat.add_sub_of_le n_hd_le_n_ih] at subs_following
                rw [eq_n_ih] at subs_following
                simp only [Option.is_none_or] at subs_following
                apply subs_following
                exact h
              . exact ih
        rcases this l (by intro e; exact (l_eq e).mp) with ⟨n, this⟩
        rw [Option.is_some_and_iff] at this; rcases this with ⟨node, node_eq, this⟩
        exists n+1
        have trg_ex := branch.triggers_exist n
        simp only [PossiblyInfiniteList.head_drop, node_eq, Option.is_none_or] at trg_ex
        cases trg_ex with
        | inr trg_ex => have trg_ex := trg_ex.right; rw [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop] at trg_ex; exact trg_ex
        | inl trg_ex =>
          rcases trg_ex with ⟨trg, trg_act, i, trg_res⟩
          apply False.elim
          apply trg_act.right
          apply obs.contains_trg_result_implies_cond i
          intro f f_mem
          apply this
          rw [l_eq]
          exists n+1
          rw [PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop] at trg_res;
          simp only [← trg_res, Option.is_some_and]
          apply Or.inr; exact f_mem

  end ChaseBranch

  namespace ChaseTree

    theorem finitely_many_branch_of_terminates (ct : ChaseTree obs kb) : ct.terminates -> ct.branches.finite := by
      intro each_b_term

      have : ∀ b, b ∈ ct.tree.branches -> b.finite := by
        intro b b_mem
        exact each_b_term (ct.chase_branch_for_tree_branch b b_mem) b_mem

      -- Koenig's Lemma
      rcases (ct.tree.branches_finite_of_each_branch_finite this) with ⟨l, _, l_eq⟩

      have decEq := Classical.typeDecidableEq (ChaseBranch obs kb)
      apply Set.finite_of_list_with_same_elements (l.attach.map (fun ⟨b, b_mem⟩ => ct.chase_branch_for_tree_branch b (by rw [← l_eq]; exact b_mem)))

      intro branch
      unfold branches
      unfold chase_branch_for_tree_branch
      simp only [List.mem_map, List.mem_attach, true_and]
      constructor
      . rintro ⟨⟨b, b_mem⟩, branch_eq⟩; simp only [← branch_eq, ← l_eq]; exact b_mem
      . intro branch_mem; exists ⟨branch.branch, by rw [l_eq]; exact branch_mem⟩

    theorem result_finite_of_branches_finite (ct : ChaseTree obs kb) : ct.branches.finite -> ct.result.finite := by
      intro bs_finite
      unfold Set.finite at bs_finite
      rcases bs_finite with ⟨l, _, iff⟩
      have : DecidableEq (FactSet sig) := Classical.typeDecidableEq (FactSet sig)
      apply Set.finite_of_list_with_same_elements (l.map ChaseBranch.result)
      intro fs
      rw [List.mem_map]
      constructor
      . rintro ⟨b, mem, eq⟩
        exists b
        constructor
        . rw [← iff]; exact mem
        . exact eq
      . rintro ⟨b, mem, eq⟩
        exists b
        constructor
        . rw [iff]; exact mem
        . exact eq

    theorem terminates_iff_result_finite (ct : ChaseTree obs kb) : ct.terminates ↔ ∀ fs, fs ∈ ct.result -> fs.finite := by
      unfold terminates
      unfold result
      constructor
      . rintro each_b_term res ⟨b, mem, eq⟩
        rw [← eq]
        rw [← ChaseBranch.terminates_iff_result_finite]
        apply each_b_term
        exact mem
      . intro each_b_term b mem
        rw [ChaseBranch.terminates_iff_result_finite]
        apply each_b_term
        exists b

  end ChaseTree

end GeneralResults

