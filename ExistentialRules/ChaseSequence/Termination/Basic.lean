import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.KoenigsLemma

import ExistentialRules.ChaseSequence.ChaseTree

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

section Definitions

  namespace ChaseDerivation
    def terminates {obs : ObsoletenessCondition sig} {rules : RuleSet sig} (cd : ChaseDerivation obs rules) : Prop := cd.branch.finite
  end ChaseDerivation

  namespace TreeDerivation
    def terminates {obs : ObsoletenessCondition sig} {rules : RuleSet sig} (td : TreeDerivation obs rules) : Prop := ∀ branch, branch ∈ td.branches -> branch.terminates
  end TreeDerivation

  namespace KnowledgeBase
    def terminates (kb : KnowledgeBase sig) (obs : ObsoletenessCondition sig) : Prop := ∀ (ct : ChaseTree obs kb), ct.terminates
  end KnowledgeBase

  namespace RuleSet
    def terminates (rs : RuleSet sig) (obs : ObsoletenessCondition sig) : Prop := ∀ (db : Database sig), { rules := rs, db := db : KnowledgeBase sig }.terminates obs
  end RuleSet

end Definitions

section GeneralResults

  namespace ChaseDerivation

    variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

    theorem terminating_has_last_node (cd : ChaseDerivation obs rules) : cd.terminates ↔ ∃ (node : cd.Node), ∀ (node2 : cd.Node), node2 ≼ node := by
      constructor
      . rintro ⟨n, h⟩
        induction n with
        | zero => have contra := cd.isSome_head; rw [PossiblyInfiniteList.head_eq, h] at contra; simp at contra
        | succ n ih =>
          cases eq : cd.branch.get? n with
          | none => apply ih; exact eq
          | some node =>
            let node : cd.Node := ⟨node, by exists n⟩
            exists node
            intro node2
            let d1 := cd.derivation_for_branch_suffix (cd.branch.drop n) (cd.branch.IsSuffix_drop n) (by rw [PossiblyInfiniteList.head_drop]; simp [eq])
            have head_eq1 : d1.head = node.val := by simp [d1, derivation_for_branch_suffix, head, PossiblyInfiniteList.head_drop, eq, node]
            have suf1 : d1 <:+ cd := (cd.branch.IsSuffix_drop n)
            -- TODO: show instead that ≼ is total
            rcases subderivation_of_node_mem node2.property with ⟨d2, head_eq2, suf2⟩
            cases PossiblyInfiniteList.suffix_or_suffix_of_suffix suf1 suf2 with
            | inl suf3 => exists d2; simp only [suf2, head_eq2, true_and]; apply d1.mem_of_mem_suffix suf3; rw [← head_eq1]; exact d1.head_mem
            | inr suf3 =>
              cases ChaseDerivation.suffix_iff_eq_or_suffix_tail.mp suf3 with
              | inl suf3 =>
                have : node = node2 := by rw [Subtype.mk.injEq, ← head_eq2, suf3, head_eq1]
                rw [this]
                exact ChaseDerivation.predecessor_refl
              | inr suf3 =>
                rcases suf3 with ⟨contra, suf3⟩
                apply False.elim
                unfold next at contra
                rw [Option.isSome_iff_ne_none] at contra
                apply contra
                simp only [d1, derivation_for_branch_suffix, PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop]
                exact h
      . rintro ⟨node, all_pred⟩
        rcases node.property with ⟨n, node_eq⟩
        exists n+1
        apply Decidable.byContradiction
        intro ne_none
        rw [← ne_eq, Option.ne_none_iff_exists'] at ne_none
        rcases ne_none with ⟨next, next_eq⟩
        let next_node : cd.Node := ⟨next, by exists n+1⟩
        specialize all_pred next_node
        let d1 := cd.derivation_for_branch_suffix (cd.branch.drop n) (cd.branch.IsSuffix_drop n) (by simp [PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?, node_eq])
        have head_eq1 : d1.head = node.val := by simp [d1, derivation_for_branch_suffix, head, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?, node_eq]
        have suf1 : d1 <:+ cd := (cd.branch.IsSuffix_drop n)
        have next_d1 : d1.next = some next := by rw [← next_eq]; simp [d1, derivation_for_branch_suffix, ChaseDerivation.next, PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop]
        have node_pred_next : node ≼ next_node := by exists d1; simp only [head_eq1, suf1, true_and]; apply d1.next_mem_of_mem; exact next_d1
        have node_eq_next : node = next_node := cd.predecessor_antisymm node_pred_next all_pred
        apply d1.head_not_mem_tail
        rw [d1.mem_tail_iff];
        . exists d1; constructor; exact d1.branch.IsSuffix_refl; rw [next_d1, head_eq1, node_eq_next]
        . simp [next_d1]

  end ChaseDerivation

  namespace ChaseBranch

    variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

    theorem terminates_iff_result_finite (cb : ChaseBranch obs kb) : cb.terminates ↔ cb.result.finite := by
      constructor
      . intro terminates
        rcases cb.terminating_has_last_node.mp terminates with ⟨node, all_pred⟩
        have : cb.result ⊆ node.val.facts := by
          rintro f ⟨node2, node2_mem, f_mem⟩
          apply cb.facts_node_subset_of_prec (all_pred ⟨node2, node2_mem⟩)
          exact f_mem
        apply Set.finite_of_subset_finite _ this
        apply cb.facts_finite_of_mem
      . rintro ⟨l, _, l_eq⟩
        rw [cb.terminating_has_last_node]
        rcases cb.facts_mem_some_node_of_mem_result l (by intro _ mem; rw [List.mem_toSet, l_eq] at mem; exact mem) with ⟨node, node_mem, l_sub⟩
        exists ⟨node, node_mem⟩
        intro node2
        -- TODO: show instead that ≼ is total
        rcases cb.subderivation_of_node_mem node_mem with ⟨d1, head_eq1, suf1⟩
        rcases cb.subderivation_of_node_mem node2.property with ⟨d2, head_eq2, suf2⟩
        cases PossiblyInfiniteList.suffix_or_suffix_of_suffix suf1 suf2 with
        | inl suf3 => exists d2; simp only [suf2, head_eq2, true_and]; apply d1.mem_of_mem_suffix suf3; rw [← head_eq1]; exact d1.head_mem
        | inr suf3 =>
          cases ChaseDerivation.suffix_iff_eq_or_suffix_tail.mp suf3 with
          | inl suf3 =>
            have : ⟨node, node_mem⟩ = node2 := by rw [Subtype.mk.injEq, ← head_eq2, suf3, head_eq1]
            rw [this]
            exact ChaseDerivation.predecessor_refl
          | inr suf3 =>
            rcases suf3 with ⟨contra, suf3⟩
            apply False.elim
            rw [Option.isSome_iff_exists] at contra
            rcases contra with ⟨next, contra⟩
            have active := d1.active_trigger_origin_next contra
            apply active.right
            apply ObsoletenessCondition.contains_trg_result_implies_cond
            have : next.facts ⊆ d1.head.facts := by
              have : ⟨next, d1.next_mem_of_mem _ contra⟩ ≼ ⟨node2.val, by apply ChaseDerivation.mem_of_mem_suffix (d2.branch.IsSuffix_trans suf3 d1.branch.IsSuffix_tail); rw [← head_eq2]; exact d2.head_mem⟩ := by
                exists d1.tail (by simp [contra])
                constructor
                . exact PossiblyInfiniteList.IsSuffix_tail
                constructor
                . simp [d1.head_tail', contra]
                . apply ChaseDerivation.mem_of_mem_suffix suf3; rw [← head_eq2]; exact d2.head_mem
              apply Set.subset_trans (d1.facts_node_subset_of_prec this)
              apply Set.subset_trans (cb.facts_node_subset_result _ node2.property)
              rw [head_eq1]
              apply Set.subset_trans _ l_sub
              intro _ mem; rw [List.mem_toSet, l_eq]; exact mem
            exact Set.subset_trans (by rw [d1.facts_next contra]; apply Set.subset_union_of_subset_right; apply Set.subset_refl) this

  end ChaseBranch

  namespace TreeDerivation

    variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

    theorem finitely_many_branch_of_terminates (td : TreeDerivation obs rules) : td.terminates -> td.branches.finite := by
      intro each_b_term

      have : ∀ b, b ∈ td.tree.branches -> b.finite := by
        intro b b_mem
        exact each_b_term (td.derivation_for_branch b b_mem) b_mem

      -- Koenig's Lemma
      rcases (td.tree.branches_finite_of_each_branch_finite this) with ⟨l, _, l_eq⟩

      have decEq := Classical.typeDecidableEq (ChaseDerivation obs rules)
      apply Set.finite_of_list_with_same_elements (l.attach.map (fun ⟨b, b_mem⟩ => td.derivation_for_branch b (by rw [← l_eq]; exact b_mem)))

      intro branch
      unfold branches
      simp only [List.mem_map, List.mem_attach, true_and]
      constructor
      . rintro ⟨⟨b, b_mem⟩, branch_eq⟩; simp only [← branch_eq, ← l_eq]; exact b_mem
      . intro branch_mem; exists ⟨branch.branch, by rw [l_eq]; exact branch_mem⟩

    theorem result_finite_of_branches_finite (td : TreeDerivation obs rules) : td.branches.finite -> td.result.finite := by
      rintro ⟨l, _, iff⟩
      have : DecidableEq (FactSet sig) := Classical.typeDecidableEq (FactSet sig)
      apply Set.finite_of_list_with_same_elements (l.map ChaseDerivation.result)
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

  end TreeDerivation

  namespace ChaseTree

    variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

    theorem terminates_iff_result_finite (ct : ChaseTree obs kb) : ct.terminates ↔ ∀ fs, fs ∈ ct.result -> fs.finite := by
      constructor
      . rintro each_b_term res ⟨b, mem, eq⟩
        let b' := ChaseTree.chaseBranch_for_branch mem
        have : b'.result = b.result := rfl
        rw [← eq, ← this]
        rw [← ChaseBranch.terminates_iff_result_finite]
        apply each_b_term
        exact mem
      . intro each_b_term b mem
        let b' := ChaseTree.chaseBranch_for_branch mem
        have : b'.terminates ↔ b.terminates := by rfl
        rw [← this]
        rw [ChaseBranch.terminates_iff_result_finite]
        apply each_b_term
        exists b

  end ChaseTree

end GeneralResults

