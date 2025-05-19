import ExistentialRules.ChaseSequence.ChaseBranch
import ExistentialRules.ChaseSequence.CoreChase.Homomorphisms
import ExistentialRules.ChaseSequence.CoreChase.Basic
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


def existsTriggerOptFsPsd (obs : ObsolescenceCondition sig) (rules : RuleSet sig) (before : RegularChaseNode obs rules) (after : Option (RegularChaseNode obs rules)) : Prop :=
  ∀ node ∈ after,
  ∃ trg : (RTrigger (obs : LaxObsolescenceCondition sig) rules),
  ∃ i,
  node = {
    facts := before.facts ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet,
    origin := some ⟨trg, i⟩
    facts_contain_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
  }

structure PseudoCoreChaseBranch (kb : KnowledgeBase sig) where
  branch : PossiblyInfiniteList (RegularChaseNode obs kb.rules)
  database_first : branch.get? 0 = some {
    facts := kb.db.toFactSet
    origin := none
    facts_contain_origin_result := by simp
  }

  triggers_active : ∀ n : Nat, ∀ before ∈ (branch.drop n).head,
    ∀ after ∈ (branch.drop n).tail.head, ∃ orig ∈ after.origin, orig.fst.val.active before.facts

  triggers_exist : ∀ n : Nat, ∀ before ∈ (branch.drop n).head,
    let after := (branch.drop n).tail.head
    (existsTriggerOptFsPsd obs kb.rules before after)

  fairness : ∀ trg : (RTrigger obs.toLaxObsolescenceCondition kb.rules), ∃ i : Nat, (∃ node ∈ (branch.drop i).head, ¬ trg.val.active node.facts)
    ∧ (∀ j : Nat, ∀ node2 ∈ (branch.drop i).tail.get? j, ¬ trg.val.active node2.facts)


  last_index : Nat

  terminates_at : ∀ m, m > last_index → (branch.get? last_index).isSome ∧ (branch.get? m).isNone

  core_node : CoreChaseNode kb.rules
  core_node_eq :
    let last_node : RegularChaseNode obs kb.rules := (branch.get? last_index).get (terminates_at (last_index + 1) (Nat.lt_add_one last_index)).left

    have fs_fin : last_node.facts.finite := by
      have : ∀ (m : Nat), ∀ cn, cn ∈ branch.get? m → cn.facts.finite := by
        intro m cn cn_eq
        induction m generalizing cn with
          | zero =>
            grind
          | succ m ih =>
            have : ∀ k, k ≤ last_index → ∃ cm, cm ∈ (branch.get? k) := by
              intro k geq
              have : ∀ l, l ≤ last_index → (branch.get? l).isSome := by
                intro l geq
                have := (terminates_at (last_index + 1) (Nat.lt_add_one last_index)).left
                grind
              specialize this k geq
              exact Option.isSome_iff_exists.mp this

            have is_some : (branch.get? m).isSome := by grind
            specialize this m (by
              apply Classical.byContradiction
              intro contra
              grind
            )
            rcases this with ⟨cm, cm_eq⟩
            specialize ih cm cm_eq
            specialize triggers_exist m cm cm_eq cn cn_eq
            rcases triggers_exist with ⟨trg, i, eq⟩
            have : cn.facts = cm.facts ∪ trg.val.mapped_head[↑i].toSet := by rw [eq]; rfl
            rw [this]
            apply Set.union_finite_of_both_finite
            exact ih
            exact List.finite_toSet trg.val.mapped_head[i]
      exact this last_index last_node
        (Option.get_mem (terminates_at (last_index + 1) (Nat.lt_add_one last_index)).left)



    have ex_wc : ∃ (wc: FactSet sig), wc.isWeakCore ∧ wc.homSubset last_node.facts := last_node.facts.exists_weak_core_for_finite_set fs_fin

    core_node = {

    fs := last_node.facts
    fs_fin := fs_fin
    core := Classical.choose ex_wc
    is_core := (Classical.choose_spec ex_wc).left
    core_sse := (Classical.choose_spec ex_wc).right
    origin := last_node.origin
    fs_contains_origin_result := by
      cases c : last_node.origin with
        | none =>
          simp
        | some o =>
          intro o2 eq
          rw [Option.mem_def, Option.some_inj] at eq
          rw [← eq];
          exact last_node.facts_contain_origin_result o c
  }


namespace PseudoCoreChaseBranch


  instance : Membership (RegularChaseNode obs kb.rules) (PseudoCoreChaseBranch kb) where
  mem cd node := node ∈ cd.branch

  theorem mem_iff {cd : PseudoCoreChaseBranch kb} : ∀ {e}, e ∈ cd ↔ ∃ n, cd.branch.get? n = some e := by rfl

  def last_node (psc : PseudoCoreChaseBranch kb) : RegularChaseNode obs kb.rules :=
    (psc.branch.get? psc.last_index).get (psc.terminates_at (psc.last_index + 1) (Nat.lt_add_one psc.last_index)).left

  def buildPseudoCoreChaseBranchFromTerminatingChaseBranch (scb : RegularChaseBranch obs kb) (last_index : Nat)
    (term_at_n : (scb.branch.infinite_list last_index).isSome ∧ (scb.branch.infinite_list (last_index+1)).isNone) : PseudoCoreChaseBranch kb :=
      let last_node : RegularChaseNode obs kb.rules := (scb.branch.get? last_index).get (term_at_n.left)

      have fs_fin : last_node.facts.finite := by
        have : ∀ (m : Nat), ∀ cn, cn ∈ scb.branch.get? m → cn.facts.finite := by
          intro m cn cn_eq
          induction m generalizing cn with
            | zero =>
              grind
            | succ m ih =>
              have : ∀ k, k ≤ last_index → ∃ cm, cm ∈ (scb.branch.get? k) := by
                intro k geq
                have : ∀ l, l ≤ last_index → (scb.branch.get? l).isSome := by
                  intro l geq
                  have := term_at_n.left
                  exact scb.leq_some_if_some last_index this l geq
                specialize this k geq
                exact Option.isSome_iff_exists.mp this
              have is_some : (scb.branch.get? m).isSome := by grind
              specialize this m (by
                apply Classical.byContradiction
                intro contra
                have contra : m > last_index := Nat.lt_of_not_le contra
                have := term_at_n.right
                have all_succ_none : ∀ m, m ≥ (last_index + 1) → (scb.branch.get? m).isNone := by
                  intro m geq
                  have nh := scb.branch.no_holes' (last_index + 1) (Option.isNone_iff_eq_none.mp this)
                  have geq : m = last_index + 1 ∨ m > last_index + 1 := by grind
                  cases geq with
                    | inl eq =>
                      rw [eq]
                      exact Bool.eq_false_imp_eq_true.mp fun a => this
                    | inr gt =>
                      exact scb.geq_none_if_none (last_index + 1) this m geq
                grind
                )
              rcases this with ⟨cm, cm_eq⟩
              specialize ih cm cm_eq
              have trg_ex := scb.triggers_exist m cm cm_eq cn cn_eq
              rcases trg_ex with ⟨isSome, eq⟩
              rw [cn.ingoingFacts_eq, cm.outgoingFacts_eq] at eq
              rw [eq]
              apply Set.union_finite_of_both_finite
              exact ih
              exact List.finite_toSet _
        exact this last_index last_node (Option.get_mem term_at_n.left)


      have ex_wc : ∃ (wc: FactSet sig), wc.isWeakCore ∧ wc.homSubset last_node.facts := last_node.facts.exists_weak_core_for_finite_set fs_fin

    {
      branch := scb.branch
      database_first := sorry -- scb.database_first
      triggers_active := scb.triggers_active
      triggers_exist := sorry -- scb.triggers_exist
      fairness := scb.fairness
      last_index := last_index
      terminates_at := by
        intro m gt
        constructor
        · exact term_at_n.left
        · exact scb.geq_none_if_none (last_index+1) term_at_n.right m (Nat.succ_le_of_lt gt)
      core_node := {
        fs := last_node.facts
        fs_fin := fs_fin
        core := Classical.choose ex_wc
        is_core := (Classical.choose_spec ex_wc).left
        core_sse := (Classical.choose_spec ex_wc).right
        origin := last_node.origin
        fs_contains_origin_result := by
          cases c : last_node.origin with
          | none =>
            simp
          | some o =>
            intro o2 eq
            rw [Option.mem_def, Option.some_inj] at eq
            rw [← eq];
            exact last_node.facts_contain_origin_result o c
      }
      core_node_eq := by
        grind

    }

  @[grind .]
  theorem psc_core_node_fs_eq (psc : PseudoCoreChaseBranch kb) : psc.core_node.fs = psc.last_node.facts := by
    have := psc.core_node_eq
    apply Set.ext
    intro f
    simp at this
    constructor
    intro f_in
    rw [this] at f_in
    exact Set.mem_of_subset_of_mem (fun e a => a) f_in
    intro f_in
    rw [this]
    exact Set.mem_of_subset_of_mem (fun e a => a) f_in


  @[grind .]
  theorem buildPseudoCoreChaseBranchFromTerminatingChaseBranch_branch_eq (scb : RegularChaseBranch obs kb) (last_index : Nat)
    (term_at_n : (scb.branch.infinite_list last_index).isSome ∧ (scb.branch.infinite_list (last_index+1)).isNone) (psc : PseudoCoreChaseBranch kb)
    (psc_eq : psc = buildPseudoCoreChaseBranchFromTerminatingChaseBranch scb last_index term_at_n) : psc.branch = scb.branch := by
      unfold buildPseudoCoreChaseBranchFromTerminatingChaseBranch at psc_eq
      rw [psc_eq]


  @[grind .]
  theorem core_node_buildPseudoCoreChaseBranchFromTerminatingChaseBranch_models_kb (scb : RegularChaseBranch obs kb) (last_index : Nat)
    (term_at_n : (scb.branch.infinite_list last_index).isSome ∧ (scb.branch.infinite_list (last_index+1)).isNone) (psc : PseudoCoreChaseBranch kb)
    (psc_eq : psc = buildPseudoCoreChaseBranchFromTerminatingChaseBranch scb last_index term_at_n) : psc.core_node.core.modelsKb kb := by

      have scb_mod := scb.result_models_kb
      have eq : scb.result = psc.last_node.facts := by sorry

      rw [eq] at scb_mod
      have := psc.core_node.core_sse
      rw [psc_core_node_fs_eq] at this
      sorry


  noncomputable def buildPseudoCoreChaseBranchFromChaseBranch (scb : RegularChaseBranch obs kb) (scb_term : scb.terminates) : PseudoCoreChaseBranch kb :=

    have : ∃ (n : Nat), (scb.branch.infinite_list n).isSome ∧ (scb.branch.infinite_list (n+1)).isNone := by
      have := scb.terminating_has_last_index
      rw [this] at scb_term
      rcases scb_term with ⟨n_ter, eq⟩
      exists n_ter
      grind


    let scb_term_n := Classical.choose this
    let scb_term_h := Classical.choose_spec this
    let last_scn := ((scb.branch.get? scb_term_n).get (scb_term_h.left))

    have fs_fin : last_scn.facts.finite := by
      have : ∀ (m : Nat), ∀ cn, cn ∈ scb.branch.get? m → cn.facts.finite := by
        intro m cn cn_eq
        induction m generalizing cn with
          | zero =>
            grind
          | succ m ih =>
            have : ∀ k, k ≤ scb_term_n → ∃ cm, cm ∈ (scb.branch.get? k) := by
              intro k geq
              have : ∀ l, l ≤ scb_term_n → (scb.branch.get? l).isSome := by
                intro l geq
                have := scb_term_h.left
                exact scb.leq_some_if_some scb_term_n this l geq
              specialize this k geq
              exact Option.isSome_iff_exists.mp this
            have is_some : (scb.branch.get? m).isSome := by grind
            specialize this m (by
              apply Classical.byContradiction
              intro contra
              have contra : m > scb_term_n := Nat.lt_of_not_le contra
              have := scb_term_h.right
              have all_succ_none : ∀ m, m ≥ (scb_term_n + 1) → (scb.branch.get? m).isNone := by
                intro m geq
                have nh := scb.branch.no_holes' (scb_term_n + 1) (Option.isNone_iff_eq_none.mp this)
                have geq : m = scb_term_n + 1 ∨ m > scb_term_n + 1 := by grind
                cases geq with
                  | inl eq =>
                    rw [eq]
                    exact Bool.eq_false_imp_eq_true.mp fun a => this
                  | inr gt =>
                    exact scb.geq_none_if_none (scb_term_n + 1) this m geq
              grind
              )
            rcases this with ⟨cm, cm_eq⟩
            specialize ih cm cm_eq
            have trg_ex := scb.triggers_exist m cm cm_eq cn cn_eq
            rcases trg_ex with ⟨isSome, eq⟩
            rw [cn.ingoingFacts_eq, cm.outgoingFacts_eq] at eq
            rw [eq]
            apply Set.union_finite_of_both_finite
            exact ih
            exact List.finite_toSet _
      exact this scb_term_n last_scn (Option.get_mem scb_term_h.left)

    have ex_wc : ∃ (wc: FactSet sig), wc.isWeakCore ∧ wc.homSubset last_scn.facts :=
      ((scb.branch.get? scb_term_n).get (scb_term_h.left)).facts.exists_weak_core_for_finite_set fs_fin
    {
      branch := scb.branch
      database_first := sorry -- scb.database_first
      triggers_active := scb.triggers_active
      triggers_exist := sorry -- scb.triggers_exist
      fairness := scb.fairness
      last_index := scb_term_n
      terminates_at := by
        intro m gt
        subst scb_term_n
        constructor
        exact scb_term_h.left

        have all_succ_none : ∀ k, k ≥ ((Classical.choose this) + 1) → (scb.branch.get? k).isNone := by
          intro k geq
          have nh := scb.branch.no_holes' ((Classical.choose this) + 1) (Option.isNone_iff_eq_none.mp scb_term_h.right)
          have geq : k = (Classical.choose this) + 1 ∨ k > (Classical.choose this) + 1 := by grind
          cases geq with
            | inl eq =>
              rw [eq]
              exact Bool.eq_false_imp_eq_true.mp fun a => scb_term_h.right
            | inr gt =>
              exact scb.geq_none_if_none ((Classical.choose this) + 1) scb_term_h.right k (Nat.le_of_succ_le gt)
        grind

      core_node := {
        fs := last_scn.facts
        fs_fin := fs_fin
        core := Classical.choose ex_wc
        is_core := (Classical.choose_spec ex_wc).left
        core_sse := (Classical.choose_spec ex_wc).right
        origin := last_scn.origin
        fs_contains_origin_result := by
          cases c : last_scn.origin with
          | none =>
            simp
          | some o =>
            intro o2 eq
            rw [Option.mem_def, Option.some_inj] at eq
            rw [← eq];
            exact last_scn.facts_contain_origin_result o c
        }

      core_node_eq := by grind
    }

end PseudoCoreChaseBranch
