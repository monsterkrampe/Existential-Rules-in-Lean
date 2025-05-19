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

import ExistentialRules.ChaseSequence.CoreChase.Util
import ExistentialRules.ChaseSequence.CoreChase.Basic


import ExistentialRules.ChaseSequence.CoreChase.CoreChaseNode



variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}

theorem ex_fact_for_term (kb : KnowledgeBase sig) (t : GroundTerm sig) : t ∈ kb.db.toFactSet.val.terms → ∃ f, f ∈ kb.db.toFactSet.val := by
  intro ⟨f, f_in_fs, f_in_ter⟩
  exists f

@[grind .]
theorem db_isWeakCore (kb : KnowledgeBase sig) : kb.db.toFactSet.val.isWeakCore := by
  let db := kb.db
  let fs := db.val
  intro gtm gtm_hom
  constructor
  · intro f gt h contra
    have eq : gtm.applyFact f = f := by
      unfold GroundTermMapping.applyFact
      rw [GeneralizedAtom.mk.injEq]
      constructor
      · rfl
      · apply List.map_id_of_id_on_all_mem
        intro e e_in
        unfold GroundTermMapping.isHomomorphism at gtm_hom
        specialize gt e e_in
        rcases gt with ⟨f2, f2_mem, e_mem⟩
        have db_funfree := kb.db.toFactSet.property.right
        specialize db_funfree f2 f2_mem e e_mem
        rcases db_funfree with ⟨c, c_eq⟩
        rw [c_eq]
        exact @gtm_hom.left c
    rw [eq] at contra
    · contradiction
  -- id is injective
  intro a b a_in b_in eq
  have a_mem : ∃ fa, fa ∈ kb.db.toFactSet.val := ex_fact_for_term kb a a_in
  rcases a_mem with ⟨fa, fa_in⟩
  have gtm_eq : ∀ f, f ∈ kb.db.toFactSet.val → gtm.applyFact f = f := by exact fun f a => GroundTermMapping.hom_on_db_id f gtm gtm_hom a
  specialize gtm_eq fa fa_in
  have gt_eq : ∀ t, t ∈ kb.db.toFactSet.val.terms → gtm t = t := by exact fun t a => GroundTermMapping.hom_on_db_term_id t gtm gtm_hom a
  rw [gt_eq, gt_eq] at eq
  exact eq
  exact b_in
  exact a_in

def existsTriggerOptFsCore (rules : RuleSet sig) (before : CoreChaseNode rules) (after : Option (CoreChaseNode rules)) : Prop :=
  ∀ node ∈ after,
  ∃ trg : (RTrigger (obs.toLaxObsolescenceCondition) rules),
  ∃ (i : Fin trg.val.mapped_head.length),
  ∃ (c : FactSet sig),
  ∃ (c_wc : c.isWeakCore),
  ∃ (c_sub : c.homSubset (before.core ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet)),

    node = {
      fs := before.core ∪ (trg.val.mapped_head[i.val]'(i.isLt)).toSet
      fs_fin := by
        apply Set.union_finite_of_both_finite
        exact CoreChaseNode.core_finite_if_fs_finite before before.fs_fin
        exact List.finite_toSet trg.val.mapped_head[↑i]
      core := c
      is_core := c_wc
      core_sse := c_sub
      origin := some ⟨trg, i⟩
      fs_contains_origin_result := by intro _ eq; rw [Option.mem_def, Option.some_inj] at eq; rw [← eq]; apply Set.subset_union_of_subset_right; apply Set.subset_refl
    }

structure CoreChaseBranch (kb : KnowledgeBase sig) where
  branch : PossiblyInfiniteList (CoreChaseNode kb.rules)
  database_first : branch.get? 0 = some {
    fs := kb.db.toFactSet
    fs_fin := kb.db.toFactSet.property.left
    core := kb.db.toFactSet
    is_core := db_isWeakCore kb
    core_sse := by
      constructor
      · exact Set.subset_refl
      · exists id
        exact GroundTermMapping.id_is_hom
    origin := none,
    fs_contains_origin_result := by simp
  }

  triggers_active : ∀ (n : Nat), ∀ before ∈ branch.get? n, ∀ after ∈ branch.get? (n+1), ∃ o ∈ after.origin, o.fst.val.active before.core

  triggers_exist : ∀ n : Nat, ∀ before ∈ branch.get? n,
    let after := branch.get? (n+1)
    (existsTriggerOptFsCore kb.rules before after)

  fairness : ∀ trg : (RTrigger obs.toLaxObsolescenceCondition kb.rules), ∃ (i : Nat), (∃ node ∈ branch.get? i, ¬ trg.val.active node.fs)
    ∧ (∀ (j : Nat), j > i → ∀ node2  ∈ branch.get? j, ¬ trg.val.active node2.fs)



namespace CoreChaseBranch

  instance : Membership (CoreChaseNode kb.rules) (CoreChaseBranch kb) where
  mem cb node := node ∈ cb.branch

  instance : Membership (CoreChaseNode kb.rules) (CoreChaseBranch kb) where
  mem cb node := node ∈ cb


  def inCoreChaseBranch (fs : FactSet sig) (cb : CoreChaseBranch kb) : Prop :=
    ∃ n : Nat, ∃ x,
      cb.branch.infinite_list n = some x ∧ (fs = x.fs ∨ fs = x.core)

  def inCoreChaseBranch.fsOnly (fs : FactSet sig) (cb : CoreChaseBranch kb) : Prop :=
  ∃ n x,
    cb.branch.infinite_list n = some x ∧
    fs = x.fs

  def inCoreChaseBranch.coreOnly (fs : FactSet sig) (cb : CoreChaseBranch kb) : Prop :=
  ∃ n x,
    cb.branch.infinite_list n = some x ∧
    fs = x.core

  instance : Membership (FactSet sig) (CoreChaseBranch kb) :=
    ⟨fun fs cb => inCoreChaseBranch cb fs⟩

  infix:50 " ∈_fs " => inCoreChaseBranch.fsOnly
  infix:50 " ∈_c " => inCoreChaseBranch.coreOnly

  def get? (cb : CoreChaseBranch kb) (n : Nat) : Option (FactSet sig) :=
    match cb.branch.infinite_list n with
    | none => none
    | some x => some x.fs


  def inCoreChaseBranchNode
    (kb : KnowledgeBase sig)
    (x : Option (CoreChaseNode kb.rules))
    (cb : CoreChaseBranch kb) : Prop :=
    match x with
    | none => False
    | some node =>
        ∃ n, cb.branch.infinite_list n = some node

  instance (kb : KnowledgeBase sig) : Membership (Option (CoreChaseNode kb.rules)) (CoreChaseBranch kb) :=
    ⟨fun cb opt_cn => inCoreChaseBranchNode kb opt_cn cb⟩


  --theorem mem_iff {cd : CoreChaseBranch kb} : ∀ {e : Option (CoreChaseNode kb.rules)}, e ∈ cd ↔ ∃ n, cd.branch.get? n = some e := by rfl

  def head (cb : CoreChaseBranch kb) : CoreChaseNode kb.rules := cb.branch.head.get (Option.isSome_of_mem cb.database_first)


  @[simp, grind =]
  theorem head_eq {cb: CoreChaseBranch kb} : cb.head = cb.branch.get? 0 := by
    have dbf := cb.database_first
    unfold CoreChaseBranch.head
    simp_all
    exact Option.mem_def.mp dbf

  @[simp, grind .]
  theorem first_fs_eq (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (cn_eq : cn ∈ cb.branch.get? 0) : cn.fs = kb.db.toFactSet.val := by
    have dbf := cb.database_first
    rw [dbf, Option.mem_def, Option.some_inj] at cn_eq
    rw [← cn_eq]

  @[simp, grind .]
  theorem fist_core_eq (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (cn_eq : cn ∈ cb.branch.get? 0) : cn.core = kb.db.toFactSet.val := by
    have dbf := cb.database_first
    rw [dbf, Option.mem_def, Option.some_inj] at cn_eq
    rw [← cn_eq]

  @[grind .]
  theorem mem_eq (cb : CoreChaseBranch kb) (cn1 cn2 : CoreChaseNode kb.rules) (n : Nat) (cn1_eq : cn1 ∈ cb.branch.get? n) (cn2_eq : cn2 ∈ cb.branch.get? n) : cn1 = cn2 := by
    rw [Option.mem_def] at cn1_eq cn2_eq
    grind

  @[grind .]
  theorem none_get_eq (cb : CoreChaseBranch kb) : cb.branch.infinite_list m = none ↔ cb.branch.get? m = none := Option.isSome_eq_isSome.mp rfl

  @[grind .]
  theorem leq_some_if_some (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? n).isSome) : ∀ m, m ≤ n → (cb.branch.get? m).isSome := by
    intro m leq
    grind

  @[grind .]
  theorem ex_prev_node_at_each_leq (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? n).isSome) : ∀ m, m ≤ n → ∃ cn, cn ∈ (cb.branch.get? m) := by
    intro m leq
    have := leq_some_if_some cb n is_some m leq
    exact Option.isSome_iff_exists.mp this

  @[grind .]
  theorem geq_none_if_none (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? n).isNone) : ∀ m, m ≥ n → (cb.branch.get? m).isNone := by
    intro m geq
    grind

  def prevNode (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? (n+1)).isSome) : CoreChaseNode kb.rules := by
    exact (cb.branch.get? n).get (by grind)

  @[grind .]
  theorem prevNode_eq (cb : CoreChaseBranch kb) (n : Nat) (is_some : (cb.branch.get? (n+1)).isSome) :
    cb.branch.get? n = some (cb.prevNode n is_some) := by
      simp [prevNode]

  @[grind .]
  theorem origin_isSome (cb : CoreChaseBranch kb) (n : Nat) {node : CoreChaseNode kb.rules} (eq : node ∈ cb.branch.get? (n + 1)) : node.origin.isSome := by
    have ex_before := ex_prev_node_at_each_leq cb n (by grind) n (Nat.le_refl n)
    rcases ex_before with ⟨before, before_eq⟩
    have trg_ex := cb.triggers_exist n before before_eq node eq
    rcases trg_ex with ⟨trg, i, c, c_wc, c_sub, eq⟩
    grind

  /-
    node1 (n) ----> node2 (n + 1)
    ~.core      ⊆   ~.fs
    because ex trigger from n1 to n2 thus n2.fs = n1.core + trig.result thus n1.core ⊆ n2.fs
  -/

  theorem before_core_sub_after_fs (cb : CoreChaseBranch kb) (n : Nat) (before after : CoreChaseNode kb.rules) (before_eq : before ∈ cb.branch.get? n) (after_eq : after ∈ cb.branch.get? (n + 1)) :
    before.core ⊆ after.fs := by
      have trg_ex := cb.triggers_exist n before before_eq after after_eq
      rcases trg_ex with ⟨trg, i, c, c_wc, c_sub, eq⟩
      have eq : after.fs = before.core ∪ trg.val.mapped_head[↑i].toSet := by grind
      rw [eq]
      exact Set.subset_union_of_subset_left fun e a => a

  @[simp]
  theorem cb_fist_isSome (cb : CoreChaseBranch kb) : (cb.branch.get? 0).isSome := by
    exact Option.isSome_of_mem cb.database_first

  @[simp]
  theorem first_fs_finite (cb : CoreChaseBranch kb) : ((cb.branch.get? 0).get (by simp)).fs.finite := ((cb.branch.get? 0).get (by simp)).fs_fin

  @[simp]
  theorem fist_core_finite (cb : CoreChaseBranch kb) : ((cb.branch.get? 0).get (by simp)).core.finite := ((cb.branch.get? 0).get (by simp)).core_finite

  @[simp, grind =]
  theorem cb_head_fs_eq (cb : CoreChaseBranch kb) : cb.head.fs = kb.db.toFactSet := by
    have dbf := cb.database_first
    have : ∃ cn, cn ∈ cb.branch.get? 0 := Option.isSome_iff_exists.mp (Option.isSome_of_mem dbf)
    rcases this with ⟨cn, cn_eq⟩
    rw [dbf, Option.mem_def, Option.some_inj] at cn_eq
    have eq : cb.head = cb.branch.get? 0 := head_eq
    grind

  @[simp, grind =]
  theorem cb_head_core_eq (cb : CoreChaseBranch kb) : cb.head.core = kb.db.toFactSet := by
    have dbf := cb.database_first
    have : ∃ cn, cn ∈ cb.branch.get? 0 := Option.isSome_iff_exists.mp (Option.isSome_of_mem dbf)
    rcases this with ⟨cn, cn_eq⟩
    rw [dbf, Option.mem_def, Option.some_inj] at cn_eq
    have eq : cb.head = cb.branch.get? 0 := head_eq
    grind

  @[grind .]
  theorem ex_prev_cn_if_origin_some (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) (origin_some : cn.origin.isSome) :
    ∃ prev_cn, prev_cn ∈ cb.branch.get? (n-1) := by
      induction n generalizing cn with
        | zero =>
          simp [cb.database_first]
        | succ n ih =>
          have := ex_prev_node_at_each_leq cb (n+1) (by exact Option.isSome_of_mem cn_eq) n (Nat.le_add_right n 1)
          rcases this with ⟨prev_cn, prev_cn_eq⟩
          exists prev_cn

  @[grind .]
  theorem origin_result_finite {rules : RuleSet sig} (node : CoreChaseNode rules) (is_some : node.origin.isSome) : (node.origin_result is_some).toSet.finite := by
    apply Set.finite_of_list_with_same_elements (node.origin_result is_some)
    intro _; rw [List.mem_toSet]

  @[grind .]
  theorem origin_trg_active_prev_core (cb : CoreChaseBranch kb) (n : Nat) (after : CoreChaseNode kb.rules) (after_eq : after ∈ cb.branch.get? (n+1)) :
    let prev_node : CoreChaseNode kb.rules := cb.prevNode n (Option.isSome_of_mem after_eq)
    ∀ o, o ∈ after.origin → o.fst.val.active prev_node.core := by
      let prev_node : CoreChaseNode kb.rules := cb.prevNode n (Option.isSome_of_mem after_eq)
      have trg_ex := cb.triggers_exist n prev_node (by grind) after after_eq
      have trg_act := cb.triggers_active n prev_node (by grind) after after_eq
      grind

  @[grind .]
  theorem next_fs_eq (cb : CoreChaseBranch kb) (n : Nat) (node : CoreChaseNode kb.rules) (node_eq : node ∈ cb.branch.get? (n+1)) :
    let prev_node : CoreChaseNode kb.rules := cb.prevNode n (Option.isSome_of_mem node_eq)
    node.fs = prev_node.core ∪ (node.origin_result (cb.origin_isSome n node_eq)).toSet := by
      let prev_node : CoreChaseNode kb.rules := cb.prevNode n (Option.isSome_of_mem node_eq)
      have trg_ex := cb.triggers_exist n prev_node (by grind) node node_eq
      rcases trg_ex with ⟨trg, i, c, c_wc, c_sub, eq⟩
      simp_all
      constructor

  @[grind .]
  theorem next_fs_eq' (cb : CoreChaseBranch kb) (n : Nat) (a b : CoreChaseNode kb.rules) (eq_a : a ∈ cb.branch.get? n) (eq_b : b ∈ cb.branch.get? (n + 1)) :
    b.fs = (b.origin_result (origin_isSome cb n eq_b)).toSet ∪ a.core := by
      have trg_ex := cb.triggers_exist n a eq_a b eq_b
      rcases trg_ex with ⟨trg, i, c, c_wc, c_sub, eq⟩
      subst b
      exact Set.unionSym a.core trg.val.mapped_head[↑i].toSet


  @[grind .]
  theorem prev_node_eq_db_if_origin_none (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) (cn_origin_none : cn.origin.isNone) :
    cn.fs = kb.db.toFactSet ∧ cn.core = kb.db.toFactSet := by
      by_cases c : n = 0
      have := cb.database_first
      subst c
      grind
      have gt : n > 0 := Nat.zero_lt_of_ne_zero c
      have eq : n - 1 + 1 = n := Nat.sub_add_cancel gt
      have := @origin_isSome _ _ _ _ _ cb (n - 1) cn (by rw [eq]; exact cn_eq)
      grind

  @[grind .]
  theorem fs_finite (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (eq : cn ∈ cb.branch.get? n) : cn.fs.finite := by
    exact cn.fs_fin

  @[grind .]
  theorem not_first_if_origin_some (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (cn_origin_some : cn.origin.isSome) :
    ∀ (n : Nat), cn ∈ cb.branch.get? n → n > 0 := by
      intro n cn_eq
      have dbf := cb.database_first
      grind

  @[grind .]
  theorem ex_facts (cb : CoreChaseBranch kb) : ∃ (fs : FactSet sig), fs ∈ cb := by
    exists ((cb.branch.get? 0).get (cb_fist_isSome cb)).fs
    have dbf := cb.database_first
    simp [dbf, Membership.mem, inCoreChaseBranch]
    exists 0, ((cb.branch.get? 0).get (cb_fist_isSome cb))
    constructor
    simp only [Option.some_get]
    rfl; · left; · simp_all

  theorem ex_facts_fs (cb : CoreChaseBranch kb) : ∃ (fs : FactSet sig), fs ∈_fs cb := by
    exists ((cb.branch.get? 0).get (cb_fist_isSome cb)).fs
    have dbf := cb.database_first
    simp [dbf, inCoreChaseBranch.fsOnly]
    exists 0, ((cb.branch.get? 0).get (cb_fist_isSome cb))
    constructor
    simp only [Option.some_get]
    rfl
    simp_all

  theorem ex_facts_core (cb : CoreChaseBranch kb) : ∃ (fs : FactSet sig), fs ∈_c cb := by
    exists ((cb.branch.get? 0).get (cb_fist_isSome cb)).core
    have dbf := cb.database_first
    simp [dbf, inCoreChaseBranch.coreOnly]
    exists 0, ((cb.branch.get? 0).get (cb_fist_isSome cb))
    constructor
    simp only [Option.some_get]
    rfl
    simp_all

  @[grind .]
  theorem db_applyFact_eq_id (cb : CoreChaseBranch kb) (init : CoreChaseNode kb.rules) (init_eq : init ∈  cb.branch.get? 0) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism init.fs fs2) :
    ∀ f, f ∈ init.fs → gtm.applyFact f = f := by
      intro f f_in
      unfold GroundTermMapping.applyFact
      rw [GeneralizedAtom.mk.injEq]
      constructor
      · rfl
      · apply List.map_id_of_id_on_all_mem
        intro gt gt_in
        unfold GroundTermMapping.isHomomorphism at gtm_hom
        have db_funfree := kb.db.toFactSet.property.right
        rw [cb.database_first] at init_eq
        simp only [Option.mem_def, Option.some.injEq] at init_eq
        rw [← init_eq] at f_in
        specialize db_funfree f f_in gt gt_in
        rcases db_funfree with ⟨c, c_eq⟩
        rw [c_eq]
        exact @gtm_hom.left c

  @[grind .]
  theorem f_in_core_if_in_fs_if_f_isFunctionFree (cb : CoreChaseBranch kb) (n : Nat) (x_eq : x ∈ cb.branch.get? n) (f : Fact sig) (f_in : f ∈ x.fs) (f_is_ff : f.isFunctionFree) : f ∈ x.core := by
      have ex_gtm := x.core_sse.right
      rcases ex_gtm with ⟨gtm, gtm_hom⟩
      have eq : gtm.applyFact f = f := gtm.hom_applyFact_isFunctionFree_eq_id x.fs x.core f f_is_ff gtm_hom
      have x_core := x.is_core
      rcases gtm_hom with ⟨gtm_c, gtm_st⟩
      specialize gtm_st f
      apply gtm_st
      exists f

  @[grind .]
  theorem f_isFunctionFree_in_next_if_some (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : x ∈ cb.branch.get? n) :
    ∀ cn ∈ cb.branch.get? (n+1), ∀ f, f ∈ x.fs ∧ f.isFunctionFree → f ∈ cn.fs := by
      intro cn cn_eq f ⟨f_in, f_in_ff⟩
      have trg_ex := cb.triggers_exist n x x_eq cn cn_eq
      rcases trg_ex with ⟨trg, i, c, c_wc, c_sub, eq⟩
      rcases eq with ⟨lhs, rhs⟩
      grind

  @[grind .]
  theorem f_isFunctionFree_in_geq (cb : CoreChaseBranch kb) (n m : Nat) (x : CoreChaseNode kb.rules) (x_eq : x ∈ cb.branch.get? n) :
     ∀ cn ∈ cb.branch.get? (n+m), ∀ f, f ∈ x.fs ∧ f.isFunctionFree → f ∈ cn.fs := by
      induction m with
        | zero =>
          simp only [Nat.add_zero, and_imp]
          intro cn_succ cn_succ_eq f f_in_fs f_is_ff
          have eq : x = cn_succ := mem_eq cb x cn_succ n x_eq cn_succ_eq
          subst eq
          exact f_in_fs
        | succ m ih =>
          intro cn_succ cn_succ_eq f ⟨f_in_fs, f_is_ff⟩
          have ex_cm : ∃ (cn_mid : CoreChaseNode kb.rules), cn_mid ∈ cb.branch.get? (n + m) :=
            cb.ex_prev_node_at_each_leq (n + m + 1) (Option.isSome_of_mem cn_succ_eq) (n + m) (Nat.le_add_right (n + m) 1)
          rcases ex_cm with ⟨cm, cm_eq⟩
          have := cb.triggers_exist (n + m) cm cm_eq cn_succ cn_succ_eq
          grind

  @[grind .]
  theorem db_fs_sub_geq_core (cb : CoreChaseBranch kb) (n : Nat) (init cn : CoreChaseNode kb.rules) (init_eq : init ∈ cb.branch.get? 0) (cn_eq : cn ∈ cb.branch.get? n) :
    init.fs ⊆ cn.core := by
      have db_funfree := kb.db.toFactSet.property.right
      have init_eq' : init.fs = kb.db.toFactSet.val := by
        have := cb.database_first
        grind

      induction n generalizing cn with
        | zero =>
          intro f f_in
          have eq : cn = init := by simp_all
          exact f_in_core_if_in_fs_if_f_isFunctionFree cb 0 cn_eq f
            (by rw [eq]; exact f_in)
            (by rw [init_eq'] at f_in; exact db_funfree f f_in)
        | succ n ih =>
          have prev_cn_ex : ∃ prev_cn, prev_cn ∈ cb.branch.get? n :=
            cb.ex_prev_node_at_each_leq (n + 1) (Option.isSome_of_mem cn_eq) n (Nat.le_add_right n 1)
          intro f f_in
          refine f_in_core_if_in_fs_if_f_isFunctionFree cb (n + 1) cn_eq f ?_ ?_
          · rcases prev_cn_ex with ⟨prev_cn, prev_cn_eq⟩
            specialize ih prev_cn (by grind) f f_in
            have := f_isFunctionFree_in_next_if_some cb n prev_cn prev_cn_eq cn cn_eq f
            have f_in_prev_fs : f ∈ prev_cn.fs := by
              have prev_cn_core_sse := prev_cn.core_sse.left f ih
              exact prev_cn_core_sse
            apply this
            constructor
            · exact f_in_prev_fs
            · rw [init_eq'] at f_in
              exact db_funfree f f_in
          · rw [init_eq'] at f_in
            exact db_funfree f f_in


 theorem ex_intermediate_if_f_mem_not_mem_succ (cb : CoreChaseBranch kb) (cn cn_succ : CoreChaseNode kb.rules) (n k : Nat)
    (cn_eq : cn ∈ cb.branch.get? n) (cn_succ_eq : cn_succ ∈ cb.branch.get? (n + k))
    (f : Fact sig) (f_in : f ∈ cn.core) (f_nin : ¬ f ∈ cn_succ.core) :
      ∃ (cm : CoreChaseNode kb.rules), f ∈ cm.fs ∧ ¬ f ∈ cm.core := by
      induction k generalizing cn_succ with
        | zero =>
          grind
        | succ k ih =>
          have ex_cm : ∃ cm, cb.branch.infinite_list (n + k) = some cm :=
            cb.ex_prev_node_at_each_leq (n + k + 1) (Option.isSome_of_mem cn_succ_eq) (n+k) (Nat.le_add_right (n + k) 1)
          rcases ex_cm with ⟨cm, cm_eq⟩
          by_cases c : (f ∈ cm.core)
          exists cn_succ
          constructor
          · have := before_core_sub_after_fs cb (n + k) cm cn_succ cm_eq cn_succ_eq
            exact this f c
          · exact f_nin
          specialize ih cm cm_eq c
          exact ih

  @[grind .]
  theorem origin_trg_active_core (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules) (cn_eq : cn ∈ cb.branch.get? (n + 1)) :
    (cn.origin.get (cb.origin_isSome n cn_eq)).fst.val.active (cb.prevNode n (Option.isSome_of_mem cn_eq)).core := by
      have ex_prev_node := ex_prev_node_at_each_leq cb (n+1) (by exact Option.isSome_of_mem cn_eq) n (Nat.le_add_right n 1)
      rcases ex_prev_node with ⟨prev_node, prev_node_eq⟩
      have trg_ex := cb.triggers_exist n prev_node prev_node_eq cn cn_eq
      rcases trg_ex with ⟨trg, i, c, c_wc, c_sub, eq⟩
      grind

  @[grind .]
  theorem functional_term_originates_from_some_trigger_or_database_core (cb : CoreChaseBranch kb) (n : Nat) (cn : CoreChaseNode kb.rules)
    (cn_eq : cb.branch.get? n = some cn) (t : GroundTerm sig) (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) (t_mem : t ∈ cn.fs.terms) :
      t ∈ ((cb.branch.get? 0).get (cb_fist_isSome cb)).fs.terms ∨
      ∃ (m : Nat) (node2 : CoreChaseNode kb.rules), node2 ∈ cb.branch.get? m ∧
      (∃ origin, origin ∈ node2.origin ∧ t ∈ origin.fst.val.fresh_terms_for_head_disjunct origin.snd.val (by rw [← PreTrigger.length_mapped_head]; exact origin.snd.isLt)) := by
        induction n generalizing cn with
          | zero =>
            rw [cb.database_first, Option.some.injEq] at cn_eq
            have func_free := kb.db.toFactSet.property.right
            unfold FactSet.isFunctionFree at func_free
            rcases t_mem with ⟨f, f_mem, t_mem⟩
            rw [← cn_eq] at f_mem
            specialize func_free f f_mem
            unfold Fact.isFunctionFree at func_free
            specialize func_free _ t_mem
            rcases func_free with ⟨_, func_free⟩
            rcases t_is_func with ⟨_, _, _, t_is_func⟩
            rw [t_is_func] at func_free
            simp [GroundTerm.func, GroundTerm.const] at func_free
          | succ n ih =>
            let prev_node := (cb.prevNode n (Option.isSome_of_mem cn_eq))
            cases Classical.em (t ∈ prev_node.core.terms) with
              | inl term_in_prev_node_core =>
                have term_in_prev_node_fs : t ∈ prev_node.fs.terms := CoreChaseNode.fs_terms_sub_core_terms prev_node t term_in_prev_node_core
                specialize ih prev_node (prevNode_eq cb n (Option.isSome_of_mem cn_eq)) term_in_prev_node_fs
                rcases ih with ⟨m2, ih⟩
                left
                exists m2
                rename_i ex
                rcases ex with ⟨m, cm, cm_eq, o, o_eq⟩
                right
                exists m, cm, cm_eq, o
              | inr term_not_in_prev_node_core =>
                right
                exists (n+1)
                exists cn
                constructor
                exact Option.mem_def.mpr cn_eq
                let origin := cn.origin.get (origin_isSome cb n cn_eq)
                exists origin
                rcases t_mem with ⟨f, f_mem, t_mem⟩
                rw [cb.next_fs_eq n cn cn_eq] at f_mem
                change f ∈ (cb.prevNode n _).core ∨ f ∈ (cn.origin_result _).toSet at f_mem
                cases f_mem with
                  | inl f_mem =>
                    apply False.elim
                    apply term_not_in_prev_node_core
                    exists f
                  | inr f_mem =>
                    have t_mem : t ∈ origin.fst.val.mapped_head[origin.snd.val].flatMap GeneralizedAtom.terms := by
                      rw[List.mem_flatMap]
                      exists f
                    rw [PreTrigger.mem_terms_mapped_head_iff] at t_mem
                    cases t_mem with
                    | inl t_mem =>
                      rcases t_is_func with ⟨_, _, _, t_is_func⟩
                      rcases t_mem with ⟨_, _, t_mem⟩
                      rw [t_is_func] at t_mem
                      simp [GroundTerm.const, GroundTerm.func] at t_mem
                    | inr t_mem =>
                      cases t_mem with
                      | inl t_mem =>
                      apply False.elim; apply term_not_in_prev_node_core
                      apply FactSet.terms_subset_of_subset (cb.origin_trg_active_core n cn cn_eq).left
                      rw [FactSet.mem_terms_toSet]
                      rw [PreTrigger.mem_terms_mapped_body_iff]
                      apply Or.inr
                      rw [List.mem_map] at t_mem; rcases t_mem with ⟨v, v_mem, t_mem⟩
                      exists v
                      constructor
                      · apply Rule.frontier_subset_vars_body;
                        apply Rule.mem_frontier_iff_mem_frontier_for_head.mpr;
                        grind
                      . exact t_mem
                      | inr t_mem =>
                        constructor
                        exact Option.get_mem (origin_isSome cb n cn_eq)
                        exact t_mem

  theorem func_term_not_mem_head {cb : CoreChaseBranch kb} {t : GroundTerm sig} (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok) :
    ¬ t ∈ cb.head.fs.terms := by
      intro t_mem
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rcases kb.db.toFactSet.property.right f (by grind) t t_mem with ⟨c, t_eq⟩
      rcases t_is_func with ⟨_, _, _, t_eq'⟩
      rw [t_eq'] at t_eq
      simp [GroundTerm.func_neq_const] at t_eq

  theorem term_mem_cn_not_mem_trg_fresh_terms (cb : CoreChaseBranch kb) (cn cn_succ : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) (cn_succ_eq : cn_succ ∈ cb.branch.get? (n+1))
   (t : GroundTerm sig) (t_mem : t ∈ cn.core.terms) :
    let trg := (cn_succ.origin.get (origin_isSome cb n cn_succ_eq)).fst
    let disj := (cn_succ.origin.get (origin_isSome cb n cn_succ_eq)).snd
    ¬ t ∈ trg.val.fresh_terms_for_head_disjunct disj (by grind) := by
      sorry

end CoreChaseBranch
