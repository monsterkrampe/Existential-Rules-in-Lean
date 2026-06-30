import ExistentialRules.ChaseSequence.CoreChase.Basic
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseNode
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {kb : KnowledgeBase sig}


  /-
    (x)              (y)
    A_1  --- →  ---  A_2
     |                |
     fs           →   fs
     ↓         ↗      ↓
   id (⊆)  (h)     id (⊆)
     ↓   ↗           ↓
   core → (h ∘ id) → core

  -/

namespace CoreChaseBranch


  @[grind .]
  theorem ex_hom_fs_core (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : x ∈ cb.branch.get? n) :
    ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fs x.core := by
      exact x.core_sse.right

  @[grind .]
  theorem ex_hom_prev_core_next_fs (cb : CoreChaseBranch kb) (n : Nat) (x y : CoreChaseNode kb.rules)
    (x_eq : x ∈ cb.branch.get? n) (y_eq : y ∈ cb.branch.get? (n + 1)) : ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.fs := by
      have sub : x.core ⊆ y.fs := before_core_sub_after_fs cb n x y x_eq y_eq
      have := x.core.ex_hom_sub y.fs sub
      exact this

  @[grind .]
  theorem ex_hom_applyFactSet_fs_core (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cn ∈ cb.branch.get? n) :
    ∃ (gtm : GroundTermMapping sig), gtm.applyFactSet cn.fs ⊆ cn.core := by
      rcases (ex_hom_fs_core cb n cn cn_eq) with ⟨gtm, gtm_hom⟩
      exists gtm
      intro f f_in
      unfold GroundTermMapping.applyFactSet at f_in
      rcases f_in with ⟨a, ahl, ahr⟩
      rw [← ahr]
      apply gtm_hom.right
      apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
      exact ahl

  @[grind .]
  theorem ex_hom_core_succ_core_if_some (cb : CoreChaseBranch kb) (n : Nat) (x y : CoreChaseNode kb.rules)
    (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.core := by
      have y_core := y.core_sse
      rcases y_core with ⟨sub, ⟨gtm_yfs_ycore, gtm_yfs_ycore_hom⟩⟩
      have : ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.fs := ex_hom_prev_core_next_fs cb n x y x_eq y_eq
      rcases this with ⟨gtm_xcore_yfs, gtm_xcore_yfs_hom⟩
      exists (gtm_yfs_ycore ∘ gtm_xcore_yfs)
      exact GroundTermMapping.isHomomorphism_compose gtm_xcore_yfs gtm_yfs_ycore x.core y.fs y.core gtm_xcore_yfs_hom gtm_yfs_ycore_hom

  @[grind .]
  theorem ex_hom_fs_succ_fs_if_some (cb : CoreChaseBranch kb) (n : Nat) (x y : CoreChaseNode kb.rules)
    (x_eq : cb.branch.infinite_list n = some x) (y_eq : cb.branch.infinite_list (n + 1) = some y) :
      ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fs y.fs := by
        have x_core := x.core_sse
        have : ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.fs := ex_hom_prev_core_next_fs cb n x y x_eq y_eq
        rcases this with ⟨gtm_xcore_yfs, gtm_xcore_yfs_hom⟩
        rcases x_core with ⟨sub, gtm_xfs_xcore, gtm_xfs_xcore_hom⟩
        exists (gtm_xcore_yfs ∘ gtm_xfs_xcore)
        exact GroundTermMapping.isHomomorphism_compose gtm_xfs_xcore gtm_xcore_yfs x.fs x.core y.fs gtm_xfs_xcore_hom gtm_xcore_yfs_hom

  -- t16 (A_0 → A_1 → A_2 → ...)
  @[grind .]
  theorem ex_hom_core_geq_core (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : x ∈ cb.branch.get? n) :
      ∀ m, ∀ y, y ∈ cb.branch.get? (n + m) → ∃ (h : GroundTermMapping sig), h.isHomomorphism x.core y.core := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.add_zero, Option.mem_def]
        intro cn cn_eq
        have eq : cn = x := by grind
        exists id
        rw [eq]
        exact GroundTermMapping.id_is_hom
      | succ m ih =>
        intro y y_eq
        simp only [Option.mem_def] at ih

        have ex_cm : ∃ (z : CoreChaseNode kb.rules), cb.branch.infinite_list (n + m) = some z :=
          cb.ex_prev_node_at_each_leq (n + m + 1) (Option.isSome_of_mem y_eq) (n + m) (Nat.le_add_right (n + m) 1)

        rcases ex_cm with ⟨z, z_eq⟩
        specialize ih z z_eq
        rcases ih with ⟨gtm_x_z, gtm_x_z_hom⟩
        have : ∃ (h : GroundTermMapping sig), h.isHomomorphism z.core y.core := ex_hom_core_succ_core_if_some cb (n + m) z y z_eq y_eq
        rcases this with ⟨gtm_z_y, gtm_z_y_hom⟩
        exists (gtm_z_y ∘ gtm_x_z)
        exact GroundTermMapping.isHomomorphism_compose gtm_x_z gtm_z_y x.core z.core y.core gtm_x_z_hom gtm_z_y_hom

  @[grind .]
  -- exHomStepToAllFollowing
  theorem ex_hom_fs_geq_fs (cb : CoreChaseBranch kb) (n : Nat) (x : CoreChaseNode kb.rules) (x_eq : x ∈ cb.branch.get? n) :
        ∀ m, ∀ y, y ∈ cb.branch.get? (n + m) → ∃ (h : GroundTermMapping sig), h.isHomomorphism x.fs y.fs := by
      intro m
      induction m with
      | zero =>
        intro y y_eq
        have eq : x = y := by grind
        rw [eq]
        exists id
        exact GroundTermMapping.id_is_hom
      | succ m ih =>
        intro y y_eq
        have ex_z := cb.ex_prev_node_at_each_leq (n+m+1) (Option.isSome_of_mem y_eq) (n+m) (Nat.le_add_right (n + m) 1)
        rcases ex_z with ⟨z, z_eq⟩
        specialize ih z z_eq
        rcases ih with ⟨gtm_x_z, gtm_x_z_hom⟩
        have ex_gtm_z_y : ∃ (h : GroundTermMapping sig), h.isHomomorphism z.fs y.fs := cb.ex_hom_fs_succ_fs_if_some (n + m) z y z_eq y_eq
        rcases ex_gtm_z_y with ⟨gtm_z_y, gtm_z_y_hom⟩
        exists (gtm_z_y ∘ gtm_x_z)
        exact GroundTermMapping.isHomomorphism_compose gtm_x_z gtm_z_y x.fs z.fs y.fs gtm_x_z_hom gtm_z_y_hom

  @[grind .]
  theorem gtm_core_set_if_gtm_fs_set (fs : FactSet sig) (cn : CoreChaseNode kb.rules) (h : GroundTermMapping sig) (h_hom : h.isHomomorphism cn.fs fs) : h.isHomomorphism cn.core fs := by
    rcases h_hom with ⟨h_c, h_af⟩
    constructor
    exact h_c
    intro f f_in
    specialize h_af f
    apply h_af
    exact h.mem_applyFactSet_if_mem_applyFactSet_sub cn.core cn.fs f f_in (cn.core_sse.left)

  @[grind .]
  theorem gtm_fs_core_is_endo (cb : CoreChaseBranch kb) (cn : CoreChaseNode kb.rules) (n : Nat) (cn_eq : cb.branch.infinite_list n = some cn) (gtm : GroundTermMapping sig) (gtm_hom : gtm.isHomomorphism cn.fs cn.core):
     (gtm.surjectiveSet cn.core.terms cn.core.terms) := by
      have sc := FactSet.isStrongCore_of_isWeakCore_of_finite cn.core cn.is_core cn.core_finite
      specialize sc gtm (gtm_core_set_if_gtm_fs_set cn.core cn gtm gtm_hom)
      rcases sc with ⟨s1, s2, s3⟩
      exact s3

  @[grind .]
  theorem core_extends_hom (A B C: FactSet sig) (C_homsub : C.homSubset B) (h : GroundTermMapping sig) (h_hom : h.isHomomorphism A B) : ∃ (h' : GroundTermMapping sig), h'.isHomomorphism A C := by
    rcases C_homsub with ⟨sub, h', h'_hom⟩
    exists (h' ∘ h)
    exact GroundTermMapping.isHomomorphism_compose h h' A B C h_hom h'_hom


end CoreChaseBranch
