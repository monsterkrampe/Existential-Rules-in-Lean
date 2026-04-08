module

public import BasicLeanDatastructures.List.AllListsOfLength
public import ExistentialRules.Terms.Basic

/-!
# Computing all GroundTerms of a given depth

This file defined a single function `all_terms_limited_by_depth` and an accompanying membership theorem `mem_all_terms_limited_by_depth`.
The function computes all possible terms that can be constructed given a list of constants and a list of function symsols such that
the depth of the terms do not exceed a given depth.
This is required for MFA later since we want to argue that when a rule set is MFA, then the number of function symbols in the chase is finite.
-/

variable {sig : Signature} [DecidableEq sig.C] [DecidableEq sig.V]

/-- We recursively construct all `GroundTerm`s that have at most a given depth. For example, the terms with at most depth 1 are exactly the constants. The recursion step uses all terms that have at most the previous depth and then combines them in all possible ways using each of the available function symbols as the new root. -/
public def all_terms_limited_by_depth (constants : List sig.C) (funcs : List (SkolemFS sig)) : Nat -> List (GroundTerm sig)
| 0 => []
| 1 => constants.map GroundTerm.const
| .succ (.succ depth) =>
  let prev := all_terms_limited_by_depth constants funcs (.succ depth)
  funcs.flatMap (fun func =>
    (all_lists_of_length prev func.arity).attach.map (fun ⟨ts, mem⟩ =>
      GroundTerm.func func ts (by
        rw [mem_all_lists_of_length] at mem
        exact mem.left
      )
    )
  ) ++ prev

/-- This theorem expresses the desired property of the definition above. The constructed list of `GroundTerm`s contains exactly the terms that have at most the desired depth and feature only constants and function symbols from the allowed lists. This theorem is at the same time a sanity check that our definition above is behaving as expected. -/
public theorem mem_all_terms_limited_by_depth (constants : List sig.C) (funcs : List (SkolemFS sig)) (depth : Nat) :
    ∀ t, t ∈ (all_terms_limited_by_depth constants funcs depth) ↔
      (t.depth ≤ depth ∧ (∀ c, c ∈ t.constants -> c ∈ constants) ∧ (∀ func, func ∈ t.functions -> func ∈ funcs)) := by
  fun_induction all_terms_limited_by_depth
  . intro t
    have : t.depth ≠ 0 := by apply Nat.ne_zero_of_lt; exact GroundTerm.depth_gt_zero
    simp [this]
  . intro t
    constructor
    . grind
    . intro h
      cases eq : t with
      | const _ => grind
      | func _ ts _ =>
        have : t.depth > 1 := by
          rw [eq, GroundTerm.depth_func]
          cases eq : (ts.map GroundTerm.depth).max? with
          | none => simp
          | some m =>
            cases m with
            | zero =>
              rw [List.max?_eq_some_iff] at eq
              have contra := eq.left
              rw [List.mem_map] at contra
              rcases contra with ⟨t, t_mem, contra⟩
              have : t.depth ≠ 0 := by apply Nat.ne_zero_of_lt; exact GroundTerm.depth_gt_zero
              apply False.elim; apply this; exact contra
            | succ m => simp
        grind
  case case3 depth prev ih =>
    intro t
    have aux : ∀ (ts : List (GroundTerm sig)),
      ((∀ (t : GroundTerm sig), t ∈ ts -> t ∈ (all_terms_limited_by_depth constants funcs depth.succ)) ↔
      ((ts.all (fun t => t.depth ≤ depth.succ)) ∧ (∀ c, c ∈ (ts.flatMap GroundTerm.constants) -> c ∈ constants) ∧
      (∀ func, func ∈ (ts.flatMap GroundTerm.functions) -> func ∈ funcs))) := by grind
    constructor
    . intro h
      rw [List.mem_append] at h
      cases h with
      | inr h => grind
      | inl h =>
        simp only [List.mem_flatMap, List.mem_map] at h
        rcases h with ⟨func, func_mem, ts, ts_mem, t_eq⟩
        rw [← t_eq]
        unfold List.attach at ts_mem
        unfold List.attachWith at ts_mem
        rw [List.mem_pmap] at ts_mem
        rcases ts_mem with ⟨ts_val, ts_mem, ts_eq⟩
        rw [mem_all_lists_of_length] at ts_mem

        rw [GroundTerm.depth_func]
        rw [GroundTerm.constants_func]
        rw [GroundTerm.functions_func]

        have aux := (aux ts_val).mp (by
          intro t t_mem
          apply ts_mem.right
          exact t_mem
        )

        rw [← ts_eq]
        constructor
        . rw [Nat.add_comm]
          apply Nat.succ_le_succ
          cases eq : (ts_val.map GroundTerm.depth).max? with
          | none => simp
          | some m =>
            rw [Option.getD_some, (ts_val.map GroundTerm.depth).max?_le_iff]
            . grind
            . grind
        . grind

    . intro h
      rw [List.mem_append]
      simp only [List.mem_flatMap, List.mem_map]
      rcases h with ⟨depth_le, consts_mem, funcs_mem⟩
      rw [Nat.le_iff_lt_or_eq] at depth_le
      cases depth_le with
      | inl depth_le => grind
      | inr depth_le =>
        cases eq : t with
        | const _ => grind
        | func t_func ts =>
          rw [eq, GroundTerm.depth_func] at depth_le
          rw [eq, GroundTerm.constants_func] at consts_mem
          rw [eq, GroundTerm.functions_func] at funcs_mem
          rw [Nat.add_comm, Nat.add_right_cancel_iff] at depth_le

          have aux := (aux ts).mpr (by
            constructor
            . rw [List.all_eq_true]
              intro t t_mem
              rw [decide_eq_true_iff]
              cases eq : (ts.map GroundTerm.depth).max? with
              | none => rw [List.max?_eq_none_iff, List.map_eq_nil_iff] at eq; rw [eq] at t_mem; simp at t_mem
              | some m =>
                rw [eq, Option.getD_some, ← Nat.succ_eq_add_one] at depth_le
                rw [List.max?_eq_some_iff] at eq
                rw [← depth_le]
                apply eq.right
                rw [List.mem_map]
                exists t
            . grind
          )

          apply Or.inl
          exists t_func
          constructor
          . apply funcs_mem; simp
          . have ts_mem : ts ∈ all_lists_of_length (all_terms_limited_by_depth constants funcs depth.succ) t_func.arity := by grind
            exists ⟨ts, ts_mem⟩
            simp

