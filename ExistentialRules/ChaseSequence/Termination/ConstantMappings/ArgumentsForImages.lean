import ExistentialRules.ChaseSequence.Termination.ConstantMappings.StrictConstantMapping

namespace StrictConstantMapping

  variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

  def arguments_for_constant (g : StrictConstantMapping sig) (possible_constants : List sig.C) (c : sig.C) : List sig.C :=
    possible_constants.filter (fun d => g d = c)

  theorem apply_to_arguments_yields_original_constant (g : StrictConstantMapping sig) (possible_constants : List sig.C) (c : sig.C) :
      ∀ arg, arg ∈ g.arguments_for_constant possible_constants c ↔ (arg ∈ possible_constants ∧ g arg = c) := by
    intro arg
    unfold arguments_for_constant
    simp

  def arguments_for_pre_term (g : StrictConstantMapping sig) (possible_constants : List sig.C) : PreGroundTerm sig -> List (PreGroundTerm sig)
  | .leaf c => (g.arguments_for_constant possible_constants c).map (fun arg => .leaf arg)
  | .inner func ts =>
    (arguments_for_pre_term_list ts).map (.inner func)
  where
    arguments_for_pre_term_list : List (PreGroundTerm sig) -> List (List (PreGroundTerm sig))
    | .nil => [[]]
    | .cons hd tl =>
      let arguments_tail := arguments_for_pre_term_list tl
      (g.arguments_for_pre_term possible_constants hd).flatMap (fun arg =>
        arguments_tail.map (fun arg_list =>
          arg :: arg_list
        )
      )

  theorem arguments_for_pre_term.length_arguments_for_pre_term_list {g : StrictConstantMapping sig} {possible_constants : List sig.C} {ts : List (PreGroundTerm sig)} :
      ∀ args ∈ arguments_for_pre_term_list g possible_constants ts, args.length = ts.length := by
    induction ts with
    | nil => simp [arguments_for_pre_term_list]
    | cons hd tl ih =>
      intro res res_mem
      unfold arguments_for_pre_term_list at res_mem
      rw [List.mem_flatMap] at res_mem
      rcases res_mem with ⟨arg, arg_for_hd, res_mem⟩
      rw [List.mem_map] at res_mem
      rcases res_mem with ⟨args, args_for_tl, res_mem⟩
      rw [← res_mem]
      rw [List.length_cons]
      rw [List.length_cons]
      rw [Nat.add_right_cancel_iff]
      apply ih
      exact args_for_tl

  theorem arguments_for_pre_term.mem_arguments_for_pre_term_list {g : StrictConstantMapping sig} {possible_constants : List sig.C} {ts : List (PreGroundTerm sig)} :
      ∀ {args}, (length_eq : args.length = ts.length) -> (args ∈ arguments_for_pre_term_list g possible_constants ts ↔ (∀ i : Nat, (lt : i < ts.length) -> args[i] ∈ g.arguments_for_pre_term possible_constants ts[i])) := by
    induction ts with
    | nil => simp [arguments_for_pre_term_list]
    | cons hd tl ih =>
      intro args length_eq
      unfold arguments_for_pre_term.arguments_for_pre_term_list
      rw [List.mem_flatMap]
      constructor
      . rintro ⟨a, a_mem, args_mem⟩
        rw [List.mem_map] at args_mem
        rcases args_mem with ⟨args', args'_mem, args_eq⟩
        intro i i_lt
        simp only [← args_eq]
        cases i with
        | zero => exact a_mem
        | succ i =>
          rw [ih] at args'_mem
          . apply args'_mem
          . simp only [← args_eq, List.length_cons, Nat.add_right_cancel_iff] at length_eq
            exact length_eq
      . intro h
        cases args with
        | nil => simp at length_eq
        | cons a args =>
          exists a
          constructor
          . exact h 0 (by simp)
          . rw [List.mem_map]
            exists args
            simp only [and_true]
            rw [ih]
            . intro i lt; exact h (i+1) (by simp [lt])
            . simp only [List.length_cons, Nat.add_right_cancel_iff] at length_eq
              exact length_eq

  theorem apply_to_arguments_yields_original_pre_term {g : StrictConstantMapping sig} {possible_constants : List sig.C} {term : FiniteTree (SkolemFS sig) sig.C} :
      ∀ {arg}, arg ∈ g.arguments_for_pre_term possible_constants term ↔ ((∀ c, c ∈ arg.leaves -> c ∈ possible_constants) ∧ g.toConstantMapping.apply_pre_ground_term arg = term) := by
    induction term with
    | leaf c =>
      intro arg
      cases arg with
      | inner func' args => simp [arguments_for_pre_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const]
      | leaf d =>
        simp only [arguments_for_pre_term, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const, FiniteTree.leaves, List.mem_singleton]
        rw [List.mem_map]
        constructor
        . rintro ⟨arg, arg_mem, arg_eq⟩
          rw [FiniteTree.leaf.injEq] at arg_eq
          rw [apply_to_arguments_yields_original_constant] at arg_mem
          rw [← arg_eq]
          constructor
          . intro _ eq; rw [eq]; exact arg_mem.left
          . rw [arg_mem.right]
        . rintro ⟨mem_possible_constants, d_eq⟩
          rw [FiniteTree.leaf.injEq] at d_eq
          exists d
          simp only [and_true]
          rw [apply_to_arguments_yields_original_constant]
          simp only [d_eq, and_true]
          apply mem_possible_constants
          rfl
    | inner func ts ih =>
      intro arg
      unfold arguments_for_pre_term
      rw [List.mem_map]
      constructor
      . rintro ⟨args, args_mem, arg_eq⟩
        have args_mem' := args_mem
        rw [arguments_for_pre_term.mem_arguments_for_pre_term_list (arguments_for_pre_term.length_arguments_for_pre_term_list _ args_mem')] at args_mem
        rw [← arg_eq]
        simp only [FiniteTree.leaves, ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, FiniteTree.inner.injEq, true_and, List.mem_flatMap]
        constructor
        . rintro c ⟨arg, arg_mem, c_mem⟩
          rcases List.getElem_of_mem arg_mem with ⟨i, lt, arg_eq⟩
          rw [← arg_eq] at c_mem
          apply ((ih _ _).mp (args_mem i (by rw [← arguments_for_pre_term.length_arguments_for_pre_term_list _ args_mem']; exact lt))).left _ c_mem
          simp
        . rw [List.map_eq_iff]
          intro i
          cases Decidable.em (i < ts.length) with
          | inr i_lt => rw [List.getElem?_eq_none (Nat.le_of_not_lt i_lt)]; rw [List.getElem?_eq_none (by rw [arguments_for_pre_term.length_arguments_for_pre_term_list _ args_mem']; exact (Nat.le_of_not_lt i_lt))]; simp
          | inl i_lt =>
            rw [List.getElem?_eq_getElem i_lt]
            rw [List.getElem?_eq_getElem (by rw [arguments_for_pre_term.length_arguments_for_pre_term_list _ args_mem']; exact i_lt)]
            rw [Option.map_some, Option.some.injEq]
            rw [← ((ih ts[i] (by simp)).mp (args_mem i i_lt)).right]
      . rintro ⟨mem_possible_constants, apply_eq⟩
        cases arg with
        | leaf d => simp [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, StrictConstantMapping.toConstantMapping, GroundTerm.const] at apply_eq
        | inner func' args =>
          simp only [ConstantMapping.apply_pre_ground_term, FiniteTree.mapLeaves, FiniteTree.inner.injEq] at apply_eq
          exists args
          simp only [apply_eq.left, and_true]
          have apply_eq_right := apply_eq.right
          rw [List.map_eq_iff] at apply_eq_right
          rw [arguments_for_pre_term.mem_arguments_for_pre_term_list (by rw [← apply_eq.right]; simp)]
          intro i lt
          have lt_args_length : i < args.length := by rw [← apply_eq.right] at lt; rw [List.length_map] at lt; exact lt
          rw [ih _ (by simp)]
          constructor
          . intro c c_mem
            apply mem_possible_constants
            simp only [FiniteTree.leaves, List.mem_flatMap]
            exists args[i]
            constructor
            . apply List.getElem_mem
            . exact c_mem
          . specialize apply_eq_right i
            rw [List.getElem?_eq_getElem lt] at apply_eq_right
            rw [List.getElem?_eq_getElem lt_args_length] at apply_eq_right
            rw [Option.map_some, Option.some.injEq] at apply_eq_right
            rw [apply_eq_right]

  theorem arguments_for_pre_term_arity_ok {g : StrictConstantMapping sig} {possible_constants : List sig.C} {t : FiniteTree (SkolemFS sig) sig.C} (arity_ok : PreGroundTerm.arity_ok t) :
      ∀ {t'}, t' ∈ (g.arguments_for_pre_term possible_constants t) -> PreGroundTerm.arity_ok t' := by
    induction t with
    | leaf c =>
      intro t' t'_mem
      unfold arguments_for_pre_term at t'_mem
      rw [List.mem_map] at t'_mem
      rcases t'_mem with ⟨d, d_mem, t'_eq⟩
      rw [← t'_eq]
      simp [PreGroundTerm.arity_ok]
    | inner f ts ih =>
      intro arg arg_mem
      unfold arguments_for_pre_term at arg_mem
      unfold PreGroundTerm.arity_ok at arity_ok
      rw [Bool.and_eq_true] at arity_ok
      rw [List.mem_map] at arg_mem
      rcases arg_mem with ⟨args, args_mem, arg_eq⟩
      rw [← arg_eq]
      simp only [PreGroundTerm.arity_ok]
      rw [Bool.and_eq_true]
      constructor
      . rw [arguments_for_pre_term.length_arguments_for_pre_term_list _ args_mem]
        exact arity_ok.left
      . rw [List.all_eq_true]
        rintro ⟨arg', arg'_mem⟩ _
        simp only
        have length_eq : args.length = ts.length := arguments_for_pre_term.length_arguments_for_pre_term_list _ args_mem
        rw [arguments_for_pre_term.mem_arguments_for_pre_term_list length_eq] at args_mem
        rcases List.getElem_of_mem arg'_mem with ⟨i, lt, arg'_eq⟩
        have lt_ts_length : i < ts.length := by rw [← length_eq]; exact lt
        apply ih ts[i] (by simp)
        . have arity_ok := arity_ok.right
          rw [List.all_eq_true] at arity_ok
          apply arity_ok ⟨ts[i], by simp⟩
          apply List.mem_attach
        . rw [← arg'_eq]; apply args_mem

  def arguments_for_term_list (g : StrictConstantMapping sig) (possible_constants : List sig.C) (ts : List (GroundTerm sig)) : List (List (GroundTerm sig)) :=
    (arguments_for_pre_term.arguments_for_pre_term_list g possible_constants ts.unattach).attach.map (fun ⟨args, args_mem⟩ =>
      args.attach.map (fun ⟨arg, arg_mem⟩ =>
        ⟨arg, by
          have : args.length = ts.unattach.length := arguments_for_pre_term.length_arguments_for_pre_term_list _ args_mem
          rw [arguments_for_pre_term.mem_arguments_for_pre_term_list this] at args_mem
          rcases List.getElem_of_mem arg_mem with ⟨i, lt, arg_eq⟩
          rw [← arg_eq]
          specialize args_mem i (by rw [← this]; exact lt)
          apply arguments_for_pre_term_arity_ok _ args_mem
          rw [List.getElem_unattach]
          exact (ts[i]'(by rw [← List.length_unattach, ← this]; exact lt)).property
        ⟩
      )
    )

  theorem apply_to_arguments_yields_original_term_list {g : StrictConstantMapping sig} {possible_constants : List sig.C} {ts : List (GroundTerm sig)} :
      ∀ {args}, args ∈ g.arguments_for_term_list possible_constants ts ↔ ((∀ c, c ∈ (args.flatMap GroundTerm.constants) -> c ∈ possible_constants) ∧ (args.map (fun arg => g.toConstantMapping.apply_ground_term arg) = ts)) := by
    intro args
    unfold arguments_for_term_list
    simp only [List.mem_map, List.mem_attach, true_and]
    constructor
    . rintro ⟨⟨args', args'_mem⟩, args_eq⟩
      have length_eq : args'.length = ts.unattach.length := arguments_for_pre_term.length_arguments_for_pre_term_list _ args'_mem
      rw [arguments_for_pre_term.mem_arguments_for_pre_term_list length_eq] at args'_mem
      constructor
      . simp only [List.mem_flatMap]
        rintro c ⟨arg, arg_mem, c_mem⟩
        rcases List.getElem_of_mem arg_mem with ⟨i, lt, arg_eq⟩
        simp only [← arg_eq, ← args_eq, List.getElem_map, List.getElem_attach] at c_mem
        apply (apply_to_arguments_yields_original_pre_term.mp (args'_mem i (by rw [← length_eq]; rw [← args_eq, List.length_map, List.length_attach] at lt; exact lt))).left
        exact c_mem
      . rw [List.map_eq_iff]
        intro i
        cases Decidable.em (i < ts.length) with
        | inr i_lt => rw [List.getElem?_eq_none (Nat.le_of_not_lt i_lt)]; rw [List.getElem?_eq_none (by rw [← args_eq, List.length_map, List.length_attach, length_eq, List.length_unattach]; apply Nat.le_of_not_lt; exact i_lt)]; simp
        | inl i_lt =>
          rw [List.getElem?_eq_getElem i_lt]
          rw [List.getElem?_eq_getElem (by rw [← args_eq, List.length_map, List.length_attach, length_eq, List.length_unattach]; exact i_lt)]
          rw [Option.map_some, Option.some.injEq]
          unfold ConstantMapping.apply_ground_term
          simp only [← args_eq, List.getElem_map, List.getElem_attach]
          rw [Subtype.mk.injEq]
          rw [(apply_to_arguments_yields_original_pre_term.mp (args'_mem i (by rw [List.length_unattach]; exact i_lt))).right]
          simp
    . rintro ⟨mem_possible_constants, apply_eq⟩
      have length_eq : args.length = ts.length := by rw [← apply_eq, List.length_map]
      exists ⟨args.unattach, by
        rw [arguments_for_pre_term.mem_arguments_for_pre_term_list (by rw [List.length_unattach, List.length_unattach]; exact length_eq)]
        intro i lt
        simp only [List.getElem_unattach]
        rw [apply_to_arguments_yields_original_pre_term]
        constructor
        . intro c c_mem
          apply mem_possible_constants
          rw [List.mem_flatMap]
          exists args[i]'(by rw [length_eq, ← List.length_unattach]; exact lt)
          constructor
          . apply List.getElem_mem
          . exact c_mem
        . simp [← apply_eq, ConstantMapping.apply_ground_term]⟩
      rw [List.map_eq_iff]
      intro i
      cases Decidable.em (i < args.length) with
      | inr lt => simp [lt]
      | inl lt => simp [lt]


  def arguments_for_fact (g : StrictConstantMapping sig) (possible_constants : List sig.C) (f : Fact sig) : List (Fact sig) :=
    (g.arguments_for_term_list possible_constants f.terms).attach.map (fun ⟨ts, mem⟩ =>
      {
        predicate := f.predicate
        terms := ts
        arity_ok := by
          unfold arguments_for_term_list at mem
          rw [List.mem_map] at mem
          rcases mem with ⟨args, args_mem, ts_eq⟩
          rw [← ts_eq]
          simp only [List.length_map, List.length_attach]
          rw [arguments_for_pre_term.length_arguments_for_pre_term_list _ args.property]
          rw [List.length_unattach]
          exact f.arity_ok
      }
    )

  theorem apply_to_arguments_yields_original_fact (g : StrictConstantMapping sig) (possible_constants : List sig.C) (f : Fact sig) :
      ∀ arg, arg ∈ g.arguments_for_fact possible_constants f ↔ ((∀ c, c ∈ arg.constants -> c ∈ possible_constants) ∧ g.toConstantMapping.apply_fact arg = f) := by
    intro arg
    unfold arguments_for_fact
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
    constructor
    . intro h
      rcases h with ⟨ts, mem, arg_eq⟩
      rw [← arg_eq]
      unfold ConstantMapping.apply_fact
      unfold TermMapping.apply_generalized_atom
      rw [GeneralizedAtom.mk.injEq]
      simp only [true_and]
      rw [apply_to_arguments_yields_original_term_list] at mem
      exact mem
    . intro h
      exists arg.terms, (by
        rw [apply_to_arguments_yields_original_term_list]
        constructor
        . exact h.left
        . have r := h.right
          unfold ConstantMapping.apply_fact at r
          rw [GeneralizedAtom.mk.injEq] at r
          exact r.right
      )
      have r := h.right
      unfold ConstantMapping.apply_fact at r
      unfold TermMapping.apply_generalized_atom at r
      rw [GeneralizedAtom.mk.injEq] at r
      rw [GeneralizedAtom.mk.injEq]
      constructor
      . rw [← r.left]
      . rfl

end StrictConstantMapping

