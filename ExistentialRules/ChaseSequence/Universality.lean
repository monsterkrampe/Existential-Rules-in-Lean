import ExistentialRules.ChaseSequence.ChaseTree

/-!
# Chase Tree Result is Universal Model Set

This whole file is dedicated to showing that the result of a `ChaseTree` is a universal model set.
More precisely, we want to show the universality part as we have already shown in `ChaseTree.result_models_kb` that each
element of the result is a model.
So what exactly remains to be shown?

We aim to show that for a given `ChaseTree` for a `KnowledgeBase` and any model $M$ of the `KnowledgeBase`,
we can pick a fact set $F$ from the result of the chase tree such that there is a homomorphism from $F$ to $M$.
This result is shown in `chaseTreeResultIsUniversal`.

The proof works by step-wise construction of both a branch in the chase tree as well as a suitable homomorphism.
The constructions builds both at the same time.
One step of the construction is done by the `hom_step` function below, which calls `hom_step_of_trg_ex` for the heavy lifting.
The base of the construction is simply an empty branch and the id mapping.
In each step of the construction, we consider an `InductiveHomomorphismResult`, which we define to be a pair of a node in the chase tree and a `GroundTermMapping` such that the mapping is a homomorphism from the node into the model $M$.

In the proof of `chaseTreeResultIsUniversal`, we leverage the `TreeDerivation.generate_derivation` function with `hom_step` as the generator function.
Besides that, all the homomorphisms from the individual steps need to be combined into a single function. The definition is not too hard and all relevant properties are also not too hard to show once we can establish that the homomorphisms for each step always extend the previous one.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

/-- The `InductiveHomomorphismResult` is used for the step-wise construction is forms the element that is the input and output of the generator function used in `TreeDerivation.generate_derivation` later. It consists of a node in the chase tree and a `GroundTermMapping` that is a homomorphism from the node to the target model. The generated branch is the chain of all the generated nodes.  -/
abbrev InductiveHomomorphismResult (ct : ChaseTree obs kb) (m : FactSet sig) :=
  { pair : ct.NodeWithAddress × (GroundTermMapping sig) // pair.snd.isHomomorphism pair.fst.node.facts m }

/-- Consider any node in the chase tree together with a homomorphism from this node to the target model. Given that there is an active trigger for the node, we return one of its child nodes together with an extended homomorphism. How do we know that such a node and homomorphism exist? This is because the existing trigger is loaded for the target model but since it is a model, we can also show that it also needs to be satisfied for the model. The way in which the trigger is satisfied in the model dictates which child node we pick and how we define the homomorphisms for the fresh terms introduced by the trigger. This is already all that happens here but it is not quite trivial to show that the constructed `GroundTermMapping` is indeed a homomorphism. -/
noncomputable def hom_step_of_trg_ex
    (ct : ChaseTree obs kb)
    (m : FactSet sig)
    (m_is_model : m.modelsKb kb)
    (node : ct.NodeWithAddress)
    (prev_hom : GroundTermMapping sig)
    (prev_hom_is_homomorphism : prev_hom.isHomomorphism node.node.facts m)
    (trg_ex : exists_trigger_list obs kb.rules node.node node.subderivation.childNodes) :
    InductiveHomomorphismResult ct m :=
  let trg := Classical.choose trg_ex
  let trg_spec := Classical.choose_spec trg_ex
  let trg_active_for_current_step := trg_spec.left
  let trg_result_used_for_next_chase_step := trg_spec.right

  let trg_variant_for_m : RTrigger obs kb.rules := {
    val := {
      rule := trg.val.rule
      subs := fun t => prev_hom (trg.val.subs t)
    }
    property := trg.property
  }
  have trg_variant_loaded_for_m : trg_variant_for_m.val.loaded m := by
    have : trg_variant_for_m.val.loaded (prev_hom.applyFactSet node.node.facts) := by
      apply PreTrigger.term_mapping_preserves_loadedness
      . exact prev_hom_is_homomorphism.left
      . exact trg_active_for_current_step.left
    apply Set.subset_trans this
    exact prev_hom_is_homomorphism.right
  have trg_variant_satisfied_on_m : trg_variant_for_m.val.satisfied m := by
    have m_models_rule : m.modelsRule trg_variant_for_m.val.rule := by exact m_is_model.right trg.val.rule trg.property
    unfold FactSet.modelsRule at m_models_rule
    apply m_models_rule
    apply trg_variant_loaded_for_m

  let head_index_for_m_subs := Classical.choose trg_variant_satisfied_on_m
  let h_head_index_for_m_subs := Classical.choose_spec trg_variant_satisfied_on_m
  let obs_for_m_subs := Classical.choose h_head_index_for_m_subs
  let h_obs_at_head_index_for_m_subs := Classical.choose_spec h_head_index_for_m_subs

  let result_index_for_trg : Fin trg.val.mapped_head.length := ⟨head_index_for_m_subs.val, by unfold PreTrigger.mapped_head; simp; exact head_index_for_m_subs.isLt⟩

  let next_hom : GroundTermMapping sig := fun t =>
    let t_in_root := t ∈ node.node.facts.terms
    have t_in_root_dec := Classical.propDecidable t_in_root
    if t_in_root then prev_hom t else
      let t_fresh := t ∈ trg.val.fresh_terms_for_head_disjunct head_index_for_m_subs.val head_index_for_m_subs.isLt
      have t_fresh_dec := Classical.propDecidable t_fresh
      if t_fresh_true : t_fresh then
        obs_for_m_subs (trg.val.existential_var_for_fresh_term _ _ t t_fresh_true)
      else t

  have next_hom_id_const : next_hom.isIdOnConstants := by
    intro c
    simp only [next_hom]
    split
    . exact prev_hom_is_homomorphism.left
    . split
      case isFalse _ => rfl
      case isTrue h => apply False.elim; have contra := trg.val.term_functional_of_mem_fresh_terms _ h; simp [GroundTerm.func, GroundTerm.const] at contra

  ⟨(TreeDerivation.NodeWithAddress.cast_for_new_root_node node ((TreeDerivation.NodeWithAddress.childNodes node.subderivation)[head_index_for_m_subs.val]'(by rw [TreeDerivation.NodeWithAddress.length_childNodes, trg_result_used_for_next_chase_step, List.length_map, List.length_attach, List.length_zipIdx_with_lt, PreTrigger.length_mapped_head]; exact head_index_for_m_subs.isLt)), next_hom), by
    constructor
    . exact next_hom_id_const
    rintro mapped_f ⟨f, f_mem, mapped_f_eq⟩
    rw [node.subderivation.facts_childNodes (by apply TreeDerivation.NodeWithAddress.mem_childNodes_of_mem_childNodes; apply List.getElem_mem)] at f_mem
    rw [mapped_f_eq]
    cases f_mem with
    | inl f_mem =>
      apply prev_hom_is_homomorphism.right
      exists f; rw [TreeDerivation.NodeWithAddress.root_subderivation'] at f_mem; simp only [f_mem, true_and]
      apply TermMapping.apply_generalized_atom_congr_left
      intro t t_mem
      have t_mem : t ∈ node.node.facts.terms := by exists f
      simp [next_hom, t_mem]
    | inr f_mem =>
      have f_mem : f ∈ trg.val.mapped_head[result_index_for_trg.val] := by
        simp only [List.mem_toSet, TreeDerivation.NodeWithAddress.cast_for_new_root_node, TreeDerivation.NodeWithAddress.node_getElem_childNodes, trg_result_used_for_next_chase_step] at f_mem
        simp only [List.getElem_map, List.getElem_attach] at f_mem
        have : ((Classical.choose trg_ex).val.mapped_head.zipIdx_with_lt[head_index_for_m_subs.val]'(by rw [List.length_zipIdx_with_lt]; exact result_index_for_trg.isLt)).fst.toSet = ((Classical.choose trg_ex).val.mapped_head[head_index_for_m_subs.val]'(result_index_for_trg.isLt)).toSet := by rw [List.zipIdx_with_lt_getElem_fst_eq_getElem]
        simp only [this] at f_mem
        have : ((Classical.choose trg_ex).val.mapped_head.zipIdx_with_lt[head_index_for_m_subs.val]'(by rw [List.length_zipIdx_with_lt]; exact result_index_for_trg.isLt)).snd = ⟨head_index_for_m_subs.val, result_index_for_trg.isLt⟩ := by rw [List.zipIdx_with_lt_getElem_snd_eq_index]
        simp only [this] at f_mem
        simp only [ChaseNode.origin_result, Option.get_some] at f_mem
        exact f_mem
      apply h_obs_at_head_index_for_m_subs.right
      rw [List.mem_toSet]
      simp only [GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
      rw [List.mem_map]
      exists (trg.val.atom_for_result_fact result_index_for_trg f_mem); constructor
      . apply PreTrigger.atom_for_result_fact_mem_head
      conv => right; rw [← trg.val.apply_on_atom_for_result_fact_is_fact result_index_for_trg f_mem]
      rw [← PreTrigger.apply_subs_for_atom_eq]
      rw [← Function.comp_apply (f := TermMapping.apply_generalized_atom next_hom)]
      rw [← GroundTermMapping.applyFact.eq_def, ← GroundSubstitution.apply_function_free_atom_compose_of_isIdOnConstants _ _ next_hom_id_const]
      apply TermMapping.apply_generalized_atom_congr_left
      intro voc voc_mem
      cases voc with
      | const c => simp [GroundSubstitution.apply_var_or_const]
      | var v =>
        rw [GroundSubstitution.apply_var_or_const_compose_of_isIdOnConstants _ _ next_hom_id_const]
        rw [Function.comp_apply, PreTrigger.apply_subs_for_var_or_const_eq]
        simp only [GroundSubstitution.apply_var_or_const]
        cases Decidable.em (v ∈ trg.val.rule.frontier) with
        | inl v_front =>
          rw [h_obs_at_head_index_for_m_subs.left v v_front]
          rw [PreTrigger.apply_to_var_or_const_frontier_var _ _ _ v_front]
          simp only [trg_variant_for_m, next_hom]
          have : trg.val.subs v ∈ node.node.facts.terms := by
            apply FactSet.terms_subset_of_subset trg_active_for_current_step.left
            rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
            apply Or.inr
            exists v; constructor
            . apply Rule.frontier_subset_vars_body; exact v_front
            . rfl
          simp [this]
        | inr v_front =>
          have v_exis : v ∈ trg.val.rule.existential_vars_for_head_disjunct head_index_for_m_subs.val head_index_for_m_subs.isLt := by
            simp only [Rule.existential_vars_for_head_disjunct, List.mem_filter, decide_eq_true_eq]; constructor
            . rw [FunctionFreeConjunction.mem_vars];
              exists (trg.val.atom_for_result_fact result_index_for_trg f_mem); constructor
              . apply PreTrigger.atom_for_result_fact_mem_head
              . exact voc_mem
            . exact v_front
          have func_term_fresh : trg.val.functional_term_for_var result_index_for_trg.val v ∈ trg.val.fresh_terms_for_head_disjunct head_index_for_m_subs.val head_index_for_m_subs.isLt := by
            apply List.mem_map_of_mem; exact v_exis
          rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
          simp only [next_hom]
          have : ¬ trg.val.functional_term_for_var result_index_for_trg.val v ∈ node.node.facts.terms := by
            intro contra
            apply trg_active_for_current_step.right
            apply obs.contains_trg_result_implies_cond result_index_for_trg
            apply ChaseTree.result_of_trigger_introducing_functional_term_occurs_in_chase node contra
            exact func_term_fresh
          simp only [this, ↓reduceIte]
          simp only [func_term_fresh, ↓reduceDIte]
          rw [PreTrigger.existential_var_for_fresh_term_after_functional_term_for_var]
          exact v_exis
  ⟩

/-- The node that we pick in `hom_step_of_trg_ex` is in the childNodes of the previous node. This is trivial. -/
theorem mem_childNodes_of_mem_hom_step_of_trg_ex
    {ct : ChaseTree obs kb}
    {m : FactSet sig}
    {m_is_model : m.modelsKb kb}
    {node : ct.NodeWithAddress}
    {prev_hom : GroundTermMapping sig}
    {prev_hom_is_homomorphism : prev_hom.isHomomorphism node.node.facts m}
    {trg_ex : exists_trigger_list obs kb.rules node.node node.subderivation.childNodes} :
    (hom_step_of_trg_ex ct m m_is_model node prev_hom prev_hom_is_homomorphism trg_ex).val.fst ∈ (TreeDerivation.NodeWithAddress.childNodes node.subderivation).map (fun c => TreeDerivation.NodeWithAddress.cast_for_new_root_node _ c) := by simp only [hom_step_of_trg_ex]; apply List.mem_map_of_mem; apply List.getElem_mem

/-- The homomorphisms that we construct in `hom_step_of_trg_ex` agrees with the previous one on all terms in the previous node. This is also trivial. -/
theorem hom_extends_prev_in_hom_step_of_trg_ex
    {ct : ChaseTree obs kb}
    {m : FactSet sig}
    {m_is_model : m.modelsKb kb}
    {node : ct.NodeWithAddress}
    {prev_hom : GroundTermMapping sig}
    {prev_hom_is_homomorphism : prev_hom.isHomomorphism node.node.facts m}
    {trg_ex : exists_trigger_list obs kb.rules node.node node.subderivation.childNodes} :
    ∀ t ∈ node.node.facts.terms, prev_hom t = (hom_step_of_trg_ex ct m m_is_model node prev_hom prev_hom_is_homomorphism trg_ex).val.snd t := by intro t t_mem; simp only [hom_step_of_trg_ex, t_mem, ↓reduceIte]

/-- When extending the `InductiveHomomorphismResult` from one step to the next, we do not necessarily know that a trigger is active for the current node. Indeed the chase might just have already finished. So we do a simple case distinction here and return an `Option` either with the result from `hom_step_of_trg_ex` or simply none. -/
noncomputable def hom_step
    (ct : ChaseTree obs kb)
    (m : FactSet sig)
    (m_is_model : m.modelsKb kb)
    (prev_res : InductiveHomomorphismResult ct m) :
    Option (InductiveHomomorphismResult ct m) :=
  let trg_ex := exists_trigger_list obs kb.rules prev_res.val.fst.node prev_res.val.fst.subderivation.childNodes
  have _trg_eq_dec := Classical.propDecidable trg_ex
  if trg_ex_true : trg_ex then
    some (hom_step_of_trg_ex ct m m_is_model prev_res.val.fst prev_res.val.snd prev_res.property trg_ex_true)
  else
    none

/-- If there is a new node returned by `hom_step`, then it is in the `childNodes` of the current node. -/
theorem mem_childNodes_of_mem_hom_step
    {ct : ChaseTree obs kb}
    {m : FactSet sig}
    {m_is_model : m.modelsKb kb}
    {prev_res : InductiveHomomorphismResult ct m} :
    ∀ res ∈ hom_step ct m m_is_model prev_res, res.val.fst ∈ (TreeDerivation.NodeWithAddress.childNodes prev_res.val.fst.subderivation).map (fun c => TreeDerivation.NodeWithAddress.cast_for_new_root_node _ c) := by
  intro res
  simp only [hom_step]
  split
  . intro res_mem
    rw [Option.mem_def, Option.some_inj] at res_mem
    rw [← res_mem]
    exact mem_childNodes_of_mem_hom_step_of_trg_ex
  . simp

/-- If `hom_step` returns none, then the current node does not have any children. -/
theorem childNodes_empty_of_hom_step_none
    {ct : ChaseTree obs kb}
    {m : FactSet sig}
    {m_is_model : m.modelsKb kb}
    {prev_res : InductiveHomomorphismResult ct m} :
    hom_step ct m m_is_model prev_res = none -> (TreeDerivation.NodeWithAddress.childNodes prev_res.val.fst.subderivation) = [] := by
  simp only [hom_step]
  split
  . simp
  . intros
    have trg_ex := ct.triggers_exist prev_res.val.fst.address
    rw [FiniteDegreeTree.root_drop] at trg_ex
    specialize trg_ex _ prev_res.val.fst.eq
    cases trg_ex with
    | inl trg_ex => contradiction
    | inr trg_ex =>
      have : (TreeDerivation.NodeWithAddress.childNodes prev_res.val.fst.subderivation).map TreeDerivation.NodeWithAddress.node = [] := by
        rw [← TreeDerivation.NodeWithAddress.childNodes_eq_childNodes]
        exact trg_ex.right
      rw [List.map_eq_nil_iff] at this
      exact this

/-- The homomorphism returns in `hom_step` agrees with the current one on all terms from the current node. -/
theorem hom_extends_prev_in_hom_step
    {ct : ChaseTree obs kb}
    {m : FactSet sig}
    {m_is_model : m.modelsKb kb}
    {prev_res : InductiveHomomorphismResult ct m} :
    ∀ pair ∈ hom_step ct m m_is_model prev_res, ∀ t ∈ prev_res.val.fst.node.facts.terms, prev_res.val.snd t = pair.val.snd t := by
  intro res
  simp only [hom_step]
  split
  . intro res_mem
    rw [Option.mem_def, Option.some_inj] at res_mem
    rw [← res_mem]
    exact hom_extends_prev_in_hom_step_of_trg_ex
  . simp

/-- As outlined at the very top of this file, we now use `TreeDerivation.generate_derivation` with the `hom_step` generator to obtain the branch in the tree that yields the result `FactSet` for which the combined `GroundTermMapping`s form a homomorphism into the target model. -/
theorem chaseTreeResultIsUniversal (ct : ChaseTree obs kb) : ∀ (m : FactSet sig), m.modelsKb kb -> ∃ (fs : FactSet sig) (h : GroundTermMapping sig), fs ∈ ct.result ∧ h.isHomomorphism fs m := by
  intro m m_is_model

  let start : InductiveHomomorphismResult ct m := ⟨(TreeDerivation.NodeWithAddress.root ct.toTreeDerivation, id), by
    simp only [TreeDerivation.NodeWithAddress.root]; rw [ct.database_first']; simp only
    constructor
    . unfold GroundTermMapping.isIdOnConstants; simp
    . rintro e ⟨f, hf⟩
      apply m_is_model.left
      have : f = e := by have hfr := hf.right; rw [hfr]; simp [TermMapping.apply_generalized_atom]
      rw [this] at hf
      exact hf.left⟩

  let derivs_with_homs : PossiblyInfiniteList (ChaseDerivation obs kb.rules × GroundTermMapping sig) :=
    PossiblyInfiniteList.generate start (hom_step ct m m_is_model) (fun res =>
      let deriv : ChaseDerivation obs kb.rules := ct.generate_subderivation res (hom_step ct m m_is_model)
        (fun res => res.val.fst)
        (by intro prev res res_mem; exact mem_childNodes_of_mem_hom_step res res_mem)
        (by intro prev eq_none
            have : prev.val.fst.subderivation.childNodes = [] := by
              rw [TreeDerivation.NodeWithAddress.childNodes_eq_childNodes, List.map_eq_nil_iff]
              exact childNodes_empty_of_hom_step_none eq_none
            rw [TreeDerivation.childNodes_eq, List.map_eq_nil_iff] at this
            exact this)
      (deriv, res.val.snd)
    )

  have derivs_with_homs_properties : ∀ step ∈ derivs_with_homs, step.snd.isHomomorphism step.fst.head.facts m := by
    intro step step_mem
    simp only [derivs_with_homs, PossiblyInfiniteList.mem_iff] at step_mem
    rcases step_mem with ⟨_, step_mem⟩
    rw [PossiblyInfiniteList.get?_generate, Option.map_eq_some_iff] at step_mem
    rcases step_mem with ⟨res, step_mem⟩
    rw [← step_mem.right, TreeDerivation.head_generate_subderivation]
    exact res.property

  let deriv := (derivs_with_homs.head.get (by simp [derivs_with_homs, PossiblyInfiniteList.head_generate])).fst
  have deriv_mem : deriv ∈ ct.branches := by
    simp only [deriv, derivs_with_homs, PossiblyInfiniteList.head_generate, Option.map_some, Option.get_some]
    apply ct.generate_subderivation_mem_branches
    rfl

  let branch := ct.chaseBranch_for_branch deriv_mem

  have deriv_eq : deriv.branch = derivs_with_homs.map (fun step => step.fst.head) := by
    let pairs : PossiblyInfiniteList (InductiveHomomorphismResult ct m) :=
      PossiblyInfiniteList.generate start (hom_step ct m m_is_model) id
    have pairs_eq : pairs.map (fun res => res.val.fst.node) = derivs_with_homs.map (fun step => step.fst.head) := by
      simp only [pairs, derivs_with_homs]
      apply PossiblyInfiniteList.ext; intro n
      simp only [PossiblyInfiniteList.get?_map, PossiblyInfiniteList.get?_generate, Option.map_map]
      apply Option.map_congr
      intro _ _
      simp only [Function.comp_apply, id_eq]
      rw [TreeDerivation.head_generate_subderivation]
    rw [← pairs_eq]
    apply PossiblyInfiniteList.ext; intro n
    rw [PossiblyInfiniteList.get?_map]
    simp only [pairs, deriv, derivs_with_homs, PossiblyInfiniteList.head_generate, Option.map_some, Option.get_some]
    simp only [TreeDerivation.generate_subderivation, TreeDerivation.generate_branch, TreeDerivation.derivation_for_branch, FiniteDegreeTree.get?_generate_branch]
    simp only [PossiblyInfiniteList.get?_generate, Option.map_map]
    apply Option.map_congr
    intro _ _
    simp only [Function.comp_apply, id_eq]
    simp only [TreeDerivation.toFiniteDegreeTreeWithRoot]
    rw [← TreeDerivation.root.eq_def, TreeDerivation.NodeWithAddress.root_subderivation']

  have homs_extend_each_other : ∀ n, ∀ step ∈ derivs_with_homs.get? n, ∀ step2 ∈ derivs_with_homs.drop n,
      ∀ t ∈ step.fst.head.facts.terms, step.snd t = step2.snd t := by
    intro n step step_mem step2 step2_mem t t_mem
    let step2 : (derivs_with_homs.drop n).Element := ⟨step2, step2_mem⟩
    show step.snd t = step2.val.snd t
    induction step2 using PossiblyInfiniteList.mem_rec with
    | head head head_mem => rw [PossiblyInfiniteList.head_drop, step_mem, Option.mem_def, Option.some_inj] at head_mem; rw [head_mem]
    | step l2 suffix ih next next_mem =>
      rcases ih with ⟨head, head_mem, ih⟩
      rw [ih]
      rw [PossiblyInfiniteList.IsSuffix_iff] at suffix; rcases suffix with ⟨m, suffix⟩
      simp only [derivs_with_homs] at suffix
      simp only [← suffix, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_drop] at head_mem
      simp only [← suffix, PossiblyInfiniteList.tail_drop, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_drop, Nat.add_succ] at next_mem
      rw [PossiblyInfiniteList.get?_generate, Option.mem_def, Option.map_eq_some_iff] at head_mem
      rcases head_mem with ⟨pair, pair_mem, head_mem⟩
      rw [PossiblyInfiniteList.get?_succ_generate, Option.mem_def, Option.map_eq_some_iff] at next_mem
      rcases next_mem with ⟨pair2, pair2_mem, next_mem⟩
      rw [pair_mem] at pair2_mem
      rw [Option.bind_some] at pair2_mem
      simp only [← head_mem, ← next_mem]
      apply hom_extends_prev_in_hom_step _ pair2_mem
      apply FactSet.terms_subset_of_subset _ _ t_mem
      have step_mem_deriv : deriv.branch.get? n = some step.fst.head := by
        rw [← PossiblyInfiniteList.head_drop]
        rw [deriv_eq, PossiblyInfiniteList.head_drop, PossiblyInfiniteList.get?_map, step_mem]
        simp
      let node1 : deriv.Node := ⟨step.fst.head, by exists n⟩
      have pair_mem_deriv : deriv.branch.get? (n+m) = some pair.val.fst.node := by
        rw [deriv_eq]
        simp only [derivs_with_homs, PossiblyInfiniteList.get?_map, PossiblyInfiniteList.get?_generate]
        rw [pair_mem]
        simp only [Option.map_some, Option.some_inj]
        rw [TreeDerivation.head_generate_subderivation]
      let node2 : deriv.Node := ⟨pair.val.fst.node, by exists (n + m)⟩
      have prec : node1 ≼ node2 := by
        exists deriv.derivation_for_branch_suffix _ (deriv.branch.IsSuffix_drop n) (by rw [PossiblyInfiniteList.head_drop, step_mem_deriv]; simp)
        simp only [ChaseDerivationSkeleton.derivation_for_branch_suffix]
        constructor
        . exact deriv.branch.IsSuffix_drop n
        constructor
        . simp only [ChaseDerivationSkeleton.head, PossiblyInfiniteList.head_drop]
          conv => left; left; rw [step_mem_deriv]
          simp [node1]
        . exists m
      exact deriv.facts_node_subset_of_prec prec

  let global_h : GroundTermMapping sig := fun t =>
    let t_mem := ∃ step ∈ derivs_with_homs, t ∈ step.fst.head.facts.terms
    have t_mem_dec := Classical.propDecidable t_mem
    if t_mem_true : t_mem then
      let step := Classical.choose t_mem_true
      let target_h := step.snd
      target_h t
    else
      t

  have global_h_eq_each_hom : ∀ step ∈ derivs_with_homs, ∀ f ∈ step.fst.head.facts, global_h.applyFact f = step.snd.applyFact f := by
    intro step step_mem f f_mem
    apply TermMapping.apply_generalized_atom_congr_left
    intro t t_mem
    simp only [global_h]
    split
    case a.isFalse not_mem =>
      apply False.elim
      apply not_mem
      exists step; simp only [step_mem, true_and]
      exists f
    case a.isTrue t_mem_true =>
      rcases step_mem with ⟨j, step_mem⟩
      let step2 := Classical.choose t_mem_true
      rcases Classical.choose_spec t_mem_true with ⟨⟨i, step2_mem⟩, t_mem⟩
      cases Nat.le_total i j with
      | inl i_le_j =>
        rcases Nat.le.dest i_le_j with ⟨k, i_le_j⟩
        apply homs_extend_each_other i step2 step2_mem step
        . rw [PossiblyInfiniteList.mem_iff]; exists k; rw [PossiblyInfiniteList.get?_drop, i_le_j]; exact step_mem
        . exact t_mem
      | inr j_le_i =>
        rcases Nat.le.dest j_le_i with ⟨k, j_le_i⟩
        apply Eq.symm
        apply homs_extend_each_other j step step_mem step2
        . rw [PossiblyInfiniteList.mem_iff]; exists k; rw [PossiblyInfiniteList.get?_drop, j_le_i]; exact step2_mem
        . exists f

  have global_h_hom : ∀ node ∈ deriv, global_h.applyFactSet node.facts ⊆ m := by
    intro node node_mem
    have node_mem : node ∈ deriv.branch := node_mem
    rw [deriv_eq, PossiblyInfiniteList.mem_map] at node_mem
    rcases node_mem with ⟨step, step_mem, node_mem⟩
    rintro f' ⟨f, f_mem, f'_eq⟩
    rw [← node_mem] at f_mem
    rw [f'_eq, ← GroundTermMapping.applyFact.eq_def, global_h_eq_each_hom step step_mem f f_mem]
    apply (derivs_with_homs_properties _ step_mem).right
    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
    exact f_mem

  exists branch.result, global_h; constructor; exists deriv; constructor
  . intro c
    simp only [global_h]
    split
    case isFalse _ => rfl
    case isTrue t_mem_true =>
      have ⟨step_mem, _⟩ := Classical.choose_spec t_mem_true
      apply (derivs_with_homs_properties _ step_mem).left
  . rintro f' ⟨f, ⟨node, node_mem, f_mem⟩, f'_eq⟩
    rw [f'_eq]
    apply global_h_hom node node_mem
    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
    exact f_mem

