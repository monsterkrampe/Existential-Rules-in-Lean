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

In the proof of `chaseTreeResultIsUniversal`, we leverage the `FiniteDegreeTree.generate_branch` function with `hom_step` as the generator function. By that, with a bit of massage, we can easily show that the constructed branch is indeed a branch in the tree using `FiniteDegreeTree.generate_branch_mem_branches`.
Besides that, all the homomorphisms from the individual steps need to be combined into a single function. The definition is not too hard and all relevant properties are also not too hard to show once we can establish that the homomorphisms for each step always extend the previous one.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

/-- The `InductiveHomomorphismResult` is used for the step-wise construction is forms the element that is the input and output of the generator function used in `FiniteDegreeTree.generate_branch` later. It consists of a node in the chase tree and a `GroundTermMapping` that is a homomorphism from the node to the target model. The generated branch is the chain of all the generated nodes.  -/
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

/-- As outlined at the very top of this file, we now use `FiniteDegreeTree.generate_branch` with the `hom_step` generator to obtain the branch in the tree that yields the result `FactSet` for which the combined `GroundTermMapping`s form a homomorphism into the target model. -/
theorem chaseTreeResultIsUniversal (ct : ChaseTree obs kb) : ∀ (m : FactSet sig), m.modelsKb kb -> ∃ (fs : FactSet sig) (h : GroundTermMapping sig), fs ∈ ct.result ∧ h.isHomomorphism fs m := by
  intro m m_is_model

  let start : Option (InductiveHomomorphismResult ct m) := some ⟨(TreeDerivation.NodeWithAddress.root ct.toTreeDerivation, id), by
    simp only [TreeDerivation.NodeWithAddress.root]; rw [ct.database_first']; simp only
    constructor
    . unfold GroundTermMapping.isIdOnConstants; simp
    . rintro e ⟨f, hf⟩
      apply m_is_model.left
      have : f = e := by have hfr := hf.right; rw [hfr]; simp [TermMapping.apply_generalized_atom]
      rw [this] at hf
      exact hf.left⟩
  let nodes_with_homs := PossiblyInfiniteList.generate start (hom_step ct m m_is_model) id
  have nodes_with_homs_properties : ∀ pair ∈ nodes_with_homs, pair.val.snd.isHomomorphism pair.val.fst.node.facts m := by intro pair _; exact pair.property
  let nodes : PossiblyInfiniteList (ChaseNode obs kb.rules) := FiniteDegreeTree.generate_branch start (hom_step ct m m_is_model) (fun res => res.val.fst.subderivation.toFiniteDegreeTreeWithRoot)
  let homs : PossiblyInfiniteList (GroundTermMapping sig) := PossiblyInfiniteList.generate start (hom_step ct m m_is_model) (fun res => res.val.snd)

  have nodes_eq : nodes = nodes_with_homs.map (fun res => res.val.fst.node) := by
    apply PossiblyInfiniteList.ext; intro n
    simp only [nodes, nodes_with_homs, FiniteDegreeTree.get?_generate_branch, PossiblyInfiniteList.get?_map, PossiblyInfiniteList.get?_generate]
    cases (InfiniteList.iterate start fun x => x.bind (hom_step ct m m_is_model)).get n with
    | none => simp
    | some _ => simp only [Option.map_some, id, TreeDerivation.toFiniteDegreeTreeWithRoot, ← TreeDerivation.root.eq_def, TreeDerivation.NodeWithAddress.root_subderivation']
  have homs_eq : homs = nodes_with_homs.map (fun res => res.val.snd) := by
    apply PossiblyInfiniteList.ext; intro n
    simp only [homs, nodes_with_homs, PossiblyInfiniteList.get?_map, PossiblyInfiniteList.get?_generate]
    cases (InfiniteList.iterate start fun x => x.bind (hom_step ct m m_is_model)).get n <;> simp

  have nodes_mem : nodes ∈ ct.tree.branches := by
    apply FiniteDegreeTree.generate_branch_mem_branches
    . intro prev res res_mem
      conv => left; simp only [TreeDerivation.toFiniteDegreeTreeWithRoot]
      rw [← TreeDerivation.mem_childTrees_iff]
      have := mem_childNodes_of_mem_hom_step res res_mem
      rw [List.mem_map] at this
      rcases this with ⟨node, node_mem, res_eq⟩
      have : res.val.fst.subderivation = node.subderivation := by
        rw [TreeDerivation.mk.injEq, ← res_eq]; simp only [TreeDerivation.NodeWithAddress.subderivation, TreeDerivation.derivation_for_suffix, TreeDerivation.NodeWithAddress.cast_for_new_root_node, FiniteDegreeTree.drop_drop]
      rw [this]
      apply TreeDerivation.NodeWithAddress.subderivation_mem_childTrees_of_mem_childNodes
      exact node_mem
    . intro prev eq_none
      have : (TreeDerivation.NodeWithAddress.childNodes prev.val.fst.subderivation).map TreeDerivation.NodeWithAddress.node = [] := by
        rw [List.map_eq_nil_iff]; exact childNodes_empty_of_hom_step_none eq_none
      rw [← TreeDerivation.NodeWithAddress.childNodes_eq_childNodes, TreeDerivation.childNodes_eq, List.map_eq_nil_iff] at this
      simp only [TreeDerivation.childTrees, List.map_eq_nil_iff, List.attach_eq_nil_iff] at this
      exact this
    . simp [start]
  let deriv := (ct.derivation_for_branch _ nodes_mem)
  have deriv_mem : deriv ∈ ct.branches := nodes_mem
  let branch := ct.chaseBranch_for_branch deriv_mem

  have homs_extend_each_other : ∀ (i k : Nat), ∀ node ∈ nodes.get? i, ∀ hom1 ∈ homs.get? i, ∀ hom2 ∈ homs.get? (i + k), ∀ t ∈ node.facts.terms, hom1 t = hom2 t := by
    intro i k node node_mem hom1 hom1_mem hom2 hom2_mem t t_mem
    induction k generalizing hom2 with
    | zero => rw [Nat.add_zero, hom1_mem, Option.mem_def, Option.some_inj] at hom2_mem; rw [hom2_mem]
    | succ k ih =>
      rw [← Nat.add_assoc, homs_eq, PossiblyInfiniteList.get?_map] at hom2_mem
      simp only [nodes_with_homs, PossiblyInfiniteList.get?_succ_generate] at hom2_mem
      rw [Option.mem_def, Option.map_eq_some_iff, Option.map_id, id_eq] at hom2_mem
      rcases hom2_mem with ⟨pair, pair_mem, hom2_mem⟩
      rw [Option.bind_eq_some_iff] at pair_mem
      rcases pair_mem with ⟨prev_pair, prev_pair_mem, pair_mem⟩
      rw [ih prev_pair.val.snd (by rw [homs_eq, PossiblyInfiniteList.get?_map]; apply Option.mem_map_of_mem; simp only [nodes_with_homs, PossiblyInfiniteList.get?_generate, Option.map_id, id_eq]; exact prev_pair_mem), ← hom2_mem]
      apply hom_extends_prev_in_hom_step _ pair_mem
      apply FactSet.terms_subset_of_subset _ _ t_mem
      let node1 : deriv.Node := ⟨node, by exists i⟩
      let node2 : deriv.Node := ⟨prev_pair.val.fst.node, by
        exists (i + k)
        simp only [deriv, TreeDerivation.derivation_for_branch]
        rw [← Option.mem_def, ← PossiblyInfiniteList.get?.eq_def, nodes_eq, PossiblyInfiniteList.get?_map]
        simp only [nodes_with_homs, PossiblyInfiniteList.get?_generate, Option.map_id, id_eq]
        apply Option.mem_map_of_mem
        exact prev_pair_mem⟩
      have prec : node1 ≼ node2 := by
        exists deriv.derivation_for_branch_suffix _ (nodes.IsSuffix_drop i) (by rw [PossiblyInfiniteList.head_drop, node_mem]; simp)
        simp only [ChaseDerivation.derivation_for_branch_suffix]
        constructor
        . exact nodes.IsSuffix_drop i
        constructor
        . simp only [ChaseDerivation.head, PossiblyInfiniteList.head_drop]
          conv => left; left; rw [node_mem]
          simp [node1]
        . exists k
          rw [← PossiblyInfiniteList.get?.eq_def]
          simp only [PossiblyInfiniteList.get?_drop]
          rw [← Option.mem_def, nodes_eq, PossiblyInfiniteList.get?_map]
          simp only [nodes_with_homs, PossiblyInfiniteList.get?_generate, Option.map_id, id_eq]
          apply Option.mem_map_of_mem
          exact prev_pair_mem
      have := deriv.facts_node_subset_of_prec prec
      exact this

  let global_h : GroundTermMapping sig := fun t =>
    let t_mem := t ∈ branch.result.terms
    have t_mem_dec := Classical.propDecidable t_mem
    if t_mem_true : t_mem then
      have node_mem := (Classical.choose_spec (Classical.choose_spec t_mem_true).left).left
      let i := Classical.choose node_mem
      have i_spec := Classical.choose_spec node_mem
      let target_h := ((homs.get? i).get (by
        rw [← PossiblyInfiniteList.get?.eq_def] at i_spec
        simp only [branch, ChaseTree.chaseBranch_for_branch, deriv, TreeDerivation.derivation_for_branch] at i_spec
        conv at i_spec => left; left; rw [nodes_eq]
        rw [PossiblyInfiniteList.get?_map, Option.map_eq_some_iff] at i_spec
        rcases i_spec with ⟨_, i_spec, _⟩
        rw [homs_eq, PossiblyInfiniteList.get?_map, i_spec]
        simp
      ))
      target_h t
    else
      t

  have global_h_eq_each_hom : ∀ pair ∈ nodes_with_homs, ∀ f ∈ pair.val.fst.node.facts, global_h.applyFact f = pair.val.snd.applyFact f := by
    intro pair pair_mem f f_mem
    apply TermMapping.apply_generalized_atom_congr_left
    intro t t_mem
    simp only [global_h]
    split
    case a.isFalse not_mem =>
      apply False.elim
      apply not_mem
      exists f; simp only [t_mem, and_true]
      apply branch.facts_node_subset_result pair.val.fst.node
      . simp only [branch, ChaseTree.chaseBranch_for_branch, deriv, TreeDerivation.derivation_for_branch]
        show pair.val.fst.node ∈ nodes
        rw [nodes_eq, PossiblyInfiniteList.mem_map]
        exists pair
      . exact f_mem
    case a.isTrue t_mem_true =>
      rcases pair_mem with ⟨j, pair_mem⟩
      have : homs.get? j = some pair.val.snd := by
        rw [homs_eq, PossiblyInfiniteList.get?_map, Option.map_eq_some_iff]; exists pair
      rw [Option.eq_some_iff_get_eq] at this
      rcases this with ⟨_, this⟩
      rw [← this]
      have node_mem := (Classical.choose_spec (Classical.choose_spec t_mem_true).left).left
      let i := Classical.choose node_mem
      have i_spec := Classical.choose_spec node_mem
      cases Nat.le_total i j with
      | inl i_le_j =>
        rcases Nat.le.dest i_le_j with ⟨k, i_le_j⟩
        conv => right; fun; left; rw [← i_le_j]
        apply homs_extend_each_other i k _ i_spec
        . simp [i]
        . simp
        . exact ⟨_, ⟨(Classical.choose_spec (Classical.choose_spec t_mem_true).left).right, (Classical.choose_spec t_mem_true).right⟩⟩
      | inr j_le_i =>
        rcases Nat.le.dest j_le_i with ⟨k, j_le_i⟩
        simp only [i] at j_le_i
        conv => left; fun; left; rw [← j_le_i]
        apply Eq.symm
        apply homs_extend_each_other j k pair.val.fst.node
        . rw [nodes_eq, PossiblyInfiniteList.get?_map]; apply Option.mem_map_of_mem; exact pair_mem
        . simp
        . simp
        . exists f

  have global_h_hom : ∀ node ∈ nodes, global_h.applyFactSet node.facts ⊆ m := by
    intro node node_mem
    rw [nodes_eq, PossiblyInfiniteList.mem_map] at node_mem
    rcases node_mem with ⟨pair, pair_mem, node_eq⟩
    rintro f' ⟨f, f_mem, f'_eq⟩
    rw [← node_eq] at f_mem
    rw [f'_eq, ← GroundTermMapping.applyFact.eq_def, global_h_eq_each_hom pair pair_mem f f_mem]
    apply pair.property.right; apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set; exact f_mem

  exists branch.result, global_h; constructor; exists deriv; constructor
  . intro c
    simp only [global_h]
    split
    case isFalse _ => rfl
    case isTrue t_mem_true =>
      have node_mem := (Classical.choose_spec (Classical.choose_spec t_mem_true).left).left
      let i := Classical.choose node_mem
      conv => left; fun; left; left; rw [homs_eq]
      conv => left; fun; left; rw [PossiblyInfiniteList.get?_map]
      rw [Option.get_map]
      apply (nodes_with_homs_properties _ _).left
      exists i
      simp only [Option.some_get]
      rfl
  . rintro f' ⟨f, ⟨node, node_mem, f_mem⟩, f'_eq⟩
    rw [f'_eq]
    apply global_h_hom node node_mem
    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
    exact f_mem

