/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.ChaseTree

/-!
# Chase Tree Result is Universal Model Set

This whole file is dedicated to showing that the result of a `ChaseTree`
is a universal model set [UniversalModelSet].
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

In the proof of `chaseTreeResultIsUniversal`, we leverage the `TreeDerivation.generate_subderivation` function with `hom_step` as the generator function.
Besides that, all the homomorphisms from the individual steps need to be combined into a single function. The definition is not too hard and all relevant properties are also not too hard to show once we can establish that the homomorphisms for each step always extend the previous one.
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]
variable {obs : ObsolescenceCondition sig} {kb : KnowledgeBase sig}

/-- The `InductiveHomomorphismResult` is used for the step-wise construction is forms the element that is the input and output of the generator function used in `TreeDerivation.generate_subderivation` later. It consists of a node in the chase tree and a `GroundTermMapping` that is a homomorphism from the node to the target model. The generated branch is the chain of all the generated nodes.  -/
abbrev InductiveHomomorphismResult {N : Type u} [CN : ChaseNode N obs kb.rules] (ct : ChaseTree N obs kb) (m : FactSet sig) :=
  { pair : ct.NodeWithAddress × (GroundTermMapping sig) // pair.snd.isHomomorphism (CN.outgoingFacts pair.fst.node) m }

/-- Consider any node in the chase tree together with a homomorphism from this node to the target model. Given that the list of child nodes is not empty, we return one of child node together with an extended homomorphism. How do we know that such a node and homomorphism exist? If the list of children is not empty, there needs to exists a trigger that has been used to derive them. The existing trigger is loaded for the target model but since it is a model, we can also show that it also needs to be satisfied for the model. The way in which the trigger is satisfied in the model dictates which child node we pick and how we define the homomorphisms for the fresh terms introduced by the trigger. This is already all that happens here but it is not quite trivial to show that the constructed `GroundTermMapping` is indeed a homomorphism. -/
noncomputable def hom_step_of_trg_ex
    {N : Type u} [CN : ChaseNode N obs kb.rules] (out_sub_in : CN.out_sub_in)
    (ct : ChaseTree N obs kb)
    (m : FactSet sig)
    (m_is_model : m.modelsKb kb)
    (node : ct.NodeWithAddress)
    (prev_hom : GroundTermMapping sig)
    (prev_hom_is_homomorphism : prev_hom.isHomomorphism (CN.outgoingFacts node.node) m)
    (children_ne_nil : node.subderivation.childNodes ≠ [])
    (trg_inactive_of_fresh_term_present : ∀ (trg : RTrigger obs kb.rules) i lt t, t ∈ trg.val.fresh_terms_for_head_disjunct i lt -> t ∈ (CN.outgoingFacts node.node).terms -> ¬ trg.val.active (CN.outgoingFacts node.node)) :
    InductiveHomomorphismResult ct m :=
  have trg_ex := node.triggers_exist children_ne_nil
  let trg := Classical.choose trg_ex
  have trg_spec := Classical.choose_spec trg_ex
  have trg_spec_act := trg_spec.left
  have trg_spec_facts_eq := trg_spec.right.left
  have trg_spec_orig_eq := trg_spec.right.right.left
  have trg_spec_idx_eq := trg_spec.right.right.right

  let trg_variant_for_m : RTrigger obs kb.rules := {
    val := {
      rule := trg.val.rule
      subs := fun t => prev_hom (trg.val.subs t)
    }
    property := trg.property
  }
  have trg_variant_loaded_for_m : trg_variant_for_m.val.loaded m := by
    suffices trg_variant_for_m.val.loaded (prev_hom.applyFactSet (CN.outgoingFacts node.node)) by
      exact Set.subset_trans this prev_hom_is_homomorphism.right
    apply PreTrigger.term_mapping_preserves_loadedness
    . exact prev_hom_is_homomorphism.left
    . exact trg_spec_act.left
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
    let t_in_node := t ∈ (CN.outgoingFacts node.node).terms
    have t_in_node_dec := Classical.propDecidable t_in_node
    if t_in_node then prev_hom t else
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
      case isTrue h => rcases trg.val.term_functional_of_mem_fresh_terms _ h with ⟨_, _, _, contra⟩; have contra := Eq.symm contra; simp [GroundTerm.func_neq_const] at contra

  ⟨((node.childNodes[head_index_for_m_subs.val]'(by
      have length_mapped_eq : (node.subderivation.childNodes.map CN.ingoingFacts).length = node.subderivation.childNodes.length := by simp
      rw [TreeDerivation.NodeWithAddress.length_childNodes, ← length_mapped_eq, trg_spec_facts_eq, List.length_map, PreTrigger.length_mapped_head]
      exact head_index_for_m_subs.isLt)), next_hom), by
    constructor
    . exact next_hom_id_const
    intro mapped_f
    rw [GroundTermMapping.mem_applyFactSet]
    intro ⟨f, f_mem, mapped_f_eq⟩
    have f_mem := out_sub_in _ f_mem
    rw [node.subderivation.facts_childNodes (by apply TreeDerivation.NodeWithAddress.mem_childNodes_of_mem_childNodes; apply List.getElem_mem)] at f_mem
    rw [mapped_f_eq]
    cases f_mem with
    | inl f_mem =>
      apply prev_hom_is_homomorphism.right
      rw [GroundTermMapping.mem_applyFactSet]
      exists f; rw [TreeDerivation.NodeWithAddress.root_subderivation'] at f_mem; simp only [f_mem, true_and]
      apply TermMapping.apply_generalized_atom_congr_left
      intro t t_mem
      have t_mem : t ∈ (CN.outgoingFacts node.node).terms := by exists f
      simp [next_hom, t_mem]
    | inr f_mem =>
      have f_mem : f ∈ trg.val.mapped_head[result_index_for_trg.val] := by
        -- this is similar to the proof of ChaseNode.succ_of_mem_succ_list
        have lt : head_index_for_m_subs.val < node.subderivation.childNodes.length := by
          have length_mapped_eq : (node.subderivation.childNodes.map CN.ingoingFacts).length = node.subderivation.childNodes.length := by simp
          rw [← length_mapped_eq, trg_spec_facts_eq, List.length_map, PreTrigger.length_mapped_head]
          exact head_index_for_m_subs.isLt
        simp only [TreeDerivation.NodeWithAddress.node_getElem_childNodes] at f_mem
        specialize trg_spec_orig_eq (node.subderivation.childNodes[head_index_for_m_subs.val]) (by simp)
        rw [Option.map_eq_some_iff] at trg_spec_orig_eq; rcases trg_spec_orig_eq with ⟨orig, orig_eq, trg_eq⟩
        rw [List.mem_toSet, CN.origin_result_eq _ (trg := trg.val) (i := result_index_for_trg.val)] at f_mem; exact f_mem
        . simp only [orig_eq, Option.get_some, trg_eq]; rfl
        . specialize trg_spec_idx_eq (node.subderivation.childNodes[head_index_for_m_subs.val], result_index_for_trg.val) (by grind)
          rw [orig_eq, Option.map_some, Option.some_inj] at trg_spec_idx_eq; simp only at trg_spec_idx_eq
          simp only [← trg_spec_idx_eq]
          grind
      apply h_obs_at_head_index_for_m_subs.right
      rw [List.mem_toSet]
      rw [GroundSubstitution.apply_function_free_conj, TermMapping.apply_generalized_atom_list]
      rw [List.mem_map]
      exists (trg.val.atom_for_result_fact result_index_for_trg f_mem); constructor
      . apply PreTrigger.atom_for_result_fact_mem_head
      conv => right; rw [← trg.val.apply_on_atom_for_result_fact_is_fact result_index_for_trg f_mem]
      rw [← PreTrigger.apply_subs_for_atom_eq]
      unfold GroundTermMapping.applyFact
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
          suffices trg.val.subs v ∈ (CN.outgoingFacts node.node).terms by simp [this]
          apply FactSet.terms_subset_of_subset trg_spec_act.left
          rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]
          apply Or.inr
          exists v; constructor
          . apply Rule.frontier_subset_vars_body; exact v_front
          . rfl
        | inr v_front =>
          have v_exis : v ∈ trg.val.rule.existential_vars_for_head_disjunct head_index_for_m_subs.val head_index_for_m_subs.isLt := by
            simp only [Rule.existential_vars_for_head_disjunct, List.mem_filter, decide_eq_true_eq]; constructor
            . rw [FunctionFreeConjunction.mem_vars];
              exists (trg.val.atom_for_result_fact result_index_for_trg f_mem); constructor
              . apply PreTrigger.atom_for_result_fact_mem_head
              . exact voc_mem
            . exact v_front
          have func_term_fresh : trg.val.functional_term_for_var result_index_for_trg.val v ∈ trg.val.fresh_terms_for_head_disjunct head_index_for_m_subs.val head_index_for_m_subs.isLt := by apply List.mem_map_of_mem; exact v_exis
          rw [PreTrigger.apply_to_var_or_const_non_frontier_var _ _ _ v_front]
          simp only [next_hom]
          suffices ¬ trg.val.functional_term_for_var result_index_for_trg.val v ∈ (CN.outgoingFacts node.node).terms by
            simp only [this, ↓reduceIte]
            simp only [func_term_fresh, ↓reduceDIte]
            rw [PreTrigger.existential_var_for_fresh_term_after_functional_term_for_var]
            exact v_exis
          intro contra
          apply trg_inactive_of_fresh_term_present _ _ _ _ func_term_fresh contra
          exact trg_spec_act
  ⟩

/-- The node that we pick in `hom_step_of_trg_ex` is in the childNodes of the previous node. This is trivial. -/
theorem mem_childNodes_of_mem_hom_step_of_trg_ex
    {N : Type u} [CN : ChaseNode N obs kb.rules] {out_sub_in : CN.out_sub_in}
    {ct : ChaseTree N obs kb}
    {m : FactSet sig}
    {m_is_model : m.modelsKb kb}
    {node : ct.NodeWithAddress}
    {prev_hom : GroundTermMapping sig}
    {prev_hom_is_homomorphism : prev_hom.isHomomorphism (CN.outgoingFacts node.node) m}
    {children_ne_nil : node.subderivation.childNodes ≠ []}
    {trg_inactive_of_fresh_term_present : ∀ (trg : RTrigger obs kb.rules) i lt t, t ∈ trg.val.fresh_terms_for_head_disjunct i lt -> t ∈ (CN.outgoingFacts node.node).terms -> ¬ trg.val.active (CN.outgoingFacts node.node)} :
    (hom_step_of_trg_ex out_sub_in ct m m_is_model node prev_hom prev_hom_is_homomorphism children_ne_nil trg_inactive_of_fresh_term_present).val.fst ∈ node.childNodes := by
  simp only [hom_step_of_trg_ex]; exact List.getElem_mem _

/-- The homomorphisms that we construct in `hom_step_of_trg_ex` agrees with the previous one on all terms in the previous node. This is also trivial. -/
theorem hom_extends_prev_in_hom_step_of_trg_ex
    {N : Type u} [CN : ChaseNode N obs kb.rules] {out_sub_in : CN.out_sub_in}
    {ct : ChaseTree N obs kb}
    {m : FactSet sig}
    {m_is_model : m.modelsKb kb}
    {node : ct.NodeWithAddress}
    {prev_hom : GroundTermMapping sig}
    {prev_hom_is_homomorphism : prev_hom.isHomomorphism (CN.outgoingFacts node.node) m}
    {children_ne_nil : node.subderivation.childNodes ≠ []}
    {trg_inactive_of_fresh_term_present : ∀ (trg : RTrigger obs kb.rules) i lt t, t ∈ trg.val.fresh_terms_for_head_disjunct i lt -> t ∈ (CN.outgoingFacts node.node).terms -> ¬ trg.val.active (CN.outgoingFacts node.node)} :
    ∀ t ∈ (CN.outgoingFacts node.node).terms, prev_hom t = (hom_step_of_trg_ex out_sub_in ct m m_is_model node prev_hom prev_hom_is_homomorphism children_ne_nil trg_inactive_of_fresh_term_present).val.snd t := by intro t t_mem; simp [hom_step_of_trg_ex, t_mem]

/-- When extending the `InductiveHomomorphismResult` from one step to the next, we do not necessarily know that a trigger is active for the current node. Indeed the chase might just have already finished. So we do a simple case distinction here and return an `Option` either with the result from `hom_step_of_trg_ex` or simply none. -/
noncomputable def hom_step
    {N : Type u} [CN : ChaseNode N obs kb.rules] (out_sub_in : CN.out_sub_in)
    (ct : ChaseTree N obs kb)
    (m : FactSet sig)
    (m_is_model : m.modelsKb kb)
    (trg_inactive_of_fresh_term_present : ∀ (node : ct.NodeWithAddress) (trg : RTrigger obs kb.rules) i lt t, t ∈ trg.val.fresh_terms_for_head_disjunct i lt -> t ∈ (CN.outgoingFacts node.node).terms -> ¬ trg.val.active (CN.outgoingFacts node.node))
    (prev_res : InductiveHomomorphismResult ct m) :
    Option (InductiveHomomorphismResult ct m) :=
  if eq_nil : prev_res.val.fst.subderivation.childNodes = []
  then none
  else some (hom_step_of_trg_ex out_sub_in ct m m_is_model prev_res.val.fst prev_res.val.snd prev_res.property eq_nil (trg_inactive_of_fresh_term_present _))

/-- If there is a new node returned by `hom_step`, then it is in the `childNodes` of the current node. -/
theorem mem_childNodes_of_mem_hom_step
    {N : Type u} [CN : ChaseNode N obs kb.rules] {out_sub_in : CN.out_sub_in}
    {ct : ChaseTree N obs kb}
    {m : FactSet sig}
    {m_is_model : m.modelsKb kb}
    {trg_inactive_of_fresh_term_present : ∀ (node : ct.NodeWithAddress) (trg : RTrigger obs kb.rules) i lt t, t ∈ trg.val.fresh_terms_for_head_disjunct i lt -> t ∈ (CN.outgoingFacts node.node).terms -> ¬ trg.val.active (CN.outgoingFacts node.node)}
    {prev_res : InductiveHomomorphismResult ct m} :
    ∀ res ∈ hom_step out_sub_in ct m m_is_model trg_inactive_of_fresh_term_present prev_res, res.val.fst ∈ prev_res.val.fst.childNodes := by
  intro res
  simp only [hom_step]
  grind [mem_childNodes_of_mem_hom_step_of_trg_ex]

/-- If `hom_step` returns none, then the current node does not have any children. -/
theorem childNodes_empty_of_hom_step_none
    {N : Type u} [CN : ChaseNode N obs kb.rules] {out_sub_in : CN.out_sub_in}
    {ct : ChaseTree N obs kb}
    {m : FactSet sig}
    {m_is_model : m.modelsKb kb}
    {trg_inactive_of_fresh_term_present : ∀ (node : ct.NodeWithAddress) (trg : RTrigger obs kb.rules) i lt t, t ∈ trg.val.fresh_terms_for_head_disjunct i lt -> t ∈ (CN.outgoingFacts node.node).terms -> ¬ trg.val.active (CN.outgoingFacts node.node)}
    {prev_res : InductiveHomomorphismResult ct m} :
    hom_step out_sub_in ct m m_is_model trg_inactive_of_fresh_term_present prev_res = none -> prev_res.val.fst.childNodes = [] := by
  simp only [hom_step]
  split
  case isTrue h => intro _; rw [TreeDerivation.NodeWithAddress.childNodes_eq_childNodes, List.map_eq_nil_iff] at h; exact h
  . simp

/-- The homomorphism returns in `hom_step` agrees with the current one on all terms from the current node. -/
theorem hom_extends_prev_in_hom_step
    {N : Type u} [CN : ChaseNode N obs kb.rules] {out_sub_in : CN.out_sub_in}
    {ct : ChaseTree N obs kb}
    {m : FactSet sig}
    {m_is_model : m.modelsKb kb}
    {trg_inactive_of_fresh_term_present : ∀ (node : ct.NodeWithAddress) (trg : RTrigger obs kb.rules) i lt t, t ∈ trg.val.fresh_terms_for_head_disjunct i lt -> t ∈ (CN.outgoingFacts node.node).terms -> ¬ trg.val.active (CN.outgoingFacts node.node)}
    {prev_res : InductiveHomomorphismResult ct m} :
    ∀ pair ∈ hom_step out_sub_in ct m m_is_model trg_inactive_of_fresh_term_present prev_res,
      ∀ t ∈ (CN.outgoingFacts prev_res.val.fst.node).terms, prev_res.val.snd t = pair.val.snd t := by
  intro res
  simp only [hom_step]
  grind [hom_extends_prev_in_hom_step_of_trg_ex]

/-- As outlined at the very top of this file, we now use `TreeDerivation.generate_subderivation` with the `hom_step` generator to obtain the branch in the tree that yields the result `FactSet` for which the combined `GroundTermMapping`s form a homomorphism into the target model. -/
public theorem chaseTreeResultIsUniversal (ct : RegularChaseTree obs kb) : ∀ (m : FactSet sig), m.modelsKb kb ->
    ∃ (fs : FactSet sig) (h : GroundTermMapping sig), fs ∈ ct.result ∧ h.isHomomorphism fs m := by
  have trg_inactive_of_fresh_term_present : ∀ (node : ct.NodeWithAddress) (trg : RTrigger obs kb.rules) i lt t, t ∈ trg.val.fresh_terms_for_head_disjunct i lt -> t ∈ (RegularChaseNode.regularChaseNodeInstance.outgoingFacts node.node).terms -> ¬ trg.val.active (RegularChaseNode.regularChaseNodeInstance.outgoingFacts node.node) := by
    intro node trg i lt t t_fresh t_mem_node trg_act
    apply trg_act.right
    apply obs.contains_trg_result_implies_cond ⟨i, by simpa using lt⟩
    exact RegularChaseTree.result_of_trigger_introducing_functional_term_occurs_in_chase node t_mem_node t_fresh

  intro m m_is_model

  let start : InductiveHomomorphismResult ct m := ⟨(TreeDerivation.NodeWithAddress.root ct.toTreeDerivation, id), by
    simp only [TreeDerivation.NodeWithAddress.root]; rw [ct.database_first'.right.left]
    constructor
    . unfold GroundTermMapping.isIdOnConstants; simp
    . intro e
      rw [GroundTermMapping.mem_applyFactSet]
      intro ⟨f, hf⟩
      apply m_is_model.left
      have : f = e := by have hfr := hf.right; rw [hfr]; simp [TermMapping.apply_generalized_atom]
      rw [this] at hf
      exact hf.left⟩

  let derivs_with_homs : PossiblyInfiniteList (RegularChaseDerivation obs kb.rules × GroundTermMapping sig) :=
    PossiblyInfiniteList.generate start (hom_step RegularChaseNode.out_sub_in ct m m_is_model trg_inactive_of_fresh_term_present) (fun res =>
      let deriv : RegularChaseDerivation obs kb.rules := ct.generate_subderivation res (hom_step RegularChaseNode.out_sub_in ct m m_is_model trg_inactive_of_fresh_term_present)
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
    simp only [derivs_with_homs, PossiblyInfiniteList.mem_iff, PossiblyInfiniteList.get?_generate, Option.map_eq_some_iff] at step_mem
    rw [← RegularChaseNode.outgoingFacts_eq]
    grind

  let deriv := (derivs_with_homs.head.get (by simp [derivs_with_homs, PossiblyInfiniteList.head_generate])).fst
  have deriv_mem : deriv ∈ ct.branches := by
    simp only [deriv, derivs_with_homs, PossiblyInfiniteList.head_generate, Option.map_some, Option.get_some]
    apply ct.generate_subderivation_mem_branches
    rfl

  let branch := ct.chaseBranch_for_branch deriv_mem

  have deriv_eq : deriv.branch = derivs_with_homs.map (fun step => step.fst.head) := by
    let pairs : PossiblyInfiniteList (InductiveHomomorphismResult ct m) :=
      PossiblyInfiniteList.generate start (hom_step RegularChaseNode.out_sub_in ct m m_is_model trg_inactive_of_fresh_term_present) id
    have pairs_eq : pairs.map (fun res => res.val.fst.node) = derivs_with_homs.map (fun step => step.fst.head) := by
      simp only [pairs, derivs_with_homs]
      apply PossiblyInfiniteList.ext; intro n
      simp only [PossiblyInfiniteList.get?_map, PossiblyInfiniteList.get?_generate, Option.map_map]
      apply Option.map_congr
      simp
    rw [← pairs_eq]
    apply PossiblyInfiniteList.ext; intro n
    rw [PossiblyInfiniteList.get?_map]
    simp only [pairs, deriv, derivs_with_homs]
    simp only [PossiblyInfiniteList.head_generate, Option.map_some, Option.get_some]
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
        simp
      let node2 : deriv.Node := ⟨pair.val.fst.node, by exists (n + m)⟩
      have prec : node1 ≼ node2 := by
        exists deriv.derivation_for_branch_suffix _ (deriv.branch.IsSuffix_drop n) (by rw [PossiblyInfiniteList.head_drop, step_mem_deriv]; simp)
        simp only [ChaseDerivationSkeleton.derivation_for_branch_suffix]
        constructor
        . exact deriv.branch.IsSuffix_drop n
        constructor
        . simp [ChaseDerivationSkeleton.head, step_mem_deriv, node1]
        . rw [ChaseDerivationSkeleton.mem_iff]; exists m; simp [pair_mem_deriv, node2]
      exact RegularChaseDerivationSkeleton.facts_node_subset_of_prec prec

  let global_h : GroundTermMapping sig := fun t =>
    let t_mem := ∃ step ∈ derivs_with_homs, t ∈ step.fst.head.facts.terms
    have t_mem_dec := Classical.propDecidable t_mem
    if t_mem_true : t_mem
    then (Classical.choose t_mem_true).snd t
    else t

  have global_h_eq_each_hom : ∀ step ∈ derivs_with_homs, ∀ f ∈ step.fst.head.facts, global_h.applyFact f = step.snd.applyFact f := by
    intro step step_mem f f_mem
    apply TermMapping.apply_generalized_atom_congr_left
    intro t t_mem
    simp only [global_h]
    split
    case isFalse not_mem =>
      apply False.elim
      apply not_mem
      exists step; simp only [step_mem, true_and]
      exists f
    case isTrue t_mem_true =>
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
    intro f'
    rw [GroundTermMapping.mem_applyFactSet]
    intro ⟨f, f_mem, f'_eq⟩
    rw [← node_mem] at f_mem
    rw [f'_eq, global_h_eq_each_hom step step_mem f f_mem]
    apply (derivs_with_homs_properties _ step_mem).right
    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
    exact f_mem

  exists RegularChaseBranch.result branch, global_h; constructor
  . unfold RegularChaseBranch.result RegularChaseTree.result RegularTreeDerivation.result; rw [Set.mem_map]; exists deriv
  constructor
  . intro c
    simp only [global_h]
    split
    case isFalse _ => rfl
    case isTrue t_mem_true =>
      have ⟨step_mem, _⟩ := Classical.choose_spec t_mem_true
      apply (derivs_with_homs_properties _ step_mem).left
  . intro f'
    rw [GroundTermMapping.mem_applyFactSet]
    intro ⟨f, ⟨node, node_mem, f_mem⟩, f'_eq⟩
    rw [f'_eq]
    apply global_h_hom node node_mem
    apply TermMapping.apply_generalized_atom_mem_apply_generalized_atom_set
    exact f_mem

