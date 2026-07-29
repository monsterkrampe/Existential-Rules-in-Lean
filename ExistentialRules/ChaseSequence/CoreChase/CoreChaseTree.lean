/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.ChaseSequence.ChaseTree
public import ExistentialRules.ChaseSequence.Termination.Basic

import ExistentialRules.ChaseSequence.CoreChase.Basic
public import ExistentialRules.ChaseSequence.CoreChase.CoreChaseNode
public import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch

/-!
# Core Chase Trees

Next to the `CoreChaseBranch` definition, we also define a tree version in line with what is done for our generic and regular chase structures.
-/

public section

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]


abbrev CoreTreeDerivation (rules : RuleSet sig) := TreeDerivation (CoreChaseNode rules) (RestrictedObsolescence sig) rules

namespace CoreTreeDerivation

variable {rules : RuleSet sig}

section FinitenessOfFactSets

/-!
## Finiteness of FactSets in the Core Chase

If we start a `CoreTreeDerivation` on a finite fact set, all other fact sets (and cores) also remain finite.
For regular chase derivations, we only show this for `ChaseBranch`es that start on a database. However, here we also require such a result on auxiliary results that we show for the `CoreTreeDerivation`.
-/

/-- If the initial facts are finite, then the facts of every node are finite. -/
theorem facts_finite_of_mem_of_root_finite {td : CoreTreeDerivation rules} (root_fin : td.root.facts.finite) (node : td.NodeWithAddress) : node.node.facts.finite := by
  induction node using TreeDerivation.mem_rec_address with
  | root => exact root_fin
  | step new_root ih c c_mem =>
    rw [← c.node.ingoingFacts_eq, new_root.subderivation.facts_childNodes (new_root.mem_childNodes_of_mem_childNodes c_mem), new_root.root_subderivation', new_root.node.outgoingFacts_eq]
    apply Set.union_finite_of_both_finite (Set.finite_of_subset_finite ih new_root.node.homSubset.left)
    apply List.finite_toSet

/-- If the initial core is finite, then the cores of every node are finite. -/
theorem core_finite_of_mem_of_root_finite {td : CoreTreeDerivation rules} (root_fin : td.root.core.finite) (node : td.NodeWithAddress) : node.node.core.finite := by
  cases node.eq_root_or_mem_child with
  | inl node_mem => rw [node_mem]; exact root_fin
  | inr node_mem =>
    rcases node_mem with ⟨c, c_mem, node', node_eq⟩
    have inner_eq : node.node = node'.node := by rw [← node_eq]; simp [TreeDerivation.NodeWithAddress.cast_for_new_root_node]
    rw [inner_eq]
    apply Set.finite_of_subset_finite (facts_finite_of_mem_of_root_finite (td := c.subderivation) _ node') node'.node.homSubset.left
    rw [c.root_subderivation',← c.node.ingoingFacts_eq]
    rw [td.facts_childNodes (by
      have := TreeDerivation.NodeWithAddress.mem_childNodes_of_mem_childNodes c_mem
      rw [TreeDerivation.NodeWithAddress.subderivation_root] at this
      exact this)]
    rw [td.root.outgoingFacts_eq]
    apply Set.union_finite_of_both_finite root_fin
    apply List.finite_toSet

end FinitenessOfFactSets

section HomomorphismsAlongChase

/-!
## Homomorphisms along the Chase

In the regular `TreeDerivation`, each steps can only add facts, which makes consecutive nodes subsets of each other.
This is not true for the core chase. But at least, we can always find a homomorphism into the following fact sets. (This trivially holds for the regular tree derivation as well since with the subset relation the id mapping always forms such a homomorphism.)
-/

/-- For each derivation, there is a homomorphism from its root into every node. -/
theorem exists_homomorphism_from_root_of_mem {td : CoreTreeDerivation rules} :
    ∀ node ∈ td, ∃ h : GroundTermMapping sig, h.isHomomorphism td.root.core node.core := by
  simp only [td.mem_iff]
  intro node ⟨addr, node_mem⟩
  let node' : td.NodeWithAddress := { node := node, address := addr, eq := node_mem }
  show ∃ h : GroundTermMapping sig, h.isHomomorphism td.root.core node'.node.core
  induction node' using td.mem_rec_address with
  | root => exact ⟨id, GroundTermMapping.isHomomorphism_id_of_subset Set.subset_refl⟩
  | step new_root ih c c_mem =>
    rcases ih with ⟨h_ih, h_ih_hom⟩
    rcases c.node.homSubset.right with ⟨h_c, h_c_hom⟩
    have id_hom_to_c : GroundTermMapping.isHomomorphism id new_root.node.core c.node.facts := by
      apply GroundTermMapping.isHomomorphism_id_of_subset
      rw [← c.node.ingoingFacts_eq, new_root.subderivation.facts_childNodes (new_root.mem_childNodes_of_mem_childNodes c_mem), new_root.root_subderivation', new_root.node.outgoingFacts_eq]
      exact Set.subset_union_of_subset_left Set.subset_refl
    exists h_c ∘ id ∘ h_ih
    apply GroundTermMapping.isHomomorphism_compose
    apply GroundTermMapping.isHomomorphism_compose
    . exact h_ih_hom
    . exact id_hom_to_c
    . exact h_c_hom

/-- The root's core cannot occur again in the child trees. If this was the case and since we always find homomorphism from to successor cores, we can argue that then the triggers would have already been satisfied. The same theorem exists for regular `TreeDerivation`s but the argument is easier for them. -/
theorem root_core_not_mem_childTrees_of_finite {td : CoreTreeDerivation rules} (root_finite : td.root.core.finite) :
    ∀ c ∈ td.childTrees, ∀ node ∈ c, td.root.core ≠ node.core := by
  intro c c_mem node node_mem contra
  have c_root_child : c.root ∈ td.childNodes := by rw [td.childNodes_eq]; apply List.mem_map_of_mem; exact c_mem
  let origin := c.root.origin.get (td.isSome_origin_of_mem_childNodes _ c_root_child)
  apply c.root.origin_trg_inactive_of_isWeakCore_of_homSubset_of_finite td.root.isWeakCore _ root_finite origin (by simp [origin])
  . exact td.active_trigger_origin_of_mem_childNodes c_root_child
  . constructor
    . rw [← c.root.ingoingFacts_eq, td.facts_childNodes c_root_child, td.root.outgoingFacts_eq]
      exact Set.subset_union_of_subset_left Set.subset_refl
    . -- there exists a homomorphism from c.root to (the second occurrence of) td.root
      rcases exists_homomorphism_from_root_of_mem _ node_mem with ⟨h, hom⟩
      -- we also have a homomorphism from c.root.facts to c.root.core by definition
      rcases c.root.homSubset.right with ⟨h_core, h_core_hom⟩
      -- we can compose both homomorphisms into a homomorphism from c.root.facts to td.root.core
      let h_facts_root : GroundTermMapping sig := h ∘ h_core
      have h_facts_root_hom : h_facts_root.isHomomorphism c.root.facts td.root.core := by
        apply GroundTermMapping.isHomomorphism_compose; exact h_core_hom; rw [contra]; exact hom
      exists h_facts_root

/-- The `root` cannot occur in the `childTree`s. Otherwise, the same fact set would occur twice in the chase. But since we always find homomorphism from to successor fact sets, we can argue that then the triggers would have already been satisfied. The same theorem exists for regular `TreeDerivation`s but the argument is easier for them. -/
theorem root_not_mem_childTrees_of_finite {td : CoreTreeDerivation rules} (root_finite : td.root.core.finite) : ¬ ∃ t ∈ td.childTrees, td.root ∈ t := by
  intro ⟨c, c_mem, root_mem⟩
  exact td.root_core_not_mem_childTrees_of_finite root_finite c c_mem _ root_mem rfl

/-- By `root_not_mem_childTrees_of_finite`, if we have a subtree but our root occurs in the subtree, then our subtree is equal to us. -/
@[grind ->]
theorem eq_of_suffix_of_root_mem_of_finite {td1 td2 : CoreTreeDerivation rules}
    (suffix : td1 <:+ td2) (root_mem : td2.root ∈ td1) (root_finite : td2.root.core.finite) : td1 = td2 := by
  rw [td1.suffix_iff_eq_or_suffix_childTree] at suffix
  cases suffix with
  | inl suffix => exact suffix
  | inr suffix => rcases suffix with ⟨td3, td3_mem, suffix⟩; apply False.elim; apply td2.root_not_mem_childTrees_of_finite root_finite; exists td3; grind

end HomomorphismsAlongChase

section Predecessors

/-!
## Predecessor Relation

We port the predecessor results from the `TreeDerivation` that are there only shown for derivations with `RegularChaseNode`s.

We also add a few results on top that are specific to the core chase such as `exists_homomorphism_of_prec` or `core_not_subset_of_strict_predecessor` (where the latter is a variant of `RegularTreeDerivation.facts_not_subset_of_strict_predecessor`.
-/

/-- For each node, there exists a homomorphism to each of its successors. -/
theorem exists_homomorphism_of_prec {td : CoreTreeDerivation rules} {n1 n2 : td.NodeWithAddress} :
    n1 ≼ n2 -> ∃ h : GroundTermMapping sig, h.isHomomorphism n1.node.core n2.node.core := by
  intro ⟨diff, addr_eq⟩
  have := exists_homomorphism_from_root_of_mem (td := n1.subderivation) n2.node
  rw [TreeDerivation.NodeWithAddress.root_subderivation'] at this
  apply this
  rw [TreeDerivation.mem_iff]
  exists diff
  rw [← n2.eq, ← addr_eq]
  simp [TreeDerivation.NodeWithAddress.subderivation, TreeDerivation.derivation_for_suffix]


section StrictPredecessor

/-- The node is a strict predecessor of each of its `childNodes`. -/
theorem node_strict_prec_childNodes_of_finite {td : CoreTreeDerivation rules} (root_fin : td.root.core.finite) {node : td.NodeWithAddress} :
    ∀ c ∈ node.childNodes, node ≺ c := by
  intro c c_mem
  constructor
  . exact td.node_prec_childNodes c c_mem
  . intro contra
    rw [← contra] at c_mem
    have node_fin : node.node.core.finite := by
      apply td.core_finite_of_mem_of_root_finite
      exact root_fin
    apply root_not_mem_childTrees_of_finite (td := node.subderivation) (by rw [node.root_subderivation']; exact node_fin)
    exists node.subderivation; constructor
    . exact node.subderivation_mem_childTrees_of_mem_childNodes c_mem
    . exact node.subderivation.root_mem

/-- The core of a strict successor cannot be a subset of our core. Otherwise, our current core would not be a core. -/
@[grind ->]
theorem core_not_subset_of_strict_predecessor_of_finite {td : CoreTreeDerivation rules} {n1 n2 : td.NodeWithAddress} (n1_fin : n1.node.core.finite) :
    n1 ≺ n2 -> ¬ n2.node.core ⊆ n1.node.core := by
  intro prec contra
  have cores_eq : n2.node.core = n1.node.core := by
    apply FactSet.homSubset_eq_self_of_isWeakCore_of_finite _ n1.node.isWeakCore n1_fin
    exact ⟨contra, exists_homomorphism_of_prec prec.left⟩
  suffices ∃ c ∈ n1.childNodes, c ≼ n2 by
    rcases this with ⟨c, c_mem, c_prec⟩
    apply root_core_not_mem_childTrees_of_finite (td := n1.subderivation) (by rw [n1.root_subderivation']; exact n1_fin) _ (TreeDerivation.NodeWithAddress.subderivation_mem_childTrees_of_mem_childNodes c_mem) n2.node (td.mem_subderivation_of_prec c_prec)
    rw [cores_eq]; simp
  exists td.next_on_path_to_succ prec; constructor
  . exact td.next_on_path_to_succ_mem_childNodes prec
  . exact td.next_on_path_to_succ_is_prec prec

end StrictPredecessor

end Predecessors

section TermsInChase

/-!
## Terms in the Chase

We make some general observations about certain terms that might occur in the chase.

1. Constants can only originate directly from rules or from the initial fact set. No other constants can be introduced.
2. Functional terms can either also originate from the initial fact set or they are introduced as fresh terms by a trigger.

The second observation entails that the precense of a functional term that does not occur in the initial fact set implies
that the trigger that introduces this term must have been applied in some `ChaseNode`.
-/


/-- Constants in the chase can only come from the initial fact set or from a constant in a rule. -/
theorem constants_node_subset_constants_fs_union_constants_rules
    {td child : CoreTreeDerivation rules}
    (child_mem : child ∈ td.childTrees)
    {node : CoreChaseNode rules} (node_mem : node ∈ child) :
    node.facts.constants ⊆ td.root.core.constants ∪ rules.head_constants :=
  TreeDerivation.constants_node_subset_constants_fs_union_constants_rules CoreChaseNode.out_sub_in child_mem node_mem

/-- Each functional term in the chase originates as a fresh term from a trigger if it was not already part of the initial fact set. -/
theorem functional_term_originates_from_some_trigger
    {td child : CoreTreeDerivation rules}
    (child_mem : child ∈ td.childTrees)
    (node : child.NodeWithAddress)
    {t : GroundTerm sig}
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
    (t_mem : t ∈ node.node.facts.terms) :
    t ∈ td.root.core.terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.node.origin, t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) :=
  TreeDerivation.functional_term_originates_from_some_trigger CoreChaseNode.out_sub_in child_mem node t_is_func t_mem

/-- If a functional term occurs in the chase, then the trigger that introduces this term must have been used in the chase, unless the term already occurs in the initial fact set. -/
theorem trigger_introducing_functional_term_occurs_in_chase
    {td child : CoreTreeDerivation rules}
    (child_mem : child ∈ td.childTrees)
    (node : child.NodeWithAddress)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.node.facts.terms)
    {trg : RTrigger (RestrictedObsolescence sig) rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    t ∈ td.root.core.terms ∨ ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.node.origin, orig.fst.equiv trg ∧ orig.snd.val = disj_idx :=
  TreeDerivation.trigger_introducing_functional_term_occurs_in_chase CoreChaseNode.out_sub_in child_mem node t_mem_node t_mem_trg

end TermsInChase

section Result

/-!
## Core Chase Result

Oppossed to regular tree derivations, the result of a core tree derivation is only defined if the derivation terminates. Then it is simply the last element.
Just like for RegularTreeDerivations however, the result also models all rules.
-/

abbrev result (td : CoreTreeDerivation rules) (term : td.terminates) : Set (FactSet sig) :=
  -- We do not use `Set.map` since we currently do not have `Set.attach`. Maybe we should introduce this...
  fun fs => ∃ (deriv : CoreChaseDerivation rules) (mem : deriv ∈ td.branches), deriv.result (term _ mem) = fs

/--
Since the result is only defined for terminating trees, it must be finite
(which does not mean that each individual fact set is finite as well, this would only hold for proper `CoreChaseTree`s).
-/
theorem result_finite {td : CoreTreeDerivation rules} (term : td.terminates) : (td.result term).finite := by
  rcases td.branches_finite_of_terminates term with ⟨branches, _, eq⟩
  have : DecidableEq (FactSet sig) := Classical.typeDecidableEq (FactSet sig)
  apply Set.finite_of_list_with_same_elements
    (branches.attach.map (fun d => CoreChaseDerivation.result d.val (by apply term d.val; rw [← eq]; exact d.property)))
  intro fs; rw [List.mem_map]
  constructor
  . intro ⟨d, _, fs_eq⟩; exists d.val, (by rw [← eq]; exact d.property)
  . intro ⟨d, mem, fs_eq⟩; exists ⟨d, by rw [eq]; exact mem⟩; simpa

/-- Each element of the `result` models the rules. -/
theorem result_models_rules {td : CoreTreeDerivation rules} (term : td.terminates) : ∀ fs ∈ td.result term, fs.modelsRules rules := by
  intro fs ⟨d, d_mem, fs_eq⟩; rw [← fs_eq]; exact d.result_models_rules (term _ d_mem)

end Result

end CoreTreeDerivation


abbrev CoreChaseTree (kb : KnowledgeBase sig) := ChaseTree (CoreChaseNode kb.rules) (RestrictedObsolescence sig) kb

namespace CoreChaseTree

variable {kb : KnowledgeBase sig}

section FinitenessOfFactSets

/-!
## Finiteness of FactSets in the Core Chase

Just as in a regular `ChaseTree`, every fact set (and every core) that occurs in the `CoreChaseTree` is finite simply since the (initial) database is finite and since each step only adds finitely many facts.
-/

/- Each fact set in the chase is finite. -/
theorem facts_finite_of_mem {ct : CoreChaseTree kb} (node : ct.NodeWithAddress) : node.node.facts.finite := by
  apply CoreTreeDerivation.facts_finite_of_mem_of_root_finite
  rw [← ct.root.ingoingFacts_eq, ct.database_first'.left]; exact kb.db.toFactSet.property.left

/- Each core in the chase is finite. -/
theorem core_finite_of_mem {ct : CoreChaseTree kb} (node : ct.NodeWithAddress) : node.node.core.finite := by
  apply Set.finite_of_subset_finite (ct.facts_finite_of_mem node) node.node.homSubset.left

end FinitenessOfFactSets

section DatabaseContainment

/-!
## Database Containment

Even though we do not have fact set monotonicity in the core chase, it is still true that the database occurs in every fact set and core in the chase.
This is because the database only features constants and these can never be remapped by any homomorphism.
We also have a result here stating that every member of the `CoreChaseTree` result is a model.
-/

/-- The database is a subset of each node since the database only contains constants which can never be remapped by homomorphisms. -/
theorem db_mem_of_mem {ct : CoreChaseTree kb} : ∀ (node : ct.NodeWithAddress), kb.db.toFactSet.val ⊆ node.node.core := by
  intro node
  rcases CoreTreeDerivation.exists_homomorphism_from_root_of_mem _ node.mem with ⟨h, hom⟩
  intro f f_mem
  apply hom.right
  rw [← CoreChaseNode.outgoingFacts_eq, ct.database_first'.right.left]
  rw [GroundTermMapping.mem_applyFactSet]; exists f; constructor; exact f_mem
  apply Eq.symm; apply h.applyFact_eq_self_of_isIdOnConstants_of_isFunctionFree
  . exact hom.left
  . exact kb.db.toFactSet.property.right f f_mem

/-- Each result member of a `CoreChaseTree` models the whole `KnowledgeBase`. -/
theorem result_models_kb {ct : CoreChaseTree kb} (term : ct.terminates) : ∀ fs ∈ CoreTreeDerivation.result ct.toTreeDerivation term, fs.modelsKb kb := by
  intro fs ⟨branch, branch_mem, fs_mem⟩
  let cb := ct.chaseBranch_for_branch branch_mem
  have cb_mem : cb.toChaseDerivation ∈ ct.branches := by simpa [cb, ChaseTree.chaseBranch_for_branch] using branch_mem
  have : CoreChaseDerivation.result branch (term _ branch_mem) = CoreChaseDerivation.result cb.toChaseDerivation (term _ cb_mem) := by rfl
  simp only [← fs_mem, this]
  exact CoreChaseBranch.result_models_kb (term _ cb_mem)

end DatabaseContainment

section Predecessors

/-!
## Predecessor Relation

Compared to the `CoreChaseDerivation`, we can now drop the explicit finiteness conditions.
-/

section StrictPredecessor

/-- The node is a strict predecessor of each of its `childNodes`. -/
theorem node_strict_prec_childNodes {ct : CoreChaseTree kb} {node : ct.NodeWithAddress} :
    ∀ c ∈ node.childNodes, node ≺ c := by
  apply CoreTreeDerivation.node_strict_prec_childNodes_of_finite; exact core_finite_of_mem (TreeDerivation.NodeWithAddress.root ct.toTreeDerivation)

/-- The core of a strict successor cannot be a subset of our core. Otherwise, our current core would not be a core. -/
@[grind ->]
theorem core_not_subset_of_strict_predecessor {ct : CoreChaseTree kb} {n1 n2 : ct.NodeWithAddress} : n1 ≺ n2 -> ¬ n2.node.core ⊆ n1.node.core := by
  apply CoreTreeDerivation.core_not_subset_of_strict_predecessor_of_finite; apply core_finite_of_mem

end StrictPredecessor

end Predecessors

section TermsInChase

/-!
## Terms in the Chase

We make some general observations about certain terms that might occur in the chase.

1. Constants can only originate directly from rules or from the initial fact set. No other constants can be introduced.
2. Functional terms can either also originate from the initial fact set or they are introduced as fresh terms by a trigger.

The second observation entails that the precense of a functional term that does not occur in the initial fact set implies
that the trigger that introduces this term must have been applied in some `ChaseNode`.
-/

/-- Constants in the chase must be in the database or in some rule. -/
theorem constants_node_subset_constants_db_union_constants_rules
    {ct : CoreChaseTree kb}
    {node : CoreChaseNode kb.rules} (node_mem : node ∈ ct) :
    node.facts.constants ⊆ (kb.db.constants.val ∪ kb.rules.head_constants) := by
  cases ct.mem_iff_eq_root_or_mem_child.mp node_mem with
  | inl node_mem => apply Set.subset_union_of_subset_left; rw [node_mem, ← ct.root.ingoingFacts_eq, ct.database_first'.left, Database.toFactSet_constants_same]; exact Set.subset_refl
  | inr node_mem =>
    rcases node_mem with ⟨_, node_mem⟩
    rw [← Database.toFactSet_constants_same, ← ct.database_first'.right.left, ct.root.outgoingFacts_eq]
    exact CoreTreeDerivation.constants_node_subset_constants_fs_union_constants_rules node_mem.left node_mem.right

/-- Each functional term in the chase originates as a fresh term from a trigger. -/
theorem functional_term_originates_from_some_trigger
    {ct : CoreChaseTree kb}
    (node : ct.NodeWithAddress)
    {t : GroundTerm sig}
    (t_is_func : ∃ func ts arity_ok, t = GroundTerm.func func ts arity_ok)
    (t_mem : t ∈ node.node.facts.terms) :
    ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.node.origin,
      t ∈ orig.fst.val.fresh_terms_for_head_disjunct orig.snd.val (by rw [← PreTrigger.length_mapped_head]; exact orig.snd.isLt) := by
  have t_nmem_root : t ∉ ct.root.core.terms := by
    intro t_mem
    exact ct.func_term_not_mem_root t_is_func t_mem
  cases node.eq_root_or_mem_child with
  | inl node_mem =>
    simp only [TreeDerivation.NodeWithAddress.root] at node_mem
    rw [node_mem, ← ct.root.ingoingFacts_eq, ct.database_first'.left, ← ct.database_first'.right.left] at t_mem
    apply False.elim; apply t_nmem_root; exact t_mem
  | inr node_mem =>
    rcases node_mem with ⟨child, child_mem, node', node_eq⟩
    cases CoreTreeDerivation.functional_term_originates_from_some_trigger (by apply TreeDerivation.NodeWithAddress.subderivation_mem_childTrees_of_mem_childNodes; exact child_mem) node' t_is_func (by rw [← node_eq] at t_mem; exact t_mem)  with
    | inl t_mem => apply False.elim; rw [TreeDerivation.NodeWithAddress.subderivation_root] at t_mem; exact t_nmem_root t_mem
    | inr t_mem =>
      rcases t_mem with ⟨node2, prec, t_mem⟩
      exists child.cast_for_new_root_node node2; constructor
      . rw [← node_eq]; exact ct.predecessor_of_suffix prec
      . exact t_mem

/-- If a functional term occurs in the chase, then the trigger that introduces this term must have been used in the chase. -/
theorem trigger_introducing_functional_term_occurs_in_chase
    {ct : CoreChaseTree kb}
    (node : ct.NodeWithAddress)
    {t : GroundTerm sig}
    (t_mem_node : t ∈ node.node.facts.terms)
    {trg : RTrigger (RestrictedObsolescence sig) kb.rules}
    {disj_idx : Nat}
    {lt : disj_idx < trg.val.rule.head.length}
    (t_mem_trg : t ∈ trg.val.fresh_terms_for_head_disjunct disj_idx lt) :
    ∃ node2, node2 ≼ node ∧ ∃ orig ∈ node2.node.origin, orig.fst.equiv trg ∧ orig.snd.val = disj_idx := by
  have t_nmem_root : t ∉ ct.root.core.terms := by
    intro t_mem
    exact ct.func_term_not_mem_root (PreTrigger.term_functional_of_mem_fresh_terms _ t_mem_trg) t_mem
  cases node.eq_root_or_mem_child with
  | inl node_mem =>
    simp only [TreeDerivation.NodeWithAddress.root] at node_mem
    rw [node_mem, ← ct.root.ingoingFacts_eq, ct.database_first'.left, ← ct.database_first'.right.left] at t_mem_node
    apply False.elim; apply t_nmem_root; exact t_mem_node
  | inr node_mem =>
    rcases node_mem with ⟨child, child_mem, node', node_eq⟩
    cases CoreTreeDerivation.trigger_introducing_functional_term_occurs_in_chase (by apply TreeDerivation.NodeWithAddress.subderivation_mem_childTrees_of_mem_childNodes; exact child_mem) node' (by rw [← node_eq] at t_mem_node; exact t_mem_node) t_mem_trg with
    | inl t_mem => apply False.elim; rw [TreeDerivation.NodeWithAddress.subderivation_root] at t_mem; exact t_nmem_root t_mem
    | inr t_mem =>
      rcases t_mem with ⟨node2, prec, t_mem⟩
      exists child.cast_for_new_root_node node2; constructor
      . rw [← node_eq]; exact ct.predecessor_of_suffix prec
      . exact t_mem

end TermsInChase

section OriginTriggerRemainsInactive

/-!
## Used triggers remain inactive

Here we prove that triggers used in the core chase remain inactive from this point.
Not only that but also every equivalent trigger (producing the same result) is inactive from this point on.
For regular chase trees this is trivial because of fact monotonicity but here it is not quite obvious (even though it's intuitive).
-/

theorem origin_trg_remains_inactive {ct : CoreChaseTree kb} {n1 n2 : ct.NodeWithAddress} (prec : n1 ≼ n2) :
    ∀ orig ∈ n1.node.origin, ∀ trg, orig.fst.equiv trg -> ¬ trg.val.active n2.node.core := by
  -- We assume for a contradiction that trg is active on n2 (captured in contra).
  intro orig orig_mem trg equiv contra
  cases ct.eq_or_strict_of_predecessor prec with
  | inl eq =>
    -- We have shown the base case (n1 = n2) in a separate result on `CoreChaseNode`.
    apply n1.node.equiv_origin_trg_inactive_for_own_core_of_finite (ct.core_finite_of_mem n1) _ orig_mem _ equiv
    rw [eq]
    exact contra
  | inr prec =>
    -- We get the node that is just before n1 and show some of its essential properties.
    rcases ct.mem_childNodes_of_some_member_of_isSome_origin n1 (by simp only [ChaseNode.origin]; rw [orig_mem]; simp) with ⟨just_before_n1, n1_child⟩
    have just_before_n1_prec : just_before_n1 ≺ n1 := ct.node_strict_prec_childNodes _ n1_child
    have orig_active_just_before_n1 : orig.fst.val.active just_before_n1.node.core := by
      have active := just_before_n1.subderivation.active_trigger_origin_of_mem_childNodes (just_before_n1.mem_childNodes_of_mem_childNodes n1_child)
      rw [Option.mem_def] at orig_mem
      simp only [ChaseNode.origin, orig_mem, Option.get_some] at active
      rw [just_before_n1.root_subderivation'] at active
      apply active
    -- We also get the node that is just before n2 and show some of its essential properties.
    rcases ct.mem_childNodes_of_some_node_of_strict_prec prec with ⟨just_before_n2, just_before_n2_succ, n2_child⟩
    -- The following is used in the proof but also required to prove termination of the recursive theorem.
    have just_before_n2_prec : just_before_n2 ≺ n2 := ct.node_strict_prec_childNodes _ n2_child
    -- From a recursive call to the theorem, we get that no equivalent trigger can be active on just_before_n2.
    have no_trg_active_head_cd2 : ∀ trg, orig.fst.equiv trg -> ¬ trg.val.active just_before_n2.node.core := origin_trg_remains_inactive just_before_n2_succ _ orig_mem
    -- If however there is an equivalent trigger loaded just_before_n2, then we can quickly conclude the proof
    -- by showing that this trigger would then in fact be active on just_before_n2, which is a contradiction.
    -- Or rather: if it was not active, then we can show that trg is obsolete on n2,
    -- but this contradicts our assumption made in the beginning.
    cases Classical.em (∃ trg, orig.fst.equiv trg ∧ trg.val.loaded just_before_n2.node.core) with
    | inl ex_loaded_trg =>
      rcases ex_loaded_trg with ⟨loaded_trg, loaded_trg_equiv, loaded_trg_loaded⟩
      apply no_trg_active_head_cd2 loaded_trg loaded_trg_equiv
      constructor; exact loaded_trg_loaded; intro loaded_trg_obs
      apply contra.right
      apply equiv_trg_obsolete_of_isWeakCore_of_homSubset_of_finite n2.node.isWeakCore n2.node.homSubset (ct.core_finite_of_mem n2) _ _ _ (PreTrigger.equiv_trans (PreTrigger.equiv_symm loaded_trg_equiv) equiv) contra.left
      apply PreTrigger.satisfied_of_satisfied_subset _ loaded_trg_obs
      rw [← n2.node.ingoingFacts_eq, just_before_n2.subderivation.facts_childNodes (just_before_n2.mem_childNodes_of_mem_childNodes n2_child)]
      apply Set.subset_union_of_subset_left
      rw [just_before_n2.root_subderivation', just_before_n2.node.outgoingFacts_eq]
      exact Set.subset_refl
    | inr ex_loaded_trg =>
      -- If no equivalent trigger is loaded just_before_n2, things get more complicated...
      -- First, we obtain the first node after n1, where no equivalent trigger is loaded; call that n3.
      let target_prop (node : ct.NodeWithAddress) : Prop :=
        n1 ≼ node ∧ ¬ ∃ trg, orig.fst.equiv trg ∧ trg.val.loaded node.node.core
      rcases ct.prop_for_node_has_minimal_such_node target_prop just_before_n2 ⟨just_before_n2_succ, ex_loaded_trg⟩ with ⟨n3, ⟨n3_prec, none_loaded_n3⟩, n3_prec_just_before_n2, n3_minimal⟩
      -- Now let's assume for a second that we can find a frontier term that is not part of n3's core.
      suffices ∃ v ∈ trg.val.rule.frontier, trg.val.subs v ∉ n3.node.core.terms by
        -- We know a couple things about such a term:
        -- 1. it must occur in just_before_n1 and n2 because the equivalent triggers are loaded there, and
        -- 2. it must be a functional term since constants can never be removed.
        rcases this with ⟨v, v_mem, t_nmem⟩
        have t_mem_core_cd_where_n1_next : trg.val.subs v ∈ just_before_n1.node.core.terms := by
          apply FactSet.terms_subset_of_subset orig_active_just_before_n1.left
          rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]; apply Or.inr
          exists v; constructor
          . apply Rule.frontier_subset_vars_body; rw [equiv.left]; exact v_mem
          . apply equiv.right; rw [equiv.left]; exact v_mem
        have t_mem_facts_cd_where_n1_next : trg.val.subs v ∈ just_before_n1.node.facts.terms := by
          apply FactSet.terms_subset_of_subset just_before_n1.node.homSubset.left
          exact t_mem_core_cd_where_n1_next
        have t_mem_facts_n2 : trg.val.subs v ∈ n2.node.facts.terms := by
          apply FactSet.terms_subset_of_subset (Set.subset_trans contra.left n2.node.homSubset.left)
          rw [FactSet.mem_terms_toSet, PreTrigger.mem_terms_mapped_body_iff]; apply Or.inr
          exists v; constructor
          . apply Rule.frontier_subset_vars_body; exact v_mem
          . rfl
        have t_func : ∃ func ts arity_ok, trg.val.subs v = .func func ts arity_ok := by
          cases eq : trg.val.subs v with
          | func func ts arity_ok => exists func, ts, arity_ok
          | const c =>
            exfalso
            apply t_nmem
            rcases CoreTreeDerivation.exists_homomorphism_of_prec (ct.predecessor_trans just_before_n1_prec.left n3_prec) with ⟨h, hom⟩
            suffices h (trg.val.subs v) ∈ n3.node.core.terms by
              rw [eq]; rw [eq, hom.left] at this; exact this
            apply FactSet.terms_subset_of_subset hom.right
            rw [h.terms_applyFactSet]
            apply Set.mem_map_of_mem
            exact t_mem_core_cd_where_n1_next
        -- We also know that n3 strictly occurs before n2 (because it occurs before just_before_n2).
        -- The argument is a bit more elaborate then one might think.
        have n3_prec_n2 : n3 ≺ n2 := ct.strict_prec_of_prec_of_strict_prec n3_prec_just_before_n2 just_before_n2_prec
        -- Since the frontier term in question occurs in just_before_n1,
        -- it must have been introduced by a trigger before.
        rcases ct.functional_term_originates_from_some_trigger just_before_n1 t_func t_mem_facts_cd_where_n1_next with ⟨t_orig_node_before_n1, t_orig_node_before_n1_prec, t_orig_before_n1, t_orig_before_n1_mem, t_mem_orig_before_n1⟩

        rcases ct.predecessor_iff.mp (ct.next_on_path_to_succ_is_prec n3_prec_n2) with ⟨n2', n2_eq⟩

        cases CoreTreeDerivation.trigger_introducing_functional_term_occurs_in_chase (td := n3.subderivation)
          (n3.subderivation_mem_childTrees_of_mem_childNodes (ct.next_on_path_to_succ_mem_childNodes n3_prec_n2))
          n2'
          (by rw [← n2_eq] at t_mem_facts_n2; exact t_mem_facts_n2)
          t_mem_orig_before_n1 with
        | inl contra => apply t_nmem; rw [n3.root_subderivation'] at contra; exact contra
        | inr trg_occurs_again =>
          -- Now for the rest of this subproof we just apply our theorem recursively to conclude
          -- the proof as we now found two nodes where a trigger is applied twice (up to equivalence).
          -- The recursive call is fine since the first occurrence is before n1, so the first node is decreasing.
          rcases trg_occurs_again with ⟨t_orig_node_after_n3, t_orig_node_after_n3_prec, t_orig_after_n3, t_orig_after_n3_mem, t_orig_trgs_equiv, t_mem_orig_after_n3⟩

          have t_orig_node_after_n3_succ : n3 ≺ TreeDerivation.NodeWithAddress.cast_for_new_root_node _ t_orig_node_after_n3 := by
            apply ct.strict_prec_of_strict_prec_of_prec (ct.node_strict_prec_childNodes _ (ct.next_on_path_to_succ_mem_childNodes n3_prec_n2))
            apply List.prefix_append
          rcases ct.mem_childNodes_of_some_node_of_strict_prec t_orig_node_after_n3_succ with ⟨just_before_t_orig_node, just_before_t_orig_node_succ, t_orig_node_child⟩
          have t_orig_nodes_prec : t_orig_node_before_n1 ≼ just_before_t_orig_node := by
            apply ct.predecessor_trans t_orig_node_before_n1_prec
            apply ct.predecessor_trans just_before_n1_prec.left
            apply ct.predecessor_trans n3_prec
            exact just_before_t_orig_node_succ
          have _term : t_orig_node_before_n1 ≺ n1 := by
            exact ct.strict_prec_of_prec_of_strict_prec t_orig_node_before_n1_prec just_before_n1_prec
          apply origin_trg_remains_inactive t_orig_nodes_prec _ t_orig_before_n1_mem _ (PreTrigger.equiv_symm t_orig_trgs_equiv)
          suffices t_orig_after_n3 = t_orig_node_after_n3.node.origin.get (just_before_t_orig_node.subderivation.isSome_origin_of_mem_childNodes _ (just_before_t_orig_node.mem_childNodes_of_mem_childNodes t_orig_node_child)) by
            rw [this];
            have active := just_before_t_orig_node.subderivation.active_trigger_origin_of_mem_childNodes (just_before_t_orig_node.mem_childNodes_of_mem_childNodes t_orig_node_child)
            rw [just_before_t_orig_node.root_subderivation'] at active
            exact active
          rw [Option.mem_def] at t_orig_after_n3_mem
          simp [t_orig_after_n3_mem]

      -- It remains to be shown now that indeed some frontier term cannot be part of n3's core.
      -- First, we prove that on n3's facts, some equivalent trigger is still loaded
      -- (meaning that all frontier terms must still be there).
      -- This means that n3 is the exact node where the frontier term gets removed when taking the core.
      have prop_still_true_on_n3_facts : ∃ trg, orig.fst.equiv trg ∧ trg.val.loaded n3.node.facts := by
        cases ct.eq_or_strict_of_predecessor n3_prec with
        | inl eq =>
          exists orig.fst; constructor; exact PreTrigger.equiv_refl
          rw [← eq]
          apply Set.subset_trans orig_active_just_before_n1.left
          rw [← n1.node.ingoingFacts_eq, just_before_n1.subderivation.facts_childNodes (just_before_n1.mem_childNodes_of_mem_childNodes n1_child)]
          apply Set.subset_union_of_subset_left
          rw [just_before_n1.root_subderivation']
          exact Set.subset_refl
        | inr prec =>
          rcases ct.mem_childNodes_of_some_node_of_strict_prec prec with ⟨just_before_n3, just_before_n3_succ, n3_child⟩
          specialize n3_minimal just_before_n3 (ct.node_strict_prec_childNodes _ n3_child)
          unfold target_prop at n3_minimal
          simp only [not_and, Classical.not_not] at n3_minimal
          rcases n3_minimal just_before_n3_succ with ⟨trg, equiv, loaded⟩
          exists trg; constructor; exact equiv
          rw [← n3.node.ingoingFacts_eq, just_before_n3.subderivation.facts_childNodes (just_before_n3.mem_childNodes_of_mem_childNodes n3_child)]
          apply Set.subset_union_of_subset_left
          rw [just_before_n3.root_subderivation']
          exact loaded

      -- Now let's assume for a contradiction that all frontier terms are still part of n3's core.
      -- The idea for the rest of the proof is the following:
      -- There is a homomorphism from n3's facts to its core. If all frontier terms still occur in the core, then we can repeat this homomorphism to just be the identity on these terms. But then this repeated homomorphism can be used to build an equivalent trigger that is loaded on n3's core, which yields the desired contradiction.
      apply Classical.byContradiction
      simp only [not_exists, not_and, Classical.not_not]
      intro frontier_still_occurs
      apply none_loaded_n3
      rcases prop_still_true_on_n3_facts with ⟨trg', equiv', loaded'⟩

      rcases ex_hom_that_is_id_on_terms_of_isWeakCore_of_homSubset_of_finite n3.node.isWeakCore n3.node.homSubset (ct.core_finite_of_mem n3)
        with ⟨h, hom, id_on_terms⟩
      let target_trg : Trigger (RestrictedObsolescence sig) := { rule := trg'.val.rule, subs := h ∘ trg'.val.subs}
      exists ⟨target_trg, trg'.property⟩; constructor
      . constructor
        . rw [equiv'.left]
        . intro v v_mem
          rw [equiv'.right _ v_mem]
          simp only [target_trg, Function.comp_apply]
          rw [id_on_terms]
          suffices trg'.val.subs v = trg.val.subs v by
            rw [this]; apply frontier_still_occurs; rw [← equiv.left]; exact v_mem
          rw [← equiv'.right _ v_mem, equiv.right _ v_mem]
      . simp only [PreTrigger.loaded, PreTrigger.mapped_body]
        rw [GroundSubstitution.apply_function_free_conj_compose_of_isIdOnConstants _ _ hom.left]
        apply Set.subset_trans _ hom.right
        rw [Function.comp_apply]
        rw [← TermMapping.apply_generalized_atom_set_toSet]
        apply TermMapping.apply_generalized_atom_set_subset_of_subset
        exact loaded'
termination_by (n1, n2)

end OriginTriggerRemainsInactive

end CoreChaseTree

