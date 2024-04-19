import ProofLibrary.KnowledgeBaseBasics
import ProofLibrary.SubstitutionAndHomomorphismBasics

structure Trigger where
  rule : Rule
  subs : GroundSubstitution

namespace Trigger
  def skolemize_var_or_const (trg : Trigger) (var_or_const : VarOrConst) : SkolemTerm := 
    var_or_const.skolemize trg.rule.id trg.rule.frontier

  def apply_to_skolemized_term (trg : Trigger) (skolem_term : SkolemTerm) : GroundTerm :=
    trg.subs.apply_skolem_term skolem_term

  def apply_to_var_or_const (trg : Trigger) : VarOrConst -> GroundTerm := 
    (trg.apply_to_skolemized_term ∘ trg.skolemize_var_or_const)

  def apply_to_function_free_atom (trg : Trigger) (atom : FunctionFreeAtom) : Fact :=
    {
      predicate := atom.predicate
      terms := atom.terms.map trg.apply_to_var_or_const
    }

  theorem apply_to_function_free_atom_terms_same_length (trg : Trigger) (atom : FunctionFreeAtom) : atom.terms.length = (trg.apply_to_function_free_atom atom).terms.length := by 
    unfold apply_to_function_free_atom
    simp

  def mapped_body (trg : Trigger) : List Fact := SubsTarget.apply trg.subs trg.rule.body
  def mapped_head (trg : Trigger) : List Fact := trg.rule.head.map trg.apply_to_function_free_atom

  theorem head_length_eq_mapped_head_length (trg : Trigger) : trg.rule.head.length = trg.mapped_head.length := by 
    unfold mapped_head
    rw [List.length_map]

  def result (trg : Trigger) : FactSet :=
    trg.mapped_head.toSet

  def idx_of_fact_in_result (trg : Trigger) (f : Fact) (f_in_res : f ∈ trg.result) : Fin trg.rule.head.length :=
    let fin_mapped := trg.mapped_head.idx_of f (trg.mapped_head.listToSetElementAlsoListElement f f_in_res)
    have fin_mapped_isLt := fin_mapped.isLt
    ⟨fin_mapped.val, by simp [mapped_head, List.length_map, List.length_enum] at fin_mapped_isLt; exact fin_mapped_isLt⟩

  theorem apply_subs_to_atom_at_idx_same_as_fact_at_idx (trg : Trigger) (idx : Fin trg.rule.head.length) : trg.apply_to_function_free_atom (trg.rule.head.get idx) = trg.mapped_head.get ⟨idx.val, by rw [← head_length_eq_mapped_head_length]; exact idx.isLt⟩ := by 
    unfold mapped_head
    simp [List.get_map]
  
  def loaded (trg : Trigger) (F : FactSet) : Prop :=
    trg.mapped_body ⊆ F

  def sobsolete (trg : Trigger) (F : FactSet) : Prop := 
    trg.mapped_head ⊆ F

  def sactive (trg : Trigger) (F : FactSet) : Prop :=
    trg.loaded F ∧ ¬ (trg.sobsolete F)

  def robsolete (trg : Trigger) (F : FactSet) : Prop := 
    ∃ s : GroundSubstitution,
      (∀ v, List.elem v (Rule.frontier trg.rule) → s v = trg.subs v) ∧
      (
        let l : List Fact := SubsTarget.apply s trg.rule.head
        l ⊆ F
      )

  def ractive (trg : Trigger) (F : FactSet) : Prop :=
    trg.loaded F ∧ ¬ (trg.robsolete F)

  theorem term_mapping_preserves_loadedness (trg : Trigger) (F : FactSet) (h : GroundTermMapping) (hh : isHomomorphism h) : trg.loaded F -> { rule := trg.rule, subs := h ∘ trg.subs : Trigger }.loaded (applyFactSet h F) := by 
    simp [loaded, mapped_body]
    induction trg.rule.body with 
    | nil => intro _ _ _; contradiction
    | cons head tail ih => 
      intro base f hf
      simp [Set.element, Set.union, List.toSet] at hf
      cases hf with 
      | inl hl => 
        have := Set.element_mapping_preserves_membership (GroundSubstitution.apply_function_free_atom trg.subs head) F (applyFact h)
        have := this (base (GroundSubstitution.apply_function_free_atom trg.subs head) (by apply Or.inl; simp [Set.element]))
        simp [Set.element, applyFactSet]
        simp [Set.element] at this 
        cases this with | intro e he => 
          exists e
          rw [hl] 
          constructor 
          exact he.left 
          rw [← he.right]
          simp [applyFact, GroundSubstitution.apply_function_free_atom]
          rw [List.combine_nested_map]
          induction head.terms with 
          | nil => simp [List.map]
          | cons t_head t_tail t_ih => 
            simp [List.map]
            constructor
            . cases t_head with 
              | var v => simp [GroundSubstitution.apply_var_or_const]
              | const c => simp [GroundSubstitution.apply_var_or_const]; apply hh (GroundTerm.const c)
            . apply t_ih
      | inr hr => 
        apply ih
        intro _ hf'; apply base; apply Or.inr; apply hf'
        exact hr 
end Trigger

namespace FactSet
  def modelsDb (fs : FactSet) (db : Database) : Prop :=
    db.toFactSet ⊆ fs

  def modelsRule (fs : FactSet) (rule : Rule) : Prop :=
    ∀ trg : Trigger,
      (trg.rule = rule ∧ trg.loaded fs)
      -> ¬ trg.ractive fs -- the rule is ractive iff it is not satisfied under FOL semantics

  def modelsRules (fs : FactSet) (rules : RuleSet) : Prop :=
    ∀ r, r ∈ rules.rules -> fs.modelsRule r

  def modelsKb (fs : FactSet) (kb : KnowledgeBase) : Prop :=
    fs.modelsDb kb.db ∧ fs.modelsRules kb.rules

  def universallyModelsKb (fs : FactSet) (kb : KnowledgeBase) : Prop :=
    fs.modelsKb kb ∧ 
    (∀ m : FactSet,
      m.modelsKb kb ->
      ∃ (h : GroundTermMapping),
        isHomomorphism h ∧
        (applyFactSet h fs) ⊆ m
    )
end FactSet

def RTrigger (r : RuleSet) := { trg : Trigger // trg.rule ∈ r.rules}

namespace RTrigger 
  theorem funcTermForExisVarInMultipleTriggersMeansTheyAreTheSame 
    {rs : RuleSet} 
    (trg1 trg2 : RTrigger rs) 
    (var1 var2 : Variable) 
    -- (var1_in_head : ∃ headAtom : FunctionFreeAtom, trg1.val.rule.head.elem headAtom ∧ headAtom.terms.elem (VarOrConst.var var1)) 
    (var1_not_in_frontier : trg1.val.rule.frontier.elem var1 = false) 
    -- (var2_in_head : ∃ headAtom : FunctionFreeAtom, trg2.val.rule.head.elem headAtom ∧ headAtom.terms.elem (VarOrConst.var var2)) 
    (var2_not_in_frontier : trg2.val.rule.frontier.elem var2 = false) 
    : 
    (trg1.val.apply_to_var_or_const (VarOrConst.var var1)) = (trg2.val.apply_to_var_or_const (VarOrConst.var var2))
    -> 
    trg1.val.rule = trg2.val.rule ∧ ∀ v, v ∈ trg1.val.rule.frontier.toSet -> trg1.val.subs v = trg2.val.subs v := by 
    intro applications_eq 
    simp [Trigger.apply_to_var_or_const, Trigger.apply_to_skolemized_term, Trigger.skolemize_var_or_const, GroundSubstitution.apply_skolem_term, VarOrConst.skolemize, var1_not_in_frontier, var2_not_in_frontier] at applications_eq
    injection applications_eq with rule_ids_and_vars_eq arguments_eq
    simp at rule_ids_and_vars_eq
    have rules_eq : trg1.val.rule = trg2.val.rule := by 
      apply rs.id_unique
      constructor
      exact trg1.property
      constructor
      exact trg2.property
      exact rule_ids_and_vars_eq.left
    constructor
    . exact rules_eq
    . let right := arguments_eq 
      rw [← FiniteTreeList.eqIffFromListEq _ _] at right
      have : trg1.val.rule.frontier = trg2.val.rule.frontier := by rw [rules_eq]
      rw [← this] at right
      rw [← List.map_eq_map_iff] at right
      apply right
end RTrigger
