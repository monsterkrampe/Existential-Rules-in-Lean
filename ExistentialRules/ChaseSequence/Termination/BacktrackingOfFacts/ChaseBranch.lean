import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts.PreTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace ChaseDerivation

  variable {obs : ObsoletenessCondition sig} {rules : RuleSet sig}

  theorem term_ruleIds_valid {cd : ChaseDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) :
      ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ rules.rules) -> (∀ t ∈ cd.head.facts.terms, t.skolem_ruleIds_valid rl) -> ∀ t ∈ node.facts.terms, t.skolem_ruleIds_valid rl := by
    intro rl rl_rs_eq head_valid
    let node : cd.Node := ⟨node, node_mem⟩
    show ∀ t ∈ node.val.facts.terms, t.skolem_ruleIds_valid rl
    induction node using cd.mem_rec with
    | head => intro t t_mem; apply head_valid; exact t_mem
    | step cd2 suffix ih next next_mem =>
      intro t t_mem
      rw [cd2.facts_next next_mem, FactSet.terms_union] at t_mem
      cases t_mem with
      | inl t_mem => apply ih; exact t_mem
      | inr t_mem =>
        let origin := next.origin.get (cd2.isSome_origin_next next_mem)
        apply PreTrigger.skolem_ruleIds_remain_valid_in_head rl origin.fst.val (by rw [rl_rs_eq]; exact origin.fst.property)
        . intro t t_mem
          apply ih
          apply FactSet.terms_subset_of_subset (cd2.active_trigger_origin_next next_mem).left
          rw [FactSet.mem_terms_toSet]; exact t_mem
        . rw [FactSet.mem_terms_toSet] at t_mem
          rw [List.mem_flatMap] at t_mem
          rw [List.mem_flatMap]
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          exists f; constructor
          . apply List.mem_flatten_of_mem
            . exact List.getElem_mem origin.snd.isLt
            . exact f_mem
          . exact t_mem

  theorem trigger_ruleIds_valid_of_loaded {cd : ChaseDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) :
      ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ rules.rules) -> (∀ t ∈ cd.head.facts.terms, t.skolem_ruleIds_valid rl) -> ∀ (trg : PreTrigger sig), trg.loaded node.facts -> trg.skolem_ruleIds_valid rl := by
    intro rl rl_rs_eq head_valid trg trg_loaded t t_mem
    apply cd.term_ruleIds_valid node_mem rl rl_rs_eq head_valid
    apply FactSet.terms_subset_of_subset trg_loaded
    rw [FactSet.mem_terms_toSet]
    exact t_mem

  theorem term_disjIdx_valid_aux {cd : ChaseDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) :
      ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ rules.rules) -> (h_head : ∀ t ∈ cd.head.facts.terms, t.skolem_ruleIds_valid rl) -> (∀ t, (t_mem : t ∈ cd.head.facts.terms) -> t.skolem_disjIdx_valid rl (h_head _ t_mem)) -> ∀ t ∈ node.facts.terms, (h : t.skolem_ruleIds_valid rl) -> t.skolem_disjIdx_valid rl h := by
    intro rl rl_rs_eq head_ruleIds_valid head_valid
    let node : cd.Node := ⟨node, node_mem⟩
    show ∀ t ∈ node.val.facts.terms, (h : t.skolem_ruleIds_valid rl) -> t.skolem_disjIdx_valid rl h
    induction node using cd.mem_rec with
    | head => intro t t_mem h; apply head_valid; exact t_mem
    | step cd2 suffix ih next next_mem =>
      intro t t_mem h
      rw [cd2.facts_next next_mem, FactSet.terms_union] at t_mem
      cases t_mem with
      | inl t_mem => apply ih; exact t_mem
      | inr t_mem =>
        let origin := next.origin.get (cd2.isSome_origin_next next_mem)
        apply PreTrigger.skolem_disjIdx_remains_valid_in_head rl origin.fst.val (by rw [rl_rs_eq]; exact origin.fst.property) (by
          apply cd.trigger_ruleIds_valid_of_loaded (cd2.mem_of_mem_suffix suffix _ cd2.head_mem) rl rl_rs_eq head_ruleIds_valid
          exact (cd2.active_trigger_origin_next next_mem).left)
        . intro t t_mem
          apply ih
          apply FactSet.terms_subset_of_subset (cd2.active_trigger_origin_next next_mem).left
          rw [FactSet.mem_terms_toSet]; exact t_mem
        . rw [FactSet.mem_terms_toSet] at t_mem
          rw [List.mem_flatMap] at t_mem
          rw [List.mem_flatMap]
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          exists f; constructor
          . apply List.mem_flatten_of_mem
            . exact List.getElem_mem origin.snd.isLt
            . exact f_mem
          . exact t_mem

  theorem term_disjIdx_valid {cd : ChaseDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ rules.rules) (head_ruleIds_valid : ∀ t ∈ cd.head.facts.terms, t.skolem_ruleIds_valid rl) (head_valid : (∀ t, (t_mem : t ∈ cd.head.facts.terms) -> t.skolem_disjIdx_valid rl (head_ruleIds_valid _ t_mem))) (t : GroundTerm sig) (t_mem : t ∈ node.facts.terms) : t.skolem_disjIdx_valid rl (cd.term_ruleIds_valid node_mem rl rl_rs_eq head_ruleIds_valid t t_mem) := cd.term_disjIdx_valid_aux node_mem rl rl_rs_eq head_ruleIds_valid head_valid t t_mem (cd.term_ruleIds_valid node_mem rl rl_rs_eq head_ruleIds_valid t t_mem)

  theorem trigger_disjIdx_valid_of_loaded {cd : ChaseDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ rules.rules) (head_ruleIds_valid : ∀ t ∈ cd.head.facts.terms, t.skolem_ruleIds_valid rl) (head_valid : (∀ t, (t_mem : t ∈ cd.head.facts.terms) -> t.skolem_disjIdx_valid rl (head_ruleIds_valid _ t_mem))) (trg : PreTrigger sig) (trg_loaded : trg.loaded node.facts) : trg.skolem_disjIdx_valid rl (cd.trigger_ruleIds_valid_of_loaded node_mem rl rl_rs_eq head_ruleIds_valid trg trg_loaded) := by
    intro t t_mem
    apply cd.term_disjIdx_valid node_mem rl rl_rs_eq head_ruleIds_valid head_valid
    apply FactSet.terms_subset_of_subset trg_loaded
    rw [FactSet.mem_terms_toSet]
    exact t_mem

  theorem term_rule_arity_valid_aux {cd : ChaseDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) :
      ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ rules.rules) -> (h_head : ∀ t ∈ cd.head.facts.terms, t.skolem_ruleIds_valid rl) -> (∀ t, (t_mem : t ∈ cd.head.facts.terms) -> t.skolem_rule_arity_valid rl (h_head _ t_mem)) -> ∀ t ∈ node.facts.terms, (h : t.skolem_ruleIds_valid rl) -> t.skolem_rule_arity_valid rl h := by
    intro rl rl_rs_eq head_ruleIds_valid head_valid
    let node : cd.Node := ⟨node, node_mem⟩
    show ∀ t ∈ node.val.facts.terms, (h : t.skolem_ruleIds_valid rl) -> t.skolem_rule_arity_valid rl h
    induction node using cd.mem_rec with
    | head => intro t t_mem h; apply head_valid; exact t_mem
    | step cd2 suffix ih next next_mem =>
      intro t t_mem h
      rw [cd2.facts_next next_mem, FactSet.terms_union] at t_mem
      cases t_mem with
      | inl t_mem => apply ih; exact t_mem
      | inr t_mem =>
        let origin := next.origin.get (cd2.isSome_origin_next next_mem)
        apply PreTrigger.skolem_rule_arity_remains_valid_in_head rl origin.fst.val (by rw [rl_rs_eq]; exact origin.fst.property) (by
          apply cd.trigger_ruleIds_valid_of_loaded (cd2.mem_of_mem_suffix suffix _ cd2.head_mem) rl rl_rs_eq head_ruleIds_valid
          exact (cd2.active_trigger_origin_next next_mem).left)
        . intro t t_mem
          apply ih
          apply FactSet.terms_subset_of_subset (cd2.active_trigger_origin_next next_mem).left
          rw [FactSet.mem_terms_toSet]; exact t_mem
        . rw [FactSet.mem_terms_toSet] at t_mem
          rw [List.mem_flatMap] at t_mem
          rw [List.mem_flatMap]
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          exists f; constructor
          . apply List.mem_flatten_of_mem
            . exact List.getElem_mem origin.snd.isLt
            . exact f_mem
          . exact t_mem

  theorem term_rule_arity_valid {cd : ChaseDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ rules.rules) (head_ruleIds_valid : ∀ t ∈ cd.head.facts.terms, t.skolem_ruleIds_valid rl) (head_valid : (∀ t, (t_mem : t ∈ cd.head.facts.terms) -> t.skolem_rule_arity_valid rl (head_ruleIds_valid _ t_mem))) (t : GroundTerm sig) (t_mem : t ∈ node.facts.terms) : t.skolem_rule_arity_valid rl (cd.term_ruleIds_valid node_mem rl rl_rs_eq head_ruleIds_valid t t_mem) := cd.term_rule_arity_valid_aux node_mem rl rl_rs_eq head_ruleIds_valid head_valid t t_mem (cd.term_ruleIds_valid node_mem rl rl_rs_eq head_ruleIds_valid t t_mem)

  theorem trigger_rule_arity_valid_of_loaded {cd : ChaseDerivation obs rules} {node : ChaseNode obs rules} (node_mem : node ∈ cd) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ rules.rules) (head_ruleIds_valid : ∀ t ∈ cd.head.facts.terms, t.skolem_ruleIds_valid rl) (head_valid : (∀ t, (t_mem : t ∈ cd.head.facts.terms) -> t.skolem_rule_arity_valid rl (head_ruleIds_valid _ t_mem))) (trg : PreTrigger sig) (trg_loaded : trg.loaded node.facts) : trg.skolem_rule_arity_valid rl (cd.trigger_ruleIds_valid_of_loaded node_mem rl rl_rs_eq head_ruleIds_valid trg trg_loaded) := by
    intro t t_mem
    apply cd.term_rule_arity_valid node_mem rl rl_rs_eq head_ruleIds_valid head_valid
    apply FactSet.terms_subset_of_subset trg_loaded
    rw [FactSet.mem_terms_toSet]
    exact t_mem

end ChaseDerivation


namespace ChaseBranch

  variable {obs : ObsoletenessCondition sig} {kb : KnowledgeBase sig}

  theorem term_ruleIds_valid {cb : ChaseBranch obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ cb.toChaseDerivation) :
      ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) -> ∀ t ∈ node.facts.terms, t.skolem_ruleIds_valid rl := by
    intro rl rl_rs_eq t t_mem
    apply cb.toChaseDerivation.term_ruleIds_valid node_mem rl rl_rs_eq _ t t_mem
    intro t t_mem
    simp only [cb.database_first'] at t_mem
    rcases t_mem with ⟨f, f_mem, t_mem⟩
    rcases kb.db.toFactSet.property.right _ f_mem _ t_mem with ⟨_, t_eq⟩
    rw [t_eq]
    apply GroundTerm.skolem_ruleIds_valid_const

  theorem trigger_ruleIds_valid_of_loaded {cb : ChaseBranch obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ cb.toChaseDerivation) :
      ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) -> ∀ (trg : PreTrigger sig), trg.loaded node.facts -> trg.skolem_ruleIds_valid rl := by
    intro rl rl_rs_eq trg trg_loaded t t_mem
    apply cb.term_ruleIds_valid node_mem rl rl_rs_eq
    apply FactSet.terms_subset_of_subset trg_loaded
    rw [FactSet.mem_terms_toSet]
    exact t_mem

  theorem term_disjIdx_valid {cb : ChaseBranch obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ cb.toChaseDerivation) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (t : GroundTerm sig) (t_mem : t ∈ node.facts.terms) : t.skolem_disjIdx_valid rl (cb.term_ruleIds_valid node_mem rl rl_rs_eq t t_mem) := by
    apply cb.toChaseDerivation.term_disjIdx_valid node_mem rl rl_rs_eq _ _ t t_mem
    . intro t t_mem
      simp only [cb.database_first'] at t_mem
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rcases kb.db.toFactSet.property.right _ f_mem _ t_mem with ⟨_, t_eq⟩
      rw [t_eq]
      apply GroundTerm.skolem_ruleIds_valid_const
    . intro t t_mem
      simp only [cb.database_first'] at t_mem
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rcases kb.db.toFactSet.property.right _ f_mem _ t_mem with ⟨_, t_eq⟩
      simp only [t_eq]
      apply GroundTerm.skolem_disjIdx_valid_const

  theorem trigger_disjIdx_valid_of_loaded {cb : ChaseBranch obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ cb.toChaseDerivation) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (trg : PreTrigger sig) (trg_loaded : trg.loaded node.facts) : trg.skolem_disjIdx_valid rl (cb.trigger_ruleIds_valid_of_loaded node_mem rl rl_rs_eq trg trg_loaded) := by
    intro t t_mem
    apply cb.term_disjIdx_valid node_mem rl rl_rs_eq
    apply FactSet.terms_subset_of_subset trg_loaded
    rw [FactSet.mem_terms_toSet]
    exact t_mem

  theorem term_rule_arity_valid {cb : ChaseBranch obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ cb.toChaseDerivation) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (t : GroundTerm sig) (t_mem : t ∈ node.facts.terms) : t.skolem_rule_arity_valid rl (cb.term_ruleIds_valid node_mem rl rl_rs_eq t t_mem) := by
    apply cb.toChaseDerivation.term_rule_arity_valid node_mem rl rl_rs_eq _ _ t t_mem
    . intro t t_mem
      simp only [cb.database_first'] at t_mem
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rcases kb.db.toFactSet.property.right _ f_mem _ t_mem with ⟨_, t_eq⟩
      rw [t_eq]
      apply GroundTerm.skolem_ruleIds_valid_const
    . intro t t_mem
      simp only [cb.database_first'] at t_mem
      rcases t_mem with ⟨f, f_mem, t_mem⟩
      rcases kb.db.toFactSet.property.right _ f_mem _ t_mem with ⟨_, t_eq⟩
      simp only [t_eq]
      apply GroundTerm.skolem_rule_arity_valid_const

  theorem trigger_rule_arity_valid_of_loaded {cb : ChaseBranch obs kb} {node : ChaseNode obs kb.rules} (node_mem : node ∈ cb.toChaseDerivation) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (trg : PreTrigger sig) (trg_loaded : trg.loaded node.facts) : trg.skolem_rule_arity_valid rl (cb.trigger_ruleIds_valid_of_loaded node_mem rl rl_rs_eq trg trg_loaded) := by
    intro t t_mem
    apply cb.term_rule_arity_valid node_mem rl rl_rs_eq
    apply FactSet.terms_subset_of_subset trg_loaded
    rw [FactSet.mem_terms_toSet]
    exact t_mem

end ChaseBranch

