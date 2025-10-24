import ExistentialRules.ChaseSequence.Termination.BacktrackingOfFacts.PreTrigger

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

namespace ChaseBranch

  theorem term_ruleIds_valid (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) -> ∀ (term : GroundTerm sig), term ∈ node.facts.val.terms -> term.skolem_ruleIds_valid rl := by
    intro rl rl_rs_eq term term_mem
    induction i generalizing node term with
    | zero =>
      rw [cb.database_first] at eq
      injection eq with eq
      rw [← eq] at term_mem
      simp only at term_mem
      unfold FactSet.terms at term_mem
      rcases term_mem with ⟨f, f_mem, term_mem⟩
      rcases kb.db.toFactSet.property.right f f_mem term term_mem with ⟨_, t_eq⟩
      rw [t_eq]
      apply GroundTerm.skolem_ruleIds_valid_const
    | succ i ih =>
      rw [cb.origin_trg_result_yields_next_node_facts i node eq] at term_mem
      unfold FactSet.terms at term_mem
      rcases term_mem with ⟨f, f_mem, term_mem⟩
      cases f_mem with
      | inl f_mem => apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq); exists f
      | inr f_mem =>
        let origin := node.origin.get (cb.origin_isSome i eq)
        rw [List.mem_toSet] at f_mem
        apply PreTrigger.skolem_ruleIds_remain_valid_in_head rl origin.fst.val (by rw [rl_rs_eq]; exact origin.fst.property)
        . intro t t_mem
          rw [List.mem_flatMap] at t_mem
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) t
          exists f
          constructor
          . have := cb.origin_trg_is_active i node eq
            apply this.left
            rw [List.mem_toSet]
            exact f_mem
          . exact t_mem
        . rw [List.mem_flatMap]
          exists f
          constructor
          . apply List.mem_flatten_of_mem
            . exact List.getElem_mem origin.snd.isLt
            . exact f_mem
          . exact term_mem

  theorem trigger_ruleIds_valid_of_loaded (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) -> ∀ (trg : PreTrigger sig), trg.loaded node.facts -> trg.skolem_ruleIds_valid rl := by
    intro rl rl_rs_eq trg trg_loaded
    intro t t_mem_body
    rw [List.mem_flatMap] at t_mem_body
    rcases t_mem_body with ⟨f, f_mem, t_mem⟩
    specialize trg_loaded f (by rw [List.mem_toSet]; exact f_mem)
    apply cb.term_ruleIds_valid i node eq rl rl_rs_eq
    exists f

  theorem term_disjIdx_valid_aux (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) -> ∀ (term : GroundTerm sig), term ∈ node.facts.val.terms -> (h : term.skolem_ruleIds_valid rl) -> term.skolem_disjIdx_valid rl h := by
    intro rl rl_rs_eq term term_mem term_ruleIds_valid
    induction i generalizing node term with
    | zero =>
      rw [cb.database_first] at eq
      injection eq with eq
      rw [← eq] at term_mem
      simp only at term_mem
      unfold FactSet.terms at term_mem
      rcases term_mem with ⟨f, f_mem, term_mem⟩
      rcases kb.db.toFactSet.property.right f f_mem term term_mem with ⟨_, t_eq⟩
      simp only [t_eq]
      apply GroundTerm.skolem_disjIdx_valid_const
    | succ i ih =>
      rw [cb.origin_trg_result_yields_next_node_facts i node eq] at term_mem
      unfold FactSet.terms at term_mem
      rcases term_mem with ⟨f, f_mem, term_mem⟩
      cases f_mem with
      | inl f_mem => apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq); exists f
      | inr f_mem =>
        let origin := node.origin.get (cb.origin_isSome i eq)
        have origin_active := cb.origin_trg_is_active i node eq
        have origin_trg_valid := cb.trigger_ruleIds_valid_of_loaded i (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) rl rl_rs_eq origin.fst.val origin_active.left
        rw [List.mem_toSet] at f_mem
        apply PreTrigger.skolem_disjIdx_remains_valid_in_head rl origin.fst.val (by rw [rl_rs_eq]; exact origin.fst.property) origin_trg_valid
        . intro t t_mem
          rw [List.mem_flatMap] at t_mem
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) t
          exists f
          constructor
          . have := cb.origin_trg_is_active i node eq
            apply this.left
            rw [List.mem_toSet]
            exact f_mem
          . exact t_mem
        . rw [List.mem_flatMap]
          exists f
          constructor
          . apply List.mem_flatten_of_mem
            . exact List.getElem_mem origin.snd.isLt
            . exact f_mem
          . exact term_mem

  theorem term_disjIdx_valid (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (term : GroundTerm sig) (term_mem : term ∈ node.facts.val.terms) : term.skolem_disjIdx_valid rl (cb.term_ruleIds_valid i node eq rl rl_rs_eq term term_mem) := cb.term_disjIdx_valid_aux i node eq rl rl_rs_eq term term_mem (cb.term_ruleIds_valid i node eq rl rl_rs_eq term term_mem)

  theorem trigger_disjIdx_valid_of_loaded (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (trg : PreTrigger sig) (trg_loaded : trg.loaded node.facts) : trg.skolem_disjIdx_valid rl (cb.trigger_ruleIds_valid_of_loaded i node eq rl rl_rs_eq trg trg_loaded) := by
    intro t t_mem_body
    rw [List.mem_flatMap] at t_mem_body
    rcases t_mem_body with ⟨f, f_mem, t_mem⟩
    specialize trg_loaded f (by rw [List.mem_toSet]; exact f_mem)
    apply cb.term_disjIdx_valid i node eq rl rl_rs_eq
    exists f

  theorem term_rule_arity_valid_aux (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) :
      ∀ (rl : RuleList sig), (∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) -> ∀ (term : GroundTerm sig), term ∈ node.facts.val.terms -> (h : term.skolem_ruleIds_valid rl) -> term.skolem_rule_arity_valid rl h := by
    intro rl rl_rs_eq term term_mem term_ruleIds_valid
    induction i generalizing node term with
    | zero =>
      rw [cb.database_first] at eq
      injection eq with eq
      rw [← eq] at term_mem
      simp only at term_mem
      unfold FactSet.terms at term_mem
      rcases term_mem with ⟨f, f_mem, term_mem⟩
      rcases kb.db.toFactSet.property.right f f_mem term term_mem with ⟨_, t_eq⟩
      simp only [t_eq]
      apply GroundTerm.skolem_rule_arity_valid_const
    | succ i ih =>
      rw [cb.origin_trg_result_yields_next_node_facts i node eq] at term_mem
      unfold FactSet.terms at term_mem
      rcases term_mem with ⟨f, f_mem, term_mem⟩
      cases f_mem with
      | inl f_mem => apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq); exists f
      | inr f_mem =>
        let origin := node.origin.get (cb.origin_isSome i eq)
        have origin_active := cb.origin_trg_is_active i node eq
        have origin_trg_valid := cb.trigger_ruleIds_valid_of_loaded i (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) rl rl_rs_eq origin.fst.val origin_active.left
        rw [List.mem_toSet] at f_mem
        apply PreTrigger.skolem_rule_arity_remains_valid_in_head rl origin.fst.val (by rw [rl_rs_eq]; exact origin.fst.property) origin_trg_valid
        . intro t t_mem
          rw [List.mem_flatMap] at t_mem
          rcases t_mem with ⟨f, f_mem, t_mem⟩
          apply ih (cb.prev_node i (by simp [eq])) (by apply cb.prev_node_eq) t
          exists f
          constructor
          . have := cb.origin_trg_is_active i node eq
            apply this.left
            rw [List.mem_toSet]
            exact f_mem
          . exact t_mem
        . rw [List.mem_flatMap]
          exists f
          constructor
          . apply List.mem_flatten_of_mem
            . exact List.getElem_mem origin.snd.isLt
            . exact f_mem
          . exact term_mem

  theorem term_rule_arity_valid (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (term : GroundTerm sig) (term_mem : term ∈ node.facts.val.terms) : term.skolem_rule_arity_valid rl (cb.term_ruleIds_valid i node eq rl rl_rs_eq term term_mem) := cb.term_rule_arity_valid_aux i node eq rl rl_rs_eq term term_mem (cb.term_ruleIds_valid i node eq rl rl_rs_eq term term_mem)

  theorem trigger_rule_arity_valid_of_loaded (cb : ChaseBranch obs kb) (i : Nat) (node : ChaseNode obs kb.rules) (eq : cb.branch.infinite_list i = some node) (rl : RuleList sig) (rl_rs_eq : ∀ r, r ∈ rl.rules ↔ r ∈ kb.rules.rules) (trg : PreTrigger sig) (trg_loaded : trg.loaded node.facts) : trg.skolem_rule_arity_valid rl (cb.trigger_ruleIds_valid_of_loaded i node eq rl rl_rs_eq trg trg_loaded) := by
    intro t t_mem_body
    rw [List.mem_flatMap] at t_mem_body
    rcases t_mem_body with ⟨f, f_mem, t_mem⟩
    specialize trg_loaded f (by rw [List.mem_toSet]; exact f_mem)
    apply cb.term_rule_arity_valid i node eq rl rl_rs_eq
    exists f

end ChaseBranch

