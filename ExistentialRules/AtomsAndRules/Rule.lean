/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import ExistentialRules.AtomsAndRules.FunctionFreeConjunction

/-!
# (Disjunctive) (Existential) Rule

A disjunctive existential rule, or simply `Rule`, formally is an expression of the form
$$∀ \vec{x}, \vec{y}. B(x, y) \to \bigvee_{i = 1}^{k} \exists \vec{z}_i. H_i(y_i, z_i)$$
where $B,H_1,\dots,H_k$ are conjunctions of function free atoms, $y$ is exactly the union of all $y_i$
and $x$, $y$, and all $z_i$ are disjoint lists of variables. $y$ is called *frontier*. $B$ is called body and the $H_i$ are called heads.
We call a rule *determinstic* if $k = 1$ so if the head is merely a conjunction.
For an overview on such rules (without disjunction) consider for example [ExistentialRules].

To represent this formal definition in Lean, we use a structure with a `FunctionFreeConjunction` for the body and a list of `FunctionFreeConjunction`s for the disjunction in the head. That's it!
The frontier variables can simply be defined as the variables occurring both in body and head and the existential variables can be indentified as the variables that occur only in the head, without the need for explicit quantification.
-/

public section

/-- The definition of a `Rule` as discussed above. -/
structure Rule (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  body : FunctionFreeConjunction sig
  head : List (FunctionFreeConjunction sig)
deriving DecidableEq

namespace Rule

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- This function returns the frontier variables that occur in a given head disjunct. This is a sublist of all the frontier variables. -/
@[expose]
def frontier_for_head (r : Rule sig) (i : Nat) (lt : i < r.head.length) : List sig.V :=
  r.body.vars.filter (fun v => v ∈ r.head[i].vars)

/-- This returns all the `frontier` variables of the rule, i.e. the variables that occur in both body and some head. -/
@[expose]
def frontier (r : Rule sig) : List sig.V :=
  r.body.vars.filter (fun v => r.head.any (fun h => v ∈ h.vars))

/-- The `pure_body_vars` are the variables from the body that are not in the `frontier`. -/
@[expose]
def pure_body_vars (r : Rule sig) : List sig.V := r.body.vars.filter (fun x => x ∉ r.frontier)

/-- We call a rule `isDatalog` if it does not contain existential variables, i.e. if all head variables occur in the body. -/
@[expose]
def isDatalog (r : Rule sig) : Bool :=
  r.head.all (fun h => h.vars.all (fun v => v ∈ r.body.vars))

/-- We call a rule `isDeterministic` if it has exactly one head disjunct. -/
@[expose]
def isDeterministic (r : Rule sig) : Bool := r.head.length = 1

/-- The predicate symbols of a rule are just the predicate symbols from the body and all heads. -/
@[expose]
def predicates (r : Rule sig) : List sig.P := r.body.predicates ++ (r.head.flatMap FunctionFreeConjunction.predicates)

/-- The constants of a rule are just the constants from the body and all heads. -/
@[expose]
def constants (r : Rule sig) : List sig.C := r.body.consts ++ r.head.flatMap (fun conj => conj.consts)

/-- Sometimes we require only the constants from the heads and therefore we define them here. -/
@[expose]
def head_constants (r : Rule sig) : List sig.C := r.head.flatMap (fun conj => conj.consts)

/-- The existential variables for a given head are simply the variables from the head that are not in the frontier. -/
@[expose]
def existential_vars_for_head_disjunct (r : Rule sig) (i : Nat) (lt : i < r.head.length) : List sig.V :=
  r.head[i].vars.filter (fun v => v ∉ r.frontier)

/-- A variable is a frontier variable if and only if it is a frontier variable in some head disjunct. -/
theorem mem_frontier_iff_mem_frontier_for_head {r : Rule sig} {v : sig.V} :
    v ∈ r.frontier ↔ ∃ i lt, v ∈ r.frontier_for_head i lt := by
  unfold frontier frontier_for_head
  simp only [List.mem_filter, List.any_eq_true, decide_eq_true_iff]
  constructor
  . rintro ⟨mem_body, ⟨h, h_mem, mem_h⟩⟩
    rw [List.mem_iff_getElem] at h_mem
    grind
  . grind

/-- A variable is in the frontier of a head if it is in the frontier of the rule and occurs as a term in the given head. -/
theorem mem_frontier_for_head_of_mem_frontier_of_mem_head_terms {r : Rule sig} {v : sig.V} {i : Nat} (lt : i < r.head.length) :
    v ∈ r.frontier -> VarOrConst.var v ∈ r.head[i].terms -> v ∈ r.frontier_for_head i lt := by
  unfold frontier frontier_for_head
  unfold FunctionFreeConjunction.terms
  grind

/-- All frontier variables occur in the body. -/
@[grind <-]
theorem frontier_subset_vars_body {r : Rule sig} : r.frontier ⊆ r.body.vars := by
  unfold Rule.frontier
  grind

/-- The frontier variables in a given head occur in the list of variables for the same head. -/
@[grind <-]
theorem frontier_for_head_subset_vars_head {r : Rule sig} {i : Nat} (lt : i < r.head.length) : r.frontier_for_head i lt ⊆ r.head[i].vars := by
  unfold Rule.frontier_for_head
  grind

/-- The head constants of the rule are also constants of the whole rule. -/
@[grind <-]
theorem head_constants_subset_constants (r : Rule sig) : r.head_constants ⊆ r.constants := by apply List.subset_append_right

/-- Each existential variable is in the head. -/
@[grind ->]
theorem mem_head_vars_of_mem_existential_vars_for_head_disjunct {r : Rule sig} {i : Nat} {lt : i < r.head.length} :
    ∀ v ∈ r.existential_vars_for_head_disjunct i lt, v ∈ r.head[i].vars := by
  grind [existential_vars_for_head_disjunct]

/-- Each existential variable is not in the frontier. -/
@[grind ->]
theorem not_mem_frontier_of_mem_existential_vars_for_head_disjunct {r : Rule sig} {i : Nat} {lt : i < r.head.length} :
    ∀ v ∈ r.existential_vars_for_head_disjunct i lt, v ∉ r.frontier := by
  grind [existential_vars_for_head_disjunct]

end Rule

