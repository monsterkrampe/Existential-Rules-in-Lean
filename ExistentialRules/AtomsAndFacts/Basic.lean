module

import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.List.EraseDupsKeepRight
public import BasicLeanDatastructures.Set.Basic
public import BasicLeanDatastructures.Set.Finite

public import ExistentialRules.Terms.Basic
import ExistentialRules.Terms.ListsOfTerms

/-!
# Atoms, Facts, Rules and the like

In this file, we define the next layers of building blocks above terms.
This includes first and foremost `Atom` and `Fact` but also
`Rule`, `RuleSet`, `Database` and `KnowledgeBase` to name a few.

The atom-like datastructures are all expressed in terms of a `GeneralizedAtom`. This will turn out convenient when defining substitutions and homomorphisms next since these can (for the most part) just be defines as generic mapping over `GeneralizedAtom`.
-/

public section

/-- A `GeneralizedAtom` consists of a predicate symbol and a list of terms of an arbitrary type such that the number of terms matches the predicate's arity. -/
structure GeneralizedAtom (sig : Signature) (T : Type u) [DecidableEq sig.P] where
  predicate : sig.P
  terms : List T
  arity_ok : terms.length = sig.arity predicate
deriving DecidableEq

/-!
## Atom
-/

/-- An `Atom` is a `GeneralizedAtom` with `SkolemTerm`s. -/
abbrev Atom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := GeneralizedAtom sig (SkolemTerm sig)

section FunctionFreeAtom

/-!
## FunctionFreeAtom
-/

/-- A `FunctionFreeAtom` is a `GeneralizedAtom` with `VarOrConst`s. -/
abbrev FunctionFreeAtom (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := GeneralizedAtom sig (VarOrConst sig)

namespace FunctionFreeAtom

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- Using `VarOrConst.filterVars`, we can obtain all variables from the terms of the `FunctionFreeAtom`. -/
def variables (a : FunctionFreeAtom sig) : List sig.V := VarOrConst.filterVars a.terms

/-- Using `VarOrConst.filterConsts`, we can obtain all constants from the terms of the `FunctionFreeAtom`. -/
def constants (a : FunctionFreeAtom sig) : List sig.C := VarOrConst.filterConsts a.terms

/-- We can `skolemize` a `FunctionFreeAtom` by skolemizing all its `VarOrConst`s. This yields an `Atom`. -/
def skolemize (ruleId : Nat) (disjunctIndex : Nat) (frontier : List sig.V) (a : FunctionFreeAtom sig) : Atom sig := {
  predicate := a.predicate,
  terms := a.terms.map (VarOrConst.skolemize ruleId disjunctIndex frontier),
  arity_ok := by rw [List.length_map, a.arity_ok]
}

/-- A variable occurs in `variables` iff it is a term of the `FunctionFreeAtom. -/
@[simp, grind =]
theorem mem_variables {a : FunctionFreeAtom sig} {v : sig.V} : v ∈ a.variables ↔ (VarOrConst.var v) ∈ a.terms := by
  unfold variables; grind

/-- A constant occurs in `constants` iff it is a term of the `FunctionFreeAtom. -/
@[simp, grind =]
theorem mem_constants {a : FunctionFreeAtom sig} {c : sig.C} : c ∈ a.constants ↔ (VarOrConst.const c) ∈ a.terms := by
  unfold constants; grind

/-- The number of terms remains unchanged when Skolemizing. -/
@[simp, grind =]
theorem length_skolemize {ruleId : Nat} {disjunctIndex : Nat} {frontier : List sig.V} {a : FunctionFreeAtom sig} :
    (a.skolemize ruleId disjunctIndex frontier).terms.length = a.terms.length := by
  unfold skolemize; simp

/-- If a a `VarOrConst` occurs in the terms of the `FunctionFreeAtom`, then the Skolemized `VarOrConst` occurs in the Skolemized `Atom`. -/
@[grind <-]
theorem mem_skolemize_of_mem {ruleId : Nat} {disjunctIndex : Nat} {frontier : List sig.V}
    {a : FunctionFreeAtom sig} {t : VarOrConst sig} :
    t ∈ a.terms -> (t.skolemize ruleId disjunctIndex frontier) ∈ (a.skolemize ruleId disjunctIndex frontier).terms := by
  unfold skolemize
  intro t_mem
  rw [List.mem_map]
  exists t

end FunctionFreeAtom

end FunctionFreeAtom

section FunctionFreeConjunction

/-!
## FunctionFreeConjunction
-/

/-- A conjunction of `FunctionFreeAtom`s $p(x, y) \land q(y)$ can simply be represented as a list of `FunctionFreeAtom`s. -/
abbrev FunctionFreeConjunction (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := List (FunctionFreeAtom sig)

namespace FunctionFreeConjunction

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The `terms` of a `FunctionFreeConjunction` are the terms of all its atoms. -/
@[expose]
def terms (conj : FunctionFreeConjunction sig) : List (VarOrConst sig) := conj.flatMap GeneralizedAtom.terms

/-- The `vars` of a `FunctionFreeConjunction` are the variables of all its atoms. -/
def vars (conj : FunctionFreeConjunction sig) : List sig.V := conj.flatMap FunctionFreeAtom.variables

/-- The `consts` of a `FunctionFreeConjunction` are the constants of all its atoms. -/
def consts (conj : FunctionFreeConjunction sig) : List sig.C := conj.flatMap FunctionFreeAtom.constants

/-- The `predicates` of a `FunctionFreeConjunction` are the predicates of all its atoms. -/
@[expose]
def predicates (conj : FunctionFreeConjunction sig) : List sig.P := conj.map GeneralizedAtom.predicate

/-- Different from the definition, we can also say that a variable is in `variables` iff there is a `FunctionFreeAtom` in the conjunction that features the variable as a term. -/
@[simp, grind =]
theorem mem_vars {conj : FunctionFreeConjunction sig} {v : sig.V} :
    v ∈ conj.vars ↔ ∃ f, f ∈ conj ∧ (VarOrConst.var v) ∈ f.terms := by
  unfold vars; simp

/-- Different from the definition, we can also say that a constant is in `constants` iff there is a `FunctionFreeAtom` in the conjunction that features the constant as a term. -/
@[simp, grind =]
theorem mem_consts {conj : FunctionFreeConjunction sig} {c : sig.C} :
    c ∈ conj.consts ↔ ∃ f, f ∈ conj ∧ (VarOrConst.const c) ∈ f.terms := by
  unfold consts; simp

end FunctionFreeConjunction

end FunctionFreeConjunction

section Rule

/-!
## (Disjunctive) (Existential) Rule

A disjunctive existential rule, or simply `Rule`, formally is an expression of the form
$$∀ \vec{x}, \vec{y}. B(x, y) \to \bigvee_{i = 1}^{k} \exists \vec{z}_i. H_i(y_i, z_i)$$
where $B,H_1,\dots,H_k$ are conjunctions of function free atoms, $y$ is exactly the union of all $y_i$
and $x$, $y$, and all $z_i$ are disjoint lists of variables. $y$ is called *frontier*. $B$ is called body and the $H_i$ are called heads.
We call a rule *determinstic* if $k = 1$ so if the head is merely a conjunction.

To represent this formal definition in Lean, we use a structure with a `FunctionFreeConjunction` for the body and a list of `FunctionFreeConjunction`s for the disjunction in the head. For bookkeeping each rule also gets an id. That's it!
The frontier variables can simply be defined as the variables occurring both in body and head and the existential variables can be indentified as the variables that occur only in the head, without the need for explicit quantification.
-/

/-- The definition of a `Rule` as discussed above. -/
structure Rule (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  id : Nat
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

/-- The Skolem function symbols of a rule are all `SkolemFS` with the rule id, all possible head indices and the respective existential variables. -/
@[expose]
def skolem_functions (r : Rule sig) : List (SkolemFS sig) := r.head.zipIdx.flatMap (fun (head, i) =>
  (head.vars.filter (fun v => v ∉ r.frontier)).map (fun v => { ruleId := r.id, disjunctIndex := i, var := v, arity := r.frontier.length })
)

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

end Rule

end Rule

section RuleSetAndRuleList

/-!
## RuleSet and RuleList
-/

/-- A `RuleSet` is a `Set (Rule sig)` where rules are uniquely identified by their id. -/
structure RuleSet (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  rules : Set (Rule sig)
  id_unique : ∀ r1 r2, r1 ∈ rules ∧ r2 ∈ rules ∧ r1.id = r2.id -> r1 = r2

/-- A `RuleList` is a `List (Rule sig)` where rules are uniquely identified by their id. -/
structure RuleList (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  rules : List (Rule sig)
  id_unique : ∀ r1 r2, r1 ∈ rules ∧ r2 ∈ rules ∧ r1.id = r2.id -> r1 = r2

namespace RuleSet

/-!
### RuleSet
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `RuleSet` is is deterministic if each rule is. -/
@[expose]
def isDeterministic (rs : RuleSet sig) : Prop := ∀ (r : Rule sig), r ∈ rs.rules -> r.isDeterministic

/-- The predicate symbols of a `RuleSet` are the predicate symbols from all rules. -/
@[expose]
def predicates (rs : RuleSet sig) : Set sig.P := fun p => ∃ r, r ∈ rs.rules ∧ p ∈ r.predicates

/-- The constants of a `RuleSet` are the constants from all rules. -/
@[expose]
def constants (rs : RuleSet sig) : Set sig.C := fun c => ∃ r, r ∈ rs.rules ∧ c ∈ r.constants

/-- The head constants of a `RuleSet` are the head constants from all rules. -/
@[expose]
def head_constants (rs : RuleSet sig) : Set sig.C := fun c => ∃ r, r ∈ rs.rules ∧ c ∈ r.head_constants

/-- The Skolem function symbols of a `RuleSet` are the Skolem function symbols from all rules. -/
@[expose]
def skolem_functions (rs : RuleSet sig) : Set (SkolemFS sig) := fun f => ∃ r, r ∈ rs.rules ∧ f ∈ r.skolem_functions

/-- If the `RuleSet` is finite, so are the `predicates`. -/
@[grind ->]
theorem predicates_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.predicates.finite := by
  intro finite
  rcases finite with ⟨l, nodup, eq⟩
  exists (l.flatMap Rule.predicates).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro p
    rw [List.mem_eraseDupsKeepRight]
    unfold predicates
    simp only [List.mem_flatMap]
    constructor <;> (intro ⟨r, h⟩; exists r; grind)

/-- If the `RuleSet` is finite, so are the `constants`. -/
@[grind ->]
theorem constants_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.constants.finite := by
  intro finite
  rcases finite with ⟨l, nodup, eq⟩
  exists (l.flatMap Rule.constants).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro c
    rw [List.mem_eraseDupsKeepRight]
    unfold constants
    simp only [List.mem_flatMap]
    constructor <;> (intro ⟨r, h⟩; exists r; grind)

/-- If the `RuleSet` is finite, so are the `head_constants`. -/
@[grind ->]
theorem head_constants_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.head_constants.finite := by
  intro finite
  rcases finite with ⟨l, nodup, eq⟩
  exists (l.flatMap Rule.head_constants).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro c
    rw [List.mem_eraseDupsKeepRight]
    unfold head_constants
    simp only [List.mem_flatMap]
    constructor <;> (intro ⟨r, h⟩; exists r; grind)

/-- If the `RuleSet` is finite, so are the `skolem_functions`. -/
@[grind ->]
theorem skolem_functions_finite_of_finite (rs : RuleSet sig) : rs.rules.finite -> rs.skolem_functions.finite := by
  intro finite
  rcases finite with ⟨l, nodup, eq⟩
  exists (l.flatMap Rule.skolem_functions).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro c
    rw [List.mem_eraseDupsKeepRight]
    unfold skolem_functions
    simp only [List.mem_flatMap]
    constructor <;> (intro ⟨r, h⟩; exists r; grind)

/-- The `head_constants` of a `RuleSet` are a subset of the `constants`. -/
@[grind <-]
theorem head_constants_subset_constants (rs : RuleSet sig) : rs.head_constants ⊆ rs.constants := by
  intro c c_mem
  rcases c_mem with ⟨r, r_mem, c_mem⟩
  exists r
  constructor
  . exact r_mem
  . apply Rule.head_constants_subset_constants; exact c_mem

end RuleSet

namespace RuleList

/-!
### RuleList
-/

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- In a `RuleList`, we can obtain a rule based on its id. -/
def get_by_id (rl : RuleList sig) (id : Nat) (id_mem : ∃ r ∈ rl.rules, r.id = id) : Rule sig :=
  (rl.rules.find? (fun r => r.id = id)).get (by simp [id_mem])

/-- A rule that we get by id is in the `RuleList`. -/
theorem get_by_id_mem (rl : RuleList sig) (id : Nat) (id_mem : ∃ r ∈ rl.rules, r.id = id) : rl.get_by_id id id_mem ∈ rl.rules := by
  unfold get_by_id; apply List.get_find?_mem

/-- A rule that we get by id is indeed the rule that the id belongs to. -/
@[simp, grind =]
theorem get_by_id_self (rl : RuleList sig) (r : Rule sig) (mem : r ∈ rl.rules) : rl.get_by_id r.id (by exists r) = r := by
  apply rl.id_unique
  constructor
  . apply List.get_find?_mem
  constructor
  . exact mem
  . unfold get_by_id
    have eq : rl.rules.find? (fun r' => r'.id = r.id) = some ((rl.rules.find? (fun r' => r'.id = r.id)).get (by rw [List.find?_isSome]; exists r; constructor; exact mem; simp)) := by simp
    apply of_decide_eq_true
    apply List.find?_some eq

end RuleList

end RuleSetAndRuleList

section FactAndFunctionFreeFact

/-!
## Facts and FunctionFreeFacts
-/

/-- A `Fact` is a `GeneralizedAtom` with `GroundTerm`s. -/
abbrev Fact (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := GeneralizedAtom sig (GroundTerm sig)

/-- A `FunctionFreeFact` is a `GeneralizedAtom` with constants. -/
abbrev FunctionFreeFact (sig : Signature) [DecidableEq sig.P] := GeneralizedAtom sig sig.C

namespace Fact

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The `constants` of a `Fact` are the constants of all terms. -/
@[expose]
def constants (f : Fact sig) : List sig.C := f.terms.flatMap GroundTerm.constants

/-- The `function_symbols` of a `Fact` are the function symbols of all terms. -/
@[expose]
def function_symbols (f : Fact sig) : List (SkolemFS sig) := f.terms.flatMap GroundTerm.functions

/-- A `Fact` is function free, if each term is a constant. -/
@[expose]
def isFunctionFree (f : Fact sig) : Prop := ∀ t, t ∈ f.terms -> ∃ c, t = GroundTerm.const c

/-- If a `Fact` `isFunctionFree`, then we can convert it to a `FunctionFreeFact`. -/
@[expose]
def toFunctionFreeFact (f : Fact sig) (isFunctionFree : f.isFunctionFree) : FunctionFreeFact sig := {
  predicate := f.predicate
  terms := f.terms.attach.map (fun t => t.val.toConst (isFunctionFree t.val t.property))
  arity_ok := by rw [List.length_map, List.length_attach, f.arity_ok]
}

end Fact

namespace FunctionFreeFact

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `FunctionFreeFact` can always be converted to a `Fact`. -/
@[expose]
def toFact (f : FunctionFreeFact sig) : Fact sig := {
  predicate := f.predicate,
  terms := f.terms.map GroundTerm.const,
  arity_ok := by rw [List.length_map, f.arity_ok]
}

/-- A `Fact` obtained from a `FunctionFreeFact` `isFunctionFree`. -/
@[grind <-]
theorem toFact_isFunctionFree (f : FunctionFreeFact sig) : f.toFact.isFunctionFree := by
  intro _
  unfold toFact
  grind

/-- Converting a `FunctionFreeFact` to a `Fact` and back yields the initial `FunctionFreeFact`. -/
@[simp, grind =]
theorem toFunctionFreeFact_after_toFact_is_id (f : FunctionFreeFact sig) : f.toFact.toFunctionFreeFact (f.toFact_isFunctionFree) = f := by
  unfold toFact
  unfold Fact.toFunctionFreeFact
  simp only
  rw [GeneralizedAtom.mk.injEq]
  constructor
  . simp
  . rw [List.map_attach_eq_pmap, List.pmap_map]
    simp

end FunctionFreeFact

namespace Fact

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- Converting a `Fact` to a `FunctionFreeFact` and back yields the initial `Fact`. -/
@[simp, grind =]
theorem toFact_after_toFunctionFreeFact_is_id (f : Fact sig) (isFunctionFree : f.isFunctionFree) : (f.toFunctionFreeFact isFunctionFree).toFact = f := by
  unfold toFunctionFreeFact
  unfold FunctionFreeFact.toFact
  simp only
  rw [GeneralizedAtom.mk.injEq]
  constructor
  . simp
  . rw [List.map_attach_eq_pmap]
    apply List.ext_get
    . simp
    . grind

end Fact

end FactAndFunctionFreeFact

section FactSet

/-!
## FactSet
-/

/-- A `FactSet` is plainly a `Set` of `Fact`s. -/
abbrev FactSet (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := Set (Fact sig)

namespace FactSet

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- The predicate symbols of a `FactSet` are the predicate symbols from all facts. -/
@[expose]
def predicates (fs : FactSet sig) : Set sig.P := fun p => ∃ f, f ∈ fs ∧ f.predicate = p

/-- The terms of a `FactSet` are the terms from all facts. -/
@[expose]
def terms (fs : FactSet sig) : Set (GroundTerm sig) := fun t => ∃ f, f ∈ fs ∧ t ∈ f.terms

/-- The constants of a `FactSet` are the constants from all facts. -/
@[expose]
def constants (fs : FactSet sig) : Set sig.C := fun c => ∃ f, f ∈ fs ∧ c ∈ f.constants

/-- The function symbols of a `FactSet` are the function symbols from all facts. -/
@[expose]
def function_symbols (fs : FactSet sig) : Set (SkolemFS sig) := fun func => ∃ f, f ∈ fs ∧ func ∈ f.function_symbols

/-- A `FactSet` is function free if all of its facts are. -/
@[expose]
def isFunctionFree (fs : FactSet sig) : Prop := ∀ f, f ∈ fs -> f.isFunctionFree

/-- When converting a list to a `FactSet`, the terms remain the same. -/
@[simp, grind =]
theorem mem_terms_toSet {l : List (Fact sig)} : ∀ t, t ∈ FactSet.terms (l.toSet) ↔ t ∈ l.flatMap GeneralizedAtom.terms := by
  intro t; rw [List.mem_flatMap]
  constructor <;> (intro ⟨f, f_mem, t_mem⟩; exists f; grind)

/-- The a `FactSet` is a subset of another, then their terms share this subset relation. -/
@[grind ->]
theorem terms_subset_of_subset {fs1 fs2 : FactSet sig} : fs1 ⊆ fs2 -> fs1.terms ⊆ fs2.terms := by
  intro sub t ⟨f, f_mem, t_mem⟩; exists f; exact ⟨sub _ f_mem, t_mem⟩

/-- The terms of the union of two `FactSet`s are the union of the terms of both sets. -/
@[simp, grind =]
theorem terms_union {fs1 fs2 : FactSet sig} : (fs1 ∪ fs2).terms = fs1.terms ∪ fs2.terms := by
  ext t
  constructor
  . rintro ⟨f, f_mem, t_mem⟩; cases f_mem with | inl f_mem => apply Or.inl; exists f | inr f_mem => apply Or.inr; exists f
  . intro t_mem; cases t_mem with
    | inl t_mem => rcases t_mem with ⟨f, f_mem, t_mem⟩; exists f; grind
    | inr t_mem => rcases t_mem with ⟨f, f_mem, t_mem⟩; exists f; grind

/-- If a `FactSet` is finite, so are its terms. -/
@[grind ->]
theorem terms_finite_of_finite (fs : FactSet sig) (finite : fs.finite) : fs.terms.finite := by
  rcases finite with ⟨l, nodup, finite⟩
  exists (l.map GeneralizedAtom.terms).flatten.eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro e
    constructor
    . intro in_l
      unfold FactSet.terms
      simp [List.mem_eraseDupsKeepRight, List.mem_flatten] at in_l
      rcases in_l with ⟨terms, ex_f, e_in_terms⟩
      rcases ex_f with ⟨f, f_in_l, terms_eq⟩
      exists f
      grind
    . intro in_fs
      unfold FactSet.terms at in_fs
      simp [List.mem_eraseDupsKeepRight, List.mem_flatten]
      rcases in_fs with ⟨f, f_in_fs, e_in_f⟩
      exists f.terms
      grind

/-- When converting a list to a `FactSet`, the constants remain the same. -/
@[simp, grind =]
theorem mem_constants_toSet {l : List (Fact sig)} : ∀ c, c ∈ FactSet.constants (l.toSet) ↔ c ∈ l.flatMap Fact.constants := by
  intro t; rw [List.mem_flatMap]
  constructor <;> (rintro ⟨f, f_mem, t_mem⟩; exists f; grind)

/-- The constants of the union of two `FactSet`s are the union of the constants of both sets. -/
@[simp, grind =]
theorem constants_union {fs1 fs2 : FactSet sig} : (fs1 ∪ fs2).constants = fs1.constants ∪ fs2.constants := by
  -- NOTE: same proof as terms_union
  ext t
  constructor
  . rintro ⟨f, f_mem, t_mem⟩; cases f_mem with | inl f_mem => apply Or.inl; exists f | inr f_mem => apply Or.inr; exists f
  . intro t_mem; cases t_mem with
    | inl t_mem => rcases t_mem with ⟨f, f_mem, t_mem⟩; exists f; grind
    | inr t_mem => rcases t_mem with ⟨f, f_mem, t_mem⟩; exists f; grind

/-- If a `FactSet` is finite, so are its constants. -/
@[grind ->]
theorem constants_finite_of_finite (fs : FactSet sig) (fin : fs.finite) : fs.constants.finite := by
  rcases fin with ⟨l, _, l_eq⟩
  exists (l.flatMap Fact.constants).eraseDupsKeepRight
  constructor
  . apply List.nodup_eraseDupsKeepRight
  . intro c
    rw [List.mem_eraseDupsKeepRight]
    rw [List.mem_flatMap]
    unfold constants
    constructor
    . intro h
      rcases h with ⟨f, f_mem, c_mem⟩
      rw [l_eq] at f_mem
      exists f
    . intro h
      rcases h with ⟨f, f_mem, c_mem⟩
      rw [← l_eq] at f_mem
      exists f

/-- A `FactSet` is finite if both its predicates and terms are. This holds since the fact set must be a subset of all facts that can possibly be constructed using the prediactes and terms available. This overapproximation is easily shown to be finite. -/
@[grind ->]
theorem finite_of_preds_finite_of_terms_finite (fs : FactSet sig) : fs.predicates.finite -> fs.terms.finite -> fs.finite := by
  intro preds_fin terms_fin
  rcases preds_fin with ⟨preds, _, preds_eq⟩
  rcases terms_fin with ⟨terms, _, terms_eq⟩

  let overapproximation : FactSet sig := fun f => f.predicate ∈ fs.predicates ∧ (∀ t, t ∈ f.terms -> t ∈ fs.terms)
  have overapproximation_fin : overapproximation.finite := by
    exists (preds.flatMap (fun p =>
      (all_lists_of_length terms (sig.arity p)).attach.map (fun ⟨ts, mem⟩ =>
        {
          predicate := p
          terms := ts
          arity_ok := ((mem_all_lists_of_length terms (sig.arity p) ts).mp mem).left
        }
      )
    )).eraseDupsKeepRight

    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro f
      rw [List.mem_eraseDupsKeepRight]
      simp only [List.mem_flatMap, List.mem_map, List.mem_attach, true_and, Subtype.exists]
      constructor
      . intro _; constructor <;> grind
      . intro h
        rcases h with ⟨pred_mem, ts_mem⟩
        exists f.predicate
        constructor
        . rw [preds_eq]; exact pred_mem
        . exists f.terms
          exists (by
            rw [mem_all_lists_of_length]
            constructor
            . exact f.arity_ok
            . intro t t_mem; rw [terms_eq]; apply ts_mem; exact t_mem
          )

  apply Set.finite_of_subset_finite overapproximation_fin
  intro f f_mem
  constructor
  . exists f
  . intro t t_mem
    exists f

/-- For a list of terms in a given `FactSet`, we can find a list of facts in the fact set such that all the terms from the list occur in the list of facts. -/
theorem list_of_facts_for_list_of_terms {ts : List (GroundTerm sig)} {fs : FactSet sig} (ts_sub : ts.toSet ⊆ fs.terms) :
    ∃ (l : List (Fact sig)), l.toSet ⊆ fs ∧ ts ⊆ l.flatMap GeneralizedAtom.terms := by
  induction ts with
  | nil => exists []; constructor; intro _ mem; simp [List.mem_toSet] at mem; simp
  | cons t ts ih =>
    rcases (ts_sub t (by simp [List.mem_toSet])) with ⟨f, f_mem, t_mem⟩
    rcases ih (by intro _ mem; rw [List.mem_toSet] at mem; apply ts_sub; simp [List.mem_toSet, mem]) with ⟨l, l_sub, ts_sub⟩
    exists (f :: l); constructor
    . intro _ mem; rw [List.mem_toSet, List.mem_cons] at mem
      cases mem with
      | inl mem => rw [mem]; exact f_mem
      | inr mem => apply l_sub; rw [List.mem_toSet]; exact mem
    . grind

end FactSet

end FactSet

section Database

/-!
## Database
-/

/-- A `Database` is a finite set of `FunctionFreeFact`s. -/
abbrev Database (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] := { X : Set (FunctionFreeFact sig) // X.finite }

namespace Database

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- Any `Database` can trivially be converted to a finite and function free `FactSet`. -/
def toFactSet (db : Database sig) : { fs : FactSet sig // fs.finite ∧ fs.isFunctionFree } := ⟨
  (fun f => ∃ f', f' ∈ db.val ∧ f'.toFact = f),
  (by
    rcases db.property with ⟨l, _, l_eq⟩
    exists (l.map FunctionFreeFact.toFact).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro f
      rw [List.mem_eraseDupsKeepRight]
      rw [List.mem_map]
      simp only [l_eq]
      rfl
  ),
  (by
    intro f f_mem
    rcases f_mem with ⟨_, _, f_eq⟩
    rw [← f_eq]
    apply FunctionFreeFact.toFact_isFunctionFree
  ),
⟩

/-- Each `Database` has a finite set of constants. -/
def constants (db : Database sig) : { C : Set sig.C // C.finite } := ⟨
  fun c => ∃ (f : FunctionFreeFact sig), f ∈ db.val ∧ c ∈ f.terms,
  by
    rcases db.property with ⟨l, _, l_eq⟩
    exists (l.flatMap (fun f => f.terms)).eraseDupsKeepRight
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro c
      rw [List.mem_eraseDupsKeepRight, List.mem_flatMap]
      constructor
      . intro h
        rcases h with ⟨f, f_mem, c_mem⟩
        exists f
        constructor
        . rw [l_eq] at f_mem
          exact f_mem
        . exact c_mem
      . intro h
        rcases h with ⟨f, f_mem, c_mem⟩
        exists f
        constructor
        . rw [← l_eq] at f_mem
          exact f_mem
        . exact c_mem
⟩

/-- When converting a `Database` to a `FactSet`, the constants remain the same. -/
@[simp, grind =]
theorem toFactSet_constants_same (db : Database sig) : db.toFactSet.val.constants = db.constants.val := by
  unfold toFactSet
  unfold constants
  unfold FactSet.constants
  simp only
  ext c
  constructor
  . intro h
    rcases h with ⟨f, f_mem, c_mem⟩
    unfold Fact.constants at c_mem
    rcases f_mem with ⟨f', f'_mem, f_eq⟩
    unfold FunctionFreeFact.toFact at f_eq
    exists f'
    grind
  . intro h
    rcases h with ⟨f, f_mem, c_mem⟩
    exists f.toFact
    constructor
    . exists f
    . unfold FunctionFreeFact.toFact
      unfold Fact.constants
      grind

end Database

end Database

section KnowledgeBase

/-!
## KnowledgeBase
-/

/-- A `KnowledgeBase` is a pair of a `Database` and a `RuleSet`. Note that usually the `RuleSet` is enforced to be finite but we only restrict this in places where we really need this. -/
structure KnowledgeBase (sig : Signature) [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V] where
  db : Database sig
  rules : RuleSet sig

namespace KnowledgeBase

variable {sig : Signature} [DecidableEq sig.P] [DecidableEq sig.C] [DecidableEq sig.V]

/-- A `KnowledgeBase` is determinstic if the underlying `RuleSet` is. -/
@[expose]
def isDeterministic (kb : KnowledgeBase sig) : Prop := kb.rules.isDeterministic

end KnowledgeBase

end KnowledgeBase

