# Existential Rules in Lean

This is a collection of some definitions, results, and proofs around
Existential Rules (aka. [Tuple-Generating Dependencies](https://en.wikipedia.org/wiki/Tuple-generating_dependency)) with disjunctions
and the Chase algorithm
written up in LEAN 4.
Mostly, the formalizations are related to my own research.

Broadly speaking, the chase takes a set of rules and an initial of facts (called database) and computes further facts to satisfy all the rules in the most general way.
This might require infinitely many chase steps. In the presence of disjunctions, the chase is branching out to produce a set of facts sets to capture all "possible worlds".

More specifically, this repo contains a generalized formalization of the chase on disjunctive existential rules in `ExistentialRules/ChaseSequence`.
The definition captures both the skolem and restricted chase at the same time through a generic `ObsoletenessCondition`.
The definition of the chase for disjunctive rules involves (possibly) infinite trees of finite degree formalized [here](https://github.com/monsterkrampe/Possibly-Infinite-Trees).

**Key results that are already formalized include the following:**
- The result of the chase is a universal model set. That is, (1) each fact set in the result indeed satisfies all rules and (2) for any given model `M` of the rule set and the database, we can find a fact set in the chase result that can be homomorphically embedded into `M`.
- A chase sequence without alternative matches on rules without disjunctions yields a universal model that is a core. (Section 3 of [this paper](https://iccl.inf.tu-dresden.de/web/Inproceedings3249))
- If a rule set is model-faithful acyclic (MFA), then every chase sequence on every database terminates. (The formalization is inspired by Section 3.1 in [this paper](https://iccl.inf.tu-dresden.de/web/Inproceedings3348); MFA was originally introduced [here](https://arxiv.org/abs/1406.4110).)

## Notes on Setup

Using [`elan`](https://github.com/leanprover/elan) / `lake`:

- Install `elan`, e.g. via `nix-shell -p elan` or simply `nix develop` if you are using nix.
- Run `lake build` to build the project. If the build is successful, the proofs are correct :tada:

