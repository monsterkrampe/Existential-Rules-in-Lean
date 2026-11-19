/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import ExistentialRules.ChaseSequence.Nontermination.BirthFacts
import ExistentialRules.ChaseSequence.Nontermination.CondenseGenerator
import ExistentialRules.ChaseSequence.Nontermination.CyclicityPrefix
import ExistentialRules.ChaseSequence.Nontermination.CyclicitySequence
import ExistentialRules.ChaseSequence.Nontermination.HeadChoice
import ExistentialRules.ChaseSequence.Nontermination.RepeatableUnblockability
import ExistentialRules.ChaseSequence.Nontermination.RepeatingConstantMappings
import ExistentialRules.ChaseSequence.Nontermination.ReversibleConstantMappings
import ExistentialRules.ChaseSequence.Nontermination.SparseSubderivationGenerator
import ExistentialRules.ChaseSequence.Nontermination.TermSkeleton
import ExistentialRules.ChaseSequence.Nontermination.Unblockability

/-!
# RPC-like Non-Termination

We are going to formalize sufficient conditions for chase non-termination.
Mainly, we will introduce the necessary machinery from Restricted Prefix Cyclicity (RPC) [RPC]
but we also aim to generalize this to capture (Disjunctive) Model-Faithful Cyclicity ((D)MFC) [DMFA] [RMFA] at the same time.

THIS IS STILL WORK IN PROGRESS. From [RPC], we have formalized Sections 3 and 5 but Sections 4 and 6 still remain.
-/

