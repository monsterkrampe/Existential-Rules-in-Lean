/-
Copyright 2026 Henrik Tscherny, Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

import ExistentialRules.ChaseSequence.CoreChase.Basic
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseBranch
import ExistentialRules.ChaseSequence.CoreChase.CoreChaseNode
import ExistentialRules.ChaseSequence.CoreChase.TerminatesIfFinUnivModelExists
import ExistentialRules.ChaseSequence.CoreChase.Universality

/-!

# Core Chase

The files in this directory contain an attempt of formalizing the core chase and more specifically Theorem 7 from [ChaseRevisited].

**Basic code contributions were made by Henrik in his Diploma thesis covering preliminary definitions and a few proof attemps. Some cleanups have happened already but the contents are still in an early stage of development. The code will be extended in the future and likely be further reworked in the process.**

-/

