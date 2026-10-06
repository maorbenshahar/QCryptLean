/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBennett
import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.BlockRefRegularization
import QCryptLean.QKD.BB84.Engine.InnerBudget.InnerBudgetPinned
import QCryptLean.Quantum.Channels.CPTP.DiamondNormAncilla

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-!
# The tightened collective inner budget at an abstract accept tail

The tightened-`εPA` CKR collective inner budget, parametrised by an abstract accept-tail scale `E`
in place of a closed accept-tail expression, so that a sharper accept tail can be substituted
without re-deriving the budget.

## Main definitions

- `QKD.BB84.Engine.improvedInnerBudgetOfTail`: the tightened collective inner budget at an
  abstract accept-tail scale `E`.

Reference: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) `\label{eq:condLHL}`
(`main.tex:462`–`:467`, `εPA` free), `\label{sec:plots}` (`main.tex:968`, the `εPA = εAT` choice at
`main.tex:976`), App. B; Renner 2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}`
(`main.tex:4561`), §5, §6.5; Christandl–König–Renner 2009 (`arXiv:0809.3019`).
-/

/-- **The tightened collective inner budget at an abstract accept-tail scale `E`.**

```
improvedInnerBudgetOfTail E = exp(−n·δ²/2) + 2·(ε_AEP + √(2·E))
```

Only the FvdG accept term `2·√(2·E)` depends on `E`. The
privacy-amplification term `exp(−n·δ²/2)` does not: it is `εPA`, funded by the tightened key-rate
condition, independent of the accept tail.

`Q` does not occur: relaxing `εPA` to the accept-tail scale removes the only `Q`-dependent term of
the tightened inner budget.

`E` is unconstrained here.  The constraints the chain places on it, `0 ≤ E` and `E < 1/8`, are
hypotheses of the theorems that consume the accept-tail interface, not of this scalar.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`–`:467`),
`\label{sec:plots}` (`main.tex:968`, `:976`); Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
noncomputable def improvedInnerBudgetOfTail
    (E : ℝ) (n : ℕ) (δ ε_AEP : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * δ ^ 2 / 2) + 2 * (ε_AEP + Real.sqrt (2 * E))

end QKD.BB84.Engine

end -- noncomputable section
