/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Math.ClassicalEntropy.Entropy
import Mathlib.Analysis.Real.Sqrt

/-!
# The basic BB84 secrecy budget

The agree-block budget is `PA + 2 ε_AEP + 2 √(2E)`, with
`PA = ½ exp(-(n - m)/4 * (log 2 - h(Q + 2δ)))`. The verification failure probability is charged
separately at the channel level. The verification tag's entropy leakage stays in the key rate.

Reference: Nahar et al. 2024, arXiv:2403.11851, `eq:condLHL`, `eq:condsecrecy`, Appendix B.
-/

open Math.ClassicalEntropy

noncomputable section

namespace QKD.BB84.Engine

/-- The collective secrecy budget `PA + 2 ε_AEP + 2 √(2E)` at `n - m` key rounds.
The privacy-amplification term is `½ exp(-(n - m)/4 * (log 2 - h(Q + 2δ)))`. -/
noncomputable def bb84CKRPostselectionInnerBudgetOfTail
    (E : ℝ) (n m : ℕ) (Q δ ε_AEP : ℝ) : ℝ :=
  2 * Real.sqrt (2 * E) +
    2 * ε_AEP +
    (1 / 2) * Real.exp (-(bb84KeyRoundCount n m : ℝ) / 4 *
      (Real.log 2 - binaryEntropy (Q + 2 * δ)))

/-- The normalized diamond budget: direct correctness `2^(-ℓEV)` plus
`C(n+15,15)` times `bb84CKRPostselectionInnerBudgetOfTail E n m Q δ ε_AEP`.
The postselection factor uses all `n` rounds; the key-dependent terms use `n - m`. -/
noncomputable def standardBudgetOfTail (E : ℝ) (n m ℓEV : ℕ) (Q δ ε_AEP : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(ℓEV : ℝ)) +
    (Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1) : ℝ) *
      bb84CKRPostselectionInnerBudgetOfTail E n m Q δ ε_AEP


end QKD.BB84.Engine

end
