import QCryptLean.QKD.BB84.Engine.PerRound.SecondOrderPenalty
import QCryptLean.QKD.BB84.Engine.Budgets.SecondOrderSharpPenalty
import QCryptLean.InfoTheory.Renyi.DivergenceVariance

/-!
# The `n_copies`-fold AEP lift at the Cor IV.2 sharp-variance-cap penalty

The scalar penalty and its elementary properties (`secondOrderSharpRegime`,
`secondOrderSharpBeta`, `bb84SecondOrderSharpAlpha`, `finiteSizePenaltySecondOrderSharp` and its
closed form) have no quantum content and live in `Engine/Budgets/SecondOrderSharpPenalty.lean`;
this module has the one quantum theorem that pays that penalty: Dupuis–Fawzi's Corollary IV.2
finite-size AEP penalty for the smooth min-entropy of an IID tensor power, charged at the variance
cap `condDivergenceVariance_le_logb_one_add_sqrt_two` (`V(X|B) ≤ log₂²(1+√2) ≈ 1.6168` at
`d_A = 2`), the sharp cap recorded as `bb84SharpVarianceCap`.

With `B := log₂(2/ε²)`, `β := secondOrderSharpBeta bb84SharpVarianceCap m ε` and `α := 1 + β`,
the chain is

```
Hmin^ε(ρ^{⊗m} ‖ ρ_B^{⊗m})
  ≥ m·H'_α(X|B)_ρ − B/(α−1)
  ≥ m·(H − ((α−1)·log 2/2)·V − (α−1)²·K) − B/β
  ≥ m·H − (bb84SharpVarianceCap/2)·log 2·m·β − K_β·m·β² − B/β
  = m·H − finiteSizePenaltySecondOrderSharp bb84SharpVarianceCap m ε.
```

## Main results

- `QKD.BB84.Engine.bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharpAt`: the `n_copies`-fold
  smooth AEP lift at the Cor IV.2 penalty charged at a free Rényi offset `β ∈ (0, 1)`
  (Dupuis–Fawzi Cor. IV.2 holds at every such `β`).
- `QKD.BB84.Engine.bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharp`: the same lift at the
  clamped optimiser `β = secondOrderSharpBeta bb84SharpVarianceCap n_copies ε`, as a corollary.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`:784`), `K(α)` (`:789`), `\label{eq_eatblock}` (`:1047`), `\label{eq_eathmin_halpha}` (`:1053`),
`\label{eq_alphachoiceext}` (`:1061`); the variance bound replaced by the sharp cap is
`\label{lem:divergence-variance-general-bounds}` (`:394`) with `\label{eq:bound_dalpha}`
(`:398`–`:399`); Tomamichel 2015 (`arXiv:1504.00233`) Prop. 6.5 (`calculus.tex:1025`
`\label{pr:min-renyi}`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open InfoTheory.Renyi
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-- **The `n_copies`-fold smooth AEP lift at the sharp-cap Cor IV.2 penalty, at a free Rényi
offset `β`.**

`ofReal (n_K·H(Z_A|E)_σ − finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap n_K ε β)
≤ Hmin^ε(ρ_σ^{⊗n_K} ‖ ρ_E^{⊗n_K})` for every admissible offset `β ∈ (0, 1)`: the
Dupuis–Fawzi Corollary IV.2 bound holds at every such `β`, not only at the clamped optimiser
`secondOrderSharpBeta`.  Via the Rényi route: the smooth min-entropy of the tensor power is bounded
below through the Petz-down conditional Rényi entropy at order `α = 1 + β`, which Corollary IV.2
relates to the conditional von Neumann entropy using the sharp variance cap
`condDivergenceVariance_le_logb_one_add_sqrt_two` and the `K(1 + β) ≤ K_β` bound.

Reference: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`:784`), `\label{eq_eatblock}` (`:1047`), `\label{eq_eathmin_halpha}` (`:1053`); Tomamichel 2015
(`arXiv:1504.00233`) Prop. 6.5 (`calculus.tex:1025`). -/
theorem bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharpAt (σ : DensityOp signalDim)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (signalDim ^ n_copies)] (ε β : ℝ)
    (hε : 0 < ε) (hβpos : 0 < β) (hβ1 : β < 1) :
    ENNReal.ofReal ((n_copies : ℝ) *
          ((vonNeumannEntropy
              ((bb84ComponentAliceZCQState σ).toJointDensityOp (bb84ComponentAliceZCQState_norm σ))
            - vonNeumannEntropy
              ((bb84ComponentAliceZCQState σ).quantumMarginalDensityOp
                (bb84ComponentAliceZCQState_norm σ))) / Real.log 2)
        - finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap n_copies ε β) ≤
      smoothMinEntropy ε (CQState.tensorPower (bb84ComponentAliceZCQState σ) n_copies)
        (SubDensityOp.tensorPower
          (DensityOp.toSubDensityOp
            ((bb84ComponentAliceZCQState σ).quantumMarginalDensityOp
              (bb84ComponentAliceZCQState_norm σ))) n_copies) := by
  haveI hd4 : NeZero signalDim := ⟨by norm_num [signalDim]⟩
  haveI hne2 : Nonempty (Fin 2) := ⟨0⟩
  haveI hnefun : Nonempty (Fin n_copies → Fin 2) := ⟨fun _ => 0⟩
  set ρ : CQState (Fin 2) signalDim := bb84ComponentAliceZCQState σ with hρdef
  have hnorm : ∑ z : Fin 2, (ρ.stateMap z).trace = 1 := bb84ComponentAliceZCQState_norm σ
  -- the Rényi order is `1 + β`, directly (no detour through the clamped optimiser)
  set α : ℝ := 1 + β with hαdef
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hα1 : 1 < α := by rw [hαdef]; linarith
  have hα2' : α < 2 := by rw [hαdef]; linarith
  have hαβ : α - 1 = β := by rw [hαdef]; ring
  have hcard : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  -- rung 4: the smooth min-entropy endpoint at `α`
  have hendpoint := InfoTheory.Renyi.smoothMinEntropy_tensorPower_ge_condPetzRenyiDown_sub
    α hα1 ε hε ρ hnorm n_copies
  rw [hαβ] at hendpoint
  -- Corollary IV.2, per round
  have hcor := condPetzRenyiDown_ge_condVonNeumann_sub α hα1 hα2' ρ hnorm
  -- the two constant caps, the first at the SHARP value `log₂²(1+√2)`
  have hV : condDivergenceVariance ρ ≤ bb84SharpVarianceCap :=
    condDivergenceVariance_le_logb_one_add_sqrt_two ρ hnorm hcard
  have hK : secondOrderK α ρ ≤ binarySecondOrderRemainderBound β :=
    secondOrderK_le_binarySecondOrderRemainderBound β hβpos hβ1 ρ hnorm hcard
  have hcoef : (0 : ℝ) ≤ (α - 1) * Real.log 2 / 2 := by rw [hαβ]; positivity
  have hVstep : ((α - 1) * Real.log 2 / 2) * condDivergenceVariance ρ
      ≤ ((α - 1) * Real.log 2 / 2) * bb84SharpVarianceCap := mul_le_mul_of_nonneg_left hV hcoef
  have hKstep : (α - 1) ^ 2 * secondOrderK α ρ ≤ (α - 1) ^ 2 * binarySecondOrderRemainderBound β :=
    mul_le_mul_of_nonneg_left hK (sq_nonneg _)
  -- the per-round floor
  have hround : condVonNeumann ρ - bb84SharpVarianceCap / 2 * Real.log 2 * β
      - binarySecondOrderRemainderBound β * β ^ 2
      ≤ condPetzRenyiDown α ρ := by
    have h1 : ((α - 1) * Real.log 2 / 2) * bb84SharpVarianceCap
        = bb84SharpVarianceCap / 2 * Real.log 2 * β := by
      rw [hαβ]; ring
    have h2 : (α - 1) ^ 2 * binarySecondOrderRemainderBound β
        = binarySecondOrderRemainderBound β * β ^ 2 := by rw [hαβ]; ring
    linarith only [hcor, hVstep, hKstep, h1, h2]
  -- scale by `n_copies` and subtract the smoothing charge
  have hmnn : (0 : ℝ) ≤ (n_copies : ℝ) := Nat.cast_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hround hmnn
  have hpen : finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap n_copies ε β
      = bb84SharpVarianceCap / 2 * Real.log 2 * (n_copies : ℝ) * β
        + binarySecondOrderRemainderBound β * (n_copies : ℝ) * β ^ 2
        + Real.logb 2 (2 / ε ^ 2) / β := by
    rw [finiteSizePenaltySecondOrderSharpAt]
  -- rewrite `H` into the Devetak–Winter form
  have hbridge : condVonNeumann ρ
      = (vonNeumannEntropy
            ((bb84ComponentAliceZCQState σ).toJointDensityOp (bb84ComponentAliceZCQState_norm σ))
          - vonNeumannEntropy
            ((bb84ComponentAliceZCQState σ).quantumMarginalDensityOp
              (bb84ComponentAliceZCQState_norm σ))) / Real.log 2 := by
    rw [hρdef, condVonNeumann_bb84ComponentAliceZCQState_eq_rate σ, bb84ComponentAliceZRate]
  rw [← hbridge, hpen]
  refine (ENNReal.ofReal_le_ofReal ?_).trans hendpoint
  calc (n_copies : ℝ) * condVonNeumann ρ
        - (bb84SharpVarianceCap / 2 * Real.log 2 * n_copies * β
          + binarySecondOrderRemainderBound β * n_copies * β ^ 2
          + Real.logb 2 (2 / ε ^ 2) / β)
      = n_copies * (condVonNeumann ρ - bb84SharpVarianceCap / 2 * Real.log 2 * β
          - binarySecondOrderRemainderBound β * β ^ 2) - Real.logb 2 (2 / ε ^ 2) / β := by ring
    _ ≤ n_copies * condPetzRenyiDown α ρ - Real.logb 2 (2 / ε ^ 2) / β :=
        sub_le_sub_right hscaled _

/-- **The `n_copies`-fold smooth AEP lift at the sharp-cap Cor IV.2 penalty** (at the clamped
optimiser `β⋆ = secondOrderSharpBeta bb84SharpVarianceCap n_K ε`), as a corollary of the free-β
version, with the completed signed floor cast by `ENNReal.ofReal`. Positivity of `β⋆` uses
`[NeZero n_K]` and `ε < 1`. -/
theorem bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharp (σ : DensityOp signalDim)
    (n_copies : ℕ) [NeZero n_copies] [NeZero (signalDim ^ n_copies)] (ε : ℝ)
    (hε : 0 < ε) (hε_lt : ε < 1) :
    ENNReal.ofReal ((n_copies : ℝ) *
          ((vonNeumannEntropy
              ((bb84ComponentAliceZCQState σ).toJointDensityOp (bb84ComponentAliceZCQState_norm σ))
            - vonNeumannEntropy
              ((bb84ComponentAliceZCQState σ).quantumMarginalDensityOp
                (bb84ComponentAliceZCQState_norm σ))) / Real.log 2)
        - finiteSizePenaltySecondOrderSharp bb84SharpVarianceCap n_copies ε) ≤
      smoothMinEntropy ε (CQState.tensorPower (bb84ComponentAliceZCQState σ) n_copies)
        (SubDensityOp.tensorPower
          (DensityOp.toSubDensityOp
            ((bb84ComponentAliceZCQState σ).quantumMarginalDensityOp
              (bb84ComponentAliceZCQState_norm σ))) n_copies) := by
  have hβpos : 0 < secondOrderSharpBeta bb84SharpVarianceCap n_copies ε :=
    secondOrderSharpBeta_pos bb84SharpVarianceCap bb84SharpVarianceCap_pos n_copies ε hε hε_lt
  have h := bb84_perSigma_smoothHmin_ge_nfold_DW_secondOrderSharpAt σ n_copies ε
    (secondOrderSharpBeta bb84SharpVarianceCap n_copies ε) hε hβpos
    ((secondOrderSharpBeta_le_one_sixteenth bb84SharpVarianceCap n_copies ε).trans_lt (by norm_num))
  rwa [← finiteSizePenaltySecondOrderSharp_eq] at h

end QKD.BB84.Engine

end -- noncomputable section
