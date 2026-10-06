import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement
import QCryptLean.Math.Concentration.BinomialPassSum

/-!
# The Bell-basis POVM and its Bell-Born weight

The four-outcome Bell-basis POVM `{|β_k⟩⟨β_k|}` and its per-outcome Born weight, together with
the Bell diagonalization of the phase-flip error projector.  Because `Z⊗Z` (bit) and `X⊗X`
(phase) commute, both the bit-error and the phase-error statistic can in principle be decoded
from a single Bell-basis outcome; this is Renner's single POVM `cM` with a multi-statistic
outcome alphabet (Renner 2005, `arXiv:quant-ph/0512258v2`, §6.5, `pr:PE` / `lem:PEsec`).

## The decisive index ordering

`bb84BellState := ![bellState00, bellState01, bellState10, bellState11]` matches the `states`
vector of `Quantum.Basis.BellStates.bellStates_orthonormal` exactly.  With
`bb84BellPOVM k = |β_k⟩⟨β_k|`, the BB84 phase-flip error projector is a diagonal reordering of
the Bell projectors: `phaseFlipProjector = bb84BellPOVM 2 + bb84BellPOVM 3` (β10, β11).

## Main definitions and results

* `bb84BellState`, `bb84BellPOVM` — the Bell vectors and the four-outcome Bell POVM.
* `bb84BellPOVM_isProjection`, `bb84BellPOVM_isHermitian`, `bb84BellPOVM_complete` — the Bell
  POVM elements are projectors, Hermitian, and sum to the identity.
* `bb84BellPOVM_phase_eq_phaseFlipProjector` — the Bell diagonalization of the phase-flip
  error projector.
* `bb84BellBorn` — the per-outcome Bell-Born weight `⟨β_k|σ|β_k⟩`.
* `bb84BellBorn_nonneg`, `bb84BellBorn_sum` — the Bell-Born weights are nonnegative and sum to
  one.
* `bb84BellBorn_phase_rate` — the phase Bell-Born marginal equals the phase-flip error rate.

## References

Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5 / `pr:PE` + `lem:PEsec`; Nahar, Tupkary, Zhao,
Lütkenhaus, Tan (2024), `arXiv:2403.11851`, Lemma 9 Eq. 44.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Quantum.Basis.BellStates InfoTheory.DeFinetti MeasureTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

/-!
## The Bell POVM
-/

/-- The four Bell vectors, indexed to match `Quantum.Basis.BellStates.bellStates_orthonormal`:
`bb84BellState = ![|β₀₀⟩, |β₀₁⟩, |β₁₀⟩, |β₁₁⟩]`. -/
def bb84BellState : Fin signalDim → Ket signalDim :=
  ![bellState00, bellState01, bellState10, bellState11]

/-- The four-outcome **Bell-basis POVM**: `bb84BellPOVM k = |β_k⟩⟨β_k|`. -/
def bb84BellPOVM : Fin signalDim → Op signalDim :=
  fun k => bb84BellState k * (bb84BellState k).dag

/-- Each Bell vector is normalized: `⟨β_k|β_k⟩ = 1`. -/
theorem bb84BellState_normalized (k : Fin signalDim) :
    (bb84BellState k).dag * bb84BellState k = 1 := by
  have h := bellStates_orthonormal k k
  simpa [bb84BellState] using h

/-- Each `bb84BellPOVM k` is an idempotent projector. -/
theorem bb84BellPOVM_isProjection (k : Fin signalDim) :
    bb84BellPOVM k * bb84BellPOVM k = bb84BellPOVM k :=
  ketbra_idempotent (bb84BellState k) (bb84BellState_normalized k)

/-- Each `bb84BellPOVM k` is Hermitian. -/
theorem bb84BellPOVM_isHermitian (k : Fin signalDim) :
    (bb84BellPOVM k).IsHermitian :=
  ketbra_hermitian (bb84BellState k)

/-- The Bell projectors sum to the identity. -/
theorem bb84BellPOVM_complete :
    ∑ k : Fin signalDim, bb84BellPOVM k = (1 : Op signalDim) := by
  rw [Fin.sum_univ_four]
  change bellState00 * bellState00.dag + bellState01 * bellState01.dag +
      bellState10 * bellState10.dag + bellState11 * bellState11.dag = 1
  exact bell_projectors_sum_identity

/-!
## Bell diagonalization of the BB84 error projectors
-/

/-- **Bell diagonalization (phase).** `phaseFlipProjector = |β₁₀⟩⟨β₁₀| + |β₁₁⟩⟨β₁₁|`, i.e. the
Bell outcomes carrying a phase error are `{2, 3}`.  Immediate from the definition of
`phaseFlipProjector` (`Model.lean`). -/
theorem bb84BellPOVM_phase_eq_phaseFlipProjector :
    bb84BellPOVM 2 + bb84BellPOVM 3 = QKD.BB84.Model.phaseFlipProjector := by
  change bellState10 * bellState10.dag + bellState11 * bellState11.dag =
    QKD.BB84.Model.phaseFlipProjector
  rfl

/-!
## The Bell-Born weight and its marginal-rate identities
-/

/-- The **Bell-Born weight** of outcome `k` on the component `σ`: `⟨β_k|σ|β_k⟩ = Tr(|β_k⟩⟨β_k| σ)`.
Explicit; no `Classical.choose`. -/
def bb84BellBorn (σ : DensityOp signalDim) (k : Fin signalDim) : ℝ :=
  (bb84BellPOVM k * σ.toOp).trace.re

/-- Each Bell-Born weight is nonnegative (trace of a projector against a PSD operator). -/
theorem bb84BellBorn_nonneg (σ : DensityOp signalDim) (k : Fin signalDim) :
    0 ≤ bb84BellBorn σ k :=
  QKD.BB84.Model.trace_projector_psd_nonneg (bb84BellPOVM k) σ.toPosSemidefOp
    (bb84BellPOVM_isProjection k) (bb84BellPOVM_isHermitian k)

/-- The Bell-Born weights sum to one (Bell completeness + `Tr σ = 1`). -/
theorem bb84BellBorn_sum (σ : DensityOp signalDim) :
    (∑ k : Fin signalDim, bb84BellBorn σ k) = 1 := by
  unfold bb84BellBorn
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, bb84BellPOVM_complete,
      Matrix.one_mul, σ.trace_one]
  norm_num

/-- The phase Bell-Born marginal `⟨β₂|σ|β₂⟩ + ⟨β₃|σ|β₃⟩` equals the phase-flip error rate. -/
theorem bb84BellBorn_phase_rate (σ : DensityOp signalDim) :
    bb84BellBorn σ 2 + bb84BellBorn σ 3 = QKD.BB84.Model.phaseFlipErrorRate_single σ := by
  unfold bb84BellBorn QKD.BB84.Model.phaseFlipErrorRate_single
  rw [← bb84BellPOVM_phase_eq_phaseFlipProjector, Matrix.add_mul, Matrix.trace_add, Complex.add_re]

end QKD.BB84.Model

end
