import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.FubiniStudyTriangle
import QCryptLean.InfoTheory.DistanceBounds.FuchsVanDeGraaf.Basic

/-!
# Fuchs–van de Graaf for pure states

Pure-state case of the mixed-state Fuchs–van de Graaf inequality, leaf for
`traceDistance_le_sqrt_one_sub_fidelitySq_normalized` in
`InfoTheory/SmoothMinEntropy/PurifiedDistance.lean`.

For normalized kets `|ψ⟩, |φ⟩` on `Fin n`, the trace distance of their pure
density operators equals `√(1 - ‖⟨ψ|φ⟩‖²)`:

  `D(|ψ⟩⟨ψ|, |φ⟩⟨φ|) = √(1 - ‖ψ.dag * φ‖²)`.

## Proof strategy

For two unit vectors `u, v ∈ ℂⁿ`, the difference of their rank-1 projectors
has eigenvalues `±√(1 - |⟨u,v⟩|²)` (on the 2-dimensional span) and `0` on the
orthogonal complement. Therefore `‖P_u - P_v‖₁ = 2√(1 - |⟨u,v⟩|²)` and
`D(P_u, P_v) = √(1 - |⟨u,v⟩|²)`.

## Main statement
- `traceDistance_pure_eq_sqrt_one_sub_abs_inner_sq` — the equality above.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder

noncomputable section

namespace Quantum.Metrics

/-- **Pure-state Fuchs–van de Graaf equality.**

For normalized kets `|ψ⟩, |φ⟩` (i.e. `ψ.dag * ψ = 1`, `φ.dag * φ = 1`), the
trace distance between their pure-state density operators equals
`√(1 - ‖⟨ψ|φ⟩‖²)`.

*Strategy.* The difference `|ψ⟩⟨ψ| - |φ⟩⟨φ|` is Hermitian with spectrum
`{+√(1-s), -√(1-s), 0, …, 0}` where `s = ‖⟨ψ|φ⟩‖²` (the nonzero eigenvalues
live on the 2-plane `span{ψ, φ}`). Hence `‖·‖₁ = 2√(1-s)`, and the trace
distance (half the trace norm) is `√(1-s)`. -/
theorem traceDistance_pure_eq_sqrt_one_sub_abs_inner_sq
    {n : ℕ} [NeZero n] (ψ φ : Ket n)
    (hψ : ψ.dag * ψ = 1) (hφ : φ.dag * φ = 1) :
    Quantum.Metrics.traceDistance
        (DensityOp.fromPure ψ hψ).toOp
        (DensityOp.fromPure φ hφ).toOp
      = Real.sqrt (1 - ‖(ψ.dag * φ : ℂ)‖ ^ 2) := by
  -- Start from the squared pure-pure identity: D² = 1 - F²(ψ,φ).
  have h_sq :=
    traceDistance_sq_eq_one_sub_fidelityPureSq_pure_pure ψ hψ φ hφ
  -- Pure fidelity equals |⟨ψ|φ⟩|.
  have h_fid :=
    InfoTheory.SmoothMinEntropy.fidelity_pure_eq_abs_inner ψ φ hψ hφ
  -- Unfold `fidelitySq` and substitute the pure-fidelity identity.
  have h_fidsq :
      DensityOp.fidelitySq (DensityOp.fromPure ψ hψ) (DensityOp.fromPure φ hφ)
        = ‖(ψ.dag * φ : ℂ)‖ ^ 2 := by
    unfold DensityOp.fidelitySq Quantum.Metrics.fidelitySq
    change DensityOp.fidelity (DensityOp.fromPure ψ hψ) (DensityOp.fromPure φ hφ) ^ 2
          = ‖(ψ.dag * φ : ℂ)‖ ^ 2
    rw [h_fid]
  rw [h_fidsq] at h_sq
  -- Take square roots, using nonnegativity of trace distance.
  have h_td_nn := Quantum.Metrics.traceDistance_nonneg
      (DensityOp.fromPure ψ hψ).toOp (DensityOp.fromPure φ hφ).toOp
  have h := congrArg Real.sqrt h_sq
  rw [Real.sqrt_sq h_td_nn] at h
  exact h

/-- **Pure-state Fuchs–van de Graaf inequality** (≤ form), which is what the
downstream FvdG on mixed states will actually call. -/
theorem traceDistance_pure_le_sqrt_one_sub_fidelitySq
    {n : ℕ} [NeZero n] (ψ φ : Ket n)
    (hψ : ψ.dag * ψ = 1) (hφ : φ.dag * φ = 1) :
    Quantum.Metrics.traceDistance
        (DensityOp.fromPure ψ hψ).toOp
        (DensityOp.fromPure φ hφ).toOp
      ≤ Real.sqrt
          (1 - Quantum.Metrics.fidelity
            (DensityOp.fromPure ψ hψ).toPosSemidefOp
            (DensityOp.fromPure φ hφ).toPosSemidefOp ^ 2) := by
  have h_eq := traceDistance_pure_eq_sqrt_one_sub_abs_inner_sq ψ φ hψ hφ
  have h_fid := InfoTheory.SmoothMinEntropy.fidelity_pure_eq_abs_inner ψ φ hψ hφ
  have h_fid' : Quantum.Metrics.fidelity
      (DensityOp.fromPure ψ hψ).toPosSemidefOp
      (DensityOp.fromPure φ hφ).toPosSemidefOp = ‖(ψ.dag * φ : ℂ)‖ := h_fid
  rw [h_eq, h_fid']

end Quantum.Metrics

end -- noncomputable section
