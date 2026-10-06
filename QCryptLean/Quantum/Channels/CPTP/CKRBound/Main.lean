import QCryptLean.InfoTheory.DistanceBounds.TraceNormContraction
import QCryptLean.Quantum.Channels.CPTP.CKRBound.GeneralContractivity
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Basic

/-!
# CKR Factor-2 and Generalized Bounds — arbitrary ancilla

Higher-level CKR bounds that sit above the ordinary reference-state
infrastructure in `Reference/Basic.lean`. This file keeps a factor-2 corollary of
general `id ⊗ T` contractivity and the generalized d = 4 CKR PSD bound with
arbitrary ancilla.

## Main statements
- `jordan_decompose_traceNorm`: Jordan decomposition of a Hermitian operator with bounded trace norm
- `traceNorm_mapIdTensor_contractive_factor2`: non-Hermitian `id ⊗ T` contractivity with factor 2
- `Quantum.Channels.partial_trace_deFinetti_gap_posSemidef`: ordinary de Finetti domination for
  arbitrary ancilla
- `ckr_psd_bound_general`: generalized CKR PSD bound with factor-2 loss
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Math.RepresentationTheory Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- **Jordan decomposition for trace norm**: Any Hermitian operator `X` with `‖X‖₁ ≤ 1`
    decomposes as `X = X₊ - X₋` with `X₊, X₋` PSD and
    `Tr(X₊).re + Tr(X₋).re ≤ 1`. -/
theorem jordan_decompose_traceNorm {d : ℕ} [NeZero d]
    (X : Op d) (hX_herm : X.IsHermitian) (hX : traceNorm X ≤ 1) :
    ∃ (X_pos X_neg : Op d),
      X_pos.PosSemidef ∧ X_neg.PosSemidef ∧
      X = X_pos - X_neg ∧
      X_pos.trace.re + X_neg.trace.re ≤ 1 := by
  open Quantum.Metrics in
  obtain ⟨X_pos, X_neg, hX_pos, hX_neg, hX_eq, hX_trace⟩ :=
    traceNormHermitian_eq_trace_pos_neg X hX_herm
  refine ⟨X_pos, X_neg, hX_pos, hX_neg, hX_eq, ?_⟩
  have h_trace_le : (X_pos.trace + X_neg.trace).re ≤ 1 := by
    rw [← hX_trace, ← traceNorm_hermitian_eq (A := X) hX_herm]
    exact hX
  simpa [Complex.add_re] using h_trace_le

/-!
## Factor-2 contractivity for `mapIdTensor`

The Hermitian contractive case lives in `HermitianContractivity.lean`. The factor-2
`mapIdTensor` statement is a compatibility corollary of the general contractivity theorem.
The trace-norm bounds for the Cartesian parts of an operator are
`Quantum.Metrics.traceNorm_realPart_le` and `Quantum.Metrics.traceNorm_imaginaryPart_le`.
-/

/-- For a complex number with zero imaginary part and nonnegative real part, `‖c‖ = c.re`. -/
lemma Complex.norm_eq_re_of_nonneg {c : ℂ} (hre : 0 ≤ c.re) (him : c.im = 0) :
    ‖c‖ = c.re := by
  rw [show ‖c‖ = Real.sqrt (c.normSq) from rfl,
    show c.normSq = c.re ^ 2 from by
      rw [Complex.normSq_apply, him, mul_zero, add_zero, sq],
    Real.sqrt_sq hre]

/-- **Trace norm contractivity for `id ⊗ T`**, stated with factor-2 slack. -/
theorem traceNorm_mapIdTensor_contractive_factor2 {n m k : ℕ}
    [NeZero n] [NeZero m] [NeZero k]
    (T : Op n →ₗ[ℂ] Op m)
    (hT_cp : IsCompletelyPositive ⇑T)
    (hT_contr : ∀ A : Op n, A.PosSemidef → (T A).trace.re ≤ A.trace.re)
    (Y : Op (k * n)) :
    traceNorm (mapIdTensor T Y) ≤ 2 * traceNorm Y := by
  have h_contr := traceNorm_mapIdTensor_contractive T hT_cp hT_contr Y
  have hY_nonneg : 0 ≤ traceNorm Y := Quantum.Metrics.traceNorm_nonneg Y
  calc
    traceNorm (mapIdTensor T Y) ≤ traceNorm Y := h_contr
    _ ≤ 2 * traceNorm Y := by
      rw [two_mul]
      exact le_add_of_nonneg_left hY_nonneg

/-!
## Generalized CKR bound

These statements reuse the ordinary reference-state machinery from
`Reference/Basic.lean`, but drop Hermiticity preservation of `Δ` by paying the
factor-2 loss from `traceNorm_mapIdTensor_contractive_factor2`.
-/

/-- **Generalized CKR bound for PSD operators** with arbitrary ancilla and factor-2 loss. -/
theorem ckr_psd_bound_general {n dimOut dimK dimR : ℕ}
    [NeZero n] [NeZero dimOut] [NeZero dimK] [NeZero dimR]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (ρ : Op (4 ^ n * dimK))
    (hρ_psd : ρ.PosSemidef)
    (hρ_trace : ρ.trace.re ≤ 1)
    (τ : DensityOp ((4 ^ n) * dimR))
    (hτ_pure : τ.IsPure)
    (hτ_deFinetti : τ.partialTraceB.toOp =
      (1 / Matrix.trace (symmetricProjector 4 n)) • symmetricProjector 4 n)
    (hρ_support : symmetricProjector 4 n * partialTraceB ρ = partialTraceB ρ) :
    traceNorm (mapTensorId Δ ρ) ≤
      2 * ↑(Nat.choose (n + 3) 3) * traceNorm (mapTensorId Δ τ.toOp) := by
  have h_dom := Quantum.Channels.partial_trace_deFinetti_gap_posSemidef
    ρ hρ_psd hρ_trace τ hτ_deFinetti hρ_support
  have hC_pos : (0 : ℝ) < ↑(Nat.choose (n + 3) 3) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  obtain ⟨T, hT_cp, hT_contr, hρ_eq⟩ :=
    substate_map_exists ρ hρ_psd τ.partialTraceB
      (Nat.choose (n + 3) 3 : ℝ) hC_pos h_dom τ hτ_pure rfl
  rw [hρ_eq, mapTensorId_smul_basic]
  rw [mapTensorId_compose_different_factors Δ T τ.toOp]
  rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
  have h_contr := traceNorm_mapIdTensor_contractive_factor2 T hT_cp hT_contr
    (mapTensorId Δ τ.toOp)
  have h_norm_eq : ‖(↑(↑(Nat.choose (n + 3) 3) : ℝ) : ℂ)‖ =
      ↑(Nat.choose (n + 3) 3) := by
    norm_cast
  rw [h_norm_eq]
  calc (↑(Nat.choose (n + 3) 3) : ℝ) * traceNorm (mapIdTensor T (mapTensorId Δ τ.toOp))
      ≤ ↑(Nat.choose (n + 3) 3) * (2 * traceNorm (mapTensorId Δ τ.toOp)) :=
        mul_le_mul_of_nonneg_left h_contr (Nat.cast_nonneg _)
    _ = 2 * ↑(Nat.choose (n + 3) 3) * traceNorm (mapTensorId Δ τ.toOp) := by
        ring

end Quantum.Channels
