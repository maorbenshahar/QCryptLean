import QCryptLean.Quantum.Operators.InverseSqrt

/-!
# Projector Cauchy–Schwarz trace-norm bound

A cross-block trace-norm bound for window-block decompositions.  For a
positive-semidefinite `ρ` and Hermitian sandwiching operators `P`, `R`,

  `‖P ρ R‖₁ ≤ √( Tr(P ρ P).re · Tr(R ρ R).re )`.

The consumer instantiates `P = 1 ⊗ P_good`, `R = 1 ⊗ P_bad` (window projectors,
which are Hermitian); idempotency of `P`, `R` is used only by the consumer (to
identify `Tr(P ρ P)` with an accepted-block weight), *not* by this lemma, which
holds for arbitrary Hermitian `P`, `R`.

## Proof

Write `S := √ρ` (Hermitian PSD, `S * S = ρ`).  The polar-unitary maximizer
`exists_unitary_trace_mul_eq_trace_cfcSqrt_mul_conjTranspose` supplies a unitary
`U` with `Tr(U (PρR)ᴴ) = ‖PρR‖₁`.  Factoring `(PρR)ᴴ = R ρ P = (URS)(SP)` and
applying the Hilbert–Schmidt Cauchy–Schwarz inequality
`norm_trace_mul_sq_le_trace_mul_trace_conjTranspose` with `A = URS`, `B = SP`
gives `‖Tr(AB)‖² ≤ Tr(A Aᴴ).re · Tr(Bᴴ B).re = Tr(RρR).re · Tr(PρP).re`, and
`‖PρR‖₁ = Re Tr(AB) ≤ ‖Tr(AB)‖` closes the bound.

## Main statement

- `projector_cauchySchwarz_traceNorm_le`
-/

open Quantum.Operators Matrix Quantum.Metrics
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- **Projector Cauchy–Schwarz trace-norm bound.**  For positive-semidefinite
`ρ` and Hermitian `P`, `R`,
`‖P ρ R‖₁ ≤ √( Tr(P ρ P).re · Tr(R ρ R).re )`. -/
theorem projector_cauchySchwarz_traceNorm_le {N : ℕ} [NeZero N]
    (ρ : Op N) (hρ : ρ.PosSemidef) (P R : Op N)
    (hP : P.IsHermitian) (hR : R.IsHermitian) :
    traceNorm (P * ρ * R) ≤
      Real.sqrt ((P * ρ * P).trace.re * (R * ρ * R).trace.re) := by
  classical
  set X : Op N := P * ρ * R with hX_def
  -- Square root of ρ.
  set S : Op N := CFC.sqrt ρ with hS_def
  have hS_psd : S.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hS_herm : Sᴴ = S := hS_psd.isHermitian.eq
  have hSS : S * S = ρ := CFC.sqrt_mul_sqrt_self ρ (ha := hρ.nonneg)
  -- Conjugate transpose of X, all sandwiching operators Hermitian.
  have hXH : Xᴴ = R * ρ * P := by
    rw [hX_def, conjTranspose_mul, conjTranspose_mul, hP.eq, hR.eq, hρ.isHermitian.eq,
      Matrix.mul_assoc]
  -- Polar-unitary maximizer applied to Xᴴ.
  obtain ⟨U, hU⟩ :=
    Quantum.Metrics.PolarUnitary.exists_unitary_trace_mul_eq_trace_cfcSqrt_mul_conjTranspose Xᴴ
  rw [conjTranspose_conjTranspose] at hU
  -- traceNorm X = Re Tr(U Xᴴ).
  have h_tn : traceNorm X = (U.toOp * Xᴴ).trace.re := by
    rw [hU, ← Quantum.Metrics.traceNorm_eq_re_trace_cfcSqrt_conjTranspose_mul X]
  -- The two HS factors.
  set A : Op N := U.toOp * R * S with hA_def
  set B : Op N := S * P with hB_def
  -- U Xᴴ = A B  (literal matrix equality, no cyclicity).
  have h_prod : U.toOp * Xᴴ = A * B := by
    rw [hXH, hA_def, hB_def, ← hSS]
    noncomm_ring
  -- A Aᴴ has trace Tr(RρR).
  have hAAT : (A * Aᴴ).trace = (R * ρ * R).trace := by
    have hAH : Aᴴ = S * R * U.toOpᴴ := by
      rw [hA_def, conjTranspose_mul, conjTranspose_mul, hS_herm, hR.eq, Matrix.mul_assoc]
    have h1 : A * Aᴴ = U.toOp * (R * ρ * R) * U.toOpᴴ := by
      rw [hA_def, hAH, ← hSS]; noncomm_ring
    rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, U.unitary_left, Matrix.one_mul]
  -- Bᴴ B has trace Tr(PρP)  (literal matrix equality).
  have hBBT : (Bᴴ * B).trace = (P * ρ * P).trace := by
    have hBH : Bᴴ = P * S := by
      rw [hB_def, conjTranspose_mul, hS_herm, hP.eq]
    rw [hBH, hB_def]
    congr 1
    rw [← hSS]; noncomm_ring
  -- Hilbert–Schmidt Cauchy–Schwarz.
  have hCS := Quantum.Metrics.norm_trace_mul_sq_le_trace_mul_trace_conjTranspose A B
  rw [hAAT, hBBT] at hCS
  -- hCS : ‖(A * B).trace‖ ^ 2 ≤ (R*ρ*R).trace.re * (P*ρ*P).trace.re
  -- Nonnegativity of the RHS factors.
  have hP_nn : 0 ≤ (P * ρ * P).trace.re := by
    have : (P * ρ * P).PosSemidef := by
      have := hρ.conjTranspose_mul_mul_same (B := P)
      rwa [hP.eq] at this
    exact this.trace_re_nonneg
  have hR_nn : 0 ≤ (R * ρ * R).trace.re := by
    have : (R * ρ * R).PosSemidef := by
      have := hρ.conjTranspose_mul_mul_same (B := R)
      rwa [hR.eq] at this
    exact this.trace_re_nonneg
  -- Assemble.
  have h_re_le_norm : (A * B).trace.re ≤ ‖(A * B).trace‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have h_norm_le : ‖(A * B).trace‖ ≤
      Real.sqrt ((R * ρ * R).trace.re * (P * ρ * P).trace.re) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hCS
  calc traceNorm X = (U.toOp * Xᴴ).trace.re := h_tn
    _ = (A * B).trace.re := by rw [h_prod]
    _ ≤ ‖(A * B).trace‖ := h_re_le_norm
    _ ≤ Real.sqrt ((R * ρ * R).trace.re * (P * ρ * P).trace.re) := h_norm_le
    _ = Real.sqrt ((P * ρ * P).trace.re * (R * ρ * R).trace.re) := by
        rw [mul_comm]

end
