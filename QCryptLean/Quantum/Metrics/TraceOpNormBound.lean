import QCryptLean.Quantum.Metrics.WatrousFactorization

/-!
# Trace-OpNorm Dual Bounds

Dual-pairing inequalities between the operator norm and the trace norm.

## Main statements

- `unitaryOp_opNorm_eq_one`: the L2 operator norm of a unitary operator is `1`.
- `norm_entry_le_opNorm`: `‖M i j‖ ≤ ‖M‖` for the L2 operator norm.
- `norm_trace_mul_psd_le_opNorm_mul_trace_re`: for any `Q` and PSD `P`,
  `‖(Q * P).trace‖ ≤ ‖Q‖ * P.trace.re`.
- `norm_trace_mul_le_opNorm_mul_traceNorm`: for any `W, X`,
  `‖(W * X).trace‖ ≤ ‖W‖ * traceNorm X`.  Equivalently, the trace norm is
  dual to the operator norm under the trace pairing.

## References

- Bhatia (1997) *Matrix Analysis*, Ch. IV (Schatten-p Hölder inequality for
  conjugate exponents `(∞, 1)`).
- Watrous (2018) *TQI*, Section 1.2 (trace norm as the dual of the operator
  norm on matrices).
-/

open Quantum.Operators Matrix Quantum.Metrics Quantum.Channels
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace Quantum.Metrics.TraceOpNormBound

/-- The L2 operator norm of a unitary operator is `1`. -/
lemma unitaryOp_opNorm_eq_one {d : ℕ} [NeZero d] (V : UnitaryOp d) :
    ‖V.toOp‖ = 1 := by
  have h1 : ‖V.toOp‖ * ‖V.toOp‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, V.unitary_left, norm_one]
  nlinarith [norm_nonneg V.toOp, sq_nonneg (‖V.toOp‖ - 1)]

/-- A single matrix entry is bounded by the L2 operator norm.
    Proof via the column norm: `‖col j‖₂² = ∑ᵢ |Mᵢⱼ|² ≥ |Mᵢⱼ|²` and
    `‖col j‖₂ ≤ ‖M‖ · ‖eⱼ‖ = ‖M‖`. -/
lemma norm_entry_le_opNorm {d : ℕ} [NeZero d]
    (M : Op d) (i j : Fin d) :
    ‖M i j‖ ≤ ‖M‖ := by
  let eⱼ : EuclideanSpace ℂ (Fin d) := EuclideanSpace.single j (1 : ℂ)
  have hnorm_j : ‖eⱼ‖ = 1 := by
    rw [PiLp.norm_single]; simp
  have hmulVec : M.mulVec eⱼ.ofLp = M.mulVec (Pi.single j 1) := by
    rw [PiLp.ofLp_single]
  -- Identify the j-th column entry with `M i j`.
  have hcol : M.mulVec (Pi.single j 1) i = M i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  -- `|M i j|² ≤ ∑ k, |M k j|² = ‖col j‖_Euc²`.
  have h_col_norm_sq : ‖(EuclideanSpace.equiv (Fin d) ℂ).symm (M.mulVec eⱼ.ofLp)‖ ^ 2 =
      ∑ k, ‖M.mulVec eⱼ.ofLp k‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
    rfl
  -- The Euclidean norm of the column is at least |M i j|.
  have h_entry_le_col_norm :
      ‖M i j‖ ≤ ‖(EuclideanSpace.equiv (Fin d) ℂ).symm (M.mulVec eⱼ.ofLp)‖ := by
    suffices h_sq : ‖M i j‖ ^ 2 ≤
        ‖(EuclideanSpace.equiv (Fin d) ℂ).symm (M.mulVec eⱼ.ofLp)‖ ^ 2 by
      have hsq_nn : (0 : ℝ) ≤ ‖M i j‖ ^ 2 := sq_nonneg _
      exact abs_le_of_sq_le_sq' h_sq (norm_nonneg _) |>.2
    rw [h_col_norm_sq]
    rw [show ‖M i j‖ ^ 2 = ‖M.mulVec eⱼ.ofLp i‖ ^ 2 from by
      rw [hmulVec, hcol]]
    exact Finset.single_le_sum (f := fun k => ‖M.mulVec eⱼ.ofLp k‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h_col_le_opNorm :
      ‖(EuclideanSpace.equiv (Fin d) ℂ).symm (M.mulVec eⱼ.ofLp)‖ ≤ ‖M‖ := by
    have := Matrix.l2_opNorm_mulVec M eⱼ
    rw [hnorm_j, mul_one] at this
    exact this
  linarith [h_entry_le_col_norm, h_col_le_opNorm]

/-- **Trace-opNorm bound for PSD factor**: for any matrix `Q` and PSD `P`,
    `‖(Q * P).trace‖ ≤ ‖Q‖ * P.trace.re`.

    Proof via spectral decomposition of `P = U * D * U*`: the trace becomes
    `∑ᵢ λᵢ · (U* Q U)ᵢᵢ`, each `‖(U* Q U)ᵢᵢ‖ ≤ ‖U* Q U‖ ≤ ‖Q‖`, so
    `‖Tr(Q P)‖ ≤ ∑ᵢ λᵢ · ‖Q‖ = ‖Q‖ · Tr(P).re`. -/
lemma norm_trace_mul_psd_le_opNorm_mul_trace_re {d : ℕ} [NeZero d]
    (Q P : Op d) (hP : P.PosSemidef) :
    ‖(Q * P).trace‖ ≤ ‖Q‖ * P.trace.re := by
  have hH := hP.isHermitian
  set U : Op d := hH.eigenvectorUnitary.val with hU_def
  set evs := hH.eigenvalues with hevs_def
  set D : Op d := diagonal (RCLike.ofReal ∘ evs) with hD_def
  have hP_spec : P = U * D * star U := hH.spectral_theorem
  have hUstarU : star U * U = 1 :=
    Matrix.UnitaryGroup.star_mul_self hH.eigenvectorUnitary
  have hUUstar : U * star U = 1 :=
    mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.prop
  have hUctU : U.conjTranspose * U = 1 := by change star U * U = 1; exact hUstarU
  have h_evs_nn : ∀ i, 0 ≤ evs i := hH.posSemidef_iff_eigenvalues_nonneg.mp hP
  have hU_norm : ‖U‖ = 1 := by
    have h1 : ‖U‖ * ‖U‖ = 1 := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hUctU, norm_one]
    nlinarith [norm_nonneg U, sq_nonneg (‖U‖ - 1)]
  have hUstar_norm : ‖star U‖ = 1 := by
    change ‖U.conjTranspose‖ = 1; rw [Matrix.l2_opNorm_conjTranspose, hU_norm]
  -- N := U* Q U has ‖N‖ ≤ ‖Q‖.
  set N : Op d := star U * Q * U with hN_def
  have hN_norm : ‖N‖ ≤ ‖Q‖ := by
    calc ‖N‖ = ‖star U * Q * U‖ := rfl
      _ ≤ ‖star U * Q‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖star U‖ * ‖Q‖) * ‖U‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖Q‖ := by rw [hUstar_norm, hU_norm, one_mul, mul_one]
  -- Tr(Q P) = Tr(N D) = ∑ᵢ N_{ii} * (evs i).
  have h_trace_eq : (Q * P).trace = ∑ i, N i i * (evs i : ℂ) := by
    calc (Q * P).trace
        = (Q * (U * D * star U)).trace := by rw [hP_spec]
      _ = (star U * Q * U * D).trace := by
          rw [show Q * (U * D * star U) = Q * U * D * star U from by
            simp [Matrix.mul_assoc]]
          rw [Matrix.trace_mul_comm (Q * U * D) (star U)]
          simp [Matrix.mul_assoc]
      _ = (N * D).trace := by rfl
      _ = ∑ i, N i i * (evs i : ℂ) := by
          simp [D, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal,
            Function.comp]
  -- Bound each term.
  have h_term_bound : ∀ i,
      ‖N i i * (evs i : ℂ)‖ ≤ ‖Q‖ * evs i := by
    intro i
    have h_Nii_bound : ‖N i i‖ ≤ ‖Q‖ :=
      (norm_entry_le_opNorm N i i).trans hN_norm
    have h_evs_abs : ‖(evs i : ℂ)‖ = evs i := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h_evs_nn i)]
    calc ‖N i i * (evs i : ℂ)‖
        = ‖N i i‖ * ‖(evs i : ℂ)‖ := norm_mul _ _
      _ = ‖N i i‖ * evs i := by rw [h_evs_abs]
      _ ≤ ‖Q‖ * evs i :=
          mul_le_mul_of_nonneg_right h_Nii_bound (h_evs_nn i)
  -- Sum bound.
  calc ‖(Q * P).trace‖
      = ‖∑ i, N i i * (evs i : ℂ)‖ := by rw [h_trace_eq]
    _ ≤ ∑ i, ‖N i i * (evs i : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖Q‖ * evs i := Finset.sum_le_sum (fun i _ => h_term_bound i)
    _ = ‖Q‖ * ∑ i, evs i := by rw [← Finset.mul_sum]
    _ = ‖Q‖ * P.trace.re := by
        congr 1
        rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]
        simp [hevs_def]

/-- **Schatten Hölder with conjugate exponents `(∞, 1)`**: for any `W, X`,
    `‖(W * X).trace‖ ≤ ‖W‖ * traceNorm X`. -/
theorem norm_trace_mul_le_opNorm_mul_traceNorm {d : ℕ} [NeZero d]
    (W X : Op d) :
    ‖(W * X).trace‖ ≤ ‖W‖ * traceNorm X := by
  -- Polar decomposition X = V * P with P PSD, Tr(P).re = traceNorm X, ‖V‖ ≤ 1.
  obtain ⟨V, P, hP_psd, hXVP, hP_trace, hV_norm⟩ :=
    Quantum.Metrics.WatrousFactorization.polar_decomposition_norm X
  -- Q := W * V has ‖Q‖ ≤ ‖W‖.
  have hQ_norm : ‖W * V‖ ≤ ‖W‖ := by
    calc ‖W * V‖ ≤ ‖W‖ * ‖V‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖W‖ * 1 :=
          mul_le_mul_of_nonneg_left hV_norm (norm_nonneg _)
      _ = ‖W‖ := mul_one _
  have h_eq : (W * X).trace = ((W * V) * P).trace := by
    rw [hXVP, ← Matrix.mul_assoc]
  rw [h_eq]
  calc ‖((W * V) * P).trace‖
      ≤ ‖W * V‖ * P.trace.re :=
        norm_trace_mul_psd_le_opNorm_mul_trace_re (W * V) P hP_psd
    _ = ‖W * V‖ * traceNorm X := by rw [hP_trace]
    _ ≤ ‖W‖ * traceNorm X := by
        apply mul_le_mul_of_nonneg_right hQ_norm
        unfold traceNorm; exact Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

end Quantum.Metrics.TraceOpNormBound

end -- noncomputable section
