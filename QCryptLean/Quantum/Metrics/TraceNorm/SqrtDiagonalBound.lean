import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity

/-!
# Trace of a matrix square root versus the square roots of its diagonal

For a positive semidefinite operator `A`, the trace of its operator square root is
bounded by the sum of the square roots of its diagonal entries:

`Tr √A ≤ ∑ᵢ √(Aᵢᵢ)`.

This is a standard matrix-analysis fact (a consequence of operator concavity of the
square root: `⟨eᵢ|√A|eᵢ⟩ ≤ √⟨eᵢ|A|eᵢ⟩` for each standard basis vector, summed over `i`).
It is the tool that reduces the Uhlmann fidelity `F(ρ_x, σ) = Tr √(√ρ_x σ √ρ_x)` against a
possibly non-diagonal reference `σ` to the diagonal weights `√(p(x,y)·σ_yy)`, and thereby
the classical-classical conditional max-entropy to a sum over the diagonal of `σ` — the
first Cauchy–Schwarz step of the TLGR (arXiv:1103.4130) fiber-wise counting bound.

## Main statement
- `trace_sqrtPosSemidefOp_re_le_sum_sqrt_diag`: `Tr √A ≤ ∑ᵢ √(Aᵢᵢ)` for `A` PSD.
-/

open Quantum.Operators Quantum.Metrics Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-- **Trace of the operator square root is bounded by the sum of square roots of the
diagonal entries.** For a positive semidefinite operator `A`,

`(Tr √A).re ≤ ∑ᵢ √((A_ii).re)`.

The diagonal entries of a PSD operator are real and nonnegative, so the right-hand side
is the sum of their genuine square roots.

Proof route (operator Jensen / per-vector Cauchy–Schwarz): write `Tr √A = ∑ᵢ ⟨eᵢ|√A|eᵢ⟩`
over the standard basis; for each unit vector `eᵢ`, with `B := √A` Hermitian PSD,
`⟨eᵢ|B|eᵢ⟩ = ⟨eᵢ, B eᵢ⟩ ≤ ‖B eᵢ‖ = √⟨eᵢ|B²|eᵢ⟩ = √⟨eᵢ|A|eᵢ⟩ = √(A_ii)`; sum over `i`. -/
theorem trace_sqrtPosSemidefOp_re_le_sum_sqrt_diag {n : ℕ} (A : PosSemidefOp n) :
    (Matrix.trace (sqrtPosSemidefOp A)).re ≤ ∑ i : Fin n, Real.sqrt (A.toOp i i).re := by
  set B := sqrtPosSemidefOp A with hB
  have hHerm : Bᴴ = B := sqrtPosSemidefOp_isHermitian A
  have hsq : B * B = A.toOp := sqrtPosSemidefOp_sq A
  -- The `i`-th diagonal entry of `A = B²` is `∑ₖ ‖B i k‖²`.
  have hdiag : ∀ i, (A.toOp i i).re = ∑ k, Complex.normSq (B i k) := by
    intro i
    have hAii : A.toOp i i = ∑ k, (Complex.normSq (B i k) : ℂ) := by
      rw [← hsq, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hik : B k i = star (B i k) := by
        have h := congrFun (congrFun hHerm k) i
        rw [Matrix.conjTranspose_apply] at h
        exact h.symm
      rw [hik, ← starRingEnd_apply, Complex.mul_conj]
    rw [hAii, ← Complex.ofReal_sum, Complex.ofReal_re]
  -- Per-vector bound: `(B i i).re ≤ √((A i i).re)`.
  have hbound : ∀ i, (B i i).re ≤ Real.sqrt ((A.toOp i i).re) := by
    intro i
    rw [hdiag i]
    have hre_le : (B i i).re ≤ Real.sqrt (Complex.normSq (B i i)) := by
      by_cases h : (B i i).re ≤ 0
      · exact le_trans h (Real.sqrt_nonneg _)
      · push_neg at h
        have h2 : ((B i i).re) ^ 2 ≤ Complex.normSq (B i i) := by
          rw [Complex.normSq_apply]; nlinarith [sq_nonneg (B i i).im]
        calc (B i i).re = Real.sqrt (((B i i).re) ^ 2) := (Real.sqrt_sq h.le).symm
          _ ≤ Real.sqrt (Complex.normSq (B i i)) := Real.sqrt_le_sqrt h2
    refine le_trans hre_le (Real.sqrt_le_sqrt ?_)
    exact Finset.single_le_sum (f := fun k => Complex.normSq (B i k))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  -- Sum over `i`.
  have htrace : (Matrix.trace B).re = ∑ i : Fin n, (B i i).re := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Complex.re_sum]
  rw [htrace]
  exact Finset.sum_le_sum (fun i _ => hbound i)

/-- **Uhlmann fidelity is bounded by the sum of square roots of the diagonal of the
sandwiched operator.** For PSD operators `A, B`,

`F(A, B) ≤ ∑ᵢ √((√A · B · √A)_ii).re`.

This packages the sandwiched operator `√A · B · √A` (whose trace-square-root is `F(A,B)`)
as a `PosSemidefOp` and applies `trace_sqrtPosSemidefOp_re_le_sum_sqrt_diag`. -/
theorem fidelity_le_sum_sqrt_sandwich_diag {n : ℕ} [NeZero n] (A B : PosSemidefOp n) :
    fidelity A B ≤ ∑ i : Fin n, Real.sqrt
      ((sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A) i i).re := by
  have hS : (sqrtPosSemidefOp A)ᴴ = sqrtPosSemidefOp A := sqrtPosSemidefOp_isHermitian A
  have hsand_psd :
      (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A).PosSemidef := by
    have h := Matrix.PosSemidef.conjTranspose_mul_mul_same
      (Quantum.Operators.posSemidefOp_implies_mathlib B) (sqrtPosSemidefOp A)
    rwa [hS] at h
  let M : PosSemidefOp n :=
    ⟨⟨sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A, hsand_psd.isHermitian⟩,
      fun v => Quantum.Operators.posSemidef_re_quadraticForm_nonneg hsand_psd v⟩
  have hfid : fidelity A B = (Matrix.trace (sqrtPosSemidefOp M)).re := rfl
  rw [hfid]
  exact trace_sqrtPosSemidefOp_re_le_sum_sqrt_diag M

end Quantum.Metrics

end -- noncomputable section
