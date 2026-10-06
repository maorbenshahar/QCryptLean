import QCryptLean.Quantum.Metrics.FidelityScaling
import QCryptLean.Quantum.TensorProducts.PSDOrder
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Fidelity lower bounds from Löwner domination

This file contains small order-theoretic helpers for Uhlmann fidelity.  The main
statement turns an operator domination `A ≤ c • B` into the lower bound
`Tr A / sqrt c ≤ F(A,B)`.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Quantum.Metrics

private lemma matrix_le_of_opLe {n : ℕ} {A B : Op n}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : opLe A B) :
    A ≤ B := by
  rw [Matrix.le_iff]
  exact Quantum.Operators.opLe.posSemidef_sub hA hB h

private lemma trace_re_le_of_matrix_le {n : ℕ} (A B : Op n)
    (h : A ≤ B) : A.trace.re ≤ B.trace.re := by
  have hpsd : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hnn := hpsd.trace_nonneg
  rw [Matrix.trace_sub] at hnn
  have hre := (Complex.nonneg_iff.mp hnn).1
  simpa [Complex.sub_re, sub_nonneg] using hre

private lemma opLe_sq_sqrt_sandwich_smul {n : ℕ}
    (A B : PosSemidefOp n) {c : ℝ}
    (hAB : opLe A.toOp ((c : ℂ) • B.toOp)) :
    opLe (A.toOp * A.toOp)
      ((c : ℂ) • (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A)) := by
  set S : Op n := sqrtPosSemidefOp A with hS_def
  have hS_herm : S.IsHermitian := by
    simpa [S] using sqrtPosSemidefOp_isHermitian A
  have hS_sq : S * S = A.toOp := by
    simpa [S] using sqrtPosSemidefOp_sq A
  have hsand := Quantum.Operators.opLe_sandwich_of_isHermitian hS_herm hAB
  have hLHS : S * A.toOp * S = A.toOp * A.toOp := by
    have h_comm : S * A.toOp = A.toOp * S := by
      conv_lhs => rw [← hS_sq]
      conv_rhs => rw [← hS_sq]
      exact (mul_assoc S S S).symm
    rw [h_comm, mul_assoc, hS_sq]
  have hRHS : S * (((c : ℝ) : ℂ) • B.toOp) * S =
      ((c : ℝ) : ℂ) • (S * B.toOp * S) := by
    calc S * (((c : ℝ) : ℂ) • B.toOp) * S
        = (((c : ℝ) : ℂ) • (S * B.toOp)) * S := by
            rw [mul_smul_comm]
      _ = ((c : ℝ) : ℂ) • (S * B.toOp * S) := by
            rw [smul_mul_assoc]
  rw [hLHS, hRHS] at hsand
  simpa [S] using hsand

private lemma sqrt_sandwich_inner_posSemidef {n : ℕ}
    (A B : PosSemidefOp n) :
    (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A).PosSemidef := by
  set S : Op n := sqrtPosSemidefOp A with hS_def
  have hB_psd : B.toOp.PosSemidef := posSemidefOp_implies_mathlib B
  have hS_herm : S.IsHermitian := by
    simpa [S] using sqrtPosSemidefOp_isHermitian A
  have h := Matrix.PosSemidef.conjTranspose_mul_mul_same hB_psd S
  simpa [S, hS_herm.eq] using h

private lemma matrix_le_sq_sqrt_sandwich_smul {n : ℕ}
    (A B : PosSemidefOp n) {c : ℝ} (hc : 0 ≤ c)
    (hAB : opLe A.toOp ((c : ℂ) • B.toOp)) :
    A.toOp * A.toOp ≤
      ((c : ℂ) • (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A)) := by
  have hA_psd : A.toOp.PosSemidef := posSemidefOp_implies_mathlib A
  have hAA_herm : (A.toOp * A.toOp).IsHermitian := by
    change (A.toOp * A.toOp)ᴴ = A.toOp * A.toOp
    rw [Matrix.conjTranspose_mul, hA_psd.isHermitian.eq]
  have hinner_psd := sqrt_sandwich_inner_posSemidef A B
  have hinner_smul_psd :
      ((c : ℂ) • (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A)).PosSemidef :=
    Matrix.PosSemidef.smul hinner_psd (RCLike.ofReal_nonneg.mpr hc)
  exact matrix_le_of_opLe hAA_herm hinner_smul_psd.isHermitian
    (opLe_sq_sqrt_sandwich_smul A B hAB)

private lemma trace_sqrt_smul_sandwich_eq_sqrt_mul_fidelity {n : ℕ} [NeZero n]
    (A B : PosSemidefOp n) {c : ℝ} (hc : 0 ≤ c) :
    letI : PartialOrder (Op n) := Matrix.instPartialOrder
    letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
    letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
    (Matrix.trace
      (CFC.sqrt ((c : ℂ) •
        (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A)))).re =
      Real.sqrt c * fidelity A B := by
  let : PartialOrder (Op n) := Matrix.instPartialOrder
  let : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  have hinner_psd := sqrt_sandwich_inner_posSemidef A B
  have hsqrt :
      CFC.sqrt ((c : ℂ) •
          (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A)) =
        ((Real.sqrt c : ℝ) : ℂ) •
          CFC.sqrt (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A) :=
    sqrt_ofReal_smul hc hinner_psd
  rw [hsqrt, Matrix.trace_smul]
  change (((Real.sqrt c : ℝ) : ℂ) *
      Matrix.trace (CFC.sqrt (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A))).re =
    Real.sqrt c * fidelity A B
  rw [Complex.re_ofReal_mul]
  rfl

private lemma trace_le_sqrt_mul_fidelity_of_opLe {n : ℕ} [NeZero n]
    (A B : PosSemidefOp n) {c : ℝ} (hc : 0 ≤ c)
    (hAB : opLe A.toOp ((c : ℂ) • B.toOp)) :
    (Matrix.trace A.toOp).re ≤ Real.sqrt c * fidelity A B := by
  let : PartialOrder (Op n) := Matrix.instPartialOrder
  let : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  let : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  -- `A² ≤ c · √A B √A`, and the square root is operator monotone
  have hsqrt_le :
      CFC.sqrt (A.toOp * A.toOp) ≤
        CFC.sqrt ((c : ℂ) • (sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A)) := by
    let : CStarAlgebra (Op n) := {}
    exact CFC.sqrt_le_sqrt _ _ (matrix_le_sq_sqrt_sandwich_smul A B hc hAB)
  have htrace_le := trace_re_le_of_matrix_le _ _ hsqrt_le
  -- `√(A²) = A`, and `Tr √(c · √A B √A) = √c · F(A, B)`
  rw [CFC.sqrt_mul_self A.toOp (posSemidefOp_implies_mathlib A).nonneg,
    trace_sqrt_smul_sandwich_eq_sqrt_mul_fidelity A B hc] at htrace_le
  exact htrace_le

/-- If `A ≤ c • B` for positive semidefinite operators and `c > 0`, then
`F(A,B) ≥ Tr(A)/sqrt(c)`. -/
lemma trace_div_sqrt_le_fidelity_of_opLe {n : ℕ} [NeZero n]
    (A B : PosSemidefOp n) {c : ℝ} (hc : 0 < c)
    (hAB : opLe A.toOp ((c : ℂ) • B.toOp)) :
    (Matrix.trace A.toOp).re / Real.sqrt c ≤ fidelity A B := by
  have htrace := trace_le_sqrt_mul_fidelity_of_opLe A B hc.le hAB
  have hsqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos_of_pos hc
  exact (div_le_iff₀ hsqrt_pos).2 (by simpa [mul_comm] using htrace)

end Quantum.Metrics

end
