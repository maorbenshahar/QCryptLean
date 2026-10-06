import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MaxEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.HmaxClassical

/-!
# Max-entropy domain and singular-reference regressions

One-outcome states with weight strictly between zero and one have negative max-entropy.
The support inverse
of a rank-one qubit projection preserves its supported collision trace.
-/

open Quantum.Operators InfoTheory.SmoothMinEntropy Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace QCryptLeanTest.MaxEntropyDomain

/-- Every one-outcome state with weight strictly between zero and one has negative max-entropy,
including the subnormalized rank-one qubit state with an orthogonal reference. -/
example (ρ : CQState Unit 2) (hpos : 0 < ρ.classicalMarginal ())
    (hlt : ρ.classicalMarginal () < 1) :
    conditionalMaxEntropyOptReal ρ (by simpa using hpos) < 0 := by
  have hbound := conditionalMaxEntropyOptReal_le_classicalMarginalMaxEntropy ρ
    (by simpa using hpos)
  have hneg : classicalMarginalMaxEntropyReal ρ (by simpa using hpos) < 0 := by
    simp only [classicalMarginalMaxEntropyReal, Fintype.sum_unique, Real.sq_sqrt hpos.le]
    exact div_neg_of_neg_of_pos (Real.log_neg hpos hlt) (Real.log_pos one_lt_two)
  exact hbound.trans_lt hneg

private def qubitProjection : DensityOp 2 where
  toOp := Matrix.diagonal (fun i => ((![1, 0] : Fin 2 → ℝ) i : ℂ))
  isHermitian := Math.SpectralTheory.isHermitian_diagonal_ofReal _
  pos_semidef := by
    apply posSemidef_re_quadraticForm_nonneg
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  trace_one := by
    simp [Matrix.trace, Fin.sum_univ_two]

private def oneOutcomeProjection : CQState Unit 2 where
  stateMap := fun _ => DensityOp.toSubDensityOp qubitProjection
  weight_le_one := by simp [toSubDensityOp_trace]

private lemma qubitProjection_support_inv :
    qubitProjection.toOp ^ (-1 : ℝ) = qubitProjection.toOp := by
  rw [CFC.rpow_eq_cfc_real (posSemidefOp_implies_mathlib
    qubitProjection.toPosSemidefOp).nonneg]
  change cfc (fun x : ℝ => x ^ (-1 : ℝ))
      (Matrix.diagonal (fun i => ((![1, 0] : Fin 2 → ℝ) i : ℂ))) = _
  rw [Math.SpectralTheory.cfc_diagonal_ofReal]
  congr 1
  funext i
  fin_cases i <;> norm_num

/-- The supported collision trace of a pure qubit state against itself is one,
even though its reference matrix is singular. -/
example : oneOutcomeProjection.traceRhoSqInvSigma qubitProjection = 1 := by
  unfold CQState.traceRhoSqInvSigma
  rw [qubitProjection_support_inv]
  norm_num [oneOutcomeProjection, qubitProjection, CQState.toJointOp,
    DensityOp.toSubDensityOp, Matrix.trace, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    Matrix.kroneckerMap_apply, Fin.sum_univ_two, Fintype.sum_prod_type, pow_two]

end QCryptLeanTest.MaxEntropyDomain

end -- noncomputable section
