import QCryptLean.Math.SpectralTheory.MatrixCFC
import QCryptLean.InfoTheory.SmoothMinEntropy.CollisionReference

/-!
# Singular-reference support inverse regression

The support inverse
of a rank-one qubit projection preserves its supported collision trace.
-/

open Quantum.Operators InfoTheory.SmoothMinEntropy Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace QCryptLeanTest.MaxEntropyDomain

private def qubitProjection : DensityOp (Fin 2) where
  toOp := Matrix.diagonal (fun i => ((![1, 0] : Fin 2 → ℝ) i : ℂ))
  posSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  trace_one := by
    simp [Matrix.trace, Fin.sum_univ_two]

private def oneOutcomeProjection : CQState Unit (Fin 2) where
  stateMap := fun _ => DensityOp.toSubDensityOp qubitProjection
  weight_le_one := by
    simp [DensityOp.toSubDensityOp, SubDensityOp.trace, qubitProjection, Matrix.trace,
      Fin.sum_univ_two]

private lemma qubitProjection_support_inv :
    qubitProjection.toOp ^ (-1 : ℝ) = qubitProjection.toOp := by
  rw [CFC.rpow_eq_cfc_real (qubitProjection.posSemidef).nonneg]
  change cfc (fun x : ℝ => x ^ (-1 : ℝ))
      (Matrix.diagonal (fun i => ((![1, 0] : Fin 2 → ℝ) i : ℂ))) = _
  rw [Math.SpectralTheory.cfc_diagonal_ofReal]
  congr 1
  funext i
  fin_cases i <;> norm_num

/-- The supported inverse fixes a rank-one projection even at its zero eigenvalue. -/
example : qubitProjection.toOp ^ (-1 : ℝ) = qubitProjection.toOp :=
  qubitProjection_support_inv

end QCryptLeanTest.MaxEntropyDomain
end
