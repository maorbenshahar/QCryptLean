import QCryptLeanTest.QKD.BB84.Reduction.RetainedExperiment.Layout
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction

/-!
# External-reference probe for the retained resource

The physical output layout has a singleton base residual.  This probe therefore uses a separate
two-dimensional reference and checks the specified unequal-reference entry within the literal
abort exit.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Reduction.RetainedAnalysisReferenceProbe
open TypedLOCC

open RetainedAnalysisLayoutProbe

attribute [local instance] retainedAnalysisOutputDimNeZero

/-- Numeral coordinate of the literal retained abort output. -/
def zeroAbortOutputIndex : Fin (RetainedAnalysisOutputDim 0 0 0 1 0 0) :=
  retainedAnalysisOutputEquiv 0 0 0 1 0 0 zeroAbortRetainedOutput

/-- Matrix unit whose two axes use different external-reference coordinates while retaining the
same complete public abort output. -/
def abortExternalReferenceMatrixUnit :
    Quantum.Operators.Op (RetainedAnalysisOutputDim 0 0 0 1 0 0 * 2) :=
  Matrix.single
    (finProdFinEquiv (zeroAbortOutputIndex, (0 : Fin 2)))
    (finProdFinEquiv (zeroAbortOutputIndex, (1 : Fin 2))) 1

/-- The actual retained ideal resource preserves the specified unequal-reference matrix entry
inside the literal abort exit. -/
theorem retainedResource_preserves_abortExternalReference :
    Quantum.Channels.mapTensorId
        (retainedAnalysisResource 0 0 0 1 0 0)
        abortExternalReferenceMatrixUnit
        (finProdFinEquiv (zeroAbortOutputIndex, (0 : Fin 2)))
        (finProdFinEquiv (zeroAbortOutputIndex, (1 : Fin 2))) = 1 := by
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  let e := retainedAnalysisOutputEquiv 0 0 0 1 0 0
  let q := zeroAbortRetainedOutput
  let rho : TypedLOCC.Op (retainedAnalysisBoundary 0 0 0 1 0 0).space :=
    Matrix.single q q 1
  have hblock :
      (Matrix.of fun i j =>
        abortExternalReferenceMatrixUnit
          (finProdFinEquiv (i, (0 : Fin 2)))
          (finProdFinEquiv (j, (1 : Fin 2)))) =
        Matrix.reindex e e rho := by
    calc
      _ = Matrix.single (e q) (e q) (1 : ℂ) := by
        ext i j
        by_cases hi : i = e q <;> by_cases hj : j = e q
        · subst i
          subst j
          simp [abortExternalReferenceMatrixUnit, zeroAbortOutputIndex, e, q,
            Matrix.single_apply]
        · simp [abortExternalReferenceMatrixUnit, zeroAbortOutputIndex, e, q,
            Matrix.single_apply, hi]
        · simp [abortExternalReferenceMatrixUnit, zeroAbortOutputIndex, e, q,
            Matrix.single_apply, hj]
        · simp [abortExternalReferenceMatrixUnit, zeroAbortOutputIndex, e, q,
            Matrix.single_apply]
      _ = Matrix.reindex e e rho := by
        ext i j
        simp only [rho, Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.single_apply, Equiv.eq_symm_apply]
  simp only [finProdFinEquiv_symm_apply,
    Quantum.Channels.finProdFinEquiv_apply_divNat,
    Quantum.Channels.finProdFinEquiv_apply_modNat]
  rw [hblock]
  change coordinateLinear e e
      (retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout.ideal
      (Matrix.reindex e e rho) (e q) (e q) = 1
  rw [coordinateLinear_reindex_apply]
  rw [(retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout.ideal_coordinate_abort
    rho q.1 zeroAbortRetainedOutput_disposition q.2 q.2]
  simp [rho]

end QKD.BB84.Reduction.RetainedAnalysisReferenceProbe
