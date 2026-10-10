import QCryptLeanTest.QKD.BB84.Reduction.RetainedExperiment.Layout
import QCryptLean.Quantum.Channels.AmplificationAlgebra

/-!
# External-reference probe for the retained resource

The physical output layout has a singleton base residual.  This probe therefore uses a separate
two-dimensional reference and checks the specified unequal-reference entry within the literal
abort exit.
-/

open Quantum.Channels

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Reduction.RetainedAnalysisReferenceProbe
open _root_.LOCC

open RetainedAnalysisLayoutProbe


/-- Public permutation/tail label of the literal retained abort output. -/
def zeroAbortOutputIndex : RetainedAnalysisOutput 0 0 0 1 0 0 :=
  retainedAnalysisOutputDataEquiv 0 0 0 1 0 0 zeroAbortRetainedOutput

/-- Matrix unit whose two axes use different external-reference coordinates while retaining the
same complete public abort output. -/
def abortExternalReferenceMatrixUnit :
    Quantum.Operators.Op (RetainedAnalysisOutput 0 0 0 1 0 0 × Fin 2) :=
  Matrix.single
    (zeroAbortOutputIndex, (0 : Fin 2))
    (zeroAbortOutputIndex, (1 : Fin 2)) 1

/-- The actual retained ideal resource preserves the specified unequal-reference matrix entry
inside the literal abort exit. -/
theorem retainedResource_preserves_abortExternalReference :
    mapTensorId
        (retainedAnalysisResource 0 0 0 1 0 0) (Fin 2)
        abortExternalReferenceMatrixUnit
        (zeroAbortOutputIndex, (0 : Fin 2))
        (zeroAbortOutputIndex, (1 : Fin 2)) = 1 := by
  rw [mapTensorId_apply]
  change retainedAnalysisResource 0 0 0 1 0 0
    (abortExternalReferenceMatrixUnit.submatrix (fun x => (x, 0)) (fun x => (x, 1)))
    (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0 zeroAbortRetainedOutput)
    (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0 zeroAbortRetainedOutput) = 1
  rw [retainedAnalysisResource_entry]
  rw [(retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout.ideal_coordinate_abort
    _ zeroAbortRetainedOutput.1 zeroAbortRetainedOutput_disposition
    zeroAbortRetainedOutput.2 zeroAbortRetainedOutput.2]
  simp [abortExternalReferenceMatrixUnit, zeroAbortOutputIndex]

end QKD.BB84.Reduction.RetainedAnalysisReferenceProbe
