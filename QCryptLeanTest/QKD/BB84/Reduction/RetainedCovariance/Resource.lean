import QCryptLeanTest.QKD.BB84.Reduction.RetainedExperiment.Layout
import Mathlib.Util.AssertNoSorry

/-!
# Nonzero accepted-entry regression for the retained key resource

This test evaluates the actual zero-round, one-bit retained key resource on a diagonal input at
ordered keys `(0, 1)`.  Its equal-key `(0, 0)` diagonal output has weight `1 / 2`, so the test
exercises key replacement rather than only an identity relabelling or a zero branch.

The resource coordinate equation is the library-specific finite realization of the ideal-resource
interface used with the permutation reduction of Christandl--König--Renner, arXiv:0809.3019,
Theorem 1 and Lemma 1.
-/

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace QKD.BB84.Reduction.RetainedCovarianceSupplement
open TypedLOCC

open RetainedAnalysisLayoutProbe

attribute [local instance] retainedAnalysisOutputDimNeZero

/-- Actual one-bit retained output layout at zero measured rounds. -/
abbrev zeroOneBitLayout :=
  (retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout

/-- Existing literal accepted output used to fix the public exit and residual coordinate. -/
def zeroOneBitBaseOutput : (retainedAnalysisBoundary 0 0 0 1 0 0).space :=
  zeroAcceptedRetainedOutput (0, 0)

/-- The base output is accepted with one output-key bit. -/
theorem zeroOneBitBaseOutput_isAccept :
    zeroOneBitLayout.disposition zeroOneBitBaseOutput.1 = .accept 1 := by
  exact zeroAcceptedRetainedOutput_disposition (0, 0)

/-- The event-dependent key type at the literal exit is the two-element one-bit key type. -/
theorem zeroOneBitKeyType_eq :
    (zeroOneBitLayout.disposition zeroOneBitBaseOutput.1).Key = Fin 2 := by
  simpa [TypedLOCC.BoundaryKeyLayout.Disposition.Key] using
    congrArg TypedLOCC.BoundaryKeyLayout.Disposition.Key zeroOneBitBaseOutput_isAccept

/-- Embed a literal one-bit key into the actual event-dependent key coordinate. -/
def zeroOneBitLayoutKey (b : Fin 2) :
    (zeroOneBitLayout.disposition zeroOneBitBaseOutput.1).Key :=
  cast zeroOneBitKeyType_eq.symm b

/-- The actual residual carried by the existing accepted output. -/
def zeroOneBitResidual : zeroOneBitLayout.Residual zeroOneBitBaseOutput.1 :=
  (zeroOneBitLayout.coordinates zeroOneBitBaseOutput.1 zeroOneBitBaseOutput.2).2.2

/-- Literal same-exit retained output with the supplied ordered Alice/Bob one-bit keys. -/
def zeroOneBitAcceptedPoint (alice bob : Fin 2) :
    (retainedAnalysisBoundary 0 0 0 1 0 0).space :=
  ⟨zeroOneBitBaseOutput.1,
    (zeroOneBitLayout.coordinates zeroOneBitBaseOutput.1).symm
      (zeroOneBitLayoutKey alice, zeroOneBitLayoutKey bob, zeroOneBitResidual)⟩

/-- The constructed point is read by the actual accepted-coordinate equivalence in Alice/Bob
order. -/
theorem zeroOneBitAcceptedPoint_coordinates (alice bob : Fin 2) :
    let h := zeroOneBitBaseOutput_isAccept
    let q := zeroOneBitAcceptedPoint alice bob
    zeroOneBitLayout.acceptCoordinates h q.2 = (alice, bob, zeroOneBitResidual) := by
  simp only [zeroOneBitAcceptedPoint, zeroOneBitLayoutKey,
    TypedLOCC.BoundaryKeyLayout.acceptCoordinates, Equiv.trans_apply]
  rw [(zeroOneBitLayout.coordinates zeroOneBitBaseOutput.1).apply_symm_apply]
  rfl

/-- Diagonal typed matrix unit at the accepted ordered-key point `(Alice, Bob) = (0, 1)`. -/
def zeroOneBitUnequalKeyInput :
    TypedLOCC.Op (retainedAnalysisBoundary 0 0 0 1 0 0).space :=
  Matrix.single (zeroOneBitAcceptedPoint 0 1) (zeroOneBitAcceptedPoint 0 1) 1

/-- The actual typed ideal resource replaces `(0, 1)` by the shared key `(0, 0)` with weight
`1 / 2`. -/
theorem zeroOneBitResource_typed_nonzero_entry :
    zeroOneBitLayout.ideal zeroOneBitUnequalKeyInput
        (zeroOneBitAcceptedPoint 0 0) (zeroOneBitAcceptedPoint 0 0) =
      (2 : ℂ)⁻¹ := by
  change zeroOneBitLayout.ideal zeroOneBitUnequalKeyInput
      ⟨zeroOneBitBaseOutput.1,
        (zeroOneBitLayout.coordinates zeroOneBitBaseOutput.1).symm
          (zeroOneBitLayoutKey 0, zeroOneBitLayoutKey 0, zeroOneBitResidual)⟩
      ⟨zeroOneBitBaseOutput.1,
        (zeroOneBitLayout.coordinates zeroOneBitBaseOutput.1).symm
          (zeroOneBitLayoutKey 0, zeroOneBitLayoutKey 0, zeroOneBitResidual)⟩ =
    (2 : ℂ)⁻¹
  rw [zeroOneBitLayout.ideal_coordinate_accept zeroOneBitUnequalKeyInput
    zeroOneBitBaseOutput.1 zeroOneBitBaseOutput_isAccept
    (zeroOneBitLayoutKey 0) (zeroOneBitLayoutKey 0)
    (zeroOneBitLayoutKey 0) (zeroOneBitLayoutKey 0)
    zeroOneBitResidual zeroOneBitResidual]
  have hentry
      (a b : (zeroOneBitLayout.disposition zeroOneBitBaseOutput.1).Key) :
      zeroOneBitUnequalKeyInput
          ⟨zeroOneBitBaseOutput.1,
            (zeroOneBitLayout.coordinates zeroOneBitBaseOutput.1).symm
              (a, b, zeroOneBitResidual)⟩
          ⟨zeroOneBitBaseOutput.1,
            (zeroOneBitLayout.coordinates zeroOneBitBaseOutput.1).symm
              (a, b, zeroOneBitResidual)⟩ =
        if a = zeroOneBitLayoutKey 0 ∧ b = zeroOneBitLayoutKey 1 then 1 else 0 := by
    by_cases ha : a = zeroOneBitLayoutKey 0
    · subst a
      by_cases hb : b = zeroOneBitLayoutKey 1
      · subst b
        simp [zeroOneBitUnequalKeyInput, zeroOneBitAcceptedPoint]
      · simp [zeroOneBitUnequalKeyInput, zeroOneBitAcceptedPoint,
          hb, Ne.symm hb]
    · simp [zeroOneBitUnequalKeyInput, zeroOneBitAcceptedPoint,
        ha, Ne.symm ha]
  simp_rw [hentry]
  rw [Fintype.sum_eq_single (zeroOneBitLayoutKey 0)]
  · rw [Fintype.sum_eq_single (zeroOneBitLayoutKey 1)]
    · simp
    · intro b hb
      simp [hb]
  · intro a ha
    simp [ha]

/-- Numeral encoding of the same diagonal accepted unequal-key input. -/
def zeroOneBitUnequalKeyNumeralInput :
    Quantum.Operators.Op (RetainedAnalysisOutputDim 0 0 0 1 0 0) :=
  Matrix.reindex
    (retainedAnalysisOutputEquiv 0 0 0 1 0 0)
    (retainedAnalysisOutputEquiv 0 0 0 1 0 0)
    zeroOneBitUnequalKeyInput

/-- The actual retained numeral resource has the required nonzero equal-key output coefficient. -/
theorem retainedAnalysisResource_nonzero_accepted_sameExit :
    retainedAnalysisResource 0 0 0 1 0 0 zeroOneBitUnequalKeyNumeralInput
        (retainedAnalysisOutputEquiv 0 0 0 1 0 0 (zeroOneBitAcceptedPoint 0 0))
        (retainedAnalysisOutputEquiv 0 0 0 1 0 0 (zeroOneBitAcceptedPoint 0 0)) =
      (2 : ℂ)⁻¹ := by
  change TypedLOCC.coordinateLinear
      (retainedAnalysisOutputEquiv 0 0 0 1 0 0)
      (retainedAnalysisOutputEquiv 0 0 0 1 0 0)
      zeroOneBitLayout.ideal zeroOneBitUnequalKeyNumeralInput
      (retainedAnalysisOutputEquiv 0 0 0 1 0 0 (zeroOneBitAcceptedPoint 0 0))
      (retainedAnalysisOutputEquiv 0 0 0 1 0 0 (zeroOneBitAcceptedPoint 0 0)) =
    (2 : ℂ)⁻¹
  rw [show zeroOneBitUnequalKeyNumeralInput = Matrix.reindex
      (retainedAnalysisOutputEquiv 0 0 0 1 0 0)
      (retainedAnalysisOutputEquiv 0 0 0 1 0 0)
      zeroOneBitUnequalKeyInput by rfl,
    TypedLOCC.coordinateLinear_reindex_apply]
  exact zeroOneBitResource_typed_nonzero_entry

/-- The computed key-replacement coefficient is nonzero. -/
theorem retainedAnalysisResource_nonzero_accepted_sameExit_ne_zero :
    retainedAnalysisResource 0 0 0 1 0 0 zeroOneBitUnequalKeyNumeralInput
        (retainedAnalysisOutputEquiv 0 0 0 1 0 0 (zeroOneBitAcceptedPoint 0 0))
        (retainedAnalysisOutputEquiv 0 0 0 1 0 0 (zeroOneBitAcceptedPoint 0 0)) ≠ 0 := by
  rw [retainedAnalysisResource_nonzero_accepted_sameExit]
  norm_num

end QKD.BB84.Reduction.RetainedCovarianceSupplement
