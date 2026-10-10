import QCryptLeanTest.QKD.BB84.Reduction.RetainedExperiment.Reference
import Mathlib.Util.AssertNoSorry
import QCryptLean.QKD.BB84.CompleteOutput

/-!
# Tests for the direct retained-block analysis map

These fixtures inspect the explicit prefix, round-grouping direction, public output coordinate,
and boundary-derived resource.  They do not use a physical `N`-round factorization or a security
bound.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Reduction.RetainedAnalysisAudit
open _root_.LOCC

open _root_.LOCC.TwoParty
open QKD.BB84.FiniteKey
open Measurement Sampling
open RetainedAnalysisLayoutProbe RetainedAnalysisReferenceProbe

/-- Nonidentity permutation of two retained positions. -/
def swapTwo : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- The two-position swap is not the identity permutation. -/
theorem swapTwo_ne_refl : swapTwo ≠ Equiv.refl (Fin 2) := by
  decide

/-- At zero rounds, the explicit output decomposition and reconstruction are inverse. -/
theorem zeroOutputData_roundtrip :
    retainedAnalysisOutputDataEquiv 0 0 0 0 0 0
        ((retainedAnalysisOutputDataEquiv 0 0 0 0 0 0).symm
          (Equiv.refl (Fin 0),
            retainedAnalysisDefaultRawTailOutput 0 0 0 0 0 0)) =
      (Equiv.refl (Fin 0),
        retainedAnalysisDefaultRawTailOutput 0 0 0 0 0 0) := by
  exact (retainedAnalysisOutputDataEquiv 0 0 0 0 0 0).apply_symm_apply _

/-- At two retained positions, the output reconstruction and decomposition are inverse. -/
theorem twoRoundOutputData_roundtrip :
    (retainedAnalysisOutputDataEquiv 0 1 1 1 0 0).symm
        (retainedAnalysisOutputDataEquiv 0 1 1 1 0 0
          ((retainedAnalysisOutputDataEquiv 0 1 1 1 0 0).symm
            (swapTwo, retainedAnalysisDefaultRawTailOutput 0 1 1 1 0 0))) =
      (retainedAnalysisOutputDataEquiv 0 1 1 1 0 0).symm
        (swapTwo, retainedAnalysisDefaultRawTailOutput 0 1 1 1 0 0) := by
  exact (retainedAnalysisOutputDataEquiv 0 1 1 1 0 0).symm_apply_apply _

/-- The inverse prefix coordinate restores both singleton exits around the announced
permutation. -/
theorem swapTwo_prefixExit_hasLiteralUnits :
    (retainedAnalysisPrefixExitEquiv 2).symm swapTwo =
      ⟨swapTwo, ⟨(), ()⟩⟩ := by
  rfl

/-- Distinct inner permutations produce distinct prefix complete exits. -/
theorem swapTwo_prefixExit_ne_refl :
    (retainedAnalysisPrefixExitEquiv 2).symm swapTwo ≠
      (retainedAnalysisPrefixExitEquiv 2).symm (Equiv.refl (Fin 2)) := by
  exact (retainedAnalysisPrefixExitEquiv 2).symm.injective.ne swapTwo_ne_refl

/-- Complete retained exit obtained by prefixing the explicit default raw-tail abort exit with
the supplied inner permutation. -/
noncomputable def defaultRetainedExitAt
    (pi : Equiv.Perm (Fin 2)) :
    (retainedAnalysisBoundary 0 1 1 0 0 0).Exit :=
  (Boundary.graftExitEquiv
    (retainedAnalysisPrefixBoundary 2)
    (fun _ => QKD.BB84.rawClassicalTailBoundary 2 2 0 0
      (@Sampling.packedPESel 0 1 1) 0)).symm
      ⟨(retainedAnalysisPrefixExitEquiv 2).symm pi,
        (retainedAnalysisDefaultRawTailOutput 0 1 1 0 0 0).1⟩

/-- Distinct inner permutations remain distinct complete retained exits. -/
theorem defaultRetainedExitAt_injective : Function.Injective defaultRetainedExitAt := by
  intro pi pi' h
  have hbase := congrArg (fun e =>
    (Boundary.graftExitEquiv
      (retainedAnalysisPrefixBoundary 2)
      (fun _ => QKD.BB84.rawClassicalTailBoundary 2 2 0 0
        (@Sampling.packedPESel 0 1 1) 0) e).1) h
  change (retainedAnalysisPrefixExitEquiv 2).symm pi =
    (retainedAnalysisPrefixExitEquiv 2).symm pi' at hbase
  exact (retainedAnalysisPrefixExitEquiv 2).symm.injective hbase

/-- The actual boundary-derived resource kills entries between two different public inner
permutations. -/
theorem retainedResource_crossPermutation_zero
    (rho : Quantum.Operators.Op (retainedAnalysisBoundary 0 1 1 0 0 0).space)
    (a : ((retainedAnalysisBoundary 0 1 1 0 0 0).system
      (defaultRetainedExitAt (Equiv.refl (Fin 2)))).total)
    (b : ((retainedAnalysisBoundary 0 1 1 0 0 0).system
      (defaultRetainedExitAt swapTwo)).total) :
    (retainedAnalysisOutputLayout 0 1 1 0 0 0).toBoundaryKeyLayout.ideal rho
        ⟨defaultRetainedExitAt (Equiv.refl (Fin 2)), a⟩
        ⟨defaultRetainedExitAt swapTwo, b⟩ = 0 := by
  apply (retainedAnalysisOutputLayout 0 1 1 0 0 0).toBoundaryKeyLayout.ideal_crossExit_zero
  exact defaultRetainedExitAt_injective.ne swapTwo_ne_refl.symm

/-- Asymmetric Alice bits in two-round selected coordinates. -/
def asymmetricAliceBits : Fin 2 → Bit := fun i => if i = 0 then 1 else 0

/-- Zero Bob bits paired with the asymmetric Alice string. -/
def asymmetricBobBits : Fin 2 → Bit := fun _ => 0

/-- Structural regrouping puts Alice's nonzero first bit in the first signal's first component. -/
theorem asymmetricSelectedPair_roundCoordinate :
    (Quantum.Symmetry.pairFunctions Bit Bit 2).symm
      (asymmetricAliceBits, asymmetricBobBits) 0 = (1, 0) := by
  rfl

/-- An off-diagonal matrix unit on unequal round strings. -/
def asymmetricRoundMatrixUnit : Quantum.Operators.Op (Signals 2) :=
  Matrix.single
    ((Quantum.Symmetry.pairFunctions Bit Bit 2).symm
      (asymmetricAliceBits, asymmetricBobBits))
    ((Quantum.Symmetry.pairFunctions Bit Bit 2).symm
      (asymmetricBobBits, asymmetricAliceBits)) 1

/-- Regrouping uses the same structural equivalence on independent row and column strings. -/
theorem asymmetricRoundMatrixUnit_reindexed :
    Matrix.reindex (Quantum.Symmetry.pairFunctions Bit Bit 2)
      (Quantum.Symmetry.pairFunctions Bit Bit 2) asymmetricRoundMatrixUnit
      (asymmetricAliceBits, asymmetricBobBits) (asymmetricBobBits, asymmetricAliceBits) = 1 := by
  simp [asymmetricRoundMatrixUnit, Matrix.reindex_apply]

/-- The first PE position is a Z-test and therefore has the identity basis mask. -/
theorem packedMask_two_first_isIdentity :
    (if (@Sampling.packedPESel 0 1 1 (⟨0, by decide⟩ : Fin 2)) &&
        (@Sampling.packedXSel 0 1 1 (⟨0, by decide⟩ : Fin 2)) then
      basisUnitary .x else (1 : Matrix Bit Bit ℂ)) = 1 := by
  simp [Sampling.packedPESel, Sampling.packedXSel]

/-- The second PE position is an X-test and therefore has the Hadamard basis mask. -/
theorem packedMask_two_second_isHadamard :
    (if (@Sampling.packedPESel 0 1 1 (⟨1, by decide⟩ : Fin 2)) &&
        (@Sampling.packedXSel 0 1 1 (⟨1, by decide⟩ : Fin 2)) then
      basisUnitary .x else (1 : Matrix Bit Bit ℂ)) =
        basisUnitary .x := by
  simp [Sampling.packedPESel, Sampling.packedXSel]

/-- A fixed nonidentity Alice prefix branch carries exactly the one uniform permutation weight.
The two output coordinates are independent. -/
theorem swapTwo_alicePrefix_hasOneUniformWeight
    (rho : Quantum.Operators.Op (FinalStage.rawSystem 2).total)
    (q q' : ((QKD.BB84.Reduction.alicePermutationAnnouncement 2
      (@Sampling.packedPESel 0 1 1) (@Sampling.packedXSel 0 1 1)).out swapTwo).total) :
    ((QKD.BB84.Reduction.alicePermutationAnnouncement 2
        (@Sampling.packedPESel 0 1 1) (@Sampling.packedXSel 0 1 1)).liftedOperation
          (swapTwo, ()) rho) q q' =
      (Fintype.card (Equiv.Perm (Fin 2)) : ℂ)⁻¹ *
        (Matrix.conjLinearMap
          (localKrausLift (FinalStage.rawSystem 2) .alice (Bits 2)
            (QKD.BB84.Model.siftPermHalf 2
              (@Sampling.packedPESel 0 1 1)
              (@Sampling.packedXSel 0 1 1) swapTwo)) rho) q q' := by
  exact QKD.BB84.Reduction.alicePermutationAnnouncement_liftedOperation_apply
    2 (@Sampling.packedPESel 0 1 1) (@Sampling.packedXSel 0 1 1)
      swapTwo rho q q'

/-- Bob's matching fixed branch contributes no second probability factor. -/
theorem swapTwo_bobPrefix_hasNoSecondWeight
    (rho : Quantum.Operators.Op (FinalStage.rawSystem 2).total)
    (q q' : ((QKD.BB84.Reduction.bobSiftUnitAnnouncement 2
      (@Sampling.packedPESel 0 1 1) (@Sampling.packedXSel 0 1 1) swapTwo).out ()).total) :
    ((QKD.BB84.Reduction.bobSiftUnitAnnouncement 2
        (@Sampling.packedPESel 0 1 1) (@Sampling.packedXSel 0 1 1) swapTwo).liftedOperation
          () rho) q q' =
      (Matrix.conjLinearMap
        (localKrausLift (FinalStage.rawSystem 2)
          .bob (Bits 2)
          (QKD.BB84.Model.siftPermHalf 2
            (@Sampling.packedPESel 0 1 1)
            (@Sampling.packedXSel 0 1 1) swapTwo)) rho) q q' := by
  exact QKD.BB84.Reduction.bobSiftUnitAnnouncement_liftedOperation_apply
    2 (@Sampling.packedPESel 0 1 1) (@Sampling.packedXSel 0 1 1)
      swapTwo rho q q'

end QKD.BB84.Reduction.RetainedAnalysisAudit

/-- Execute the compiled test harness. -/
def main : IO Unit := pure ()
