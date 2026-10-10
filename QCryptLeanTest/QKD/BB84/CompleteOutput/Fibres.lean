import QCryptLean.QKD.BB84.CompleteOutput
import Mathlib.Util.AssertNoSorry

/-!
# Tests for successful complete-output fibres

The fixtures inspect the explicit cast equivalence and successful fibre of
`QCryptLean.QKD.BB84.CompleteOutput` independently of the general fibre laws.  They cover
zero and full quotas, an arbitrary child coordinate, distinct raw controls and exits, unequal
accepted source keys, and the literal Unit/Unit shortage branch.
-/

noncomputable section

namespace QCryptLeanTest.BB84.CompleteOutput.Fibres

open _root_.LOCC
open QKD.BB84 _root_.LOCC.TwoParty QKD.BB84

/-- The canonical zero-round raw control. -/
def emptyControl : Sampling.RawControl 0 := Sampling.defaultRawControl 0

/-- Zero rounds and zero quotas select the success branch. -/
theorem emptyControl_hasZeroQuotas : Sampling.HasQuotas 0 0 0 emptyControl := by
  decide

/-- Two all-Z rounds supply a full two-position key quota. -/
def fullControl : Sampling.RawControl 2 := Sampling.defaultRawControl 2

/-- The full two-position quota is available in `fullControl`. -/
theorem fullControl_hasFullQuota : Sampling.HasQuotas 2 0 0 fullControl := by
  decide

/-- Opposite one-round bases with their unique empty shuffle. -/
def mismatchControl : Sampling.RawControl 1 :=
  ⟨(fun _ => Measurement.Basis.z), (fun _ => Measurement.Basis.x),
    Sampling.increasingShuffle (fun _ => Measurement.Basis.z)
      (fun _ => Measurement.Basis.x)⟩

/-- The mismatched one-round control cannot supply one key position. -/
theorem mismatchControl_hasShortage :
    ¬Sampling.HasQuotas 1 0 0 mismatchControl := by
  decide

/-- The all-X one-round raw control with its unique increasing shuffle. -/
def xControl : Sampling.RawControl 1 :=
  ⟨(fun _ => Measurement.Basis.x), (fun _ => Measurement.Basis.x),
    Sampling.increasingShuffle (fun _ => Measurement.Basis.x)
      (fun _ => Measurement.Basis.x)⟩

/-- The all-Z one-round raw control with its unique increasing shuffle. -/
def zControl : Sampling.RawControl 1 := Sampling.defaultRawControl 1

/-- The all-Z one-round control supplies its single key position. -/
theorem zControl_hasFullQuota : Sampling.HasQuotas 1 0 0 zControl := by
  decide

/-- Distinct basis strings give distinct complete late-selection exits. -/
theorem distinctControls_give_distinctLateExits :
    Measurement.lateSelectionExit 1 1 0 0 mismatchControl ≠
      Measurement.lateSelectionExit 1 1 0 0 xControl := by
  intro h
  have hcontrol := congrArg (QKD.BB84.lateSelectionExitEquiv 1 1 0 0) h
  have hm : QKD.BB84.lateSelectionExitEquiv 1 1 0 0
      (Measurement.lateSelectionExit 1 1 0 0 mismatchControl) = mismatchControl := by
    change (QKD.BB84.lateSelectionExitEquiv 1 1 0 0)
      ((QKD.BB84.lateSelectionExitEquiv 1 1 0 0).symm mismatchControl) = mismatchControl
    exact (QKD.BB84.lateSelectionExitEquiv 1 1 0 0).apply_symm_apply mismatchControl
  have hx : QKD.BB84.lateSelectionExitEquiv 1 1 0 0
      (Measurement.lateSelectionExit 1 1 0 0 xControl) = xControl := by
    change (QKD.BB84.lateSelectionExitEquiv 1 1 0 0)
      ((QKD.BB84.lateSelectionExitEquiv 1 1 0 0).symm xControl) = xControl
    exact (QKD.BB84.lateSelectionExitEquiv 1 1 0 0).apply_symm_apply xControl
  rw [hm, hx] at hcontrol
  have ha := congrArg (fun ω : Sampling.RawControl 1 => ω.a 0) hcontrol
  simp [mismatchControl, xControl] at ha

/-- The mismatch and all-Z basis strings give distinct complete late-selection exits. -/
theorem mismatchAndZ_give_distinctLateExits :
    Measurement.lateSelectionExit 1 1 0 0 mismatchControl ≠
      Measurement.lateSelectionExit 1 1 0 0 zControl := by
  intro h
  have hcontrol := congrArg (QKD.BB84.lateSelectionExitEquiv 1 1 0 0) h
  have hm : QKD.BB84.lateSelectionExitEquiv 1 1 0 0
      (Measurement.lateSelectionExit 1 1 0 0 mismatchControl) = mismatchControl := by
    change (QKD.BB84.lateSelectionExitEquiv 1 1 0 0)
      ((QKD.BB84.lateSelectionExitEquiv 1 1 0 0).symm mismatchControl) = mismatchControl
    exact (QKD.BB84.lateSelectionExitEquiv 1 1 0 0).apply_symm_apply mismatchControl
  have hz : QKD.BB84.lateSelectionExitEquiv 1 1 0 0
      (Measurement.lateSelectionExit 1 1 0 0 zControl) = zControl := by
    change (QKD.BB84.lateSelectionExitEquiv 1 1 0 0)
      ((QKD.BB84.lateSelectionExitEquiv 1 1 0 0).symm zControl) = zControl
    exact (QKD.BB84.lateSelectionExitEquiv 1 1 0 0).apply_symm_apply zControl
  rw [hm, hz] at hcontrol
  have hb := congrArg (fun ω : Sampling.RawControl 1 => ω.b 0) hcontrol
  change Measurement.Basis.x = Measurement.Basis.z at hb
  exact (by decide : Measurement.Basis.x ≠ Measurement.Basis.z) hb

/-- Explicit semantic data for the zero-round classical tail. -/
def zeroTailData : QKD.BB84.ClassicalTailData 0 0 1 0 (@Sampling.packedPESel 0 0 0) 0 where
  alicePE i := Fin.elim0 i
  bobPE i := Fin.elim0 i
  seedPair := (fun _ _ => 0, fun _ _ => 0)
  evTag := 0
  syndrome := 0

/-- A literal zero-round raw classical-tail output with the supplied accepted Alice/Bob keys. -/
def zeroAcceptedRawOutput (keys : Measurement.Bits 1 × Measurement.Bits 1) :
    RawClassicalTailOutput 0 0 1 0 (@Sampling.packedPESel 0 0 0) 0 :=
  (Boundary.graftSpaceEquiv
    (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@Sampling.packedPESel 0 0 0) 0)
    (fun _ => FinalStage.boundary 1)).symm
      ⟨(QKD.BB84.classicalTailExitEquiv 0 0 1 0
          (@Sampling.packedPESel 0 0 0) 0).symm zeroTailData,
        (FinalStage.outputEquiv 1).symm (Sum.inl keys)⟩

/-- The source output constructor contains the literal ordered accepted key pair. -/
theorem zeroAcceptedRawOutput_keys (keys : Measurement.Bits 1 × Measurement.Bits 1) :
    FinalStage.outputEquiv 1
        (Boundary.graftSpaceEquiv
          (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@Sampling.packedPESel 0 0 0) 0)
          (fun _ => FinalStage.boundary 1)
          (zeroAcceptedRawOutput keys)).2 =
      Sum.inl keys := by
  rw [show Boundary.graftSpaceEquiv
      (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@Sampling.packedPESel 0 0 0) 0)
      (fun _ => FinalStage.boundary 1) (zeroAcceptedRawOutput keys) =
        ⟨(QKD.BB84.classicalTailExitEquiv 0 0 1 0
          (@Sampling.packedPESel 0 0 0) 0).symm zeroTailData,
          (FinalStage.outputEquiv 1).symm (Sum.inl keys)⟩ by
      exact (Boundary.graftSpaceEquiv
        (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@Sampling.packedPESel 0 0 0) 0)
        (fun _ => FinalStage.boundary 1)).apply_symm_apply _]
  exact (FinalStage.outputEquiv 1).apply_symm_apply (Sum.inl keys)

/-- The explicit success embedding remains injective on outputs with swapped unequal keys. -/
theorem zeroQuotaEmbedding_distinguishesOrderedKeys :
    successCompleteOutputEmbedding 0 0 0 0 1 0 0 emptyControl
        emptyControl_hasZeroQuotas (zeroAcceptedRawOutput (0, 1)) ≠
      successCompleteOutputEmbedding 0 0 0 0 1 0 0 emptyControl
        emptyControl_hasZeroQuotas (zeroAcceptedRawOutput (1, 0)) := by
  apply (successCompleteOutputEmbedding 0 0 0 0 1 0 0 emptyControl
    emptyControl_hasZeroQuotas).injective.ne
  intro h
  have hk := congrArg (fun q =>
    FinalStage.outputEquiv 1
      (Boundary.graftSpaceEquiv
        (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@Sampling.packedPESel 0 0 0) 0)
        (fun _ => FinalStage.boundary 1) q).2) h
  have hk' : Sum.inl ((0, 1) : Measurement.Bits 1 × Measurement.Bits 1) = Sum.inl (1, 0) :=
    (zeroAcceptedRawOutput_keys (0, 1)).symm.trans
      (hk.trans (zeroAcceptedRawOutput_keys (1, 0)))
  exact (by decide : ((0, 1) : Measurement.Bits 1 × Measurement.Bits 1) ≠ (1, 0)) (Sum.inl.inj hk')

/-- The explicit success-child equivalence sends two swapped unequal-key tail points to distinct
child coordinates.  The `(0,1)` source is a deliberately unrestricted ambient accepted output,
not a claim that the physical protocol reaches unequal accepted keys. -/
theorem zeroSuccessEquiv_distinguishesAmbientTailPoints :
    successContinuationSpaceEquiv 0 0 0 0 1 0 0 emptyControl
        emptyControl_hasZeroQuotas (zeroAcceptedRawOutput (0, 1)) ≠
      successContinuationSpaceEquiv 0 0 0 0 1 0 0 emptyControl
        emptyControl_hasZeroQuotas (zeroAcceptedRawOutput (1, 0)) := by
  apply (successContinuationSpaceEquiv 0 0 0 0 1 0 0 emptyControl
    emptyControl_hasZeroQuotas).injective.ne
  intro h
  have hk := congrArg (fun q =>
    FinalStage.outputEquiv 1
      (Boundary.graftSpaceEquiv
        (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@Sampling.packedPESel 0 0 0) 0)
        (fun _ => FinalStage.boundary 1) q).2) h
  have hk' : Sum.inl ((0, 1) : Measurement.Bits 1 × Measurement.Bits 1) = Sum.inl (1, 0) :=
    (zeroAcceptedRawOutput_keys (0, 1)).symm.trans
      (hk.trans (zeroAcceptedRawOutput_keys (1, 0)))
  exact (by decide : ((0, 1) : Measurement.Bits 1 × Measurement.Bits 1) ≠ (1, 0)) (Sum.inl.inj hk')

/-- Inverting the explicit success-child cast recovers the concrete unequal-key ambient tail
point. -/
theorem zeroSuccessEquiv_inverse_recoversAmbientTailPoint :
    (successContinuationSpaceEquiv 0 0 0 0 1 0 0 emptyControl
      emptyControl_hasZeroQuotas).symm
        (successContinuationSpaceEquiv 0 0 0 0 1 0 0 emptyControl
          emptyControl_hasZeroQuotas (zeroAcceptedRawOutput (0, 1))) =
      zeroAcceptedRawOutput (0, 1) := by
  exact (successContinuationSpaceEquiv 0 0 0 0 1 0 0 emptyControl
    emptyControl_hasZeroQuotas).symm_apply_apply _

/-- Prefix an arbitrary zero-quota continuation child through the actual outer graft equivalence. -/
def zeroSuccessAmbientOfChild
    (c : (QKD.BB84.completeContinuationBoundary 0 0 0 0 1 0 0
      (Measurement.lateSelectionExit 0 0 0 0 emptyControl)).space) :
    (QKD.BB84.boundary 0 0 0 0 1 0 0).space :=
  (Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary 0 0 0 0)
    (QKD.BB84.completeContinuationBoundary 0 0 0 0 1 0 0)).symm
      ⟨Measurement.lateSelectionExit 0 0 0 0 emptyControl, c⟩

/-- Every explicitly prefixed child lies in the zero-quota success embedding range, proved directly
from the two explicit equivalences rather than the general range theorem being tested. -/
theorem zeroSuccessAmbientOfChild_mem_range
    (c : (QKD.BB84.completeContinuationBoundary 0 0 0 0 1 0 0
      (Measurement.lateSelectionExit 0 0 0 0 emptyControl)).space) :
    zeroSuccessAmbientOfChild c ∈ Set.range
      (successCompleteOutputEmbedding 0 0 0 0 1 0 0 emptyControl
        emptyControl_hasZeroQuotas) := by
  refine ⟨(successContinuationSpaceEquiv 0 0 0 0 1 0 0 emptyControl
    emptyControl_hasZeroQuotas).symm c, ?_⟩
  apply (Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary 0 0 0 0)
    (QKD.BB84.completeContinuationBoundary 0 0 0 0 1 0 0)).injective
  simp [zeroSuccessAmbientOfChild, successCompleteOutputEmbedding,
    successContinuationSpaceEquiv]
  rfl

/-- A literal mismatch-exit ambient output built through the promoted shortage equality. -/
def mismatchAmbientOutput :
    (QKD.BB84.boundary 1 1 0 0 0 0 0).space :=
  (Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary 1 1 0 0)
    (QKD.BB84.completeContinuationBoundary 1 1 0 0 0 0 0)).symm
      ⟨Measurement.lateSelectionExit 1 1 0 0 mismatchControl,
        Equiv.cast (congrArg Boundary.space
          (completeContinuationBoundary_shortage 1 1 0 0 0 0 0 mismatchControl
            mismatchControl_hasShortage).symm)
          ((Boundary.leafSpaceEquiv Measurement.lateSelectionAbortSystem).symm
            ((TwoParty.pairEquiv Unit Unit).symm ((), ())))⟩

/-- An ambient point at a distinct raw-control exit is outside the all-X success embedding range. -/
theorem mismatchAmbientOutput_not_mem_zSuccessRange :
    mismatchAmbientOutput ∉ Set.range
      (successCompleteOutputEmbedding 1 1 0 0 0 0 0 zControl zControl_hasFullQuota) := by
  rintro ⟨q, hq⟩
  have hpair := congrArg
    (Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary 1 1 0 0)
      (QKD.BB84.completeContinuationBoundary 1 1 0 0 0 0 0)) hq
  have hfirst := congrArg Sigma.fst hpair
  simp [mismatchAmbientOutput, successCompleteOutputEmbedding] at hfirst
  exact mismatchAndZ_give_distinctLateExits hfirst.symm

/-- The promoted shortage boundary law computes the concrete mismatched one-round child as abort. -/
theorem mismatchBoundary_isAbort :
    QKD.BB84.completeContinuationBoundary 1 1 0 0 0 0 0
        (Measurement.lateSelectionExit 1 1 0 0 mismatchControl) =
      .leaf Measurement.lateSelectionAbortSystem :=
  completeContinuationBoundary_shortage 1 1 0 0 0 0 0 mismatchControl
    mismatchControl_hasShortage

/-- The explicit success embedding prefixes the literal zero-round raw-control exit. -/
theorem zeroQuotaEmbedding_outerExit
    (q : RawClassicalTailOutput 0 0 1 0 (@Sampling.packedPESel 0 0 0) 0) :
    (Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary 0 0 0 0)
      (QKD.BB84.completeContinuationBoundary 0 0 0 0 1 0 0)
      (successCompleteOutputEmbedding 0 0 0 0 1 0 0 emptyControl
        emptyControl_hasZeroQuotas q)).1 =
      Measurement.lateSelectionExit 0 0 0 0 emptyControl := by
  exact congrArg Sigma.fst ((Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary 0 0 0 0)
    (QKD.BB84.completeContinuationBoundary 0 0 0 0 1 0 0)).apply_symm_apply _)

/-- The explicit full-quota embedding is a well-typed injection at the boundary edge case. -/
theorem fullQuotaEmbedding_exists :
    Nonempty
      (RawClassicalTailOutput 2 0 0 0 (@Sampling.packedPESel 2 0 0) 0 ↪
        (QKD.BB84.boundary 2 2 0 0 0 0 0).space) :=
  ⟨successCompleteOutputEmbedding 2 2 0 0 0 0 0 fullControl
    fullControl_hasFullQuota⟩

/-- The shortage constructor prefixes the actual `lateSelectionAbortAt` outer exit. -/
theorem shortageConstructor_usesActualAbortOuterExit :
    (Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary 1 1 0 0)
      (QKD.BB84.completeContinuationBoundary 1 1 0 0 0 0 0)
      (shortageCompleteOutput 1 1 0 0 0 0 0 mismatchControl
        mismatchControl_hasShortage)).1 =
      (Measurement.lateSelectionAbortAt 1 1 0 0 mismatchControl
        mismatchControl_hasShortage).1 := by
  simp [shortageCompleteOutput]

/-- The literal child coordinate used by `shortageCompleteOutput` has Unit/Unit local payload. -/
def literalAbortChild : (Boundary.leaf Measurement.lateSelectionAbortSystem).space :=
  (Boundary.leafSpaceEquiv Measurement.lateSelectionAbortSystem).symm
    ((TwoParty.pairEquiv Unit Unit).symm ((), ()))

/-- Reading the literal shortage child through the actual leaf and two-party equivalences gives
the unique Unit/Unit payload. -/
theorem literalAbortChild_hasUnitPayload :
    TwoParty.pairEquiv Unit Unit
        (Boundary.leafSpaceEquiv Measurement.lateSelectionAbortSystem literalAbortChild) =
      ((), ()) := by
  simp [literalAbortChild]

end QCryptLeanTest.BB84.CompleteOutput.Fibres
