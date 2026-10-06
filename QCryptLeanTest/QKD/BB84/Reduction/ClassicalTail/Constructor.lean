import QCryptLean.QKD.BB84.Reduction.ClassicalTail
import QCryptLean.QKD.BB84.TailOutput
import Mathlib.Util.AssertNoSorry

/-!
# Constructor tests for the direct retained BB84 tail

This test decodes the actual final-point constructor independently of the tail-kernel
theorem.  The calculation is structural bookkeeping for the retained classical program motivated
by Renner, arXiv:quant-ph/0512258v2, Section 6.5, and Nahar et al., arXiv:2403.11851, Section V.C;
it is not a security theorem from either paper.
-/

noncomputable section

namespace QKD.BB84.Reduction.DirectTailConstructorGate
open TypedLOCC

open TypedLOCC.TwoParty
open QKD.BB84.Engine
open QKD.BB84

/-- Decoding the actual final-point constructor returns the ordered Alice/Bob key slots when its
actual flag is zero, and returns the key-free `Unit` abort payload when that flag is nonzero. -/
theorem rawClassicalTailFinalPoint_decoder
    (n m ell ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ)
    (d : QKD.BB84.ClassicalTailData n m ell ellEV peSel leakEC)
    (x : (FinalStage.rawSystem n).total) :
    let flag := QKD.BB84.Model.acceptFlagOf n m ellEV peSel xSel leakEC ec delta Q
      d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob)
    finalStageOutputEquiv ell
        (rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q d x) =
      if flag = 0 then
        Sum.inl
          (QKD.BB84.Model.aliceKeySlotOf n ell peSel d.seedPair.1 flag (x .alice),
           QKD.BB84.Model.bobKeySlotOf n ell peSel leakEC ec d.seedPair.1 d.syndrome
             flag (x .bob))
      else Sum.inr () := by
  dsimp only
  by_cases hflag : QKD.BB84.Model.acceptFlagOf n m ellEV peSel xSel leakEC ec delta Q
      d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob) = 0
  · rw [if_pos hflag]
    let keys :=
      (QKD.BB84.Model.aliceKeySlotOf n ell peSel d.seedPair.1
          (QKD.BB84.Model.acceptFlagOf n m ellEV peSel xSel leakEC ec delta Q
            d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob)) (x .alice),
       QKD.BB84.Model.bobKeySlotOf n ell peSel leakEC ec d.seedPair.1 d.syndrome
          (QKD.BB84.Model.acceptFlagOf n m ellEV peSel xSel leakEC ec delta Q
            d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob)) (x .bob))
    change finalStageOutputEquiv ell
        (rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q d x) =
      Sum.inl keys
    have hpoint :
        rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q d x =
          (finalStageOutputEquiv ell).symm (Sum.inl keys) := by
      apply (Boundary.publicSpaceEquiv (FinalStage.flagBoundary ell)).injective
      simp only [rawClassicalTailFinalPoint, hflag, dif_pos,
        Equiv.apply_symm_apply, finalStageOutputEquiv, Equiv.coe_fn_symm_mk,
        Boundary.publicSpaceEquiv_apply]
      simp [keys, hflag, finalStageLeafExit, FinalStage.flagBoundary,
        Boundary.leafSpaceEquiv, TwoParty.pairEquiv]
      rfl
    rw [hpoint, (finalStageOutputEquiv ell).apply_symm_apply]
  · rw [if_neg hflag]
    have hflag_one : QKD.BB84.Model.acceptFlagOf n m ellEV peSel xSel leakEC ec delta Q
        d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob) = 1 :=
      Fin.eq_one_of_ne_zero _ hflag
    have hpoint :
        rawClassicalTailFinalPoint n m ell ellEV peSel xSel leakEC ec delta Q d x =
          (finalStageOutputEquiv ell).symm (Sum.inr ()) := by
      apply (Boundary.publicSpaceEquiv (FinalStage.flagBoundary ell)).injective
      simp only [rawClassicalTailFinalPoint, hflag_one, finalStageOutputEquiv,
        Equiv.coe_fn_symm_mk,
        Boundary.publicSpaceEquiv_apply]
      simp only [Boundary.system_announce, Fin.isValue, one_ne_zero, ↓dreduceDIte,
        eq_mpr_eq_cast, Sigma.mk.injEq]
      refine ⟨hflag_one, ?_⟩
      refine (cast_heq _ _).trans (heq_of_eq ?_)
      apply Sigma.ext (Unit.ext _ _)
      apply heq_of_eq
      funext p
      cases p <;> exact Unit.ext _ _
    rw [hpoint, (finalStageOutputEquiv ell).apply_symm_apply]

end QKD.BB84.Reduction.DirectTailConstructorGate
