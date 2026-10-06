import QCryptLean.QKD.BB84.Reduction.BasisErasure
import QCryptLean.QKD.BB84.Reduction.Factorization.Reconstruction
import QCryptLean.QKD.BB84.Reduction.RetainedBlocks
import QCryptLean.QKD.BB84.Measurement.LatePublicControl.BranchValues
import QCryptLean.QKD.BB84.Program

/-!
# The success sector of the retained-round factorization

Assume `nK + mZ + mX ≤ N` and let `omega` be a raw control that meets every quota
(`Sampling.HasQuotas`).  For every complex input operator and all classical-tail outputs `qa`,
`qb`, `retainedFactorization_success_sector` identifies the output entry of the BB84 program between
the successful complete outputs `successCompleteOutputEmbedding … omega hquota qa` and
`… qb` with the corresponding entry of
`reconstruction ∘ retainedControlLift (retainedAnalysisReal …) ∘ comparisonPre`.

The program side is evaluated through the success branch value of the sifting stage
(`Measurement.weightedLatePublicSelectionProgram_success_apply`), basis erasure
(`selectedBitsToRawProgram_denote_diag`) and the classical tail.  The factorized side is evaluated
through the success rows of the reconstruction Kraus family, the success coefficient of
`comparisonPre` and the reference-block formula of the retained experiment
(`retainedAnalysisReal_referenceBlock_eq_program`).  The two agree because the totalized
selection law disintegrates the raw-control law over retained subsets and inner permutations
(`Sampling.totalizedReconstructedStatusRawLaw_eq`).
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Reduction

open TypedLOCC QKD.BB84 QKD.BB84.Reduction
open QKD.BB84.Measurement QKD.BB84.Sampling
open QKD.BB84.Engine

attribute [local instance] retainedAnalysisRoundDimNeZero
attribute [local instance] retainedAnalysisOutputDimNeZero
attribute [local instance] QKD.BB84.boundaryCardNeZero
attribute [local instance] comparisonControlCardNeZero

/-- Entry of a conjugation `A · B · Aᴴ`, as the iterated coordinate sum. -/
private theorem mul_mul_conjTranspose_apply {m n : Type} [Fintype n] (A : Matrix m n ℂ)
    (B : Matrix n n ℂ) (i j : m) :
    (A * B * Aᴴ) i j = ∑ x, (∑ y, A i y * B y x) * star (A j x) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem successfulCompleteContinuation_output_apply
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (sigma : TypedLOCC.Op
      (Measurement.weightedSelectedRecordSystem N (nK + mZ + mX)).total)
    (qa qb : (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX)
      ell ellEV (@Sampling.packedPESel nK mZ mX) leakEC).space) :
    (QKD.BB84.successfulCompleteContinuation N nK mZ mX ell ellEV leakEC ec delta Q).denote
        sigma qa qb =
      if qa = qb then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec
                delta Q x st = qa then
              (Fintype.card (KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                (∑ qB : Measurement.SelectedLocalRecord N (nK + mZ + mX),
                  ∑ qA : Measurement.SelectedLocalRecord N (nK + mZ + mX),
                    if x .alice = QKD.BB84.selectedBitsToRaw qA ∧
                        x .bob = QKD.BB84.selectedBitsToRaw qB then
                      sigma ((TwoParty.pairEquiv _ _).symm (qA, qB))
                        ((TwoParty.pairEquiv _ _).symm (qA, qB))
                    else 0)
            else 0
      else 0 := by
  unfold QKD.BB84.successfulCompleteContinuation
  rw [Program.denote_graft]
  let B : Boundary TwoParty.Party := .leaf (FinalStage.rawSystem (nK + mZ + mX))
  let C : B.Exit → Boundary TwoParty.Party := fun _ =>
    QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX)
      ell ellEV (@Sampling.packedPESel nK mZ mX) leakEC
  have hrow (q : (C ()).space) :
      (Boundary.graftSpaceEquiv B C).symm ⟨(), q⟩ = q := by
    simpa only [B, C, Boundary.graftSpaceEquiv_leaf_apply] using
      (Equiv.symm_apply_apply (Boundary.graftSpaceEquiv B C) q)
  change (Program.controlledContinuation (fun _ : B.Exit =>
      QKD.BB84.rawClassicalTailProgram (nK + mZ + mX) (mZ + mX)
        ell ellEV (@Sampling.packedPESel nK mZ mX)
        (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q)
      ((QKD.BB84.selectedBitsToRawProgram N (nK + mZ + mX)).denote sigma)) qa qb = _
  conv_lhs =>
    rw [← hrow qa, ← hrow qb]
  rw [Program.controlledContinuation_sameExit]
  let tau : TypedLOCC.Op (FinalStage.rawSystem (nK + mZ + mX)).total :=
    (Boundary.exitKraus B () : Matrix _ _ ℂ)ᴴ *
      (QKD.BB84.selectedBitsToRawProgram N (nK + mZ + mX)).denote sigma *
      Boundary.exitKraus B ()
  change (QKD.BB84.rawClassicalTailProgram (nK + mZ + mX) (mZ + mX)
      ell ellEV (@Sampling.packedPESel nK mZ mX)
      (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q).denote
        tau qa qb = _
  rw [rawClassicalTailProgram_output_apply]
  by_cases hq : qa = qb
  · rw [if_pos hq, if_pos hq]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro st _
    by_cases hout : rawClassicalTailOutputPoint (nK + mZ + mX)
        (mZ + mX) ell ellEV (@Sampling.packedPESel nK mZ mX)
        (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = qa
    · rw [if_pos hout, if_pos hout]
      congr 1
      have htau : tau x x =
          (QKD.BB84.selectedBitsToRawProgram N (nK + mZ + mX)).denote sigma
            ⟨(), x⟩ ⟨(), x⟩ := by
        simp [tau, B, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Boundary.exitKraus_apply]
      rw [htau]
      exact selectedBitsToRawProgram_denote_diag N (nK + mZ + mX) sigma x
    · rw [if_neg hout, if_neg hout]
  · rw [if_neg hq, if_neg hq]

private theorem program_denote_success_eq_continuation
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (QKD.BB84.program pA pB N nK mZ mX ell ellEV leakEC
        ec delta Q).denote rho
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qa)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qb) =
    (QKD.BB84.completeContinuation N nK mZ mX ell ellEV leakEC ec delta Q
      (Measurement.lateSelectionExit N nK mZ mX omega)).denote
      ((Boundary.exitKraus (Measurement.lateSelectionBoundary N nK mZ mX)
          (Measurement.lateSelectionExit N nK mZ mX omega))ᴴ *
        (Measurement.weightedLatePublicSelectionProgram
          pA pB N nK mZ mX).denote rho *
        Boundary.exitKraus (Measurement.lateSelectionBoundary N nK mZ mX)
          (Measurement.lateSelectionExit N nK mZ mX omega))
      (successContinuationSpaceEquiv
        N nK mZ mX ell ellEV leakEC omega hquota qa)
      (successContinuationSpaceEquiv
        N nK mZ mX ell ellEV leakEC omega hquota qb) := by
  unfold QKD.BB84.program
  rw [Program.denote_graft]
  let G := Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
  let E := successContinuationSpaceEquiv
    N nK mZ mX ell ellEV leakEC omega hquota
  have hqa : successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
      omega hquota qa =
      G.symm ⟨Measurement.lateSelectionExit N nK mZ mX omega, E qa⟩ := by
    apply G.injective
    rw [graftSpaceEquiv_successCompleteOutputEmbedding]
    simp [G, E]
  have hqb : successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
      omega hquota qb =
      G.symm ⟨Measurement.lateSelectionExit N nK mZ mX omega, E qb⟩ := by
    apply G.injective
    rw [graftSpaceEquiv_successCompleteOutputEmbedding]
    simp [G, E]
  rw [hqa, hqb]
  change (Program.controlledContinuation
      (QKD.BB84.completeContinuation N nK mZ mX ell ellEV leakEC ec delta Q)
      ((Measurement.weightedLatePublicSelectionProgram
        pA pB N nK mZ mX).denote rho))
      (G.symm ⟨Measurement.lateSelectionExit N nK mZ mX omega, E qa⟩)
      (G.symm ⟨Measurement.lateSelectionExit N nK mZ mX omega, E qb⟩) = _
  rw [Program.controlledContinuation_sameExit]

private theorem program_denote_success_raw_formula
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (QKD.BB84.program pA pB N nK mZ mX ell ellEV leakEC
        ec delta Q).denote rho
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qa)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qb) =
      if qa = qb then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = qa then
              (Fintype.card (KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                (∑ qB : Measurement.SelectedLocalRecord N (nK + mZ + mX),
                  ∑ qA : Measurement.SelectedLocalRecord N (nK + mZ + mX),
                    if x .alice = QKD.BB84.selectedBitsToRaw qA ∧
                        x .bob = QKD.BB84.selectedBitsToRaw qB then
                      (Measurement.weightedLatePublicSelectionProgram
                        pA pB N nK mZ mX).denote rho
                        (Measurement.lateSelectionSuccessAt N nK mZ mX
                          omega hquota (qA, qB))
                        (Measurement.lateSelectionSuccessAt N nK mZ mX
                          omega hquota (qA, qB))
                    else 0)
            else 0
      else 0 := by
  rw [program_denote_success_eq_continuation]
  let e := Measurement.lateSelectionExit N nK mZ mX omega
  have he : QKD.BB84.lateSelectionExitEquiv N nK mZ mX e = omega := by
    change QKD.BB84.lateSelectionExitEquiv N nK mZ mX
      ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega) = omega
    exact (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply omega
  have hquota' : HasQuotas nK mZ mX
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX e) := by
    rw [he]
    exact hquota
  have hstart :
      (Measurement.lateSelectionBoundary N nK mZ mX).system e =
        Measurement.weightedSelectedRecordSystem N (nK + mZ + mX) := by
    rcases omega with ⟨aBasis, bBasis, order⟩
    change (Measurement.lateSelectionLeaf N nK mZ mX
      ⟨aBasis, bBasis, order⟩).system _ = _
    rw [QKD.BB84.lateSelectionLeaf_system, if_pos hquota]
  have hout :
      QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC e =
        QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC := by
    exact completeContinuationBoundary_success
      N nK mZ mX ell ellEV leakEC omega hquota
  unfold QKD.BB84.completeContinuation
  rw [dif_pos hquota']
  dsimp only
  change (cast
      (congrArg (fun R => Program R
        (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC e)) hstart.symm)
      (cast (congrArg (fun B => Program
          (Measurement.weightedSelectedRecordSystem N (nK + mZ + mX)) B) hout.symm)
        (QKD.BB84.successfulCompleteContinuation N nK mZ mX ell ellEV leakEC ec delta Q))).denote
      _ _ _ = _
  rw [Program.denote_cast_apply hstart rfl]
  rw [Program.denote_cast_apply rfl hout]
  simp only [Equiv.cast_refl, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_id_id,
      successContinuationSpaceEquiv, Equiv.cast_apply, Equiv.refl_apply, cast_cast, cast_eq,
      Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, _root_.mul_inv_rev]
  rw [successfulCompleteContinuation_output_apply]
  let ESystem := Equiv.cast (congrArg MultipartiteSystem.total hstart)
  have hpoint (qA qB : Measurement.SelectedLocalRecord N (nK + mZ + mX)) :
      (⟨e, ESystem.symm ((TwoParty.pairEquiv _ _).symm (qA, qB))⟩ :
          (Measurement.lateSelectionBoundary N nK mZ mX).space) =
        Measurement.lateSelectionSuccessAt N nK mZ mX
          omega hquota (qA, qB) := by
    rcases omega with ⟨aBasis, bBasis, order⟩
    let hleaf : Measurement.lateSelectionLeaf N nK mZ mX
        ⟨aBasis, bBasis, order⟩ =
          .leaf (Measurement.weightedSelectedRecordSystem N (nK + mZ + mX)) := by
      simp [Measurement.lateSelectionLeaf, hquota]
    apply (Boundary.publicSpaceEquiv (fun a : Fin N → Basis =>
      .announce (Fin N → Basis) fun b =>
        .announce (Shuffle a b) fun order =>
          Measurement.lateSelectionLeaf N nK mZ mX
            ⟨a, b, order⟩)).injective
    simp only [Boundary.publicSpaceEquiv, Equiv.sigmaAssoc, lateSelectionExit, eq_mpr_eq_cast,
        cast_eq, id_eq, hquota, Equiv.coe_fn_mk, lateSelectionSuccessAt, Boundary.leafSpaceEquiv,
        Equiv.coe_fn_symm_mk, Sigma.mk.injEq, heq_eq_eq, ↓reduceDIte, true_and, ESystem, e]
    have castBoundarySnd
        {B C : Boundary TwoParty.Party} (h : B = C) (z : B.space) :
        (cast (congrArg Boundary.space h) z).2 ≍ z.2 := by
      cases h
      rfl
    constructor
    · congr
      exact Subsingleton.elim _ _
    · change
        (cast (congrArg MultipartiteSystem.total hstart).symm
          ((TwoParty.pairEquiv _ _).symm (qA, qB))) ≍
        (cast (congrArg Boundary.space hleaf).symm
          ⟨(), (TwoParty.pairEquiv _ _).symm (qA, qB)⟩).2
      exact (cast_heq _ _).trans
        (castBoundarySnd hleaf.symm
          ⟨(), (TwoParty.pairEquiv _ _).symm (qA, qB)⟩).symm
  have hdiag (qA qB : Measurement.SelectedLocalRecord N (nK + mZ + mX)) :
      (((Boundary.exitKraus (Measurement.lateSelectionBoundary N nK mZ mX) e)ᴴ *
          (Measurement.weightedLatePublicSelectionProgram
            pA pB N nK mZ mX).denote rho *
          Boundary.exitKraus (Measurement.lateSelectionBoundary N nK mZ mX) e).submatrix
        ESystem.symm ESystem.symm)
        ((TwoParty.pairEquiv _ _).symm (qA, qB))
        ((TwoParty.pairEquiv _ _).symm (qA, qB)) =
      (Measurement.weightedLatePublicSelectionProgram
        pA pB N nK mZ mX).denote rho
        (Measurement.lateSelectionSuccessAt N nK mZ mX
          omega hquota (qA, qB))
        (Measurement.lateSelectionSuccessAt N nK mZ mX
          omega hquota (qA, qB)) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Boundary.exitKraus_apply, hpoint]
  have hdiag' (qA qB : Measurement.SelectedLocalRecord N (nK + mZ + mX)) :
      (((Boundary.exitKraus (Measurement.lateSelectionBoundary N nK mZ mX)
            (Measurement.lateSelectionExit N nK mZ mX omega))ᴴ *
          (Measurement.weightedLatePublicSelectionProgram
            pA pB N nK mZ mX).denote rho *
          Boundary.exitKraus (Measurement.lateSelectionBoundary N nK mZ mX)
            (Measurement.lateSelectionExit N nK mZ mX omega)).submatrix
        (Equiv.cast (congrArg MultipartiteSystem.total hstart)).symm
        (Equiv.cast (congrArg MultipartiteSystem.total hstart)).symm)
        ((TwoParty.pairEquiv _ _).symm (qA, qB))
        ((TwoParty.pairEquiv _ _).symm (qA, qB)) =
      (Measurement.weightedLatePublicSelectionProgram
        pA pB N nK mZ mX).denote rho
        (Measurement.lateSelectionSuccessAt N nK mZ mX
          omega hquota (qA, qB))
        (Measurement.lateSelectionSuccessAt N nK mZ mX
          omega hquota (qA, qB)) := by
    simpa only [e, ESystem] using hdiag qA qB
  simp_rw [hdiag']
  simp

private theorem weightedLatePublicSelection_selectedBits_sum
    (pA pB : PMF Basis) (N nK mZ mX : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total)
    (x : (FinalStage.rawSystem (nK + mZ + mX)).total) :
    (∑ qB : Measurement.SelectedLocalRecord N (nK + mZ + mX),
      ∑ qA : Measurement.SelectedLocalRecord N (nK + mZ + mX),
        if x .alice = QKD.BB84.selectedBitsToRaw qA ∧
            x .bob = QKD.BB84.selectedBitsToRaw qB then
          (Measurement.weightedLatePublicSelectionProgram
            pA pB N nK mZ mX).denote rho
            (Measurement.lateSelectionSuccessAt N nK mZ mX
              omega hquota (qA, qB))
            (Measurement.lateSelectionSuccessAt N nK mZ mX
              omega hquota (qA, qB))
        else 0) =
      (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ *
        ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB omega.b).toReal : ℂ) *
        fixedBasisSelectedBornBlock (selectedEmbedding omega hquota)
          omega.a omega.b
          ((retainedBitCoordinateEquiv (nK + mZ + mX)).symm (x .alice))
          ((retainedBitCoordinateEquiv (nK + mZ + mX)).symm (x .bob))
          (Matrix.of fun i j =>
            (reindexOp (weightedScheduleUnitInputEquiv N) rho) i.1 j.1) () () := by
  let qA0 : Measurement.SelectedLocalRecord N (nK + mZ + mX) :=
    (omega.a,
      (retainedBitCoordinateEquiv (nK + mZ + mX)).symm (x .alice))
  let qB0 : Measurement.SelectedLocalRecord N (nK + mZ + mX) :=
    (omega.b,
      (retainedBitCoordinateEquiv (nK + mZ + mX)).symm (x .bob))
  have hreference :
      selectedReferenceInputBlock
          (Matrix.of fun i j =>
            (reindexOp (weightedScheduleUnitInputEquiv N) rho) i.1 j.1)
          () () =
        reindexOp (weightedScheduleUnitInputEquiv N) rho := by
    rfl
  simp_rw [Measurement.weightedLatePublicSelectionProgram_success_apply]
  simp only [Measurement.selectedMeasurementLaw]
  rw [Finset.sum_eq_single qB0]
  · rw [Finset.sum_eq_single qA0]
    · simp [qA0, qB0, QKD.BB84.selectedBitsToRaw, retainedBitCoordinateEquiv,
        fixedBasisSelectedBornBlock, hreference]
      ring
    · intro qA _ hne
      by_cases hbits : x .alice = QKD.BB84.selectedBitsToRaw qA
      · have hbase : qA.1 ≠ omega.a := by
          intro hb
          apply hne
          apply Prod.ext
          · exact hb
          · apply (retainedBitCoordinateEquiv (nK + mZ + mX)).injective
            simpa [qA0, QKD.BB84.selectedBitsToRaw, retainedBitCoordinateEquiv] using hbits.symm
        simp [hbits, hbase]
      · simp [hbits]
    · simp
  · intro qB _ hne
    by_cases hbits : x .bob = QKD.BB84.selectedBitsToRaw qB
    · have hbase : qB.1 ≠ omega.b := by
        intro hb
        apply hne
        apply Prod.ext
        · exact hb
        · apply (retainedBitCoordinateEquiv (nK + mZ + mX)).injective
          simpa [qB0, QKD.BB84.selectedBitsToRaw, retainedBitCoordinateEquiv] using hbits.symm
      simp [hbits, hbase]
    · simp [hbits]
  · simp

private theorem totalized_success_mass_formula
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) (omega : RawControl N)
    (hquota : HasQuotas nK mZ mX omega) :
    (∑ S : Set.powersetCard (Fin N) (nK + mZ + mX),
      ∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
        selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)) =
      rawControlLaw N pA pB omega := by
  have hpoint := congrArg
    (fun P : PMF (Bool × RawControl N) => P (true, omega))
    (totalizedReconstructedStatusRawLaw_eq N nK mZ mX pA pB hN)
  change totalizedReconstructedStatusRawLaw N nK mZ mX pA pB hN
      (true, omega) =
    taggedRawControlLaw N nK mZ mX pA pB (true, omega) at hpoint
  have htagged :
      taggedRawControlLaw N nK mZ mX pA pB (true, omega) =
        rawControlLaw N pA pB omega := by
    rw [taggedRawControlLaw, PMF.map_apply]
    simp only [tsum_fintype]
    rw [Finset.sum_eq_single omega]
    · simp [hquota]
    · intro x _ hne
      simp [show omega ≠ x by exact Ne.symm hne]
    · simp
  rw [htagged] at hpoint
  by_cases hn : nK + mZ + mX = 0
  · have hnK : nK = 0 := by omega
    have hmZ : mZ = 0 := by omega
    have hmX : mX = 0 := by omega
    subst nK
    subst mZ
    subst mX
    rw [totalizedReconstructedStatusRawLaw, dif_pos rfl] at hpoint
    simp only [PMF.bind_apply, PMF.pure_apply, tsum_fintype,
      Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero] at hpoint
    simpa [selectionSuccessMass_zero_quotas] using hpoint
  · rw [totalizedReconstructedStatusRawLaw, dif_neg hn] at hpoint
    simp only [PMF.bind_apply, PMF.pure_apply, tsum_fintype,
      Fintype.sum_bool, selectionStatusLaw, PMF.ofFintype_apply,
      selectionStatusWeight, Bool.false_eq_true, if_false, if_true,
      Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero] at hpoint
    simp_rw [Finset.mul_sum] at hpoint
    simp only [mul_ite, mul_zero, Bool.true_eq_false, false_and,
      if_false, Finset.sum_const_zero, add_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at hpoint
    simpa only [mul_assoc] using hpoint

private theorem totalized_success_complex_mass_formula
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) (omega : RawControl N)
    (hquota : HasQuotas nK mZ mX omega) :
    (∑ S : Set.powersetCard (Fin N) (nK + mZ + mX),
      ∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
        (((selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)).toReal : ℂ))) =
      ((rawControlLaw N pA pB omega).toReal : ℂ) := by
  have hsuccess : selectionSuccessMass N nK mZ mX pA pB ≠ ⊤ :=
    selectionSuccessMass_ne_top N nK mZ mX pA pB
  have hterm (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (pi : Equiv.Perm (Fin (nK + mZ + mX))) :
      selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hsuccess
        ((uniformRetainedSubset hN).apply_ne_top S))
      (ENNReal.mul_ne_top ((uniformInnerPerm _).apply_ne_top pi)
        ((totalSelectedControlKernel N nK mZ mX pA pB _).apply_ne_top omega))
  have hinner (S : Set.powersetCard (Fin N) (nK + mZ + mX)) :
      (∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
        selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)) ≠ ⊤ := by
    exact (ENNReal.sum_ne_top).2 (fun pi _ => hterm S pi)
  have hmass := totalized_success_mass_formula N nK mZ mX pA pB
    hN omega hquota
  have hreal := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_sum (fun S _ => hinner S)] at hreal
  simp_rw [ENNReal.toReal_sum (fun pi _ => hterm _ pi)] at hreal
  exact_mod_cast hreal

private theorem totalized_success_native_formula
    {R : Type} [Fintype R] [DecidableEq R]
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) (omega : RawControl N)
    (hquota : HasQuotas nK mZ mX omega)
    (uA uB : Fin (nK + mZ + mX) → Bit)
    (W : TypedLOCC.Op (((Fin N → Bit) × (Fin N → Bit)) × R)) (s t : R) :
    (∑ S : Set.powersetCard (Fin N) (nK + mZ + mX),
      ∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
        ((selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)).toReal : ℂ) *
        nativeSelectedBornBlock S
          (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) pi uA uB W s t) =
      ((rawControlLaw N pA pB omega).toReal : ℂ) *
        fixedBasisSelectedBornBlock (selectedEmbedding omega hquota)
          omega.a omega.b uA uB W s t := by
  have hterm (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (pi : Equiv.Perm (Fin (nK + mZ + mX))) :
      ((selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)).toReal : ℂ) *
        nativeSelectedBornBlock S
          (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) pi uA uB W s t =
        ((selectionSuccessMass N nK mZ mX pA pB *
          uniformRetainedSubset hN S *
          (uniformInnerPerm (nK + mZ + mX) pi *
            totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)).toReal : ℂ) *
        fixedBasisSelectedBornBlock (selectedEmbedding omega hquota)
          omega.a omega.b uA uB W s t := by
    by_cases hkernel : totalSelectedControlKernel N nK mZ mX pA pB
        (Math.FiniteEmbedding.joinSubsetPerm S pi) omega = 0
    · simp [hkernel]
    · have hpositive : 0 < totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi) omega :=
        pos_iff_ne_zero.mpr hkernel
      have hselect := totalSelectedControlKernel_select N nK mZ mX pA pB
        (Math.FiniteEmbedding.joinSubsetPerm S pi) omega hpositive
      have hactual : select nK mZ mX omega =
          some (selectedEmbedding omega hquota) := by
        simp [select, hquota]
      rw [hactual] at hselect
      have hembedding : selectedEmbedding omega hquota =
          Math.FiniteEmbedding.joinSubsetPerm S pi :=
        Option.some.inj hselect
      rw [selectedMeasurement_joinSubsetPerm_eq_native omega hquota S pi
        hembedding uA uB W s t]
  simp_rw [hterm]
  simp_rw [← Finset.sum_mul]
  rw [totalized_success_complex_mass_formula N nK mZ mX pA pB
    hN omega hquota]

private theorem program_denote_success_output_formula
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (QKD.BB84.program pA pB N nK mZ mX ell ellEV leakEC
        ec delta Q).denote rho
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qa)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qb) =
      if qa = qb then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX)
                ell ellEV (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = qa then
              (Fintype.card (KeyHashSeedPairEV
                (nK + mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                (((rawControlLaw N pA pB omega).toReal : ℂ) *
                  fixedBasisSelectedBornBlock (selectedEmbedding omega hquota)
                    omega.a omega.b
                    ((retainedBitCoordinateEquiv
                      (nK + mZ + mX)).symm (x .alice))
                    ((retainedBitCoordinateEquiv
                      (nK + mZ + mX)).symm (x .bob))
                    (Matrix.of fun i j =>
                      (reindexOp (weightedScheduleUnitInputEquiv N) rho)
                        i.1 j.1) () ())
            else 0
      else 0 := by
  rw [program_denote_success_raw_formula]
  simp_rw [weightedLatePublicSelection_selectedBits_sum]
  rw [rawControlLaw_toReal_eq]

private theorem reconstruction_success
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (mid : Quantum.Operators.Op
      (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC *
        Fintype.card (ComparisonControl N (nK + mZ + mX)))) :
    reconstruction N nK mZ mX ell ellEV leakEC pA pB mid
        ((Fintype.equivFin _)
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota qa))
        ((Fintype.equivFin _)
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota qb)) =
      ∑ S, ∑ pi,
        (((totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi) omega).toReal : ℂ) *
        Matrix.reindex
          (reconstructionInputEquiv N nK mZ mX ell ellEV leakEC).symm
          (reconstructionInputEquiv N nK mZ mX ell ellEV leakEC).symm mid
          (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
              ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
                (pi, qa)), Sum.inl S)
          (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
              ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
                (pi, qb)), Sum.inl S)) := by
  have hfailureRow
      (j : Fin (nK + mZ + mX))
      (r : Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC))
      (eta : FailureControlSupport N nK mZ mX pA pB j)
      (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC)
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB
          (Sum.inr ⟨j, r, eta⟩)
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota q) x = 0 := by
    change reconstructionShortageKraus N nK mZ mX ell ellEV leakEC
        pA pB j r eta
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota q) x = 0
    unfold reconstructionShortageKraus
    rw [Matrix.smul_apply]
    rw [Matrix.single_apply_of_row_ne]
    · exact smul_zero _
    · intro heq
      have hrc := congrArg (fun y =>
        QKD.BB84.lateSelectionExitEquiv N nK mZ mX
          ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC) y.1).1) heq
      dsimp only at hrc
      rw [shortageCompleteOutput_rawControl] at hrc
      rw [successCompleteOutputEmbedding_exit] at hrc
      unfold successExitMap at hrc
      rw [Equiv.apply_symm_apply] at hrc
      change eta.1 = QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        (Measurement.lateSelectionExit N nK mZ mX omega) at hrc
      have hrc' : eta.1 = omega := hrc.trans
        ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).right_inv omega)
      exact (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j eta)
        (hrc' ▸ hquota)
  let EPost := reconstructionInputEquiv N nK mZ mX ell ellEV leakEC
  let sigma : Matrix
      (ReconstructionInput N nK mZ mX ell ellEV leakEC)
      (ReconstructionInput N nK mZ mX ell ellEV leakEC) ℂ :=
    Matrix.reindex EPost.symm EPost.symm mid
  have hmid : mid = Matrix.reindex EPost EPost sigma := by
    simp [sigma, Matrix.reindex_apply]
  unfold reconstruction
  rw [hmid, coordinateLinear_reindex_apply]
  unfold Instrument.channel Instrument.operation
  -- entry of the Kraus sum `∑ₒ Kₒ σ Kₒᴴ`, one conjugation at a time
  simp only [Fintype.sum_unique, LinearMap.sum_apply, Matrix.sum_apply, matrixConjLinear_apply,
    ← Finset.sum_mul]
  simp only [reconstructionInstrument]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sigma]
  simp_rw [hfailureRow]
  simp only [zero_mul, Finset.sum_const_zero, star_zero, mul_zero, add_zero]
  simp only [EPost, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.symm_apply_apply]
  change _ = ∑ S, ∑ pi,
    (((totalSelectedControlKernel N nK mZ mX pA pB
      (Math.FiniteEmbedding.joinSubsetPerm S pi) omega).toReal : ℂ) *
      sigma
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
            ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
              (pi, qa)), Sum.inl S)
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
            ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
              (pi, qb)), Sum.inl S))
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro pi _
  let E := retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
  let D := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
  let xA : ReconstructionInput N nK mZ mX ell ellEV leakEC :=
    (E (D.symm (pi, qa)), Sum.inl S)
  let xB : ReconstructionInput N nK mZ mX ell ellEV leakEC :=
    (E (D.symm (pi, qb)), Sum.inl S)
  let K := totalSelectedControlKernel N nK mZ mX pA pB
    (Math.FiniteEmbedding.joinSubsetPerm S pi)
  change _ = ((K omega).toReal : ℂ) * sigma xA xB
  have hsuccessRaw
      (xi : RawControl N) (hxi : HasQuotas nK mZ mX xi)
      (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC) :
      QKD.BB84.lateSelectionExitEquiv N nK mZ mX
          ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC)
            (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
              xi hxi q).1).1 = xi := by
    rw [successCompleteOutputEmbedding_exit]
    unfold successExitMap
    rw [Equiv.apply_symm_apply]
    exact (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).right_inv xi
  have hrow_of_control_ne
      (eta : SelectedControlSupport N nK mZ mX pA pB S pi)
      (heta : eta.1 ≠ omega)
      (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC)
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB
          (Sum.inl ⟨S, pi, eta⟩)
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota q) x = 0 := by
    change reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC
        pA pB S pi eta
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota q) x = 0
    unfold reconstructionSuccessKraus
    dsimp only
    split
    · rename_i hc
      exfalso
      have hrc := congrArg (fun y =>
        QKD.BB84.lateSelectionExitEquiv N nK mZ mX
          ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC) y.1).1) hc.2.2
      dsimp only at hrc
      rw [hsuccessRaw omega hquota q,
        hsuccessRaw eta.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi eta)
          (D (E.symm x.1)).2] at hrc
      exact heta hrc.symm
    · rfl
  by_cases hpos : 0 < K omega
  · let eta0 : SelectedControlSupport N nK mZ mX pA pB S pi :=
      ⟨omega, hpos⟩
    have hrow_self
        (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC)
        (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
        reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB
            (Sum.inl ⟨S, pi, eta0⟩)
            (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
              omega hquota q) x =
          if x = (E (D.symm (pi, q)), Sum.inl S) then
            Instrument.weightedChoiceScale K omega else 0 := by
      change reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC
          pA pB S pi eta0
            (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
              omega hquota q) x = _
      unfold reconstructionSuccessKraus
      dsimp only
      by_cases hx : x = (E (D.symm (pi, q)), Sum.inl S)
      · subst x
        simp [E, D, K, eta0]
      · rw [if_neg hx]
        split
        · rename_i hc
          exfalso
          apply hx
          rcases hc with ⟨hcS, hcpi, hcout⟩
          apply Prod.ext
          · have htail :
                q = (D (E.symm x.1)).2 := by
              apply (successCompleteOutputEmbedding
                N nK mZ mX ell ellEV leakEC omega hquota).injective
              simpa [eta0] using hcout
            have hdata : D (E.symm x.1) = (pi, q) := by
              apply Prod.ext
              · exact hcpi
              · exact htail.symm
            calc
              x.1 = E (E.symm x.1) := (E.apply_symm_apply x.1).symm
              _ = E (D.symm (pi, q)) := by
                rw [← hdata, D.symm_apply_apply]
          · exact hcS
        · rfl
    rw [Finset.sum_eq_single eta0]
    · rw [Finset.sum_eq_single xB]
      · rw [hrow_self qb xB, if_pos rfl]
        rw [Finset.sum_eq_single xA]
        · rw [hrow_self qa xA, if_pos rfl]
          calc
            (Instrument.weightedChoiceScale K omega * sigma xA xB) *
                star (Instrument.weightedChoiceScale K omega) =
              (star (Instrument.weightedChoiceScale K omega) *
                Instrument.weightedChoiceScale K omega) * sigma xA xB := by ring
            _ = ((K omega).toReal : ℂ) * sigma xA xB := by
              rw [Instrument.weightedChoiceScale_star_mul]
        · intro x _ hx
          rw [hrow_self qa x, if_neg hx, zero_mul]
        · exact fun h => absurd (Finset.mem_univ _) h
      · intro x _ hx
        rw [hrow_self qb x, if_neg hx, star_zero, mul_zero]
      · exact fun h => absurd (Finset.mem_univ _) h
    · intro eta _ heta
      have hcontrol : eta.1 ≠ omega := by
        intro h
        apply heta
        apply Subtype.ext
        exact h
      simp_rw [hrow_of_control_ne eta hcontrol]
      simp
    · simp
  · have hzero : K omega = 0 := bot_unique (le_of_not_gt hpos)
    have hzreal : ((K omega).toReal : ℂ) = 0 := by
      rw [hzero, ENNReal.toReal_zero, Complex.ofReal_zero]
    rw [hzreal, zero_mul]
    apply Finset.sum_eq_zero
    intro eta _
    have hcontrol : eta.1 ≠ omega := by
      intro h
      apply hpos
      rw [← h]
      exact eta.2
    simp_rw [hrow_of_control_ne eta hcontrol]
    simp only [zero_mul, Finset.sum_const_zero, star_zero, mul_zero]

private theorem retainedMid_success
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : TypedLOCC.Op (ComparisonPreInput N))
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (q q' : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space) :
    let pre := comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex (comparisonPreInputEquiv N)
        (comparisonPreInputEquiv N) rho)
    let mid := retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
      (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q) pre
    let EPost := reconstructionInputEquiv N nK mZ mX ell ellEV leakEC
    let sigma := Matrix.reindex EPost.symm EPost.symm mid
    let block : Quantum.Operators.Op (4 ^ (nK + mZ + mX)) :=
      Matrix.of fun i j =>
        (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).channel rho
            ((retainedSelectedPairToRoundEquiv
              (nK + mZ + mX)).symm i)
            ((retainedSelectedPairToRoundEquiv
              (nK + mZ + mX)).symm j)
    sigma
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC q, Sum.inl S)
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC q', Sum.inl S) =
      comparisonPreSuccessCoefficient N nK mZ mX pA pB *
        retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q block
          (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC q)
          (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC q') := by
  dsimp only
  unfold retainedControlLift reconstructionInputEquiv
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm]
  change Quantum.Channels.mapTensorId
      (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)
      (Matrix.reindex
        (comparisonPreToRetainedControlEquiv N (nK + mZ + mX))
        (comparisonPreToRetainedControlEquiv N (nK + mZ + mX))
        (comparisonPre N nK mZ mX pA pB hN
          (Matrix.reindex (comparisonPreInputEquiv N)
            (comparisonPreInputEquiv N) rho)))
      (finProdFinEquiv
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC q,
          Fintype.equivFin _ (Sum.inl S : ComparisonControl N _)))
      (finProdFinEquiv
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC q',
          Fintype.equivFin _ (Sum.inl S : ComparisonControl N _))) = _
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  simp only [finProdFinEquiv_symm_apply,
    Quantum.Channels.finProdFinEquiv_apply_divNat,
    Quantum.Channels.finProdFinEquiv_apply_modNat]
  let regrouped := Matrix.reindex
    (comparisonPreToRetainedControlEquiv N (nK + mZ + mX))
    (comparisonPreToRetainedControlEquiv N (nK + mZ + mX))
    (comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex (comparisonPreInputEquiv N)
        (comparisonPreInputEquiv N) rho))
  let block : Quantum.Operators.Op (4 ^ (nK + mZ + mX)) :=
    Matrix.of fun i j =>
      (selectedInputMarginalInstrument
        (increasingSubsetEmbedding S)).channel rho
          ((retainedSelectedPairToRoundEquiv
            (nK + mZ + mX)).symm i)
          ((retainedSelectedPairToRoundEquiv
            (nK + mZ + mX)).symm j)
  have hregroup (i j : Fin (4 ^ (nK + mZ + mX))) :
      regrouped
          (finProdFinEquiv
            (i, Fintype.equivFin _ (Sum.inl S : ComparisonControl N _)))
          (finProdFinEquiv
            (j, Fintype.equivFin _ (Sum.inl S : ComparisonControl N _))) =
        comparisonPreSuccessCoefficient N nK mZ mX pA pB * block i j := by
    dsimp only [regrouped, block]
    unfold comparisonPre
    have hcoord (u : Fin (4 ^ (nK + mZ + mX))) :
        (comparisonPreToRetainedControlEquiv N
            (nK + mZ + mX)).symm
          (finProdFinEquiv
            (u, Fintype.equivFin _
              (Sum.inl S : ComparisonControl N (nK + mZ + mX)))) =
          comparisonPreOutputEquiv N (nK + mZ + mX)
            (selectedPairNumeralEquiv (nK + mZ + mX)
                ((retainedSelectedPairToRoundEquiv
                  (nK + mZ + mX)).symm u),
              Sum.inl S) := by
      unfold comparisonPreToRetainedControlEquiv
        comparisonSelectedToRoundEquiv comparisonPreOutputEquiv
      simp
    change (coordinateLinear (comparisonPreInputEquiv N)
        (comparisonPreOutputEquiv N (nK + mZ + mX))
        (comparisonPreInstrument N nK mZ mX pA pB hN).channel)
      (Matrix.reindex (comparisonPreInputEquiv N)
        (comparisonPreInputEquiv N) rho)
      ((comparisonPreToRetainedControlEquiv N
        (nK + mZ + mX)).symm
          (finProdFinEquiv
            (i, Fintype.equivFin _
              (Sum.inl S : ComparisonControl N (nK + mZ + mX)))))
      ((comparisonPreToRetainedControlEquiv N
        (nK + mZ + mX)).symm
          (finProdFinEquiv
            (j, Fintype.equivFin _
              (Sum.inl S : ComparisonControl N (nK + mZ + mX))))) = _
    rw [hcoord i, hcoord j, coordinateLinear_reindex_apply,
      comparisonPreInstrument_success_apply]
    simp
  have hblock :
      (Matrix.of fun i j =>
        regrouped
          (finProdFinEquiv
            (i, Fintype.equivFin _ (Sum.inl S : ComparisonControl N _)))
          (finProdFinEquiv
            (j, Fintype.equivFin _ (Sum.inl S : ComparisonControl N _)))) =
        comparisonPreSuccessCoefficient N nK mZ mX pA pB • block := by
    ext i j
    simp [hregroup]
  rw [hblock, map_smul]
  rfl

private theorem retainedAnalysisReal_success
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : TypedLOCC.Op (ComparisonPreInput N))
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    let block : Quantum.Operators.Op (4 ^ (nK + mZ + mX)) :=
      Matrix.of fun i j =>
        (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).channel rho
            ((retainedSelectedPairToRoundEquiv
              (nK + mZ + mX)).symm i)
            ((retainedSelectedPairToRoundEquiv
              (nK + mZ + mX)).symm j)
    let Wphys : TypedLOCC.Op (ComparisonPreInput N × Unit) :=
      Matrix.of fun i j => rho i.1 j.1
    retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q block
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
          ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
            (pi, qa)))
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
          ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
            (pi, qb))) =
      if qa = qb then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV
              (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint
                (nK + mZ + mX) (mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = qa then
              (Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹ *
                ((Fintype.card (KeyHashSeedPairEV
                    (nK + mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                  nativeSelectedBornBlock S
                    (@Sampling.packedPESel nK mZ mX)
                    (@Sampling.packedXSel nK mZ mX) pi
                    ((retainedBitCoordinateEquiv
                      (nK + mZ + mX)).symm (x .alice))
                    ((retainedBitCoordinateEquiv
                      (nK + mZ + mX)).symm (x .bob)) Wphys () ())
            else 0
      else 0 := by
  let n := nK + mZ + mX
  let M : TypedLOCC.Op (ComparisonPreInput n) :=
    (selectedInputMarginalInstrument
      (increasingSubsetEmbedding S)).channel rho
  let block : Quantum.Operators.Op (4 ^ n) :=
    Matrix.of fun i j =>
      M ((retainedSelectedPairToRoundEquiv n).symm i)
        ((retainedSelectedPairToRoundEquiv n).symm j)
  let rhoNum := retainedAnalysisRoundToBlock n block
  let wRound : Quantum.Operators.Op ((4 ^ n) * 1) :=
    Matrix.of fun i j => block (finProdFinEquiv.symm i).1
      (finProdFinEquiv.symm j).1
  let wBlock : Quantum.Operators.Op ((2 ^ n * 2 ^ n) * 1) :=
    Matrix.of fun i j => rhoNum (finProdFinEquiv.symm i).1
      (finProdFinEquiv.symm j).1
  let Wphys : TypedLOCC.Op (ComparisonPreInput N × Unit) :=
    Matrix.of fun i j => rho i.1 j.1
  let E := retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
  let D := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
  let qA := D.symm (pi, qa)
  let qB := D.symm (pi, qb)
  have hwRound : (Matrix.of fun i j =>
      wRound (finProdFinEquiv (i, (0 : Fin 1)))
        (finProdFinEquiv (j, (0 : Fin 1)))) = block := by
    ext i j
    simp [wRound, Quantum.Channels.finProdFinEquiv_apply_divNat]
  have hwBlock : retainedAnalysisRoundReferenceToBlock wRound = wBlock := by
    ext i j
    simp [retainedAnalysisRoundReferenceToBlock, wRound, wBlock, rhoNum,
      retainedAnalysisRoundToBlock_apply,
      Quantum.Channels.finProdFinEquiv_apply_divNat]
  have hNative (x : (FinalStage.rawSystem n).total) :
      retainedAnalysisMeasuredReferenceBlock
          (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) pi wBlock x 0 0 =
        nativeSelectedBornBlock S
          (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) pi
          ((retainedBitCoordinateEquiv n).symm (x .alice))
          ((retainedBitCoordinateEquiv n).symm (x .bob)) Wphys () () := by
    have hw : (Matrix.of fun i j =>
        wBlock (finProdFinEquiv (i, (0 : Fin 1)))
          (finProdFinEquiv (j, (0 : Fin 1)))) = rhoNum := by
      ext i j
      simp [wBlock, Quantum.Channels.finProdFinEquiv_apply_divNat]
    have hMeasured :
        retainedAnalysisMeasuredReferenceBlock
            (@Sampling.packedPESel nK mZ mX)
            (@Sampling.packedXSel nK mZ mX) pi wBlock x 0 0 =
          retainedAnalysisSiftedState
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) pi
            (Matrix.reindex (retainedAnalysisBlockInputEquiv n).symm
              (retainedAnalysisBlockInputEquiv n).symm rhoNum) x x := by
      unfold retainedAnalysisMeasuredReferenceBlock
        retainedAnalysisProgramInputReferenceBlock
      simp only [Matrix.of_apply]
      rw [hw]
    have hRhoNum : rhoNum = Matrix.reindex
        (selectedPairNumeralEquiv n) (selectedPairNumeralEquiv n) M := by
      ext i j
      simp [rhoNum, block, retainedAnalysisRoundToBlock,
        retainedSelectedPairToRoundEquiv, Matrix.reindex_apply,
        Matrix.reindexLinearEquiv_apply]
    rw [hMeasured]
    let e := retainedAnalysisBlockInputEquiv n
    let kappa := QKD.BB84.Model.siftPermHalf n
      (@Sampling.packedPESel nK mZ mX)
      (@Sampling.packedXSel nK mZ mX) pi
    let kp := Quantum.TensorProducts.Op.tensor kappa kappa
    let prefixState : Quantum.Operators.Op (2 ^ n * 2 ^ n) →
        TypedLOCC.Op (FinalStage.rawSystem n).total := fun sigma =>
      retainedAnalysisSiftedState
        (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) pi
        (Matrix.reindex e.symm e.symm sigma)
    have hcoord (sigma : Quantum.Operators.Op (2 ^ n * 2 ^ n)) :
        Matrix.reindex e e (prefixState sigma) = kp * sigma * kpᴴ :=
      reindex_retainedAnalysisSiftedState _ _ pi sigma
    have hentry (sigma : Quantum.Operators.Op (2 ^ n * 2 ^ n))
        (y : (FinalStage.rawSystem n).total) :
        prefixState sigma y y = (kp * sigma * kpᴴ) (e y) (e y) := by
      have hy := congrFun₂ (hcoord sigma) (e y) (e y)
      simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply] using hy
    change prefixState rhoNum x x = _
    rw [hentry, hRhoNum]
    let uA := (retainedBitCoordinateEquiv n).symm (x .alice)
    let uB := (retainedBitCoordinateEquiv n).symm (x .bob)
    let knative := nativeSiftPairKraus n
      (@Sampling.packedPESel nK mZ mX)
      (@Sampling.packedXSel nK mZ mX) pi uA uB
    have hWphys : selectedReferenceInputBlock Wphys () () = rho := by
      ext i j
      rfl
    change (kp * Matrix.reindex (selectedPairNumeralEquiv n)
        (selectedPairNumeralEquiv n) M * kpᴴ) (e x) (e x) =
      (knative * M * knativeᴴ) () ()
    have hrow (y : ComparisonPreInput n) :
        kp (e x) (selectedPairNumeralEquiv n y) = knative () y := by
      rcases y with ⟨yA, yB⟩
      simp [kp, kappa, e, knative, uA, uB,
        retainedAnalysisBlockInputEquiv, TwoParty.pairEquiv,
        selectedPairNumeralEquiv, nativeSiftPairKraus,
        nativeSiftMeasurementRow, retainedBitCoordinateEquiv,
        Instrument.computationalMeasurement,
        Instrument.nondemolitionReadout,
        Instrument.nondemolitionReadoutKraus,
        Quantum.TensorProducts.Op.tensor]
    rw [mul_mul_conjTranspose_apply, mul_mul_conjTranspose_apply]
    rw [← Equiv.sum_comp (selectedPairNumeralEquiv n)]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Equiv.sum_comp (selectedPairNumeralEquiv n)]
    apply congrArg₂ (fun a b : ℂ => a * b)
    · apply Finset.sum_congr rfl
      intro z _
      simp [Matrix.reindex_apply, hrow]
    · simp [hrow]
  have hReal := retainedAnalysisReal_referenceBlock_eq_program
    nK mZ mX ell ellEV leakEC 1 ec delta Q wRound qA qB 0 0
  have hProgram := retainedAnalysisProgram_reference_blocks
    nK mZ mX ell ellEV leakEC 1 ec delta Q wBlock qA qB 0 0
  dsimp only at hReal hProgram
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block] at hReal
  simp only [Equiv.symm_apply_apply] at hReal
  rw [hwRound] at hReal
  rw [hwBlock] at hReal
  rw [hProgram] at hReal
  change retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q block
      (E qA) (E qB) = _
  rw [hReal]
  simp only [qA, qB, D, Equiv.apply_symm_apply, hNative]
  by_cases hq : qa = qb
  · subst qb
    rw [if_pos rfl, if_pos rfl]
  · have hq' :
        (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
            (pi, qa) ≠
          (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
            (pi, qb) := by
      intro h
      apply hq
      exact congrArg Prod.snd
        ((retainedAnalysisOutputDataEquiv
          nK mZ mX ell ellEV leakEC).symm.injective h)
    rw [if_neg hq', if_neg hq]

/-- On a quota-success exit, the BB84 program and the factorized real map have the same complete
output block for every complex input operator and every pair of classical-tail outputs. -/
theorem retainedFactorization_success_sector
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total)
    (omega : RawControl N) (hquota : HasQuotas nK mZ mX omega)
    (qa qb : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    (QKD.BB84.program pA pB N nK mZ mX ell ellEV leakEC
        ec delta Q).denote rho
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qa)
      (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        omega hquota qb) =
      let mid := retainedControlLift N (nK + mZ + mX)
        (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
        (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)
        (comparisonPre N nK mZ mX pA pB hN
          (Matrix.reindex (Fintype.equivFin _)
            (Fintype.equivFin _) rho))
      reconstruction N nK mZ mX ell ellEV leakEC pA pB mid
        (Fintype.equivFin _
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota qa))
        (Fintype.equivFin _
          (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
            omega hquota qb)) := by
  dsimp only
  rw [reconstruction_success pA pB N nK mZ mX ell ellEV leakEC
    omega hquota qa qb]
  let rhoBits : TypedLOCC.Op (ComparisonPreInput N) :=
    reindexOp (weightedScheduleUnitInputEquiv N) rho
  have hinput :
      Matrix.reindex (comparisonPreInputEquiv N)
          (comparisonPreInputEquiv N) rhoBits =
        Matrix.reindex (Fintype.equivFin (weightedStreamSystem Unit N).total)
          (Fintype.equivFin (weightedStreamSystem Unit N).total) rho := by
    ext i j
    simp [rhoBits, reindexOp, comparisonPreInputEquiv, Matrix.reindex_apply]
  rw [← hinput]
  simp_rw [retainedMid_success pA pB N nK mZ mX ell ellEV leakEC hN
    ec delta Q rhoBits]
  simp_rw [retainedAnalysisReal_success N nK mZ mX ell ellEV leakEC
    ec delta Q rhoBits]
  rw [program_denote_success_output_formula pA pB N nK mZ mX
    ell ellEV leakEC omega hquota ec delta Q rho qa qb]
  by_cases hq : qa = qb
  · subst qb
    simp only [if_pos]
    have hcoeff
        (S : Set.powersetCard (Fin N) (nK + mZ + mX))
        (pi : Equiv.Perm (Fin (nK + mZ + mX))) :
        ((totalSelectedControlKernel N nK mZ mX pA pB
            (Math.FiniteEmbedding.joinSubsetPerm S pi) omega).toReal : ℂ) *
            (comparisonPreSuccessCoefficient N nK mZ mX pA pB *
              (Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹) =
          ((selectionSuccessMass N nK mZ mX pA pB *
            uniformRetainedSubset hN S *
            (uniformInnerPerm (nK + mZ + mX) pi *
              totalSelectedControlKernel N nK mZ mX pA pB
                (Math.FiniteEmbedding.joinSubsetPerm S pi) omega)).toReal : ℂ) := by
      simp [comparisonPreSuccessCoefficient, uniformRetainedSubset,
        uniformInnerPerm, PMF.uniformOfFintype_apply, ENNReal.toReal_mul]
      ring
    let Wphys : TypedLOCC.Op (ComparisonPreInput N × Unit) :=
      Matrix.of fun i j => rhoBits i.1 j.1
    have hWphys :
        (Matrix.of fun i j =>
          (reindexOp (weightedScheduleUnitInputEquiv N) rho) i.1 j.1) =
          Wphys := by
      rfl
    have hreconstruct
        (x : (FinalStage.rawSystem (nK + mZ + mX)).total) :
        ((rawControlLaw N pA pB omega).toReal : ℂ) *
            fixedBasisSelectedBornBlock (selectedEmbedding omega hquota)
              omega.a omega.b
              ((retainedBitCoordinateEquiv
                (nK + mZ + mX)).symm (x .alice))
              ((retainedBitCoordinateEquiv
                (nK + mZ + mX)).symm (x .bob)) Wphys () () =
          ∑ S : Set.powersetCard (Fin N) (nK + mZ + mX),
            ∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
              ((selectionSuccessMass N nK mZ mX pA pB *
                uniformRetainedSubset hN S *
                (uniformInnerPerm (nK + mZ + mX) pi *
                  totalSelectedControlKernel N nK mZ mX pA pB
                    (Math.FiniteEmbedding.joinSubsetPerm S pi)
                    omega)).toReal : ℂ) *
                nativeSelectedBornBlock S
                  (@Sampling.packedPESel nK mZ mX)
                  (@Sampling.packedXSel nK mZ mX) pi
                  ((retainedBitCoordinateEquiv
                    (nK + mZ + mX)).symm (x .alice))
                  ((retainedBitCoordinateEquiv
                    (nK + mZ + mX)).symm (x .bob)) Wphys () () := by
      exact (totalized_success_native_formula N nK mZ mX pA pB hN
        omega hquota
        ((retainedBitCoordinateEquiv (nK + mZ + mX)).symm (x .alice))
        ((retainedBitCoordinateEquiv (nK + mZ + mX)).symm (x .bob))
        Wphys () ()).symm
    have hterm
        (S : Set.powersetCard (Fin N) (nK + mZ + mX))
        (pi : Equiv.Perm (Fin (nK + mZ + mX)))
        (x : (FinalStage.rawSystem (nK + mZ + mX)).total) :
        ((totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi) omega).toReal : ℂ) *
          (comparisonPreSuccessCoefficient N nK mZ mX pA pB *
            ((Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹ *
              ((Fintype.card (KeyHashSeedPairEV
                (nK + mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                nativeSelectedBornBlock S
                  (@Sampling.packedPESel nK mZ mX)
                  (@Sampling.packedXSel nK mZ mX) pi
                  ((retainedBitCoordinateEquiv
                    (nK + mZ + mX)).symm (x .alice))
                  ((retainedBitCoordinateEquiv
                    (nK + mZ + mX)).symm (x .bob)) Wphys () ()))) =
          (Fintype.card (KeyHashSeedPairEV
            (nK + mZ + mX) ell ellEV
            (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
            ((selectionSuccessMass N nK mZ mX pA pB *
              uniformRetainedSubset hN S *
              (uniformInnerPerm (nK + mZ + mX) pi *
                totalSelectedControlKernel N nK mZ mX pA pB
                  (Math.FiniteEmbedding.joinSubsetPerm S pi)
                  omega)).toReal : ℂ) *
            nativeSelectedBornBlock S
              (@Sampling.packedPESel nK mZ mX)
              (@Sampling.packedXSel nK mZ mX) pi
              ((retainedBitCoordinateEquiv
                (nK + mZ + mX)).symm (x .alice))
              ((retainedBitCoordinateEquiv
                (nK + mZ + mX)).symm (x .bob)) Wphys () () := by
      calc
        _ = (Fintype.card (KeyHashSeedPairEV
              (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
            ((((totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi) omega).toReal : ℂ) *
                (comparisonPreSuccessCoefficient N nK mZ mX pA pB *
                  (Fintype.card
                    (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹)) *
              nativeSelectedBornBlock S
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) pi
                ((retainedBitCoordinateEquiv
                  (nK + mZ + mX)).symm (x .alice))
                ((retainedBitCoordinateEquiv
                  (nK + mZ + mX)).symm (x .bob)) Wphys () ()) := by ring
        _ = _ := by
          rw [hcoeff S pi]
          ring
    rw [hWphys]
    simp_rw [hreconstruct]
    simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    simp_rw [hterm]
    have hite {A B : Type} [Fintype A] [Fintype B]
        (p : Prop) [Decidable p] (f : A → B → ℂ) :
        (if p then ∑ a, ∑ b, f a b else 0) =
          ∑ a, ∑ b, if p then f a b else 0 := by
      by_cases hp : p <;> simp [hp]
    simp_rw [hite]
    conv_rhs =>
      enter [2, S]
      rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs =>
      enter [2, x]
      enter [2, S]
      rw [Finset.sum_comm]
    conv_rhs =>
      enter [2, x]
      rw [Finset.sum_comm]
    simp only [mul_assoc]
  · simp only [if_neg hq, mul_zero, Finset.sum_const_zero]

end QKD.BB84.Reduction
