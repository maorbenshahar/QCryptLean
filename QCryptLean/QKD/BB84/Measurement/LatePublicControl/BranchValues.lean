import QCryptLean.QKD.BB84.Measurement.LatePublicControl
import QCryptLean.LOCC.Typed.Program.ExitWeight
import QCryptLean.LOCC.Typed.Instrument.MatrixConj

/-!
# Exact branch values of the measure-first sifting stage

`weightedLatePublicSelectionProgram` is the destructive measurement schedule followed by the late
public basis/shuffle control and quota selection.  This module computes, for an **arbitrary** input
operator, its exact matrix entry in each of the two kinds of complete public branch:

* `weightedLatePublicSelectionProgram_success_apply` — a quota-feasible control, where the retained
  entry is the selected-record measurement law at precisely the embedding that control chose,
  weighted by the uniform shuffle probability, and zero unless both selected records carry the
  announced basis strings;
* `weightedLatePublicSelectionProgram_abort_apply` — a quota-shortage control, where both complete
  local records have been discarded and the diagonal entry is the announced basis strings'
  probability times the uniform shuffle weight times the sum over every local outcome string.

Both are equalities of finite coordinate expressions with no IID, positivity, normalization,
support or security hypothesis.  They are the coordinate input of the retained-round
factorization (`QCryptLean.QKD.BB84.Reduction.Factorization.Real.Success` and
`... .Real.Shortage`) and are deliberately kept out of the chronological construction's import
path.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open TypedLOCC

open TypedLOCC.TwoParty
open QKD.BB84.Sampling

/-- Alice's basis announcement keeps exactly the diagonal entries whose Alice record carries
the announced basis string. -/
private theorem completedBasisAliceAnnouncement_liftedOperation_diag (N : ℕ)
    (a : Fin N → Basis) (sigma : Op (weightedStreamSystem (finishAcc Unit N) 0).total)
    (rA rB : CompletedLocalRecord N) :
    (completedBasisAliceAnnouncement N).liftedOperation a sigma
        ((MultipartiteSystem.pairEquiv _).symm (rA, rB))
        ((MultipartiteSystem.pairEquiv _).symm (rA, rB)) =
      if completedBasisString N rA = a then
        sigma ((MultipartiteSystem.pairEquiv _).symm (rA, rB))
          ((MultipartiteSystem.pairEquiv _).symm (rA, rB))
      else 0 := by
  change (((Instrument.nondemolitionReadout (completedBasisString N)).liftAt
    (weightedStreamSystem (finishAcc Unit N) 0) .alice).operation a sigma)
      (((weightedStreamSystem (finishAcc Unit N) 0).set .alice
        (CompletedLocalRecord N)).pairEquiv.symm (rA, rB))
      (((weightedStreamSystem (finishAcc Unit N) 0).set .alice
        (CompletedLocalRecord N)).pairEquiv.symm (rA, rB)) = _
  rw [Instrument.liftAt_alice_operation_apply]
  simpa only [Matrix.submatrix_apply, and_self] using
    Instrument.nondemolitionReadout_operation_apply (completedBasisString N) a
      (sigma.submatrix
        (fun x => (weightedStreamSystem (finishAcc Unit N) 0).pairEquiv.symm (x, rB))
        (fun x => (weightedStreamSystem (finishAcc Unit N) 0).pairEquiv.symm (x, rB))) rA rA

/-- After both basis announcements, exactly the diagonal entries whose two records carry the
announced basis strings survive. -/
private theorem completedBasisAnnouncements_liftedOperation_diag (N : ℕ)
    (a b : Fin N → Basis) (sigma : Op (weightedStreamSystem (finishAcc Unit N) 0).total)
    (rA rB : CompletedLocalRecord N) :
    (completedBasisBobAnnouncement N a).liftedOperation b
        ((completedBasisAliceAnnouncement N).liftedOperation a sigma)
        ((MultipartiteSystem.pairEquiv _).symm (rA, rB))
        ((MultipartiteSystem.pairEquiv _).symm (rA, rB)) =
      if completedBasisString N rA = a ∧
          completedBasisString N rB = b then
        sigma ((MultipartiteSystem.pairEquiv _).symm (rA, rB))
          ((MultipartiteSystem.pairEquiv _).symm (rA, rB))
      else 0 := by
  change (((Instrument.nondemolitionReadout (completedBasisString N)).liftAt
    ((completedBasisAliceAnnouncement N).out a) .bob).operation b
      ((completedBasisAliceAnnouncement N).liftedOperation a sigma))
      ((((completedBasisAliceAnnouncement N).out a).set .bob
        (CompletedLocalRecord N)).pairEquiv.symm (rA, rB))
      ((((completedBasisAliceAnnouncement N).out a).set .bob
        (CompletedLocalRecord N)).pairEquiv.symm (rA, rB)) = _
  rw [Instrument.liftAt_bob_operation_apply]
  refine (Instrument.nondemolitionReadout_operation_apply (completedBasisString N) b
    (((completedBasisAliceAnnouncement N).liftedOperation a sigma).submatrix
      (fun x => ((completedBasisAliceAnnouncement N).out a).pairEquiv.symm (rA, x))
      (fun x => ((completedBasisAliceAnnouncement N).out a).pairEquiv.symm (rA, x))) rB rB).trans ?_
  simp only [Matrix.submatrix_apply, and_self]
  have hAlice : (completedBasisAliceAnnouncement N).liftedOperation a sigma
      (((completedBasisAliceAnnouncement N).out a).pairEquiv.symm (rA, rB))
      (((completedBasisAliceAnnouncement N).out a).pairEquiv.symm (rA, rB)) =
        if completedBasisString N rA = a then
          sigma ((weightedStreamSystem (finishAcc Unit N) 0).pairEquiv.symm (rA, rB))
            ((weightedStreamSystem (finishAcc Unit N) 0).pairEquiv.symm (rA, rB)) else 0 :=
    completedBasisAliceAnnouncement_liftedOperation_diag N a sigma rA rB
  rw [hAlice]
  by_cases hA : completedBasisString N rA = a <;>
    by_cases hB : completedBasisString N rB = b <;> simp [hA, hB]

/-- **The shuffle announcement is a uniform weight.** Announcing the sampled shuffle `order`
leaves the local registers untouched and weights the branch by the uniform probability
`|Shuffle a b|⁻¹`. -/
theorem shuffleAnnouncement_liftedOperation_apply (N : ℕ) (a b : Fin N → Basis)
    (order : Shuffle a b) (upsilon : Op ((completedBasisBobAnnouncement N a).out b).total) :
    reindexOp (Equiv.cast (congrArg MultipartiteSystem.total
      (show (shuffleAnnouncement N a b).out order =
          (completedBasisBobAnnouncement N a).out b from by
        rw [shuffleAnnouncement, AnnouncedAction.out_ofInstrument]
        exact MultipartiteSystem.set_self _ _)))
        ((shuffleAnnouncement N a b).liftedOperation (order, ()) upsilon) =
      (Fintype.card (Shuffle a b) : ℂ)⁻¹ • upsilon := by
  let R := (completedBasisBobAnnouncement N a).out b
  have hentry (q q' : R.total) :
      (shuffleAnnouncement N a b).liftedOperation (order, ()) upsilon
          ((R.splitAtSet .alice (CompletedLocalRecord N)).symm (R.splitAt .alice q))
          ((R.splitAtSet .alice (CompletedLocalRecord N)).symm (R.splitAt .alice q')) =
        (Fintype.card (Shuffle a b) : ℂ)⁻¹ * upsilon q q' := by
    change ((uniformShuffleInstrument N a b).liftAt R .alice).operation
      (order, ()) upsilon _ _ = _
    rw [Instrument.liftAt_operation_apply (R := R) .alice (uniformShuffleInstrument N a b)]
    simp only [Equiv.apply_symm_apply, uniformShuffleInstrument,
      Instrument.uniformChoice_operation, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1
    simpa only [and_self, ite_true, Matrix.submatrix_apply, Prod.eta,
      Equiv.symm_apply_apply] using
      Instrument.nondemolitionReadout_operation_apply (fun _ : CompletedLocalRecord N => ()) ()
        (upsilon.submatrix
          (fun x => (R.splitAt .alice).symm (x, (R.splitAt .alice q).2))
          (fun x => (R.splitAt .alice).symm (x, (R.splitAt .alice q').2)))
        (R.splitAt .alice q).1 (R.splitAt .alice q').1
  ext q q'
  change (shuffleAnnouncement N a b).liftedOperation (order, ()) upsilon
    (cast (congrArg MultipartiteSystem.total (R.set_self .alice).symm) q)
    (cast (congrArg MultipartiteSystem.total (R.set_self .alice).symm) q') = _
  rw [← MultipartiteSystem.splitAtSet_self_symm, ← MultipartiteSystem.splitAtSet_self_symm]
  exact hentry q q'

/-- Exact arbitrary-operator value in a successful complete public branch.

The full basis strings and sampled shuffle remain in the output exit.  The selected continuation
uses precisely the embedding computed from that same public raw control.  No IID, positivity,
normalization, support, or security assumption is present.
-/
theorem weightedLatePublicSelectionProgram_success_apply
    (pA pB : PMF Basis) (N nK mZ mX : ℕ)
    (omega : RawControl N)
    (h : HasQuotas nK mZ mX omega)
    (rho : Op (weightedStreamSystem Unit N).total)
    (q q' : SelectedLocalRecord N (nK + mZ + mX) ×
      SelectedLocalRecord N (nK + mZ + mX)) :
    (weightedLatePublicSelectionProgram pA pB N nK mZ mX).denote rho
        (lateSelectionSuccessAt N nK mZ mX omega h q)
        (lateSelectionSuccessAt N nK mZ mX omega h q') =
      if q.1.1 = omega.a ∧ q'.1.1 = omega.a ∧
          q.2.1 = omega.b ∧ q'.2.1 = omega.b then
        (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ *
          selectedMeasurementLaw pA pB
            (selectedEmbedding omega h)
            (reindexOp (weightedScheduleUnitInputEquiv N) rho) q q'
      else 0 := by
  unfold weightedLatePublicSelectionProgram
  rw [Program.denote_graft]
  have hrow (x : (lateSelectionBoundary N nK mZ mX).space) :
      ((Boundary.graftSpaceEquiv
        (.leaf (weightedStreamSystem (finishAcc Unit N) 0))
        (fun _ => lateSelectionBoundary N nK mZ mX)).symm ⟨(), x⟩) = x := by
    simpa only [Boundary.graftSpaceEquiv_leaf_apply] using
      (Equiv.symm_apply_apply
        (Boundary.graftSpaceEquiv
          (.leaf (weightedStreamSystem (finishAcc Unit N) 0))
          (fun _ => lateSelectionBoundary N nK mZ mX)) x)
  rw [← hrow (lateSelectionSuccessAt N nK mZ mX omega h q),
    ← hrow (lateSelectionSuccessAt N nK mZ mX omega h q')]
  change (Program.controlledContinuation
      (fun _ : (Boundary.leaf (weightedStreamSystem (finishAcc Unit N) 0)).Exit =>
        latePublicSelectionProgram N nK mZ mX)
      ((weightedMeasurementSchedule pA pB N).denote rho)) _ _ = _
  rw [Program.controlledContinuation_sameExit]
  let sigma : Op (weightedStreamSystem (finishAcc Unit N) 0).total :=
    ((Boundary.exitKraus
      (.leaf (weightedStreamSystem (finishAcc Unit N) 0)) ())ᴴ *
        (weightedMeasurementSchedule pA pB N).denote rho *
      Boundary.exitKraus
        (.leaf (weightedStreamSystem (finishAcc Unit N) 0)) ())
  change (latePublicSelectionProgram N nK mZ mX).denote sigma
    (lateSelectionSuccessAt N nK mZ mX omega h q)
    (lateSelectionSuccessAt N nK mZ mX omega h q') = _
  have hB : (completedBasisBobAnnouncement N omega.a).out omega.b =
      weightedStreamSystem (finishAcc Unit N) 0 := by
    simp only [completedBasisBobAnnouncement, completedBasisAliceAnnouncement,
      AnnouncedAction.out_ofInstrument, weightedStreamSystem, TwoParty.set_alice,
      TwoParty.set_bob]
    rfl
  have hself : (shuffleAnnouncement N omega.a omega.b).out omega.order =
      (completedBasisBobAnnouncement N omega.a).out omega.b := by
    rw [shuffleAnnouncement, AnnouncedAction.out_ofInstrument]
    exact MultipartiteSystem.set_self _ _
  let hfinal := hself.trans hB
  let tau := (completedBasisAliceAnnouncement N).liftedOperation omega.a sigma
  let upsilonRaw := (completedBasisBobAnnouncement N omega.a).liftedOperation omega.b tau
  let upsilon := upsilonRaw.submatrix
    (Equiv.cast (congrArg MultipartiteSystem.total hB)).symm
    (Equiv.cast (congrArg MultipartiteSystem.total hB)).symm
  have hcastB (rA rB : CompletedLocalRecord N) :
      (Equiv.cast (congrArg MultipartiteSystem.total hB)).symm
          ((TwoParty.pairEquiv _ _).symm (rA, rB)) =
        ((completedBasisBobAnnouncement N omega.a).out omega.b).pairEquiv.symm (rA, rB) := by
    change cast (congrArg MultipartiteSystem.total hB.symm)
      ((weightedStreamSystem (finishAcc Unit N) 0).pairEquiv.symm (rA, rB)) = _
    rw [MultipartiteSystem.cast_pairEquiv_symm hB.symm]
    rfl
  have hshuffle :
      ((shuffleAnnouncement N omega.a omega.b).liftedOperation
        (omega.order, ()) upsilonRaw).submatrix
          (Equiv.cast (congrArg MultipartiteSystem.total hfinal)).symm
          (Equiv.cast (congrArg MultipartiteSystem.total hfinal)).symm =
        (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ • upsilon := by
    ext z z'
    have hop := congrFun (congrFun
      (shuffleAnnouncement_liftedOperation_apply N omega.a omega.b omega.order upsilonRaw)
      ((Equiv.cast (congrArg MultipartiteSystem.total hB)).symm z))
      ((Equiv.cast (congrArg MultipartiteSystem.total hB)).symm z')
    change (shuffleAnnouncement N omega.a omega.b).liftedOperation (omega.order, ()) upsilonRaw
      (cast (congrArg MultipartiteSystem.total hself.symm)
        (cast (congrArg MultipartiteSystem.total hB.symm) z))
      (cast (congrArg MultipartiteSystem.total hself.symm)
        (cast (congrArg MultipartiteSystem.total hB.symm) z')) = _ at hop
    simpa only [cast_cast] using hop
  unfold latePublicSelectionProgram lateSelectionSuccessAt
  simp only [id_eq]
  have hAlice := Program.denote_then_publicSpaceEquiv_symm_apply
    (completedBasisAliceAnnouncement N) (Equiv.refl _) (fun _ => rfl)
  simp only [completedBasisAliceAnnouncement_announce] at hAlice
  refine (hAlice _ _ sigma omega.a _ _).trans ?_
  have hBob := Program.denote_then_publicSpaceEquiv_symm_apply
    (completedBasisBobAnnouncement N omega.a) (Equiv.refl _) (fun _ => rfl)
  simp only [completedBasisBobAnnouncement_announce] at hBob
  refine (hBob _ _ tau omega.b _ _).trans ?_
  have hShuffle := Program.denote_then_publicSpaceEquiv_symm_apply
    (shuffleAnnouncement N omega.a omega.b) (Equiv.prodUnique _ _) (fun _ => rfl)
  simp only [shuffleAnnouncement_announce] at hShuffle
  refine (hShuffle _ _ upsilonRaw (omega.order, ()) _ _).trans ?_
  rw [Program.denote_cast_apply hfinal rfl]
  simp only [Equiv.cast_refl, Equiv.refl_apply]
  change (quotaSelectionContinuation N nK mZ mX omega).denote
    (((shuffleAnnouncement N omega.a omega.b).liftedOperation
      (omega.order, ()) upsilonRaw).submatrix
        (Equiv.cast (congrArg MultipartiteSystem.total hfinal)).symm
        (Equiv.cast (congrArg MultipartiteSystem.total hfinal)).symm) _ _ = _
  rw [hshuffle]
  simp only [map_smul, Matrix.smul_apply, smul_eq_mul]
  have hquota : HEq
      (quotaSelectionContinuation N nK mZ mX omega)
      (selectedRecordContinuation (selectedEmbedding omega h)) := by
    unfold quotaSelectionContinuation
    split
    · rename_i h'
      cases Subsingleton.elim h' h
      simp only [eq_mpr_eq_cast]
      exact cast_heq _ _
    · contradiction
  let hleaf : (Boundary.leaf
      (weightedSelectedRecordSystem N (nK + mZ + mX))) =
        lateSelectionLeaf N nK mZ mX omega := by
    symm
    simp [lateSelectionLeaf, h]
  have hquotaCast :
      quotaSelectionContinuation N nK mZ mX omega =
        hleaf ▸ selectedRecordContinuation
          (selectedEmbedding omega h) := by
    apply eq_of_heq
    exact hquota.trans (eqRec_heq hleaf
      (selectedRecordContinuation (selectedEmbedding omega h))).symm
  have htransport {B C : Boundary Party} (hb : B = C)
      (p : Program (weightedStreamSystem (finishAcc Unit N) 0) B)
      (xi : Op (weightedStreamSystem (finishAcc Unit N) 0).total)
      (x y : B.space) {x' y' : C.space}
      (hx : HEq x' x) (hy : HEq y' y) :
      ((hb ▸ p).denote xi) x' y' =
        p.denote xi x y := by
    cases hb
    cases hx
    cases hy
    rfl
  rw [hquotaCast]
  have hselectedSigma :
      (selectedRecordContinuation (selectedEmbedding omega h)).denote sigma
          ((Boundary.leafSpaceEquiv
            (weightedSelectedRecordSystem N (nK + mZ + mX))).symm
              ((TwoParty.pairEquiv _ _).symm q))
          ((Boundary.leafSpaceEquiv
            (weightedSelectedRecordSystem N (nK + mZ + mX))).symm
              ((TwoParty.pairEquiv _ _).symm q')) =
        selectedMeasurementLaw pA pB (selectedEmbedding omega h)
          (reindexOp (weightedScheduleUnitInputEquiv N) rho) q q' := by
    have hop := LinearMap.congr_fun
      (weightedSelectedMeasurementProgram_denote_eq pA pB N
        (selectedEmbedding omega h)) rho
    have hentry := congrFun (congrFun hop q) q'
    simp only [LinearMap.comp_apply] at hentry
    unfold weightedSelectedMeasurementProgram at hentry
    rw [Program.denote_graft] at hentry
    simp only [reindexOp] at hentry
    let xq := (Boundary.leafSpaceEquiv
      (weightedSelectedRecordSystem N (nK + mZ + mX))).symm
        ((TwoParty.pairEquiv _ _).symm q)
    let xq' := (Boundary.leafSpaceEquiv
      (weightedSelectedRecordSystem N (nK + mZ + mX))).symm
        ((TwoParty.pairEquiv _ _).symm q')
    change (Program.controlledContinuation
      (fun _ : (Boundary.leaf
        (weightedStreamSystem (finishAcc Unit N) 0)).Exit =>
          selectedRecordContinuation (selectedEmbedding omega h))
      ((weightedMeasurementSchedule pA pB N).denote rho))
        xq xq' = _ at hentry
    have hleafrow
        (x : (Boundary.leaf
          (weightedSelectedRecordSystem N (nK + mZ + mX))).space) :
        ((Boundary.graftSpaceEquiv
          (.leaf (weightedStreamSystem (finishAcc Unit N) 0))
          (fun _ => .leaf
            (weightedSelectedRecordSystem N (nK + mZ + mX)))).symm
              ⟨(), x⟩) = x := by
      simpa only [Boundary.graftSpaceEquiv_leaf_apply] using
        (Equiv.symm_apply_apply
          (Boundary.graftSpaceEquiv
            (.leaf (weightedStreamSystem (finishAcc Unit N) 0))
            (fun _ => .leaf
              (weightedSelectedRecordSystem N (nK + mZ + mX)))) x)
    rw [← hleafrow xq, ← hleafrow xq'] at hentry
    rw [Program.controlledContinuation_sameExit] at hentry
    exact hentry
  have hupsilonDiag
      (rA rB : CompletedLocalRecord N) :
      upsilon ((TwoParty.pairEquiv _ _).symm (rA, rB))
          ((TwoParty.pairEquiv _ _).symm (rA, rB)) =
        if completedBasisString N rA = omega.a ∧
            completedBasisString N rB = omega.b then
          sigma ((TwoParty.pairEquiv _ _).symm (rA, rB))
            ((TwoParty.pairEquiv _ _).symm (rA, rB))
        else 0 := by
    change upsilonRaw
      ((Equiv.cast (congrArg MultipartiteSystem.total hB)).symm
        ((TwoParty.pairEquiv _ _).symm (rA, rB)))
      ((Equiv.cast (congrArg MultipartiteSystem.total hB)).symm
        ((TwoParty.pairEquiv _ _).symm (rA, rB))) = _
    rw [hcastB]
    exact completedBasisAnnouncements_liftedOperation_diag N omega.a omega.b sigma rA rB
  have hselectedBasis
      (r : CompletedLocalRecord N) :
      (selectedLocalRecord (selectedEmbedding omega h) r).1 =
        completedBasisString N r := by
    rfl
  have hselectedUpsilon :
      (selectedRecordContinuation (selectedEmbedding omega h)).denote upsilon
          ((Boundary.leafSpaceEquiv
            (weightedSelectedRecordSystem N (nK + mZ + mX))).symm
              ((TwoParty.pairEquiv _ _).symm q))
          ((Boundary.leafSpaceEquiv
            (weightedSelectedRecordSystem N (nK + mZ + mX))).symm
              ((TwoParty.pairEquiv _ _).symm q')) =
        if q.1.1 = omega.a ∧ q'.1.1 = omega.a ∧
            q.2.1 = omega.b ∧ q'.2.1 = omega.b then
          (selectedRecordContinuation
            (selectedEmbedding omega h)).denote sigma
              ((Boundary.leafSpaceEquiv
                (weightedSelectedRecordSystem N
                  (nK + mZ + mX))).symm
                    ((TwoParty.pairEquiv _ _).symm q))
              ((Boundary.leafSpaceEquiv
                (weightedSelectedRecordSystem N
                  (nK + mZ + mX))).symm
                    ((TwoParty.pairEquiv _ _).symm q'))
        else 0 := by
    rw [selectedRecordContinuation_denote_apply _ upsilon q q',
      selectedRecordContinuation_denote_apply _ sigma q q']
    by_cases hg : q.1.1 = omega.a ∧ q'.1.1 = omega.a ∧
        q.2.1 = omega.b ∧ q'.2.1 = omega.b
    · rw [if_pos hg]
      apply Finset.sum_congr rfl
      intro rB _
      by_cases hb : q.2 =
          selectedLocalRecord (selectedEmbedding omega h) rB ∧
        q'.2 = selectedLocalRecord (selectedEmbedding omega h) rB
      · rw [if_pos hb, if_pos hb]
        apply Finset.sum_congr rfl
        intro rA _
        by_cases ha : q.1 =
            selectedLocalRecord (selectedEmbedding omega h) rA ∧
          q'.1 = selectedLocalRecord (selectedEmbedding omega h) rA
        · rw [if_pos ha, if_pos ha, hupsilonDiag]
          have hAr : completedBasisString N rA = omega.a := by
            rw [← hselectedBasis, ← ha.1]
            exact hg.1
          have hBr : completedBasisString N rB = omega.b := by
            rw [← hselectedBasis, ← hb.1]
            exact hg.2.2.1
          rw [if_pos ⟨hAr, hBr⟩]
        · rw [if_neg ha, if_neg ha]
      · rw [if_neg hb, if_neg hb]
    · rw [if_neg hg]
      apply Finset.sum_eq_zero
      intro rB _
      by_cases hb : q.2 =
          selectedLocalRecord (selectedEmbedding omega h) rB ∧
        q'.2 = selectedLocalRecord (selectedEmbedding omega h) rB
      · rw [if_pos hb]
        apply Finset.sum_eq_zero
        intro rA _
        by_cases ha : q.1 =
            selectedLocalRecord (selectedEmbedding omega h) rA ∧
          q'.1 = selectedLocalRecord (selectedEmbedding omega h) rA
        · rw [if_pos ha, hupsilonDiag]
          have hnot : ¬ (completedBasisString N rA = omega.a ∧
              completedBasisString N rB = omega.b) := by
            rintro ⟨hAr, hBr⟩
            apply hg
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [ha.1, hselectedBasis]
              exact hAr
            · rw [ha.2, hselectedBasis]
              exact hAr
            · rw [hb.1, hselectedBasis]
              exact hBr
            · rw [hb.2, hselectedBasis]
              exact hBr
          rw [if_neg hnot]
        · rw [if_neg ha]
      · rw [if_neg hb]
  rw [htransport hleaf
    (selectedRecordContinuation (selectedEmbedding omega h)) upsilon
    ((Boundary.leafSpaceEquiv
      (weightedSelectedRecordSystem N (nK + mZ + mX))).symm
        ((TwoParty.pairEquiv _ _).symm q))
    ((Boundary.leafSpaceEquiv
      (weightedSelectedRecordSystem N (nK + mZ + mX))).symm
        ((TwoParty.pairEquiv _ _).symm q'))
    (cast_heq _ _) (cast_heq _ _)]
  rw [hselectedUpsilon, hselectedSigma]
  by_cases hg : q.1.1 = omega.a ∧ q'.1.1 = omega.a ∧
      q.2.1 = omega.b ∧ q'.2.1 = omega.b <;> simp [hg]

/-- The single classical point of the fully discarded shortage register. -/
private abbrev abortRow : (Boundary.leaf lateSelectionAbortSystem).space :=
  (Boundary.leafSpaceEquiv lateSelectionAbortSystem).symm
    ((TwoParty.pairEquiv Unit Unit).symm ((), ()))

/-- **Entry of the complete-record discard.** Alice and then Bob trace out their complete local
records, so the single entry of the discarded register sums the input diagonal over both records. -/
theorem discardCompletedRecords_denote_apply (N : ℕ)
    (xi : Op (weightedStreamSystem (finishAcc Unit N) 0).total) :
    (discardCompletedRecords N).denote xi abortRow abortRow =
      ∑ rB : CompletedLocalRecord N, ∑ rA : CompletedLocalRecord N,
        xi ((TwoParty.pairEquiv _ _).symm (rA, rB))
          ((TwoParty.pairEquiv _ _).symm (rA, rB)) := by
  have hpoint (x : (Boundary.leaf lateSelectionAbortSystem).space) : x = abortRow := by
    apply (Boundary.leafSpaceEquiv lateSelectionAbortSystem).injective
    apply (TwoParty.pairEquiv Unit Unit).injective
    exact Subsingleton.elim _ _
  have hout : ((discardCompletedRecords N).denote xi).trace =
      (discardCompletedRecords N).denote xi abortRow abortRow := by
    rw [Matrix.trace, Finset.sum_eq_single abortRow]
    · rfl
    · intro x _ hx
      exact (hx (hpoint x)).elim
    · simp
  rw [← hout, Program.trace_denote]
  have hsum := Equiv.sum_comp (TwoParty.pairEquiv
    (CompletedLocalRecord N) (CompletedLocalRecord N)).symm (fun q => xi q q)
  simp only [Matrix.trace, Matrix.diag_apply]
  calc
    _ = ∑ q : CompletedLocalRecord N × CompletedLocalRecord N,
        xi ((TwoParty.pairEquiv _ _).symm q) ((TwoParty.pairEquiv _ _).symm q) := hsum.symm
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Exact arbitrary-operator diagonal value in a key-free shortage branch.

Both complete local records are physically discarded after their basis strings and shuffle have
been announced.  The branch retains the full metadata and sums every local outcome string; there
is no key register or quota-success premise.
-/
theorem weightedLatePublicSelectionProgram_abort_apply
    (pA pB : PMF Basis) (N nK mZ mX : ℕ)
    (omega : RawControl N)
    (h : ¬ HasQuotas nK mZ mX omega)
    (rho : Op (weightedStreamSystem Unit N).total) :
    (weightedLatePublicSelectionProgram pA pB N nK mZ mX).denote rho
        (lateSelectionAbortAt N nK mZ mX omega h)
        (lateSelectionAbortAt N nK mZ mX omega h) =
      (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ *
      ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
      ((Sampling.basisStringLaw N pB omega.b).toReal : ℂ) *
      ∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
        (matrixConjLinear
          (fixedBasisPairKraus
            (completeStoredRecords omega.a xA)
            (completeStoredRecords omega.b xB))
          (reindexOp (weightedScheduleUnitInputEquiv N) rho)) () () := by
  unfold weightedLatePublicSelectionProgram
  rw [Program.denote_graft]
  have hrow (x : (lateSelectionBoundary N nK mZ mX).space) :
      ((Boundary.graftSpaceEquiv
        (.leaf (weightedStreamSystem (finishAcc Unit N) 0))
        (fun _ => lateSelectionBoundary N nK mZ mX)).symm ⟨(), x⟩) = x := by
    simpa only [Boundary.graftSpaceEquiv_leaf_apply] using
      (Equiv.symm_apply_apply
        (Boundary.graftSpaceEquiv
          (.leaf (weightedStreamSystem (finishAcc Unit N) 0))
          (fun _ => lateSelectionBoundary N nK mZ mX)) x)
  rw [← hrow (lateSelectionAbortAt N nK mZ mX omega h),
    ← hrow (lateSelectionAbortAt N nK mZ mX omega h)]
  change (Program.controlledContinuation
      (fun _ : (Boundary.leaf (weightedStreamSystem (finishAcc Unit N) 0)).Exit =>
        latePublicSelectionProgram N nK mZ mX)
      ((weightedMeasurementSchedule pA pB N).denote rho)) _ _ = _
  rw [Program.controlledContinuation_sameExit]
  let sigma : Op (weightedStreamSystem (finishAcc Unit N) 0).total :=
    ((Boundary.exitKraus
      (.leaf (weightedStreamSystem (finishAcc Unit N) 0)) ())ᴴ *
        (weightedMeasurementSchedule pA pB N).denote rho *
      Boundary.exitKraus
        (.leaf (weightedStreamSystem (finishAcc Unit N) 0)) ())
  change (latePublicSelectionProgram N nK mZ mX).denote sigma
    (lateSelectionAbortAt N nK mZ mX omega h)
    (lateSelectionAbortAt N nK mZ mX omega h) = _
  have hB : (completedBasisBobAnnouncement N omega.a).out omega.b =
      weightedStreamSystem (finishAcc Unit N) 0 := by
    simp only [completedBasisBobAnnouncement, completedBasisAliceAnnouncement,
      AnnouncedAction.out_ofInstrument, weightedStreamSystem, TwoParty.set_alice,
      TwoParty.set_bob]
    rfl
  have hself : (shuffleAnnouncement N omega.a omega.b).out omega.order =
      (completedBasisBobAnnouncement N omega.a).out omega.b := by
    rw [shuffleAnnouncement, AnnouncedAction.out_ofInstrument]
    exact MultipartiteSystem.set_self _ _
  let hfinal := hself.trans hB
  let tau := (completedBasisAliceAnnouncement N).liftedOperation omega.a sigma
  let upsilonRaw := (completedBasisBobAnnouncement N omega.a).liftedOperation omega.b tau
  let upsilon := upsilonRaw.submatrix
    (Equiv.cast (congrArg MultipartiteSystem.total hB)).symm
    (Equiv.cast (congrArg MultipartiteSystem.total hB)).symm
  have hcastB (rA rB : CompletedLocalRecord N) :
      (Equiv.cast (congrArg MultipartiteSystem.total hB)).symm
          ((TwoParty.pairEquiv _ _).symm (rA, rB)) =
        ((completedBasisBobAnnouncement N omega.a).out omega.b).pairEquiv.symm (rA, rB) := by
    change cast (congrArg MultipartiteSystem.total hB.symm)
      ((weightedStreamSystem (finishAcc Unit N) 0).pairEquiv.symm (rA, rB)) = _
    rw [MultipartiteSystem.cast_pairEquiv_symm hB.symm]
    rfl
  have hshuffle :
      ((shuffleAnnouncement N omega.a omega.b).liftedOperation
        (omega.order, ()) upsilonRaw).submatrix
          (Equiv.cast (congrArg MultipartiteSystem.total hfinal)).symm
          (Equiv.cast (congrArg MultipartiteSystem.total hfinal)).symm =
        (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ • upsilon := by
    ext z z'
    have hop := congrFun (congrFun
      (shuffleAnnouncement_liftedOperation_apply N omega.a omega.b omega.order upsilonRaw)
      ((Equiv.cast (congrArg MultipartiteSystem.total hB)).symm z))
      ((Equiv.cast (congrArg MultipartiteSystem.total hB)).symm z')
    change (shuffleAnnouncement N omega.a omega.b).liftedOperation (omega.order, ()) upsilonRaw
      (cast (congrArg MultipartiteSystem.total hself.symm)
        (cast (congrArg MultipartiteSystem.total hB.symm) z))
      (cast (congrArg MultipartiteSystem.total hself.symm)
        (cast (congrArg MultipartiteSystem.total hB.symm) z')) = _ at hop
    simpa only [cast_cast] using hop
  unfold latePublicSelectionProgram lateSelectionAbortAt
  simp only [id_eq]
  have hAlice := Program.denote_then_publicSpaceEquiv_symm_apply
    (completedBasisAliceAnnouncement N) (Equiv.refl _) (fun _ => rfl)
  simp only [completedBasisAliceAnnouncement_announce] at hAlice
  refine (hAlice _ _ sigma omega.a _ _).trans ?_
  have hBob := Program.denote_then_publicSpaceEquiv_symm_apply
    (completedBasisBobAnnouncement N omega.a) (Equiv.refl _) (fun _ => rfl)
  simp only [completedBasisBobAnnouncement_announce] at hBob
  refine (hBob _ _ tau omega.b _ _).trans ?_
  have hShuffle := Program.denote_then_publicSpaceEquiv_symm_apply
    (shuffleAnnouncement N omega.a omega.b) (Equiv.prodUnique _ _) (fun _ => rfl)
  simp only [shuffleAnnouncement_announce] at hShuffle
  refine (hShuffle _ _ upsilonRaw (omega.order, ()) _ _).trans ?_
  rw [Program.denote_cast_apply hfinal rfl]
  simp only [Equiv.cast_refl, Equiv.refl_apply]
  change (quotaSelectionContinuation N nK mZ mX omega).denote
    (((shuffleAnnouncement N omega.a omega.b).liftedOperation
      (omega.order, ()) upsilonRaw).submatrix
        (Equiv.cast (congrArg MultipartiteSystem.total hfinal)).symm
        (Equiv.cast (congrArg MultipartiteSystem.total hfinal)).symm) _ _ = _
  rw [hshuffle]
  simp only [map_smul, Matrix.smul_apply, smul_eq_mul]
  have hquota : HEq
      (quotaSelectionContinuation N nK mZ mX omega)
      (discardCompletedRecords N) := by
    unfold quotaSelectionContinuation
    split
    · contradiction
    · rename_i h'
      cases Subsingleton.elim h' h
      simp only [eq_mpr_eq_cast]
      exact cast_heq _ _
  let hleaf : (Boundary.leaf lateSelectionAbortSystem) =
      lateSelectionLeaf N nK mZ mX omega := by
    symm
    simp [lateSelectionLeaf, h]
  have hquotaCast :
      quotaSelectionContinuation N nK mZ mX omega =
        hleaf ▸ discardCompletedRecords N := by
    apply eq_of_heq
    exact hquota.trans
      (eqRec_heq hleaf (discardCompletedRecords N)).symm
  have htransport {B C : Boundary Party} (hb : B = C)
      (p : Program (weightedStreamSystem (finishAcc Unit N) 0) B)
      (xi : Op (weightedStreamSystem (finishAcc Unit N) 0).total)
      (x y : B.space) {x' y' : C.space}
      (hx : HEq x' x) (hy : HEq y' y) :
      ((hb ▸ p).denote xi) x' y' = p.denote xi x y := by
    cases hb
    cases hx
    cases hy
    rfl
  rw [hquotaCast]
  have hupsilonDiag
      (rA rB : CompletedLocalRecord N) :
      upsilon ((TwoParty.pairEquiv _ _).symm (rA, rB))
          ((TwoParty.pairEquiv _ _).symm (rA, rB)) =
        if completedBasisString N rA = omega.a ∧
            completedBasisString N rB = omega.b then
          sigma ((TwoParty.pairEquiv _ _).symm (rA, rB))
            ((TwoParty.pairEquiv _ _).symm (rA, rB))
        else 0 := by
    change upsilonRaw
      ((Equiv.cast (congrArg MultipartiteSystem.total hB)).symm
        ((TwoParty.pairEquiv _ _).symm (rA, rB)))
      ((Equiv.cast (congrArg MultipartiteSystem.total hB)).symm
        ((TwoParty.pairEquiv _ _).symm (rA, rB))) = _
    rw [hcastB]
    exact completedBasisAnnouncements_liftedOperation_diag N omega.a omega.b sigma rA rB
  let recordStreamEquiv : CompletedLocalRecord N ≃
      (Fin N → StoredRecord) :=
    (finishedStreamEquiv Unit N).trans (unitProdEquiv _)
  have hsumRecords (g : CompletedLocalRecord N → ℂ) :
      (∑ q, g q) = ∑ r : Fin N → StoredRecord,
        g (recordStreamEquiv.symm r) := by
    exact (Equiv.sum_comp recordStreamEquiv.symm g).symm
  have hcompletedBasis (r : Fin N → StoredRecord) :
      completedBasisString N (recordStreamEquiv.symm r) =
        storedBasisString r := by
    simp [completedBasisString, recordStreamEquiv, finishedStreamEquiv,
      unitProdEquiv]
  let recordDataEquiv : (Fin N → StoredRecord) ≃
      (Fin N → Basis) × (Fin N → Bit) :=
    { toFun := fun r =>
        (storedBasisString r, fun i => (r i).2.2)
      invFun := fun q i => ((), (q.1 i, q.2 i))
      left_inv := by
        intro r
        funext i
        rcases hri : r i with ⟨u, theta, x⟩
        rcases u with ⟨⟩
        simp only [storedBasisString, hri]
      right_inv := by
        rintro ⟨theta, x⟩
        rfl }
  have hrecordDataSymm
      (q : (Fin N → Basis) × (Fin N → Bit)) :
      recordDataEquiv.symm q =
        fun i => ((), (q.1 i, q.2 i)) := by
    rfl
  have hstoredData (theta : Fin N → Basis) (x : Fin N → Bit) :
      storedBasisString (fun i => ((), (theta i, x i))) = theta := by
    rfl
  have hsumRecordData (g : (Fin N → StoredRecord) → ℂ) :
      (∑ r, g r) =
        ∑ q : (Fin N → Basis) × (Fin N → Bit),
          g (recordDataEquiv.symm q) := by
    exact (Equiv.sum_comp recordDataEquiv.symm g).symm
  have hsigmaRecords (rA rB : Fin N → StoredRecord) :
      sigma
          ((TwoParty.pairEquiv _ _).symm
            (recordStreamEquiv.symm rA, recordStreamEquiv.symm rB))
          ((TwoParty.pairEquiv _ _).symm
            (recordStreamEquiv.symm rA, recordStreamEquiv.symm rB)) =
        ((Sampling.basisStringLaw N pA
          (storedBasisString rA)).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB
          (storedBasisString rB)).toReal : ℂ) *
        (matrixConjLinear (fixedBasisPairKraus rA rB)
          (reindexOp (weightedScheduleUnitInputEquiv N) rho)) () () := by
    have hentry :
        sigma
            ((TwoParty.pairEquiv _ _).symm
              (recordStreamEquiv.symm rA, recordStreamEquiv.symm rB))
            ((TwoParty.pairEquiv _ _).symm
              (recordStreamEquiv.symm rA, recordStreamEquiv.symm rB)) =
          (weightedMeasurementSchedule pA pB N).denote rho
            ((Boundary.leafSpaceEquiv
              (weightedStreamSystem (finishAcc Unit N) 0)).symm
                ((TwoParty.pairEquiv _ _).symm
                  (recordStreamEquiv.symm rA,
                    recordStreamEquiv.symm rB)))
            ((Boundary.leafSpaceEquiv
              (weightedStreamSystem (finishAcc Unit N) 0)).symm
                ((TwoParty.pairEquiv _ _).symm
                  (recordStreamEquiv.symm rA,
                    recordStreamEquiv.symm rB))) := by
      simp [sigma, Matrix.mul_apply, Boundary.exitKraus_apply,
        Boundary.leafSpaceEquiv]
    rw [hentry]
    have hs := weightedMeasurementSchedule_output_apply pA pB N rho
      rA rA rB rB
    simp only [and_self, if_true] at hs
    simpa [sigma, recordStreamEquiv, reindexOp,
      weightedScheduleOutputEquiv, weightedScheduleUnitInputEquiv,
      weightedStreamPairEquiv, weightedScheduleInputBlock] using hs
  rw [htransport hleaf (discardCompletedRecords N) upsilon
    abortRow abortRow (cast_heq _ _) (cast_heq _ _)]
  rw [discardCompletedRecords_denote_apply]
  rw [Finset.sum_comm]
  rw [hsumRecords]
  simp_rw [hsumRecords, hupsilonDiag, hcompletedBasis, hsigmaRecords]
  rw [hsumRecordData]
  simp_rw [hsumRecordData, hrecordDataSymm, hstoredData]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single omega.a]
  · simp only [true_and]
    have hsumB (xA : Fin N → Bit) :
        (∑ thetaB : Fin N → Basis, ∑ xB : Fin N → Bit,
          if thetaB = omega.b then
            ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
              ((Sampling.basisStringLaw N pB thetaB).toReal : ℂ) *
              (matrixConjLinear
                (fixedBasisPairKraus
                  (completeStoredRecords omega.a xA)
                  (completeStoredRecords thetaB xB))
                (reindexOp (weightedScheduleUnitInputEquiv N) rho)) () ()
          else 0) =
        ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
          ((Sampling.basisStringLaw N pB omega.b).toReal : ℂ) *
          ∑ xB : Fin N → Bit,
            (matrixConjLinear
              (fixedBasisPairKraus
                (completeStoredRecords omega.a xA)
                (completeStoredRecords omega.b xB))
              (reindexOp (weightedScheduleUnitInputEquiv N) rho)) () () := by
      rw [Finset.sum_eq_single omega.b]
      · simp only [if_pos]
        rw [← Finset.mul_sum]
      · intro thetaB _ hthetaB
        apply Finset.sum_eq_zero
        intro xB _
        rw [if_neg hthetaB]
      · simp
    let c : ℂ :=
      ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB omega.b).toReal : ℂ)
    have hselectedSums :
        (∑ xA : Fin N → Bit, ∑ thetaB : Fin N → Basis,
          ∑ xB : Fin N → Bit,
            if thetaB = omega.b then
              ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
                ((Sampling.basisStringLaw N pB thetaB).toReal : ℂ) *
                (matrixConjLinear
                  (fixedBasisPairKraus
                    (completeStoredRecords omega.a xA)
                    (completeStoredRecords thetaB xB))
                  (reindexOp (weightedScheduleUnitInputEquiv N) rho)) () ()
            else 0) =
          c * ∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
            (matrixConjLinear
              (fixedBasisPairKraus
                (completeStoredRecords omega.a xA)
                (completeStoredRecords omega.b xB))
              (reindexOp (weightedScheduleUnitInputEquiv N) rho)) () () := by
      calc
        _ = ∑ xA : Fin N → Bit, c *
              ∑ xB : Fin N → Bit,
                (matrixConjLinear
                  (fixedBasisPairKraus
                    (completeStoredRecords omega.a xA)
                    (completeStoredRecords omega.b xB))
                  (reindexOp (weightedScheduleUnitInputEquiv N) rho)) () () := by
          apply Finset.sum_congr rfl
          intro xA _
          exact hsumB xA
        _ = _ := by
          rw [Finset.mul_sum]
    change (Fintype.card (Shuffle omega.a omega.b) : ℂ)⁻¹ *
        (∑ xA : Fin N → Bit, ∑ thetaB : Fin N → Basis,
          ∑ xB : Fin N → Bit,
            if thetaB = omega.b then
              ((Sampling.basisStringLaw N pA omega.a).toReal : ℂ) *
                ((Sampling.basisStringLaw N pB thetaB).toReal : ℂ) *
                (matrixConjLinear
                  (fixedBasisPairKraus
                    (completeStoredRecords omega.a xA)
                    (completeStoredRecords thetaB xB))
                  (reindexOp (weightedScheduleUnitInputEquiv N) rho)) () ()
            else 0) = _
    rw [hselectedSums]
    unfold c
    simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
    simp_rw [Fintype.sum_prod_type]
    ring
  · intro thetaA _ hthetaA
    apply Finset.sum_eq_zero
    intro xA _
    apply Finset.sum_eq_zero
    intro thetaB _
    apply Finset.sum_eq_zero
    intro xB _
    rw [if_neg]
    exact fun hab => hthetaA hab.1
  · simp

/-- The fixed-basis measurement rows of any two basis strings resolve the identity: their Born
weights over all outcome strings add up to the trace.

This is the completeness of the pair of destructive single-round measurements behind the
shortage-branch value; it holds for every operator, with no state, positivity or normalization
hypothesis. -/
theorem sum_matrixConjLinear_fixedBasisPairKraus (N : ℕ) (a b : Fin N → Basis)
    (ρ : Op ((Fin N → Bit) × (Fin N → Bit))) :
    (∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
      matrixConjLinear (fixedBasisPairKraus (completeStoredRecords a xA)
        (completeStoredRecords b xB)) ρ () ()) = ρ.trace := by
  have hcol (θ : Basis) (j j' : Bit) :
      (∑ s : Bit, star (basisUnitary θ s j) * basisUnitary θ s j') = if j = j' then 1 else 0 := by
    have hU : (basisUnitary θ)ᴴ * basisUnitary θ = 1 := by
      cases θ with
      | z => simp [basisUnitary]
      | x => exact Quantum.Gates.hadamard_unitary
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrFun (congrFun hU j) j'
  have hcomplete :
      (∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
        (fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB))ᴴ *
          fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB)) = 1 := by
    ext v v'
    have hterm (xA xB : Fin N → Bit) :
        ((fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB))ᴴ *
            fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB)) v v' =
          ∏ i, (star (basisUnitary (a i) (xA i) (v.1 i)) * basisUnitary (a i) (xA i) (v'.1 i)) *
            (star (basisUnitary (b i) (xB i) (v.2 i)) * basisUnitary (b i) (xB i) (v'.2 i)) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_unique,
        fixedBasisPairKraus, completeStoredRecords, star_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [star_mul']
      ring
    simp only [Matrix.sum_apply, hterm]
    rw [sum_sum_prod (fun i s t =>
      (star (basisUnitary (a i) s (v.1 i)) * basisUnitary (a i) s (v'.1 i)) *
        (star (basisUnitary (b i) t (v.2 i)) * basisUnitary (b i) t (v'.2 i)))]
    simp only [← Finset.sum_mul_sum, hcol, Finset.prod_mul_distrib, Finset.prod_boole,
      Finset.mem_univ, forall_const, Matrix.one_apply]
    by_cases hv : v = v'
    · subst hv
      simp
    · rw [if_neg hv]
      by_cases h1 : ∀ i, v.1 i = v'.1 i
      · have h2 : ¬ ∀ i, v.2 i = v'.2 i := fun h2 => hv (Prod.ext (funext h1) (funext h2))
        rw [if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  calc
    _ = ∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
          Matrix.trace ((fixedBasisPairKraus (completeStoredRecords a xA)
              (completeStoredRecords b xB))ᴴ *
            fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB) * ρ) := by
      refine Finset.sum_congr rfl fun xA _ => Finset.sum_congr rfl fun xB _ => ?_
      rw [← Matrix.trace_mul_cycle]
      simp [matrixConjLinear, Matrix.trace]
    _ = Matrix.trace ((∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
          (fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB))ᴴ *
            fixedBasisPairKraus (completeStoredRecords a xA) (completeStoredRecords b xB)) *
          ρ) := by
      rw [Finset.sum_mul, Matrix.trace_sum]
      simp_rw [Finset.sum_mul, Matrix.trace_sum]
    _ = ρ.trace := by rw [hcomplete, Matrix.one_mul]

/-- **The shortage branch carries its raw-control mass, for every input.**  At a public control
failing a quota, both parties have discarded their complete records; the unique abort entry is the
raw-control mass of `ω` times the trace of the input.  No positivity, normalization or product
structure of `ρ` is used. -/
theorem weightedLatePublicSelectionProgram_shortage_apply
    (pA pB : PMF Basis) (N nK mZ mX : ℕ) (ω : RawControl N) (h : ¬ HasQuotas nK mZ mX ω)
    (ρ : Op (weightedStreamSystem Unit N).total) :
    (weightedLatePublicSelectionProgram pA pB N nK mZ mX).denote ρ
        (lateSelectionAbortAt N nK mZ mX ω h) (lateSelectionAbortAt N nK mZ mX ω h) =
      ((rawControlLaw N pA pB ω).toReal : ℂ) * ρ.trace := by
  rw [weightedLatePublicSelectionProgram_abort_apply, sum_matrixConjLinear_fixedBasisPairKraus,
    rawControlLaw_toReal_eq]
  rw [trace_reindexOp]

end QKD.BB84.Measurement
