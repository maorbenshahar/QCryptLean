import QCryptLean.QKD.BB84.Reduction.Factorization.Reconstruction
import QCryptLean.QKD.BB84.Measurement.LatePublicControl.BranchValues
import QCryptLean.QKD.BB84.Program

/-!
# The shortage sector of the retained-round factorization

Assume `nK + mZ + mX ≤ N` and let `omega` be a raw control that misses a quota.  The BB84 program
then aborts; its only complete output over this exit is the metadata-bearing abort output
`shortageCompleteOutput … omega hshort`, which keeps `omega` at its public exit.  For every complex
input operator, `retainedFactorization_shortage_sector` identifies the program's diagonal output
entry there with the corresponding entry of
`reconstruction ∘ retainedControlLift (retainedAnalysisReal …) ∘ comparisonPre`.

On the program side the entry is the abort branch value of the sifting stage
(`Measurement.weightedLatePublicSelectionProgram_abort_apply`): the raw-control probability of
`omega` times the trace of the input.  On the factorized side the shortage branches of the
reconstruction trace out the retained output of the failure-control blocks, the retained real
experiment preserves traces, and only the first shortage label carries the failure coefficient of
`comparisonPre`.  The totalized failure kernel reproduces the raw-control law
(`Sampling.totalizedReconstructedStatusRawLaw_eq`).

Pfister et al., arXiv:1506.07502v3, Section IV, Protocol 3, Step 5', likewise aborts when
fixed-round quotas cannot be met, and their Appendix C analyzes the sifting outputs and the abort
probability; this is context for the shortage branch, not an identity for these coordinates.
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
attribute [local instance] comparisonControlCardNeZero

/-- At a complete shortage output the reconstruction channel keeps only the totalized failure
kernel against the retained diagonal of the failure-control blocks. -/
private theorem reconstruction_shortage
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (mid : Quantum.Operators.Op
      (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC *
        Fintype.card (ComparisonControl N (nK + mZ + mX)))) :
    reconstruction N nK mZ mX ell ellEV leakEC pA pB mid
        ((Fintype.equivFin _)
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort))
        ((Fintype.equivFin _)
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)) =
      ∑ j : Fin (nK + mZ + mX),
        ((totalFailureControlKernel N nK mZ mX pA pB j omega).toReal : ℂ) *
          ∑ r : Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC),
            Matrix.reindex
              (reconstructionInputEquiv N nK mZ mX ell ellEV leakEC).symm
              (reconstructionInputEquiv N nK mZ mX ell ellEV leakEC).symm mid
              (r, Sum.inr j) (r, Sum.inr j) := by
  have hsuccessRow
      (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (pi : Equiv.Perm (Fin (nK + mZ + mX)))
      (eta : SelectedControlSupport N nK mZ mX pA pB S pi)
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB
          (Sum.inl ⟨S, pi, eta⟩)
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) x = 0 := by
    change reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC
        pA pB S pi eta
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) x = 0
    unfold reconstructionSuccessKraus
    dsimp only
    split
    · rename_i hc
      exfalso
      have hrc := congrArg (fun y =>
        QKD.BB84.lateSelectionExitEquiv N nK mZ mX
          ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC) y.1).1) hc.2.2
      rw [shortageCompleteOutput_rawControl] at hrc
      rw [successCompleteOutputEmbedding_exit] at hrc
      unfold successExitMap at hrc
      rw [Equiv.apply_symm_apply] at hrc
      have hrc' : omega = eta.1 := by
        exact hrc
      apply hshort
      rw [hrc']
      exact selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi eta
    · rfl
  let EPost := reconstructionInputEquiv N nK mZ mX ell ellEV leakEC
  let sigma : Matrix
      (ReconstructionInput N nK mZ mX ell ellEV leakEC)
      (ReconstructionInput N nK mZ mX ell ellEV leakEC) ℂ :=
    Matrix.reindex EPost.symm EPost.symm mid
  have hmid : mid = Matrix.reindex EPost EPost sigma := by
    simp [sigma, Matrix.reindex_apply]
  have hrow_of_control_ne
      (j : Fin (nK + mZ + mX))
      (r : Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC))
      (eta : FailureControlSupport N nK mZ mX pA pB j)
      (heta : eta.1 ≠ omega)
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB
          (Sum.inr ⟨j, r, eta⟩)
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) x = 0 := by
    change reconstructionShortageKraus N nK mZ mX ell ellEV leakEC
        pA pB j r eta
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) x = 0
    unfold reconstructionShortageKraus
    refine (Matrix.smul_apply _ _ _ _).trans ?_
    have hrow : shortageCompleteOutput N nK mZ mX ell ellEV leakEC eta.1
        (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j eta) ≠
        shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort := by
      intro heq
      have hrc := congrArg (fun y =>
        QKD.BB84.lateSelectionExitEquiv N nK mZ mX
          ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC) y.1).1) heq
      rw [shortageCompleteOutput_rawControl,
        shortageCompleteOutput_rawControl] at hrc
      exact heta hrc
    exact (congrArg (fun z : ℂ => _ • z)
      (Matrix.single_apply_of_row_ne hrow
        ((r, Sum.inr j) : ReconstructionInput N nK mZ mX ell ellEV leakEC)
        x (1 : ℂ))).trans (smul_zero _)
  -- The right-hand side reads `sigma` on the diagonal.
  change _ = ∑ j : Fin (nK + mZ + mX),
    ((totalFailureControlKernel N nK mZ mX pA pB j omega).toReal : ℂ) *
      ∑ r : Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC),
        sigma (r, Sum.inr j) (r, Sum.inr j)
  unfold reconstruction
  rw [hmid, coordinateLinear_reindex_apply]
  unfold Instrument.channel Instrument.operation
  simp only [Fintype.sum_unique, LinearMap.sum_apply, Matrix.sum_apply, reconstructionInstrument]
  -- Every success row vanishes at a shortage output.
  have hsuccess
      (k : Σ S : Set.powersetCard (Fin N) (nK + mZ + mX),
        Σ pi : Equiv.Perm (Fin (nK + mZ + mX)), SelectedControlSupport N nK mZ mX pA pB S pi) :
      matrixConjLinear (reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB (Sum.inl k)) sigma
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) = 0 :=
    matrixConjLinear_apply_eq_zero_of_row_left _ _ (funext (hsuccessRow k.1 k.2.1 k.2.2)) _
  conv_lhs => tactic => exact Fintype.sum_sum_type _
  simp only [hsuccess, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  let K := totalFailureControlKernel N nK mZ mX pA pB j
  let x0 : ReconstructionInput N nK mZ mX ell ellEV leakEC := (r, Sum.inr j)
  by_cases hpos : 0 < K omega
  · -- Only the shortage row of the actual control `omega` survives; it reads `sigma x0 x0`.
    let eta0 : FailureControlSupport N nK mZ mX pA pB j := ⟨omega, hpos⟩
    have hrow_self :
        reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB (Sum.inr ⟨j, r, eta0⟩)
            (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) =
          Pi.single x0 (Instrument.weightedChoiceScale K omega) := by
      funext x
      change reconstructionShortageKraus N nK mZ mX ell ellEV leakEC
          pA pB j r eta0
            (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) x = _
      unfold reconstructionShortageKraus
      refine (Matrix.smul_apply _ _ _ _).trans ?_
      rw [Pi.single_apply]
      by_cases hx : x = x0
      · subst x
        rw [ite_eq_left rfl]
        refine (congrArg (fun z : ℂ => (_ : ℂ) • z)
          (Matrix.single_apply_same _ _ (1 : ℂ))).trans ?_
        exact mul_one _
      · rw [ite_eq_right hx]
        exact (congrArg (fun z : ℂ => (_ : ℂ) • z)
          (Matrix.single_apply_of_col_ne _ _ (Ne.symm hx) (1 : ℂ))).trans (smul_zero _)
    rw [Fintype.sum_eq_single eta0 fun eta heta =>
        matrixConjLinear_apply_eq_zero_of_row_left _ _
          (funext (hrow_of_control_ne j r eta fun h => heta (Subtype.ext h))) _,
      matrixConjLinear_apply_of_row_eq_single _ _ hrow_self hrow_self, mul_right_comm,
      mul_comm (Instrument.weightedChoiceScale K omega), Instrument.weightedChoiceScale_star_mul]
  · -- A control of zero weight carries no shortage row at all.
    rw [show K omega = 0 from bot_unique (le_of_not_gt hpos), ENNReal.toReal_zero,
      Complex.ofReal_zero, zero_mul]
    exact Finset.sum_eq_zero fun eta _ =>
      matrixConjLinear_apply_eq_zero_of_row_left _ _
        (funext (hrow_of_control_ne j r eta fun h => hpos (h ▸ eta.2))) _

/-- The program's diagonal entry at a complete shortage output is the late-selection abort entry. -/
private theorem program_denote_shortage_eq_abort
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total) :
    (QKD.BB84.program pA pB N nK mZ mX ell ellEV leakEC
        ec delta Q).denote rho
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) =
    (Measurement.weightedLatePublicSelectionProgram
      pA pB N nK mZ mX).denote rho
      (Measurement.lateSelectionAbortAt N nK mZ mX omega hshort)
      (Measurement.lateSelectionAbortAt N nK mZ mX omega hshort) := by
  unfold QKD.BB84.program
  conv_lhs =>
    tactic => exact congrFun (congrFun (LinearMap.congr_fun
      (Program.denote_graft (Measurement.weightedLatePublicSelectionProgram
        pA pB N nK mZ mX) _) rho) _) _
  let outer := Measurement.lateSelectionAbortAt N nK mZ mX omega hshort
  -- The complete shortage output, typed as a point of the grafted boundary.
  let y : ((Measurement.lateSelectionBoundary N nK mZ mX).graft
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC)).space :=
    shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort
  let G := Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
  have hy : y = G.symm (G y) := (G.symm_apply_apply y).symm
  change (Program.controlledContinuation
      (QKD.BB84.completeContinuation N nK mZ mX ell ellEV leakEC ec delta Q)
      ((Measurement.weightedLatePublicSelectionProgram
        pA pB N nK mZ mX).denote rho)) y y = _
  rw [hy]
  generalize hz : G y = z
  rcases z with ⟨e, c⟩
  rw [Program.controlledContinuation_sameExit]
  have hzfst : (G y).1 = e := congrArg Sigma.fst hz
  have heraw : QKD.BB84.lateSelectionExitEquiv N nK mZ mX e = omega := by
    rw [← hzfst]
    dsimp only [G]
    rw [Boundary.graftSpaceEquiv_fst]
    exact shortageCompleteOutput_rawControl
      N nK mZ mX ell ellEV leakEC omega hshort
  have he : e = outer.1 := by
    apply (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).injective
    rw [heraw]
    rcases omega with ⟨a, b, order⟩
    rfl
  have hshortE : ¬ HasQuotas nK mZ mX
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX e) := by
    rw [heraw]
    exact hshort
  have hstart : (Measurement.lateSelectionBoundary N nK mZ mX).system e =
      Measurement.lateSelectionAbortSystem := by
    rcases e with ⟨a, b, order, leaf⟩
    have h' : ¬ HasQuotas nK mZ mX ⟨a, b, order⟩ := by
      simpa [QKD.BB84.lateSelectionExitEquiv] using hshortE
    change (Measurement.lateSelectionLeaf N nK mZ mX
      ⟨a, b, order⟩).system leaf = _
    rw [QKD.BB84.lateSelectionLeaf_system, ite_eq_right h']
  have hout : QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC e =
      .leaf Measurement.lateSelectionAbortSystem := by
    simp [QKD.BB84.completeContinuationBoundary, hshortE]
  have hextract
      (sigma : TypedLOCC.Op
        (Measurement.lateSelectionBoundary N nK mZ mX).space)
      (q q' : ((Measurement.lateSelectionBoundary N nK mZ mX).system e).total) :
      (((Measurement.lateSelectionBoundary N nK mZ mX).exitKraus e)ᴴ *
          sigma *
        (Measurement.lateSelectionBoundary N nK mZ mX).exitKraus e) q q' =
        sigma ⟨e, q⟩ ⟨e, q'⟩ := by
    -- Both exit inclusions pick out the boundary points over the exit `e`.
    simp [Matrix.mul_apply, Boundary.exitKraus_apply]
  unfold QKD.BB84.completeContinuation
  rw [dite_eq_right hshortE]
  -- At a shortage exit the continuation is `done`, transported along `hstart` and `hout`.
  simp only [eq_mpr_eq_cast]
  rw [Program.denote_cast_apply hstart rfl]
  rw [Program.denote_cast_apply rfl hout]
  let qpoint : ((Measurement.lateSelectionBoundary N nK mZ mX).system e).total :=
    (Equiv.cast (congrArg MultipartiteSystem.total hstart)).symm
      (Boundary.leafSpaceEquiv Measurement.lateSelectionAbortSystem
        (Equiv.cast (congrArg Boundary.space hout) c))
  rw [Program.denote_done]
  simp only [LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [hextract]
  simp only [Equiv.cast_refl, Equiv.refl_symm, Equiv.refl_apply,
    Equiv.cast_apply]
  have hpoint : (⟨e, qpoint⟩ :
      (Measurement.lateSelectionBoundary N nK mZ mX).space) = outer := by
    apply Sigma.ext he
    let htype := congrArg (fun f =>
      ((Measurement.lateSelectionBoundary N nK mZ mX).system f).total) he
    have hstartOuter :
        (Measurement.lateSelectionBoundary N nK mZ mX).system outer.1 =
          Measurement.lateSelectionAbortSystem := by
      rw [← he]
      exact hstart
    have hsub (u v :
        ((Measurement.lateSelectionBoundary N nK mZ mX).system outer.1).total) :
        u = v := by
      apply (Equiv.cast (congrArg MultipartiteSystem.total hstartOuter)).injective
      apply (TwoParty.pairEquiv Unit Unit).injective
      apply Prod.ext
      · exact Unit.ext _ _
      · exact Unit.ext _ _
    exact (cast_heq htype qpoint).symm.trans
      (heq_of_eq (hsub (cast htype qpoint) outer.2))
  change (Measurement.weightedLatePublicSelectionProgram
      pA pB N nK mZ mX).denote rho
        (⟨e, qpoint⟩ : (Measurement.lateSelectionBoundary N nK mZ mX).space)
        ⟨e, qpoint⟩ = _
  rw [hpoint]

/-- Closed form of the program's diagonal entry at a complete shortage output. -/
private theorem program_denote_shortage_output_formula
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total) :
    (QKD.BB84.program pA pB N nK mZ mX ell ellEV leakEC
        ec delta Q).denote rho
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) =
      ((rawControlLaw N pA pB omega).toReal : ℂ) *
        ∑ xA : Fin N → Bit, ∑ xB : Fin N → Bit,
          matrixConjLinear
            (fixedBasisPairKraus
              (completeStoredRecords omega.a xA)
              (completeStoredRecords omega.b xB))
            (reindexOp (weightedScheduleUnitInputEquiv N) rho) () () := by
  rw [program_denote_shortage_eq_abort]
  rw [weightedLatePublicSelectionProgram_abort_apply]
  rw [rawControlLaw_toReal_eq]

/-- Retained-real trace of a failure control block of the lifted preprocessor output. -/
private theorem retainedMid_failure_trace
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : TypedLOCC.Op (ComparisonPreInput N))
    (j : Fin (nK + mZ + mX)) :
    let pre := comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex (comparisonPreInputEquiv N)
        (comparisonPreInputEquiv N) rho)
    let mid := retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
      (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q) pre
    let EPost := reconstructionInputEquiv N nK mZ mX ell ellEV leakEC
    let sigma := Matrix.reindex EPost.symm EPost.symm mid
    (∑ r : Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC),
      sigma (r, Sum.inr j) (r, Sum.inr j)) =
      if j.val = 0 then
        comparisonPreFailureCoefficient N nK mZ mX pA pB *
          ∑ a : ComparisonPreInput N, rho a a
      else 0 := by
  dsimp only
  unfold retainedControlLift reconstructionInputEquiv
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm]
  let regrouped := Matrix.reindex
    (comparisonPreToRetainedControlEquiv N (nK + mZ + mX))
    (comparisonPreToRetainedControlEquiv N (nK + mZ + mX))
    (comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex (comparisonPreInputEquiv N)
        (comparisonPreInputEquiv N) rho))
  let block : Quantum.Operators.Op (4 ^ (nK + mZ + mX)) :=
    Matrix.of fun i k =>
      regrouped
        (finProdFinEquiv
          (i, Fintype.equivFin _
            (Sum.inr j : ComparisonControl N (nK + mZ + mX))))
        (finProdFinEquiv
          (k, Fintype.equivFin _
            (Sum.inr j : ComparisonControl N (nK + mZ + mX))))
  have hregroup (i k : Fin (4 ^ (nK + mZ + mX))) :
      regrouped
        (finProdFinEquiv
          (i, Fintype.equivFin _
            (Sum.inr j : ComparisonControl N (nK + mZ + mX))))
        (finProdFinEquiv
          (k, Fintype.equivFin _
            (Sum.inr j : ComparisonControl N (nK + mZ + mX)))) =
      comparisonPreEntry N nK mZ mX pA pB rho
        ((comparisonSelectedToRoundEquiv (nK + mZ + mX)).symm i, Sum.inr j)
        ((comparisonSelectedToRoundEquiv (nK + mZ + mX)).symm k, Sum.inr j) := by
    dsimp only [regrouped]
    unfold comparisonPre
    have hcoord (u : Fin (4 ^ (nK + mZ + mX))) :
        (comparisonPreToRetainedControlEquiv N
          (nK + mZ + mX)).symm
          (finProdFinEquiv
            (u, Fintype.equivFin _
              (Sum.inr j : ComparisonControl N (nK + mZ + mX)))) =
        comparisonPreOutputEquiv N (nK + mZ + mX)
          ((comparisonSelectedToRoundEquiv (nK + mZ + mX)).symm u,
            Sum.inr j) := by
      unfold comparisonPreToRetainedControlEquiv comparisonPreOutputEquiv
      simp
      rfl
    change (coordinateLinear (comparisonPreInputEquiv N)
        (comparisonPreOutputEquiv N (nK + mZ + mX))
        (comparisonPreInstrument N nK mZ mX pA pB hN).channel)
      (Matrix.reindex (comparisonPreInputEquiv N)
        (comparisonPreInputEquiv N) rho)
      ((comparisonPreToRetainedControlEquiv N
        (nK + mZ + mX)).symm
          (finProdFinEquiv
            (i, Fintype.equivFin _
              (Sum.inr j : ComparisonControl N (nK + mZ + mX)))))
      ((comparisonPreToRetainedControlEquiv N
        (nK + mZ + mX)).symm
          (finProdFinEquiv
            (k, Fintype.equivFin _
              (Sum.inr j : ComparisonControl N (nK + mZ + mX))))) = _
    rw [hcoord i, hcoord k, coordinateLinear_reindex_apply]
    rw [comparisonPreInstrument_channel_apply]
  have htrace : (∑ i : Fin (4 ^ (nK + mZ + mX)), block i i) =
      if j.val = 0 then
        comparisonPreFailureCoefficient N nK mZ mX pA pB *
          ∑ a : ComparisonPreInput N, rho a a
      else 0 := by
    let i0 := comparisonSelectedToRoundEquiv (nK + mZ + mX)
      (comparisonZeroNativeInput (nK + mZ + mX))
    rw [Finset.sum_eq_single i0]
    · rw [show block i0 i0 =
          if j.val = 0 then
            comparisonPreFailureCoefficient N nK mZ mX pA pB *
              ∑ a : ComparisonPreInput N, rho a a
          else 0 by
        rw [show block i0 i0 = comparisonPreEntry N nK mZ mX pA pB rho
            (comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j)
            (comparisonZeroNativeInput (nK + mZ + mX), Sum.inr j) by
          dsimp only [block, Matrix.of_apply]
          rw [hregroup]
          simp [i0]]
        simp [comparisonPreEntry]]
    · intro i _ hi
      rw [show block i i = comparisonPreEntry N nK mZ mX pA pB rho
          ((comparisonSelectedToRoundEquiv (nK + mZ + mX)).symm i, Sum.inr j)
          ((comparisonSelectedToRoundEquiv (nK + mZ + mX)).symm i, Sum.inr j) by
        exact hregroup i i]
      simp only [comparisonPreEntry]
      rw [ite_eq_right]
      intro hc
      apply hi
      calc
        i = comparisonSelectedToRoundEquiv (nK + mZ + mX)
              ((comparisonSelectedToRoundEquiv (nK + mZ + mX)).symm i) :=
            ((comparisonSelectedToRoundEquiv
              (nK + mZ + mX)).apply_symm_apply i).symm
        _ = i0 := by rw [hc.2.2.1]
    · intro hi
      exact (hi (Finset.mem_univ i0)).elim
  change (∑ x,
    Quantum.Channels.mapTensorId
      (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)
      regrouped
      (finProdFinEquiv
        (x, Fintype.equivFin _
          (Sum.inr j : ComparisonControl N (nK + mZ + mX))))
      (finProdFinEquiv
        (x, Fintype.equivFin _
          (Sum.inr j : ComparisonControl N (nK + mZ + mX))))) = _
  simp_rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  simp only [finProdFinEquiv_symm_apply,
    Quantum.Channels.finProdFinEquiv_apply_divNat,
    Quantum.Channels.finProdFinEquiv_apply_modNat]
  change (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q block).trace = _
  rw [(retainedAnalysisReal_isCPTP
    nK mZ mX ell ellEV leakEC ec delta Q).2.2 block]
  exact htrace

/-- The totalized status law reproduces the raw-control law on a shortage exit. -/
private theorem totalized_failure_mass_formula
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) (omega : RawControl N)
    (hshort : ¬ HasQuotas nK mZ mX omega) :
    let hn : nK + mZ + mX ≠ 0 := by
      intro hzero
      have hnK : nK = 0 := by omega
      have hmZ : mZ = 0 := by omega
      have hmX : mX = 0 := by omega
      subst nK
      subst mZ
      subst mX
      exact hshort (by simp [HasQuotas])
    let j0 : Fin (nK + mZ + mX) := ⟨0, Nat.pos_of_ne_zero hn⟩
    selectionFailureMass N nK mZ mX pA pB *
        totalFailureControlKernel N nK mZ mX pA pB j0 omega =
      rawControlLaw N pA pB omega := by
  dsimp only
  have hn : nK + mZ + mX ≠ 0 := by
    intro hzero
    have hnK : nK = 0 := by omega
    have hmZ : mZ = 0 := by omega
    have hmX : mX = 0 := by omega
    subst nK
    subst mZ
    subst mX
    exact hshort (by simp [HasQuotas])
  have hpoint := congrArg
    (fun P : PMF (Bool × RawControl N) => P (false, omega))
    (totalizedReconstructedStatusRawLaw_eq N nK mZ mX pA pB hN)
  change totalizedReconstructedStatusRawLaw N nK mZ mX pA pB hN
      (false, omega) =
    taggedRawControlLaw N nK mZ mX pA pB (false, omega) at hpoint
  have htagged :
      taggedRawControlLaw N nK mZ mX pA pB (false, omega) =
        rawControlLaw N pA pB omega := by
    rw [taggedRawControlLaw, PMF.map_apply]
    simp only [tsum_fintype]
    rw [Finset.sum_eq_single omega]
    · simp [hshort]
    · intro x _ hne
      simp [show omega ≠ x by exact Ne.symm hne]
    · simp
  rw [htagged] at hpoint
  rw [totalizedReconstructedStatusRawLaw, dite_eq_right hn] at hpoint
  simp only [PMF.bind_apply, PMF.pure_apply, tsum_fintype,
    Fintype.sum_bool, selectionStatusLaw, PMF.ofFintype_apply,
    selectionStatusWeight, Bool.false_eq_true, ite_false, ite_true,
    Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero] at hpoint
  simp only [false_and, ite_false,
    Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at hpoint
  simp only [Finset.sum_const_zero, mul_zero, zero_add] at hpoint
  simpa only [mul_assoc] using hpoint

/-- Complex form of the totalized shortage mass identity. -/
private theorem totalized_failure_complex_mass_formula
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) (omega : RawControl N)
    (hshort : ¬ HasQuotas nK mZ mX omega) :
    let hn : nK + mZ + mX ≠ 0 := by
      intro hzero
      have hnK : nK = 0 := by omega
      have hmZ : mZ = 0 := by omega
      have hmX : mX = 0 := by omega
      subst nK
      subst mZ
      subst mX
      exact hshort (by simp [HasQuotas])
    let j0 : Fin (nK + mZ + mX) := ⟨0, Nat.pos_of_ne_zero hn⟩
    comparisonPreFailureCoefficient N nK mZ mX pA pB *
        ((totalFailureControlKernel N nK mZ mX pA pB j0 omega).toReal : ℂ) =
      ((rawControlLaw N pA pB omega).toReal : ℂ) := by
  dsimp only
  have hmass := totalized_failure_mass_formula
    N nK mZ mX pA pB hN omega hshort
  dsimp only at hmass
  unfold comparisonPreFailureCoefficient
  have hreal := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_mul] at hreal
  exact_mod_cast hreal

/-- On a quota-shortage exit, the BB84 program and the factorized real map have the same diagonal
entry at the metadata-bearing abort output, for every complex input operator. -/
theorem retainedFactorization_shortage_sector
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (omega : RawControl N) (hshort : ¬ HasQuotas nK mZ mX omega)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total) :
    let rhoBits := reindexOp (weightedScheduleUnitInputEquiv N) rho
    let pre := comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex (comparisonPreInputEquiv N)
        (comparisonPreInputEquiv N) rhoBits)
    let mid := retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
      (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q) pre
    (QKD.BB84.program pA pB N nK mZ mX ell ellEV leakEC
        ec delta Q).denote rho
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort) =
    reconstruction N nK mZ mX ell ellEV leakEC pA pB mid
      ((Fintype.equivFin _)
        (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort))
      ((Fintype.equivFin _)
        (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega hshort)) := by
  dsimp only
  rw [program_denote_shortage_output_formula]
  rw [sum_matrixConjLinear_fixedBasisPairKraus]
  rw [reconstruction_shortage]
  simp_rw [retainedMid_failure_trace]
  have hn : nK + mZ + mX ≠ 0 := by
    intro hzero
    have hnK : nK = 0 := by omega
    have hmZ : mZ = 0 := by omega
    have hmX : mX = 0 := by omega
    subst nK
    subst mZ
    subst mX
    exact hshort (by simp [HasQuotas])
  let j0 : Fin (nK + mZ + mX) := ⟨0, Nat.pos_of_ne_zero hn⟩
  rw [Finset.sum_eq_single j0]
  · rw [ite_eq_left (by rfl)]
    have hmass := totalized_failure_complex_mass_formula
      N nK mZ mX pA pB hN omega hshort
    dsimp only at hmass
    rw [← hmass]
    dsimp only [j0]
    change comparisonPreFailureCoefficient N nK mZ mX pA pB *
        ((totalFailureControlKernel N nK mZ mX pA pB
          ⟨0, Nat.pos_of_ne_zero hn⟩ omega).toReal : ℂ) *
          (∑ a, (reindexOp (weightedScheduleUnitInputEquiv N) rho) a a) = _
    ring
  · intro j _ hne
    have hj : j.val ≠ 0 := by
      intro hj0
      apply hne
      apply Fin.ext
      exact hj0
    rw [ite_eq_right hj]
    ring
  · intro hmem
    exact (hmem (Finset.mem_univ j0)).elim

end QKD.BB84.Reduction
