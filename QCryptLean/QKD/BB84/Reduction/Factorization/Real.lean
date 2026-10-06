import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.Reduction.Factorization.Real.Shortage
import QCryptLean.QKD.BB84.Reduction.Factorization.Real.Success
import QCryptLean.QKD.BB84.Program

/-!
# The real map of the retained-round factorization

`coordinates_real_eq_retainedFactorizedReal`: when `nK + mZ + mX ≤ N`, the real map of the BB84
coordinates `QKD.BB84.coordinates … .real` equals `retainedFactorizedReal`, the composite of
`comparisonPre`, the retained real experiment in every control block and the reconstruction
channel.  Output entries are split by the raw controls at the public exits of their two points.
Over one raw control, the success sector (`retainedFactorization_success_sector`) or the shortage
sector (`retainedFactorization_shortage_sector`) applies.  Between distinct raw controls both
sides vanish: the program's real map is block diagonal in its public exits
(`QKD.Protocol.real_isExitBlockDiagonal`), and no reconstruction Kraus branch connects
two raw controls.
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

/-- The reconstruction channel has zero entries between distinct complete raw-control exits. -/
private theorem reconstruction_rawControlDiagonal
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (mid : Quantum.Operators.Op
      (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC *
        Fintype.card (ComparisonControl N (nK + mZ + mX))))
    (omega omega' : RawControl N) (hne : omega ≠ omega')
    (a : (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC
      ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega)).space)
    (b : (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC
      ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega')).space) :
    let G := Boundary.graftSpaceEquiv
      (Measurement.lateSelectionBoundary N nK mZ mX)
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
    reconstruction N nK mZ mX ell ellEV leakEC pA pB mid
      ((Fintype.equivFin _) (G.symm
        ⟨(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega, a⟩))
      ((Fintype.equivFin _) (G.symm
        ⟨(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega', b⟩)) = 0 := by
  dsimp only
  let G := Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
  let y : ReconstructionOutput N nK mZ mX ell ellEV leakEC := G.symm
    ⟨(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega, a⟩
  let z : ReconstructionOutput N nK mZ mX ell ellEV leakEC := G.symm
    ⟨(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega', b⟩
  let rawOf (q : (QKD.BB84.boundary N nK mZ mX ell ellEV leakEC).space) :=
    QKD.BB84.lateSelectionExitEquiv N nK mZ mX
      ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC q.1).1)
  have hrawY : rawOf y = omega := by
    dsimp only [rawOf, y, QKD.BB84.exitEquiv,
      QKD.BB84.boundary]
    refine (congrArg (QKD.BB84.lateSelectionExitEquiv N nK mZ mX)
      ((Boundary.graftSpaceEquiv_fst (Measurement.lateSelectionBoundary N nK mZ mX)
        (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC) _).symm.trans
          (congrArg Sigma.fst (G.apply_symm_apply _)))).trans ?_
    exact (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply omega
  have hrawZ : rawOf z = omega' := by
    dsimp only [rawOf, z, QKD.BB84.exitEquiv,
      QKD.BB84.boundary]
    refine (congrArg (QKD.BB84.lateSelectionExitEquiv N nK mZ mX)
      ((Boundary.graftSpaceEquiv_fst (Measurement.lateSelectionBoundary N nK mZ mX)
        (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC) _).symm.trans
          (congrArg Sigma.fst (G.apply_symm_apply _)))).trans ?_
    exact (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply omega'
  have hsuccessRaw
      (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (pi : Equiv.Perm (Fin (nK + mZ + mX)))
      (eta : SelectedControlSupport N nK mZ mX pA pB S pi)
      (q : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC) :
      rawOf (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        eta.1 (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi eta) q) = eta.1 := by
    dsimp only [rawOf]
    rw [successCompleteOutputEmbedding_exit]
    unfold successExitMap
    rw [Equiv.apply_symm_apply]
    exact (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply eta.1
  have hfailureRaw
      (j : Fin (nK + mZ + mX))
      (eta : FailureControlSupport N nK mZ mX pA pB j) :
      rawOf (shortageCompleteOutput N nK mZ mX ell ellEV leakEC eta.1
        (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j eta)) = eta.1 := by
    dsimp only [rawOf]
    rw [shortageCompleteOutput_rawControl]
  -- Each success branch has its rows in the embedding of its raw control `eta`, which contains
  -- at most one of `y`, `z` (their raw controls `omega ≠ omega'` differ).
  have hsuccess
      (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (pi : Equiv.Perm (Fin (nK + mZ + mX)))
      (eta : SelectedControlSupport N nK mZ mX pA pB S pi)
      (x x' : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi eta y x *
        star (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC
          pA pB S pi eta z x') = 0 := by
    by_cases hy : y ∈ Set.range (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
        eta.1 (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi eta))
    · have hz : z ∉ Set.range (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC
          eta.1 (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi eta)) := by
        rintro ⟨qz, hqz⟩
        obtain ⟨qy, hqy⟩ := hy
        apply hne
        calc
          omega = rawOf y := hrawY.symm
          _ = eta.1 := by rw [← hqy, hsuccessRaw]
          _ = rawOf z := by rw [← hqz, hsuccessRaw]
          _ = omega' := hrawZ
      rw [reconstructionSuccessKraus_row_eq_zero N nK mZ mX ell ellEV leakEC pA pB S pi eta hz,
        Pi.zero_apply, star_zero, mul_zero]
    · rw [reconstructionSuccessKraus_row_eq_zero N nK mZ mX ell ellEV leakEC pA pB S pi eta hy,
        Pi.zero_apply, zero_mul]
  -- Each shortage branch is a matrix unit whose single nonzero row, the abort output of its raw
  -- control `eta`, is again at most one of `y`, `z`.
  have hfailure
      (j : Fin (nK + mZ + mX))
      (r : Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC))
      (eta : FailureControlSupport N nK mZ mX pA pB j)
      (x x' : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r eta y x *
        star (reconstructionShortageKraus N nK mZ mX ell ellEV leakEC
          pA pB j r eta z x') = 0 := by
    rw [reconstructionShortageKraus_eq_single]
    by_cases hy : y = shortageCompleteOutput N nK mZ mX ell ellEV leakEC eta.1
        (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j eta)
    · have hz : z ≠ shortageCompleteOutput N nK mZ mX ell ellEV leakEC eta.1
          (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j eta) := by
        intro hz
        apply hne
        calc
          omega = rawOf y := hrawY.symm
          _ = eta.1 := by rw [hy, hfailureRaw]
          _ = rawOf z := by rw [hz, hfailureRaw]
          _ = omega' := hrawZ
      refine (congrArg (fun w : ℂ => (_ : ℂ) * star w)
        (Matrix.single_apply_of_row_ne (Ne.symm hz) _ _ _)).trans ?_
      simp only [star_zero, mul_zero]
    · exact (congrArg (fun w : ℂ => w * (_ : ℂ))
        (Matrix.single_apply_of_row_ne (Ne.symm hy) _ _ _)).trans (zero_mul _)
  let EPost := reconstructionInputEquiv N nK mZ mX ell ellEV leakEC
  let sigma : Matrix
      (ReconstructionInput N nK mZ mX ell ellEV leakEC)
      (ReconstructionInput N nK mZ mX ell ellEV leakEC) ℂ :=
    Matrix.reindex EPost.symm EPost.symm mid
  have hmid : mid = Matrix.reindex EPost EPost sigma := by
    simp [sigma, Matrix.reindex_apply]
  -- Split the channel into its success and shortage branches; each has a zero `(y, z)` entry.
  unfold reconstruction
  rw [hmid]
  refine (coordinateLinear_reindex_apply EPost
    (Fintype.equivFin (QKD.BB84.boundary N nK mZ mX ell ellEV leakEC).space)
    (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel sigma y z).trans ?_
  rw [reconstructionInstrument_channel_apply,
    Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply,
    Finset.sum_eq_zero fun a _ => matrixConjLinear_apply_eq_zero _ sigma _ _
      (hsuccess a.1 a.2.1 a.2.2), zero_add]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.sum_apply]
  refine Finset.sum_eq_zero fun eta _ => ?_
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun r _ => matrixConjLinear_apply_eq_zero _ sigma _ _
    (hfailure j r eta)

/-- The complete real map of the BB84 program factors exactly through `comparisonPre`, the retained
real experiment in every control block and the reconstruction channel. -/
theorem coordinates_real_eq_retainedFactorizedReal
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    (QKD.BB84.coordinates
      pA pB N nK mZ mX ell ellEV leakEC ec delta Q).real =
      retainedFactorizedReal
        pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q := by
  apply LinearMap.ext
  intro W
  unfold QKD.Protocol.NumeralCoordinates.real retainedFactorizedReal
  ext y z
  let eIn := (QKD.BB84.coordinates
    pA pB N nK mZ mX ell ellEV leakEC ec delta Q).inputEquiv
  let eOut := (QKD.BB84.coordinates
    pA pB N nK mZ mX ell ellEV leakEC ec delta Q).outputEquiv
  let rho := Matrix.reindex eIn.symm eIn.symm W
  have hW : W = Matrix.reindex eIn eIn rho := by
    simp [rho, Matrix.reindex_apply]
  obtain ⟨u, rfl⟩ := eOut.surjective y
  obtain ⟨v, rfl⟩ := eOut.surjective z
  rw [hW]
  rw [Numbering.map_reindex_apply]
  let G := Boundary.graftSpaceEquiv
    (Measurement.lateSelectionBoundary N nK mZ mX)
    (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC)
  obtain ⟨⟨eu, a⟩, rfl⟩ := G.symm.surjective u
  obtain ⟨⟨ev, b⟩, rfl⟩ := G.symm.surjective v
  obtain ⟨omega, rfl⟩ :=
    (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm.surjective eu
  obtain ⟨omega', rfl⟩ :=
    (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm.surjective ev
  let mid := retainedControlLift N (nK + mZ + mX)
    (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
    (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)
    (comparisonPre N nK mZ mX pA pB hN
      (Matrix.reindex eIn eIn rho))
  by_cases hcontrol : omega = omega'
  · subst omega'
    by_cases hquota : HasQuotas nK mZ mX omega
    · -- Success sector: both output points are successful complete outputs of `omega`.
      have hrange (c : (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC
          ((QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega)).space) :
          G.symm ⟨(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega, c⟩ ∈ Set.range
            (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega hquota) := by
        apply (mem_range_successCompleteOutputEmbedding_iff
          N nK mZ mX ell ellEV leakEC omega hquota _).2
        rw [G.apply_symm_apply]
        rfl
      obtain ⟨qa, hqa⟩ := hrange a
      obtain ⟨qb, hqb⟩ := hrange b
      rw [← hqa, ← hqb]
      exact retainedFactorization_success_sector pA pB N nK mZ mX
        ell ellEV leakEC hN ec delta Q rho omega hquota qa qb
    · have ha := graftSpaceEquiv_symm_shortage_fibre
          N nK mZ mX ell ellEV leakEC omega hquota a
      have hb := graftSpaceEquiv_symm_shortage_fibre
          N nK mZ mX ell ellEV leakEC omega hquota b
      -- Shortage sector: both output points are abort outputs of `omega`.
      rw [ha, hb]
      have hs := retainedFactorization_shortage_sector pA pB N nK mZ mX
        ell ellEV leakEC hN omega hquota ec delta Q rho
      dsimp only at hs
      have hinput :
          Matrix.reindex (comparisonPreInputEquiv N)
              (comparisonPreInputEquiv N)
              (reindexOp (weightedScheduleUnitInputEquiv N) rho) =
            Matrix.reindex (Fintype.equivFin (weightedStreamSystem Unit N).total)
              (Fintype.equivFin (weightedStreamSystem Unit N).total) rho := by
        ext i j
        change rho
          ((weightedScheduleUnitInputEquiv N).symm ((weightedScheduleUnitInputEquiv N)
            ((Fintype.equivFin _).symm i)))
          ((weightedScheduleUnitInputEquiv N).symm ((weightedScheduleUnitInputEquiv N)
            ((Fintype.equivFin _).symm j))) = _
        exact congrArg₂ rho
          ((weightedScheduleUnitInputEquiv N).symm_apply_apply _)
          ((weightedScheduleUnitInputEquiv N).symm_apply_apply _)
      rw [hinput] at hs
      exact hs
  · let y := G.symm
      ⟨(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega, a⟩
    let z := G.symm
      ⟨(QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega', b⟩
    let rawOf
        (q : (QKD.BB84.boundary N nK mZ mX ell ellEV leakEC).space) :=
      QKD.BB84.lateSelectionExitEquiv N nK mZ mX
        ((QKD.BB84.exitEquiv N nK mZ mX ell ellEV leakEC q.1).1)
    have hrawY : rawOf y = omega := by
      dsimp only [rawOf, y, G, QKD.BB84.exitEquiv,
        QKD.BB84.boundary]
      refine (congrArg (QKD.BB84.lateSelectionExitEquiv N nK mZ mX)
        ((Boundary.graftSpaceEquiv_fst (Measurement.lateSelectionBoundary N nK mZ mX)
          (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC) _).symm.trans
            (congrArg Sigma.fst (G.apply_symm_apply _)))).trans ?_
      exact (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply omega
    have hrawZ : rawOf z = omega' := by
      dsimp only [rawOf, z, G, QKD.BB84.exitEquiv,
        QKD.BB84.boundary]
      refine (congrArg (QKD.BB84.lateSelectionExitEquiv N nK mZ mX)
        ((Boundary.graftSpaceEquiv_fst (Measurement.lateSelectionBoundary N nK mZ mX)
          (QKD.BB84.completeContinuationBoundary N nK mZ mX ell ellEV leakEC) _).symm.trans
            (congrArg Sigma.fst (G.apply_symm_apply _)))).trans ?_
      exact (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply omega'
    have hexit : y.1 ≠ z.1 := by
      intro he
      apply hcontrol
      calc
        omega = rawOf y := hrawY.symm
        _ = rawOf z := by
          dsimp only [rawOf]
          rw [he]
        _ = omega' := hrawZ
    -- Distinct raw controls: the program's real map is block diagonal in its public exits, and no
    -- reconstruction branch connects the two exits.
    have hleft : (QKD.BB84.protocol pA pB N nK mZ mX ell ellEV leakEC
        ec delta Q).real rho y z = 0 :=
      (QKD.BB84.protocol pA pB N nK mZ mX ell ellEV leakEC
        ec delta Q).real_isExitBlockDiagonal rho y.1 z.1 y.2 z.2 hexit
    exact hleft.trans (reconstruction_rawControlDiagonal pA pB N nK mZ mX
      ell ellEV leakEC mid omega omega' hcontrol a b).symm

end QKD.BB84.Reduction
