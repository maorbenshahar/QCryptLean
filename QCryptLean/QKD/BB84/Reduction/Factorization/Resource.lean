import QCryptLean.QKD.BB84.Reduction.Factorization.Reconstruction
import QCryptLean.LOCC.Typed.ChannelCoordinates.TensorId
import QCryptLean.LOCC.Typed.Instrument.MatrixConj
import QCryptLean.QKD.BB84.Program

/-!
# The reconstruction channel intertwines the key resources

`reconstruction` rebuilds the complete BB84 output from the retained-analysis output and the
complete comparison control.  This module proves that it intertwines the two boundary-derived
full-exit key resources (`reconstruction_resource_intertwines`): the complete-output resource after
reconstruction is reconstruction after the retained-analysis resource applied in every block of
the comparison control (`retainedControlResource`).

The reconstruction channel is a sum of conjugations by explicit Kraus matrices, and the identity
is proved one branch at a time.

* A **success branch** for a retained subset `S`, an announced permutation `pi` and a supported
  raw control `omega` carries the retained tail over `pi` in the control block of `S` onto the
  successful fibre of `omega`, scaled by the square root of the selected control weight.  The
  successful fibre and the fibre of `pi` are the images of morphisms of key layouts out of the
  retained-tail layout (`successCompleteOutputHom`, `retainedAnalysisFibreHom`), along which the
  ideal key resource is natural (`TypedLOCC.BoundaryKeyLayout.Hom.ideal_eq_iff`).  Both resources
  therefore act on the branch as the retained-tail resource.
* A **shortage branch** for a quota index `j` and a supported raw control `omega` traces out the
  retained output in the control block of `j` and prepares the metadata-bearing abort output of
  `omega`, scaled by the failure weight.  The complete-output resource fixes that abort point
  (`TypedLOCC.BoundaryKeyLayout.ideal_single_of_abort`), and the blockwise retained resource keeps
  the trace of the block (`TypedLOCC.tensorIdLinear_trace_block`), because the retained ideal
  preserves the trace in any coordinates (`TypedLOCC.BoundaryKeyLayout.trace_ideal`,
  `TypedLOCC.coordinateLinear_trace`).

The physical program is a finite-round LOCC protocol; such instruments are described by
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II.  The reconstruction is an
analytical channel of the proof, not a step of that program.  Pfister et al., arXiv:1506.07502v3,
Section IV, Protocol 3, Step 5', likewise aborts when fixed-round quotas cannot be met, and their
Appendix C analyzes the sifting outputs and the abort probability; this is context for the
shortage branch.  The intertwining identity concerns this library's reconstruction channel.
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

/-- The retained-analysis resource applied in every block of the complete comparison control. -/
abbrev retainedControlResource (N nK mZ mX ell ellEV leakEC : ℕ) :
    Op (ReconstructionInput N nK mZ mX ell ellEV leakEC) →ₗ[ℂ]
      Op (ReconstructionInput N nK mZ mX ell ellEV leakEC) :=
  tensorIdLinear (ComparisonControl N (nK + mZ + mX))
    (retainedAnalysisResource nK mZ mX ell ellEV leakEC)

/-- **On one success slice the blockwise retained resource is the retained-tail resource.**

Read at the success input coordinates of a retained subset `S` and an announced permutation `pi`,
the retained resource in every control block is the retained-tail ideal of the same slice. -/
theorem retainedControlResource_successInput
    (N nK mZ mX ell ellEV leakEC : ℕ)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (rho : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    (retainedControlResource N nK mZ mX ell ellEV leakEC rho).submatrix
        (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi)
        (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi) =
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout.ideal
        (rho.submatrix (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi)
          (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi)) := by
  ext u v
  have h := (retainedAnalysisFibreHom nK mZ mX ell ellEV leakEC pi).ideal_apply
    ((rho.submatrix (fun a => (a, Sum.inl S)) (fun a => (a, Sum.inl S))).submatrix
      (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)
      (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)) u v
  rw [coe_retainedAnalysisFibreHom] at h
  rw [Matrix.submatrix_apply, tensorIdLinear_apply]
  exact (retainedAnalysisResource_entry nK mZ mX ell ellEV leakEC _ _ _).trans h

/-- **The complete-output resource commutes with one success branch of the reconstruction.** -/
theorem reconstructionSuccessKraus_resource_intertwines
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi)
    (rho : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    (QKD.BB84.outputLayout N nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
        (matrixConjLinear
          (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega) rho) =
      matrixConjLinear
        (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega)
        (retainedControlResource N nK mZ mX ell ellEV leakEC rho) := by
  have hsupport : ∀ (M : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) y z,
      (y ∉ Set.range (successCompleteOutputHom N nK mZ mX ell ellEV leakEC omega.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega)) ∨
        z ∉ Set.range (successCompleteOutputHom N nK mZ mX ell ellEV leakEC omega.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega))) →
      matrixConjLinear
          (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega) M y z =
        0 := by
    rw [coe_successCompleteOutputHom]
    rintro M y z (hy | hz)
    · exact matrixConjLinear_apply_eq_zero_of_row_left _ M
        (reconstructionSuccessKraus_row_eq_zero N nK mZ mX ell ellEV leakEC pA pB S pi omega
          hy) z
    · exact matrixConjLinear_apply_eq_zero_of_row_right _ M y
        (reconstructionSuccessKraus_row_eq_zero N nK mZ mX ell ellEV leakEC pA pB S pi omega
          hz)
  have hpull : ∀ M : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC),
      (matrixConjLinear
          (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega) M).submatrix
          (successCompleteOutputHom N nK mZ mX ell ellEV leakEC omega.1
            (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega))
          (successCompleteOutputHom N nK mZ mX ell ellEV leakEC omega.1
            (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega)) =
        (star (Instrument.weightedChoiceScale (totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi)) omega.1) *
            Instrument.weightedChoiceScale (totalSelectedControlKernel N nK mZ mX pA pB
              (Math.FiniteEmbedding.joinSubsetPerm S pi)) omega.1) •
          M.submatrix (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi)
            (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi) := by
    intro M
    rw [coe_successCompleteOutputHom]
    exact matrixConjLinear_submatrix_of_row_eq_single _ M _ _ _
      (reconstructionSuccessKraus_row N nK mZ mX ell ellEV leakEC pA pB S pi omega)
  rw [BoundaryKeyLayout.Hom.ideal_eq_iff _ (hsupport rho) (hsupport _), hpull, hpull, map_smul,
    retainedControlResource_successInput]

/-- **The complete-output resource commutes with one shortage branch of the reconstruction.** -/
theorem reconstructionShortageKraus_resource_intertwines
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX)) (omega : FailureControlSupport N nK mZ mX pA pB j)
    (rho : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    (QKD.BB84.outputLayout N nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
        (∑ r, matrixConjLinear
          (reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega) rho) =
      ∑ r, matrixConjLinear
        (reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega)
        (retainedControlResource N nK mZ mX ell ellEV leakEC rho) := by
  have hsum : ∀ M : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC),
      ∑ r, matrixConjLinear
          (reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega) M =
        Matrix.single
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega.1
            (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega))
          (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega.1
            (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega))
          (Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j) omega.1 *
            (∑ r, M (r, Sum.inr j) (r, Sum.inr j)) *
            star (Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j)
              omega.1)) := by
    intro M
    simp_rw [reconstructionShortageKraus_eq_single]
    refine (Finset.sum_congr rfl (fun r _ => matrixConjLinear_single _ _ _ M)).trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    generalize shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega.1
      (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega) = y
    exact (map_sum (Matrix.singleAddMonoidHom (α := ℂ) y y) _ _).symm
  rw [hsum, hsum, BoundaryKeyLayout.ideal_single_of_abort _ rfl
      (shortageCompleteOutput_disposition N nK mZ mX ell ellEV leakEC omega.1
        (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega))]
  have htrace := tensorIdLinear_trace_block
      (retainedAnalysisResource nK mZ mX ell ellEV leakEC)
      (coordinateLinear_trace _ _ _
        (retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.trace_ideal)
      rho (Sum.inr j : ComparisonControl N (nK + mZ + mX))
  exact congrArg (fun z : ℂ => Matrix.single _ _
    (Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j) omega.1 *
      z * star (Instrument.weightedChoiceScale
        (totalFailureControlKernel N nK mZ mX pA pB j) omega.1))) htrace.symm

/-- The complete-output resource commutes with the whole reconstruction channel. -/
theorem reconstructionInstrument_resource_intertwines
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (rho : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    (QKD.BB84.outputLayout N nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
        ((reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel rho) =
      (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel
        (retainedControlResource N nK mZ mX ell ellEV leakEC rho) := by
  rw [reconstructionInstrument_channel_apply, reconstructionInstrument_channel_apply,
    map_add, map_sum, map_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun a _ => ?_)
    (Finset.sum_congr rfl fun j _ => ?_)
  · exact reconstructionSuccessKraus_resource_intertwines N nK mZ mX ell ellEV leakEC pA pB
      a.1 a.2.1 a.2.2 rho
  · rw [map_sum]
    exact Finset.sum_congr rfl fun omega _ =>
      reconstructionShortageKraus_resource_intertwines N nK mZ mX ell ellEV leakEC pA pB
        j omega rho

/-- Reconstruction intertwines the complete-exit key resource of the BB84 coordinates with the
retained-analysis resource in every control block, on the whole retained-output-times-control
space. -/
theorem reconstruction_resource_intertwines
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    let A := QKD.BB84.coordinates
      pA pB N nK mZ mX ell ellEV leakEC ec delta Q
    A.resource.comp
        (reconstruction N nK mZ mX ell ellEV leakEC pA pB) =
      (reconstruction N nK mZ mX ell ellEV leakEC pA pB).comp
        (Quantum.Channels.mapTensorIdLinear
          (k := Fintype.card (ComparisonControl N (nK + mZ + mX)))
          (retainedAnalysisResource nK mZ mX ell ellEV leakEC)) := by
  intro A
  have hA : A.resource =
      coordinateLinear
        (Fintype.equivFin (QKD.BB84.boundary N nK mZ mX ell ellEV leakEC).space)
        (Fintype.equivFin (QKD.BB84.boundary N nK mZ mX ell ellEV leakEC).space)
        (QKD.BB84.outputLayout N nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal :=
    rfl
  have hchan : ((QKD.BB84.outputLayout
        N nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal).comp
      ((reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel) =
      ((reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel).comp
        (retainedControlResource N nK mZ mX ell ellEV leakEC) :=
    LinearMap.ext fun rho =>
      reconstructionInstrument_resource_intertwines N nK mZ mX ell ellEV leakEC pA pB rho
  have hT : Quantum.Channels.mapTensorIdLinear
        (k := Fintype.card (ComparisonControl N (nK + mZ + mX)))
        (retainedAnalysisResource nK mZ mX ell ellEV leakEC) =
      coordinateLinear (reconstructionInputEquiv N nK mZ mX ell ellEV leakEC)
        (reconstructionInputEquiv N nK mZ mX ell ellEV leakEC)
        (retainedControlResource N nK mZ mX ell ellEV leakEC) :=
    mapTensorIdLinear_eq_coordinateLinear (Fintype.equivFin _) _
  rw [hA, hT, reconstruction]
  refine (coordinateLinear_comp _ _ _ _ _).symm.trans ?_
  refine Eq.trans ?_ (coordinateLinear_comp _ _ _ _ _)
  exact congrArg (coordinateLinear _ _) hchan

end QKD.BB84.Reduction
