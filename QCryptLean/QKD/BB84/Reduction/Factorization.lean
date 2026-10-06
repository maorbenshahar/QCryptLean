import QCryptLean.QKD.BB84.Reduction.QuotaShortage
import QCryptLean.QKD.BB84.Reduction.Factorization.Real
import QCryptLean.QKD.BB84.Reduction.Factorization.Resource
import QCryptLean.QKD.BB84.Program

/-!
# The retained-round factorization of the BB84 real and ideal maps

For arbitrary basis laws `pA`, `pB`, batch sizes and error-correction scheme `ec`, the complete
real-minus-ideal map of the BB84 coordinates `QKD.BB84.coordinates` is controlled by the
real-minus-ideal map `retainedAnalysisDifference` of the retained-round experiment on the selected
rounds.

* `coordinates_real_eq_retainedFactorizedReal`, `coordinates_ideal_eq_retainedFactorizedIdeal`
  and `coordinates_difference_eq_retainedFactorizedDifference`: when `nK + mZ + mX ≤ N`, the
  real, ideal and real-minus-ideal maps factor exactly as
  `reconstruction ∘ retainedControlLift M ∘ comparisonPre`, where `M` is the retained real, ideal
  or difference map.  The ideal factorization follows from the real one and
  `reconstruction_resource_intertwines`.
* `coordinates_difference_diamondNorm_le_retained_of_le`: in that regime the diamond norm of the
  physical difference is at most that of the retained difference, because `comparisonPre` and
  `reconstruction` are CPTP and the control lift of a Hermitian-preserving map does not increase
  the diamond norm.
* `coordinates_difference_diamondNorm_le_retained`: the same bound for every `N`.  When
  `N < nK + mZ + mX` every run takes the shortage branch and the physical difference vanishes
  (`weightedBB84_difference_eq_zero_of_totalQuota_gt`).

The diamond norm uses a reference of the input dimension; for a Hermitian-preserving map, such as
a difference of two channels, it also bounds the trace-norm action with a reference of any
dimension (`Quantum.Channels.traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving`).  This
contraction precedes the postselection bounds that the finite-key budgets apply to the retained
difference (Christandl--König--Renner, arXiv:0809.3019, Theorem 1, the Post-Selection Theorem);
it is a statement about this library's channels, not a result of that paper.
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

/-- Exact ideal factorization, reduced to the real factorization and resource intertwining. -/
theorem coordinates_ideal_eq_retainedFactorizedIdeal
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    (QKD.BB84.coordinates
      pA pB N nK mZ mX ell ellEV leakEC ec delta Q).ideal =
      retainedFactorizedIdeal
        pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q := by
  let A := QKD.BB84.coordinates
    pA pB N nK mZ mX ell ellEV leakEC ec delta Q
  let Post := reconstruction N nK mZ mX ell ellEV leakEC pA pB
  let R := Quantum.Channels.mapTensorIdLinear
    (k := Fintype.card (ComparisonControl N (nK + mZ + mX)))
    (retainedAnalysisResource nK mZ mX ell ellEV leakEC)
  let L := retainedControlLift N (nK + mZ + mX)
    (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
    (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)
  let Pre := comparisonPre N nK mZ mX pA pB hN
  have hreal : A.real = Post.comp (L.comp Pre) := by
    exact coordinates_real_eq_retainedFactorizedReal
      pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q
  have hcomm : A.resource.comp Post = Post.comp R := by
    exact reconstruction_resource_intertwines
      pA pB N nK mZ mX ell ellEV leakEC ec delta Q
  rw [A.ideal_eq_resource_comp_real, hreal]
  calc
    A.resource.comp (Post.comp (L.comp Pre)) =
        (A.resource.comp Post).comp (L.comp Pre) := by rfl
    _ = (Post.comp R).comp (L.comp Pre) :=
      congrArg (fun F => F.comp (L.comp Pre)) hcomm
    _ = Post.comp ((R.comp L).comp Pre) := by rfl
    _ = retainedFactorizedIdeal
        pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q := by
      rw [show R.comp L =
          retainedControlLift N (nK + mZ + mX)
            (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
            ((retainedAnalysisResource nK mZ mX ell ellEV leakEC).comp
              (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)) by
        exact retainedControlLift_comp _ _ _ _ _ _]
      rfl

/-- Exact factorization of the physical real-minus-ideal map. -/
theorem coordinates_difference_eq_retainedFactorizedDifference
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    (QKD.BB84.coordinates
      pA pB N nK mZ mX ell ellEV leakEC ec delta Q).difference =
      retainedFactorizedDifference
        pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q := by
  rw [(QKD.BB84.coordinates
    pA pB N nK mZ mX ell ellEV leakEC ec delta Q).difference_eq_real_sub_ideal]
  rw [coordinates_real_eq_retainedFactorizedReal
      pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q,
    coordinates_ideal_eq_retainedFactorizedIdeal
      pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q]
  simp only [retainedFactorizedReal, retainedFactorizedIdeal,
    retainedFactorizedDifference, retainedAnalysisDifference]
  rw [retainedControlLift_sub]
  conv_rhs =>
    rw [← LinearMap.comp_assoc, LinearMap.comp_sub, LinearMap.sub_comp]
  rfl

/-- For feasible quotas, the physical real-minus-ideal map has at most the diamond norm of the
retained-round difference. -/
theorem coordinates_difference_diamondNorm_le_retained_of_le
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    Quantum.Channels.diamondNorm
        (QKD.BB84.coordinates
          pA pB N nK mZ mX ell ellEV leakEC ec delta Q).difference ≤
      Quantum.Channels.diamondNorm
        (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q) := by
  letI := comparisonPreInputDimNeZero N
  letI := comparisonPreOutputDimNeZero N (nK + mZ + mX)
  letI := reconstructionInputDimNeZero N nK mZ mX ell ellEV leakEC
  set Delta := retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q with hDelta
  have hHerm : ∀ M : Quantum.Operators.Op (4 ^ (nK + mZ + mX)),
      Delta Mᴴ = (Delta M)ᴴ :=
    retainedAnalysisDifference_preserves_conjTranspose
      nK mZ mX ell ellEV leakEC ec delta Q
  have hLiftHerm := retainedControlLift_preserves_conjTranspose
    N (nK + mZ + mX) (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
    Delta hHerm
  rw [coordinates_difference_eq_retainedFactorizedDifference
    pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q]
  exact (Quantum.Channels.diamondNorm_sandwich_cptp_le
      (reconstruction N nK mZ mX ell ellEV leakEC pA pB)
      (reconstruction_isCPTP N nK mZ mX ell ellEV leakEC pA pB)
      (retainedControlLift N (nK + mZ + mX)
        (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) Delta)
      hLiftHerm
      (comparisonPre N nK mZ mX pA pB hN)
      (comparisonPre_isCPTP N nK mZ mX pA pB hN)).trans
    (retainedControlLift_diamondNorm_le
      N (nK + mZ + mX) (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
      Delta hHerm)

/-- The coefficient-one physical-to-retained diamond-norm reduction, including the all-shortage
branch when the physical batch is too small for the quotas. -/
theorem coordinates_difference_diamondNorm_le_retained
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    Quantum.Channels.diamondNorm
        (QKD.BB84.coordinates
          pA pB N nK mZ mX ell ellEV leakEC ec delta Q).difference ≤
      Quantum.Channels.diamondNorm
        (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q) := by
  by_cases hN : nK + mZ + mX ≤ N
  · exact coordinates_difference_diamondNorm_le_retained_of_le
      pA pB N nK mZ mX ell ellEV leakEC hN ec delta Q
  · have hgt : N < nK + mZ + mX := Nat.lt_of_not_ge hN
    have hzero := weightedBB84_difference_eq_zero_of_totalQuota_gt
      pA pB N nK mZ mX ell ellEV leakEC hgt ec delta Q
    rw [hzero]
    have hz : Quantum.Channels.diamondNorm
        (0 : Quantum.Operators.Op
            (QKD.BB84.coordinates
              pA pB N nK mZ mX ell ellEV leakEC ec delta Q).inputDim →ₗ[ℂ]
          Quantum.Operators.Op
            (QKD.BB84.coordinates
              pA pB N nK mZ mX ell ellEV leakEC ec delta Q).outputDim) ≤ 0 := by
      refine Quantum.Channels.diamondNorm_le_of_forall _ _ fun W _ => ?_
      rw [Quantum.Channels.mapTensorId_zero_map, Quantum.Channels.traceNorm_zero]
    exact hz.trans (Quantum.Channels.diamondNorm_nonneg
      (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q))

end QKD.BB84.Reduction
