import QCryptLean.QKD.BB84.Program.Coordinates

/-!
# All-shortage real/ideal comparison

This module isolates the exact branch where the requested retained quota exceeds the physical
round count. Every complete output then has the existing metadata-bearing abort disposition, so the
boundary ideal fixes the exit-block-diagonal real output.

Pfister et al., arXiv:1506.07502v3, Sections IV--V and Eq. (35), motivate the fixed-count shortage
branch. The cardinal obstruction and exact channel equality below are properties of the explicit
typed implementation.
-/

noncomputable section

namespace QKD.BB84.Reduction
open TypedLOCC

open QKD.BB84.Engine

/-- If the total retained quota exceeds the physical round count, every complete exit of the
actual output layout is aborting.

A quota-success branch would supply the explicit
`Sampling.selectedEmbedding : Fin (nK + mZ + mX) ↪ Fin N`, contradicting the cardinal
inequality. The conclusion retains the complete outer basis strings, shuffle, and all
branch-dependent public metadata; it only classifies the leaf disposition.
-/
theorem weightedOutputLayout_disposition_abort_of_totalQuota_gt
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (hN : N < nK + mZ + mX)
    (e : (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).Exit) :
    (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition e =
      BoundaryKeyLayout.Disposition.abort := by
  have hno (omega : Sampling.RawControl N) :
      ¬ Sampling.HasQuotas nK mZ mX omega := by
    intro hquota
    have hcard : Fintype.card (Fin (nK + mZ + mX)) ≤ Fintype.card (Fin N) :=
      Fintype.card_le_of_injective _ (Sampling.selectedEmbedding omega hquota).injective
    simp only [Fintype.card_fin] at hcard
    omega
  have hdelegate
      (outer : (Measurement.lateSelectionBoundary N nK mZ mX).Exit)
      (child : (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC outer).Exit) :
      (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
          ((QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC).symm
            ⟨outer, child⟩) =
        (QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC outer).disposition
          child := by
    let g := (Measurement.lateSelectionBoundary N nK mZ mX).graftExitEquiv
      (QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)
    have hg : g (g.symm ⟨outer, child⟩) = ⟨outer, child⟩ :=
      g.apply_symm_apply ⟨outer, child⟩
    unfold QKD.BB84.outputLayout QKD.BB84.exitEquiv
      QKD.OutputLayout.graftFixedParties
    dsimp only
    change (QKD.BB84.completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
        (g (g.symm ⟨outer, child⟩)).1).disposition
          (g (g.symm ⟨outer, child⟩)).2 = _
    rw [hg]
  rw [← (QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC).symm_apply_apply e]
  generalize (QKD.BB84.exitEquiv N nK mZ mX ℓ ℓEV leakEC) e = pair
  rcases pair with ⟨outer, child⟩
  rw [hdelegate outer child]
  have hshort : ¬ Sampling.HasQuotas nK mZ mX
      (QKD.BB84.lateSelectionExitEquiv N nK mZ mX outer) := hno _
  unfold QKD.BB84.completeContinuationOutputLayout
  split
  · contradiction
  · rename_i hboundary
    have htransport {B C : Boundary TwoParty.Party} (heq : B = C)
        (L : QKD.OutputLayout B) (x : C.Exit) :
        (QKD.OutputLayout.transport heq L).disposition x =
          L.disposition (heq.symm ▸ x) := by
      subst C
      rfl
    rw [htransport]
    rfl

/-- If the requested total retained quota exceeds the physical round count, the actual protocol's
derived real-minus-ideal map is zero because every reachable branch is key-free shortage.

The fixed-count shortage is motivated by Pfister et al., arXiv:1506.07502v3, Sections IV--V and
Eq. (35). The exact equality is implementation-specific: the real output is already block
diagonal in its complete public exit, and the boundary ideal preserves every entry inside the
metadata-bearing abort block.
-/
theorem weightedBB84_difference_eq_zero_of_totalQuota_gt
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (hN : N < nK + mZ + mX)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    (QKD.BB84.coordinates
      pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).difference = 0 := by
  let A := QKD.BB84.protocol
    pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q
  have hresource (rho : Op A.boundary.space)
      (hdiag : Boundary.IsExitBlockDiagonal A.boundary rho) :
      A.resource rho = rho := by
    ext i j
    rcases i with ⟨e, a⟩
    rcases j with ⟨f, b⟩
    change A.layout.toBoundaryKeyLayout.ideal rho ⟨e, a⟩ ⟨f, b⟩ =
      rho ⟨e, a⟩ ⟨f, b⟩
    by_cases hef : e = f
    · subst f
      have hdisposition : A.layout.disposition e =
          BoundaryKeyLayout.Disposition.abort := by
        change (QKD.BB84.outputLayout N nK mZ mX ℓ ℓEV leakEC).disposition
          e = BoundaryKeyLayout.Disposition.abort
        exact weightedOutputLayout_disposition_abort_of_totalQuota_gt
          N nK mZ mX ℓ ℓEV leakEC hN e
      exact A.layout.toBoundaryKeyLayout.ideal_coordinate_abort
        rho e hdisposition a b
    · rw [A.layout.toBoundaryKeyLayout.ideal_crossExit_zero rho hef a b,
        hdiag e f a b hef]
  have hideal : A.ideal = A.real := by
    apply LinearMap.ext
    intro rho
    change A.resource (A.real rho) = A.real rho
    exact hresource (A.real rho) (A.real_isExitBlockDiagonal rho)
  have hdifference : A.difference = 0 := by
    simp [QKD.Protocol.difference, hideal]
  have hdifference' :
      (QKD.BB84.protocol
        pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).difference = 0 := by
    simpa [A] using hdifference
  unfold QKD.Protocol.NumeralCoordinates.difference
  rw [hdifference']
  exact Numbering.map_zero _

end QKD.BB84.Reduction
