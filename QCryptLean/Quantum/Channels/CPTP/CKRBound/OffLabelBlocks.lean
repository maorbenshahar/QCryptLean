import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction

/-!
# `mapTensorId` off-label block lemmas

Generic support-preservation and fixed-label-block facts for `mapTensorId` /
`mapTensorIdLinear` acting through a right `eve ⊗ label` tensor factor, for an arbitrary
`Φ : Op inDim →ₗ[ℂ] Op outDim`: a fixed label block commutes with `mapTensorId`, off-label
zero support is preserved, and the linear-map version of the fixed-label block identity.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

lemma mapTensorId_assoc_right_labelBlock_eq
    {inDim outDim eveDim labelDim : ℕ}
    [NeZero inDim] [NeZero outDim] [NeZero eveDim] [NeZero labelDim]
    (Φ : Op inDim →ₗ[ℂ] Op outDim)
    (W : Op (inDim * (eveDim * labelDim)))
    (j : Fin labelDim) :
    let eIn : Fin (inDim * (eveDim * labelDim)) ≃
        Fin (inDim * eveDim) × Fin labelDim :=
      finProdFinEquiv_assoc_right inDim eveDim labelDim
    let eOut : Fin (outDim * (eveDim * labelDim)) ≃
        Fin (outDim * eveDim) × Fin labelDim :=
      finProdFinEquiv_assoc_right outDim eveDim labelDim
    (mapTensorId Φ W).submatrix
        (fun x : Fin (outDim * eveDim) => eOut.symm (x, j))
        (fun x : Fin (outDim * eveDim) => eOut.symm (x, j)) =
      mapTensorId Φ
        (W.submatrix
          (fun x : Fin (inDim * eveDim) => eIn.symm (x, j))
          (fun x : Fin (inDim * eveDim) => eIn.symm (x, j))) := by
  classical
  intro eIn eOut
  ext p q
  simp only [Matrix.submatrix_apply]
  rw [mapTensorId_apply_eq_apply_block, mapTensorId_apply_eq_apply_block]
  simp [eIn, eOut, finProdFinEquiv_assoc_right, finProdFinEquiv_symm_apply,
    finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]

lemma mapTensorId_preserves_assoc_right_offLabel_zero
    {inDim outDim eveDim labelDim : ℕ}
    [NeZero inDim] [NeZero outDim] [NeZero eveDim] [NeZero labelDim]
    (Φ : Op inDim →ₗ[ℂ] Op outDim)
    (W : Op (inDim * (eveDim * labelDim)))
    (hW :
      let eIn : Fin (inDim * (eveDim * labelDim)) ≃
          Fin (inDim * eveDim) × Fin labelDim :=
        finProdFinEquiv_assoc_right inDim eveDim labelDim
      ∀ p q : Fin (inDim * (eveDim * labelDim)),
        (eIn p).2 ≠ (eIn q).2 → W p q = 0) :
    let eOut : Fin (outDim * (eveDim * labelDim)) ≃
        Fin (outDim * eveDim) × Fin labelDim :=
      finProdFinEquiv_assoc_right outDim eveDim labelDim
    ∀ p q : Fin (outDim * (eveDim * labelDim)),
      (eOut p).2 ≠ (eOut q).2 → mapTensorId Φ W p q = 0 := by
  classical
  intro eOut p q hpq
  rw [mapTensorId_apply_eq_apply_block]
  have hkern :
      (Matrix.of fun i j =>
        W (finProdFinEquiv (i, (finProdFinEquiv.symm p).2))
          (finProdFinEquiv (j, (finProdFinEquiv.symm q).2))) =
        (0 : Op inDim) := by
    ext i j
    simp only [Matrix.of_apply]
    apply hW
    simpa [eOut, finProdFinEquiv_assoc_right, finProdFinEquiv_symm_apply] using hpq
  rw [hkern]
  simp

lemma mapTensorIdLinear_assoc_right_fixed_label_block
    {inDim outDim eveDim labelDim : ℕ}
    [NeZero inDim] [NeZero outDim] [NeZero eveDim] [NeZero labelDim]
    [NeZero (eveDim * labelDim)]
    (Φ : Op inDim →ₗ[ℂ] Op outDim)
    (W : Op (inDim * (eveDim * labelDim)))
    (j : Fin labelDim) :
    let eIn : Fin (inDim * (eveDim * labelDim)) ≃
        Fin (inDim * eveDim) × Fin labelDim :=
      finProdFinEquiv_assoc_right inDim eveDim labelDim
    let eOut : Fin (outDim * (eveDim * labelDim)) ≃
        Fin (outDim * eveDim) × Fin labelDim :=
      finProdFinEquiv_assoc_right outDim eveDim labelDim
    (mapTensorIdLinear Φ W).submatrix
        (fun x : Fin (outDim * eveDim) => eOut.symm (x, j))
        (fun x : Fin (outDim * eveDim) => eOut.symm (x, j)) =
      mapTensorIdLinear Φ
        (W.submatrix
          (fun x : Fin (inDim * eveDim) => eIn.symm (x, j))
          (fun x : Fin (inDim * eveDim) => eIn.symm (x, j))) := by
  classical
  ext p q
  simp [mapTensorIdLinear, mapTensorId_apply_eq_apply_block,
    finProdFinEquiv_assoc_right, finProdFinEquiv_symm_apply,
    finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat]

end Quantum.Channels
