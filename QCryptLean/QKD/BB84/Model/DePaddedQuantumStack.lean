import QCryptLean.Quantum.Channels.CPTP.BlockPinchingChannel
import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.SiftOperation
import QCryptLean.QKD.BB84.Model.BB84Locality
import QCryptLean.LOCC.ClassicalInstruments
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.InfoTheory.Postselection.Lift

/-!
# The BB84 quantum stack at the bare Eve slot, de-padded

`QKD.BB84.Model.bb84SymRealChannel` is built as a `(1/n!)` mixture over `π` of a
multi-layer composite carrying a one-dimensional Eve slot throughout.  This module strips that
slot and computes the joint measurement and the sift-after-permutation composite in explicit
coordinates.

## Main definitions

- `QKD.BB84.Model.bb84MeasureBare`: the joint computational-basis dephasing of the `4 ^ n` signal
  register, with the one-dimensional Eve slot stripped.

## Main results

- `QKD.BB84.Model.measurementChannel_one_castDim`: the `measurementChannel` at
  `eveDim = 1` is exactly `bb84MeasureBare`, modulo the `⊗ 1₁` cast.
- `QKD.BB84.Model.unitRegisterEmbed_comm_permuteSignal`: the unit-register padding is
  permutation-covariant, so it commutes with the signal permutation and contributes only a cast.
- `QKD.BB84.Model.siftEmbedPerm_castDim`: the quantum stack's input to the classical layer,
  de-padded — layers 7, 8 and 9 compose to "conjugate by the sift-after-permutation".
- `QKD.BB84.Model.siftPermHalf_pair_conj_reindex`: the two parties' local halves fuse into the
  sift-after-permutation across the laboratory cut.
-/
open Equiv

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Quantum.Channels Matrix
open Math.RepresentationTheory InfoTheory.Postselection QKD.BB84.Engine
open LOCC
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Model

/-! ## The joint measurement -/

/-- **The joint computational-basis dephasing of the `4 ^ n` signal register.** This is the content
of `measurementChannel` with the one-dimensional Eve slot stripped; the two are tied by
`measurementChannel_one_castDim`. -/
def bb84MeasureBare (n : ℕ) : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n) :=
  ∑ c : Fin (4 ^ n), LOCC.matrixConjLinear (Matrix.single c c (1 : ℂ))

theorem bb84MeasureBare_apply (n : ℕ) (A : Op (4 ^ n)) :
    bb84MeasureBare n A =
      ∑ c : Fin (4 ^ n), Matrix.single c c (1 : ℂ) * A * Matrix.single c c (1 : ℂ) := by
  simp only [bb84MeasureBare, LinearMap.coe_sum, Finset.sum_apply,
    LOCC.matrixConjLinear_apply, Matrix.conjTranspose_single, star_one]

/-- **The measurement channel at the unit Eve slot is the bare dephasing.** The `⊗ 1₁`
padding is a dimension cast and nothing else. -/
theorem measurementChannel_one_castDim (n : ℕ) (A : Op (4 ^ n)) :
    measurementChannel n 1 (Op.castDim (Nat.mul_one (4 ^ n)).symm A) =
      Op.castDim (Nat.mul_one (4 ^ n)).symm (bb84MeasureBare n A) := by
  have hK : ∀ c : Fin (4 ^ n),
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
          (Matrix.kroneckerMap (· * ·) (Matrix.single c c (1 : ℂ) : Op (4 ^ n)) (1 : Op 1)) :
            Op (4 ^ n * 1)) =
        Op.castDim (Nat.mul_one (4 ^ n)).symm (Matrix.single c c (1 : ℂ)) := by
    intro c
    rw [op_castDim_mul_one_eq_tensor_one]
    rfl
  change (∑ c : Fin (4 ^ n),
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (Matrix.single c c (1 : ℂ) : Op (4 ^ n)) (1 : Op 1))) *
      Op.castDim (Nat.mul_one (4 ^ n)).symm A *
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (Matrix.single c c (1 : ℂ) : Op (4 ^ n)) (1 : Op 1)))ᴴ) = _
  rw [bb84MeasureBare_apply, Op.castDim_sum_univ]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hK c, Op.castDim_conjTranspose, Matrix.conjTranspose_single, star_one, Op.castDim_mul,
    Op.castDim_mul]

/-! ## The quantum stack, de-padded -/

/-- **The whole quantum stack, de-padded.** Layers 6, 7, 8 and 9 of `bb84SymRealChannel` at the
bare slot compose to "conjugate by the sift-after-permutation, then dephase" — with the `⊗ 1₁`
padding stripped by a dimension cast. Every object in the chain appears by name. -/
theorem siftedConjChannel_one_castDim (n : ℕ) (peSel xSel : Fin n → Bool) (A : Op (4 ^ n)) :
    bb84SiftedConjChannel n 1 peSel xSel (Op.castDim (Nat.mul_one (4 ^ n)).symm A) =
      Op.castDim (Nat.mul_one (4 ^ n)).symm
        (bb84SiftedRotation n peSel xSel * A * (bb84SiftedRotation n peSel xSel)ᴴ) := by
  change (∑ _ : Unit, Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op 1) *
      Op.castDim (Nat.mul_one (4 ^ n)).symm A *
      (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op 1))ᴴ) = _
  rw [Finset.univ_unique, Finset.sum_singleton, ← op_castDim_mul_one_eq_tensor_one,
    Op.castDim_conjTranspose, Op.castDim_mul, Op.castDim_mul]

/-- **The unit-register padding is permutation-covariant** — it is `ρ ↦ ρ ⊗ 1₁`, so it
commutes with the signal permutation and contributes only a cast.

Thus the permute-then-attack counterexample does not apply to the bare channel: the bare
slot's `pre` is exactly this map. It *does* reach the slot-carrying variant, whose `pre` is an
arbitrary CPTP map. -/
theorem unitRegisterEmbed_comm_permuteSignal (n : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (π : Equiv.Perm (Fin n)) (ρ : Op (4 ^ n)) :
    bb84UnitRegisterEmbed n (permuteSignalLinear n π ρ) =
      Op.castDim (Nat.mul_one (4 ^ n)).symm (permuteSignalLinear n π ρ) := by
  rw [bb84UnitRegisterEmbed_apply, op_castDim_mul_one_eq_tensor_one]

/-- **The quantum stack's input to the classical layer, de-padded.** Layers 7, 8 and 9 compose to
"conjugate by the sift-after-permutation", with the `⊗ 1₁` padding a dimension cast. -/
theorem siftEmbedPerm_castDim (n : ℕ) [NeZero n] [NeZero (4 ^ n)] (peSel xSel : Fin n → Bool)
    (π : Equiv.Perm (Fin n)) (ρ : Op (4 ^ n)) :
    bb84SiftedConjChannel n 1 peSel xSel
        (bb84UnitRegisterEmbed n (permuteSignalLinear n π ρ)) =
      Op.castDim (Nat.mul_one (4 ^ n)).symm
        (bb84SiftedRotation n peSel xSel * permuteSignalLinear n π ρ *
          (bb84SiftedRotation n peSel xSel)ᴴ) := by
  rw [unitRegisterEmbed_comm_permuteSignal, siftedConjChannel_one_castDim]

/-- **The two parties' halves fuse into the sift-after-permutation across the laboratory cut.**
This is the composite of the two product forms. -/
theorem siftPermHalf_pair_conj_reindex (n : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) (ρ : Op (4 ^ n)) :
    Op.tensor (siftPermHalf n peSel xSel π) (siftPermHalf n peSel xSel π) *
        Matrix.reindex (roundGroupEquiv 2 2 n) (roundGroupEquiv 2 2 n) ρ *
        (Op.tensor (siftPermHalf n peSel xSel π) (siftPermHalf n peSel xSel π))ᴴ =
      Matrix.reindex (roundGroupEquiv 2 2 n) (roundGroupEquiv 2 2 n)
        (bb84SiftedRotation n peSel xSel * permuteSignalLinear n π ρ *
          (bb84SiftedRotation n peSel xSel)ᴴ) := by
  simp only [siftPermHalf]
  rw [bb84SiftedRotation_conj_reindex_roundGroupEquiv,
    permuteSignalLinear_reindex_roundGroupEquiv, conj_conj_eq_conj_mul, Op.tensor_mul]

end QKD.BB84.Model

end
