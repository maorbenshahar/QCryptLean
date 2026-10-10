import QCryptLean.QKD.BB84.Measurement.SelectedBornRule
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the fixed-basis selected-measurement identity

The fixtures inspect the definitions independently of the selected-measurement identities.
The existing `joinSubsetPerm_apply` theorem is used as the orientation check;
the already reviewed numeric non-involutive regression is not duplicated here.
-/

open Quantum.Operators (Op)

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace SelectedMeasurementAudit

open _root_.LOCC
open QKD.BB84.Measurement

/-- The packed basis mask has Z-key, Z-test, then X-test orientation. -/
theorem packedRoleBasis_three_roles :
    packedRoleBasis (nK := 1) (mZ := 1) (mX := 1) 0 = .z ∧
      packedRoleBasis (nK := 1) (mZ := 1) (mX := 1) 1 = .z ∧
      packedRoleBasis (nK := 1) (mZ := 1) (mX := 1) 2 = .x := by
  decide

/-- Reference row and column extraction retains unequal coordinates literally. -/
theorem selectedReferenceInputBlock_apply
    {N : ℕ} {R : Type}
    (W : Op (((Fin N → Bit) × (Fin N → Bit)) × R))
    (x y : (Fin N → Bit) × (Fin N → Bit)) (s t : R) :
    selectedReferenceInputBlock W s t x y = W (x, s) (y, t) := by
  rfl

/-- A concrete non-Hermitian reference off-diagonal survives block extraction. -/
theorem reference_offDiagonal_survives :
    let x : (Fin 0 → Bit) × (Fin 0 → Bit) := (Fin.elim0, Fin.elim0)
    let W : Op (((Fin 0 → Bit) × (Fin 0 → Bit)) × Fin 2) :=
      fun q q' => if q.2 = 0 ∧ q'.2 = 1 then (3 + Complex.I : ℂ) else 0
    selectedReferenceInputBlock W 0 1 x x = (3 + Complex.I : ℂ) := by
  change (if (0 : Fin 2) = 0 ∧ (1 : Fin 2) = 1 then (3 + Complex.I : ℂ) else 0) = _
  exact ite_eq_left ⟨rfl, rfl⟩

/-- The increasing-subset embedding is the value projection of the existing ordered
enumeration. -/
theorem increasingSubsetEmbedding_apply
    {n N : ℕ} (S : Set.powersetCard (Fin N) n) (k : Fin n) :
    increasingSubsetEmbedding S k =
      (Math.FiniteEmbedding.increasingSubsetEquiv S k).1 := by
  rfl

/-- The identity uses the source-defined inverse-permutation orientation. -/
theorem joinSubsetPerm_symm_orientation
    {n N : ℕ} (S : Set.powersetCard (Fin N) n)
    (pi : Equiv.Perm (Fin n)) (k : Fin n) :
    Math.FiniteEmbedding.joinSubsetPerm S pi k =
      increasingSubsetEmbedding S (pi.symm k) := by
  rfl

/-- The native row is literally the actual computational-measurement Kraus projector after
`siftPermHalf`. -/
theorem nativeSiftMeasurementRow_constructor
    (n : ℕ) (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (u x : Fin n → Bit) :
    nativeSiftMeasurementRow n peSel xSel pi u () x =
      (((_root_.LOCC.Instrument.computationalMeasurement
            (Bits n)).kraus
          u () *
        QKD.BB84.Model.siftPermHalf n peSel xSel pi)
        u x) := by
  rfl

/-- The two-party native Kraus row is the product of the literal local native rows. -/
theorem nativeSiftPairKraus_constructor
    (n : ℕ) (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (uA uB : Fin n → Bit) (x : (Fin n → Bit) × (Fin n → Bit)) :
    nativeSiftPairKraus n peSel xSel pi uA uB () x =
      nativeSiftMeasurementRow n peSel xSel pi uA () x.1 *
        nativeSiftMeasurementRow n peSel xSel pi uB () x.2 := by
  rfl

/-- The zero-size native row is the unique scalar row with coefficient one. -/
theorem nativeSiftMeasurementRow_zero
    (peSel xSel : Fin 0 → Bool) (pi : Equiv.Perm (Fin 0)) :
    nativeSiftMeasurementRow 0 peSel xSel pi Fin.elim0 () Fin.elim0 = 1 := by
  simp only [nativeSiftMeasurementRow, Instrument.computationalMeasurement,
    Instrument.nondemolitionReadout, Instrument.nondemolitionReadoutKraus, id_eq,
    QKD.BB84.Model.siftPermHalf, piTensorProduct, Finset.univ_eq_empty,
    Bool.and_eq_true, reindex_apply, Equiv.symm_symm, Finset.prod_empty,
    Quantum.Symmetry.permutationRepresentation, tensorPermutation, Matrix.mul_apply,
    Finset.univ_unique, diagonal_apply, ↓reduceIte, of_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_singleton, Finset.sum_ite_irrel, Finset.sum_ite_eq,
    Finset.sum_const_zero]
  split_ifs <;> first
  | rfl
  | (exfalso; apply_assumption; exact Subsingleton.elim _ _)

end SelectedMeasurementAudit
