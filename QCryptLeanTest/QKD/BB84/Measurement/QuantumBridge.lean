import QCryptLean.QKD.BB84.Measurement.QuantumBridge
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the fixed-basis selected-measurement bridge

The fixtures below inspect the explicit definitions independently of the two intentionally open
theorem bodies.  The existing `joinSubsetPerm_apply` theorem is used as the orientation check;
the already reviewed numeric non-involutive regression is not duplicated here.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QuantumBridgeAudit

open TypedLOCC
open QKD.BB84.Measurement

/-- The packed basis mask has Z-key, Z-test, then X-test orientation. -/
theorem packedRoleBasis_three_roles :
    packedRoleBasis (nK := 1) (mZ := 1) (mX := 1) 0 = .z ∧
      packedRoleBasis (nK := 1) (mZ := 1) (mX := 1) 1 = .z ∧
      packedRoleBasis (nK := 1) (mZ := 1) (mX := 1) 2 = .x := by
  decide

/-- Reference row and column extraction retains unequal coordinates literally. -/
theorem selectedReferenceInputBlock_apply
    {N : ℕ} {R : Type} [Fintype R] [DecidableEq R]
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

/-- Native bit-string numeral coordinates are exactly `finFunctionFinEquiv`. -/
theorem retainedBitCoordinateEquiv_apply (n : ℕ) (x : Fin n → Bit) :
    retainedBitCoordinateEquiv n x = finFunctionFinEquiv x := by
  rfl

/-- Empty retained bit strings have the unique zero numeral coordinate. -/
theorem retainedBitCoordinateEquiv_zero :
    retainedBitCoordinateEquiv 0 (Fin.elim0 : Fin 0 → Bit) = 0 := by
  apply Fin.ext
  rfl

/-- The increasing-subset embedding is the value projection of the existing ordered
enumeration. -/
theorem increasingSubsetEmbedding_apply
    {n N : ℕ} (S : Set.powersetCard (Fin N) n) (k : Fin n) :
    increasingSubsetEmbedding S k =
      (Math.FiniteEmbedding.increasingSubsetEquiv S k).1 := by
  rfl

/-- The bridge uses the source-defined inverse-permutation orientation. -/
theorem joinSubsetPerm_bridge_orientation
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
      (((TypedLOCC.Instrument.computationalMeasurement
            (Fin (2 ^ n))).kraus
          (retainedBitCoordinateEquiv n u) () *
        QKD.BB84.Model.siftPermHalf n peSel xSel pi)
        (retainedBitCoordinateEquiv n u) (retainedBitCoordinateEquiv n x)) := by
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
  have hcoord (i : Fin (2 ^ 0)) :
      i = finFunctionFinEquiv (Fin.elim0 : Fin 0 → Fin 2) := by
    apply finFunctionFinEquiv.symm.injective
    funext k
    exact Fin.elim0 k
  have hperm :
      finFunctionFinEquiv.symm
          (finFunctionFinEquiv (Fin.elim0 : Fin 0 → Fin 2)) =
        finFunctionFinEquiv.symm
            (finFunctionFinEquiv (Fin.elim0 : Fin 0 → Fin 2)) ∘ pi.symm := by
    funext k
    exact Fin.elim0 k
  simpa [nativeSiftMeasurementRow, retainedBitCoordinateEquiv,
    TypedLOCC.Instrument.computationalMeasurement,
    TypedLOCC.Instrument.nondemolitionReadout,
    TypedLOCC.Instrument.nondemolitionReadoutKraus,
    QKD.BB84.Model.siftPermHalf, Quantum.TensorProducts.tensorFamily,
    Math.RepresentationTheory.permutationRepresentation,
    Matrix.mul_apply, hcoord] using hperm

end QuantumBridgeAudit
