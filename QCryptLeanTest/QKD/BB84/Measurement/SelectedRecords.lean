import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the selected-record continuation and comparison law

Constructor and projection fixtures below inspect the actual local actions and grafted program.
The matrix fixtures inspect only the explicit right-hand-side comparison law and the already
proved selected-input marginal; they do not use the physical-program equality.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

open TypedLOCC
open TypedLOCC.TwoParty
open QKD.BB84.Measurement

local instance (N : ℕ) : DecidableEq (Fin N → Basis) :=
  Fintype.decidablePiFintype

local instance (N : ℕ) : DecidableEq (Fin N → Bit) :=
  Fintype.decidablePiFintype

namespace SelectedRecordsAudit

/-- The strict-subset embedding selecting the second coordinate of a two-round record. -/
def selectSecond : Fin 1 ↪ Fin 2 where
  toFun _ := 1
  inj' _ _ _ := Subsingleton.elim _ _

/-- Full selection with the selected coordinates in reverse order. -/
def reverseTwo : Fin 2 ↪ Fin 2 where
  toFun i := ⟨1 - i, by omega⟩
  inj' a b h := by
    apply Fin.ext
    simp only [Fin.mk.injEq] at h ⊢
    omega

/-- The empty selection into a one-round record. -/
def selectNoneOne : Fin 0 ↪ Fin 1 where
  toFun i := Fin.elim0 i
  inj' i := Fin.elim0 i

/-- The unique embedding between empty finite types. -/
def selectNoneNone : Fin 0 ↪ Fin 0 where
  toFun i := Fin.elim0 i
  inj' i := Fin.elim0 i

/-- A two-round basis string whose entries distinguish chronological order. -/
def twoBases (i : Fin 2) : Basis :=
  if i = 0 then .z else .x

/-- A two-round bit string whose entries distinguish chronological order. -/
def twoBits (i : Fin 2) : Bit :=
  if i = 0 then 0 else 1

/-- Concrete completed two-round stored records. -/
def twoStored : Fin 2 → StoredRecord :=
  fun i => ((), (twoBases i, twoBits i))

/-- Concrete completed local stream representing `twoStored`. -/
def completedTwo : streamRegister (finishAcc Unit 2) 0 :=
  ((finishAccEquiv Unit 2).symm ((), twoStored), fun i => Fin.elim0 i)

/-- Strict selection retains the entire basis string. -/
theorem strictSelection_retains_all_bases :
    (selectedLocalRecord selectSecond completedTwo).1 = twoBases := by
  change storedBasisString (finishedStreamEquiv Unit 2 completedTwo).2 = twoBases
  rw [show (finishedStreamEquiv Unit 2 completedTwo).2 = twoStored by
    simp [completedTwo]]
  rfl

/-- Strict selection reads only the bit at the second chronological coordinate. -/
theorem strictSelection_reads_second_bit :
    (selectedLocalRecord selectSecond completedTwo).2 0 = 1 := by
  change twoBits (selectSecond 0) = 1
  change (if (1 : Fin 2) = 0 then (0 : Bit) else 1) = 1
  exact ite_eq_right (by decide)

/-- Full reversed selection preserves all bases but reverses the retained bit order. -/
theorem reversedFullSelection_bits :
    (selectedLocalRecord reverseTwo completedTwo).2 = fun i => twoBits (reverseTwo i) := by
  simp [selectedLocalRecord, completedTwo, twoStored]

/-- The empty selection retains the one-round basis and has the unique empty selected-bit
coordinate. -/
theorem emptySelection_one_round
    (r : Fin 1 → StoredRecord) :
    selectedLocalRecord selectNoneOne
        ((finishAccEquiv Unit 1).symm ((), r), fun i => Fin.elim0 i) =
      (storedBasisString r, fun i => Fin.elim0 i) := by
  apply Prod.ext
  · simp [selectedLocalRecord]
  · funext i
    exact Fin.elim0 i

/-- At zero rounds both retained functions are the unique empty functions. -/
theorem emptySelection_zero_round
    (q : streamRegister (finishAcc Unit 0) 0) :
    selectedLocalRecord selectNoneNone q =
      ((fun i => Fin.elim0 i), fun i => Fin.elim0 i) := by
  apply Prod.ext <;> funext i <;> exact Fin.elim0 i

/-- The selected stored-record reconstruction retains each selected basis and selected bit. -/
theorem selectedStoredRecords_apply {n N : ℕ} (f : Fin n ↪ Fin N)
    (a : Fin N → Basis) (u : Fin n → Bit) (i : Fin n) :
    selectedStoredRecords f a u i = ((), (a (f i), u i)) := by
  rfl

/-- Alice's constructor is the requested local function-and-forget action. -/
theorem selectedRecordAliceAction_constructor {n N : ℕ} (f : Fin n ↪ Fin N) :
    selectedRecordAliceAction f =
      PrivateAction.ofInstrument .alice
        (Instrument.functionAndForget (selectedLocalRecord f)) := by
  rfl

/-- Bob's constructor is the requested local function-and-forget action. -/
theorem selectedRecordBobAction_constructor {n N : ℕ} (f : Fin n ↪ Fin N) :
    selectedRecordBobAction f =
      PrivateAction.ofInstrument .bob
        (Instrument.functionAndForget (selectedLocalRecord f)) := by
  rfl

/-- The continuation has exactly two private nodes in Alice-then-Bob order. -/
theorem selectedRecordContinuation_shape {n N : ℕ} (f : Fin n ↪ Fin N) :
    HEq (selectedRecordContinuation f)
      (Program.priv (selectedRecordAliceAction f)
        (Program.priv (selectedRecordBobAction f) Program.done)) := by
  unfold selectedRecordContinuation
  exact cast_heq _ _

/-- The physical consumer is definitionally the actual schedule grafted with the local
continuation. -/
theorem weightedSelectedMeasurementProgram_graft_shape
    (pA pB : PMF Basis) {n : ℕ} (N : ℕ) (f : Fin n ↪ Fin N) :
    weightedSelectedMeasurementProgram pA pB N f =
      (weightedMeasurementSchedule pA pB N).graft
        (fun _ => selectedRecordContinuation f) := by
  rfl

/-- Constant one-element zero bit string. -/
def zeroOne : Fin 1 → Bit := fun _ => 0

/-- Constant one-element one bit string. -/
def oneOne : Fin 1 → Bit := fun _ => 1

/-- The two one-element bit strings differ. -/
theorem zeroOne_ne_oneOne : zeroOne ≠ oneOne := by
  intro h
  have h0 := congrFun h 0
  simp [zeroOne, oneOne] at h0

-- The selected marginal instrument's off-diagonal survival/vanishing behaviour on split
-- coordinates (`selectSecond`) is checked once, in `SelectedMarginalAudit`
-- (`QCryptLeanTest/QKD/BB84/Measurement/SelectedMarginal.lean`).

/-- A pure Z law gives zero explicit comparison-law weight to an Alice X-basis record. -/
theorem selectedMeasurementLaw_pureZ_Xbranch_zero
    (rho : Op ((Fin 1 → Bit) × (Fin 1 → Bit))) :
    selectedMeasurementLaw (PMF.pure Basis.z) (PMF.pure Basis.z)
        (Function.Embedding.refl (Fin 1)) rho
        (((fun _ => Basis.x), zeroOne), ((fun _ => Basis.z), zeroOne))
        (((fun _ => Basis.x), zeroOne), ((fun _ => Basis.z), zeroOne)) = 0 := by
  rw [selectedMeasurementLaw_apply]
  simp [QKD.BB84.Sampling.basisStringLaw_apply]

/-- Separate pure X and pure Z laws contribute unit probability to their respective displayed
basis strings in the explicit comparison formula. -/
theorem independentBasisWeights_XZ :
    ((QKD.BB84.Sampling.basisStringLaw 1 (PMF.pure Basis.x)
      (fun _ => Basis.x)).toReal : ℂ) *
    ((QKD.BB84.Sampling.basisStringLaw 1 (PMF.pure Basis.z)
      (fun _ => Basis.z)).toReal : ℂ) = 1 := by
  simp [QKD.BB84.Sampling.basisStringLaw_apply]

/-- With an X-basis Alice record and a Z-basis Bob record, the selected fixed-basis row has the
expected nonzero coefficient on the all-zero input. -/
theorem selectedXZKraus_zeroInput :
    fixedBasisPairKraus
        (selectedStoredRecords (Function.Embedding.refl (Fin 1))
          (fun _ => Basis.x) zeroOne)
        (selectedStoredRecords (Function.Embedding.refl (Fin 1))
          (fun _ => Basis.z) zeroOne)
        () (zeroOne, zeroOne) =
      (1 : ℂ) / (Real.sqrt 2 : ℂ) := by
  simp [fixedBasisPairKraus, selectedStoredRecords, zeroOne, basisUnitary,
    Quantum.Gates.hadamard, Quantum.Operators.ket_mul_bra_apply,
    Quantum.Operators.Ket.dag, Matrix.one_apply]

/-- The same X/Z selected row has the same nonzero coefficient when Alice's selected input bit is
one and Bob's remains zero. -/
theorem selectedXZKraus_aliceOneInput :
    fixedBasisPairKraus
        (selectedStoredRecords (Function.Embedding.refl (Fin 1))
          (fun _ => Basis.x) zeroOne)
        (selectedStoredRecords (Function.Embedding.refl (Fin 1))
          (fun _ => Basis.z) zeroOne)
        () (oneOne, zeroOne) =
      (1 : ℂ) / (Real.sqrt 2 : ℂ) := by
  simp [fixedBasisPairKraus, selectedStoredRecords, zeroOne, oneOne, basisUnitary,
    Quantum.Gates.hadamard, Quantum.Operators.ket_mul_bra_apply,
    Quantum.Operators.Ket.dag, Matrix.one_apply]

/-- The X-basis row processes the retained one-way matrix unit with a nonzero contribution.  This
is an explicit comparison-law summand, not a use of the physical-program identity. -/
theorem selectedX_matrixUnitContribution_nonzero :
    let K := fixedBasisPairKraus
      (selectedStoredRecords (Function.Embedding.refl (Fin 1))
        (fun _ => Basis.x) zeroOne)
      (selectedStoredRecords (Function.Embedding.refl (Fin 1))
        (fun _ => Basis.z) zeroOne)
    K () (zeroOne, zeroOne) * 3 * star (K () (oneOne, zeroOne)) ≠ 0 := by
  dsimp only
  rw [selectedXZKraus_zeroInput, selectedXZKraus_aliceOneInput]
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have hcoef : (1 : ℂ) / (Real.sqrt 2 : ℂ) ≠ 0 :=
    div_ne_zero one_ne_zero hsqrt
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact hcoef
    · norm_num
  · exact star_ne_zero.mpr hcoef

/-- The comparison law is diagonal in complete selected records even when its input contains
selected coherence.  This checks the explicit RHS law, not the physical-program equality. -/
theorem selectedMeasurementLaw_output_offDiagonal_zero
    (pA pB : PMF Basis)
    (rho : Op ((Fin 1 → Bit) × (Fin 1 → Bit))) :
    selectedMeasurementLaw pA pB (Function.Embedding.refl (Fin 1)) rho
        (((fun _ => Basis.x), zeroOne), ((fun _ => Basis.z), zeroOne))
        (((fun _ => Basis.x), oneOne), ((fun _ => Basis.z), zeroOne)) = 0 := by
  rw [selectedMeasurementLaw_apply]
  simp [zeroOne_ne_oneOne]

end SelectedRecordsAudit
