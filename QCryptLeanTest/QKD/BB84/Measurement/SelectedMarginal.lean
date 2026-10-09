import QCryptLean.QKD.BB84.Measurement.SelectedMarginal
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the selected-input marginal instrument

This test checks every core declaration and exercises the explicit coordinate order and the
certified discard on concrete finite inputs.  None of its fixtures invokes the general
channel formula.
-/

open Quantum.Operators (Op)

open scoped Matrix BigOperators
open Matrix

open _root_.LOCC
open QKD.BB84.Measurement

namespace SelectedMarginalAudit

/-- The strict-subset embedding selecting the second coordinate of `Fin 2`. -/
def selectSecond : Fin 1 ↪ Fin 2 where
  toFun _ := 1
  inj' _ _ _ := Subsingleton.elim _ _

/-- The increasing complement of selectSecond is its first coordinate. -/
theorem selectSecond_complement_zero :
    (Math.FiniteEmbedding.embeddingComplementEquiv selectSecond 0 : Fin 2) = 0 := by
  have hnot :
      ¬ ((Math.FiniteEmbedding.embeddingComplementEquiv selectSecond 0 : Fin 2) ∈
        Set.range selectSecond) :=
    (Math.FiniteEmbedding.embeddingComplementEquiv selectSecond 0).property
  have hne :
      (Math.FiniteEmbedding.embeddingComplementEquiv selectSecond 0 : Fin 2) ≠ 1 := by
    intro h
    apply hnot
    exact ⟨0, by exact h.symm⟩
  apply Fin.ext
  omega

/-- The selected half of the strict-subset split reads the second original coordinate. -/
theorem selectSecond_selected_coordinate (x : Fin 2 → Bit) :
    (selectedBitSplit selectSecond x).1 0 = x 1 := by
  rfl

/-- The complementary half of the strict-subset split reads the remaining first coordinate. -/
theorem selectSecond_complement_coordinate (x : Fin 2 → Bit) :
    (selectedBitSplit selectSecond x).2 0 = x 0 := by
  exact congrArg x selectSecond_complement_zero

/-- A full-size nonidentity embedding that reverses the two selected coordinates. -/
def reverseTwo : Fin 2 ↪ Fin 2 where
  toFun i := ⟨1 - i, by omega⟩
  inj' a b h := by
    apply Fin.ext
    simp only [Fin.mk.injEq] at h ⊢
    omega

/-- Full selection preserves the embedding's nonidentity order at its first coordinate. -/
theorem reverseTwo_first (x : Fin 2 → Bit) :
    (selectedBitSplit reverseTwo x).1 0 = x 1 := by
  rfl

/-- Full selection preserves the embedding's nonidentity order at its second coordinate. -/
theorem reverseTwo_second (x : Fin 2 → Bit) :
    (selectedBitSplit reverseTwo x).1 1 = x 0 := by
  rfl

/-- The unique zero selection into one input coordinate. -/
def selectNoneOne : Fin 0 ↪ Fin 1 where
  toFun i := Fin.elim0 i
  inj' i := Fin.elim0 i

/-- The constant one-element bit strings used in strict-subset channel probes. -/
def zeroOne : Fin 1 → Bit := fun _ => 0

/-- The constant one-element one bit string used for a retained off-diagonal coordinate. -/
def oneOne : Fin 1 → Bit := fun _ => 1

/-- The two constant one-element bit strings are distinct. -/
theorem zeroOne_ne_oneOne : zeroOne ≠ oneOne := by
  intro h
  have h0 := congrFun h 0
  simp [zeroOne, oneOne] at h0

/-- A split-coordinate matrix unit whose selected coordinates are off diagonal and whose
complementary coordinates agree. -/
def retainedOffDiagonalSplit :
    Op (((Fin 1 → Bit) × (Fin 1 → Bit)) ×
      ((Fin 1 → Bit) × (Fin 1 → Bit))) :=
  fun p q =>
    if p = ((zeroOne, zeroOne), (zeroOne, zeroOne)) ∧
        q = ((oneOne, zeroOne), (zeroOne, zeroOne))
    then 3 else 0

/-- Transport the retained off-diagonal matrix unit back to full two-round bit strings. -/
noncomputable def retainedOffDiagonalInput :
    Op ((Fin 2 → Bit) × (Fin 2 → Bit)) :=
  (Matrix.reindexLinearEquiv ℂ ℂ (selectedPairBitSplit selectSecond).symm (selectedPairBitSplit
    selectSecond).symm).toLinearMap retainedOffDiagonalSplit

/-- The certified selected marginal preserves the nonzero selected off-diagonal entry when the
discarded Alice/Bob coordinates agree. -/
theorem retainedOffDiagonal_survives :
    (selectedInputMarginalInstrument selectSecond).channel retainedOffDiagonalInput
      (zeroOne, zeroOne) (oneOne, zeroOne) = 3 := by
  simp only [selectedInputMarginalInstrument, Instrument.channel_eq_sum,
    Fintype.sum_unique]
  rw [Instrument.onFactor_operation_apply,
    Instrument.discardToUnit_operation_apply]
  simp [retainedOffDiagonalInput, retainedOffDiagonalSplit, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply,
    unitProdEquiv]

/-- A split-coordinate matrix unit supported only between two different discarded coordinates. -/
def discardedOffDiagonalSplit :
    Op (((Fin 1 → Bit) × (Fin 1 → Bit)) ×
      ((Fin 1 → Bit) × (Fin 1 → Bit))) :=
  fun p q =>
    if p = ((zeroOne, zeroOne), (zeroOne, zeroOne)) ∧
        q = ((zeroOne, zeroOne), (oneOne, zeroOne))
    then 5 else 0

/-- Transport the discarded off-diagonal matrix unit back to full two-round bit strings. -/
noncomputable def discardedOffDiagonalInput :
    Op ((Fin 2 → Bit) × (Fin 2 → Bit)) :=
  (Matrix.reindexLinearEquiv ℂ ℂ (selectedPairBitSplit selectSecond).symm (selectedPairBitSplit
    selectSecond).symm).toLinearMap discardedOffDiagonalSplit

/-- The certified marginal annihilates a matrix unit that is off diagonal only in the discarded
coordinate. -/
theorem discardedOffDiagonal_vanishes :
    (selectedInputMarginalInstrument selectSecond).channel discardedOffDiagonalInput
      (zeroOne, zeroOne) (zeroOne, zeroOne) = 0 := by
  simp only [selectedInputMarginalInstrument, Instrument.channel_eq_sum,
    Fintype.sum_unique]
  rw [Instrument.onFactor_operation_apply,
    Instrument.discardToUnit_operation_apply]
  change (∑ u : (Fin 1 → Bit) × (Fin 1 → Bit), discardedOffDiagonalSplit
    (selectedPairBitSplit selectSecond ((selectedPairBitSplit selectSecond).symm
      ((zeroOne, zeroOne), u)))
    (selectedPairBitSplit selectSecond ((selectedPairBitSplit selectSecond).symm
      ((zeroOne, zeroOne), u)))) = 0
  simp only [Equiv.apply_symm_apply, discardedOffDiagonalSplit]
  apply Finset.sum_eq_zero
  intro u _
  rw [ite_eq_right]
  rintro ⟨hu0, hu1⟩
  apply zeroOne_ne_oneOne
  exact congrArg (fun p => p.2.1) (hu0.symm.trans hu1)

/-- A split-coordinate matrix unit with the unique empty selected pair and one diagonal
complementary pair. -/
def emptySelectionDiagonalSplit :
    Op (((Fin 0 → Bit) × (Fin 0 → Bit)) ×
      ((Fin 1 → Bit) × (Fin 1 → Bit))) :=
  fun p q =>
    if p = (((fun i => Fin.elim0 i), (fun i => Fin.elim0 i)),
          (zeroOne, zeroOne)) ∧
        q = (((fun i => Fin.elim0 i), (fun i => Fin.elim0 i)),
          (zeroOne, zeroOne))
    then 7 else 0

/-- Transport the empty-selection diagonal matrix unit to the full one-round input. -/
noncomputable def emptySelectionDiagonalInput :
    Op ((Fin 1 → Bit) × (Fin 1 → Bit)) :=
  (Matrix.reindexLinearEquiv ℂ ℂ (selectedPairBitSplit selectNoneOne).symm (selectedPairBitSplit
    selectNoneOne).symm).toLinearMap emptySelectionDiagonalSplit

/-- The empty-selection channel returns the trace on the explicit one-diagonal-entry input. -/
theorem emptySelection_trace :
    (selectedInputMarginalInstrument selectNoneOne).channel emptySelectionDiagonalInput
      ((fun i => Fin.elim0 i), (fun i => Fin.elim0 i))
      ((fun i => Fin.elim0 i), (fun i => Fin.elim0 i)) = 7 := by
  simp only [selectedInputMarginalInstrument, Instrument.channel_eq_sum,
    Fintype.sum_unique]
  rw [Instrument.onFactor_operation_apply,
    Instrument.discardToUnit_operation_apply]
  simp [emptySelectionDiagonalInput, emptySelectionDiagonalSplit,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply, unitProdEquiv]

end SelectedMarginalAudit
