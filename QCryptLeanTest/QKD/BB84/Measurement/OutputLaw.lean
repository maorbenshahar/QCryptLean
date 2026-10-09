import QCryptLean.QKD.BB84.Measurement.OutputLaw
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the exact weighted-schedule output law

The one-round checks below evaluate only the explicit RHS basis weights, Kraus row, and input
block.  They are not presented as independent proofs of the actual one-round schedule channel;
that equality is precisely the theorem.  The zero-round and off-diagonal-block checks are
likewise definition-driven.
-/

open Quantum.Operators (Op)

open scoped Matrix BigOperators ENNReal
open Matrix

open _root_.LOCC
open _root_.LOCC.TwoParty
open QKD.BB84.Measurement

attribute [local instance] storedRecordVectorDecidableEq

namespace OutputLawAudit

/-- The unique empty bit string. -/
def emptyBits : Fin 0 → Bit := fun i => Fin.elim0 i

/-- A stored Z-basis zero outcome used in explicit coefficient checks. -/
def zZeroStored : StoredRecord := ((), (Basis.z, 0))

/-- A stored X-basis zero outcome used in explicit coefficient checks. -/
def xZeroStored : StoredRecord := ((), (Basis.x, 0))

/-- At zero rounds the fixed-record rectangular row is the empty product. -/
theorem fixedBasisPairKraus_zero
    (rA rB : Fin 0 → StoredRecord) :
    fixedBasisPairKraus rA rB () (emptyBits, emptyBits) = 1 := by
  simp [fixedBasisPairKraus]

/-- A mixed Z/X one-round record reads Alice's Z row and Bob's X row in that order. -/
theorem fixedBasisPairKraus_one_zx_coefficient :
    fixedBasisPairKraus
        (fun _ : Fin 1 => zZeroStored)
        (fun _ : Fin 1 => xZeroStored) ()
        ((fun _ => (0 : Bit)), (fun _ => (0 : Bit))) =
      (1 : ℂ) / (Real.sqrt 2 : ℂ) := by
  simp [fixedBasisPairKraus, zZeroStored, xZeroStored, basisUnitary,
    Quantum.Gates.hadamard, Matrix.reindex_apply,
    Matrix.submatrix_apply, finTwoEquiv, Matrix.one_apply]

/-- Separate pure-Z and pure-X laws give unit mass to their respective one-round stored bases. -/
theorem independentPureBasisWeights_one :
    ((QKD.BB84.Sampling.basisStringLaw 1 (PMF.pure Basis.z)
      (storedBasisString (fun _ : Fin 1 => zZeroStored))).toReal : ℂ) *
    ((QKD.BB84.Sampling.basisStringLaw 1 (PMF.pure Basis.x)
      (storedBasisString (fun _ : Fin 1 => xZeroStored))).toReal : ℂ) = 1 := by
  simp [QKD.BB84.Sampling.basisStringLaw_apply,
    storedBasisString, zZeroStored, xZeroStored]

/-- A pure-Z law gives zero RHS basis weight to a one-round stored X basis. -/
theorem pureZ_storedX_weight_zero :
    (QKD.BB84.Sampling.basisStringLaw 1 (PMF.pure Basis.z)
      (storedBasisString (fun _ : Fin 1 => xZeroStored))).toReal = 0 := by
  simp [QKD.BB84.Sampling.basisStringLaw_apply,
    storedBasisString, xZeroStored]

/-- A zero-round input with a one-way Alice-accumulator entry; its reverse entry is zero. -/
def offDiagonalAccumulatorInput :
    Op (weightedStreamSystem (Fin 2) 0).total :=
  fun q q' =>
    if q = (weightedStreamPairEquiv (Fin 2) 0).symm
          (((0, emptyBits)), ((0, emptyBits))) ∧
        q' = (weightedStreamPairEquiv (Fin 2) 0).symm
          (((1, emptyBits)), ((0, emptyBits)))
    then 2 else 0

/-- The structural input block retains the selected nonzero off-diagonal accumulator entry. -/
theorem inputBlock_offDiagonal_forward :
    weightedScheduleInputBlock (Fin 2) 0 offDiagonalAccumulatorInput
      0 1 0 0 (emptyBits, emptyBits) (emptyBits, emptyBits) = 2 := by
  change offDiagonalAccumulatorInput
    ((weightedStreamPairEquiv (Fin 2) 0).symm ((0, emptyBits), (0, emptyBits)))
    ((weightedStreamPairEquiv (Fin 2) 0).symm ((1, emptyBits), (0, emptyBits))) = 2
  unfold offDiagonalAccumulatorInput
  exact ite_eq_left ⟨rfl, rfl⟩

/-- Reversing the selected accumulator row and column reaches the zero reverse entry. -/
theorem inputBlock_offDiagonal_reverse :
    weightedScheduleInputBlock (Fin 2) 0 offDiagonalAccumulatorInput
      1 0 0 0 (emptyBits, emptyBits) (emptyBits, emptyBits) = 0 := by
  change offDiagonalAccumulatorInput
    ((weightedStreamPairEquiv (Fin 2) 0).symm ((1, emptyBits), (0, emptyBits)))
    ((weightedStreamPairEquiv (Fin 2) 0).symm ((0, emptyBits), (0, emptyBits))) = 0
  unfold offDiagonalAccumulatorInput
  apply ite_eq_right
  intro h
  have hzero := congrArg (fun q => ((weightedStreamPairEquiv (Fin 2) 0) q).1.1) h.1
  have : (1 : Fin 2) = 0 := by simpa only [Equiv.apply_symm_apply] using hzero
  exact one_ne_zero this

/- The already-proved schedule diagonal theorem is available, but does not identify diagonal
coefficients and is not used to assert either output-law target. -/

end OutputLawAudit
