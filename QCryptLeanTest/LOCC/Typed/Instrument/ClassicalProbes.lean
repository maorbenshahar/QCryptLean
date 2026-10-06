import QCryptLean.LOCC.Typed.Instrument.Classical
import Mathlib.Util.AssertNoSorry

/-!
# Definition-level probes for finite classical instruments

These probes evaluate the two explicit Kraus families without invoking any theorem about them.
They cover empty finite types, a many-to-one function, and a genuinely
non-Hermitian matrix unit.  In particular, the last probes distinguish nondemolition readout from
measure-and-prepare processing on an off-diagonal operator.
-/

open scoped Matrix BigOperators
open Matrix

namespace QCryptLeanTest.LOCC.Instrument.ClassicalProbes

open TypedLOCC
open TypedLOCC.Instrument

/-! ## Empty finite types -/

/-- The unique function between empty finite types. -/
def emptyFunction : Fin 0 → Fin 0 := fun a => Fin.elim0 a

/-- On an empty input register, the empty nondemolition Kraus family resolves the empty identity.

This proof unfolds only the explicit Kraus definition; it does not use
`nondemolitionReadoutKraus_complete`. -/
theorem empty_nondemolitionReadoutKraus_complete :
    ∑ y : Fin 0,
        (nondemolitionReadoutKraus emptyFunction y)ᴴ *
          nondemolitionReadoutKraus emptyFunction y =
      (1 : Matrix (Fin 0) (Fin 0) ℂ) := by
  ext i j
  exact Fin.elim0 i

/-- On an empty input register, the empty rank-one Kraus family likewise resolves the empty
identity.

This proof unfolds only the explicit Kraus definition; it does not use
`functionAndForgetKraus_complete`. -/
theorem empty_functionAndForgetKraus_complete :
    ∑ a : Fin 0,
        (functionAndForgetKraus emptyFunction a)ᴴ *
          functionAndForgetKraus emptyFunction a =
      (1 : Matrix (Fin 0) (Fin 0) ℂ) := by
  ext i j
  exact Fin.elim0 i

/-! ## Many-to-one processing -/

/-- A many-to-one classical function on a two-element register. -/
def constantZero : Fin 2 → Fin 2 := fun _ => 0

/-- The two colliding input values remain different hidden Kraus indices. -/
theorem constantZero_hiddenKraus_distinct :
    functionAndForgetKraus constantZero 0 ≠
      functionAndForgetKraus constantZero 1 := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  simp [functionAndForgetKraus, constantZero] at h00

/-- A many-to-one readout still resolves the identity after summing over observed fibres. -/
theorem constantZero_nondemolitionReadoutKraus_complete :
    ∑ y : Fin 2,
        (nondemolitionReadoutKraus constantZero y)ᴴ *
          nondemolitionReadoutKraus constantZero y =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nondemolitionReadoutKraus, constantZero]

/-- Colliding output values do not spoil completeness because the input basis value is hidden
Kraus data rather than an observed outcome. -/
theorem constantZero_functionAndForgetKraus_complete :
    ∑ a : Fin 2,
        (functionAndForgetKraus constantZero a)ᴴ *
          functionAndForgetKraus constantZero a =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [functionAndForgetKraus, constantZero]

/-- Direct operator sum of the rank-one Kraus family, without passing through the certified
instrument or its operation theorem. -/
noncomputable def rawFunctionAndForget
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (f : A → B) (rho : Op A) : Op B :=
  ∑ a : A, matrixConjLinear (functionAndForgetKraus f a) rho

/-- For the constant function, both input populations accumulate at the same output basis value.
All other output entries vanish. -/
theorem constantZero_rawFunctionAndForget_apply (rho : Op (Fin 2)) (b b' : Fin 2) :
    rawFunctionAndForget constantZero rho b b' =
      if b = 0 ∧ b' = 0 then rho 0 0 + rho 1 1 else 0 := by
  fin_cases b <;> fin_cases b' <;>
    simp [rawFunctionAndForget, functionAndForgetKraus, constantZero,
      matrixConjLinear]

/-- The direct many-to-one operation preserves the sum of diagonal entries for every operator;
no Hermiticity, positivity, or normalization assumption is present. -/
theorem constantZero_rawFunctionAndForget_trace (rho : Op (Fin 2)) :
    ∑ b : Fin 2, rawFunctionAndForget constantZero rho b b =
      ∑ a : Fin 2, rho a a := by
  simp [constantZero_rawFunctionAndForget_apply]

/-- Direct discard absorption for the many-to-one operation on every operator, proved from the raw
Kraus sum and `discardToUnit_channel_apply`. -/
theorem constantZero_discard_rawFunctionAndForget (rho : Op (Fin 2)) :
    (discardToUnit (Fin 2)).channel (rawFunctionAndForget constantZero rho) =
      (discardToUnit (Fin 2)).channel rho := by
  ext u v
  cases u
  cases v
  simpa only [discardToUnit_channel_apply] using
    constantZero_rawFunctionAndForget_trace rho

/-! ## A non-Hermitian witness -/

/-- The off-diagonal matrix unit `|0⟩⟨1|`. -/
def offDiagonal : Op (Fin 2) := Matrix.single 0 1 1

/-- The chosen matrix unit is genuinely non-Hermitian. -/
theorem offDiagonal_not_selfAdjoint : offDiagonalᴴ ≠ offDiagonal := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  simp [offDiagonal, Matrix.conjTranspose_apply] at h01

/-- Direct single-outcome operation of the nondemolition Kraus matrix, without passing through
the certified instrument or its operation theorem. -/
noncomputable def rawNondemolitionReadout
    {A Y : Type} [Fintype A] [DecidableEq A] [DecidableEq Y]
    (f : A → Y) (y : Y) (rho : Op A) : Op A :=
  matrixConjLinear (nondemolitionReadoutKraus f y) rho

/-- Sum the directly defined outcome operations, without constructing the certified instrument. -/
noncomputable def rawNondemolitionChannel
    {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    (f : A → Y) (rho : Op A) : Op A :=
  ∑ y : Y, rawNondemolitionReadout f y rho

/-- Summing the outcomes of a constant coarse readout is the identity channel on every operator,
including all within-fibre coherences. -/
theorem constantZero_rawNondemolitionChannel (rho : Op (Fin 2)) :
    rawNondemolitionChannel constantZero rho = rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawNondemolitionChannel, rawNondemolitionReadout,
      nondemolitionReadoutKraus, constantZero, matrixConjLinear, Matrix.mul_apply]

/-- A constant nondemolition readout preserves coherence inside its sole occupied fibre, even on
the non-Hermitian matrix unit. -/
theorem constantZero_rawNondemolitionReadout_offDiagonal :
    rawNondemolitionReadout constantZero 0 offDiagonal = offDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawNondemolitionReadout, nondemolitionReadoutKraus, constantZero,
      offDiagonal, matrixConjLinear]

/-- Deterministic processing with the old value forgotten destroys the same off-diagonal matrix
unit, although its two basis values have the same image under constantZero. -/
theorem constantZero_rawFunctionAndForget_offDiagonal :
    rawFunctionAndForget constantZero offDiagonal = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawFunctionAndForget, functionAndForgetKraus, constantZero,
      offDiagonal, matrixConjLinear]

/-- The direct discard law in particular holds on the explicit non-Hermitian witness. -/
theorem constantZero_discard_nonHermitian :
    (discardToUnit (Fin 2)).channel
        (rawFunctionAndForget constantZero offDiagonal) =
      (discardToUnit (Fin 2)).channel offDiagonal :=
  constantZero_discard_rawFunctionAndForget offDiagonal

/-- The two direct operations are therefore unequal on an arbitrary, non-Hermitian operator.

This is the negative control against identifying a nondemolition coarse readout with a
fine-grained measurement whose input value is hidden. -/
theorem constantZero_readout_ne_functionAndForget :
    rawNondemolitionReadout constantZero 0 offDiagonal ≠
      rawFunctionAndForget constantZero offDiagonal := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  simp [rawNondemolitionReadout, nondemolitionReadoutKraus,
    rawFunctionAndForget, functionAndForgetKraus, constantZero,
    offDiagonal, matrixConjLinear] at h01

end QCryptLeanTest.LOCC.Instrument.ClassicalProbes
