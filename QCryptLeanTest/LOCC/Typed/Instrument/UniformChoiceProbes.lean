import QCryptLean.LOCC.Typed.Instrument.UniformChoice
import Mathlib.Util.AssertNoSorry

/-!
# Definition-level probes for uniform finite instrument choice

These probes use the explicit scale and Kraus definitions.  None of the five theorem stubs in
`UniformChoice.lean` is used.  A four-seed family exposes the exact amplitude `1/2` and branch
weight `1/4`; its certified member has two hidden Kraus indices behind one observed local outcome.
The operator witness is deliberately non-Hermitian.
-/

open scoped Matrix BigOperators
open Matrix

namespace QCryptLeanTest.LOCC.Instrument.UniformChoiceProbes

open TypedLOCC
open TypedLOCC.Instrument

/-! ## A certified instrument with more than one hidden Kraus index -/

/-- The computational-basis rank-one projector at `t`. -/
def basisProjector (t : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => if i = t ∧ j = t then 1 else 0

/-- One observed outcome with two hidden Kraus representatives.  Their sum is the dephasing
channel, so completeness is proved here without any uniform-choice law. -/
def twoHidden : Instrument (Fin 2) (Fin 2) Unit where
  krausIndex _ := Fin 2
  kraus _ t := basisProjector t
  complete := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [basisProjector, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The seed selects a member of the family.  Identical members are intentional: seed visibility
is tested independently of any same-dimensional renaming of the local basis. -/
def family (_ : Fin 4) : Instrument (Fin 2) (Fin 2) Unit := twoHidden

/-- Four equiprobable seeds have Kraus amplitude exactly `1/2`. -/
theorem finFour_scale : uniformChoiceScale (R := Fin 4) = (1 / 2 : ℂ) := by
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  norm_num [uniformChoiceScale, hsqrt]

/-- The raw uniform-choice Kraus matrix has the expected amplitude on its supported diagonal.
This unfolds `uniformChoiceKraus` itself, not `uniformChoice_kraus`. -/
theorem finFour_rawKraus_diagonal (r : Fin 4) (t : Fin 2) :
    uniformChoiceKraus family r () t t t = (1 / 2 : ℂ) := by
  simp [uniformChoiceKraus, family, twoHidden, basisProjector, finFour_scale]

/-- The same raw Kraus matrix vanishes off the basis point selected by its hidden index. -/
theorem finFour_rawKraus_offSupport (r : Fin 4) (t i j : Fin 2)
    (h : ¬ (i = t ∧ j = t)) :
    uniformChoiceKraus family r () t i j = 0 := by
  simp [uniformChoiceKraus, family, twoHidden, basisProjector, h]

/-! ## Exact branch weight on an arbitrary operator -/

/-- Directly sum the hidden Kraus fibre at one observed branch. -/
noncomputable def rawUniformBranch
    {A B R Y : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype Y] (I : R → Instrument A B Y) (r : R) (y : Y) (rho : Op A) : Op B :=
  ∑ t : (I r).krausIndex y, matrixConjLinear (uniformChoiceKraus I r y t) rho

/-- A matrix with both a population and an off-diagonal entry. -/
def nonHermitian : Op (Fin 2) :=
  Matrix.single 0 0 1 + Matrix.single 0 1 1

/-- The branch-weight witness is genuinely non-Hermitian. -/
theorem nonHermitian_not_selfAdjoint : nonHermitianᴴ ≠ nonHermitian := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  simp [nonHermitian, Matrix.conjTranspose_apply] at h01

/-- A fixed observed seed branch carries exactly one quarter of the retained population. -/
theorem finFour_rawBranch_weight (r : Fin 4) :
    rawUniformBranch family r () nonHermitian 0 0 = (1 / 4 : ℂ) := by
  simp [rawUniformBranch, uniformChoiceKraus, finFour_scale, family, twoHidden,
    basisProjector, nonHermitian, matrixConjLinear, Matrix.sum_apply, Matrix.mul_apply]
  norm_num [map_ofNat]

/-- The dephasing member destroys the off-diagonal part of the same non-Hermitian witness. -/
theorem finFour_rawBranch_offDiagonal (r : Fin 4) :
    rawUniformBranch family r () nonHermitian 0 1 = 0 := by
  simp [rawUniformBranch, uniformChoiceKraus, finFour_scale, family, twoHidden,
    basisProjector, nonHermitian, matrixConjLinear, Matrix.sum_apply, Matrix.mul_apply]

/-! ## Observed pairs and hidden fibres remain separate -/

/-- Different seeds are different observed outcomes even when the selected instruments coincide. -/
theorem observed_seed_pairs_distinct :
    ((0, ()) : Fin 4 × Unit) ≠ ((1, ()) : Fin 4 × Unit) := by
  decide

/-- The raw dependent hidden fibre at `(r, ())` is exactly the member instrument's two-element
fibre; it does not acquire the observed seed as another hidden coordinate. -/
abbrev RawHidden (ry : Fin 4 × Unit) : Type :=
  (family ry.1).krausIndex ry.2

theorem hidden_fibre_card (r : Fin 4) :
    Fintype.card (RawHidden (r, ())) = 2 := by
  rfl

def hiddenZero (r : Fin 4) : RawHidden (r, ()) := by
  change Fin 2
  exact 0

def hiddenOne (r : Fin 4) : RawHidden (r, ()) := by
  change Fin 2
  exact 1

/-- Multiple hidden representatives remain distinct behind the same observed pair. -/
theorem hidden_indices_distinct (r : Fin 4) : hiddenZero r ≠ hiddenOne r := by
  change (0 : Fin 2) ≠ 1
  decide

/-! ## Empty input is valid, while an empty seed type is not -/

/-- A certified instrument on an empty input and output carrier. -/
def emptyInputInstrument : Instrument (Fin 0) (Fin 0) Unit where
  krausIndex _ := Unit
  kraus _ _ := 0
  complete := by
    ext i j
    exact Fin.elim0 i

def emptyInputFamily (_ : Fin 4) : Instrument (Fin 0) (Fin 0) Unit :=
  emptyInputInstrument

/-- The directly scaled family is complete on an empty input.  This is proved extensionally from
the raw definition and does not invoke `uniformChoiceKraus_complete`. -/
theorem empty_input_rawKraus_complete :
    ∑ ry : Fin 4 × Unit, ∑ t : (emptyInputFamily ry.1).krausIndex ry.2,
        (uniformChoiceKraus emptyInputFamily ry.1 ry.2 t)ᴴ *
          uniformChoiceKraus emptyInputFamily ry.1 ry.2 t =
      (1 : Matrix (Fin 0) (Fin 0) ℂ) := by
  ext i j
  exact Fin.elim0 i

def emptySeedFamily : Fin 0 → Instrument (Fin 0) (Fin 0) Unit :=
  fun r => Fin.elim0 r

/-- `Nonempty R` is a genuine constructor requirement: an empty seed family cannot be passed to
`uniformChoice`.  This is an elaboration failure, not an unproved mathematical claim. -/
example : True := by
  fail_if_success
    let _bad := uniformChoice emptySeedFamily
  trivial

end QCryptLeanTest.LOCC.Instrument.UniformChoiceProbes
