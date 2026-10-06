import QCryptLean.LOCC.Typed.Instrument.Discard

/-!
# Finite classical processing as typed quantum instruments

This module gives direct Kraus constructions for two classical operations used by finite LOCC
programs.  `nondemolitionReadout f` observes `f a` while retaining the input register, whereas
`functionAndForget f` writes `f a` into a new register and discards the old value.  Their observed
outcomes and hidden Kraus indices are explicit in the `Instrument` type.

The instrument semantics follow Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2.  The two constructions formalize the local classical processing used
in the QKD protocols described in arXiv:0809.3019, `main.tex:408`--`:448` and
arXiv:2403.11851, `main.tex:910`--`:919`.
-/

open scoped Matrix BigOperators
open Matrix

namespace TypedLOCC
namespace Instrument

variable {alpha beta Y : Type}

/-! ## Nondemolition readout -/

/-- The Kraus matrix for observing `y` under a deterministic readout `f` while retaining the
input register.  It is the diagonal projector onto the fibre `f⁻¹ {y}`. -/
def nondemolitionReadoutKraus [Fintype alpha] [DecidableEq alpha]
    [DecidableEq Y] (f : alpha → Y) (y : Y) : Matrix alpha alpha ℂ :=
  Matrix.diagonal fun a => if f a = y then 1 else 0

/-- Entrywise formula for the fibre projector used by `nondemolitionReadout`.

This is the single-Kraus CP operation at one observed outcome in the finite-instrument
description of arXiv:1210.4583, Section 2. -/
@[simp] theorem nondemolitionReadoutKraus_apply [Fintype alpha] [DecidableEq alpha]
    [DecidableEq Y] (f : alpha → Y) (y : Y) (a b : alpha) :
    nondemolitionReadoutKraus f y a b =
      if a = b ∧ f a = y then 1 else 0 := by
  by_cases h : a = b <;> simp [nondemolitionReadoutKraus, h]

/-- The fibre projectors of a deterministic readout resolve the identity.

This is the completeness equation for the finite instrument whose observed outcome is `f a`;
compare the finite-outcome instrument normalization in arXiv:1210.4583, Section 2. -/
theorem nondemolitionReadoutKraus_complete [Fintype alpha] [DecidableEq alpha]
    [Fintype Y] [DecidableEq Y] (f : alpha → Y) :
    ∑ y : Y, (nondemolitionReadoutKraus f y)ᴴ * nondemolitionReadoutKraus f y = 1 := by
  classical
  ext a b
  simp [Matrix.sum_apply, nondemolitionReadoutKraus, Matrix.diagonal_apply,
    Matrix.one_apply]

/-- Observe `f a` and retain the input register.

The observed outcome is `Y`; the hidden Kraus fibre is `Unit`.  At outcome `y`, the CP operation
is conjugation by the diagonal projector onto `f⁻¹ {y}`. -/
def nondemolitionReadout [Fintype alpha] [DecidableEq alpha]
    [Fintype Y] [DecidableEq Y] (f : alpha → Y) : Instrument alpha alpha Y where
  krausIndex _ := Unit
  kraus y _ := nondemolitionReadoutKraus f y
  complete := by
    simpa only [Fintype.sum_unique] using nondemolitionReadoutKraus_complete f

/-- The certified readout exposes exactly the fibre-projector Kraus matrix. -/
@[simp] theorem nondemolitionReadout_kraus [Fintype alpha] [DecidableEq alpha]
    [Fintype Y] [DecidableEq Y] (f : alpha → Y) (y : Y) :
    (nondemolitionReadout f).kraus y () = nondemolitionReadoutKraus f y := by
  rfl

/-- Exact operation of a nondemolition readout on an arbitrary operator.

The outcome-`y` branch retains precisely the matrix entries whose two indices lie in the fibre
`f⁻¹ {y}`.  Thus it preserves coherences inside one fibre; no diagonality hypothesis on `rho`
is assumed. -/
@[simp] theorem nondemolitionReadout_operation_apply [Fintype alpha] [DecidableEq alpha]
    [Fintype Y] [DecidableEq Y] (f : alpha → Y) (y : Y)
    (rho : Op alpha) (a b : alpha) :
    ((nondemolitionReadout f).operation y rho) a b =
      if f a = y ∧ f b = y then rho a b else 0 := by
  by_cases ha : f a = y <;> by_cases hb : f b = y <;>
    simp [Instrument.operation, nondemolitionReadout, matrixConjLinear,
      Matrix.mul_apply, nondemolitionReadoutKraus_apply, ha, hb]

/-! ## Deterministic processing with the input value forgotten -/

/-- The hidden Kraus matrix that sends the basis value `a` to `f a`.

Keeping `a` as the hidden Kraus index, rather than as an observed outcome, makes the resulting
instrument a one-outcome local channel. -/
def functionAndForgetKraus [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] (f : alpha → beta) (a : alpha) :
    Matrix beta alpha ℂ :=
  Matrix.single (f a) a 1

/-- Entrywise formula for the rank-one Kraus matrix of `functionAndForget`. -/
@[simp] theorem functionAndForgetKraus_apply [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] (f : alpha → beta) (a : alpha)
    (b : beta) (a' : alpha) :
    functionAndForgetKraus f a b a' =
      if b = f a ∧ a' = a then 1 else 0 := by
  simp only [functionAndForgetKraus, Matrix.single_apply, eq_comm]

/-- The rank-one Kraus family for deterministic processing and forgetting resolves the input
identity.

The output values `f a` need not be distinct: each input basis value has its own hidden Kraus
index.  This is the completeness equation for the local classical post-processing maps described
in arXiv:0809.3019, `main.tex:408`--`:448` and
arXiv:2403.11851, `main.tex:910`--`:919`. -/
theorem functionAndForgetKraus_complete [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] (f : alpha → beta) :
    ∑ a : alpha, (functionAndForgetKraus f a)ᴴ * functionAndForgetKraus f a = 1 := by
  have ha : ∀ a : alpha,
      (functionAndForgetKraus f a)ᴴ * functionAndForgetKraus f a =
        Matrix.single a a (1 : ℂ) := by
    intro a
    rw [functionAndForgetKraus, Matrix.conjTranspose_single,
      Matrix.single_mul_single_same]
    simp
  simp_rw [ha]
  ext i j
  simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Apply the deterministic classical function `f` and discard the old basis value.

The observed outcome is `Unit`; the input basis value is the hidden Kraus index.  Hence the map
is measure-and-prepare on arbitrary operators and agrees with ordinary deterministic processing
on computational-basis classical states. -/
def functionAndForget [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] (f : alpha → beta) : Instrument alpha beta Unit where
  krausIndex _ := alpha
  kraus _ a := functionAndForgetKraus f a
  complete := by
    simpa only [Fintype.sum_unique] using functionAndForgetKraus_complete f

/-- The certified deterministic-processing instrument exposes exactly its rank-one Kraus
family. -/
@[simp] theorem functionAndForget_kraus [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] (f : alpha → beta) (a : alpha) :
    (functionAndForget f).kraus () a = functionAndForgetKraus f a := by
  rfl

/-- Exact one-outcome operation of `functionAndForget` on an arbitrary operator.

Only input diagonal entries remain, and every such entry is accumulated at the diagonal output
coordinate selected by `f`. -/
@[simp] theorem functionAndForget_operation_apply [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] (f : alpha → beta)
    (rho : Op alpha) (b b' : beta) :
    ((functionAndForget f).operation () rho) b b' =
      ∑ a : alpha, if b = f a ∧ b' = f a then rho a a else 0 := by
  simp only [Instrument.operation, LinearMap.sum_apply, functionAndForget,
    matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, functionAndForgetKraus_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hb : b = f a <;> by_cases hb' : b' = f a <;> simp [hb, hb']

/-! ## Trace preservation and discard -/

/-- The channel of any certified finite instrument preserves the sum of diagonal entries.

This is the matrix trace-preservation consequence of `Instrument.complete`; it is the total-map
normalization in the finite-instrument definition of arXiv:1210.4583, Section 2. -/
theorem channel_trace_eq [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta] [Fintype Y]
    (I : Instrument alpha beta Y) (rho : Op alpha) :
    ∑ b : beta, (I.channel rho) b b = ∑ a : alpha, rho a a := by
  change Matrix.trace (I.channel rho) = Matrix.trace rho
  unfold Instrument.channel Instrument.operation
  simp only [LinearMap.sum_apply, matrixConjLinear, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_sum]
  calc
    _ = ∑ y : Y, ∑ r : I.krausIndex y,
          Matrix.trace ((I.kraus y r)ᴴ * I.kraus y r * rho) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro r _
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((∑ y : Y, ∑ r : I.krausIndex y,
        (I.kraus y r)ᴴ * I.kraus y r) * rho) := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
      simp_rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = _ := by rw [I.complete, Matrix.one_mul]

/-- Discarding the output of any certified instrument equals discarding its input.

This is an equality of linear maps and therefore holds on every operator, without a classicality,
positivity, or trace-one hypothesis. -/
theorem discardToUnit_comp_channel [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    [Fintype beta] [DecidableEq beta] [Nonempty beta] [Fintype Y]
    (I : Instrument alpha beta Y) :
    (discardToUnit beta).channel.comp I.channel = (discardToUnit alpha).channel := by
  ext rho u v
  cases u
  cases v
  simpa only [LinearMap.comp_apply, discardToUnit_channel_apply] using
    channel_trace_eq I rho

/-- Discarding after `functionAndForget f` equals discarding the original register, on every
operator. -/
theorem discardToUnit_comp_functionAndForget [Fintype alpha] [DecidableEq alpha]
    [Nonempty alpha] [Fintype beta] [DecidableEq beta] [Nonempty beta]
    (f : alpha → beta) :
    (discardToUnit beta).channel.comp (functionAndForget f).channel =
      (discardToUnit alpha).channel := by
  exact discardToUnit_comp_channel (functionAndForget f)

end Instrument
end TypedLOCC
