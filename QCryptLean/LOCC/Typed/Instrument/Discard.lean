import QCryptLean.LOCC.Typed.ChannelCoordinates

/-!
# Discarding a finite typed register

This module presents the local discard channel directly on an arbitrary finite basis type.
The retained factor has dimension one, the observed outcome is `Unit`, and the traced basis
index is a hidden Kraus index.
-/

open scoped Matrix BigOperators
open Matrix

namespace TypedLOCC

/-- The explicit coordinate equivalence between the trivial register and `Fin 1`. -/
def unitEquivFinOne : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := (Fin.eq_zero i).symm

/-- **Discard a finite local register to the trivial register.**

The observed outcome is `Unit`.  The input basis `K` is instead the hidden Kraus fibre, with
Kraus matrices `⟨k|`.  Thus the total operation is the partial trace to a one-dimensional
factor. This is the local discard operation used in the instrument trees of
Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2. -/
def Instrument.discardToUnit (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] :
    Instrument K Unit Unit where
  krausIndex _ := K
  kraus _ k := Matrix.of fun _ x => if x = k then 1 else 0
  complete := by
    ext x y
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply, Finset.univ_unique, Finset.sum_singleton,
      apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, zero_mul, one_mul]
    rw [Finset.sum_ite_eq Finset.univ x (fun k => if y = k then (1 : ℂ) else 0)]
    simp only [Finset.mem_univ, if_true]
    exact if_congr eq_comm rfl rfl

/-- The individual hidden Kraus matrices of `discardToUnit` are the basis bras. -/
@[simp] theorem Instrument.discardToUnit_kraus_apply
    (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (k x : K) :
    (Instrument.discardToUnit K).kraus () k () x =
      if x = k then 1 else 0 := rfl

/-- Distinct input and hidden-basis indices give a zero entry.  In particular, on every basis of
cardinality greater than one, `discardToUnit` is not represented by a one-row all-ones Kraus
matrix. -/
@[simp] theorem Instrument.discardToUnit_kraus_apply_of_ne
    (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (k x : K) (h : x ≠ k) :
    (Instrument.discardToUnit K).kraus () k () x = 0 := by
  simp [Instrument.discardToUnit_kraus_apply, h]

/-- The hidden basis-bra Kraus family satisfies the resolution of the identity. -/
theorem Instrument.discardToUnit_complete
    (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] :
    ∑ k : K, ((Instrument.discardToUnit K).kraus () k)ᴴ *
      (Instrument.discardToUnit K).kraus () k = 1 := by
  simpa using (Instrument.discardToUnit K).complete

/-- The unique observed operation of `discardToUnit` returns the trace of the input matrix. -/
@[simp] theorem Instrument.discardToUnit_operation_apply
    (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (rho : Op K) :
    ((Instrument.discardToUnit K).operation () rho) () () = ∑ x : K, rho x x := by
  simp only [Instrument.operation, LinearMap.sum_apply, Instrument.discardToUnit,
    matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.mul_apply]

/-- The total channel of `discardToUnit` is its unique operation and returns the matrix trace. -/
@[simp] theorem Instrument.discardToUnit_channel_apply
    (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (rho : Op K) :
    ((Instrument.discardToUnit K).channel rho) () () = ∑ x : K, rho x x := by
  simp [Instrument.channel, Instrument.discardToUnit_operation_apply]

/-- The finite-coordinate discard channel is CPTP, obtained directly from instrument
completeness via `Instrument.coordinateChannel_isCPTP`. -/
theorem Instrument.discardToUnit_coordinateChannel_isCPTP
    (K : Type) [Fintype K] [DecidableEq K] [Nonempty K]
    {dK : ℕ} [NeZero dK] (eK : K ≃ Fin dK) :
    Quantum.Channels.IsCPTP
      ⇑(coordinateLinear eK unitEquivFinOne (Instrument.discardToUnit K).channel) :=
  (Instrument.discardToUnit K).coordinateChannel_isCPTP eK unitEquivFinOne

end TypedLOCC
