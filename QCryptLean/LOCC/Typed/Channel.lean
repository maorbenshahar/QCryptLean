import QCryptLean.LOCC.Typed.Instrument

/-!
# Instrument operations and channels

This module defines the completely positive operations and total channel denoted by a certified
instrument, including the coordinate formula for the operation of an instrument lifted to a joint
typed register.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace TypedLOCC

/-- **The completely positive operation at one observed outcome.**  Its internal Kraus fibre is
summed out here and is never returned as classical data. -/
noncomputable def Instrument.operation {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    {Outcome : Type} [Fintype Outcome] (J : Instrument A B Outcome) (o : Outcome) :
    Op A →ₗ[ℂ] Op B :=
  ∑ r : J.krausIndex o, matrixConjLinear (J.kraus o r)

/-- Keeping an instrument outcome stores that outcome in the second output factor and has no
matrix entries in any other outcome block.  This is the operation-level form of the observed
classical record in the instrument-tree model of Chitambar--Leung--Mančinska--Ozols--Winter,
arXiv:1210.4583, Section 2. -/
@[simp] theorem Instrument.keeping_operation_apply
    {A HH Outcome : Type} [Fintype A] [DecidableEq A]
    [Fintype HH] [DecidableEq HH] [Fintype Outcome] [DecidableEq Outcome]
    (I : Instrument A HH Outcome) (o : Outcome) (rho : Op A)
    (h h' : HH) (y z : Outcome) :
    ((I.keeping.operation o) rho) (h, y) (h', z) =
      if y = o ∧ z = o then (I.operation o rho) h h' else 0 := by
  simp only [Instrument.operation, LinearMap.sum_apply, Instrument.keeping,
    matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  by_cases hy : y = o
  · subst y
    by_cases hz : z = o
    · subst z
      rw [if_pos ⟨rfl, rfl⟩]
      apply Finset.sum_congr rfl
      intro r _
      simp [Matrix.mul_apply]
    · simp [hz, Matrix.mul_apply]
  · simp [hy, Matrix.mul_apply]

/-- **The channel a certified instrument denotes.**  First sum the internal Kraus fibre of each
observed outcome, then sum the observed operations.  `Instrument.complete` certifies trace
preservation of this total map. -/
noncomputable def Instrument.channel {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    {Outcome : Type} [Fintype Outcome] (J : Instrument A B Outcome) : Op A →ₗ[ℂ] Op B :=
  ∑ o : Outcome, J.operation o

namespace Instrument

/-- Entrywise operation of an instrument lifted at one party.

The local input operator is the two-sided slice of `rho` selected by the spectator coordinate of
`q` on rows and the independently selected spectator coordinate of `q'` on columns.  The theorem
holds for every operator and every observed outcome, with no positivity, trace, self-adjointness,
or equality assumption on the two spectator coordinates.  It is the coordinate form of extending
a local CP operation by identities on the spectator registers. -/
theorem liftAt_operation_apply
    {P : Type} [Fintype P] [DecidableEq P]
    {R : MultipartiteSystem P} (i : P) {HH : Type}
    [Nonempty HH] [Fintype HH] [DecidableEq HH]
    {Outcome : Type} [Fintype Outcome]
    (I : Instrument (R.reg i) HH Outcome)
    (o : Outcome) (rho : Op R.total) (q q' : (R.set i HH).total) :
    ((I.liftAt R i).operation o rho) q q' =
      (I.operation o
        (rho.submatrix
          (fun x =>
            (R.splitAt i).symm
              (x, ((R.splitAtSet i HH) q).2))
          (fun y =>
            (R.splitAt i).symm
              (y, ((R.splitAtSet i HH) q').2))))
        ((R.splitAtSet i HH) q).1
        ((R.splitAtSet i HH) q').1 := by
  have hsum (f : R.total → ℂ) :
      (∑ x, f x) =
        ∑ p : R.reg i × R.rest i, f ((R.splitAt i).symm p) := by
    exact (Equiv.sum_comp (R.splitAt i).symm f).symm
  simp only [Instrument.operation, Instrument.liftAt, matrixConjLinear,
    LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.sum_apply, Matrix.mul_apply, localKrausLift_apply, ite_mul,
    zero_mul, Matrix.conjTranspose_apply, RCLike.star_def]
  simp_rw [hsum]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp [apply_ite]
  rfl

end Instrument
end TypedLOCC
