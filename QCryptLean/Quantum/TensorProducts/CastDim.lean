import QCryptLean.Quantum.TensorProducts.MatrixUnits

/-!
# Transporting an operator along a dimension equality

`Quantum.Operators.Op.castDim h` moves an operator between two registers whose dimensions are
equal as natural numbers. `Op.castDim_eq_reindex_finCongr` identifies it with the value-preserving
relabelling of their indices.

The additive, scalar, multiplicative, unit and adjoint laws are in
`Basic.lean`. This module gives the index-relabelling identity, composition
and cancellation laws, and the transport laws for finite
sums, matrix units and the two tensor factors. The same cast as a *matrix*, so that it can sit
inside a Kraus product, is `Quantum.TensorProducts.castRect`.

## Main statements

* `Quantum.TensorProducts.Op.castDim_eq_reindex_finCongr`: a dimension cast is the
  value-preserving reindex `finCongr h`.
* `Quantum.TensorProducts.Op.castDim_eq`, `Quantum.TensorProducts.Op.castDim_trans`,
  `Quantum.TensorProducts.Op.castDim_cancel`: a cast to the same register is the identity, casts
  compose, and a cast is undone by a cast back. Which proof of a dimension equality is supplied
  never matters. `Op.castDimLinear_trans` is the composition law for the linear-map form, and
  the three `DensityOp` companions carry the same laws to normalized states.
* `Quantum.TensorProducts.Op.castDim_zero`, `Quantum.TensorProducts.Op.castDim_sum`,
  `Quantum.TensorProducts.Op.castDim_sum_univ`: casts kill zero and commute with finite sums.
* `Quantum.TensorProducts.Op.castDim_trace`, `Quantum.TensorProducts.Op.castDim_posSemidef`: a
  cast preserves the trace and the positive cone.
* `Quantum.TensorProducts.Op.castDim_single`: a cast carries a matrix unit to the matrix unit at
  the cast indices.
* `Quantum.TensorProducts.Op.tensor_castDim_left`, `Quantum.TensorProducts.Op.tensor_castDim_right`:
  casting one tensor factor is casting the product along the induced dimension equality.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

/-- A dimension cast relabels each index to the index with the same numeral. -/
theorem Op.castDim_eq_reindex_finCongr {p q : ℕ} (h : p = q) (M : Op p) :
    Op.castDim h M = Matrix.reindex (finCongr h) (finCongr h) M := by
  subst h; rfl

/-- A cast of a register to itself is the identity, whichever proof of the (trivial) dimension
equality is supplied. The `Op` counterpart of Mathlib's `cast_eq`. -/
theorem Op.castDim_eq {p : ℕ} (h : p = p) (M : Op p) : Op.castDim h M = M := rfl

/-- Dimension casts compose. -/
theorem Op.castDim_trans {p q r : ℕ} (h₁ : p = q) (h₂ : q = r) (M : Op p) :
    Op.castDim h₂ (Op.castDim h₁ M) = Op.castDim (h₁.trans h₂) M := by
  subst h₁; subst h₂; rfl

/-- **A cast is undone by a cast back**, whichever two proofs of the dimension equalities are
supplied. -/
theorem Op.castDim_cancel {p q : ℕ} (h : p = q) (h' : q = p) (M : Op p) :
    Op.castDim h' (Op.castDim h M) = M := by
  subst h; rfl

/-- Dimension casts compose, in the linear-map form. -/
theorem Op.castDimLinear_trans {p q r : ℕ} (h₁ : p = q) (h₂ : q = r) (M : Op p) :
    Op.castDimLinear h₂ (Op.castDimLinear h₁ M) = Op.castDimLinear (h₁.trans h₂) M :=
  Op.castDim_trans h₁ h₂ M

/-- A cast of a density operator to the same register is the identity. -/
theorem DensityOp.castDim_eq {p : ℕ} (h : p = p) (ρ : DensityOp p) :
    DensityOp.castDim h ρ = ρ := rfl

/-- Density-operator dimension casts compose. -/
theorem DensityOp.castDim_trans {p q r : ℕ} (h₁ : p = q) (h₂ : q = r) (ρ : DensityOp p) :
    DensityOp.castDim h₂ (DensityOp.castDim h₁ ρ) = DensityOp.castDim (h₁.trans h₂) ρ := by
  subst h₁; subst h₂; rfl

/-- A density-operator cast is undone by a cast back. -/
theorem DensityOp.castDim_cancel {p q : ℕ} (h : p = q) (h' : q = p) (ρ : DensityOp p) :
    DensityOp.castDim h' (DensityOp.castDim h ρ) = ρ := by
  subst h; rfl

/-- A dimension cast kills the zero operator. -/
@[simp] theorem Op.castDim_zero {p q : ℕ} (h : p = q) : Op.castDim h (0 : Op p) = 0 := by
  subst h; rfl

/-- A dimension cast preserves the trace. -/
theorem Op.castDim_trace {p q : ℕ} (h : p = q) (A : Op p) :
    (Op.castDim h A).trace = A.trace := by
  subst h; rfl

/-- A dimension cast preserves positive semidefiniteness. -/
theorem Op.castDim_posSemidef {p q : ℕ} (h : p = q) (A : Op p) (hA : A.PosSemidef) :
    (Op.castDim h A).PosSemidef := by
  subst h; exact hA

/-- Dimension casts commute with finite sums. -/
theorem Op.castDim_sum {p q : ℕ} (h : p = q) {ι : Type*} (s : Finset ι) (f : ι → Op p) :
    Op.castDim h (∑ i ∈ s, f i) = ∑ i ∈ s, Op.castDim h (f i) := by
  subst h; rfl

/-- `Quantum.TensorProducts.Op.castDim_sum` at a `Finset.univ` sum. -/
theorem Op.castDim_sum_univ {p q : ℕ} (h : p = q) {ι : Type*} [Fintype ι] (f : ι → Op p) :
    Op.castDim h (∑ i, f i) = ∑ i, Op.castDim h (f i) :=
  Op.castDim_sum h Finset.univ f

/-- A cast carries a matrix unit to the matrix unit at the cast indices. The diagonal case
`Matrix.single a a 1` is a rank-one basis projector, which is how this is usually met. -/
theorem Op.castDim_single {c c' : ℕ} (h : c = c') (a b : Fin c) (v : ℂ) :
    Op.castDim h (Matrix.single a b v) =
      Matrix.single (Fin.cast h a) (Fin.cast h b) v := by
  subst h; rfl

/-- A cast of the **left** tensor factor is a cast of the product. -/
theorem Op.tensor_castDim_left {p p' q : ℕ} (h : p = p') (M : Op p) (N : Op q) :
    Op.tensor (Op.castDim h M) N = Op.castDim (congrArg (· * q) h) (Op.tensor M N) := by
  subst h; rfl

/-- A cast of the **right** tensor factor is a cast of the product. -/
theorem Op.tensor_castDim_right {p q q' : ℕ} (h : q = q') (M : Op p) (N : Op q) :
    Op.tensor M (Op.castDim h N) = Op.castDim (congrArg (p * ·) h) (Op.tensor M N) := by
  subst h; rfl

end Quantum.TensorProducts

end
