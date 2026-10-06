import QCryptLean.Quantum.Channels.CPTP.Basic

/-!
# CPTP Positive Transport — trace-rescaling completely positive maps

This file provides small completely positive map constructions used to transport
positive semidefinite operator blocks between finite-dimensional systems.

## Main definitions
- `traceSmulMap`: the trace-rescaling linear map `X ↦ Tr(X) * c • B`.

## Main statements
- `op_tensor_one_posSemidef`: `1 ⊗ B` is positive semidefinite when `B` is.
- `choiMatrix_traceSmulMap`: Choi matrix of `traceSmulMap`.
- `exists_isCompletelyPositive_map_apply_eq_of_posSemidef_nonzero`: a
  trace-rescaling CP map sends a nonzero positive block to a chosen positive
  block.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Tensoring a positive operator with the identity on the left preserves
positive semidefiniteness. -/
lemma op_tensor_one_posSemidef {n m : ℕ} [NeZero n] [NeZero m] {B : Op m}
    (hB : B.PosSemidef) :
    (Quantum.TensorProducts.Op.tensor (1 : Op n) B).PosSemidef := by
  have hKron :
      (Matrix.kroneckerMap (· * ·) (1 : Op n) B).PosSemidef :=
    Matrix.PosSemidef.one.kronecker hB
  change (Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.kroneckerMap (· * ·) (1 : Op n) B)).PosSemidef
  rw [Matrix.reindex_apply]
  exact (Matrix.posSemidef_submatrix_equiv finProdFinEquiv.symm).mpr hKron

/-- The trace-rescaling linear map `X ↦ Tr(X) * c • B`. -/
def traceSmulMap {n m : ℕ} (c : ℂ) (B : Op m) : Op n →ₗ[ℂ] Op m :=
  { toFun := fun X => (X.trace * c) • B
    map_add' := by
      intro X Y
      ext i j
      simp [Matrix.trace_add, add_mul]
    map_smul' := by
      intro a X
      ext i j
      simp [Matrix.trace_smul]
      ring_nf }

/-- The Choi matrix of `traceSmulMap c B` is `c • (1 ⊗ B)`. -/
lemma choiMatrix_traceSmulMap {n m : ℕ} [NeZero n] [NeZero m]
    (c : ℂ) (B : Op m) :
    ChoiMatrix n m (⇑(traceSmulMap (n := n) c B)) =
      c • Quantum.TensorProducts.Op.tensor (1 : Op n) B := by
  ext α β
  simp only [ChoiMatrix, traceSmulMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.of_apply, Matrix.smul_apply, Quantum.TensorProducts.Op.tensor,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [trace_matrixUnit]
  ring_nf

/-- A nonzero positive input block can be transported to any positive output
block by a completely positive linear map.

One concrete construction is the entanglement-breaking map
`X ↦ (Tr X / Tr A) • B`; the nonzero PSD hypothesis gives `0 < Tr A`. -/
lemma exists_isCompletelyPositive_map_apply_eq_of_posSemidef_nonzero
    {n m : ℕ} [NeZero n] [NeZero m] {A : Op n} {B : Op m}
    (hA : A.PosSemidef) (hA_ne : A ≠ 0) (hB : B.PosSemidef) :
    ∃ Φ : Op n →ₗ[ℂ] Op m, IsCompletelyPositive (⇑Φ) ∧ B = Φ A := by
  let Φ : Op n →ₗ[ℂ] Op m := traceSmulMap (A.trace)⁻¹ B
  refine ⟨Φ, ?_, ?_⟩
  · have hChoieq :
        ChoiMatrix n m (⇑Φ) =
          (A.trace)⁻¹ • Quantum.TensorProducts.Op.tensor (1 : Op n) B := by
      simpa [Φ] using choiMatrix_traceSmulMap (A.trace)⁻¹ B
    unfold IsCompletelyPositive
    rw [hChoieq]
    exact Matrix.PosSemidef.smul (op_tensor_one_posSemidef hB)
      (inv_nonneg.mpr hA.trace_nonneg)
  · have htr_ne : A.trace ≠ 0 := by
      intro htr_zero
      exact hA_ne ((hA.trace_eq_zero_iff).mp htr_zero)
    rw [show Φ A = B by
      ext i j
      simp [Φ, traceSmulMap, mul_inv_cancel₀ htr_ne]]

/-- Preparing a normalized positive operator is a channel. -/
lemma traceSmulMap_one_isCPTP {a b : ℕ} [NeZero a] [NeZero b] (ρ : DensityOp b) :
    IsCPTP ⇑(traceSmulMap (n := a) 1 ρ.toOp) := by
  refine ⟨(traceSmulMap 1 ρ.toOp).isLinear, ?_, ?_⟩
  · unfold IsCompletelyPositive
    rw [choiMatrix_traceSmulMap, one_smul]
    exact op_tensor_one_posSemidef (posSemidefOp_implies_mathlib ρ.toPosSemidefOp)
  · intro A
    simp [traceSmulMap, Matrix.trace_smul, ρ.trace_one]

end Quantum.Channels

end
