import QCryptLean.Quantum.Operators.InverseSqrt
import QCryptLean.Quantum.Operators.OpGeoMean
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Antitonicity of the inverse square root

`A ⪯ B` between positive definite operators implies `B^{−1/2} ⪯ A^{−1/2}`: replacing a reference by
a smaller one can only raise the `σ^{−1/2}`-weighted readout of a positive semidefinite block.

This is the operator step behind a **reference change** in a collision-entropy or leftover-hashing
chain.  Only two operator-monotonicity facts are used, both in Mathlib:

* `CStarAlgebra.inv_le_inv` — inversion is antitone on the positive units, i.e. `A ≤ B ⟹ B⁻¹ ≤ A⁻¹`;
* `CFC.sqrt_le_sqrt` — Löwner–Heinz at exponent `½` (Bhatia, *Matrix Analysis*, §V.1), i.e.
  `X ≤ Y ⟹ √X ≤ √Y`.

`Matrix.PosDef.inverseSqrt hσ` is **by definition** `CFC.sqrt σ⁻¹` (`InverseSqrt.lean`), so the two
compose directly.  Nothing here needs Frobenius-sandwich monotonicity, the operator geometric mean,
or any block-diagonal inverse-square-root theory: the reference change of a collision quantity
happens at the level of the scalar `Re Tr[σ^{−1/2}·M]` for a single fixed `M`, where
`Quantum.Operators.trace_mul_le_of_opLe` (`PSDOrder.lean`) finishes the job.

The `CStarAlgebra (Op N)` instance is introduced **locally**, in the proof body only, from the
file-level `open scoped Matrix.Norms.L2Operator`; it is never exported, so the L2 operator
`NormedRing` cannot leak into downstream typeclass synthesis (the pattern of
`InfoTheory.DeFinetti.sqrtOp_continuous`).

Reference: Bhatia, *Matrix Analysis* (1997), §V.1 (Löwner–Heinz) and Prop. V.1.6 (inverse
antitonicity).
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Matrix.PosDef

/-- **Inverse antitonicity in the Löwner order.**  For positive definite `A ⪯ B`, `B⁻¹ ⪯ A⁻¹`.

`CStarAlgebra.inv_le_inv` on the units `A`, `B` of `Op N`, with `Matrix.coe_units_inv` identifying
the group inverse of the unit with the nonsingular matrix inverse. -/
theorem matrix_inv_le_inv_of_le {N : ℕ} {A B : Op N} (hA : A.PosDef) (hB : B.PosDef)
    (h : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  let : CStarAlgebra (Op N) := {}
  have hu := CStarAlgebra.inv_le_inv (a := hA.isUnit.unit) (b := hB.isUnit.unit)
    (by rw [IsUnit.unit_spec]; exact hA.posSemidef.nonneg)
    (by rw [IsUnit.unit_spec, IsUnit.unit_spec]; exact h)
  have e1 : ((hA.isUnit.unit⁻¹ : (Op N)ˣ) : Op N) = A⁻¹ := by
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
  have e2 : ((hB.isUnit.unit⁻¹ : (Op N)ˣ) : Op N) = B⁻¹ := by
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
  rwa [e1, e2] at hu

/-- **The inverse square root is antitone.**  `A ⪯ B` between positive definite operators gives
`B^{−1/2} ⪯ A^{−1/2}`.

Inverse antitonicity followed by Löwner–Heinz at exponent `½`
(`matrix_inv_le_inv_of_le`, then `CFC.sqrt_le_sqrt`), read through the definitional
`hσ.inverseSqrt = CFC.sqrt σ⁻¹`. -/
theorem opLe_inverseSqrt_antitone {N : ℕ} {A B : Op N} (hA : A.PosDef) (hB : B.PosDef)
    (h : opLe A B) : opLe hB.inverseSqrt hA.inverseSqrt := by
  let : CStarAlgebra (Op N) := {}
  have hle : A ≤ B := Matrix.le_iff.mpr (opLe.posSemidef_sub hA.isHermitian hB.isHermitian h)
  exact opLe_of_matrix_le (by
    simpa [Matrix.PosDef.inverseSqrt] using
      CFC.sqrt_le_sqrt B⁻¹ A⁻¹ (matrix_inv_le_inv_of_le hA hB hle))

end Matrix.PosDef

namespace Quantum.Operators

/-- **The reference-change inequality, at the scalar level.**

If the reference `R` is dominated by `σ` in the Löwner order, then for every positive semidefinite
block `M` the `R`-weighted readout is at least the `σ`-weighted one:

`Re Tr[σ^{−1/2}·M] ≤ Re Tr[R^{−1/2}·M]`.

`opLe_inverseSqrt_antitone` supplies `σ^{−1/2} ⪯ R^{−1/2}` and `trace_mul_le_of_opLe`
(`PSDOrder.lean`) turns it into the trace inequality against `M ⪰ 0`. -/
theorem re_trace_inverseSqrt_mul_le_of_opLe {N : ℕ} {R σ : Op N}
    (hR : R.PosDef) (hσ : σ.PosDef) (hdom : opLe R σ) {M : Op N} (hM : M.PosSemidef) :
    (hσ.inverseSqrt * M).trace.re ≤ (hR.inverseSqrt * M).trace.re := by
  have hanti : opLe hσ.inverseSqrt hR.inverseSqrt :=
    Matrix.PosDef.opLe_inverseSqrt_antitone hR hσ hdom
  have h := Quantum.Operators.trace_mul_le_of_opLe hM
    hσ.inverseSqrt_isHermitian hR.inverseSqrt_isHermitian hanti
  rwa [Matrix.trace_mul_comm M hσ.inverseSqrt, Matrix.trace_mul_comm M hR.inverseSqrt] at h

end Quantum.Operators

end -- noncomputable section
