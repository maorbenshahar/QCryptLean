import QCryptLean.Quantum.Operators.Types
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Complex.Basic

/-!
# The topology of density operators

Density operators carry the **entrywise topology**: the topology induced by the embedding
`DensityOp.toOp : DensityOp n → Op n` into matrices. In this topology the state space is compact.
Its image is the set of positive semidefinite matrices of trace one, which is closed (the positive
semidefinite cone is closed) and bounded (every entry of a positive semidefinite matrix of trace
at most one has norm at most one).

Compactness makes every continuous function of the state bounded, so a continuous function of the
state is integrable against any finite measure on the state space
(`Continuous.integrable_of_compactSpace`).

## Main definitions

- `Quantum.Operators.instTopologicalSpaceDensityOp`: the entrywise topology on `DensityOp n`.

## Main statements

- `DensityOp.isEmbedding_toOp`, `DensityOp.continuous_toOp`: `toOp` is a topological embedding.
- `DensityOp.range_toOp`: its range is the set of positive semidefinite matrices of trace one.
- `isClosed_setOf_posSemidef`: the positive semidefinite cone is closed.
- `posSemidef_entry_norm_sq_le_diag_mul`, `posSemidef_trace_le_one_entry_norm_le_one`,
  `DensityOp.entry_norm_le_one`: the entry bounds `‖A i j‖² ≤ A i i · A j j` and
  `‖A i j‖ ≤ 1` for positive semidefinite `A` with trace at most one.
- The instances `T2Space (DensityOp n)` and `CompactSpace (DensityOp n)`.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace Quantum.Operators

variable {n : ℕ}

/-- The entrywise topology on density operators, induced by the embedding into matrices. -/
instance instTopologicalSpaceDensityOp : TopologicalSpace (DensityOp n) :=
  TopologicalSpace.induced (fun ρ => ρ.toOp) inferInstance

namespace DensityOp

/-- The embedding `ρ ↦ ρ.toOp` of `DensityOp n` into matrices is a topological embedding. -/
theorem isEmbedding_toOp : Topology.IsEmbedding (fun ρ : DensityOp n => ρ.toOp) :=
  ⟨⟨rfl⟩, fun _ _ h => DensityOp.ext h⟩

/-- The embedding `ρ ↦ ρ.toOp` is continuous. -/
theorem continuous_toOp : Continuous (fun ρ : DensityOp n => ρ.toOp) :=
  isEmbedding_toOp.continuous

instance : T2Space (DensityOp n) :=
  isEmbedding_toOp.t2Space

/-- The density operators are exactly the positive semidefinite matrices of trace one. -/
theorem range_toOp :
    Set.range (fun ρ : DensityOp n => ρ.toOp) = {M : Op n | M.PosSemidef ∧ M.trace = 1} := by
  ext M
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ⟨posSemidefOp_implies_mathlib ρ.toPosSemidefOp, ρ.trace_one⟩
  · rintro ⟨hpsd, htr⟩
    exact ⟨⟨⟨⟨M, hpsd.isHermitian⟩, fun v => posSemidef_re_quadraticForm_nonneg hpsd v⟩, htr⟩, rfl⟩

end DensityOp

/-- The cone of positive semidefinite matrices is closed in the entrywise topology. -/
lemma isClosed_setOf_posSemidef : IsClosed {A : Op n | A.PosSemidef} := by
  have h_herm : IsClosed {A : Op n | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have h_dot : ∀ v : Fin n → ℂ, IsClosed {A : Op n | 0 ≤ star v ⬝ᵥ A.mulVec v} := fun v =>
    isClosed_Ici.preimage
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))
  have hrewrite : {A : Op n | A.PosSemidef} =
      {A : Op n | A.IsHermitian} ∩ ⋂ v : Fin n → ℂ, {A : Op n | 0 ≤ star v ⬝ᵥ A.mulVec v} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
  rw [hrewrite]
  exact h_herm.inter (isClosed_iInter h_dot)

/-- **Cauchy–Schwarz entry bound**: an entry of a positive semidefinite matrix is bounded by the
geometric mean of the two diagonal entries, `‖A i j‖² ≤ A i i · A j j`. -/
lemma posSemidef_entry_norm_sq_le_diag_mul {A : Op n} (hA : A.PosSemidef) (i j : Fin n) :
    ‖A i j‖ ^ 2 ≤ (A i i).re * (A j j).re := by
  let Apsd : PosSemidefOp n :=
    { toHermitianOp := ⟨A, hA.isHermitian⟩
      pos_semidef := fun v => posSemidef_re_quadraticForm_nonneg hA v }
  simpa [Apsd, Complex.normSq_eq_norm_sq] using pos_semidef_off_diag_bound Apsd i j

/-- A positive semidefinite matrix whose trace has real part at most one has every entry of norm at
most one. -/
lemma posSemidef_trace_le_one_entry_norm_le_one {A : Op n} (hA : A.PosSemidef)
    (htr : A.trace.re ≤ 1) (i j : Fin n) : ‖A i j‖ ≤ 1 := by
  have hdiag_nonneg : ∀ k : Fin n, 0 ≤ (A k k).re := fun k => psd_diag_re_nonneg A hA k
  have hdiag_le : ∀ k : Fin n, (A k k).re ≤ 1 := fun k => by
    refine le_trans ?_ htr
    rw [Matrix.trace, Complex.re_sum]
    exact Finset.single_le_sum (f := fun m => (A m m).re) (fun m _ => hdiag_nonneg m)
      (Finset.mem_univ k)
  have hsq : ‖A i j‖ ^ 2 ≤ (A i i).re * (A j j).re := posSemidef_entry_norm_sq_le_diag_mul hA i j
  have hb : (A i i).re * (A j j).re ≤ 1 :=
    (mul_le_mul (hdiag_le i) (hdiag_le j) (hdiag_nonneg j) zero_le_one).trans_eq (one_mul 1)
  nlinarith [norm_nonneg (A i j), le_trans hsq hb]

/-- Every entry of a density operator has norm at most one. -/
lemma DensityOp.entry_norm_le_one (σ : DensityOp n) (i j : Fin n) : ‖σ.toOp i j‖ ≤ 1 :=
  posSemidef_trace_le_one_entry_norm_le_one (posSemidefOp_implies_mathlib σ.toPosSemidefOp)
    (by rw [σ.trace_one, Complex.one_re]) i j

/-- **The state space is compact.** The image of `ρ ↦ ρ.toOp` is the closed set of positive
semidefinite matrices of trace one, which lies in the compact box of matrices with entries of norm
at most one. -/
instance : CompactSpace (DensityOp n) := by
  refine ⟨DensityOp.isEmbedding_toOp.isInducing.isCompact_iff.2 ?_⟩
  rw [Set.image_univ, DensityOp.range_toOp]
  have hBox : IsCompact (Set.univ.pi fun _ : Fin n =>
      Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) 1 : Set (Op n)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1
  refine hBox.of_isClosed_subset
    (isClosed_setOf_posSemidef.inter (isClosed_eq continuous_id.matrix_trace continuous_const))
    fun M hM => ?_
  simp only [Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  exact posSemidef_trace_le_one_entry_norm_le_one hM.1 (by rw [hM.2, Complex.one_re])

end Quantum.Operators
