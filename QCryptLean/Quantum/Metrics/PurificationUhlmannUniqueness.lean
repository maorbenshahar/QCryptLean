import QCryptLean.Quantum.Channels.CPTP.IdTensorRect
import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.Metrics.RectangularPolar
import QCryptLean.Quantum.Matrix.RectangularGramIsometry
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Purification Uniqueness — rectangular Uhlmann partial isometries, Schmidt-rank bound

Two purifications of the same density operator differ by a partial isometry on the
reference register.  For same-dimension purifications the partial isometry is unitary;
for different-dimension purifications it is a left-isometry (i.e.\ a rectangular matrix
`V : Matrix (Fin dimR₂) (Fin dimR₁) ℂ` satisfying `Vᴴ * V = 1`).

## Mathematical content

**Watrous, Quantum Information (2018), §2.2 Theorem 2.21 (Uhlmann's theorem).**  For any
two purifications `ψ₁ : Ket (d * dimR₁)` and `ψ₂ : Ket (d * dimR₂)` of the same density
operator `ρ : DensityOp d`, there exists a partial isometry
`V : Matrix (Fin dimR₂) (Fin dimR₁) ℂ` (satisfying `Vᴴ * V = 1` when `dimR₁ ≤ dimR₂`)
such that `ψ₂ = (1_d ⊗ V) ψ₁`.  Here `1_d ⊗ V` acts as
`(fun (i, j) => ψ₁ (i, (Vᴴ · e_j)))` in index notation.

For same-dimension purifications (`dimR₁ = dimR₂`), `V` is a full unitary, and the
result specializes to `purification_unitary_freedom_canonical` in
`PurificationFreedom.lean`.

## Main statements

- `purification_unique_up_to_partial_isometry_on_reference` — general partial-isometry form:
  any two purifications of the same density operator are related by a left-isometry on R.
- `bipartitePure_partialTraceB_rank_le_right_dim` — the left marginal of a pure
  bipartite density operator has rank at most the right-register dimension.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Operators

/-! ## Pure-state marginal helper -/

/-- The ket extracted from a pure bipartite density operator purifies its left marginal. -/
theorem DensityOp.partialTraceB_pureKetOf_ketbra {d r : ℕ} [NeZero d] [NeZero r]
    (τ : DensityOp (d * r)) (hτ : τ.IsPure) :
    Quantum.TensorProducts.partialTraceB ((τ.pureKetOf hτ) * (τ.pureKetOf hτ).dag) =
      τ.partialTraceB.toOp := by
  rw [← DensityOp.pureKetOf_spec τ hτ]
  rfl

end Quantum.Operators

namespace Quantum.Metrics

/-! ## General partial-isometry form of purification uniqueness -/

/-- Right multiplication of rectangular ket coordinates is the corresponding
reference-register action by the transposed matrix. -/
theorem ketVecMatrix_mul_to_reference_transpose_coordinates
    {d dimR₁ dimR₂ : ℕ}
    (ψ₁ : Ket (d * dimR₁)) (ψ₂ : Ket (d * dimR₂))
    (W : Matrix (Fin dimR₁) (Fin dimR₂) ℂ)
    (hψ : RectangularPolar.ketVecMatrix ψ₂ =
      RectangularPolar.ketVecMatrix ψ₁ * W) :
    ψ₂.vec = fun k =>
      ∑ (pair : Fin d × Fin dimR₁),
        ((1 : Op d) pair.1 (finProdFinEquiv.symm k).1 *
          W.transpose (finProdFinEquiv.symm k).2 pair.2) *
          ψ₁.vec (finProdFinEquiv pair) := by
  ext k
  let q := finProdFinEquiv.symm k
  have hk :=
    congrArg (fun M : Matrix (Fin d) (Fin dimR₂) ℂ => M q.1 q.2) hψ
  rw [show k = finProdFinEquiv q by exact (finProdFinEquiv.apply_symm_apply k).symm]
  simpa [RectangularPolar.ketVecMatrix, Matrix.mul_apply, Matrix.one_apply,
    Fintype.sum_prod_type, q, mul_comm, mul_left_comm, mul_assoc] using hk

/-- Convert the rectangular coefficient-matrix relation into the displayed
reference-register action used by `purification_unique_up_to_partial_isometry_on_reference`.

The matrix theorem naturally produces `W : Matrix (Fin dimR₁) (Fin dimR₂) ℂ` with
`ketVecMatrix ψ₂ = ketVecMatrix ψ₁ * W`.  The reference-side witness in the ket statement
is the un-conjugated transpose `W.transpose`. -/
theorem ketVecMatrix_mul_coisometry_to_reference_isometry_coordinates
    {d dimR₁ dimR₂ : ℕ}
    (ψ₁ : Ket (d * dimR₁)) (ψ₂ : Ket (d * dimR₂))
    (W : Matrix (Fin dimR₁) (Fin dimR₂) ℂ)
    (hW : W * Wᴴ = (1 : Op dimR₁))
    (hψ : RectangularPolar.ketVecMatrix ψ₂ =
      RectangularPolar.ketVecMatrix ψ₁ * W) :
    (W.transpose)ᴴ * W.transpose =
        (1 : Op dimR₁) ∧
      ψ₂.vec = fun k =>
        ∑ (pair : Fin d × Fin dimR₁),
          ((1 : Op d) pair.1 (finProdFinEquiv.symm k).1 *
            W.transpose (finProdFinEquiv.symm k).2 pair.2) *
            ψ₁.vec (finProdFinEquiv pair) := by
  constructor
  · rw [show (W.transpose)ᴴ * W.transpose = (W * Wᴴ).transpose by
        rw [Matrix.transpose_mul]
        congr 1,
      hW, Matrix.transpose_one]
  · exact ketVecMatrix_mul_to_reference_transpose_coordinates ψ₁ ψ₂ W hψ

/-- Purifications of the same density operator have equal rectangular row Gram matrices. -/
theorem ketVecMatrix_mul_conjTranspose_eq_of_same_partialTraceB
    {d dimR₁ dimR₂ : ℕ}
    (ρ : DensityOp d)
    (ψ₁ : Ket (d * dimR₁)) (ψ₂ : Ket (d * dimR₂))
    (hψ₁_pu : partialTraceB (ψ₁ * ψ₁.dag) = ρ.toOp)
    (hψ₂_pu : partialTraceB (ψ₂ * ψ₂.dag) = ρ.toOp) :
    RectangularPolar.ketVecMatrix ψ₁ * (RectangularPolar.ketVecMatrix ψ₁)ᴴ =
      RectangularPolar.ketVecMatrix ψ₂ * (RectangularPolar.ketVecMatrix ψ₂)ᴴ := by
  calc
    RectangularPolar.ketVecMatrix ψ₁ * (RectangularPolar.ketVecMatrix ψ₁)ᴴ =
        partialTraceB (ψ₁ * ψ₁.dag) :=
      RectangularPolar.ketVecMatrix_mul_conjTranspose_eq_partialTraceB ψ₁
    _ = ρ.toOp := hψ₁_pu
    _ = partialTraceB (ψ₂ * ψ₂.dag) := hψ₂_pu.symm
    _ = RectangularPolar.ketVecMatrix ψ₂ * (RectangularPolar.ketVecMatrix ψ₂)ᴴ :=
      (RectangularPolar.ketVecMatrix_mul_conjTranspose_eq_partialTraceB ψ₂).symm

/-- **Purification uniqueness up to partial isometry on the reference register.**

For any two normalized purifications `ψ₁ : Ket (d * dimR₁)` and
`ψ₂ : Ket (d * dimR₂)` of the same density operator `ρ : DensityOp d`
(i.e. `partialTraceB (ψ₁ * ψ₁.dag) = ρ` and `partialTraceB (ψ₂ * ψ₂.dag) = ρ`),
there exists a left-isometry `V : Matrix (Fin dimR₂) (Fin dimR₁) ℂ`
(satisfying `Vᴴ * V = 1`) such that

  `ψ₂ = (Op.tensorMixed (1 : Op d) V) * ψ₁`,

where `Op.tensorMixed (1 : Op d) V` is the mixed-dimension `(1 ⊗ V)` action.

The dimension bound `dimR₁ ≤ dimR₂` is required: a left-isometry from `ℂ^{dimR₁}`
to `ℂ^{dimR₂}` exists only when `dimR₁ ≤ dimR₂`.

**References.**
- Watrous, *The Theory of Quantum Information* (2018), §2.2 Theorem 2.21.
- Renner, *Security of QKD*, ETH PhD thesis (2005), Lemma 4.2.2.

**Reduction to same-dimension case.** When `dimR₁ = dimR₂`, the partial isometry `V`
is unitary, and the statement reduces to `purification_unitary_freedom_canonical`
(up to an identification of `Op.tensorMixed (1 : Op d) V` with
`Op.tensor (1 : Op d) W.toOp`). -/
theorem purification_unique_up_to_partial_isometry_on_reference
    {d dimR₁ dimR₂ : ℕ} [NeZero d] [NeZero dimR₁] [NeZero dimR₂]
    (ρ : DensityOp d)
    (ψ₁ : Ket (d * dimR₁)) (ψ₂ : Ket (d * dimR₂))
    (_hψ₁_norm : ψ₁.dag * ψ₁ = 1)
    (_hψ₂_norm : ψ₂.dag * ψ₂ = 1)
    (hψ₁_pu : partialTraceB (ψ₁ * ψ₁.dag) = ρ.toOp)
    (hψ₂_pu : partialTraceB (ψ₂ * ψ₂.dag) = ρ.toOp)
    (hdim : dimR₁ ≤ dimR₂) :
    ∃ V : Matrix (Fin dimR₂) (Fin dimR₁) ℂ,
      Vᴴ * V = (1 : Op dimR₁) ∧
      ψ₂.vec = fun k =>
        ∑ (pair : Fin d × Fin dimR₁),
          ((1 : Op d) pair.1 (finProdFinEquiv.symm k).1 *
            V (finProdFinEquiv.symm k).2 pair.2) * ψ₁.vec (finProdFinEquiv pair) := by
  have hgram :
      RectangularPolar.ketVecMatrix ψ₁ * (RectangularPolar.ketVecMatrix ψ₁)ᴴ =
        RectangularPolar.ketVecMatrix ψ₂ * (RectangularPolar.ketVecMatrix ψ₂)ᴴ := by
    exact ketVecMatrix_mul_conjTranspose_eq_of_same_partialTraceB
      ρ ψ₁ ψ₂ hψ₁_pu hψ₂_pu
  obtain ⟨W, hW, hψW⟩ :=
    Matrix.exists_coisometry_right_factor_of_mul_conjTranspose_eq
      (RectangularPolar.ketVecMatrix ψ₁) (RectangularPolar.ketVecMatrix ψ₂) hgram hdim
  obtain ⟨hV_iso, hV_vec⟩ :=
    ketVecMatrix_mul_coisometry_to_reference_isometry_coordinates ψ₁ ψ₂ W hW hψW
  exact ⟨W.transpose, hV_iso, hV_vec⟩

/-! ## Bipartite pure-state rank bound -/

/-- **Schmidt-rank bound for a pure bipartite density operator.**

For a pure state on `A ⊗ R`, the rank of the `A`-marginal is bounded by the
reference dimension.  In matrix form, after reshaping the pure ket into
`M : Matrix (Fin d) (Fin dimR) ℂ`, the marginal is `M * Mᴴ`, whose rank is at most
the number of columns. -/
theorem bipartitePure_partialTraceB_rank_le_right_dim
    {d dimR : ℕ} [NeZero d] [NeZero dimR]
    (τ : DensityOp (d * dimR)) (hτ : τ.IsPure) :
    Matrix.rank τ.partialTraceB.toOp ≤ dimR := by
  let ψ := τ.pureKetOf hτ
  have h_marginal :
      τ.partialTraceB.toOp =
        RectangularPolar.ketVecMatrix ψ * (RectangularPolar.ketVecMatrix ψ)ᴴ := by
    rw [← Quantum.Operators.DensityOp.partialTraceB_pureKetOf_ketbra τ hτ]
    exact (RectangularPolar.ketVecMatrix_mul_conjTranspose_eq_partialTraceB ψ).symm
  rw [h_marginal, Matrix.rank_self_mul_conjTranspose]
  exact Matrix.rank_le_width (RectangularPolar.ketVecMatrix ψ)

/-- Two pure states with the same system marginal are related by an isometry
on the reference, in operator form. -/
lemma exists_isometry_eq_idTensorRect_conj_of_partialTraceB_eq {a r s : ℕ}
    [NeZero a] [NeZero r] [NeZero s]
    (τ : DensityOp (a * r)) (ψ : DensityOp (a * s))
    (hτ : τ.IsPure) (hψ : ψ.IsPure)
    (hmarg : ψ.partialTraceB = τ.partialTraceB) (hrs : r ≤ s) :
    ∃ W : Matrix (Fin s) (Fin r) ℂ,
      Wᴴ * W = 1 ∧
      ψ.toOp = idTensorRectMatrix a s r W * τ.toOp * (idTensorRectMatrix a s r W)ᴴ := by
  obtain ⟨W, hW, hvec⟩ :=
    Quantum.Metrics.purification_unique_up_to_partial_isometry_on_reference
      τ.partialTraceB (τ.pureKetOf hτ) (ψ.pureKetOf hψ)
      (DensityOp.pureKetOf_normalized τ hτ) (DensityOp.pureKetOf_normalized ψ hψ)
      (by rw [DensityOp.partialTraceB_pureKetOf_ketbra])
      (by rw [DensityOp.partialTraceB_pureKetOf_ketbra, hmarg]) hrs
  refine ⟨W, hW, ?_⟩
  have hv : (ψ.pureKetOf hψ).vec =
      (idTensorRectMatrix a s r W).mulVec (τ.pureKetOf hτ).vec := by
    rw [hvec]
    funext k
    simp only [Matrix.mulVec, dotProduct]
    rw [← Equiv.sum_comp finProdFinEquiv]
    apply Finset.sum_congr rfl
    intro p _
    simp only [idTensorRectMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, Equiv.symm_apply_apply, Matrix.one_apply]
    simp only [eq_comm]
  rw [DensityOp.pureKetOf_spec ψ hψ, DensityOp.pureKetOf_spec τ hτ,
    Quantum.Operators.ket_mul_dag_eq_vecMulVec,
    Quantum.Operators.ket_mul_dag_eq_vecMulVec,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec, hv]

end Quantum.Metrics

end -- noncomputable section
