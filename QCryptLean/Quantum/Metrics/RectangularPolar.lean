import QCryptLean.Quantum.Metrics.TraceNorm.FidelitySymm
import QCryptLean.Quantum.Metrics.TraceOpNormBound
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Math.LinearAlgebra.UnitaryExtension
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD

/-!
# Rectangular Polar Uhlmann Bounds — ket vectorization, partial traces, overlap estimates

This file proves the ket-vectorization and trace-estimate infrastructure used for the
generalized-ancilla Uhlmann upper bound

  `‖⟨ψρ | ψτ⟩‖ ≤ F(ρ, τ)`

with `ψρ, ψτ : Ket (d * a)` and `a` an arbitrary nonzero ancilla
dimension (Watrous Prop. 3.13 (i)).  The approach is the standard
rectangular polar-decomposition route:

1. **Rectangular vec representation.** A ket `ψ : Ket (d * a)` is the
   vectorization of a rectangular matrix `M : Matrix (Fin d) (Fin a) ℂ`
   via `finProdFinEquiv`.
2. **Partial trace ↔ Gram.** Under that vectorization,
   `partialTraceB (ψ * ψ.dag) = M * M.conjTranspose`.
3. **Rectangular polar.** Given `M * M.conjTranspose = ρ` with `ρ`
   positive semidefinite, write `M = √ρ · W` for some contraction
   `W : Matrix (Fin d) (Fin a) ℂ`.  The construction zero-pads `M` to a
   square `(d+a) × (d+a)` matrix and applies the square polar
   decomposition (`Quantum.Metrics.PolarUnitary.Op.exists_unitary_polar_left`);
   `W` is the top-right block of the resulting unitary.
4. **Overlap as contraction-twisted trace.**
   `(ψρ.dag * ψτ : ℂ) = Tr(Mρᴴ * Mτ) = Tr((Wτ · Wρᴴ) · √ρ · √τ)`.
5. **Hölder bound.** `‖Tr((Wτ · Wρᴴ) · √ρ · √τ)‖ ≤ ‖Wτ · Wρᴴ‖₂_op ·
   traceNorm(√ρ · √τ) ≤ traceNorm(√ρ · √τ) = F(ρ, τ)`, using
   `Quantum.Metrics.TraceOpNormBound.norm_trace_mul_le_opNorm_mul_traceNorm`
   and sub-multiplicativity of the operator norm.

The named lemmas below package this route.

## Main definitions

- `ketVecMatrix`: the rectangular vec representation of a ket.
- `ketOfVecMatrix`: the ket obtained by vectorizing a rectangular matrix.

## Main statements

- `ketVecMatrix_mul_conjTranspose_eq_partialTraceB`: partial trace as `M * Mᴴ`.
- `dag_mul_eq_trace_vecMatrix_mul`: ket overlap as `Tr(Mρᴴ · Mτ)`.
- `Math.LinearAlgebra.UnitaryExtension.exists_rectangular_polar_contraction`: rectangular polar
decomposition with a contraction factor.
- `dag_mul_eq_trace_contraction_sqrt_of_polar`: overlap rewritten using
  rectangular polar factors.
- `norm_trace_mul_le_traceNorm_of_opNorm_le_one`: trace pairing against a contraction.
- `norm_overlap_le_fidelity_of_polar_psd`: the same overlap bound for arbitrary
  positive semidefinite marginals.
- `norm_overlap_le_fidelity_of_polar`: generalized-ancilla Uhlmann overlap bound.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Quantum.Metrics.RectangularPolar

/-- Rectangular vec representation of a ket on a tensor product.

For `ψ : Ket (d * a)`, the matrix entry `ketVecMatrix ψ i j` is the
component of `ψ` at the index `finProdFinEquiv (i, j)`. -/
def ketVecMatrix {d a : ℕ} (ψ : Ket (d * a)) :
    Matrix (Fin d) (Fin a) ℂ :=
  Matrix.of fun i j => ψ.vec (finProdFinEquiv (i, j))

/-- Ket obtained by vectorizing a rectangular matrix through `finProdFinEquiv`. -/
def ketOfVecMatrix {d a : ℕ} (M : Matrix (Fin d) (Fin a) ℂ) :
    Ket (d * a) :=
  ⟨fun k => M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2⟩

/-- Entries of the rectangular vectorization are the corresponding tensor-product coordinates. -/
@[simp]
lemma ketVecMatrix_apply {d a : ℕ} (ψ : Ket (d * a)) (i : Fin d) (j : Fin a) :
    ketVecMatrix ψ i j = ψ.vec (finProdFinEquiv (i, j)) := rfl

/-- Vectorizing back from a rectangular matrix recovers the matrix. -/
@[simp]
lemma ketVecMatrix_ketOfVecMatrix {d a : ℕ} (M : Matrix (Fin d) (Fin a) ℂ) :
    ketVecMatrix (ketOfVecMatrix M) = M := by
  ext i j
  change M (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = M i j
  rw [Equiv.symm_apply_apply]

/-- The partial trace `partialTraceB (ψ * ψ.dag)` recovers `M * Mᴴ` where
`M = ketVecMatrix ψ` is the rectangular vec representation of `ψ`. -/
lemma ketVecMatrix_mul_conjTranspose_eq_partialTraceB
    {d a : ℕ} (ψ : Ket (d * a)) :
    (ketVecMatrix ψ) * (ketVecMatrix ψ).conjTranspose =
      partialTraceB (ψ * ψ.dag) := by
  ext i j
  simp [partialTraceB, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ketVecMatrix_apply, ket_mul_bra_apply, Ket.dag_vec]

/-- The bra–ket overlap of two kets on `d * a` equals the trace
`Tr(Mρᴴ · Mτ)` of the product of their rectangular vec
representations. -/
lemma dag_mul_eq_trace_vecMatrix_mul
    {d a : ℕ} (ψρ ψτ : Ket (d * a)) :
    (ψρ.dag * ψτ : ℂ) =
      ((ketVecMatrix ψρ).conjTranspose * ketVecMatrix ψτ).trace := by
  rw [bra_mul_ket_eq]
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type_right]
  simp [ketVecMatrix, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Ket.dag_vec]

/-- The ket associated to a rectangular matrix has partial trace `M * Mᴴ`. -/
lemma partialTraceB_ketOfVecMatrix
    {d a : ℕ} (M : Matrix (Fin d) (Fin a) ℂ) :
    partialTraceB ((ketOfVecMatrix M) * (ketOfVecMatrix M).dag) =
      M * M.conjTranspose := by
  rw [← ketVecMatrix_mul_conjTranspose_eq_partialTraceB (ketOfVecMatrix M)]
  simp

/-! ### Zero-padding helpers: reduce a rectangular `M : d × a` to a square `(d+a) × (d+a)`
matrix so we can apply the square polar decomposition `Op.exists_unitary_polar_left`. -/

/-- Embed `A : d × d` as the top-left block of a `(d+a) × (d+a)` square matrix,
with zeros in the other three blocks. -/
def padBlockTL (a : ℕ) {d : ℕ} (A : Op d) : Op (d + a) :=
  (Matrix.fromBlocks A (0 : Matrix (Fin d) (Fin a) ℂ)
                     (0 : Matrix (Fin a) (Fin d) ℂ)
                     (0 : Op a)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- Embed a rectangular `M : d × a` as the top-right block of a `(d+a) × (d+a)`
square matrix, with zeros in the other three blocks. -/
def padTopRight {d a : ℕ} (M : Matrix (Fin d) (Fin a) ℂ) : Op (d + a) :=
  (Matrix.fromBlocks (0 : Op d) M
                     (0 : Matrix (Fin a) (Fin d) ℂ)
                     (0 : Op a)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- Top-left block padding is multiplicative. -/
lemma padBlockTL_mul {d a : ℕ} (A B : Op d) :
    padBlockTL a A * padBlockTL a B = padBlockTL a (A * B) := by
  unfold padBlockTL
  rw [Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _,
      Matrix.fromBlocks_multiply]
  simp

/-- `padTopRight M * (padTopRight M)ᴴ = padBlockTL (M Mᴴ)`. -/
lemma padTopRight_mul_conjTranspose {d a : ℕ} (M : Matrix (Fin d) (Fin a) ℂ) :
    padTopRight M * (padTopRight M).conjTranspose =
      padBlockTL a (M * M.conjTranspose) := by
  unfold padTopRight padBlockTL
  rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose,
      Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _,
      Matrix.fromBlocks_multiply]
  simp

/-- The block-diagonal-style padding of a PSD matrix is PSD. -/
lemma padBlockTL_posSemidef {d a : ℕ} {A : Op d}
    (hA : A.PosSemidef) : (padBlockTL a A).PosSemidef := by
  unfold padBlockTL
  exact (Matrix.PosSemidef.fromBlocks_zero hA (Matrix.PosSemidef.zero)).submatrix _

/-- `CFC.sqrt` commutes with the top-left block padding (for PSD inputs). -/
lemma cfcSqrt_padBlockTL {d a : ℕ} {P : Op d}
    (hP : P.PosSemidef) :
    CFC.sqrt (padBlockTL a P) = padBlockTL a (CFC.sqrt P) := by
  refine CFC.sqrt_unique ?_ ?_
  · -- `pad √P * pad √P = pad (√P * √P) = pad P`.
    rw [padBlockTL_mul, CFC.sqrt_mul_sqrt_self P hP.nonneg]
  · -- `pad √P` is positive semidefinite because `√P` is.
    exact (padBlockTL_posSemidef (CFC.sqrt_nonneg P).posSemidef).nonneg

/-- The `(inl, inr)` block extractor of an `Op (d + a)`: top-`d`-rows × right-`a`-columns. -/
def topRightBlock {d a : ℕ} (A : Op (d + a)) : Matrix (Fin d) (Fin a) ℂ :=
  Matrix.of fun (i : Fin d) (j : Fin a) =>
    A (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))

@[simp] lemma topRightBlock_apply {d a : ℕ} (A : Op (d + a))
    (i : Fin d) (j : Fin a) :
    topRightBlock A i j = A (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) :=
  rfl

/-- Reading off the top-right block of `padTopRight M` returns `M`. -/
lemma topRightBlock_padTopRight {d a : ℕ} (M : Matrix (Fin d) (Fin a) ℂ) :
    topRightBlock (padTopRight M) = M := by
  ext i j
  unfold padTopRight
  simp [topRightBlock, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂]

/-- The top-right block of `padBlockTL S * X` is `S` times the top-right block of `X`. -/
lemma topRightBlock_padBlockTL_mul {d a : ℕ}
    (S : Op d) (X : Op (d + a)) :
    topRightBlock (padBlockTL a S * X) = S * topRightBlock X := by
  ext i j
  simp only [topRightBlock_apply, Matrix.mul_apply]
  -- Reindex the sum over `Fin (d+a)` via `finSumFinEquiv`, then split into inl/inr parts.
  rw [show (∑ k : Fin (d + a),
            padBlockTL a S (finSumFinEquiv (Sum.inl i)) k *
              X k (finSumFinEquiv (Sum.inr j)))
        = ∑ y : Fin d ⊕ Fin a,
            padBlockTL a S (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv y) *
              X (finSumFinEquiv y) (finSumFinEquiv (Sum.inr j)) from
      (finSumFinEquiv.sum_comp _).symm]
  rw [Fintype.sum_sum_type]
  -- `padBlockTL a S` is nonzero only on the `(inl, inl)` block, equal to `S`.
  have hL : ∀ i' : Fin d,
      padBlockTL a S (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl i'))
        = S i i' := by
    intro i'
    simp [padBlockTL, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁]
  have hR : ∀ j' : Fin a,
      padBlockTL a S (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j'))
        = 0 := by
    intro j'
    simp [padBlockTL, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂]
  simp only [hL, hR, zero_mul, Finset.sum_const_zero, add_zero]

/-- `‖(1 : Op n)‖ ≤ 1`: the L2 operator norm of the identity is at most one
(equal to 1 if `n ≥ 1`, equal to 0 if `n = 0`). -/
lemma l2_opNorm_one_le {n : ℕ} : ‖(1 : Op n)‖ ≤ 1 := by
  -- ‖1‖² = ‖1ᴴ * 1‖ = ‖1‖, so ‖1‖ ∈ {0, 1}.
  have h_sq : ‖(1 : Op n)‖ * ‖(1 : Op n)‖ = ‖(1 : Op n)‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Op n)
    -- h : ‖(1 : Op n)ᴴ * (1 : Op n)‖ = ‖(1 : Op n)‖ * ‖(1 : Op n)‖
    rw [show ((1 : Op n).conjTranspose) = (1 : Op n) from Matrix.conjTranspose_one,
        one_mul] at h
    exact h.symm
  have hnn : 0 ≤ ‖(1 : Op n)‖ := norm_nonneg _
  nlinarith [h_sq, hnn, sq_nonneg (‖(1 : Op n)‖ - 1)]

/-- A partial-isometry factorization helper: `W := topRightBlock U.toOp`
factors as `E1 * U.toOp * E2`, where `E1` and `E2` are 0/1 selector matrices
(row-selector and column-selector respectively). -/
private lemma topRightBlock_eq_proj_mul_unitary_mul_incl {d a : ℕ}
    (U : UnitaryOp (d + a)) :
    let E1 : Matrix (Fin d) (Fin (d + a)) ℂ :=
      Matrix.of fun (i : Fin d) (k : Fin (d + a)) =>
        if k = finSumFinEquiv (Sum.inl i) then (1 : ℂ) else 0
    let E2 : Matrix (Fin (d + a)) (Fin a) ℂ :=
      Matrix.of fun (k : Fin (d + a)) (j : Fin a) =>
        if k = finSumFinEquiv (Sum.inr j) then (1 : ℂ) else 0
    topRightBlock U.toOp = E1 * U.toOp * E2 := by
  intro E1 E2
  ext i j
  -- Expand the double matrix product `((E1 * U.toOp) * E2) i j` entry-wise:
  --   ∑ k, (∑ l, (if l = e(inl i) then 1 else 0) * U.toOp l k) * (if k = e(inr j) then 1 else 0)
  -- Reduce outer (over k) by picking k = e(inr j); then inner (over l) by l = e(inl i).
  simp only [topRightBlock_apply, Matrix.mul_apply, E1, E2, Matrix.of_apply]
  rw [Finset.sum_eq_single (finSumFinEquiv (Sum.inr j))]
  · -- Main outer case: k = e(inr j); the outer if-factor is 1.
    rw [if_pos rfl, mul_one]
    rw [Finset.sum_eq_single (finSumFinEquiv (Sum.inl i))]
    · simp
    · intro l _ hl; rw [if_neg hl]; ring
    · intro h; exact (h (Finset.mem_univ _)).elim
  · -- Outer non-singled case: k ≠ e(inr j); the outer if-factor is 0.
    intro k _ hk; rw [if_neg hk]; ring
  · intro h; exact (h (Finset.mem_univ _)).elim

/-- The first selector matrix `E1` satisfies `E1 * E1ᴴ = (1 : Op d)`. -/
private lemma E1_mul_conjTranspose_eq_one {d a : ℕ} :
    let E1 : Matrix (Fin d) (Fin (d + a)) ℂ :=
      Matrix.of fun (i : Fin d) (k : Fin (d + a)) =>
        if k = finSumFinEquiv (Sum.inl i) then (1 : ℂ) else 0
    E1 * E1.conjTranspose = (1 : Op d) := by
  intro E1
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, E1, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single (finSumFinEquiv (Sum.inl i))]
    · simp
    · intro b _ hb; rw [if_neg hb]; simp
    · intro h; exact (h (Finset.mem_univ _)).elim
  · rw [Matrix.one_apply_ne hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = finSumFinEquiv (Sum.inl i)
    · have hkj : ¬ (k = finSumFinEquiv (Sum.inl j)) := by
        intro hkj
        apply hij
        have heq : finSumFinEquiv (Sum.inl i) = finSumFinEquiv (Sum.inl j) :=
          hki.symm.trans hkj
        have := finSumFinEquiv.injective heq
        exact Sum.inl.inj this
      rw [if_pos hki, if_neg hkj]; simp
    · rw [if_neg hki]; simp

/-- The second selector matrix `E2` satisfies `E2ᴴ * E2 = (1 : Op a)`. -/
private lemma E2_conjTranspose_mul_eq_one {d a : ℕ} :
    let E2 : Matrix (Fin (d + a)) (Fin a) ℂ :=
      Matrix.of fun (k : Fin (d + a)) (j : Fin a) =>
        if k = finSumFinEquiv (Sum.inr j) then (1 : ℂ) else 0
    E2.conjTranspose * E2 = (1 : Op a) := by
  intro E2
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, E2, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single (finSumFinEquiv (Sum.inr i))]
    · simp
    · intro b _ hb; rw [if_neg hb]; simp
    · intro h; exact (h (Finset.mem_univ _)).elim
  · rw [Matrix.one_apply_ne hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = finSumFinEquiv (Sum.inr i)
    · have hkj : ¬ (k = finSumFinEquiv (Sum.inr j)) := by
        intro hkj
        apply hij
        have heq : finSumFinEquiv (Sum.inr i) = finSumFinEquiv (Sum.inr j) :=
          hki.symm.trans hkj
        have := finSumFinEquiv.injective heq
        exact Sum.inr.inj this
      rw [if_pos hki, if_neg hkj]; simp
    · rw [if_neg hki]; simp

/-- A nonnegative real whose square is at most one is itself at most one. -/
private lemma le_one_of_nonneg_of_mul_self_le_one {x : ℝ} (hx : 0 ≤ x) (h : x * x ≤ 1) :
    x ≤ 1 :=
  (mul_self_le_mul_self_iff hx zero_le_one).mpr (by rwa [mul_one])

/-- The top-right block of a unitary on `Fin (d + a)` is a contraction. -/
lemma l2_opNorm_topRightBlock_unitaryOp_le_one {d a : ℕ}
    (U : UnitaryOp (d + a)) : ‖topRightBlock U.toOp‖ ≤ 1 := by
  set E1 : Matrix (Fin d) (Fin (d + a)) ℂ :=
    Matrix.of fun (i : Fin d) (k : Fin (d + a)) =>
      if k = finSumFinEquiv (Sum.inl i) then (1 : ℂ) else 0
  set E2 : Matrix (Fin (d + a)) (Fin a) ℂ :=
    Matrix.of fun (k : Fin (d + a)) (j : Fin a) =>
      if k = finSumFinEquiv (Sum.inr j) then (1 : ℂ) else 0
  have hW_eq : topRightBlock U.toOp = E1 * U.toOp * E2 :=
    topRightBlock_eq_proj_mul_unitary_mul_incl U
  -- ‖E1‖² = ‖E1 * E1ᴴ‖ = ‖(1 : Op d)‖
  have hE1_sq : ‖E1‖ * ‖E1‖ = ‖(1 : Op d)‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self E1.conjTranspose
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h
    rw [E1_mul_conjTranspose_eq_one] at h
    exact h.symm
  -- ‖E2‖² = ‖E2ᴴ * E2‖ = ‖(1 : Op a)‖
  have hE2_sq : ‖E2‖ * ‖E2‖ = ‖(1 : Op a)‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self E2
    rw [E2_conjTranspose_mul_eq_one] at h
    exact h.symm
  -- ‖U.toOp‖² = ‖1 : Op (d+a)‖
  have hU_sq : ‖U.toOp‖ * ‖U.toOp‖ = ‖(1 : Op (d + a))‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self U.toOp
    rw [U.unitary_left] at h
    exact h.symm
  have hone_d : ‖(1 : Op d)‖ ≤ 1 := l2_opNorm_one_le
  have hone_a : ‖(1 : Op a)‖ ≤ 1 := l2_opNorm_one_le
  have hone_da : ‖(1 : Op (d + a))‖ ≤ 1 := l2_opNorm_one_le
  have hE1_nn : 0 ≤ ‖E1‖ := norm_nonneg _
  have hE2_nn : 0 ≤ ‖E2‖ := norm_nonneg _
  have hU_nn : 0 ≤ ‖U.toOp‖ := norm_nonneg _
  have hE1_le : ‖E1‖ ≤ 1 := le_one_of_nonneg_of_mul_self_le_one hE1_nn (hE1_sq.le.trans hone_d)
  have hE2_le : ‖E2‖ ≤ 1 := le_one_of_nonneg_of_mul_self_le_one hE2_nn (hE2_sq.le.trans hone_a)
  have hU_le : ‖U.toOp‖ ≤ 1 :=
    le_one_of_nonneg_of_mul_self_le_one hU_nn (hU_sq.le.trans hone_da)
  -- Submultiplicativity: ‖W‖ = ‖E1 * U * E2‖ ≤ ‖E1‖ * ‖U‖ * ‖E2‖ ≤ 1.
  calc
    ‖topRightBlock U.toOp‖ = ‖E1 * U.toOp * E2‖ := by rw [hW_eq]
    _ ≤ ‖E1 * U.toOp‖ * ‖E2‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖E1‖ * ‖U.toOp‖ * ‖E2‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ 1 := by
        have h1 : ‖E1‖ * ‖U.toOp‖ ≤ 1 := mul_le_one₀ hE1_le hU_nn hU_le
        exact mul_le_one₀ h1 hE2_nn hE2_le

/-- Trace identity for a polar factorization: if `Sρ` is Hermitian, then
`Tr((Sρ · Wρ)ᴴ · (Sτ · Wτ)) = Tr((Wτ · Wρᴴ) · (Sρ · Sτ))`. -/
lemma trace_polar_substitution {d a : ℕ}
    (Sρ Sτ : Op d) (Wρ Wτ : Matrix (Fin d) (Fin a) ℂ)
    (hSρ : Sρ.conjTranspose = Sρ) :
    ((Sρ * Wρ).conjTranspose * (Sτ * Wτ)).trace =
      ((Wτ * Wρ.conjTranspose) * (Sρ * Sτ)).trace := by
  rw [Matrix.trace_mul_comm, Matrix.conjTranspose_mul, hSρ,
      show (Sτ * Wτ) * (Wρ.conjTranspose * Sρ)
        = Sτ * (Wτ * Wρ.conjTranspose * Sρ) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- Overlap of vectorized rectangular matrices as a trace. -/
lemma ketOfVecMatrix_dag_mul_eq_trace
    {d a : ℕ} (M N : Matrix (Fin d) (Fin a) ℂ) :
    ((ketOfVecMatrix M).dag * ketOfVecMatrix N : ℂ) =
      (M.conjTranspose * N).trace := by
  simpa using dag_mul_eq_trace_vecMatrix_mul (ketOfVecMatrix M) (ketOfVecMatrix N)

/-- Overlap with one vectorized rectangular matrix as a trace. -/
lemma dag_mul_ketOfVecMatrix_eq_trace
    {d a : ℕ} (ψ : Ket (d * a)) (M : Matrix (Fin d) (Fin a) ℂ) :
    (ψ.dag * ketOfVecMatrix M : ℂ) =
      ((ketVecMatrix ψ).conjTranspose * M).trace := by
  simpa using dag_mul_eq_trace_vecMatrix_mul ψ (ketOfVecMatrix M)

/-- Rectangular polar factorizations rewrite a ket overlap as a contraction-twisted trace. -/
lemma dag_mul_eq_trace_contraction_sqrt_of_polar
    {d a : ℕ} (ψρ ψτ : Ket (d * a))
    (Sρ Sτ : Op d)
    (Wρ Wτ : Matrix (Fin d) (Fin a) ℂ)
    (hMρ : ketVecMatrix ψρ = Sρ * Wρ)
    (hMτ : ketVecMatrix ψτ = Sτ * Wτ)
    (hSρ : Sρ.conjTranspose = Sρ) :
    (ψρ.dag * ψτ : ℂ) =
      ((Wτ * Wρ.conjTranspose) * (Sρ * Sτ)).trace := by
  calc
    (ψρ.dag * ψτ : ℂ)
        = ((ketVecMatrix ψρ).conjTranspose * ketVecMatrix ψτ).trace :=
            dag_mul_eq_trace_vecMatrix_mul ψρ ψτ
    _ = (((Sρ * Wρ).conjTranspose * (Sτ * Wτ)).trace) := by
            rw [hMρ, hMτ]
    _ = ((Wτ * Wρ.conjTranspose) * (Sρ * Sτ)).trace :=
            trace_polar_substitution Sρ Sτ Wρ Wτ hSρ

/-- Trace pairing with an operator-norm contraction is bounded by the trace norm. -/
lemma norm_trace_mul_le_traceNorm_of_opNorm_le_one
    {d : ℕ} [NeZero d] (W X : Op d) (hW : ‖W‖ ≤ 1) :
    ‖(W * X).trace‖ ≤ traceNorm X := by
  have hTraceNorm_nonneg : 0 ≤ traceNorm X := by
    unfold traceNorm
    exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  calc
    ‖(W * X).trace‖ ≤ ‖W‖ * traceNorm X :=
      Quantum.Metrics.TraceOpNormBound.norm_trace_mul_le_opNorm_mul_traceNorm W X
    _ ≤ 1 * traceNorm X := mul_le_mul_of_nonneg_right hW hTraceNorm_nonneg
    _ = traceNorm X := one_mul _

/-- Rectangular-polar Uhlmann upper bound for kets whose right-factor
partial traces are arbitrary positive semidefinite marginals. -/
lemma norm_overlap_le_fidelity_of_polar_psd
    {d anc : ℕ} [NeZero d] [NeZero anc]
    (ρ σ : PosSemidefOp d)
    (ψ φ : Ket (d * anc))
    (hψ : Quantum.TensorProducts.partialTraceB (ψ * ψ.dag) = ρ.toOp)
    (hφ : Quantum.TensorProducts.partialTraceB (φ * φ.dag) = σ.toOp) :
    ‖(ψ.dag * φ : ℂ)‖ ≤ Quantum.Metrics.fidelity ρ σ := by
  let Mψ : Matrix (Fin d) (Fin anc) ℂ :=
    ketVecMatrix ψ
  let Mφ : Matrix (Fin d) (Fin anc) ℂ :=
    ketVecMatrix φ
  let Sρ : Op d := CFC.sqrt ρ.toOp
  let Sσ : Op d := CFC.sqrt σ.toOp
  have hGramψ : Mψ * Mψ.conjTranspose = ρ.toOp := by
    simpa [Mψ] using
      (ketVecMatrix_mul_conjTranspose_eq_partialTraceB ψ).trans hψ
  have hGramφ : Mφ * Mφ.conjTranspose = σ.toOp := by
    simpa [Mφ] using
      (ketVecMatrix_mul_conjTranspose_eq_partialTraceB φ).trans hφ
  obtain ⟨Wψ, hMψ_polar, hWψ_norm⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_rectangular_polar_contraction_of_gram_eq
      (M := Mψ) (A := ρ.toOp) hGramψ
  obtain ⟨Wφ, hMφ_polar, hWφ_norm⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_rectangular_polar_contraction_of_gram_eq
      (M := Mφ) (A := σ.toOp) hGramφ
  have hSρ_herm : Sρ.conjTranspose = Sρ := by
    simpa [Sρ] using Math.SpectralTheory.cfc_sqrt_conjTranspose_eq ρ.toOp
  have hOverlap :
      (ψ.dag * φ : ℂ) =
        ((Wφ * Wψ.conjTranspose) * (Sρ * Sσ)).trace := by
    exact dag_mul_eq_trace_contraction_sqrt_of_polar ψ φ Sρ Sσ Wψ Wφ
      (by simpa [Mψ, Sρ] using hMψ_polar)
      (by simpa [Mφ, Sσ] using hMφ_polar)
      hSρ_herm
  have hW_norm : ‖Wφ * Wψ.conjTranspose‖ ≤ 1 :=
    Math.LinearAlgebra.UnitaryExtension.l2_opNorm_mul_conjTranspose_le_one
      hWφ_norm hWψ_norm
  have hfid :
      Quantum.Metrics.fidelity ρ σ =
        Quantum.Metrics.traceNorm (Sρ * Sσ) := by
    simpa [Quantum.Metrics.sqrtPosSemidefOp, Sρ, Sσ] using
      Quantum.Metrics.fidelity_eq_traceNorm_sqrtProduct ρ σ
  rw [hOverlap]
  calc
    ‖(((Wφ * Wψ.conjTranspose) * (Sρ * Sσ)).trace)‖
        ≤ Quantum.Metrics.traceNorm (Sρ * Sσ) :=
          norm_trace_mul_le_traceNorm_of_opNorm_le_one
            (Wφ * Wψ.conjTranspose) (Sρ * Sσ) hW_norm
    _ = Quantum.Metrics.fidelity ρ σ := by
        rw [← hfid]

/-- Generalized-ancilla Uhlmann upper bound for density-operator marginals. -/
lemma norm_overlap_le_fidelity_of_polar
    {d a : ℕ} [NeZero d] [NeZero a] (ρ τ : DensityOp d)
    (ψρ ψτ : Ket (d * a))
    (hpuρ : partialTraceB (ψρ * ψρ.dag) = ρ.toOp)
    (hpuτ : partialTraceB (ψτ * ψτ.dag) = τ.toOp) :
    ‖(ψρ.dag * ψτ : ℂ)‖
      ≤ Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp := by
  -- A density operator is in particular a positive semidefinite operator.
  exact norm_overlap_le_fidelity_of_polar_psd ρ.toPosSemidefOp τ.toPosSemidefOp ψρ ψτ hpuρ hpuτ

end Quantum.Metrics.RectangularPolar

end -- noncomputable section
