import QCryptLean.Quantum.TensorProducts.ProjectiveConditioning
import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized

/-!
# Helper Lemmas for Renner `lem:disttracebound`

Small linear-algebra facts isolated from
`QCryptLean/InfoTheory/SmoothMinEntropy/Renner/DistTraceBound.lean`
to keep that file's main proof short and locally inspectable.

The main file proves
`traceNorm (ρ.toOp - P * ρ.toOp * P) ≤
   2 * Real.sqrt (ρ.trace * (ρ.trace - (P * ρ.toOp * P).trace.re))`
for a sub-density operator `ρ` and a Hermitian projector `P`.

This helper module collects three families of facts used at three different
points of that proof:

* (H1) `Quantum.TensorProducts.trace_re_projector_sandwich_le`:
  the radicand `ρ.trace - tr(PρP)` is non-negative — i.e. a Hermitian
  projector sandwich does not increase the real trace of a PSD operator.
  This is a direct rewrap of
  `Quantum.TensorProducts.trace_re_projector_sandwich_le`, packaged for
  consumption by the `SubDensityOp` API used in the main theorem.

* (H2) `traceNorm_rank_one_eq`:
  the Schatten-1 norm of a rank-one outer product `|u⟩⟨v|`
  (encoded as `Matrix.vecMulVec u (star v)`) equals `‖u‖ * ‖v‖`.
  Used by the pure base case of Renner thesis lines 10054–10080,
  where the operator `ρ - PρP` is a sum of two rank-one outer products
  and one applies the triangle inequality term-wise.

* (H3) `traceNorm_subDensityOp_sub_projector_sandwich_nonneg_radicand`:
  a small wrapper combining (H1) and `SubDensityOp.trace_nonneg` to give
  `0 ≤ ρ.trace * (ρ.trace - (P * ρ.toOp * P).trace.re)`,
  the non-negativity of the argument to `Real.sqrt` that appears on the
  right-hand side of the main theorem.

The full base case (Strategy B identity, spectral expansion, Cauchy–Schwarz)
is **not** in this file — those steps will be added in subsequent helper
modules.
-/

open Quantum.Operators Quantum.Metrics Quantum.TensorProducts Matrix
open scoped ComplexOrder BigOperators

noncomputable section

namespace InfoTheory.SmoothMinEntropy.DistTraceBoundHelpers

/-! ## (H1) Projector sandwich does not increase the real trace -/

/-- **(H1, SubDensityOp form)**. Direct corollary of
`Quantum.TensorProducts.trace_re_projector_sandwich_le`
for a sub-density operator: `(P * ρ.toOp * P).trace.re ≤ ρ.trace`. -/
lemma tr_projector_sandwich_le_subDensityOp_trace {n : ℕ}
    (ρ : SubDensityOp n) (P : Op n)
    (hP_idem : P * P = P) (hP_herm : P† = P) :
    (P * ρ.toOp * P).trace.re ≤ ρ.trace := by
  have hM_psd : ρ.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have h := Quantum.TensorProducts.trace_re_projector_sandwich_le (M := ρ.toOp) hP_idem hP_herm
      hM_psd
  -- `ρ.trace = ρ.toOp.trace.re` by definition of `SubDensityOp.trace`.
  change (P * ρ.toOp * P).trace.re ≤ ρ.toOp.trace.re
  exact h

/-- The trace deficit `ρ.trace - tr(PρP)` is non-negative. -/
lemma subDensityOp_trace_sub_projector_sandwich_re_nonneg {n : ℕ}
    (ρ : SubDensityOp n) (P : Op n)
    (hP_idem : P * P = P) (hP_herm : P† = P) :
    0 ≤ ρ.trace - (P * ρ.toOp * P).trace.re :=
  sub_nonneg.mpr
    (tr_projector_sandwich_le_subDensityOp_trace ρ P hP_idem hP_herm)

/-! ## (H2) Trace norm of a rank-one outer product

For vectors `u v : Fin n → ℂ`, `Matrix.vecMulVec u (star v)` is the rank-one
matrix `|u⟩⟨v|` (entry `(i,j)` is `u i * star (v j)`).

The standard fact `‖|u⟩⟨v|‖₁ = ‖u‖ * ‖v‖` is needed for the pure base case
of the main theorem. The proof goes by computing
`(uv*)†(uv*) = ‖v‖² · uu*` and then noting that `uu*` has unique non-zero
eigenvalue `‖u‖²`, so `(uv*)†(uv*)` has unique non-zero eigenvalue
`‖u‖² ‖v‖²`. The trace norm is then `Real.sqrt (‖u‖² ‖v‖²) = ‖u‖ * ‖v‖`.

The full eigenvalue computation is deferred and tracked as a `sorry`.
The statement is the real mathematical statement and is referenced by name. -/

/-! ### (H2, sub-helpers) -/

/-- **(H2, sub-helper L1)** The complex-valued dot product `star u ⬝ᵥ u`
equals the squared Euclidean norm of `u`, viewed as a complex number with
zero imaginary part. -/
lemma dotProduct_star_self_eq_normSq_complex_ofReal {n : ℕ}
    (u : Fin n → ℂ) :
    ((star u) ⬝ᵥ u : ℂ) =
      ((‖(EuclideanSpace.equiv (Fin n) ℂ).symm u‖ ^ 2 : ℝ) : ℂ) := by
  -- Step 1: ‖u‖² as a sum of pointwise squared norms.
  have h_sq : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm u‖ ^ 2 =
      ∑ i, ‖u i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    rfl
  -- Step 2: rewrite the dot product as a sum of `star (u i) * u i`.
  change ∑ i, star (u i) * u i = _
  rw [h_sq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- `star (u i) * u i = ↑‖u i‖²` by `mul_conj` + `sq_norm`.
  rw [Complex.sq_norm, mul_comm]
  exact Complex.mul_conj (u i)

/-- **(H2, sub-helper)**, twin of `dotProduct_star_self_eq_normSq_complex_ofReal`
with the order swapped. -/
lemma dotProduct_self_star_eq_normSq_complex_ofReal {n : ℕ}
    (v : Fin n → ℂ) :
    (v ⬝ᵥ (star v) : ℂ) =
      ((‖(EuclideanSpace.equiv (Fin n) ℂ).symm v‖ ^ 2 : ℝ) : ℂ) := by
  have h := dotProduct_star_self_eq_normSq_complex_ofReal v
  -- `v ⬝ᵥ star v = star v ⬝ᵥ v` by entrywise commutativity in ℂ.
  have h_swap : (v ⬝ᵥ (star v) : ℂ) = ((star v) ⬝ᵥ v : ℂ) := by
    change (∑ i, v i * star (v i)) = ∑ i, star (v i) * v i
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [h_swap, h]

/-- **(H2, sub-helper L2)** Algebraic identity:
`(vecMulVec u (star v))† * vecMulVec u (star v)
   = (star u ⬝ᵥ u : ℂ) • vecMulVec v (star v)`. -/
lemma conjTranspose_vecMulVec_mul_vecMulVec_eq {n : ℕ}
    (u v : Fin n → ℂ) :
    (Matrix.vecMulVec u (star v))ᴴ * Matrix.vecMulVec u (star v) =
      ((star u) ⬝ᵥ u : ℂ) • Matrix.vecMulVec v (star v) := by
  rw [Matrix.conjTranspose_vecMulVec, star_star,
      Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]

/-- **(H2, sub-helper L3a)** Arithmetic fact: for a nonneg sequence
indexed by a finite type, if at most one entry is nonzero, the sum of the
square roots equals the square root of the sum. -/
private lemma sum_sqrt_eq_sqrt_sum_of_card_supp_le_one
    {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h_supp : Fintype.card {i // f i ≠ 0} ≤ 1) :
    ∑ i, Real.sqrt (f i) = Real.sqrt (∑ i, f i) := by
  classical
  have hsub : Subsingleton {i // f i ≠ 0} :=
    Fintype.card_le_one_iff_subsingleton.mp h_supp
  by_cases hall : ∃ j, f j ≠ 0
  · obtain ⟨j, hj⟩ := hall
    have h_others : ∀ i, f i ≠ 0 → i = j := by
      intro i hi
      have heq : (⟨i, hi⟩ : {k // f k ≠ 0}) = ⟨j, hj⟩ := Subsingleton.elim _ _
      exact (Subtype.mk.injEq _ _ _ _).mp heq
    have h_sum_sqrt : ∑ i, Real.sqrt (f i) = Real.sqrt (f j) := by
      refine Finset.sum_eq_single j (fun i _ hij => ?_)
        (fun h => absurd (Finset.mem_univ j) h)
      have hi0 : f i = 0 := by
        by_contra hfi
        exact hij (h_others i hfi)
      rw [hi0, Real.sqrt_zero]
    have h_sum : ∑ i, f i = f j := by
      refine Finset.sum_eq_single j (fun i _ hij => ?_)
        (fun h => absurd (Finset.mem_univ j) h)
      by_contra hfi
      exact hij (h_others i hfi)
    rw [h_sum_sqrt, h_sum]
  · push Not at hall
    simp [hall]

/-- **(H2, sub-helper L3)** For any matrix `A` such that `Aᴴ * A` has
rank ≤ 1, the trace norm of `A` equals
`Real.sqrt ((Aᴴ * A).trace.re)`.

This is the spectral collapse step: `Aᴴ * A` is automatically PSD, and
PSD plus rank ≤ 1 gives at most one nonzero eigenvalue, so the
sum-of-square-roots in `traceNorm` collapses to a single square root. -/
lemma traceNorm_eq_sqrt_re_trace_of_rank_le_one
    {n : ℕ} [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ}
    (h_rank : (Aᴴ * A).rank ≤ 1) :
    traceNorm A = Real.sqrt (Aᴴ * A).trace.re := by
  classical
  -- `Aᴴ * A` is PSD and Hermitian.
  have hPSD : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hAA : (Aᴴ * A).IsHermitian := hPSD.isHermitian
  -- At most one nonzero eigenvalue (from rank ≤ 1).
  have h_supp : Fintype.card {i // hAA.eigenvalues i ≠ 0} ≤ 1 := by
    rw [← Matrix.IsHermitian.rank_eq_card_non_zero_eigs hAA]
    exact h_rank
  -- Apply the arithmetic L3a.
  have h_arith :
      ∑ i, Real.sqrt (hAA.eigenvalues i) =
        Real.sqrt (∑ i, hAA.eigenvalues i) :=
    sum_sqrt_eq_sqrt_sum_of_card_supp_le_one _ h_supp
  -- Identify ∑ eigᵢ with (Aᴴ * A).trace.re.
  have h_trace_eq :
      ((∑ i, hAA.eigenvalues i : ℝ) : ℂ) = (Aᴴ * A).trace := by
    rw [hAA.trace_eq_sum_eigenvalues]
    push_cast; rfl
  have h_trace_re : (∑ i, hAA.eigenvalues i : ℝ) = (Aᴴ * A).trace.re := by
    have := congr_arg Complex.re h_trace_eq
    simpa using this
  -- Unfold `traceNorm`.
  change ∑ i, Real.sqrt (hAA.eigenvalues i) = _
  rw [h_arith, h_trace_re]

/-- **(H2)** Schatten-1 norm of the rank-one operator `|u⟩⟨v|`. -/
lemma traceNorm_rank_one_eq {n : ℕ} [NeZero n] (u v : Fin n → ℂ) :
    traceNorm (Matrix.vecMulVec u (star v)) =
      ‖(EuclideanSpace.equiv (Fin n) ℂ).symm u‖ *
        ‖(EuclideanSpace.equiv (Fin n) ℂ).symm v‖ := by
  set A := Matrix.vecMulVec u (star v) with hA_def
  -- The product `Aᴴ * A` equals the real-scalar multiple of `vecMulVec v (star v)`.
  have h_AA : Aᴴ * A =
      ((star u) ⬝ᵥ u : ℂ) • Matrix.vecMulVec v (star v) :=
    conjTranspose_vecMulVec_mul_vecMulVec_eq u v
  -- Rank ≤ 1 because `A` itself has rank ≤ 1.
  have h_rank : (Aᴴ * A).rank ≤ 1 :=
    (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_vecMulVec_le _ _)
  -- Use the spectral collapse.
  rw [traceNorm_eq_sqrt_re_trace_of_rank_le_one h_rank]
  -- Identify the trace of `Aᴴ * A` with `‖u‖² ‖v‖²`.
  have h_uu : ((star u) ⬝ᵥ u : ℂ) =
      ((‖(EuclideanSpace.equiv (Fin n) ℂ).symm u‖ ^ 2 : ℝ) : ℂ) :=
    dotProduct_star_self_eq_normSq_complex_ofReal u
  have h_vv : (v ⬝ᵥ (star v) : ℂ) =
      ((‖(EuclideanSpace.equiv (Fin n) ℂ).symm v‖ ^ 2 : ℝ) : ℂ) :=
    dotProduct_self_star_eq_normSq_complex_ofReal v
  have h_trace_calc : (Aᴴ * A).trace =
      ((‖(EuclideanSpace.equiv (Fin n) ℂ).symm u‖ ^ 2 : ℝ) : ℂ) *
        ((‖(EuclideanSpace.equiv (Fin n) ℂ).symm v‖ ^ 2 : ℝ) : ℂ) := by
    rw [h_AA, Matrix.trace_smul, Matrix.trace_vecMulVec, h_uu, h_vv]
    rfl
  rw [h_trace_calc]
  -- Take real part and simplify the square root.
  set a : ℝ := ‖(EuclideanSpace.equiv (Fin n) ℂ).symm u‖
  set b : ℝ := ‖(EuclideanSpace.equiv (Fin n) ℂ).symm v‖
  have ha_nn : 0 ≤ a := norm_nonneg _
  have hb_nn : 0 ≤ b := norm_nonneg _
  have h_re :
      (((a ^ 2 : ℝ) : ℂ) * ((b ^ 2 : ℝ) : ℂ)).re = a ^ 2 * b ^ 2 := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h_re,
      show a ^ 2 * b ^ 2 = (a * b) ^ 2 from by ring,
      Real.sqrt_sq (mul_nonneg ha_nn hb_nn)]

/-! ## (H4) Rank-1 splitting identity

For any matrices `M P`, regardless of whether `P` is idempotent, the operator
`M - P * M * P` admits the decomposition
`(1 - P) * M + P * M * (1 - P)`. (The `1 - P` factor on the *left* of the first
term and on the *right* of the second is what makes both pieces rank-one when
`M` is rank-one — see (H5).)
-/

/-- **(H4)** Algebraic identity: for any `M P : Op n`,
`M - P * M * P = (1 - P) * M + P * M * (1 - P)`.

The right-hand side displays the operator as the sum of two pieces, each a
projector-applied-on-one-side of `M`. This is the algebraic input to the
pure base-case trace-norm bound in (H5). -/
lemma op_sub_projector_sandwich_eq_rank_one_split {n : ℕ} (M P : Op n) :
    M - P * M * P = (1 - P) * M + P * M * (1 - P) := by
  noncomm_ring

/-! ## (H5) Pure base-case trace-norm bound

For a unit vector `φ : Fin n → ℂ` and a Hermitian projector `P`, the
trace-norm of the rank-2 difference
`|φ⟩⟨φ| - P|φ⟩⟨φ|P` is bounded by `2 √(1 - ⟨φ|P|φ⟩)`.

The proof uses (H4) to split the difference into two rank-1 outer products,
the trace-norm triangle inequality, and (H2) to compute each rank-1 factor.
The remaining real-analysis facts (relating `‖Pφ‖² ` and `‖(1-P)φ‖²` to the
quadratic form `⟨φ|P|φ⟩`) are extracted as their own named sub-helpers below.
-/

/-- **(H5, sub-helper)**: for a Hermitian idempotent projector `P` and any
`φ : Fin n → ℂ`, the squared Euclidean norm of `P φ` equals the real
quadratic form `(quadraticForm P φ).re`. -/
lemma norm_projector_mulVec_sq_eq_quadraticForm
    {n : ℕ} {P : Op n} (hP_idem : P * P = P) (hP_herm : P† = P)
    (φ : Fin n → ℂ) :
    ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (P.mulVec φ)‖ ^ 2 =
      (quadraticForm P φ).re := by
  -- Step 1: the squared Euclidean norm equals the sum of pointwise squared norms.
  have h1 : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (P.mulVec φ)‖ ^ 2 =
      ∑ i, ‖(P.mulVec φ) i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    rfl
  rw [h1]
  -- Step 2: each pointwise squared norm is the real part of `star z * z`.
  have h2 : ∀ z : ℂ, ‖z‖ ^ 2 = (star z * z).re := by
    intro z
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re]
  -- Step 3: rewrite the sum as the real part of the dot product.
  have h3 : (∑ i, ‖(P.mulVec φ) i‖ ^ 2 : ℝ) =
      ((star (P.mulVec φ)) ⬝ᵥ (P.mulVec φ)).re := by
    simp_rw [h2]
    rw [show ((star (P.mulVec φ)) ⬝ᵥ (P.mulVec φ)) =
            ∑ i, star ((P.mulVec φ) i) * (P.mulVec φ) i from rfl]
    rw [Complex.re_sum]
  rw [h3]
  -- Step 4: use `star (P φ) = vecMul (star φ) P†` and the dot-product/mulVec
  -- conversion to expose `(P† * P)` acting on `φ`, then collapse with the
  -- idempotent and Hermitian hypotheses.
  rw [Matrix.star_mulVec, hP_herm]
  rw [show Matrix.vecMul (star φ) P ⬝ᵥ (P.mulVec φ) =
          (star φ) ⬝ᵥ ((P * P).mulVec φ) by
        rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]]
  rw [hP_idem]
  rfl

/-- **(H5, sub-helper)**: for a unit vector `φ`, the real part of the
self quadratic form `star φ ⬝ᵥ φ` equals 1. Equivalently, the
Euclidean norm of `φ` is 1. -/
lemma quadraticForm_one_re_of_unit
    {n : ℕ} (φ : Fin n → ℂ)
    (hφ : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm φ‖ = 1) :
    (quadraticForm (1 : Op n) φ).re = 1 := by
  -- Apply the H5 projector-norm identity with `P = 1`.
  have h_idem : (1 : Op n) * 1 = 1 := one_mul 1
  have h_herm : (1 : Op n)† = 1 := Matrix.conjTranspose_one
  have h := norm_projector_mulVec_sq_eq_quadraticForm h_idem h_herm φ
  rw [Matrix.one_mulVec, hφ] at h
  -- `‖.‖^2 = 1^2 = 1`
  simpa using h.symm

/-- **(H5, sub-helper)**: for a Hermitian idempotent projector `P` and a
unit vector `φ`, the squared Euclidean norm of `(1-P)φ` equals
`1 - ⟨φ|P|φ⟩`. -/
lemma norm_complement_mulVec_sq_eq_one_sub_quadraticForm
    {n : ℕ} {P : Op n} (hP_idem : P * P = P) (hP_herm : P† = P)
    (φ : Fin n → ℂ)
    (hφ : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm φ‖ = 1) :
    ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((1 - P).mulVec φ)‖ ^ 2 =
      1 - (quadraticForm P φ).re := by
  -- `1 - P` is also Hermitian and idempotent.
  have h_idem' : (1 - P) * (1 - P) = 1 - P :=
    Quantum.TensorProducts.projector_complement_idempotent hP_idem
  have h_herm' : Matrix.conjTranspose (1 - P) = 1 - P :=
    Quantum.TensorProducts.projector_complement_hermitian hP_herm
  -- Apply the projector identity to `1 - P`.
  rw [norm_projector_mulVec_sq_eq_quadraticForm h_idem' h_herm' φ]
  -- Show: `(quadraticForm (1-P) φ).re = 1 - (quadraticForm P φ).re`.
  have h_split : quadraticForm (1 - P) φ =
      quadraticForm (1 : Op n) φ - quadraticForm P φ := by
    unfold quadraticForm
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [h_split, Complex.sub_re, quadraticForm_one_re_of_unit φ hφ]

/-- **(H5, sub-helper)**: for a Hermitian idempotent projector `P` and a
unit vector `φ`, `‖Pφ‖ ≤ 1`. -/
lemma norm_projector_mulVec_le_one_of_unit
    {n : ℕ} {P : Op n} (hP_idem : P * P = P) (hP_herm : P† = P)
    (φ : Fin n → ℂ)
    (hφ : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm φ‖ = 1) :
    ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (P.mulVec φ)‖ ≤ 1 := by
  -- `‖Pφ‖² = ⟨φ|P|φ⟩.re` and `‖(1-P)φ‖² = 1 - ⟨φ|P|φ⟩.re ≥ 0`, so `‖Pφ‖² ≤ 1`.
  have h_proj := norm_projector_mulVec_sq_eq_quadraticForm hP_idem hP_herm φ
  have h_compl := norm_complement_mulVec_sq_eq_one_sub_quadraticForm
    hP_idem hP_herm φ hφ
  have h_compl_nn : 0 ≤
      ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((1 - P).mulVec φ)‖ ^ 2 :=
    sq_nonneg _
  -- Combine: ‖Pφ‖² ≤ 1.
  have h_le : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (P.mulVec φ)‖ ^ 2 ≤ 1 := by
    rw [h_proj]
    linarith
  -- Recover the linear bound from the squared bound.
  have h_nn : 0 ≤ ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (P.mulVec φ)‖ :=
    norm_nonneg _
  nlinarith [h_le, h_nn]

/-- **(H5, sub-helper)**: nonnegativity of the radicand `1 - ⟨φ|P|φ⟩` for the
pure base case, proved as a side-product of
`norm_complement_mulVec_sq_eq_one_sub_quadraticForm`. -/
lemma one_sub_quadraticForm_nonneg
    {n : ℕ} {P : Op n} (hP_idem : P * P = P) (hP_herm : P† = P)
    (φ : Fin n → ℂ)
    (hφ : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm φ‖ = 1) :
    0 ≤ 1 - (quadraticForm P φ).re := by
  -- The squared norm of `(1 - P).mulVec φ` is `1 - ⟨φ|P|φ⟩` and squared norms
  -- are nonnegative.
  have h := norm_complement_mulVec_sq_eq_one_sub_quadraticForm hP_idem hP_herm φ hφ
  have hsq : 0 ≤ ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((1 - P).mulVec φ)‖ ^ 2 :=
    sq_nonneg _
  linarith

/-- **(H5)** Pure base-case trace-norm bound.

For a unit vector `φ : Fin n → ℂ` and a Hermitian idempotent projector
`P : Op n`,
`traceNorm (|φ⟩⟨φ| - P|φ⟩⟨φ|P) ≤ 2 √(1 - ⟨φ|P|φ⟩)`.

The proof uses
* `op_sub_projector_sandwich_eq_rank_one_split` (H4) to split the operator,
* `Quantum.Metrics.traceNorm_add_le` to apply the triangle inequality,
* `traceNorm_rank_one_eq` (H2) to evaluate each rank-1 trace norm,
* the `norm_*_mulVec_*_quadraticForm` sub-helpers above.

The bookkeeping that combines these into the final `2 √(1 - ⟨φ|P|φ⟩)` bound
is the residual `sorry` of this round; the named sub-steps are all isolated. -/
theorem traceNorm_pure_base_case
    {n : ℕ} [NeZero n] {P : Op n}
    (hP_idem : P * P = P) (hP_herm : P† = P)
    (φ : Fin n → ℂ)
    (hφ : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm φ‖ = 1) :
    traceNorm
        (Matrix.vecMulVec φ (star φ) - P * Matrix.vecMulVec φ (star φ) * P) ≤
      2 * Real.sqrt (1 - (quadraticForm P φ).re) := by
  -- Step 1: Algebraic split via (H4).
  rw [op_sub_projector_sandwich_eq_rank_one_split]
  -- Step 2: Rewrite each summand as a single `vecMulVec`.
  have h_herm' : Matrix.conjTranspose ((1 : Op n) - P) = 1 - P :=
    Quantum.TensorProducts.projector_complement_hermitian hP_herm
  have h_vecMul :
      Matrix.vecMul (star φ) ((1 : Op n) - P) = star ((1 - P).mulVec φ) := by
    rw [Matrix.star_mulVec, h_herm']
  rw [Matrix.mul_vecMulVec, mul_assoc, Matrix.vecMulVec_mul,
      Matrix.mul_vecMulVec, h_vecMul]
  -- Step 3: Triangle inequality + rank-one trace-norm evaluations.
  have h_tri := Quantum.Metrics.traceNorm_add_le
    (Matrix.vecMulVec ((1 - P).mulVec φ) (star φ))
    (Matrix.vecMulVec (P.mulVec φ) (star ((1 - P).mulVec φ)))
  rw [traceNorm_rank_one_eq ((1 - P).mulVec φ) φ,
      traceNorm_rank_one_eq (P.mulVec φ) ((1 - P).mulVec φ)] at h_tri
  refine le_trans h_tri ?_
  -- Step 4: scalar inequality.
  -- Drop ‖φ‖ = 1 on the first summand.
  rw [hφ, mul_one]
  -- Identify ‖(1-P)φ‖ with √(1 - ⟨φ|P|φ⟩).
  have h_sq :=
    norm_complement_mulVec_sq_eq_one_sub_quadraticForm hP_idem hP_herm φ hφ
  have h_norm_compl_nn :
      0 ≤ ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((1 - P).mulVec φ)‖ :=
    norm_nonneg _
  have h_compl_eq :
      ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((1 - P).mulVec φ)‖ =
        Real.sqrt (1 - (quadraticForm P φ).re) := by
    rw [← h_sq, Real.sqrt_sq h_norm_compl_nn]
  -- ‖Pφ‖ ≤ 1 ⇒ 1 + ‖Pφ‖ ≤ 2.
  have h_proj_le :=
    norm_projector_mulVec_le_one_of_unit hP_idem hP_herm φ hφ
  have h_sqrt_nn :
      0 ≤ Real.sqrt (1 - (quadraticForm P φ).re) := Real.sqrt_nonneg _
  calc ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((1 - P).mulVec φ)‖ +
          ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (P.mulVec φ)‖ *
            ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((1 - P).mulVec φ)‖
        = (1 + ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (P.mulVec φ)‖) *
            ‖(EuclideanSpace.equiv (Fin n) ℂ).symm ((1 - P).mulVec φ)‖ := by ring
      _ = (1 + ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (P.mulVec φ)‖) *
            Real.sqrt (1 - (quadraticForm P φ).re) := by rw [h_compl_eq]
      _ ≤ 2 * Real.sqrt (1 - (quadraticForm P φ).re) :=
          mul_le_mul_of_nonneg_right (by linarith) h_sqrt_nn

/-! ## (H3) Non-negativity of the radicand in the main theorem -/

/-- **(H3)** Non-negativity of the argument of `Real.sqrt` that appears on
the right-hand side of `traceNorm_sub_projector_sandwich_le`. -/
lemma traceNorm_subDensityOp_sub_projector_sandwich_nonneg_radicand
    {n : ℕ} (ρ : SubDensityOp n) (P : Op n)
    (hP_idem : P * P = P) (hP_herm : P† = P) :
    0 ≤ ρ.trace * (ρ.trace - (P * ρ.toOp * P).trace.re) :=
  mul_nonneg ρ.trace_nonneg
    (subDensityOp_trace_sub_projector_sandwich_re_nonneg
      ρ P hP_idem hP_herm)

end InfoTheory.SmoothMinEntropy.DistTraceBoundHelpers

end -- noncomputable section
