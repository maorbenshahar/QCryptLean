import QCryptLean.Quantum.Operators.OrthFamilyInvSqrt

/-!
# The general-`A` readout of `σ^{−1/2}` for a regularised orthogonal family

`OrthFamilyInvSqrt.lean` reads off `Re Tr[σ^{−1/2}·A]` for a **rank-one** `A = |χ⟩⟨χ|`.  The
operator this is applied to is not rank one — an accepting marginal block is block-diagonal over
several orbits, one rank-one block each, so its rank is the number of realised blocks and there is
no vector `χ`.  This file supplies the general-`A` analogue, over the same interface: same family
`u`, weights `α`, norms `r`, regulariser `c`, and the same `horth`/`hnorm`/`hr` hypothesis shapes,
so it composes with `orthFamilyInvSqrt_sq_mul_regularized` and
`posDef_inverseSqrt_eq_orthFamilyInvSqrt` without adapters.

## Main statements

* `one_sub_orthFamilyProj_mul_eq_zero_of_cols` — the columnwise span hypothesis `P *ᵥ A_{·j} =
A_{·j}`
  is the matrix hypothesis `(𝟙 − P)·A = 0`.  (Producers of the span condition work column by column;
  the readout consumes the matrix form.)  `…_of_cols_comp` is the same through a surjective
  reindexing of the column index, for a producer stated in a structured (e.g. tensor) frame.
* `re_trace_inverseSqrt_mul_of_mem_span` — **the general-`A` eigenform**:
  `Re Tr[σ^{−1/2}·A] = ∑_i (α_i r_i + c)^{−1/2}·r_i^{−1}·Re⟨u_i, A u_i⟩` whenever `(𝟙 − P)·A = 0`.
* `re_dotProduct_mulVec_re_nonneg` — a positive semidefinite `A` has nonnegative diagonal
  quadratic form, the one side condition the bound below needs.
* `re_trace_inverseSqrt_mul_le` — **the general-`A` upper bound**, the analogue of
  `re_trace_inverseSqrt_mul_vecMulVec_le`: at `α = (1 − γ)·λ` the regularised readout is at most
  `(1 − γ)^{−1/2}` times the *unregularised* one, which carries no regularisation parameter.

## Relation to the rank-one file

Both statements specialise to their `OrthFamilyInvSqrt.lean` siblings at `A = |χ⟩⟨χ|`, where
`⟨u_i, A u_i⟩ = |⟨u_i, χ⟩|²` and `(𝟙 − P)·|χ⟩⟨χ| = 0` is `P·χ = χ`.  Nothing in that file is
edited or re-proved here.

## Relation to the diagonalising-unitary eigenform

The eigenform route is general in `A` but assumes a **unitary `W` that
diagonalises `σ` completely** (`W·σ·Wᴴ = diagonal d`, `d k > 0` for every `k`), and its readout runs
over the full index set of the rotated matrix.  Here no such unitary exists: the family need not
span, so a full eigenbasis would need a `Classical.choose`d completion of each orbit.  The
regulariser `c·𝟙` supplies the missing eigenvalue on the complement, the sum runs only over the
family, and the span hypothesis `(𝟙 − P)·A = 0` is exactly what deletes the complement's
`c^{−1/2}` contribution.

## Sources

Uniqueness of the positive semidefinite square root: Bhatia, *Matrix Analysis*, Thm V.1.9 — used
only through the already-proved `posDef_inverseSqrt_eq_orthFamilyInvSqrt`.  No operator
monotonicity anywhere.  For an off-span operator `A`, the complementary contribution is
`c^{−1/2}·Tr[(𝟙−P)A]`.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Operators

variable {ι : Type*} [Fintype ι] {N : ℕ}

section Family

variable {u : ι → (Fin N → ℂ)} {r α : ι → ℝ}

/-- **The columnwise span condition is the matrix span condition.**

`P *ᵥ A_{·j} = A_{·j}` for every column index `j` is `(𝟙 − P)·A = 0`.  Producers of the span
condition (which read a matrix entry at a fixed second index) give the left-hand form; the trace
readout consumes the right-hand one. -/
lemma one_sub_orthFamilyProj_mul_eq_zero_of_cols {A : Op N}
    (hA : ∀ j, orthFamilyProj u r *ᵥ (fun k => A k j) = fun k => A k j) :
    ((1 : Op N) - orthFamilyProj u r) * A = 0 := by
  ext i j
  have h : (orthFamilyProj u r *ᵥ (fun k => A k j)) i = A i j := congrFun (hA j) i
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.zero_apply,
    show (orthFamilyProj u r * A) i j = (orthFamilyProj u r *ᵥ (fun k => A k j)) i from rfl, h,
    sub_self]

/-- **The columnwise span condition, through a reindexing of the column index.**

The same bridge when the columns are indexed by a structured type `κ` mapping onto `Fin N` (a
rotated tensor frame, say): it is enough to know `P *ᵥ A_{·(e b)} = A_{·(e b)}` for every `b : κ`,
provided `e` is onto. -/
lemma one_sub_orthFamilyProj_mul_eq_zero_of_cols_comp {A : Op N} {κ : Type*} {e : κ → Fin N}
    (he : Function.Surjective e)
    (hA : ∀ b : κ, orthFamilyProj u r *ᵥ (fun k => A k (e b)) = fun k => A k (e b)) :
    ((1 : Op N) - orthFamilyProj u r) * A = 0 :=
  one_sub_orthFamilyProj_mul_eq_zero_of_cols
    (fun j => by obtain ⟨b, rfl⟩ := he j; exact hA b)

/-- **The general-`A` eigenform of `σ^{−1/2}`.**

For an operator `A` with no component off the span of the family (`(𝟙 − P)·A = 0`),

`Re Tr[σ^{−1/2}·A] = ∑_i (α_i r_i + c)^{−1/2}·r_i^{−1}·Re⟨u_i, A u_i⟩`.

The `c^{−1/2}·(𝟙 − P)` block of `orthFamilyInvSqrt` contributes nothing precisely because of the
span hypothesis; off the span it contributes `c^{−1/2}·Tr[(𝟙 − P)·A]`, which diverges as the
regularisation is removed. -/
theorem re_trace_inverseSqrt_mul_of_mem_span
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (hα : ∀ i, 0 ≤ α i) {c : ℝ} (hc : 0 < c)
    (hσ : (orthFamilyRegularized u α c).PosDef)
    (A : Op N) (hA : ((1 : Op N) - orthFamilyProj u r) * A = 0) :
    (hσ.inverseSqrt * A).trace.re
      = ∑ i : ι, (Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹ * (star (u i) ⬝ᵥ (A *ᵥ u i)).re := by
  have hterm : ∀ i : ι,
      (((((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹ : ℝ) : ℂ)
          • Matrix.vecMulVec (u i) (star (u i))) * A).trace
        = ((((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹ : ℝ)) : ℂ) * (star (u i) ⬝ᵥ (A *ᵥ u i)) := by
    intro i
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm,
      trace_mul_vecMulVec_star A (u i), smul_eq_mul]
  rw [posDef_inverseSqrt_eq_orthFamilyInvSqrt horth hnorm hr hα hc hσ, orthFamilyInvSqrt,
    Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, hA, smul_zero, Matrix.trace_zero, zero_add,
    Finset.sum_mul, Matrix.trace_sum]
  simp only [hterm]
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl (fun i _ => Complex.re_ofReal_mul _ _)

/-- A positive semidefinite operator has nonnegative real diagonal quadratic form. -/
lemma re_dotProduct_mulVec_re_nonneg {A : Op N} (hA : A.PosSemidef) (v : Fin N → ℂ) :
    0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re :=
  (Complex.le_def.mp (hA.dotProduct_mulVec_nonneg v)).1

/-- **The general-`A` `(1 − γ)^{−1/2}` envelope.**

At `α = (1 − γ)·λ` — unregularised orbit weights uniformly damped by `1 − γ`, plus the `c·𝟙`
regularisation — the regularised readout of any `A` supported in the span, whose orbit diagonal
`Re⟨u_i, A u_i⟩` is nonnegative (e.g. `A` positive semidefinite, via
`re_dotProduct_mulVec_re_nonneg`), is bounded by `(1 − γ)^{−1/2}` times the *unregularised* readout:

`Re Tr[σ_γ^{−1/2}·A] ≤ (1 − γ)^{−1/2}·∑_i (λ_i r_i)^{−1/2}·r_i^{−1}·Re⟨u_i, A u_i⟩.`

The right-hand side contains no regularisation parameter: the entire cost of removing `c` is the
single prefactor `(1 − γ)^{−1/2}`. -/
theorem re_trace_inverseSqrt_mul_le
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) {γ : ℝ} (hγ : γ < 1) {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i)
    {c : ℝ} (hc : 0 < c)
    (hσ : (orthFamilyRegularized u (fun i => (1 - γ) * lam i) c).PosDef)
    (A : Op N) (hA : ((1 : Op N) - orthFamilyProj u r) * A = 0)
    (hAnn : ∀ i, 0 ≤ (star (u i) ⬝ᵥ (A *ᵥ u i)).re) :
    (hσ.inverseSqrt * A).trace.re
      ≤ (Real.sqrt (1 - γ))⁻¹
          * ∑ i : ι, (Real.sqrt (lam i * r i))⁻¹ * (r i)⁻¹ * (star (u i) ⬝ᵥ (A *ᵥ u i)).re := by
  have hα : ∀ i, 0 ≤ (1 - γ) * lam i :=
    fun i => mul_nonneg (sub_nonneg.mpr hγ.le) (hlam i).le
  rw [re_trace_inverseSqrt_mul_of_mem_span horth hnorm hr hα hc hσ A hA, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hnn : (0 : ℝ) ≤ (r i)⁻¹ * (star (u i) ⬝ᵥ (A *ᵥ u i)).re :=
    mul_nonneg (le_of_lt (inv_pos.mpr (hr i))) (hAnn i)
  have hstep : (Real.sqrt ((1 - γ) * lam i * r i + c))⁻¹
      ≤ (Real.sqrt (1 - γ))⁻¹ * (Real.sqrt (lam i * r i))⁻¹ := by
    rw [show (1 - γ) * lam i * r i + c = (1 - γ) * (lam i * r i) + c from by ring]
    exact inv_sqrt_regularized_le hγ (mul_pos (hlam i) (hr i)) hc.le
  calc (Real.sqrt ((1 - γ) * lam i * r i + c))⁻¹ * (r i)⁻¹ * (star (u i) ⬝ᵥ (A *ᵥ u i)).re
      = (Real.sqrt ((1 - γ) * lam i * r i + c))⁻¹
          * ((r i)⁻¹ * (star (u i) ⬝ᵥ (A *ᵥ u i)).re) := by ring
    _ ≤ ((Real.sqrt (1 - γ))⁻¹ * (Real.sqrt (lam i * r i))⁻¹)
          * ((r i)⁻¹ * (star (u i) ⬝ᵥ (A *ᵥ u i)).re) := mul_le_mul_of_nonneg_right hstep hnn
    _ = (Real.sqrt (1 - γ))⁻¹
          * ((Real.sqrt (lam i * r i))⁻¹ * (r i)⁻¹ * (star (u i) ⬝ᵥ (A *ᵥ u i)).re) := by ring

end Family

end Quantum.Operators

end -- noncomputable section
