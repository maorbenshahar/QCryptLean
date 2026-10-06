import QCryptLean.Quantum.Operators.InverseSqrt
import QCryptLean.Quantum.TensorProducts.ProjectiveConditioning

/-!
# `σ^{−1/2}` for a regularised orthogonal-family operator

The inverse square root of

`σ = ∑_i α_i · |u_i⟩⟨u_i| + c · 𝟙`,   `⟨u_i, u_j⟩ = 0 (i ≠ j)`,  `‖u_i‖² = r_i > 0`,  `c > 0`,

for a **pairwise-orthogonal family `u` that need not span**.  This is the missing `inverseSqrt`
machinery for a reference operator with a **non-trivial kernel**: the `c·𝟙` regularisation makes `σ`
positive definite, and the kernel of `∑_i α_i |u_i⟩⟨u_i|` is carried explicitly by the complementary
projector `𝟙 − P`, whose `σ`-eigenvalue is exactly `c`.

## Why there is no diagonalising unitary here

The obvious route — complete `{u_i/√r_i}` to an orthonormal eigenbasis and conjugate a diagonal
matrix — needs `r_i − 1` further vectors per orbit with no canonical choice, i.e.
`Classical.choose`.
It is not needed.  `orthFamilyInvSqrt` writes `σ^{−1/2}` **explicitly** as
`c^{−1/2}(𝟙 − P) + ∑_i (α_i r_i + c)^{−1/2} r_i^{−1} |u_i⟩⟨u_i|` and identifies it with
`hσ.inverseSqrt` by uniqueness of the positive square root (`CFC.sqrt_unique`) — the eigenform
mechanism generalised from a diagonalising unitary to an orthogonal family.
No eigenbasis completion, no `Classical.choose`, no operator monotonicity (Löwner–Heinz).

## Main definitions

* `orthFamilyProj u r` — the orthogonal projector `P = ∑_i r_i^{−1} |u_i⟩⟨u_i|` onto `span {u_i}`.
* `orthFamilyRegularized u α c` — the operator `σ = ∑_i α_i |u_i⟩⟨u_i| + c·𝟙`.
* `orthFamilyInvSqrt u r α c` — the explicit `σ^{−1/2}`.

## Main statements

* `orthFamilyProj_mul_self`, `orthFamilyProj_posSemidef` — `P` is an orthogonal projector.
* `orthFamilyRegularized_posDef` — `σ` is positive definite as soon as `c > 0` and `α ≥ 0`.
* `orthFamilyInvSqrt_sq_mul_regularized` — `S·S·σ = 𝟙`.
* `posDef_inverseSqrt_eq_orthFamilyInvSqrt` — `hσ.inverseSqrt = S` (this is the spectral step).
* `re_trace_inverseSqrt_mul_vecMulVec_of_mem_span` — the quadratic-form readout for a vector in the
  span of the family: `Re Tr[σ^{−1/2}|χ⟩⟨χ|] = ∑_i (α_i r_i + c)^{−1/2} r_i^{−1} |⟨u_i, χ⟩|²`.
* `inv_sqrt_regularized_le` — the scalar step `((1−γ)λ + c)^{−1/2} ≤ (1−γ)^{−1/2} λ^{−1/2}`.
* `re_trace_inverseSqrt_mul_vecMulVec_le` — the two assembled: the `(1−γ)^{−1/2}` envelope of the
  regularised quadratic form by the **unregularised** one.

## Sources

Uniqueness of the positive semidefinite square root: Bhatia, *Matrix Analysis*, Thm V.1.9; in Lean
`CFC.sqrt_unique`.  Operator monotonicity (Bhatia Prop. V.1.6, Löwner–Heinz at `p = −1/2`) is
**not**
used: `inv_sqrt_regularized_le` is a scalar inequality, because on each orbit the operators in
question act by a scalar.

For two orthogonal vectors, `P·P − P = 0`, `S·S·σ − 𝟙 = 0`, and the eigenvalues of `S`
are `(α₁r₁+c)^{−1/2}`, `(α₂r₂+c)^{−1/2}`, and `c^{−1/2}` on the complement.
The off-span contribution is exactly the regulariser eigenvalue `c^{−1/2}`.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Operators

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-! ## The three objects -/

/-- **The orthogonal projector onto the span of a pairwise-orthogonal family.**

`P = ∑_i r_i^{−1} · |u_i⟩⟨u_i|`, where `r_i = ‖u_i‖²`.  It is a genuine orthogonal projector exactly
when the `u_i` are pairwise orthogonal with `‖u_i‖² = r_i`; the family need **not** span, and `𝟙 −
P`
is then the projector onto its orthogonal complement. -/
def orthFamilyProj (u : ι → (Fin N → ℂ)) (r : ι → ℝ) : Op N :=
  ∑ i : ι, ((r i : ℝ) : ℂ)⁻¹ • Matrix.vecMulVec (u i) (star (u i))

/-- **The regularised orthogonal-family operator** `σ = ∑_i α_i·|u_i⟩⟨u_i| + c·𝟙`.

`c > 0` is the regularisation that makes `σ` invertible: without it `σ` is singular whenever the
family fails to span, and `σ^{−1/2}` does not exist. -/
def orthFamilyRegularized (u : ι → (Fin N → ℂ)) (α : ι → ℝ) (c : ℝ) : Op N :=
  (∑ i : ι, ((α i : ℝ) : ℂ) • Matrix.vecMulVec (u i) (star (u i))) + ((c : ℝ) : ℂ) • (1 : Op N)

/-- **The explicit inverse square root of `orthFamilyRegularized`**:

`S = c^{−1/2}·(𝟙 − P) + ∑_i (α_i r_i + c)^{−1/2}·r_i^{−1}·|u_i⟩⟨u_i|`.

On the span of the family `S` acts by `(α_i r_i + c)^{−1/2}` on the `i`-th orbit, and on the
orthogonal complement — the kernel of the unregularised operator — by `c^{−1/2}`. -/
def orthFamilyInvSqrt (u : ι → (Fin N → ℂ)) (r α : ι → ℝ) (c : ℝ) : Op N :=
  (((Real.sqrt c)⁻¹ : ℝ) : ℂ) • ((1 : Op N) - orthFamilyProj u r)
    + ∑ i : ι, (((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹ : ℝ) : ℂ)
        • Matrix.vecMulVec (u i) (star (u i))

/-! ## Rank-one algebra -/

/-- `|v⟩⟨v|·|w⟩⟨w| = ⟨v, w⟩·|v⟩⟨w|`. -/
lemma vecMulVec_star_mul_vecMulVec_star (v w : Fin N → ℂ) :
    Matrix.vecMulVec v (star v) * Matrix.vecMulVec w (star w)
      = (star v ⬝ᵥ w) • Matrix.vecMulVec v (star w) := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  ext a b
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `Tr[M·|v⟩⟨v|] = ⟨v|M|v⟩`. -/
lemma trace_mul_vecMulVec_star (M : Op N) (v : Fin N → ℂ) :
    (M * Matrix.vecMulVec v (star v)).trace = star v ⬝ᵥ M.mulVec v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec, Pi.star_apply,
    Matrix.mulVec, dotProduct, Matrix.of_apply]
  conv_rhs => arg 2; ext i; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-! ## The scalar step -/

/-- **The scalar step of the `σ_γ^{−1/2}` bound**:
`((1 − γ)·λ + c)^{−1/2} ≤ (1 − γ)^{−1/2}·λ^{−1/2}` for `γ < 1`, `λ > 0`, `c ≥ 0`.

This is the *entire* content of "removing the regularisation costs a factor `(1 − γ)^{−1/2}`".  On a
single orbit the two operators being compared act by scalars, so no operator monotonicity
(Löwner–Heinz / Bhatia Prop. V.1.6) is involved.  Exactly tight iff `c = 0`. -/
lemma inv_sqrt_regularized_le {γ lam c : ℝ} (hγ : γ < 1) (hlam : 0 < lam) (hc : 0 ≤ c) :
    (Real.sqrt ((1 - γ) * lam + c))⁻¹ ≤ (Real.sqrt (1 - γ))⁻¹ * (Real.sqrt lam)⁻¹ := by
  have h1 : (0 : ℝ) < 1 - γ := by linarith
  have hprod : (0 : ℝ) < (1 - γ) * lam := mul_pos h1 hlam
  have hpos : (0 : ℝ) < Real.sqrt ((1 - γ) * lam) := Real.sqrt_pos.mpr hprod
  have hle : Real.sqrt ((1 - γ) * lam) ≤ Real.sqrt ((1 - γ) * lam + c) :=
    Real.sqrt_le_sqrt (by linarith)
  have hinv : (Real.sqrt ((1 - γ) * lam + c))⁻¹ ≤ (Real.sqrt ((1 - γ) * lam))⁻¹ :=
    inv_anti₀ hpos hle
  rwa [Real.sqrt_mul h1.le, mul_inv] at hinv

/-! ## The projector `P` -/

section Family

variable {u : ι → (Fin N → ℂ)} {r α : ι → ℝ}

/-- `P·|u_j⟩⟨u_j| = |u_j⟩⟨u_j|`: the projector fixes every member of its own family.  The
orthogonality of the family kills every cross term, and `‖u_j‖² = r_j` cancels the normalisation. -/
lemma orthFamilyProj_mul_vecMulVec
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (j : ι) :
    orthFamilyProj u r * Matrix.vecMulVec (u j) (star (u j))
      = Matrix.vecMulVec (u j) (star (u j)) := by
  have hrj : ((r j : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr j).ne'
  rw [orthFamilyProj, Finset.sum_mul, Finset.sum_eq_single j]
  · rw [smul_mul_assoc, vecMulVec_star_mul_vecMulVec_star, hnorm, smul_smul,
      inv_mul_cancel₀ hrj, one_smul]
  · intro i _ hij
    rw [smul_mul_assoc, vecMulVec_star_mul_vecMulVec_star, horth i j hij, zero_smul, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- `P` is idempotent. -/
lemma orthFamilyProj_mul_self
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) :
    orthFamilyProj u r * orthFamilyProj u r = orthFamilyProj u r := by
  nth_rewrite 2 [orthFamilyProj]
  rw [Matrix.mul_sum]
  rw [show (∑ j : ι, orthFamilyProj u r *
        (((r j : ℝ) : ℂ)⁻¹ • Matrix.vecMulVec (u j) (star (u j))))
      = ∑ j : ι, ((r j : ℝ) : ℂ)⁻¹ • Matrix.vecMulVec (u j) (star (u j)) from
    Finset.sum_congr rfl (fun j _ => by
      rw [mul_smul_comm, orthFamilyProj_mul_vecMulVec horth hnorm hr j])]
  rw [orthFamilyProj]

/-- `P` is positive semidefinite (hence Hermitian): a nonnegative combination of rank-one
projectors. -/
lemma orthFamilyProj_posSemidef (hr : ∀ i, 0 < r i) : (orthFamilyProj u r).PosSemidef := by
  rw [orthFamilyProj]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero ?_
  intro i _
  have hnn : (0 : ℂ) ≤ ((r i : ℝ) : ℂ)⁻¹ := by
    rw [show ((r i : ℝ) : ℂ)⁻¹ = (((r i)⁻¹ : ℝ) : ℂ) from by push_cast; ring]
    exact Complex.zero_le_real.mpr (le_of_lt (inv_pos.mpr (hr i)))
  exact (Matrix.posSemidef_vecMulVec_self_star (u i)).smul hnn

/-- `|u_j⟩⟨u_j|·P = |u_j⟩⟨u_j|`, the right-hand form of `orthFamilyProj_mul_vecMulVec`. -/
lemma vecMulVec_mul_orthFamilyProj
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (j : ι) :
    Matrix.vecMulVec (u j) (star (u j)) * orthFamilyProj u r
      = Matrix.vecMulVec (u j) (star (u j)) := by
  have h := congrArg Matrix.conjTranspose (orthFamilyProj_mul_vecMulVec horth hnorm hr j)
  rwa [Matrix.conjTranspose_mul, (Matrix.posSemidef_vecMulVec_self_star (u j)).isHermitian.eq,
    (orthFamilyProj_posSemidef (u := u) hr).isHermitian.eq] at h

/-- The complementary projector annihilates every member of the family. -/
lemma one_sub_orthFamilyProj_mul_vecMulVec
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (j : ι) :
    ((1 : Op N) - orthFamilyProj u r) * Matrix.vecMulVec (u j) (star (u j)) = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, orthFamilyProj_mul_vecMulVec horth hnorm hr j, sub_self]

/-- The complementary projector annihilates every member of the family, on the right. -/
lemma vecMulVec_mul_one_sub_orthFamilyProj
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (j : ι) :
    Matrix.vecMulVec (u j) (star (u j)) * ((1 : Op N) - orthFamilyProj u r) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, vecMulVec_mul_orthFamilyProj horth hnorm hr j, sub_self]

/-! ## Products inside the family algebra -/

/-- The family spans a commutative "diagonal" algebra: a product of two coefficient combinations is
again one, with coefficients multiplied and weighted by `r`. -/
lemma orthFamily_sum_mul_sum
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ)) (f g : ι → ℂ) :
    (∑ i : ι, f i • Matrix.vecMulVec (u i) (star (u i)))
        * (∑ j : ι, g j • Matrix.vecMulVec (u j) (star (u j)))
      = ∑ i : ι, (f i * g i * ((r i : ℝ) : ℂ)) • Matrix.vecMulVec (u i) (star (u i)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_sum, Finset.sum_eq_single i]
  · rw [smul_mul_assoc, mul_smul_comm, smul_smul, vecMulVec_star_mul_vecMulVec_star, hnorm,
      smul_smul]
  · intro j _ hji
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, vecMulVec_star_mul_vecMulVec_star,
      horth i j (Ne.symm hji), zero_smul, smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The complementary projector annihilates every coefficient combination of the family. -/
lemma one_sub_orthFamilyProj_mul_sum
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (f : ι → ℂ) :
    ((1 : Op N) - orthFamilyProj u r) * (∑ i : ι, f i • Matrix.vecMulVec (u i) (star (u i))) = 0 :=
        by
  rw [Matrix.mul_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [mul_smul_comm, one_sub_orthFamilyProj_mul_vecMulVec horth hnorm hr i, smul_zero]

/-- The complementary projector annihilates every coefficient combination of the family, on the
right. -/
lemma sum_mul_one_sub_orthFamilyProj
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (f : ι → ℂ) :
    (∑ i : ι, f i • Matrix.vecMulVec (u i) (star (u i))) * ((1 : Op N) - orthFamilyProj u r) = 0 :=
        by
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [smul_mul_assoc, vecMulVec_mul_one_sub_orthFamilyProj horth hnorm hr i, smul_zero]

/-! ## The normal form `b·(𝟙 − P) + ∑ f_i·|u_i⟩⟨u_i|` -/

/-- Every operator of the normal form `b·(𝟙 − P) + ∑_i f_i·|u_i⟩⟨u_i|` multiplies like a diagonal
matrix: the `(𝟙 − P)` blocks and the orbit blocks never mix.  This one lemma carries the whole of
the operator algebra of Layer 2; everything after it is scalar arithmetic. -/
lemma orthFamilyNormalForm_mul
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (b₁ b₂ : ℂ) (f g : ι → ℂ) :
    (b₁ • ((1 : Op N) - orthFamilyProj u r)
        + ∑ i : ι, f i • Matrix.vecMulVec (u i) (star (u i)))
      * (b₂ • ((1 : Op N) - orthFamilyProj u r)
        + ∑ i : ι, g i • Matrix.vecMulVec (u i) (star (u i)))
      = (b₁ * b₂) • ((1 : Op N) - orthFamilyProj u r)
        + ∑ i : ι, (f i * g i * ((r i : ℝ) : ℂ)) • Matrix.vecMulVec (u i) (star (u i)) := by
  have hQQ : ((1 : Op N) - orthFamilyProj u r) * ((1 : Op N) - orthFamilyProj u r)
      = (1 : Op N) - orthFamilyProj u r :=
    Quantum.TensorProducts.projector_complement_idempotent (orthFamilyProj_mul_self horth hnorm hr)
  have e1 : (b₁ • ((1 : Op N) - orthFamilyProj u r)) * (b₂ • ((1 : Op N) - orthFamilyProj u r))
      = (b₁ * b₂) • ((1 : Op N) - orthFamilyProj u r) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hQQ, smul_smul]
  have e2 : (b₁ • ((1 : Op N) - orthFamilyProj u r))
      * (∑ i : ι, g i • Matrix.vecMulVec (u i) (star (u i))) = 0 := by
    rw [Matrix.smul_mul, one_sub_orthFamilyProj_mul_sum horth hnorm hr g, smul_zero]
  have e3 : (∑ i : ι, f i • Matrix.vecMulVec (u i) (star (u i)))
      * (b₂ • ((1 : Op N) - orthFamilyProj u r)) = 0 := by
    rw [Matrix.mul_smul, sum_mul_one_sub_orthFamilyProj horth hnorm hr f, smul_zero]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3,
    orthFamily_sum_mul_sum horth hnorm f g, add_zero, zero_add]

/-- The normal form at `b = 1`, `f_i = r_i^{−1}` is the identity: `(𝟙 − P) + P = 𝟙`. -/
lemma orthFamilyNormalForm_one :
    (1 : ℂ) • ((1 : Op N) - orthFamilyProj u r)
        + ∑ i : ι, ((r i : ℝ) : ℂ)⁻¹ • Matrix.vecMulVec (u i) (star (u i))
      = (1 : Op N) := by
  rw [one_smul, ← orthFamilyProj, sub_add_cancel]

/-! ## The regularised operator and its inverse square root -/

/-- The regularised operator, split along the projector:
`σ = c·(𝟙 − P) + ∑_i (α_i + c/r_i)·|u_i⟩⟨u_i|`.  Both summands are now *inside* the family algebra
(with the kernel block carried by `𝟙 − P`), which is what makes the whole computation a scalar one
per orbit. -/
lemma orthFamilyRegularized_eq_split (c : ℝ) :
    orthFamilyRegularized u α c
      = ((c : ℝ) : ℂ) • ((1 : Op N) - orthFamilyProj u r)
        + ∑ i : ι, (((α i + c * (r i)⁻¹ : ℝ)) : ℂ) • Matrix.vecMulVec (u i) (star (u i)) := by
  have h1 : (((c : ℝ) : ℂ) • orthFamilyProj u r)
      = ∑ i : ι, (((c * (r i)⁻¹ : ℝ)) : ℂ) • Matrix.vecMulVec (u i) (star (u i)) := by
    rw [orthFamilyProj, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [smul_smul]; push_cast; ring_nf)
  have h2 : (∑ i : ι, (((α i + c * (r i)⁻¹ : ℝ)) : ℂ) • Matrix.vecMulVec (u i) (star (u i)))
      = (∑ i : ι, ((α i : ℝ) : ℂ) • Matrix.vecMulVec (u i) (star (u i)))
        + ∑ i : ι, (((c * (r i)⁻¹ : ℝ)) : ℂ) • Matrix.vecMulVec (u i) (star (u i)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [← add_smul]; push_cast; ring_nf)
  rw [orthFamilyRegularized, smul_sub, h1, h2]
  abel

/-- `σ` is positive definite: a nonnegative combination of rank-one projectors plus `c·𝟙` with
`c > 0`.  This is exactly the hypothesis `Matrix.PosDef.inverseSqrt` demands, and it is why the
regularisation is not optional. -/
lemma orthFamilyRegularized_posDef (hα : ∀ i, 0 ≤ α i) {c : ℝ} (hc : 0 < c) :
    (orthFamilyRegularized u α c).PosDef := by
  rw [orthFamilyRegularized]
  refine Matrix.PosDef.posSemidef_add ?_ ?_
  · refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
      Matrix.PosSemidef.zero ?_
    intro i _
    exact (Matrix.posSemidef_vecMulVec_self_star (u i)).smul (Complex.zero_le_real.mpr (hα i))
  · exact (Matrix.PosDef.one (R := ℂ) (n := Fin N)).smul
      (by exact_mod_cast Complex.zero_lt_real.mpr hc)

/-- `S = orthFamilyInvSqrt u r α c` is positive semidefinite: `𝟙 − P` is a projector and every
coefficient is a nonnegative real (an inverse square root, or `0` where `Real.sqrt` saturates). -/
lemma orthFamilyInvSqrt_posSemidef
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (c : ℝ) :
    (orthFamilyInvSqrt u r α c).PosSemidef := by
  rw [orthFamilyInvSqrt]
  refine Matrix.PosSemidef.add ?_ ?_
  · refine Matrix.PosSemidef.smul ?_ (Complex.zero_le_real.mpr (by positivity))
    exact Quantum.TensorProducts.projector_complement_posSemidef (orthFamilyProj u r)
      (orthFamilyProj_mul_self horth hnorm hr) (orthFamilyProj_posSemidef (u := u)
          hr).isHermitian.eq
  · refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
      Matrix.PosSemidef.zero ?_
    intro i _
    refine (Matrix.posSemidef_vecMulVec_self_star (u i)).smul
      (Complex.zero_le_real.mpr ?_)
    have h1 : (0 : ℝ) ≤ (Real.sqrt (α i * r i + c))⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ (r i)⁻¹ := le_of_lt (inv_pos.mpr (hr i))
    exact mul_nonneg h1 h2

/-- **`S·S·σ = 𝟙`** — the whole content of the spectral step.

Both `S·S` and `σ` are in the normal form of `orthFamilyNormalForm_mul`, so the product is one too,
with coefficients `c^{−1}·c = 1` on the kernel block and
`[(α_i r_i + c)^{−1} r_i^{−2}]·r_i·[(α_i r_i + c) r_i^{−1}]·r_i = r_i^{−1}` on the `i`-th orbit —
exactly the coefficients of `orthFamilyNormalForm_one`. -/
lemma orthFamilyInvSqrt_sq_mul_regularized
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (hα : ∀ i, 0 ≤ α i) {c : ℝ} (hc : 0 < c) :
    orthFamilyInvSqrt u r α c * orthFamilyInvSqrt u r α c * orthFamilyRegularized u α c
      = (1 : Op N) := by
  have hcsq : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have hcne : Real.sqrt c ≠ 0 := Real.sqrt_ne_zero'.mpr hc
  -- the kernel-block coefficient
  have hb : (((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ * c : ℝ)) = 1 := by
    field_simp
    rw [sq, hcsq]
  -- the orbit coefficients
  have ha : ∀ i : ι,
      ((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹) * ((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹)
          * (r i) * (α i + c * (r i)⁻¹) * (r i) = (r i)⁻¹ := by
    intro i
    have hri : (r i) ≠ 0 := (hr i).ne'
    have hpos : 0 < α i * r i + c := by
      have := mul_nonneg (hα i) (hr i).le
      linarith
    have hs : Real.sqrt (α i * r i + c) * Real.sqrt (α i * r i + c) = α i * r i + c :=
      Real.mul_self_sqrt hpos.le
    have hs2 : Real.sqrt (α i * r i + c) ^ 2 = α i * r i + c := by rw [sq]; exact hs
    have hsne : Real.sqrt (α i * r i + c) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
    field_simp
    exact hs2.symm
  -- the same two coefficient identities, transported to `ℂ`
  have hcoef : ∀ i : ι, ((((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹ : ℝ) : ℂ)
        * (((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹ : ℝ) : ℂ) * ((r i : ℝ) : ℂ)
        * (((α i + c * (r i)⁻¹ : ℝ)) : ℂ) * ((r i : ℝ) : ℂ)) = ((r i : ℝ) : ℂ)⁻¹ := by
    intro i
    rw [show ((((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹ : ℝ) : ℂ)
          * (((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹ : ℝ) : ℂ) * ((r i : ℝ) : ℂ)
          * (((α i + c * (r i)⁻¹ : ℝ)) : ℂ) * ((r i : ℝ) : ℂ))
        = ((((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹)
              * ((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹) * (r i)
              * (α i + c * (r i)⁻¹) * (r i) : ℝ) : ℂ) from by push_cast; ring,
      ha i, Complex.ofReal_inv]
  rw [orthFamilyInvSqrt, orthFamilyNormalForm_mul horth hnorm hr,
    orthFamilyRegularized_eq_split (u := u) (r := r) c,
    orthFamilyNormalForm_mul horth hnorm hr]
  rw [show ((((Real.sqrt c)⁻¹ : ℝ) : ℂ) * (((Real.sqrt c)⁻¹ : ℝ) : ℂ)) * ((c : ℝ) : ℂ)
      = (1 : ℂ) from by rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hb]; norm_num]
  simp only [hcoef]
  exact orthFamilyNormalForm_one

/-- **The spectral step**: the explicit `orthFamilyInvSqrt` *is* `σ^{−1/2}`.

By `orthFamilyInvSqrt_sq_mul_regularized` the explicit `S` is a left inverse of `σ` after squaring,
so `S·S = σ⁻¹`; `S` is positive semidefinite; and the positive square root of a positive element is
unique (`CFC.sqrt_unique`).  No diagonalising unitary is constructed anywhere. -/
theorem posDef_inverseSqrt_eq_orthFamilyInvSqrt
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (hα : ∀ i, 0 ≤ α i) {c : ℝ} (hc : 0 < c)
    (hσ : (orthFamilyRegularized u α c).PosDef) :
    hσ.inverseSqrt = orthFamilyInvSqrt u r α c := by
  rw [Matrix.PosDef.inverseSqrt]
  exact CFC.sqrt_unique
    (Matrix.inv_eq_left_inv (orthFamilyInvSqrt_sq_mul_regularized horth hnorm hr hα hc)).symm
    (orthFamilyInvSqrt_posSemidef horth hnorm hr c).nonneg

/-! ## The readout on the span, and the `(1−γ)^{−1/2}` envelope -/

/-- **The quadratic-form readout of `σ^{−1/2}` at a vector in the span of the family.**

For `χ` fixed by the projector (`P·χ = χ`, i.e. `χ` has no component in the kernel of the
unregularised operator),

`Re Tr[σ^{−1/2}·|χ⟩⟨χ|] = ∑_i (α_i r_i + c)^{−1/2}·r_i^{−1}·|⟨u_i, χ⟩|².`

The `c^{−1/2}` block contributes nothing precisely because `χ` is in the span; off the span it
contributes the regulariser eigenvalue `c^{−1/2}`, which diverges as the regularisation is removed.
That is the exact sense in which the span hypothesis is load-bearing rather than decorative. -/
theorem re_trace_inverseSqrt_mul_vecMulVec_of_mem_span
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) (hα : ∀ i, 0 ≤ α i) {c : ℝ} (hc : 0 < c)
    (hσ : (orthFamilyRegularized u α c).PosDef)
    (χ : Fin N → ℂ) (hχ : orthFamilyProj u r *ᵥ χ = χ) :
    (hσ.inverseSqrt * Matrix.vecMulVec χ (star χ)).trace.re
      = ∑ i : ι, (Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹ * ‖star (u i) ⬝ᵥ χ‖ ^ 2 := by
  have hQχ : ((1 : Op N) - orthFamilyProj u r) *ᵥ χ = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hχ, sub_self]
  have hstarz : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [show star z = (starRingEnd ℂ) z from rfl, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hterm : ∀ i : ι, star χ ⬝ᵥ (Matrix.vecMulVec (u i) (star (u i)) *ᵥ χ)
      = ((‖star (u i) ⬝ᵥ χ‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have hz : star χ ⬝ᵥ (Matrix.vecMulVec (u i) (star (u i)) *ᵥ χ)
        = star (star (u i) ⬝ᵥ χ) * (star (u i) ⬝ᵥ χ) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Pi.star_apply,
        star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    rw [hz, hstarz]
  rw [posDef_inverseSqrt_eq_orthFamilyInvSqrt horth hnorm hr hα hc hσ,
    trace_mul_vecMulVec_star, orthFamilyInvSqrt, Matrix.add_mulVec, Matrix.smul_mulVec,
    hQχ, smul_zero, zero_add, Matrix.sum_mulVec, dotProduct_sum]
  rw [show (∑ i : ι, star χ ⬝ᵥ (((((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹ : ℝ) : ℂ)
        • Matrix.vecMulVec (u i) (star (u i))) *ᵥ χ))
      = ∑ i : ι, ((((Real.sqrt (α i * r i + c))⁻¹ * (r i)⁻¹) * ‖star (u i) ⬝ᵥ χ‖ ^ 2 : ℝ) : ℂ) from
    Finset.sum_congr rfl (fun i _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hterm i, ← Complex.ofReal_mul])]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]

/-- **Step 0′ (general form): the `(1 − γ)^{−1/2}` envelope of the regularised readout.**

At `α = (1 − γ)·λ` — a family of unregularised orbit weights, uniformly damped by `1 − γ`, plus the
`c·𝟙` regularisation — the regularised quadratic form is bounded by `(1 − γ)^{−1/2}` times the
*unregularised* one:

`Re Tr[σ_γ^{−1/2}·|χ⟩⟨χ|] ≤ (1 − γ)^{−1/2}·∑_i (λ_i r_i)^{−1/2}·r_i^{−1}·|⟨u_i, χ⟩|².`

`λ_i r_i` is the eigenvalue of the unregularised `∑_j λ_j·|u_j⟩⟨u_j|` on the `i`-th orbit (each
`u_i`
has norm-squared `r_i`), so the right-hand side carries **no** regularisation parameter at all: the
entire cost of removing `c` is the single prefactor `(1 − γ)^{−1/2}`, and it is paid per amplitude,
i.e. `(1 − γ)^{−1}` in a collision sum. -/
theorem re_trace_inverseSqrt_mul_vecMulVec_le
    (horth : ∀ i j, i ≠ j → star (u i) ⬝ᵥ u j = 0)
    (hnorm : ∀ i, star (u i) ⬝ᵥ u i = ((r i : ℝ) : ℂ))
    (hr : ∀ i, 0 < r i) {γ : ℝ} (hγ : γ < 1) {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i)
    {c : ℝ} (hc : 0 < c)
    (hσ : (orthFamilyRegularized u (fun i => (1 - γ) * lam i) c).PosDef)
    (χ : Fin N → ℂ) (hχ : orthFamilyProj u r *ᵥ χ = χ) :
    (hσ.inverseSqrt * Matrix.vecMulVec χ (star χ)).trace.re
      ≤ (Real.sqrt (1 - γ))⁻¹
          * ∑ i : ι, (Real.sqrt (lam i * r i))⁻¹ * (r i)⁻¹ * ‖star (u i) ⬝ᵥ χ‖ ^ 2 := by
  have hα : ∀ i, 0 ≤ (1 - γ) * lam i := fun i => mul_nonneg (by linarith) (hlam i).le
  rw [re_trace_inverseSqrt_mul_vecMulVec_of_mem_span horth hnorm hr hα hc hσ χ hχ, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hnn : (0 : ℝ) ≤ (r i)⁻¹ * ‖star (u i) ⬝ᵥ χ‖ ^ 2 :=
    mul_nonneg (le_of_lt (inv_pos.mpr (hr i))) (sq_nonneg _)
  have hstep : (Real.sqrt ((1 - γ) * lam i * r i + c))⁻¹
      ≤ (Real.sqrt (1 - γ))⁻¹ * (Real.sqrt (lam i * r i))⁻¹ := by
    rw [show (1 - γ) * lam i * r i + c = (1 - γ) * (lam i * r i) + c from by ring]
    exact inv_sqrt_regularized_le hγ (mul_pos (hlam i) (hr i)) hc.le
  calc (Real.sqrt ((1 - γ) * lam i * r i + c))⁻¹ * (r i)⁻¹ * ‖star (u i) ⬝ᵥ χ‖ ^ 2
      = (Real.sqrt ((1 - γ) * lam i * r i + c))⁻¹ * ((r i)⁻¹ * ‖star (u i) ⬝ᵥ χ‖ ^ 2) := by ring
    _ ≤ ((Real.sqrt (1 - γ))⁻¹ * (Real.sqrt (lam i * r i))⁻¹)
          * ((r i)⁻¹ * ‖star (u i) ⬝ᵥ χ‖ ^ 2) := mul_le_mul_of_nonneg_right hstep hnn
    _ = (Real.sqrt (1 - γ))⁻¹
          * ((Real.sqrt (lam i * r i))⁻¹ * (r i)⁻¹ * ‖star (u i) ⬝ᵥ χ‖ ^ 2) := by ring

end Family

end Quantum.Operators

end -- noncomputable section
