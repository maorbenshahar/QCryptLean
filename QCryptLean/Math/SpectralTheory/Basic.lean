import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.Submodule.Lattice
import QCryptLean.Math.LinearAlgebra.SubmoduleDimension

/-!
# Spectral Theory for Linear Algebra

General spectral theory results needed for quantum information proofs.
This module contains eigenvalue theorems for arbitrary matrices, not specific
to density operators or quantum states.

## Main Results

- `nonzero_eigenvalues_conjTranspose_mul_eq`: CC† and C†C have the same non-zero eigenvalues
- `eigenvalues_kronecker`: Eigenvalues of A ⊗ B are products of eigenvalues of A and B
- `cfc_sqrt_conjTranspose_eq`: the CFC square root of a matrix is Hermitian

## Applications

These theorems are used in:
- Schmidt decomposition (reduced density matrices have same spectrum)
- Entropy additivity for tensor products

## Mathematical Background

### CC† vs C†C Eigenvalues

For any matrix C : Matrix m n ℂ, the matrices CC† (m × m) and C†C (n × n) have
the same non-zero eigenvalues, counting multiplicities.

**Proof sketch via SVD**:
1. C = UΣV† where Σ has singular values σᵢ
2. CC† = UΣΣ†U† has eigenvalues σᵢ²
3. C†C = VΣ†ΣV† has eigenvalues σᵢ²
4. Both have the same non-zero eigenvalues (σᵢ² for σᵢ ≠ 0)

**Alternative algebraic proof**:
If Cv = λv with λ ≠ 0, then C†Cv = λC†v, and C†v ≠ 0.
So λ is an eigenvalue of C†C iff λ is an eigenvalue of CC†.

### Tensor Product Eigenvalues

For Hermitian matrices A and B with eigenvalues {λᵢ} and {μⱼ}:
- A ⊗ B has eigenvalues {λᵢ · μⱼ}
- This follows from (v ⊗ w) being an eigenvector of A ⊗ B when v, w are eigenvectors

-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix Unitary

/-- Local dagger notation for conjugate transpose (avoids tier-violating import) -/
local postfix:max "†" => Matrix.conjTranspose

namespace Math.SpectralTheory

variable {n m : ℕ}

/-- The non-unital continuous functional calculus of complex matrices (behind `CFC.sqrt`,
`CFC.abs` and the real powers `A ^ (r : ℝ)`): the restriction of the unital calculus
`Matrix.IsHermitian.instContinuousFunctionalCalculus`. It is the instance typeclass search would
find anyway; declaring it here short-circuits that search, which is otherwise slow on matrices
because it first tries, and fails, the restriction of a complex calculus
(`IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus`). -/
instance instNonUnitalContinuousFunctionalCalculusMatrix {ι : Type*} [Fintype ι]
    [DecidableEq ι] : NonUnitalContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital

/-!
## Eigenvalue Multisets

We work with eigenvalues as multisets (unordered with multiplicity) since
we care about the spectrum, not the ordering.
-/

/-- Eigenvalues of a Hermitian matrix as a multiset of reals. -/
noncomputable def hermitianEigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) : Multiset ℝ :=
  Finset.univ.val.map hA.eigenvalues

/-- Eigenvalues of a Hermitian matrix with product index type. -/
noncomputable def hermitianEigenvaluesProd {n m : ℕ}
    (A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) (hA : A.IsHermitian) : Multiset ℝ :=
  Finset.univ.val.map hA.eigenvalues

/-- Non-zero eigenvalues of a Hermitian matrix. -/
noncomputable def nonzeroEigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) : Multiset ℝ :=
  (hermitianEigenvalues A hA).filter (· ≠ 0)

/-!
## CC† and C†C Have Same Non-Zero Eigenvalues

This is the key lemma for Schmidt decomposition.

The proof strategy establishes a correspondence between eigenvectors.
-/

/-- Helper: If v is an eigenvector of CC† with eigenvalue lam,
then C†v is an eigenvector of C†C with the same eigenvalue.

This is the key step in showing eigenspace correspondence. -/
lemma eigenvector_map_conjTranspose (C : Matrix (Fin n) (Fin m) ℂ)
    {v : Fin n → ℂ} {lam : ℂ} :
    (C * Cᴴ) *ᵥ v = lam • v →
    (Cᴴ * C) *ᵥ (Cᴴ *ᵥ v) = lam • (Cᴴ *ᵥ v) := by
  intro hv
  -- Use mulVec_mulVec: M *ᵥ N *ᵥ w = (M * N) *ᵥ w
  have step1 : (Cᴴ * C) *ᵥ (Cᴴ *ᵥ v) = Cᴴ *ᵥ (C *ᵥ (Cᴴ *ᵥ v)) := by
    rw [← mulVec_mulVec]
  have step2 : C *ᵥ (Cᴴ *ᵥ v) = (C * Cᴴ) *ᵥ v := by
    rw [mulVec_mulVec]
  rw [step1, step2, hv, mulVec_smul]

/-- Helper: By symmetry, eigenvectors map in the reverse direction. -/
lemma eigenvector_map_transpose (C : Matrix (Fin n) (Fin m) ℂ)
    {w : Fin m → ℂ} {lam : ℂ} :
    (Cᴴ * C) *ᵥ w = lam • w →
    (C * Cᴴ) *ᵥ (C *ᵥ w) = lam • (C *ᵥ w) := by
  intro hw
  -- Symmetric to eigenvector_map_conjTranspose
  have step1 : (C * Cᴴ) *ᵥ (C *ᵥ w) = C *ᵥ (Cᴴ *ᵥ (C *ᵥ w)) := by
    rw [← mulVec_mulVec]
  have step2 : Cᴴ *ᵥ (C *ᵥ w) = (Cᴴ * C) *ᵥ w := by
    rw [mulVec_mulVec]
  rw [step1, step2, hw, mulVec_smul]

/-- The critical fact: C†v ≠ 0 when v is an eigenvector with non-zero eigenvalue.

Proof by contradiction: if C†v = 0, then CC†v = C(C†v) = C(0) = 0 = λv.
But λ ≠ 0 and v ≠ 0, so λv ≠ 0, contradiction. -/
lemma conjTranspose_mulVec_ne_zero_of_eigenvalue_ne_zero
    (C : Matrix (Fin n) (Fin m) ℂ) {v : Fin n → ℂ} {lam : ℂ}
    (hlam : lam ≠ 0) (hv : v ≠ 0) (heigen : (C * Cᴴ) *ᵥ v = lam • v) :
    Cᴴ *ᵥ v ≠ 0 := by
  intro h_contra  -- Assume Cᴴ *ᵥ v = 0
  -- Then (C * Cᴴ) *ᵥ v = C *ᵥ (Cᴴ *ᵥ v) = C *ᵥ 0 = 0
  have h1 : (C * Cᴴ) *ᵥ v = 0 := by
    rw [← mulVec_mulVec, h_contra, mulVec_zero]
  -- But heigen says (C * Cᴴ) *ᵥ v = lam • v, so lam • v = 0
  rw [heigen] at h1
  -- Since lam ≠ 0 and v ≠ 0, this is a contradiction
  have h2 : v = 0 := by
    have : lam⁻¹ • (lam • v) = lam⁻¹ • (0 : Fin n → ℂ) := by rw [h1]
    simp only [smul_zero, inv_smul_smul₀ hlam] at this
    exact this
  exact hv h2

/-- CC† is Hermitian for any matrix C. -/
theorem mul_conjTranspose_isHermitian (C : Matrix (Fin n) (Fin m) ℂ) :
    (C * Cᴴ).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-- C†C is Hermitian for any matrix C. -/
theorem conjTranspose_mul_isHermitian (C : Matrix (Fin n) (Fin m) ℂ) :
    (Cᴴ * C).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-- CC† is positive semidefinite. -/
theorem mul_conjTranspose_posSemidef (C : Matrix (Fin n) (Fin m) ℂ) :
    (C * Cᴴ).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose C

/-- C†C is positive semidefinite. -/
theorem conjTranspose_mul_posSemidef (C : Matrix (Fin n) (Fin m) ℂ) :
    (Cᴴ * C).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self C

/-- The CFC square root of a matrix is Hermitian. -/
lemma cfc_sqrt_conjTranspose_eq {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) :
    (CFC.sqrt P).conjTranspose = CFC.sqrt P := by
  exact ((CFC.sqrt_nonneg (a := P)).posSemidef).isHermitian.eq

/-- **Main theorem**: CC† and C†C have the same non-zero eigenvalues.

For any matrix C, the non-zero eigenvalues of CC† equal those of C†C
(as multisets, counting multiplicities).

This is fundamental for Schmidt decomposition: if ρ = |ψ⟩⟨ψ| is a pure
bipartite state with coefficient matrix C, then:
- ρ_A = Tr_B(ρ) has the same spectrum as C†C
- ρ_B = Tr_A(ρ) has the same spectrum as CC†
- Therefore ρ_A and ρ_B have the same non-zero eigenvalues.

**Proof strategy**: Algebraic approach via eigenspace bijection.

1. Key observation: If CC†v = λv with λ ≠ 0, then C†C(C†v) = λ(C†v)
   Proof: C†C(C†v) = C†(CC†v) = C†(λv) = λ(C†v)

2. Crucial fact: C†v ≠ 0 when λ ≠ 0
   Proof via inner product: ⟨C†v, C†v⟩ = ⟨v, CC†v⟩ = ⟨v, λv⟩ = λ̄⟨v, v⟩
   Since λ ≠ 0 and v ≠ 0, we have ⟨C†v, C†v⟩ ≠ 0, thus C†v ≠ 0

3. This establishes an isomorphism: eigenspace(CC†, λ) ≃ eigenspace(C†C, λ) for λ ≠ 0

4. By symmetry (C ↔ C†), the reverse direction holds

5. Eigenspace dimensions determine multiset multiplicities, so multisets are equal

**Missing infrastructure**:
- Eigenspace isomorphism (v ↦ C†v)
- Connection between eigenspace dimension and multiset multiplicity
- Inner product arguments for (Fin n → ℂ)

**Alternative via SVD** (not yet in Mathlib):
- C = UΣV† implies CC† = UΣ²U† and C†C = VΣ²V†
- Both have eigenvalues σᵢ² for singular values σᵢ

**Partial evidence**:
- `rank_conjTranspose_mul_self` and `rank_self_mul_conjTranspose` show same rank
- Rank = number of non-zero eigenvalues for PSD matrices
- This confirms the cardinalities match, but not the multiset equality with multiplicities -/
theorem nonzero_eigenvalues_conjTranspose_mul_eq [NeZero n] [NeZero m]
    (C : Matrix (Fin n) (Fin m) ℂ) :
    nonzeroEigenvalues (C * Cᴴ) (mul_conjTranspose_isHermitian C) =
    nonzeroEigenvalues (Cᴴ * C) (conjTranspose_mul_isHermitian C) := by
  -- PROOF VIA CHARACTERISTIC POLYNOMIALS
  -- The key insight is charpoly_mul_comm': X^m * charpoly(CC†) = X^n * charpoly(C†C)
  -- This means the non-zero roots (with multiplicities) are the same.
  --
  -- Step 1: Get the characteristic polynomial relationship
  have h_charpoly := Matrix.charpoly_mul_comm' C Cᴴ
  -- h_charpoly: X^m * (C * Cᴴ).charpoly = X^n * (Cᴴ * C).charpoly
  --
  -- Step 2: Use roots_charpoly_eq_eigenvalues to connect eigenvalues to roots
  have h_roots_CC := (mul_conjTranspose_isHermitian C).roots_charpoly_eq_eigenvalues
  have h_roots_CtC := (conjTranspose_mul_isHermitian C).roots_charpoly_eq_eigenvalues
  --
  -- PROOF: Show multiset equality by counting each non-zero element
  unfold nonzeroEigenvalues hermitianEigenvalues
  ext a
  by_cases ha : a = 0
  · -- For a = 0: count in filter (· ≠ 0) is 0 on both sides
    subst ha
    simp only [ne_eq, Multiset.count_filter_of_neg, not_true_eq_false, not_false_eq_true]
  · -- For a ≠ 0: use the characteristic polynomial relationship
    simp only [Multiset.count_filter, ne_eq, ha, not_false_eq_true, ↓reduceIte]
    -- The eigenvalues multiset maps through RCLike.ofReal ∘ eigenvalues
    -- count a (map eigenvalues univ) = count (ofReal a) (map ofReal (map eigenvalues univ))
    -- = count (ofReal a) (charpoly.roots) = rootMultiplicity (ofReal a) charpoly
    --
    -- Key relation: map (f ∘ g) s = map f (map g s)
    have h_count_CC : Multiset.count a
        (Finset.univ.val.map (mul_conjTranspose_isHermitian C).eigenvalues) =
        (C * Cᴴ).charpoly.rootMultiplicity (↑a : ℂ) := by
      -- Step 1: count a (map eigenvalues univ) = count (↑a) (map ↑· (map eigenvalues univ))
      have h_step1 : Multiset.count a (Finset.univ.val.map (mul_conjTranspose_isHermitian
          C).eigenvalues) =
          Multiset.count (↑a : ℂ)
            (Multiset.map (fun r : ℝ => (r : ℂ)) (Finset.univ.val.map (mul_conjTranspose_isHermitian
                C).eigenvalues)) :=
        (Multiset.count_map_eq_count' (fun r : ℝ => (r : ℂ)) _ Complex.ofReal_injective a).symm
      -- Step 2: map ↑· (map eigenvalues univ) = map (↑· ∘ eigenvalues) univ
      have h_step2 : Multiset.map (fun r : ℝ => (r : ℂ))
          (Finset.univ.val.map (mul_conjTranspose_isHermitian C).eigenvalues) =
          Multiset.map (RCLike.ofReal ∘ (mul_conjTranspose_isHermitian C).eigenvalues)
              Finset.univ.val := by
        rw [← Multiset.map_map]; rfl
      -- Step 3: map (↑· ∘ eigenvalues) univ = charpoly.roots (by h_roots_CC)
      -- Step 4: count in roots = rootMultiplicity (by Polynomial.count_roots)
      rw [h_step1, h_step2, ← h_roots_CC, Polynomial.count_roots]
    have h_count_CtC : Multiset.count a
        (Finset.univ.val.map (conjTranspose_mul_isHermitian C).eigenvalues) =
        (Cᴴ * C).charpoly.rootMultiplicity (↑a : ℂ) := by
      have h_step1 : Multiset.count a (Finset.univ.val.map (conjTranspose_mul_isHermitian
          C).eigenvalues) =
          Multiset.count (↑a : ℂ)
            (Multiset.map (fun r : ℝ => (r : ℂ)) (Finset.univ.val.map (conjTranspose_mul_isHermitian
                C).eigenvalues)) :=
        (Multiset.count_map_eq_count' (fun r : ℝ => (r : ℂ)) _ Complex.ofReal_injective a).symm
      have h_step2 : Multiset.map (fun r : ℝ => (r : ℂ))
          (Finset.univ.val.map (conjTranspose_mul_isHermitian C).eigenvalues) =
          Multiset.map (RCLike.ofReal ∘ (conjTranspose_mul_isHermitian C).eigenvalues)
              Finset.univ.val := by
        rw [← Multiset.map_map]; rfl
      rw [h_step1, h_step2, ← h_roots_CtC, Polynomial.count_roots]
    rw [h_count_CC, h_count_CtC]
    -- Now show: (C * Cᴴ).charpoly.rootMultiplicity a = (Cᴴ * C).charpoly.rootMultiplicity a
    -- for a ≠ 0, using h_charpoly: X^m * (C * Cᴴ).charpoly = X^n * (Cᴴ * C).charpoly
    have h_a_ne : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    -- For a ≠ 0, a is not a root of X^k, so rootMultiplicity a (X^k) = 0
    have h_not_root_X_pow : ∀ k : ℕ, ¬(Polynomial.X ^ k : Polynomial ℂ).IsRoot (↑a : ℂ) := by
      intro k
      simp only [Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_X]
      exact pow_ne_zero k h_a_ne
    have h_rm_pow_X_ne_zero : ∀ k : ℕ, (Polynomial.X ^ k : Polynomial ℂ).rootMultiplicity (↑a : ℂ) =
        0 := by
      intro k
      exact Polynomial.rootMultiplicity_eq_zero (h_not_root_X_pow k)
    -- Key: X^k ≠ 0 in any nontrivial semiring
    have h_X_pow_ne_zero : ∀ k : ℕ, (Polynomial.X ^ k : Polynomial ℂ) ≠ 0 := by
      intro k
      exact pow_ne_zero k Polynomial.X_ne_zero
    -- Charpoly is nonzero (monic polynomials are nonzero)
    have h_charpoly_ne_zero_CC : (C * Cᴴ).charpoly ≠ 0 :=
      Polynomial.Monic.ne_zero (Matrix.charpoly_monic _)
    have h_charpoly_ne_zero_CtC : (Cᴴ * C).charpoly ≠ 0 :=
      Polynomial.Monic.ne_zero (Matrix.charpoly_monic _)
    -- Product of nonzero polynomials is nonzero
    have h_prod_ne_zero_CC : (Polynomial.X ^ Fintype.card (Fin m) : Polynomial ℂ) * (C *
        Cᴴ).charpoly ≠ 0 :=
      mul_ne_zero (h_X_pow_ne_zero _) h_charpoly_ne_zero_CC
    have h_prod_ne_zero_CtC : (Polynomial.X ^ Fintype.card (Fin n) : Polynomial ℂ) * (Cᴴ *
        C).charpoly ≠ 0 :=
      mul_ne_zero (h_X_pow_ne_zero _) h_charpoly_ne_zero_CtC
    calc (C * Cᴴ).charpoly.rootMultiplicity (↑a : ℂ)
        = 0 + (C * Cᴴ).charpoly.rootMultiplicity (↑a : ℂ) := by ring
      _ = (Polynomial.X ^ Fintype.card (Fin m) : Polynomial ℂ).rootMultiplicity (↑a : ℂ) +
          (C * Cᴴ).charpoly.rootMultiplicity (↑a : ℂ) := by rw [h_rm_pow_X_ne_zero]
      _ = ((Polynomial.X ^ Fintype.card (Fin m) : Polynomial ℂ) * (C *
          Cᴴ).charpoly).rootMultiplicity (↑a : ℂ) := by
            rw [Polynomial.rootMultiplicity_mul h_prod_ne_zero_CC]
      _ = ((Polynomial.X ^ Fintype.card (Fin n) : Polynomial ℂ) * (Cᴴ *
          C).charpoly).rootMultiplicity (↑a : ℂ) := by
            rw [h_charpoly]
      _ = (Polynomial.X ^ Fintype.card (Fin n) : Polynomial ℂ).rootMultiplicity (↑a : ℂ) +
          (Cᴴ * C).charpoly.rootMultiplicity (↑a : ℂ) := by
            rw [Polynomial.rootMultiplicity_mul h_prod_ne_zero_CtC]
      _ = 0 + (Cᴴ * C).charpoly.rootMultiplicity (↑a : ℂ) := by rw [h_rm_pow_X_ne_zero]
      _ = (Cᴴ * C).charpoly.rootMultiplicity (↑a : ℂ) := by ring

/-- Corollary: The multisets of eigenvalues of CC† and C†C, when restricted
to non-zero values, are equal. This is stated in terms of the filter operation. -/
theorem eigenvalues_mul_conjTranspose_filter_eq [NeZero n] [NeZero m]
    (C : Matrix (Fin n) (Fin m) ℂ) :
    (Finset.univ.val.map (mul_conjTranspose_isHermitian C).eigenvalues).filter (· ≠ 0) =
    (Finset.univ.val.map (conjTranspose_mul_isHermitian C).eigenvalues).filter (· ≠ 0) := by
  exact nonzero_eigenvalues_conjTranspose_mul_eq C

/-!
## Tensor Product Eigenvalues

For Hermitian matrices, the eigenvalues of A ⊗ B are products of eigenvalues.
-/

/-- Tensor product (Kronecker product) of Hermitian matrices is Hermitian.

Note: Matrix.kroneckerMap produces Matrix (Fin n × Fin m) (Fin n × Fin m),
not Matrix (Fin (n*m)) (Fin (n*m)). -/
theorem kronecker_isHermitian
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.kroneckerMap (· * ·) A B).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_kronecker, hA.eq, hB.eq]

/-!
### Helper Lemmas for Kronecker Eigenvalues

We establish key properties of Kronecker products that support the eigenvalue theorem.
-/

/-- Power of Kronecker product: (A ⊗ B)^k = A^k ⊗ B^k.

This follows from the mixed-product property: (A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD).
By induction, (A ⊗ B)^k = A^k ⊗ B^k. -/
lemma kronecker_pow
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) (k : ℕ) :
    (Matrix.kroneckerMap (· * ·) A B) ^ k =
    Matrix.kroneckerMap (· * ·) (A ^ k) (B ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    -- 1 ⊗ 1 = 1 for the product index type
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [kroneckerMap_apply, one_apply, Prod.mk.injEq]
    by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;> simp [h1, h2]
  | succ k ih =>
    rw [pow_succ, pow_succ, pow_succ, ih]
    -- Use mixed-product property: (A^k ⊗ B^k) * (A ⊗ B) = (A^k * A) ⊗ (B^k * B)
    exact (mul_kronecker_mul (A ^ k) A (B ^ k) B).symm

/-- Trace of Kronecker power: trace((A ⊗ B)^k) = trace(A^k) * trace(B^k).

Combines `kronecker_pow` with `trace_kronecker`. -/
lemma trace_kronecker_pow
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) (k : ℕ) :
    ((Matrix.kroneckerMap (· * ·) A B) ^ k).trace = (A ^ k).trace * (B ^ k).trace := by
  rw [kronecker_pow, trace_kronecker]

/-- For Hermitian matrices, trace(A^k) = ∑ᵢ λᵢ^k where λᵢ are eigenvalues.

This connects traces to eigenvalue power sums.

**Proof sketch**: Use spectral theorem A = U * diagonal(λ) * U†, then
(A)^k = U * diagonal(λ)^k * U†, and trace is invariant under similarity. -/
lemma trace_pow_eq_sum_eigenvalues_pow
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i : ℂ) ^ k := by
  -- Use spectral theorem: A = U * D * U† where D = diagonal(eigenvalues)
  have h_spec := hA.spectral_theorem
  -- Let U = eigenvectorUnitary and D = diagonal(eigenvalues)
  set U := hA.eigenvectorUnitary.val with hU_def
  set D := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) with hD_def
  -- Spectral theorem: A = U * D * U†
  have h_A_eq : A = U * D * U† := by
    rw [hU_def, hD_def]
    -- spectral_theorem uses Unitary.conjStarAlgAut, need to convert
    have h_spec' := h_spec
    simp only [Unitary.conjStarAlgAut_apply] at h_spec'
    exact h_spec'
  -- Show A^k = U * D^k * U† by induction
  have h_pow_eq : A ^ k = U * D ^ k * U† := by
    rw [h_A_eq]
    induction k with
    | zero =>
      simp only [pow_zero]
      -- 1 = U * 1 * U† = U * U† = 1 (since U is unitary)
      have h_UU : U * U† = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
      rw [Matrix.mul_one, h_UU]
    | succ k ih =>
      rw [pow_succ, ih]
      -- (U * D^k * U†) * (U * D * U†) = U * D^k * (U† * U) * D * U†
      -- = U * D^k * 1 * D * U† = U * D^(k+1) * U†
      have h_UU : U† * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
      -- Associate: (U * D^k * U†) * (U * D * U†) = U * D^k * (U† * U) * D * U†
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (U * D ^ k)]
      -- Now: U * D^k * ((U† * U) * D * U†) = U * D^k * (1 * D * U†) = U * D^k * D * U†
      rw [← Matrix.mul_assoc U†, h_UU, Matrix.one_mul]
      -- Now: U * D^k * D * Uᴴ = U * (D^k * D) * Uᴴ = U * D^(k+1) * Uᴴ
      -- Associate D^k and D together, then use pow_succ
      -- Normalize both sides with associativity, then use congr to show D^k * D = D^(k+1)
      simp only [Matrix.mul_assoc] at *
      congr 1
      rw [← Matrix.mul_assoc, ← pow_succ]
  -- trace(A^k) = trace(U * D^k * U†) = trace(D^k * U† * U) = trace(D^k)
  have h_trace_eq : (A ^ k).trace = (D ^ k).trace := by
    rw [h_pow_eq]
    -- trace(U * D^k * U†) = trace(D^k * U† * U) by trace_mul_cycle
    rw [Matrix.trace_mul_cycle]
    have h_UU : U† * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rw [h_UU, Matrix.one_mul]
  -- trace(D^k) = ∑ (diagonal entries)^k = ∑ λᵢ^k
  have h_D_trace : (D ^ k).trace = ∑ i, (hA.eigenvalues i : ℂ) ^ k := by
    rw [hD_def]
    -- D^k = diagonal(λ)^k = diagonal(λ^k)
    -- Prove by induction that diagonal(λ)^k = diagonal(λ^k)
    have h_diag_pow : ∀ k, (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) ^ k =
        Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ)) ^ k) := by
      intro k
      induction k with
      | zero => simp [pow_zero, Matrix.diagonal_one]
      | succ k ih =>
        rw [pow_succ, ih]
        ext i j
        simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
        by_cases h : i = j <;> simp [h, pow_succ]
    rw [h_diag_pow k]
    -- trace(diagonal(λ^k)) = ∑ λᵢ^k
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_apply]
    rw [Finset.sum_congr rfl]
    intro i _
    simp
  -- Combine: trace(A^k) = trace(D^k) = ∑ λᵢ^k
  rw [h_trace_eq, h_D_trace]

/-- Power sums of Kronecker eigenvalues equal products of power sums.

For all k: ∑ (eigenvalues of A⊗B)^k = (∑ λᵢ^k)(∑ μⱼ^k)

This follows from:
1. `trace_kronecker_pow`: trace((A ⊗ B)^k) = trace(A^k) * trace(B^k)
2. `trace_pow_eq_sum_eigenvalues_pow`: trace(M^k) = ∑ (eigenvalues)^k

**Key insight**: Since power sums determine multisets (Newton's identities),
this equality of power sums implies the multisets are equal. -/
lemma eigenvalue_power_sum_kronecker
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : ℕ) :
    ∑ p : Fin n × Fin m, ((kronecker_isHermitian A B hA hB).eigenvalues p : ℂ) ^ k =
    (∑ i, (hA.eigenvalues i : ℂ) ^ k) * (∑ j, (hB.eigenvalues j : ℂ) ^ k) := by
  -- PROOF STRATEGY:
  -- Step 1: ∑ eigenvalues(A⊗B)^k = trace((A ⊗ B)^k)  [trace_pow_eq_sum_eigenvalues_pow]
  -- Step 2: trace((A ⊗ B)^k) = trace(A^k) * trace(B^k)  [trace_kronecker_pow]
  -- Step 3: trace(A^k) = ∑ λᵢ^k, trace(B^k) = ∑ μⱼ^k  [trace_pow_eq_sum_eigenvalues_pow]
  -- Step 4: Combine to get the result
  -- Step 1: Connect eigenvalue power sum to trace for Kronecker product
  -- The proof is identical to trace_pow_eq_sum_eigenvalues_pow, just with product index type
  set AB := Matrix.kroneckerMap (· * ·) A B with h_AB_def
  have h_kron : AB.IsHermitian := kronecker_isHermitian A B hA hB
  -- Use the same spectral theorem approach as trace_pow_eq_sum_eigenvalues_pow
  -- The structure is identical: AB = U * D * U†, so AB^k = U * D^k * U†,
  -- and trace(AB^k) = trace(D^k) = ∑ eigenvalues^k
  have h_lhs : ∑ p : Fin n × Fin m, (h_kron.eigenvalues p : ℂ) ^ k = (AB ^ k).trace := by
    -- Apply the same proof as trace_pow_eq_sum_eigenvalues_pow
    -- The key is that IsHermitian.trace_eq_sum_eigenvalues works for any index type
    -- and the power relationship follows from the spectral theorem in the same way
    have h_spec := h_kron.spectral_theorem
    set U := h_kron.eigenvectorUnitary.val with hU_def
    set D := Matrix.diagonal (fun p => (h_kron.eigenvalues p : ℂ)) with hD_def
    have h_AB_eq : AB = U * D * U† := by
      rw [hU_def, hD_def]
      simp only [Unitary.conjStarAlgAut_apply] at h_spec
      exact h_spec
    -- Show AB^k = U * D^k * U† (same proof as trace_pow_eq_sum_eigenvalues_pow)
    have h_pow_eq : AB ^ k = U * D ^ k * U† := by
      rw [h_AB_eq]
      induction k with
      | zero =>
        simp only [pow_zero]
        have h_UU : U * U† = 1 := Unitary.coe_mul_star_self h_kron.eigenvectorUnitary
        rw [Matrix.mul_one, h_UU]
      | succ k ih =>
        rw [pow_succ, ih]
        -- Now goal: (U * D^k * U†) * (U * D * U†) = U * D^(k+1) * U†
        -- Note: (U * D * U†) is already in the goal, no need to rewrite h_AB_eq
        have h_UU : U† * U = 1 := Unitary.coe_star_mul_self h_kron.eigenvectorUnitary
        -- Associate: (U * D^k * U†) * (U * D * U†) = U * D^k * (U† * U) * D * U†
        rw [← Matrix.mul_assoc, Matrix.mul_assoc (U * D ^ k)]
        -- Now: U * D^k * ((U† * U) * D * U†) = U * D^k * (1 * D * U†) = U * D^k * D * U†
        rw [← Matrix.mul_assoc U†, h_UU, Matrix.one_mul]
        -- Now: U * D^k * D * Uᴴ = U * (D^k * D) * Uᴴ = U * D^(k+1) * Uᴴ
        -- Associate D^k and D together, then use pow_succ
        -- Normalize both sides with associativity, then use congr to show D^k * D = D^(k+1)
        simp only [Matrix.mul_assoc] at *
        congr 1
        rw [← Matrix.mul_assoc, ← pow_succ]
    -- trace(AB^k) = trace(D^k) = ∑ eigenvalues^k
    have h_trace_eq : (AB ^ k).trace = (D ^ k).trace := by
      rw [h_pow_eq, Matrix.trace_mul_cycle]
      have h_UU : U† * U = 1 := Unitary.coe_star_mul_self h_kron.eigenvectorUnitary
      rw [h_UU, Matrix.one_mul]
    -- trace(D^k) = ∑ (diagonal entries)^k = ∑ eigenvalues^k
    have h_D_trace : (D ^ k).trace = ∑ p : Fin n × Fin m, (h_kron.eigenvalues p : ℂ) ^ k := by
      rw [hD_def]
      -- D^k = diagonal(λ)^k = diagonal(λ^k) (same proof as before)
      have h_diag_pow : ∀ k, (Matrix.diagonal (fun p => (h_kron.eigenvalues p : ℂ))) ^ k =
          Matrix.diagonal (fun p => ((h_kron.eigenvalues p : ℂ)) ^ k) := by
        intro k
        induction k with
        | zero => simp [pow_zero, Matrix.diagonal_one]
        | succ k ih =>
          rw [pow_succ, ih]
          ext p q
          simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
          by_cases h : p = q <;> simp [h, pow_succ]
      rw [h_diag_pow k]
      simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_apply]
      rw [Finset.sum_congr rfl]
      intro p _
      simp
    -- Combine: trace(AB^k) = trace(D^k) = ∑ eigenvalues^k
    rw [h_trace_eq, h_D_trace]
  -- Step 2: Trace of Kronecker power equals product of traces
  have h_trace : (AB ^ k).trace = (A ^ k).trace * (B ^ k).trace :=
    trace_kronecker_pow A B k
  -- Step 3: Traces equal eigenvalue power sums
  have h_rhs_A := trace_pow_eq_sum_eigenvalues_pow A hA k
  have h_rhs_B := trace_pow_eq_sum_eigenvalues_pow B hB k
  -- Combine: ∑ ev(A⊗B)^k = trace((A⊗B)^k) = trace(A^k) * trace(B^k) = (∑ λ^k)(∑ μ^k)
  rw [h_lhs, h_trace, h_rhs_A, h_rhs_B]

/-- **Tensor product eigenvalue theorem**: the eigenvalue multiset of the Kronecker product
`A ⊗ B` of Hermitian matrices equals the multiset of pairwise products `λᵢ · μⱼ` of the
eigenvalues of `A` and `B`.

Proved via the spectral decompositions `A = U_A · diag(λ_A) · U_A†`,
`B = U_B · diag(λ_B) · U_B†`: the Kronecker product `U_A ⊗ U_B` is unitary and conjugates
`A ⊗ B` to `diag(λ_A) ⊗ diag(λ_B) = diag(λ_A,i · λ_B,j)` (`Matrix.diagonal_kronecker_diagonal`),
so `A ⊗ B` and this diagonal matrix are similar and hence share a characteristic polynomial;
reading off the roots of both sides gives the eigenvalue multiset equality. -/
lemma eigenvalue_kronecker_multiset_eq {n m : ℕ} [NeZero n] [NeZero m]
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Finset.univ : Finset (Fin n × Fin m)).val.map
      (fun k => (kronecker_isHermitian A B hA hB).eigenvalues k) =
    (Finset.univ : Finset (Fin n × Fin m)).val.map
      (fun ⟨i, j⟩ => hA.eigenvalues i * hB.eigenvalues j) := by
  -- PROOF VIA CHARACTERISTIC POLYNOMIALS
  -- Strategy: Show the charpolys of A⊗B and diagonal(products) are equal,
  -- which implies their eigenvalue multisets (via roots) are equal.
  --
  -- Let's abbreviate notation
  set AB := kroneckerMap (· * ·) A B with hAB_def
  set hAB := kronecker_isHermitian A B hA hB with hAB_herm_def
  -- Diagonal matrices from spectral theorem
  set D_A := diagonal ((fun r : ℝ => (r : ℂ)) ∘ hA.eigenvalues) with hD_A_def
  set D_B := diagonal ((fun r : ℝ => (r : ℂ)) ∘ hB.eigenvalues) with hD_B_def
  set D_AB := diagonal (fun p : Fin n × Fin m =>
    (hA.eigenvalues p.1 : ℂ) * (hB.eigenvalues p.2 : ℂ)) with hD_AB_def
  -- Unitary matrices from spectral theorem
  set U_A := hA.eigenvectorUnitary.val with hU_A_def
  set U_B := hB.eigenvectorUnitary.val with hU_B_def
  -- Step: D_A ⊗ D_B = D_AB (diagonal of products)
  have h_diag_kron : kroneckerMap (· * ·) D_A D_B = D_AB := by
    rw [hD_A_def, hD_B_def, hD_AB_def, diagonal_kronecker_diagonal]; rfl
  -- Spectral decompositions
  have h_A_spec : A = U_A * D_A * U_A.conjTranspose := by
    have h := hA.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h; exact h
  have h_B_spec : B = U_B * D_B * U_B.conjTranspose := by
    have h := hB.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h; exact h
  -- A⊗B = (U_A⊗U_B) * (D_A⊗D_B) * (U_A†⊗U_B†)
  have h_AB_decomp : AB = kroneckerMap (· * ·) U_A U_B *
      kroneckerMap (· * ·) D_A D_B *
      kroneckerMap (· * ·) U_A.conjTranspose U_B.conjTranspose := by
    rw [hAB_def, h_A_spec, h_B_spec, mul_kronecker_mul, mul_kronecker_mul]
  have h_star_left : (kroneckerMap (· * ·) U_A U_B).conjTranspose *
      kroneckerMap (· * ·) U_A U_B = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul]
    have hU_A' : U_A.conjTranspose * U_A = 1 :=
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
    have hU_B' : U_B.conjTranspose * U_B = 1 :=
      Unitary.coe_star_mul_self hB.eigenvectorUnitary
    rw [hU_A', hU_B', one_kronecker_one]
  -- Cyclic invariance of the characteristic polynomial cancels the unitary factors.
  have h_charpoly_eq : AB.charpoly = D_AB.charpoly := by
    rw [h_AB_decomp, h_diag_kron, ← conjTranspose_kronecker, charpoly_mul_comm,
      ← Matrix.mul_assoc, h_star_left, one_mul]
  -- D_AB is Hermitian (diagonal with real entries on diagonal)
  have h_D_AB_herm : D_AB.IsHermitian := by
    rw [hD_AB_def, isHermitian_diagonal_iff]
    intro ⟨i, j⟩
    -- Need: IsSelfAdjoint ((hA.eigenvalues i : ℂ) * (hB.eigenvalues j : ℂ))
    -- star (x * y) = star x * star y, and for real r, star (r : ℂ) = r
    simp only [IsSelfAdjoint, star_mul', RCLike.star_def, Complex.conj_ofReal]
  -- Use roots_charpoly_eq_eigenvalues
  have h_roots_AB := hAB.roots_charpoly_eq_eigenvalues
  have h_roots_D_AB := h_D_AB_herm.roots_charpoly_eq_eigenvalues
  -- Equal charpolys → equal roots
  have h_roots_eq : Multiset.map ((RCLike.ofReal (K := ℂ)) ∘ hAB.eigenvalues) Finset.univ.val =
      Multiset.map ((RCLike.ofReal (K := ℂ)) ∘ h_D_AB_herm.eigenvalues) Finset.univ.val := by
    rw [← h_roots_AB, ← h_roots_D_AB, h_charpoly_eq]
  -- By injectivity of ofReal
  have h_inj : Function.Injective (RCLike.ofReal (K := ℂ)) := RCLike.ofReal_injective
  have h_eigenvalues_eq : Finset.univ.val.map hAB.eigenvalues =
      Finset.univ.val.map h_D_AB_herm.eigenvalues := by
    apply Multiset.map_injective h_inj
    simp only [Multiset.map_map] at h_roots_eq ⊢; exact h_roots_eq
  -- For diagonal matrix D_AB, eigenvalues = diagonal entries (as multiset)
  have h_D_AB_charpoly : D_AB.charpoly = ∏ p : Fin n × Fin m,
      (Polynomial.X - Polynomial.C ((hA.eigenvalues p.1 : ℂ) * (hB.eigenvalues p.2 : ℂ))) := by
    rw [hD_AB_def, charpoly_diagonal]
  have h_D_AB_roots : D_AB.charpoly.roots = Finset.univ.val.map
      (fun p : Fin n × Fin m => (hA.eigenvalues p.1 : ℂ) * (hB.eigenvalues p.2 : ℂ)) := by
    rw [h_D_AB_charpoly]
    have h := Polynomial.roots_prod
      (fun p : Fin n × Fin m => Polynomial.X - Polynomial.C ((hA.eigenvalues p.1 : ℂ) *
          (hB.eigenvalues p.2 : ℂ)))
      Finset.univ
    have hne : ∏ p : Fin n × Fin m, (Polynomial.X - Polynomial.C ((hA.eigenvalues p.1 : ℂ) *
        (hB.eigenvalues p.2 : ℂ))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_; intros; exact Polynomial.X_sub_C_ne_zero _
    specialize h hne
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton] at h
    exact h
  have h_diag_ev : Finset.univ.val.map h_D_AB_herm.eigenvalues =
      Finset.univ.val.map (fun (p : Fin n × Fin m) => hA.eigenvalues p.1 * hB.eigenvalues p.2) := by
    -- h_roots_D_AB : D_AB.charpoly.roots = Multiset.map (RCLike.ofReal ∘ h_D_AB_herm.eigenvalues)
    -- Finset.univ.val
    -- h_D_AB_roots : D_AB.charpoly.roots = Finset.univ.val.map (fun p => (hA.eigenvalues p.1 : ℂ) *
    -- (hB.eigenvalues p.2 : ℂ))
    -- First, show the complex products equal the ofReal of real products
    have h_products_real : ∀ p : Fin n × Fin m,
        (hA.eigenvalues p.1 : ℂ) * (hB.eigenvalues p.2 : ℂ) =
        RCLike.ofReal (hA.eigenvalues p.1 * hB.eigenvalues p.2) := fun p =>
      (Complex.ofReal_mul _ _).symm
    -- Now combine the two characterizations of D_AB.charpoly.roots
    have h_eq : Multiset.map ((RCLike.ofReal (K := ℂ)) ∘ h_D_AB_herm.eigenvalues) Finset.univ.val =
        Multiset.map (fun p : Fin n × Fin m => (RCLike.ofReal (K := ℂ)) (hA.eigenvalues p.1 *
            hB.eigenvalues p.2)) Finset.univ.val := by
      rw [← h_roots_D_AB, h_D_AB_roots]
      congr 1; ext p; exact h_products_real p
    have h_eq' : Multiset.map (RCLike.ofReal (K := ℂ)) (Multiset.map h_D_AB_herm.eigenvalues
        Finset.univ.val) =
        Multiset.map (RCLike.ofReal (K := ℂ)) (Multiset.map (fun (p : Fin n × Fin m) =>
            hA.eigenvalues p.1 * hB.eigenvalues p.2) Finset.univ.val) := by
      simp only [Multiset.map_map]; exact h_eq
    exact Multiset.map_injective h_inj h_eq'
  rw [h_eigenvalues_eq, h_diag_ev]

/-- **Tensor product eigenvalue theorem**: If A has eigenvalues {λᵢ} and B has
eigenvalues {μⱼ}, then A ⊗ B has eigenvalues {λᵢ · μⱼ}. See eigenvalue_kronecker_multiset_eq
for the proof justification.
-/
theorem eigenvalues_kronecker [NeZero n] [NeZero m]
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hermitianEigenvaluesProd (Matrix.kroneckerMap (· * ·) A B) (kronecker_isHermitian A B hA hB) =
    (hermitianEigenvalues A hA).bind (fun ev_a =>
      (hermitianEigenvalues B hB).map (· * ev_a)) := by
  -- Use eigenvalue_kronecker_multiset_eq and show the bind form equals the map form
  unfold hermitianEigenvaluesProd hermitianEigenvalues
  -- LHS: Finset.univ.val.map (kronecker.eigenvalues)
  -- RHS: (univ.val.map hA.eigenvalues).bind (λ a => (univ.val.map hB.eigenvalues).map (· * a))
  -- By eigenvalue_kronecker_multiset_eq:
  --   LHS = univ.val.map (λ ⟨i,j⟩ => hA.eigenvalues i * hB.eigenvalues j)
  -- We need: (map f).bind (λ a => (map g).map (· * a)) = map (λ ⟨i,j⟩ => f i * g j) (for products)
  rw [eigenvalue_kronecker_multiset_eq A B hA hB]
  -- Now need: map (λ ⟨i,j⟩ => λ_i * μ_j) univ = (map λ).bind (λ a => (map μ).map (· * a))
  -- Prove this by rewriting the RHS
  symm
  rw [← Finset.univ_product_univ, Finset.product_val]
  -- Now have: univ.val ×ˢ univ.val which is Multiset.product
  change ((Multiset.map hA.eigenvalues Finset.univ.val).bind fun ev_a =>
      Multiset.map (fun x => x * ev_a) (Multiset.map hB.eigenvalues Finset.univ.val)) =
    Multiset.map (fun x => match x with | (i, j) => hA.eigenvalues i * hB.eigenvalues j)
      (Multiset.product Finset.univ.val Finset.univ.val)
  rw [Multiset.product.eq_1, Multiset.map_bind, Multiset.bind_map]
  simp only [Multiset.map_map, Function.comp_apply]
  congr 1
  ext i
  rw [show (fun x : Fin m => hB.eigenvalues x * hA.eigenvalues i) =
      (fun x : Fin m => hA.eigenvalues i * hB.eigenvalues x) from
      funext (fun x => mul_comm (hB.eigenvalues x) (hA.eigenvalues i))]

/-- Sum over eigenvalues of a Kronecker product equals the double sum over the factor
eigenvalues: `∑ₖ f(eigenvalue_k(A⊗B)) = ∑ᵢ ∑ⱼ f(λᵢ · μⱼ)`, for any `f : ℝ → ℝ`.

Immediate from the multiset equality `eigenvalue_kronecker_multiset_eq`: summing the same
function over equal multisets gives equal sums. Used in proving entropy additivity; see also
`InfoTheory.VonNeumannEntropy.vonNeumannEntropy_tensor_additive`. -/
theorem sum_eigenvalues_kronecker [NeZero n] [NeZero m]
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) :
    ∑ k : Fin n × Fin m, f ((kronecker_isHermitian A B hA hB).eigenvalues k) =
    ∑ i : Fin n, ∑ j : Fin m, f (hA.eigenvalues i * hB.eigenvalues j) := by
  -- Use eigenvalue_kronecker_multiset_eq to equate the multisets
  have h_eq := eigenvalue_kronecker_multiset_eq A B hA hB
  -- Convert RHS from double sum to single sum over product type
  rw [← Fintype.sum_prod_type']
  -- Now both sides are single sums over Fin n × Fin m
  -- LHS: ∑ k, f(eigenvalues k)
  -- RHS: ∑ k, f(λ_k.1 * μ_k.2)
  -- Convert to Multiset.sum form
  rw [← Finset.sum_map_val, ← Finset.sum_map_val]
  -- Now show: map (f ∘ eigenvalues) univ = map (f ∘ product) univ
  congr 1
  -- Use the fact that if two multisets s and t are equal,
  -- then map g s = map g t
  have h_map : ∀ (g : ℝ → ℝ) (s t : Multiset ℝ), s = t → Multiset.map g s = Multiset.map g t := by
    intros g s t h; rw [h]
  -- Rewrite using h_eq
  conv_lhs => rw [show (fun k => f ((kronecker_isHermitian A B hA hB).eigenvalues k)) =
      f ∘ (fun k => (kronecker_isHermitian A B hA hB).eigenvalues k) from rfl]
  conv_rhs => rw [show (fun x : Fin n × Fin m => f (hA.eigenvalues x.1 * hB.eigenvalues x.2)) =
      f ∘ (fun x : Fin n × Fin m => hA.eigenvalues x.1 * hB.eigenvalues x.2) from rfl]
  simp only [← Multiset.map_map]
  rw [h_eq]

/-!
## Rank Equalities (Available from Mathlib)

These are already in Mathlib and confirm that CC† and C†C have the same rank:
- `Matrix.rank_conjTranspose_mul_self`
- `Matrix.rank_self_mul_conjTranspose`

The rank equals the number of non-zero eigenvalues, which is consistent with
our theorem `nonzero_eigenvalues_conjTranspose_mul_eq`.
-/

/-!
## Entry-wise Conjugation Preserves Eigenvalues for Hermitian Matrices

For Hermitian matrices, entry-wise conjugation (M.map star) preserves eigenvalues
because it equals the transpose (which preserves the characteristic polynomial).
-/

/-- For a Hermitian matrix H, its transpose equals its entry-wise conjugate.
    This follows from H = H† = (H.map star)ᵀ, so Hᵀ = H.map star. -/
lemma hermitian_transpose_eq_map_star {n : Type*}
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    Hᵀ = H.map star := by
  have h : Hᴴ = H := hH.eq
  ext i j
  have hij := congrFun (congrFun h j) i
  simp only [conjTranspose_apply] at hij
  simp only [transpose_apply, map_apply]
  exact hij.symm

/-- Entry-wise conjugation of a Hermitian matrix is Hermitian.
    Since H.map star = Hᵀ for Hermitian H, and transpose preserves Hermiticity. -/
lemma map_star_isHermitian {n : Type*}
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    (H.map star).IsHermitian := by
  rw [← hermitian_transpose_eq_map_star H hH]
  exact hH.transpose

/-- For a Hermitian matrix, the characteristic polynomial is preserved by entry-wise conjugation.
    This follows from charpoly(H.map star) = charpoly(Hᵀ) = charpoly(H). -/
lemma charpoly_map_star_hermitian {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    (H.map star).charpoly = H.charpoly := by
  rw [← hermitian_transpose_eq_map_star H hH]
  exact charpoly_transpose H

/-- For a Hermitian matrix, entry-wise conjugation preserves the eigenvalue multiset.
    Since the characteristic polynomials are equal, the roots (eigenvalues) are equal. -/
lemma eigenvalues_map_star_eq {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    let hH' := map_star_isHermitian H hH
    Finset.univ.val.map hH'.eigenvalues = Finset.univ.val.map hH.eigenvalues := by
  intro hH'
  have h_charpoly_eq := charpoly_map_star_hermitian H hH
  have h_roots_H := hH.roots_charpoly_eq_eigenvalues
  have h_roots_H' := hH'.roots_charpoly_eq_eigenvalues
  have h_roots_eq : (H.map star).charpoly.roots = H.charpoly.roots := by rw [h_charpoly_eq]
  have h_eq : Multiset.map (RCLike.ofReal (K := ℂ) ∘ hH'.eigenvalues) Finset.univ.val =
      Multiset.map (RCLike.ofReal (K := ℂ) ∘ hH.eigenvalues) Finset.univ.val := by
    rw [← h_roots_H', ← h_roots_H, h_roots_eq]
  have h_eq' : Multiset.map (fun r : ℝ => (r : ℂ))
        (Multiset.map hH'.eigenvalues Finset.univ.val) =
      Multiset.map (fun r : ℝ => (r : ℂ))
        (Multiset.map hH.eigenvalues Finset.univ.val) := by
    rw [Multiset.map_map, Multiset.map_map]
    exact h_eq
  have h_inj : Function.Injective (fun r : ℝ => (r : ℂ)) := Complex.ofReal_injective
  exact Multiset.map_injective h_inj h_eq'

/-- For two Hermitian matrices that are equal, their eigenvalues are pointwise equal. -/
lemma eigenvalues_eq_of_matrix_eq {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h_eq : A = B) :
    ∀ i, hA.eigenvalues i = hB.eigenvalues i := by
  subst h_eq
  intro i
  rfl

/-!
## Real-exponent (CFC) Kronecker power factorization

The natural-power Kronecker identity `(A ⊗ B) ^ k = A ^ k ⊗ B ^ k`
(`kronecker_pow`) extends to *real* exponents via the continuous functional
calculus: for positive semidefinite `A`, `B`,
`(A ⊗ B) ^ x = A ^ x ⊗ B ^ x` (`kronecker_cfcRpow`), where `^ x` is
`CFC.rpow`. The proof routes through the spectral decomposition
`A = U_A · D_A · U_A†`: writing `cfc f` of a Hermitian matrix as conjugation of a
diagonal by the eigenvector unitary, the Kronecker factorizes because the
eigenvector unitary of `A ⊗ B` may be taken to be `U_A ⊗ U_B` and the diagonal
`D_A ⊗ D_B` carries entries `λ_i μ_j` with `(λ_i μ_j) ^ x = λ_i ^ x μ_j ^ x`.

The collision-trace corollary `trace_kronecker_cfcRpow_collision`,
`tr[(A ⊗ C) ^ a · (B ⊗ D) ^ b] = tr[A ^ a · B ^ b] · tr[C ^ a · D ^ b]`, is the
spectral-theory ingredient behind tensor-power moment-generating-function
factorizations.
-/

/-- A real diagonal matrix (entries `RCLike.ofReal ∘ d`) is Hermitian. -/
lemma isHermitian_diagonal_ofReal {ι : Type*} [DecidableEq ι] (d : ι → ℝ) :
    (diagonal (fun i => (d i : ℂ))).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  rw [IsSelfAdjoint]; ext i; simp

/-- Each diagonal entry of a real diagonal matrix is in its real spectrum. -/
lemma diagonal_ofReal_mem_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (i : ι) :
    (d i) ∈ spectrum ℝ (diagonal (fun i => (d i : ℂ))) := by
  rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ) (a := diagonal (fun i => (d i : ℂ))) (r := d i),
    spectrum_diagonal]
  exact ⟨i, by simp [Complex.coe_algebraMap]⟩

/-- The diagonal continuous functional calculus star algebra homomorphism: the map
sending a continuous function `g` on the spectrum to the diagonal matrix
`diagonal (RCLike.ofReal ∘ g ∘ d)`. By uniqueness of the continuous functional
calculus this agrees with `cfcHom` (see `cfc_diagonal_ofReal`). -/
noncomputable def diagonalCfcHom {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    C(spectrum ℝ (diagonal (fun i => (d i : ℂ))), ℝ) →⋆ₐ[ℝ] Matrix ι ι ℂ where
  toFun g := diagonal fun i => ((g ⟨d i, diagonal_ofReal_mem_spectrum d i⟩ : ℝ) : ℂ)
  map_zero' := by simp [← diagonal_zero]
  map_one' := by simp [← diagonal_one]
  map_mul' f g := by simp [diagonal_mul_diagonal]
  map_add' f g := by simp [← diagonal_add]
  commutes' r := by
    ext i j
    have hL : (((algebraMap ℝ C(spectrum ℝ (diagonal (fun i => (d i : ℂ))), ℝ)) r)
        ⟨d i, diagonal_ofReal_mem_spectrum d i⟩ : ℝ) = r := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [diagonal_apply]
    simp only [hL]
    rw [Matrix.algebraMap_eq_diagonal, diagonal_apply]
    by_cases h : i = j <;> simp [h, Pi.algebraMap_apply]
  map_star' f := by
    rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    ext i
    simp

@[simp]
lemma diagonalCfcHom_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ)
    (g : C(spectrum ℝ (diagonal (fun i => (d i : ℂ))), ℝ)) :
    diagonalCfcHom d g
      = diagonal fun i => ((g ⟨d i, diagonal_ofReal_mem_spectrum d i⟩ : ℝ) : ℂ) := rfl

lemma diagonalCfcHom_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    Continuous (diagonalCfcHom d) := by
  apply continuous_matrix
  intro i j
  by_cases h : i = j
  · subst h
    simp only [diagonalCfcHom_apply, diagonal_apply_eq]
    exact Complex.continuous_ofReal.comp (continuous_eval_const _)
  · simp only [diagonalCfcHom_apply, diagonal_apply_ne _ h]
    exact continuous_const

lemma diagonalCfcHom_id {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    diagonalCfcHom d ((ContinuousMap.id ℝ).restrict (spectrum ℝ (diagonal (fun i => (d i : ℂ)))))
      = diagonal (fun i => (d i : ℂ)) := by
  rw [diagonalCfcHom_apply]; rfl

/-- The continuous functional calculus of a real diagonal matrix is the diagonal of
`f` applied entrywise: `cfc f (diagonal (↑·d)) = diagonal (↑·(f ∘ d))`. -/
lemma cfc_diagonal_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  have hsa : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := isHermitian_diagonal_ofReal d
  have hcont : ContinuousOn f (spectrum ℝ (diagonal (fun i => (d i : ℂ)))) :=
    (diagonal (fun i => (d i : ℂ))).finite_real_spectrum.continuousOn f
  rw [cfc_apply f (diagonal (fun i => (d i : ℂ))) hsa hcont]
  have huniq : cfcHom hsa = diagonalCfcHom d :=
    cfcHom_eq_of_continuous_of_map_id hsa (diagonalCfcHom d) (diagonalCfcHom_continuous d)
      (diagonalCfcHom_id d)
  rw [huniq, diagonalCfcHom_apply]
  rfl

/-- Conjugation `x ↦ u · x · u†` by a unitary matrix is continuous. -/
lemma conjStarAlgAut_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : unitary (Matrix ι ι ℂ)) :
    Continuous (conjStarAlgAut ℂ (Matrix ι ι ℂ) u) := by
  have heq : (conjStarAlgAut ℂ (Matrix ι ι ℂ) u : Matrix ι ι ℂ → _)
      = fun x => (u : Matrix ι ι ℂ) * x * star (u : Matrix ι ι ℂ) := by
    ext x; simp [conjStarAlgAut_apply]
  rw [show (conjStarAlgAut ℂ (Matrix ι ι ℂ) u : Matrix ι ι ℂ → Matrix ι ι ℂ) = _ from heq]
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/-- The continuous functional calculus is equivariant under unitary conjugation:
`cfc f (u · A · u†) = u · cfc f A · u†`. -/
lemma cfc_conjStarAlgAut {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (u : unitary (Matrix ι ι ℂ)) (f : ℝ → ℝ) :
    cfc f (conjStarAlgAut ℂ _ u A) = conjStarAlgAut ℂ _ u (cfc f A) :=
  (StarAlgHomClass.map_cfc (conjStarAlgAut ℂ _ u) f A
    (hf := (A.finite_real_spectrum).continuousOn f) (hφ := conjStarAlgAut_continuous u)
    (ha := hA) (hφa := by cfc_tac)).symm

/-- Spectral form of `cfc f A` for a Hermitian matrix: conjugation of the diagonal
`diagonal (↑·(f ∘ eigenvalues))` by the eigenvector unitary. -/
lemma cfc_eq_conjStarAlgAut_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))) := by
  have hofReal : (RCLike.ofReal ∘ hA.eigenvalues : ι → ℂ)
      = fun i => ((hA.eigenvalues i : ℝ) : ℂ) := rfl
  conv_lhs => rw [hA.spectral_theorem, hofReal]
  rw [cfc_conjStarAlgAut _ (isHermitian_diagonal_ofReal hA.eigenvalues) hA.eigenvectorUnitary f,
    cfc_diagonal_ofReal]

/-- `CFC.rpow` of a positive semidefinite matrix in spectral form: conjugation of
the diagonal `diagonal (↑·(eigenvalues ^ x))` by the eigenvector unitary. -/
lemma posSemidef_cfcRpow_eq_conjStarAlgAut_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (x : ℝ) :
    A ^ x = conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
      (diagonal (fun i => ((hA.1.eigenvalues i ^ x : ℝ) : ℂ))) := by
  rw [CFC.rpow_eq_cfc_real (a := A) (y := x) hA.nonneg,
    cfc_eq_conjStarAlgAut_diagonal A hA.1 (fun t => t ^ x)]

/-- Unitary conjugation of a diagonal matrix is the eigenprojector sum: for the
eigenvector unitary `U = hA.eigenvectorUnitary` and any scalar family `d`,
`U · diagonal d · U† = ∑ i, d i • |u_i⟩⟨u_i|` with `u_i = (hA.eigenvectorBasis i).ofLp`.
This is the entrywise generalization of `isHermitian_eq_sum_smul_vecMulVec` to an
arbitrary diagonal (here used at `d i = eigenvalues i ^ x`). -/
lemma conjStarAlgAut_eigenvectorUnitary_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (d : ι → ℂ) :
    conjStarAlgAut ℂ _ hA.eigenvectorUnitary (diagonal d) =
      ∑ i, d i • Matrix.vecMulVec ((hA.eigenvectorBasis i).ofLp)
        (star ((hA.eigenvectorBasis i).ofLp)) := by
  classical
  rw [conjStarAlgAut_apply]
  set U : Matrix ι ι ℂ := (↑hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU_def
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  rw [show star ((hA.eigenvectorBasis i).ofLp) b
        = star ((hA.eigenvectorBasis i).ofLp b) from rfl]
  rw [hU_def, hA.eigenvectorUnitary_apply a i, hA.eigenvectorUnitary_apply b i]
  ring

/-- **Real-exponent spectral expansion of a PSD matrix.** For positive semidefinite
`A` and real `x`, the `CFC.rpow` power is the eigenvalue-`x` weighted sum of the
rank-one eigenprojectors `|u_i⟩⟨u_i|`:
`A ^ x = ∑ i, (eigenvalues i ^ x : ℂ) • |u_i⟩⟨u_i|`.
This is the real-exponent analogue of `isHermitian_eq_sum_smul_vecMulVec`. -/
lemma posSemidef_cfcRpow_eq_sum_smul_vecMulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (x : ℝ) :
    A ^ x = ∑ i, ((hA.1.eigenvalues i ^ x : ℝ) : ℂ) •
        Matrix.vecMulVec ((hA.1.eigenvectorBasis i).ofLp)
          (star ((hA.1.eigenvectorBasis i).ofLp)) := by
  rw [posSemidef_cfcRpow_eq_conjStarAlgAut_diagonal hA x,
    conjStarAlgAut_eigenvectorUnitary_diagonal hA.1
      (fun i => ((hA.1.eigenvalues i ^ x : ℝ) : ℂ))]

/-- Kronecker of two unitary matrices, bundled as a unitary element over the product
index type. -/
noncomputable def kroneckerUnitary {n m : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ)
    (v : Matrix.unitaryGroup (Fin m) ℂ) :
    unitary (Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :=
  ⟨(u : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (v : Matrix (Fin m) (Fin m) ℂ),
    Matrix.kronecker_mem_unitary u.2 v.2⟩

/-- Conjugation by a Kronecker unitary splits over the Kronecker product:
`(U ⊗ V) · (X ⊗ Y) · (U ⊗ V)† = (U · X · U†) ⊗ (V · Y · V†)`. -/
lemma conjStarAlgAut_kronecker {n m : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ)
    (v : Matrix.unitaryGroup (Fin m) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    conjStarAlgAut ℂ _ (kroneckerUnitary u v) (X ⊗ₖ Y)
      = (conjStarAlgAut ℂ _ u X) ⊗ₖ (conjStarAlgAut ℂ _ v Y) := by
  simp only [conjStarAlgAut_apply]
  change ((u : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (v : Matrix (Fin m) (Fin m) ℂ)) * (X ⊗ₖ Y)
      * star ((u : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (v : Matrix (Fin m) (Fin m) ℂ))
    = ((u : Matrix (Fin n) (Fin n) ℂ) * X * star (u : Matrix (Fin n) (Fin n) ℂ))
        ⊗ₖ ((v : Matrix (Fin m) (Fin m) ℂ) * Y * star (v : Matrix (Fin m) (Fin m) ℂ))
  rw [star_eq_conjTranspose, conjTranspose_kronecker, Matrix.mul_kronecker_mul,
    Matrix.mul_kronecker_mul, star_eq_conjTranspose, star_eq_conjTranspose]

/-- **Real-exponent Kronecker / CFC power factorization.** For positive semidefinite
matrices `A`, `B`, the `CFC.rpow` real power distributes over the Kronecker product:
`(A ⊗ B) ^ x = A ^ x ⊗ B ^ x`. This is the real-exponent analogue of the
natural-power identity `kronecker_pow`. -/
theorem kronecker_cfcRpow {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (x : ℝ) :
    (A ⊗ₖ B) ^ x = (A ^ x) ⊗ₖ (B ^ x) := by
  set UA := hA.1.eigenvectorUnitary
  set UB := hB.1.eigenvectorUnitary
  set eA := hA.1.eigenvalues with heA
  set eB := hB.1.eigenvalues with heB
  have hAB_eq : A ⊗ₖ B = conjStarAlgAut ℂ _ (kroneckerUnitary UA UB)
      ((diagonal (fun i => ((eA i : ℝ) : ℂ))) ⊗ₖ (diagonal (fun j => ((eB j : ℝ) : ℂ)))) := by
    rw [conjStarAlgAut_kronecker]
    conv_lhs => rw [hA.1.spectral_theorem, hB.1.spectral_theorem]
    rfl
  have hDD_herm : ((diagonal (fun i => ((eA i : ℝ) : ℂ)))
      ⊗ₖ (diagonal (fun j => ((eB j : ℝ) : ℂ)))).IsHermitian := by
    rw [Matrix.diagonal_kronecker_diagonal]
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      rw [IsSelfAdjoint]; ext mn; simp)
  rw [CFC.rpow_eq_cfc_real (a := A ⊗ₖ B) (y := x) (hA.kronecker hB).nonneg, hAB_eq,
    cfc_conjStarAlgAut _ hDD_herm (kroneckerUnitary UA UB) (fun t => t ^ x),
    Matrix.diagonal_kronecker_diagonal]
  rw [show (fun mn : Fin n × Fin m => ((eA mn.1 : ℝ) : ℂ) * ((eB mn.2 : ℝ) : ℂ))
      = (fun mn : Fin n × Fin m => (((eA mn.1 * eB mn.2 : ℝ)) : ℂ)) by
    funext mn; push_cast; ring, cfc_diagonal_ofReal]
  rw [show (fun mn : Fin n × Fin m => (((eA mn.1 * eB mn.2) ^ x : ℝ) : ℂ))
      = (fun mn : Fin n × Fin m => ((eA mn.1 ^ x : ℝ) : ℂ) * ((eB mn.2 ^ x : ℝ) : ℂ)) by
    funext mn
    rw [Real.mul_rpow (hA.eigenvalues_nonneg mn.1) (hB.eigenvalues_nonneg mn.2)]
    push_cast; ring]
  rw [← Matrix.diagonal_kronecker_diagonal (fun i => ((eA i ^ x : ℝ) : ℂ))
      (fun j => ((eB j ^ x : ℝ) : ℂ)), conjStarAlgAut_kronecker,
    ← posSemidef_cfcRpow_eq_conjStarAlgAut_diagonal hA x,
    ← posSemidef_cfcRpow_eq_conjStarAlgAut_diagonal hB x]

/-- **Collision-trace factorization at real exponents.** For positive semidefinite
`A, B` (index `Fin n`) and `C, D` (index `Fin m`), the collision trace of the
Kronecker products factorizes:
`tr[(A ⊗ C) ^ a · (B ⊗ D) ^ b] = tr[A ^ a · B ^ b] · tr[C ^ a · D ^ b]`. -/
theorem trace_kronecker_cfcRpow_collision {n m : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ} {C D : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
    (a b : ℝ) :
    (((A ⊗ₖ C) ^ a) * ((B ⊗ₖ D) ^ b)).trace
      = ((A ^ a) * (B ^ b)).trace * ((C ^ a) * (D ^ b)).trace := by
  rw [kronecker_cfcRpow hA hC a, kronecker_cfcRpow hB hD b,
    ← Matrix.mul_kronecker_mul (A ^ a) (B ^ b) (C ^ a) (D ^ b), Matrix.trace_kronecker]

/-- **Collision trace as an eigenprojector double sum.** For positive semidefinite
`A, B` on `Fin n` with eigendata `(eA, u)`, `(eB, v)`, the real-exponent collision
trace expands over the rank-one eigenprojectors:
`tr[A ^ a · B ^ b] = ∑ i ∑ j (eA_i ^ a) · (eB_j ^ b) · tr[|u_i⟩⟨u_i| · |v_j⟩⟨v_j|]`.
This is the operator-trace side of Renner's spectral MGF sum: combined with the
reference/block spectral resolutions it identifies the collision trace with the
eigenvalue/overlap triple sum. -/
lemma trace_cfcRpow_mul_cfcRpow_eq_eigen_double_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) (a b : ℝ) :
    ((A ^ a) * (B ^ b)).trace =
      ∑ i, ∑ j, ((hA.1.eigenvalues i ^ a : ℝ) : ℂ) * ((hB.1.eigenvalues j ^ b : ℝ) : ℂ)
        * (Matrix.vecMulVec ((hA.1.eigenvectorBasis i).ofLp)
              (star ((hA.1.eigenvectorBasis i).ofLp))
            * Matrix.vecMulVec ((hB.1.eigenvectorBasis j).ofLp)
              (star ((hB.1.eigenvectorBasis j).ofLp))).trace := by
  rw [posSemidef_cfcRpow_eq_sum_smul_vecMulVec hA a,
    posSemidef_cfcRpow_eq_sum_smul_vecMulVec hB b, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]

end Math.SpectralTheory

-- Foreign namespace stubs moved to their home modules:
-- QuantumMetrics → Quantum/Metrics/TraceNorm.lean
-- QuantumMeasurement → InfoTheory/Measurement/POVM.lean
-- QuantumDeFinetti → InfoTheory/DeFinetti/Theorem.lean
-- RelativeEntropy → InfoTheory/RelativeEntropy/Basic.lean
-- QuantumInfo → Quantum/Operators/Types.lean
