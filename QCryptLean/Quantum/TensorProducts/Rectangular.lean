import QCryptLean.Quantum.Matrix.Reindex
import QCryptLean.Quantum.TensorProducts.CastDim

/-!
# Rectangular register algebra: the Kronecker tensor and the dimension cast, as matrices

`Quantum.TensorProducts.Op.tensor` is square-only, and `Quantum.Operators.Op.castDim` moves an
operator between registers of equal dimension but is not itself a matrix. A step that changes a
register's dimension — a local instrument with a dimension-changing branch, a register
regrouping inside a Kraus product — needs both operations in *rectangular* form. This module
supplies them and their laws.

The tensor uses `finProdFinEquiv` to index each product register, with the **first** factor as
the high digit. Section 1 records the corresponding index formulas.

## Main definitions

* `Quantum.TensorProducts.tensorRect`: the **rectangular Kronecker tensor**
  `Matrix (Fin a) (Fin b) ℂ → Matrix (Fin c) (Fin d) ℂ → Matrix (Fin (a * c)) (Fin (b * d)) ℂ`.
  On square arguments it is definitionally `Op.tensor` (`tensorRect_square`).
* `Quantum.TensorProducts.castRect`: the rectangular numeric-diagonal matrix from `Fin n` to
  `Fin m`. When `n = m`, it realizes the value-preserving register relabelling as a Kraus
  operator, so a register regrouping can sit inside a Kraus product.

## Main statements

* `tensorRect_mul`, `tensorRect_conjTranspose`, `tensorRect_one`: simultaneous multiplication,
  adjoints, and identities of the two tensor factors, so a chain of local operations stays a
  product across a cut.
* `tensorRect_sum_left`/`_right`, `tensorRect_smul_left`/`_right`, `tensorRect_zero_left`/`_right`:
  bilinearity, in both factors.
* `tensorRect_single_left_eq_sum`, `tensorRect_single_right_eq_sum`: a tensor with a matrix unit
  is the corresponding `Matrix.single`-sum, placed in one block; `tensorRect_single_one_eq_sum`,
  `tensorRect_one_single_eq_sum` and `sum_single_finProdFinEquiv_apply` are the identity cases,
  and `finProdFinEquiv_fixed_left_sum_double_single_apply` evaluates a general block at a fixed
  first-factor index.
* `castRect_conj`: **a dimension cast is a Kraus conjugation**, and `castRect_isometry` says it
  never disturbs a completeness relation. `conj_mul_conj` composes two conjugations, which is
  what lets a cast be absorbed into a neighbouring Kraus operator.
* `eq_tensorRect_single_of_support` and `partialIsometry_submatrix_of_support`: a matrix whose
  support sits over a single index pair of the second factor **is** a rectangular tensor with a
  matrix unit, and a partial isometry stays one on its slice. `tensorRect_single_right_injective`
  and `tensorRect_single_left_injective`: the factor paired with a fixed matrix unit is
  determined.
  `not_isTensorRect_of_support_separated` shows that per-row/per-column designation alone does
  not ensure a tensor factorization.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators Kronecker

noncomputable section

namespace Quantum.TensorProducts

/-! ## 1. The numeral convention

`finProdFinEquiv (a, b) = b + n · a`, so the **first** factor is the high digit (`divNat`). -/

theorem finProdFinEquiv_symm_fst_val {m n : ℕ} (i : Fin (m * n)) :
    (((finProdFinEquiv.symm i).1 : Fin m) : ℕ) = (i : ℕ) / n := rfl

theorem finProdFinEquiv_symm_snd_val {m n : ℕ} (i : Fin (m * n)) :
    (((finProdFinEquiv.symm i).2 : Fin n) : ℕ) = (i : ℕ) % n := rfl

theorem finProdFinEquiv_val {m n : ℕ} (a : Fin m) (b : Fin n) :
    ((finProdFinEquiv (a, b) : Fin (m * n)) : ℕ) = (b : ℕ) + n * (a : ℕ) := rfl

/-! ## 2. The rectangular Kronecker tensor

Mathlib's `Matrix.kroneckerMap` is already rectangular; only the two `reindex`es to the numeral
index differ from `Op.tensor`. -/

/-- **The rectangular Kronecker tensor.** `tensorRect A B` acts on the product register
`Fin (a * c)` indexed by `finProdFinEquiv`, with `A` on the **first** (high-digit, `divNat`)
factor. On square arguments it is definitionally `Op.tensor` (`tensorRect_square`). -/
def tensorRect {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin c) (Fin d) ℂ) :
    Matrix (Fin (a * c)) (Fin (b * d)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kroneckerMap (· * ·) A B)

/-- Entry of a rectangular Kronecker tensor, split along `finProdFinEquiv`. The rectangular
counterpart of `Op_tensor_apply_finProd`. -/
theorem tensorRect_apply {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
    (B : Matrix (Fin c) (Fin d) ℂ) (i : Fin (a * c)) (j : Fin (b * d)) :
    tensorRect A B i j =
      A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
        B (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  simp only [tensorRect, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

/-- The entry of a rectangular tensor at a pair index, with the `finProdFinEquiv` round trip
already discharged. -/
theorem tensorRect_apply_pair {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
    (B : Matrix (Fin c) (Fin d) ℂ) (i : Fin a) (l : Fin c) (j : Fin b) (m : Fin d) :
    tensorRect A B (finProdFinEquiv (i, l)) (finProdFinEquiv (j, m)) = A i j * B l m := by
  rw [tensorRect_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- On square arguments the rectangular tensor **is** `Op.tensor`, definitionally. This is what
lets a two-party statement proved with `tensorRect` be consumed by the existing square
`Op.tensor` API without a cast. -/
@[simp] theorem tensorRect_square {n m : ℕ} (A : Op n) (B : Op m) :
    tensorRect A B = Op.tensor A B := rfl

/-- Conjugate transpose distributes over the rectangular tensor. -/
theorem tensorRect_conjTranspose {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
    (B : Matrix (Fin c) (Fin d) ℂ) :
    (tensorRect A B)ᴴ = tensorRect Aᴴ Bᴴ := by
  simp only [tensorRect, Matrix.conjTranspose_reindex, Matrix.conjTranspose_kronecker]

/-- The rectangular tensor is multiplicative: composing two local steps party-by-party is the
same as composing their joint lifts. This is the fact that makes a chain of local operations
stay a product across the cut. -/
theorem tensorRect_mul {a b c d e f : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
    (B : Matrix (Fin c) (Fin d) ℂ) (C : Matrix (Fin b) (Fin e) ℂ)
    (D : Matrix (Fin d) (Fin f) ℂ) :
    tensorRect A B * tensorRect C D = tensorRect (A * C) (B * D) := by
  simp only [tensorRect, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]

/-- The rectangular tensor of identities is the identity. -/
@[simp] theorem tensorRect_one {a b : ℕ} :
    tensorRect (1 : Op a) (1 : Op b) = (1 : Op (a * b)) :=
  Op.tensor_one

/-- The rectangular tensor is additive in its left factor, over a finite index. -/
theorem tensorRect_sum_left {a b c d : ℕ} {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin c) (Fin d) ℂ) :
    ∑ x, tensorRect (A x) B = tensorRect (∑ x, A x) B := by
  ext i j
  simp only [Matrix.sum_apply, tensorRect_apply, ← Finset.sum_mul]

/-- The rectangular tensor is additive in its right factor, over a finite index. -/
theorem tensorRect_sum_right {a b c d : ℕ} {κ : Type*} [Fintype κ]
    (A : Matrix (Fin a) (Fin b) ℂ) (B : κ → Matrix (Fin c) (Fin d) ℂ) :
    ∑ x, tensorRect A (B x) = tensorRect A (∑ x, B x) := by
  ext i j
  simp only [Matrix.sum_apply, tensorRect_apply, ← Finset.mul_sum]

/-- The rectangular tensor is homogeneous in its left factor. -/
theorem tensorRect_smul_left {a b c d : ℕ} (z : ℂ) (A : Matrix (Fin a) (Fin b) ℂ)
    (B : Matrix (Fin c) (Fin d) ℂ) : tensorRect (z • A) B = z • tensorRect A B := by
  ext i j
  simp only [tensorRect_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]

/-- The rectangular tensor is homogeneous in its right factor. -/
theorem tensorRect_smul_right {a b c d : ℕ} (z : ℂ) (A : Matrix (Fin a) (Fin b) ℂ)
    (B : Matrix (Fin c) (Fin d) ℂ) : tensorRect A (z • B) = z • tensorRect A B := by
  ext i j
  simp only [tensorRect_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- A vanishing left factor kills the rectangular tensor. -/
@[simp] theorem tensorRect_zero_left {a b c d : ℕ} (B : Matrix (Fin c) (Fin d) ℂ) :
    tensorRect (0 : Matrix (Fin a) (Fin b) ℂ) B = 0 := by
  ext i j
  simp [tensorRect_apply]

/-- A vanishing right factor kills the rectangular tensor. -/
@[simp] theorem tensorRect_zero_right {a b c d : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) :
    tensorRect A (0 : Matrix (Fin c) (Fin d) ℂ) = 0 := by
  ext i j
  simp [tensorRect_apply]

/-! ### The rectangular tensor against the computational basis -/

/-- The column of a left lift `A ⊗ 1` at a product basis index: whatever `A` does to the first
factor, the second index rides through untouched. -/
theorem tensorRect_one_right_col {p q c : ℕ} (A : Matrix (Fin q) (Fin p) ℂ) (a : Fin p)
    (b : Fin c) (u : Fin q) (z : ℂ) (h : ∀ i, A i a = if i = u then z else 0)
    (i : Fin (q * c)) :
    tensorRect A (1 : Matrix (Fin c) (Fin c) ℂ) i (finProdFinEquiv (a, b)) =
      if i = finProdFinEquiv (u, b) then z else 0 := by
  obtain ⟨⟨i1, i2⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [tensorRect_apply]
  simp only [Equiv.symm_apply_apply, Matrix.one_apply, h i1, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq]
  by_cases h1 : i1 = u <;> by_cases h2 : i2 = b <;> simp [h1, h2]

/-- The column of a right lift `1 ⊗ B` at a product basis index. -/
theorem tensorRect_one_left_col {p q c : ℕ} (B : Matrix (Fin q) (Fin p) ℂ) (a : Fin c)
    (b : Fin p) (u : Fin q) (z : ℂ) (h : ∀ i, B i b = if i = u then z else 0)
    (i : Fin (c * q)) :
    tensorRect (1 : Matrix (Fin c) (Fin c) ℂ) B i (finProdFinEquiv (a, b)) =
      if i = finProdFinEquiv (a, u) then z else 0 := by
  obtain ⟨⟨i1, i2⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [tensorRect_apply]
  simp only [Equiv.symm_apply_apply, Matrix.one_apply, h i2, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq]
  by_cases h1 : i1 = a <;> by_cases h2 : i2 = u <;> simp [h1, h2]

/-- **A tensor with a matrix unit on the second factor is a `Matrix.single`-sum**, one term per
entry of `M`, all placed in the `(d, d')` block. -/
theorem tensorRect_single_right_eq_sum {N N' D D' : ℕ} (d : Fin D) (d' : Fin D')
    (M : Matrix (Fin N) (Fin N') ℂ) :
    tensorRect M (Matrix.single d d' (1 : ℂ)) =
      ∑ a : Fin N, ∑ b : Fin N',
        Matrix.single (finProdFinEquiv (a, d)) (finProdFinEquiv (b, d')) (M a b) := by
  ext p q
  obtain ⟨⟨p₁, p₂⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨q₁, q₂⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [tensorRect_apply, Matrix.sum_apply, Finset.sum_eq_single p₁]
  · rw [Matrix.sum_apply, Finset.sum_eq_single q₁]
    · simp only [Matrix.single_apply, Equiv.symm_apply_apply,
        EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, true_and]
      by_cases h₂ : d = p₂ <;> by_cases h₂' : d' = q₂ <;> simp [h₂, h₂']
    · intro b _ hb
      exact Matrix.single_apply_of_col_ne _ _
        (fun hc => hb (congrArg Prod.fst (finProdFinEquiv.injective hc))) _
    · intro h
      exact absurd (Finset.mem_univ q₁) h
  · intro a _ ha
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    exact Matrix.single_apply_of_row_ne
      (fun hc => ha (congrArg Prod.fst (finProdFinEquiv.injective hc))) _ _ _
  · intro h
    exact absurd (Finset.mem_univ p₁) h

/-- The mirror of `tensorRect_single_right_eq_sum`, with the matrix unit on the first factor. -/
theorem tensorRect_single_left_eq_sum {N N' D D' : ℕ} (d : Fin D) (d' : Fin D')
    (M : Matrix (Fin N) (Fin N') ℂ) :
    tensorRect (Matrix.single d d' (1 : ℂ)) M =
      ∑ a : Fin N, ∑ b : Fin N',
        Matrix.single (finProdFinEquiv (d, a)) (finProdFinEquiv (d', b)) (M a b) := by
  ext p q
  obtain ⟨⟨p₁, p₂⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨q₁, q₂⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [tensorRect_apply, Matrix.sum_apply, Finset.sum_eq_single p₂]
  · rw [Matrix.sum_apply, Finset.sum_eq_single q₂]
    · simp only [Matrix.single_apply, Equiv.symm_apply_apply,
        EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, and_true]
      by_cases h₁ : d = p₁ <;> by_cases h₁' : d' = q₁ <;> simp [h₁, h₁']
    · intro b _ hb
      exact Matrix.single_apply_of_col_ne _ _
        (fun hc => hb (congrArg Prod.snd (finProdFinEquiv.injective hc))) _
    · intro h
      exact absurd (Finset.mem_univ q₂) h
  · intro a _ ha
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    exact Matrix.single_apply_of_row_ne
      (fun hc => ha (congrArg Prod.snd (finProdFinEquiv.injective hc))) _ _ _
  · intro h
    exact absurd (Finset.mem_univ p₂) h

/-- **A matrix unit tensored with the identity** is the sum, over the second-factor index, of the
matrix units that fix that index: `|a⟩⟨b| ⊗ 1 = ∑ r, |a, r⟩⟨b, r|`. -/
theorem tensorRect_single_one_eq_sum {D D' e : ℕ} (a : Fin D) (b : Fin D') :
    tensorRect (Matrix.single a b (1 : ℂ)) (1 : Op e) =
      ∑ r : Fin e, Matrix.single (finProdFinEquiv (a, r)) (finProdFinEquiv (b, r)) (1 : ℂ) := by
  rw [tensorRect_single_left_eq_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single r (fun s _ hs => by rw [Matrix.one_apply_ne' hs, Matrix.single_zero])
    (fun h => absurd (Finset.mem_univ r) h), Matrix.one_apply_eq]

/-- The mirror of `tensorRect_single_one_eq_sum`: `1 ⊗ |a⟩⟨b| = ∑ r, |r, a⟩⟨r, b|`. -/
theorem tensorRect_one_single_eq_sum {D D' e : ℕ} (a : Fin D) (b : Fin D') :
    tensorRect (1 : Op e) (Matrix.single a b (1 : ℂ)) =
      ∑ r : Fin e, Matrix.single (finProdFinEquiv (r, a)) (finProdFinEquiv (r, b)) (1 : ℂ) := by
  rw [tensorRect_single_right_eq_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single r (fun s _ hs => by rw [Matrix.one_apply_ne' hs, Matrix.single_zero])
    (fun h => absurd (Finset.mem_univ r) h), Matrix.one_apply_eq]

/-- Entries of `∑ r, |a, r⟩⟨b, r| = |a⟩⟨b| ⊗ 1`: one exactly where the second-factor indices agree
and the first-factor indices are `a` and `b`. -/
theorem sum_single_finProdFinEquiv_apply {D D' e : ℕ} (a : Fin D) (b : Fin D')
    (p : Fin (D * e)) (q : Fin (D' * e)) :
    (∑ r : Fin e, Matrix.single (finProdFinEquiv (a, r)) (finProdFinEquiv (b, r)) (1 : ℂ)) p q =
      if p.modNat = q.modNat then (if a = p.divNat ∧ b = q.divNat then 1 else 0) else 0 := by
  rw [← tensorRect_single_one_eq_sum, tensorRect_apply, finProdFinEquiv_symm_apply,
    finProdFinEquiv_symm_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases hmod : p.modNat = q.modNat <;> by_cases hab : a = p.divNat ∧ b = q.divNat <;>
    simp [hmod, hab]

/-- Entries of a block `∑ r, ∑ r', F r r' |out, r⟩⟨out, r'|` at the fixed first-factor index
`out`: at `(p, q)` only the matrix unit carrying the second-factor indices of `p` and `q`
survives. -/
theorem finProdFinEquiv_fixed_left_sum_double_single_apply {outDim refDim : ℕ}
    (out : Fin outDim) (F : Fin refDim → Fin refDim → ℂ) (p q : Fin (outDim * refDim)) :
    (∑ r : Fin refDim, ∑ r' : Fin refDim,
      Matrix.single (finProdFinEquiv (out, r)) (finProdFinEquiv (out, r')) (F r r')) p q =
      Matrix.single (finProdFinEquiv (out, p.modNat))
        (finProdFinEquiv (out, q.modNat)) (F p.modNat q.modNat) p q := by
  classical
  have hmod : ∀ r : Fin refDim, (finProdFinEquiv (out, r)).modNat = r := fun r =>
    congrArg Prod.snd
      ((finProdFinEquiv_symm_apply _).symm.trans (finProdFinEquiv.symm_apply_apply (out, r)))
  have hne : ∀ {r : Fin refDim} {x : Fin (outDim * refDim)}, r ≠ x.modNat →
      finProdFinEquiv (out, r) ≠ x := fun hr hx => hr (by rw [← hx, hmod])
  simp only [Matrix.sum_apply]
  rw [Finset.sum_eq_single p.modNat
    (fun r _ hr => Finset.sum_eq_zero fun r' _ => by simp [hne hr])
    (fun h => absurd (Finset.mem_univ _) h)]
  exact Finset.sum_eq_single q.modNat (fun r' _ hr' => by simp [hne hr'])
    (fun h => absurd (Finset.mem_univ _) h)

/-! ## 3. Composing rectangular conjugations -/

/-- Conjugation by a composite Kraus operator, in the order the induction produces it. -/
theorem conj_mul_conj {a b c : ℕ} (Km : Matrix (Fin b) (Fin a) ℂ) (Lm : Matrix (Fin c) (Fin b) ℂ)
    (ρ : Op a) : Lm * (Km * ρ * Kmᴴ) * Lmᴴ = (Lm * Km) * ρ * (Lm * Km)ᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-! ## 4. The dimension cast as a matrix

A register regrouping such as `(a·b)·c → a·(b·c)` is value-preserving: it changes the type of the
index but not its numeral. For arbitrary `n` and `m`, `castRect n m` is the rectangular matrix with
ones where the row and column numerals agree and zeros elsewhere. Under a dimension equality it is
the corresponding relabelling matrix, so the cast can appear inside a Kraus product. -/

/-- **The rectangular numeric diagonal.** `castRect n m` has a one at `(i,j)` exactly when the
row and column have the same natural-number value. For equal dimensions it is the matrix of the
value-preserving relabelling. -/
def castRect (n m : ℕ) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

@[simp] theorem castRect_apply (n m : ℕ) (i : Fin m) (j : Fin n) :
    castRect n m i j = if (i : ℕ) = (j : ℕ) then 1 else 0 := rfl

@[simp] theorem castRect_self (n : ℕ) : castRect n n = 1 := by
  ext i j
  simp [castRect, Matrix.one_apply, Fin.ext_iff]

/-- Left multiplication by an equal-dimension `castRect` relabels the row index. -/
theorem castRect_mul {n m p : ℕ} (h : n = m) (M : Matrix (Fin n) (Fin p) ℂ) :
    castRect n m * M = M.submatrix (Fin.cast h.symm) id := by
  subst h
  ext i j
  simp [Matrix.submatrix_apply]

/-- Right multiplication by an equal-dimension `castRect` relabels the column index. -/
theorem mul_castRect {n m p : ℕ} (h : n = m) (M : Matrix (Fin p) (Fin m) ℂ) :
    M * castRect n m = M.submatrix id (Fin.cast h) := by
  subst h
  ext i j
  simp [Matrix.submatrix_apply]

@[simp] theorem castRect_conjTranspose (n m : ℕ) : (castRect n m)ᴴ = castRect m n := by
  ext i j
  simp [castRect, Matrix.conjTranspose_apply, eq_comm]

/-- Equal-dimension numeric-diagonal relabellings compose. -/
theorem castRect_comp {n m p : ℕ} (h : n = m) (h' : m = p) :
    castRect m p * castRect n m = castRect n p := by
  subst h; subst h'; simp

/-- A dimension cast is an isometry, so it never changes the completeness relation of a Kraus
family it is composed into. -/
theorem castRect_isometry {n m : ℕ} (h : n = m) : (castRect n m)ᴴ * castRect n m = 1 := by
  subst h; simp

/-- A dimension cast is conjugation by the value-preserving rectangular identity. -/
theorem castRect_conj {n m : ℕ} (h : n = m) (ρ : Op n) :
    castRect n m * ρ * (castRect n m)ᴴ = Op.castDim h ρ := by
  subst h
  simp [Op.castDim]

/-- The linear dimension cast is conjugation by its equal-dimension relabelling matrix. -/
theorem castDimLinear_apply_eq_conj {n m : ℕ} (h : n = m) (ρ : Op n) :
    Op.castDimLinear h ρ = castRect n m * ρ * (castRect n m)ᴴ := (castRect_conj h ρ).symm

/-- A cast on the second factor alone is a cast of the whole register. -/
theorem tensorRect_one_castRect {a b b' : ℕ} (h : b = b') :
    tensorRect (1 : Op a) (castRect b b') = castRect (a * b) (a * b') := by
  subst h
  rw [castRect_self, tensorRect_one, castRect_self]

/-! ## 5. Recognizing a tensor product from its support

A matrix on `Fin (n * a) × Fin (m * b)` whose nonzero entries all sit over **one** index pair
`(p₀, q₀)` of the second factor is the rectangular tensor of its `(p₀, q₀)` slice with the matrix
unit `|p₀⟩⟨q₀|`. The proof is elementary entrywise matrix algebra. Its operator-theoretic
context is the Stinespring/Kraus formalism in Watrous, *The Theory of Quantum Information* (2018)
§2.2, and Paulsen, *Completely Bounded Maps and Operator Algebras* (2002) Ch. 4; neither reference
states this exact finite-matrix support lemma.

The single-pair hypothesis cannot be weakened to *per-row and per-column* designation functions
`p = f i`, `q = g j`: `not_isTensorRect_of_support_separated` exhibits a partial isometry obeying
that weaker condition which is not a rectangular tensor at all. -/

/-- **A matrix supported over one index pair of the second factor is a tensor with a matrix
unit.** Pure support algebra: no isometry, positivity or nonzero-dimension hypothesis. -/
theorem eq_tensorRect_single_of_support {n m a b : ℕ}
    (V : Matrix (Fin (n * a)) (Fin (m * b)) ℂ) (p₀ : Fin a) (q₀ : Fin b)
    (hsupp : ∀ (i : Fin n) (j : Fin m) (p : Fin a) (q : Fin b),
      V (finProdFinEquiv (i, p)) (finProdFinEquiv (j, q)) ≠ 0 → p = p₀ ∧ q = q₀) :
    V = tensorRect (V.submatrix (fun i => finProdFinEquiv (i, p₀))
      (fun j => finProdFinEquiv (j, q₀))) (Matrix.single p₀ q₀ (1 : ℂ)) := by
  ext x y
  obtain ⟨⟨i, p⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j, q⟩, rfl⟩ := finProdFinEquiv.surjective y
  rw [tensorRect_apply_pair, Matrix.submatrix_apply, Matrix.single_apply]
  by_cases hp : p = p₀
  · by_cases hq : q = q₀
    · subst hp; subst hq; simp
    · rw [ite_eq_right fun hc => hq hc.2.symm, mul_zero]
      by_contra hne
      exact hq (hsupp i j p q hne).2
  · rw [ite_eq_right fun hc => hp hc.1.symm, mul_zero]
    by_contra hne
    exact hp (hsupp i j p q hne).1

/-- The left factor of a tensor with a fixed matrix unit is determined. -/
theorem tensorRect_single_right_injective {n m a b : ℕ} (p₀ : Fin a) (q₀ : Fin b)
    {W W' : Matrix (Fin n) (Fin m) ℂ}
    (h : tensorRect W (Matrix.single p₀ q₀ (1 : ℂ)) =
      tensorRect W' (Matrix.single p₀ q₀ (1 : ℂ))) : W = W' := by
  ext i j
  have := congrFun₂ h (finProdFinEquiv (i, p₀)) (finProdFinEquiv (j, q₀))
  rwa [tensorRect_apply_pair, tensorRect_apply_pair, Matrix.single_apply_same,
    mul_one, mul_one] at this

/-- The right factor of a tensor with a fixed matrix unit on the left is determined. The mirror of
`tensorRect_single_right_injective`. -/
theorem tensorRect_single_left_injective {n m a b : ℕ} (p₀ : Fin a) (q₀ : Fin b)
    {W W' : Matrix (Fin n) (Fin m) ℂ}
    (h : tensorRect (Matrix.single p₀ q₀ (1 : ℂ)) W =
      tensorRect (Matrix.single p₀ q₀ (1 : ℂ)) W') : W = W' := by
  ext i j
  have := congrFun₂ h (finProdFinEquiv (p₀, i)) (finProdFinEquiv (q₀, j))
  rwa [tensorRect_apply_pair, tensorRect_apply_pair, Matrix.single_apply_same,
    one_mul, one_mul] at this

/-- A matrix unit is a partial isometry. -/
theorem single_mul_conjTranspose_mul_self {a b : ℕ} (p₀ : Fin a) (q₀ : Fin b) :
    Matrix.single p₀ q₀ (1 : ℂ) * (Matrix.single p₀ q₀ (1 : ℂ))ᴴ *
        Matrix.single p₀ q₀ (1 : ℂ) = Matrix.single p₀ q₀ (1 : ℂ) := by
  simp [Matrix.conjTranspose_single]

/-- **The slice of a partial isometry supported over one index pair is a partial isometry.**
Together with `eq_tensorRect_single_of_support` this is the constant-block factorization: the
partial isometry is `W ⊗ |p₀⟩⟨q₀|` with `W` again a partial isometry. -/
theorem partialIsometry_submatrix_of_support {n m a b : ℕ}
    (V : Matrix (Fin (n * a)) (Fin (m * b)) ℂ) (hV : V * Vᴴ * V = V) (p₀ : Fin a) (q₀ : Fin b)
    (hsupp : ∀ (i : Fin n) (j : Fin m) (p : Fin a) (q : Fin b),
      V (finProdFinEquiv (i, p)) (finProdFinEquiv (j, q)) ≠ 0 → p = p₀ ∧ q = q₀) :
    let W := V.submatrix (fun i => finProdFinEquiv (i, p₀))
      (fun j => finProdFinEquiv (j, q₀))
    W * Wᴴ * W = W := by
  dsimp only
  set W := V.submatrix (fun i => finProdFinEquiv (i, p₀)) (fun j => finProdFinEquiv (j, q₀))
  set M := Matrix.single p₀ q₀ (1 : ℂ)
  have hfac : V = tensorRect W M := eq_tensorRect_single_of_support V p₀ q₀ hsupp
  refine tensorRect_single_right_injective p₀ q₀ ?_
  have key : tensorRect (W * Wᴴ * W) (M * Mᴴ * M) = tensorRect W M := by
    rw [← tensorRect_mul, ← tensorRect_mul, ← tensorRect_conjTranspose, ← hfac, hV]
  rwa [single_mul_conjTranspose_mul_self] at key

/-- The witness for `not_isTensorRect_of_support_separated`: `diag (1, 0, 0, 1)` on
`Fin (2 * 2)`, the orthogonal projection onto the two basis vectors whose two digits agree. -/
def diagAgreeProj : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℂ := Matrix.diagonal ![1, 0, 0, 1]

/-- **Per-row and per-column designation is not enough.** `diagAgreeProj` is a partial isometry
whose support obeys the separated condition `p = f i`, `q = g j` at `f = g = id`, but it is not a
rectangular tensor product of any two factors. Thus that displayed weakening does not imply the
factorization proved by `eq_tensorRect_single_of_support`. -/
theorem not_isTensorRect_of_support_separated :
    diagAgreeProj * diagAgreeProjᴴ * diagAgreeProj = diagAgreeProj ∧
      (∀ i j p q : Fin 2,
        diagAgreeProj (finProdFinEquiv (i, p)) (finProdFinEquiv (j, q)) ≠ 0 → p = i ∧ q = j) ∧
      ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, diagAgreeProj ≠ tensorRect A B := by
  -- `finProdFinEquiv (i, p) = p + 2 * i`: the first factor is the high digit.
  have e00 : finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)) = (0 : Fin (2 * 2)) := rfl
  have e01 : finProdFinEquiv ((0 : Fin 2), (1 : Fin 2)) = (1 : Fin (2 * 2)) := rfl
  have e10 : finProdFinEquiv ((1 : Fin 2), (0 : Fin 2)) = (2 : Fin (2 * 2)) := rfl
  have e11 : finProdFinEquiv ((1 : Fin 2), (1 : Fin 2)) = (3 : Fin (2 * 2)) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [diagAgreeProj, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp
  · intro i j p q
    fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases q <;>
      simp [diagAgreeProj, e00, e01, e10, e11]
  · intro A B hAB
    have entry : ∀ i p j q : Fin 2,
        diagAgreeProj (finProdFinEquiv (i, p)) (finProdFinEquiv (j, q)) = A i j * B p q :=
      fun i p j q => by rw [hAB, tensorRect_apply_pair]
    have h00 : A 0 0 * B 0 0 = 1 := by simpa [diagAgreeProj, e00] using (entry 0 0 0 0).symm
    have h11 : A 1 1 * B 1 1 = 1 := by simpa [diagAgreeProj, e11] using (entry 1 1 1 1).symm
    have h01 : A 0 0 * B 1 1 = 0 := by simpa [diagAgreeProj, e01] using (entry 0 1 0 1).symm
    rcases mul_eq_zero.mp h01 with h | h
    · simp [h] at h00
    · simp [h] at h11

/-- A rectangular first-register sandwich acts on each reference block separately. -/
lemma tensorRect_one_sandwich_block {b c r : ℕ}
    (E : Matrix (Fin c) (Fin b) ℂ) (A : Op (b * r))
    (i j : Fin c) (k l : Fin r) :
    (tensorRect E (1 : Op r) * A * (tensorRect E (1 : Op r))ᴴ)
        (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) =
      (E * (Matrix.of fun u v => A (finProdFinEquiv (u, k))
        (finProdFinEquiv (v, l))) * Eᴴ) i j := by
  rw [tensorRect_conjTranspose, Matrix.conjTranspose_one]
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type, tensorRect_apply, Equiv.symm_apply_apply]
  simp_rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type, Equiv.symm_apply_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.of_apply]

end Quantum.TensorProducts

end
