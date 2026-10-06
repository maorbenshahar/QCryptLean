import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Substate Extraction Infrastructure

Matrix reshaping helpers and the Douglas factorization theorem for the
Alberti-Uhlmann substate extraction.

## Main definitions

- `reshapeVec`: converts a vector `Fin (n * m) → ℂ` to `Matrix (Fin n) (Fin m) ℂ`
  using `finProdFinEquiv`
- `unreshapeVec`: the inverse, converting a matrix back to a vector

## Main results

- `partialTraceB_vecMulVec_eq_mul_conjTranspose`: partial trace of an outer product
  equals the matrix product `reshapeVec v * (reshapeVec v)ᴴ`
- `reshapeVec_one_tensor_mul_ket`: action by `1 ⊗ V` becomes right multiplication
  by `Vᵀ` after reshaping
- `matrix_douglas_factorization`: if `B B† ≥ Σ A_k A_k†` then `A_k = B C_k`
  with `Σ C_k C_k† ≤ I` (Douglas 1966, Fillmore-Williams 1971)
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

namespace Quantum.Channels

/-- Reshape a vector in `Fin (n * m) → ℂ` to a matrix `Matrix (Fin n) (Fin m) ℂ`
    using the canonical bijection `Fin n × Fin m ≃ Fin (n * m)`.
    Entry: `(reshapeVec v) i j = v (finProdFinEquiv (i, j))`. -/
def reshapeVec {n m : ℕ} (v : Fin (n * m) → ℂ) :
    Matrix (Fin n) (Fin m) ℂ :=
  Matrix.of fun i j => v (finProdFinEquiv (i, j))

/-- Inverse of `reshapeVec`: convert a matrix back to a vector. -/
def unreshapeVec {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℂ) :
    Fin (n * m) → ℂ :=
  fun p => M (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2

noncomputable section

@[simp]
theorem reshapeVec_apply {n m : ℕ} (v : Fin (n * m) → ℂ)
    (i : Fin n) (j : Fin m) :
    reshapeVec v i j = v (finProdFinEquiv (i, j)) := by
  simp [reshapeVec, Matrix.of_apply]

@[simp]
theorem unreshapeVec_apply {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) ℂ) (p : Fin (n * m)) :
    unreshapeVec M p =
      M (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 := by
  simp [unreshapeVec]

@[simp]
theorem reshapeVec_unreshapeVec {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) ℂ) :
    reshapeVec (unreshapeVec M) = M := by
  ext i j; simp [reshapeVec, unreshapeVec, Matrix.of_apply]

@[simp]
theorem unreshapeVec_reshapeVec {n m : ℕ}
    (v : Fin (n * m) → ℂ) :
    unreshapeVec (reshapeVec v) = v := by
  ext p
  simp only [unreshapeVec_apply, finProdFinEquiv_symm_apply,
    reshapeVec_apply]
  exact congr_arg v (finProdFinEquiv.apply_symm_apply p)

@[simp]
theorem reshapeVec_smul {n m : ℕ} (c : ℂ) (v : Fin (n * m) → ℂ) :
    reshapeVec (c • v) = c • reshapeVec v := by
  ext i j; simp [reshapeVec, Matrix.of_apply, Pi.smul_apply]

/-- Reshaping the action of `1 ⊗ V` on a ket gives right multiplication by
`Vᵀ` on the reshaped matrix of coefficients. -/
lemma reshapeVec_one_tensor_mul_ket {d : ℕ} (V : Op d) (ψ : Ket (d * d)) :
    reshapeVec ((Op.tensor (1 : Op d) V) * ψ).vec =
      reshapeVec ψ.vec * V.transpose := by
  ext i j
  calc
    reshapeVec ((Op.tensor (1 : Op d) V) * ψ).vec i j =
        ∑ p : Fin d × Fin d,
          ((if i = p.1 then 1 else 0) * V j p.2) * ψ.vec (finProdFinEquiv p) := by
      simp only [reshapeVec_apply, op_mul_ket_vec, Matrix.mulVec, dotProduct]
      rw [Fintype.sum_equiv finProdFinEquiv.symm _
        (fun p : Fin d × Fin d =>
          ((if i = p.1 then 1 else 0) * V j p.2) * ψ.vec (finProdFinEquiv p))
        (by
          intro x
          have hx : finProdFinEquiv (x.divNat, x.modNat) = x := by
            simpa [finProdFinEquiv_symm_apply] using finProdFinEquiv.apply_symm_apply x
          have hψx : ψ.vec x = ψ.vec (finProdFinEquiv (x.divNat, x.modNat)) := by
            rw [hx]
          by_cases hix : i = x.divNat
          · simp [Op.tensor, hix, hψx]
          · simp [Op.tensor, hix, hψx])]
    _ = ∑ b : Fin d, ψ.vec (finProdFinEquiv (i, b)) * V j b := by
      rw [Fintype.sum_prod_type]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = (reshapeVec ψ.vec * V.transpose) i j := by
      simp only [reshapeVec_apply, Matrix.mul_apply, Matrix.transpose_apply]

/-- Partial trace of an outer product equals the matrix product of
    reshaped vectors: `Tr_B(|v⟩⟨v|) = V * V†` where `V = reshapeVec v`. -/
theorem partialTraceB_vecMulVec_eq_mul_conjTranspose {n m : ℕ}
    (v : Fin (n * m) → ℂ) :
    partialTraceB (vecMulVec v (star v)) =
      reshapeVec v * (reshapeVec v)ᴴ := by
  ext i j
  simp only [partialTraceB, Matrix.of_apply, vecMulVec_apply,
    Pi.star_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, reshapeVec_apply]

/-- Partial trace of an outer product over the A-factor equals the matrix product of
    the transposed reshaped vector:
    `Tr_A(|v⟩⟨v|) = Vᵀ * (Vᵀ)†` where `V = reshapeVec v`. -/
theorem partialTraceA_vecMulVec_eq_transpose_mul_conjTranspose {n m : ℕ}
    (v : Fin (n * m) → ℂ) :
    partialTraceA (vecMulVec v (star v)) =
      (reshapeVec v)ᵀ * ((reshapeVec v)ᵀ)ᴴ := by
  ext i j
  simp only [partialTraceA, Matrix.of_apply, vecMulVec_apply,
    Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, reshapeVec_apply]

/-- Partial trace of a sum of outer products equals the sum of
    matrix products. -/
theorem partialTraceB_sum_vecMulVec_eq {n m r : ℕ}
    (v : Fin r → (Fin (n * m) → ℂ)) :
    partialTraceB (∑ k, vecMulVec (v k) (star (v k))) =
      ∑ k, reshapeVec (v k) * (reshapeVec (v k))ᴴ := by
  simp_rw [← partialTraceB_vecMulVec_eq_mul_conjTranspose]
  exact partialTraceB_finset_sum Finset.univ _

/-- Partial trace over the A-factor of a sum of outer products equals the sum of
    the corresponding transposed matrix products. -/
theorem partialTraceA_sum_vecMulVec_eq {n m r : ℕ}
    (v : Fin r → (Fin (n * m) → ℂ)) :
    partialTraceA (∑ k, vecMulVec (v k) (star (v k))) =
      ∑ k, (reshapeVec (v k))ᵀ * ((reshapeVec (v k))ᵀ)ᴴ := by
  ext i j
  simp only [partialTraceA, Matrix.of_apply, Matrix.sum_apply, vecMulVec_apply,
    Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, reshapeVec_apply]
  rw [Finset.sum_comm]

/-- The quadratic form of `M * Mᴴ` equals the squared inner product of `Mᴴ v`. -/
private lemma quadForm_mul_conjTranspose {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) ℂ) (v : Fin n → ℂ) :
    star v ⬝ᵥ (M * Mᴴ).mulVec v = star (Mᴴ.mulVec v) ⬝ᵥ (Mᴴ.mulVec v) := by
  have key : star v ᵥ* M = star (Mᴴ.mulVec v) := by
    have h := vecMul_conjTranspose Mᴴ (star v)
    rwa [conjTranspose_conjTranspose, star_star] at h
  rw [← mulVec_mulVec, dotProduct_mulVec, key]

/-- PSD domination implies kernel inclusion: if `B B† - Σ A_k A_k† ≥ 0`,
    then `Bᴴ v = 0` implies `(A k)ᴴ v = 0` for all k. -/
private lemma ker_conjTranspose_of_psd_dom {n m q : ℕ} {r : ℕ}
    (A : Fin r → Matrix (Fin n) (Fin m) ℂ)
    (B : Matrix (Fin n) (Fin q) ℂ)
    (h_dom : (B * Bᴴ - ∑ k, A k * (A k)ᴴ).PosSemidef)
    (v : Fin n → ℂ) (hv : Bᴴ.mulVec v = 0) (k : Fin r) :
    (A k)ᴴ.mulVec v = 0 := by
  -- The PSD condition gives: ‖B†v‖² ≥ Σ_k ‖Ak†v‖² for all v
  -- When B†v = 0, this forces each Ak†v = 0
  have h0 := h_dom.dotProduct_mulVec_nonneg v
  rw [sub_mulVec, dotProduct_sub, quadForm_mul_conjTranspose, hv, dotProduct_zero] at h0
  -- h0 : 0 ≤ 0 - star v ⬝ᵥ (∑ k, A k * (A k)ᴴ).mulVec v
  -- Which means star v ⬝ᵥ (∑ k, A k * (A k)ᴴ).mulVec v ≤ 0
  have h_sum_le : star v ⬝ᵥ (∑ k, A k * (A k)ᴴ).mulVec v ≤ 0 := by
    rwa [zero_sub, neg_nonneg] at h0
  -- The sum term ≥ Ak-th term ≥ 0
  have h_each_nonneg : ∀ j, 0 ≤ star v ⬝ᵥ (A j * (A j)ᴴ).mulVec v := by
    intro j; rw [quadForm_mul_conjTranspose]; exact dotProduct_star_self_nonneg _
  -- Expand sum: (∑ f k).mulVec v = ∑ (f k).mulVec v
  rw [Matrix.sum_mulVec, dotProduct_sum] at h_sum_le
  -- The k-th term is squeezed between 0 and 0
  have h_k_le : star v ⬝ᵥ (A k * (A k)ᴴ).mulVec v ≤ 0 := by
    exact le_trans
      (Finset.single_le_sum (fun j _ => h_each_nonneg j) (Finset.mem_univ k)) h_sum_le
  have h_k_eq : star v ⬝ᵥ (A k * (A k)ᴴ).mulVec v = 0 :=
    le_antisymm h_k_le (h_each_nonneg k)
  rw [quadForm_mul_conjTranspose] at h_k_eq
  exact dotProduct_star_self_eq_zero.mp h_k_eq

/-- If the `i`-th eigenvalue of `Bᴴ * B` is zero, then `B` kills
    the corresponding eigenvector. -/
private lemma mulVec_eigvec_eq_zero_of_eigenvalue_zero {n q : ℕ}
    (B : Matrix (Fin n) (Fin q) ℂ)
    (hS : (Bᴴ * B).IsHermitian)
    (i : Fin q) (hi : hS.eigenvalues i = 0) :
    B *ᵥ ⇑(hS.eigenvectorBasis i) = 0 := by
  -- ‖B *ᵥ uᵢ‖² = uᵢ† (Bᴴ B) uᵢ = λᵢ ‖uᵢ‖² = 0
  let u : Fin q → ℂ := hS.eigenvectorBasis i
  have hmv : (Bᴴ * B) *ᵥ u = (hS.eigenvalues i : ℂ) • u :=
    hS.mulVec_eigenvectorBasis i
  have h_norm_sq : star (B *ᵥ u) ⬝ᵥ (B *ᵥ u) = 0 := by
    -- Rewrite: star(Bu) · Bu = u† (B†B) u = u† (λ•u) = 0
    have h_eq : star (B *ᵥ u) ⬝ᵥ (B *ᵥ u) =
        star u ⬝ᵥ (Bᴴ * B) *ᵥ u := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    rw [h_eq, hmv]; simp [hi]
  exact dotProduct_star_self_eq_zero.mp h_norm_sq

/-- The pseudoinverse eigenvalue map: sends 0 ↦ 0 and x ↦ x⁻¹. -/
private def pinvEigenFun (x : ℝ) : ℝ := if x = 0 then 0 else x⁻¹

/-- The range indicator map: sends 0 ↦ 0 and nonzero x ↦ 1. -/
private def rangeIndicator (x : ℝ) : ℝ := if x = 0 then 0 else 1

/-- Product of an eigenvalue with its pseudoinverse equals the
    range indicator. -/
private lemma eigenval_mul_pinv (x : ℝ) :
    x * pinvEigenFun x = rangeIndicator x := by
  simp only [pinvEigenFun, rangeIndicator]
  split_ifs with h
  · simp [h]
  · exact mul_inv_cancel₀ h

/-- `S * S_pinv` equals the spectral range projector `U * Proj * U†`. -/
private lemma mul_pinv_eq_rangeProj {q : ℕ}
    {S : Op q} (hS : S.IsHermitian) :
    let U := (hS.eigenvectorUnitary : Op q)
    let D_pinv := diagonal (fun i => (pinvEigenFun (hS.eigenvalues i) : ℂ))
    let Proj := diagonal (fun i => (rangeIndicator (hS.eigenvalues i) : ℂ))
    S * (U * D_pinv * star U) = U * Proj * star U := by
  dsimp only
  set U := (hS.eigenvectorUnitary : Op q)
  set D_pinv := diagonal (fun i => (pinvEigenFun (hS.eigenvalues i) : ℂ))
  set Λ := diagonal (Complex.ofReal ∘ hS.eigenvalues)
  set Proj := diagonal (fun i => (rangeIndicator (hS.eigenvalues i) : ℂ))
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have h_diag_mul : Λ * D_pinv = Proj := by
    simp only [Λ, D_pinv, diagonal_mul_diagonal]
    congr 1; ext i
    simp only [Function.comp_apply, ← Complex.ofReal_mul, eigenval_mul_pinv]
  rw [hS.spectral_theorem]
  calc U * Λ * star U * (U * D_pinv * star U)
      = U * Λ * (star U * U) * D_pinv * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * (Λ * D_pinv) * star U := by
        rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = U * Proj * star U := by rw [h_diag_mul]

/-- `S_pinv * S` also equals the spectral range projector `U * Proj * U†`. -/
private lemma pinv_mul_eq_rangeProj {q : ℕ}
    {S : Op q} (hS : S.IsHermitian) :
    let U := (hS.eigenvectorUnitary : Op q)
    let D_pinv := diagonal (fun i => (pinvEigenFun (hS.eigenvalues i) : ℂ))
    let Proj := diagonal (fun i => (rangeIndicator (hS.eigenvalues i) : ℂ))
    (U * D_pinv * star U) * S = U * Proj * star U := by
  dsimp only
  set U := (hS.eigenvectorUnitary : Op q)
  set D_pinv := diagonal (fun i => (pinvEigenFun (hS.eigenvalues i) : ℂ))
  set Λ := diagonal (Complex.ofReal ∘ hS.eigenvalues)
  set Proj := diagonal (fun i => (rangeIndicator (hS.eigenvalues i) : ℂ))
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have h_diag_mul : D_pinv * Λ = Proj := by
    simp only [D_pinv, Λ, diagonal_mul_diagonal]
    congr 1; ext i
    simp only [Function.comp_apply, ← Complex.ofReal_mul, mul_comm, eigenval_mul_pinv]
  rw [hS.spectral_theorem]
  calc (U * D_pinv * star U) * (U * Λ * star U)
      = U * D_pinv * (star U * U) * Λ * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * (D_pinv * Λ) * star U := by
        rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = U * Proj * star U := by rw [h_diag_mul]

/-- The `(i,j)`-th entry of `B * U` is the `i`-th component of
    `B *ᵥ eigenvectorBasis j`. -/
private lemma mul_eigvecUnitary_entry {n q : ℕ}
    (B : Matrix (Fin n) (Fin q) ℂ)
    (hS : (Bᴴ * B).IsHermitian) (i : Fin n) (j : Fin q) :
    (B * (hS.eigenvectorUnitary : Op q)) i j =
      (B *ᵥ ⇑(hS.eigenvectorBasis j)) i := by
  simp [Matrix.mul_apply, mulVec, dotProduct,
    Matrix.IsHermitian.eigenvectorUnitary_apply]

/-- Key spectral identity: `S * S_pinv * Bᴴ = Bᴴ`. The range
    projector of `S = Bᴴ * B` fixes `Bᴴ`. -/
private lemma proj_mul_conjTranspose {n q : ℕ}
    (B : Matrix (Fin n) (Fin q) ℂ)
    (hS : (Bᴴ * B).IsHermitian) :
    let U : Op q := hS.eigenvectorUnitary
    let D_pinv := diagonal (fun i =>
      (pinvEigenFun (hS.eigenvalues i) : ℂ))
    let S_pinv := U * D_pinv * star U
    (Bᴴ * B) * S_pinv * Bᴴ = Bᴴ := by
  dsimp only
  set U := (hS.eigenvectorUnitary : Op q)
  set D_pinv := diagonal (fun i => (pinvEigenFun (hS.eigenvalues i) : ℂ))
  set Proj := diagonal (fun i => (rangeIndicator (hS.eigenvalues i) : ℂ))
  have hUUr : U * star U = 1 := Unitary.coe_mul_star_self hS.eigenvectorUnitary
  have h_proj_eq : Bᴴ * B * (U * D_pinv * star U) = U * Proj * star U :=
    mul_pinv_eq_rangeProj hS
  -- Proj * (U† * Bᴴ) = U† * Bᴴ: when λᵢ = 0, B *ᵥ uᵢ = 0
  have h_pi_fix : Proj * (star U * Bᴴ) = star U * Bᴴ := by
    have hBU : star U * Bᴴ = (B * U)ᴴ := by
      rw [conjTranspose_mul, Matrix.star_eq_conjTranspose]
    rw [hBU]
    ext i j
    simp only [Proj, diagonal_mul, conjTranspose_apply]
    by_cases hi : hS.eigenvalues i = 0
    · -- eigenvalue zero: B *ᵥ uᵢ = 0, so (B * U)_{j,i} = 0
      have h_BU_zero : (B * U) j i = 0 := by
        rw [mul_eigvecUnitary_entry]
        exact congr_fun (mulVec_eigvec_eq_zero_of_eigenvalue_zero B hS i hi) j
      simp [rangeIndicator, hi, h_BU_zero]
    · simp [rangeIndicator, hi]
  -- Assemble: S * S_pinv * Bᴴ = U * (Proj * U† * Bᴴ) = U * U† * Bᴴ = Bᴴ
  calc Bᴴ * B * (U * D_pinv * star U) * Bᴴ
      = U * Proj * star U * Bᴴ := by rw [h_proj_eq]
    _ = U * (Proj * (star U * Bᴴ)) := by simp only [Matrix.mul_assoc]
    _ = U * (star U * Bᴴ) := by rw [h_pi_fix]
    _ = (U * star U) * Bᴴ := by simp only [Matrix.mul_assoc]
    _ = Bᴴ := by rw [hUUr, Matrix.one_mul]

/-- The pseudoinverse `S_pinv = U D_pinv U†` is Hermitian. -/
private lemma pinv_isHermitian {q : ℕ}
    {S : Op q}
    (hS : S.IsHermitian) :
    let U : Op q := hS.eigenvectorUnitary
    let D_pinv := diagonal (fun i =>
      (pinvEigenFun (hS.eigenvalues i) : ℂ))
    (U * D_pinv * star U).IsHermitian := by
  dsimp only
  have hD : (diagonal (fun i => (pinvEigenFun (hS.eigenvalues i) : ℂ))).IsHermitian := by
    rw [isHermitian_diagonal_iff]
    intro i; exact Complex.conj_ofReal _
  rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_mul,
    Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
    hD.eq, Matrix.mul_assoc]

/-- If a Hermitian projector complement annihilates `A` on the left after
    adjointing, then the projector fixes `A`. -/
private lemma eq_mul_of_mul_one_sub_eq_zero_of_isHermitian {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℂ)
    (P : Op n)
    (hP : P.IsHermitian)
    (hA : Aᴴ * (1 - P) = 0) :
    A = P * A := by
  have h_ct : (1 - P)ᴴ * A = 0 := by
    have := congr_arg Matrix.conjTranspose hA
    rwa [conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_zero] at this
  have h_one_sub : (1 - P)ᴴ = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hP.eq]
  rw [h_one_sub] at h_ct
  have h_sub : (1 - P) * A = A - P * A := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  exact sub_eq_zero.mp (h_sub ▸ h_ct)

/-- `B * (S_pinv * Bᴴ * Aₖ) = Aₖ` — the factorization identity.
    Uses the projector identity and kernel inclusion. -/
private lemma factorization_identity {n m q : ℕ} {r : ℕ}
    (A : Fin r → Matrix (Fin n) (Fin m) ℂ)
    (B : Matrix (Fin n) (Fin q) ℂ)
    (h_ker : ∀ v k, Bᴴ.mulVec v = 0 →
      (A k)ᴴ.mulVec v = 0)
    (hS : (Bᴴ * B).IsHermitian) (k : Fin r) :
    let U : Op q := hS.eigenvectorUnitary
    let D_pinv := diagonal (fun i =>
      (pinvEigenFun (hS.eigenvalues i) : ℂ))
    let S_pinv := U * D_pinv * star U
    A k = B * (S_pinv * Bᴴ * A k) := by
  intro U D_pinv S_pinv
  -- Step 1: Bᴴ * (I - B S_pinv Bᴴ) = 0 (projector identity)
  have h_proj : Bᴴ * B * S_pinv * Bᴴ = Bᴴ :=
    proj_mul_conjTranspose B hS
  have h_BtI_P : Bᴴ * (1 - B * S_pinv * Bᴴ) = 0 := by
    simp only [Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc, h_proj, sub_self]
  -- Step 2: ∀ v, Bᴴ *ᵥ ((I - P) v) = 0
  have h_ker_P v :
      Bᴴ *ᵥ ((1 - B * S_pinv * Bᴴ) *ᵥ v) = 0 := by
    rw [mulVec_mulVec, h_BtI_P, zero_mulVec]
  -- Step 3: ∀ v, (A k)ᴴ *ᵥ ((I - P) v) = 0
  have h_Ak_P v :
      (A k)ᴴ *ᵥ ((1 - B * S_pinv * Bᴴ) *ᵥ v) = 0 :=
    h_ker _ k (h_ker_P v)
  -- Step 4: `(A k)ᴴ * (I - P) = 0`
  have h_mat : (A k)ᴴ * (1 - B * S_pinv * Bᴴ) = 0 := by
    ext i j
    simpa using congr_fun (h_Ak_P (Pi.single j 1)) i
  have hSp_herm : S_pinvᴴ = S_pinv := (pinv_isHermitian hS).eq
  have hP_herm : (B * S_pinv * Bᴴ).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hSp_herm]
    simp only [Matrix.mul_assoc]
  have h_fix : A k = (B * S_pinv * Bᴴ) * A k :=
    eq_mul_of_mul_one_sub_eq_zero_of_isHermitian
      (A := A k) (P := B * S_pinv * Bᴴ) hP_herm h_mat
  simpa [Matrix.mul_assoc] using h_fix

/-- Sandwiching a finite sum of outer products by `P` distributes over the sum. -/
private lemma sum_mul_mul_conjTranspose_eq {n m q : ℕ} {r : ℕ}
    (A : Fin r → Matrix (Fin n) (Fin m) ℂ)
    (P : Matrix (Fin q) (Fin n) ℂ) :
    ∑ k, (P * A k) * (P * A k)ᴴ =
      P * (∑ k, A k * (A k)ᴴ) * Pᴴ := by
  rw [show (P * ∑ k, A k * (A k)ᴴ) * Pᴴ =
      ∑ k, P * (A k * (A k)ᴴ) * Pᴴ by
    rw [Matrix.mul_sum, Matrix.sum_mul]]
  congr 1
  ext1 k
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The contraction bound: `(1 - Σ Cₖ Cₖᴴ).PosSemidef` when
    `Cₖ = S_pinv * Bᴴ * Aₖ` and `(BBᴴ - Σ AₖAₖᴴ).PosSemidef`. -/
private lemma contraction_bound {n m q : ℕ} {r : ℕ}
    (A : Fin r → Matrix (Fin n) (Fin m) ℂ)
    (B : Matrix (Fin n) (Fin q) ℂ)
    (h_dom : (B * Bᴴ - ∑ k, A k * (A k)ᴴ).PosSemidef)
    (hS : (Bᴴ * B).IsHermitian) :
    let U := (hS.eigenvectorUnitary : Matrix _ _ ℂ)
    let D_pinv := diagonal (fun i =>
      (pinvEigenFun (hS.eigenvalues i) : ℂ))
    let S_pinv := U * D_pinv * star U
    let C := fun k => S_pinv * Bᴴ * A k
    ((1 : Op q) -
      ∑ k, C k * (C k)ᴴ).PosSemidef := by
  dsimp only
  set U := (hS.eigenvectorUnitary : Op q)
  set D_pinv := diagonal (fun i => (pinvEigenFun (hS.eigenvalues i) : ℂ))
  set S_pinv := U * D_pinv * star U
  set Proj := diagonal (fun i => (rangeIndicator (hS.eigenvalues i) : ℂ))
  -- Unitary identities
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hUUr : U * star U = 1 := Unitary.coe_mul_star_self hS.eigenvectorUnitary
  -- S_pinv is Hermitian
  have hSp : S_pinvᴴ = S_pinv := (pinv_isHermitian hS).eq
  -- Step 1: P = S_pinv * Bᴴ, Pᴴ = B * S_pinv
  set P := S_pinv * Bᴴ with hP_def
  have hP_ct : Pᴴ = B * S_pinv := by
    rw [hP_def, conjTranspose_mul, conjTranspose_conjTranspose, hSp]
  -- Step 1a: Σ (P*Ak)(P*Ak)ᴴ = P * (Σ Ak Akᴴ) * Pᴴ
  have h_sum_eq : ∑ k, (P * A k) * (P * A k)ᴴ =
      P * (∑ k, A k * (A k)ᴴ) * Pᴴ :=
    sum_mul_mul_conjTranspose_eq A P
  -- Step 2: Sandwich lemma
  have h_sand : (P * (B * Bᴴ - ∑ k, A k * (A k)ᴴ) * Pᴴ).PosSemidef :=
    h_dom.mul_mul_conjTranspose_same P
  -- Rewrite sandwich as P*BBᴴ*Pᴴ - Σ (P*Ak)(P*Ak)ᴴ
  have h_expand : P * (B * Bᴴ - ∑ k, A k * (A k)ᴴ) * Pᴴ =
      P * (B * Bᴴ) * Pᴴ - ∑ k, (P * A k) * (P * A k)ᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← h_sum_eq]
  -- Step 3: Spectral projector identities
  have h_SSp : (Bᴴ * B) * S_pinv = U * Proj * star U :=
    mul_pinv_eq_rangeProj hS
  have h_SpS : S_pinv * (Bᴴ * B) = U * Proj * star U :=
    pinv_mul_eq_rangeProj hS
  have h_Proj_sq : Proj * Proj = Proj := by
    simp only [Proj, diagonal_mul_diagonal]
    congr 1; ext i; simp only [rangeIndicator]
    split_ifs <;> norm_num
  -- P * BBᴴ * Pᴴ = R (range projector)
  have h_PBBtP : P * (B * Bᴴ) * Pᴴ = U * Proj * star U := by
    rw [hP_def, hP_ct]
    rw [show S_pinv * Bᴴ * (B * Bᴴ) * (B * S_pinv) =
        S_pinv * (Bᴴ * B) * ((Bᴴ * B) * S_pinv) from by
      simp only [Matrix.mul_assoc]]
    rw [h_SpS, h_SSp]
    -- R * R = R
    calc U * Proj * star U * (U * Proj * star U)
        = U * Proj * (star U * U) * Proj * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (Proj * Proj) * star U := by
          rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = U * Proj * star U := by rw [h_Proj_sq]
  -- Step 4: (I - R).PosSemidef
  have h_IR_psd : ((1 : Op q) -
      U * Proj * star U).PosSemidef := by
    have h_split : (1 : Op q) - U * Proj * star U =
        U * (1 - Proj) * star U := by
      have : U * 1 * star U = (1 : Matrix _ _ ℂ) := by
        rw [Matrix.mul_one, hUUr]
      rw [Matrix.mul_sub, Matrix.sub_mul, this]
    rw [h_split]
    -- (1 - Proj) is a diagonal with entries in {0, 1}, hence PSD
    have h_one_sub_proj : ((1 : Op q) - Proj).PosSemidef := by
      rw [show (1 : Op q) - Proj =
          diagonal (fun i => 1 - (rangeIndicator (hS.eigenvalues i) : ℂ)) from by
        simp [Proj, ← diagonal_one, ← diagonal_sub]]
      rw [posSemidef_diagonal_iff]
      intro i; simp only [rangeIndicator]
      split_ifs <;> norm_num
    exact h_one_sub_proj.mul_mul_conjTranspose_same U
  -- Step 5: Combine
  -- I - Σ Ck Ckᴴ = (I - R) + (R - Σ Ck Ckᴴ), both PSD
  -- The goal already uses P since `set P` folded `S_pinv * Bᴴ`
  have h_decomp : (1 : Op q) -
      ∑ k, (P * A k) * (P * A k)ᴴ =
    ((1 : Matrix _ _ ℂ) - U * Proj * star U) +
    (U * Proj * star U - ∑ k, (P * A k) * (P * A k)ᴴ) := by
    simp [sub_add_sub_cancel]
  rw [h_decomp]
  apply PosSemidef.add h_IR_psd
  rw [← h_PBBtP, ← h_expand]
  exact h_sand

/-- Range inclusion from PSD domination: If `B B† ≥ Σ A_k A_k†`,
    then `A_k = B * C_k` for some `C_k`, with contraction
    bound `Σ C_k C_k† ≤ I`.

    Reference: Douglas (1966), Fillmore-Williams (1971). -/
lemma matrix_douglas_factorization {n m q : ℕ} {r : ℕ}
    (A : Fin r → Matrix (Fin n) (Fin m) ℂ)
    (B : Matrix (Fin n) (Fin q) ℂ)
    (h_dom : (B * Bᴴ - ∑ k, A k * (A k)ᴴ).PosSemidef) :
    ∃ C : Fin r → Matrix (Fin q) (Fin m) ℂ,
      (∀ k, A k = B * C k) ∧
      ((1 : Op q) -
        ∑ k, C k * (C k)ᴴ).PosSemidef := by
  have h_ker : ∀ v k, Bᴴ.mulVec v = 0 →
      (A k)ᴴ.mulVec v = 0 :=
    fun v k hv =>
      ker_conjTranspose_of_psd_dom A B h_dom v hv k
  have hS : (Bᴴ * B).IsHermitian :=
    isHermitian_conjTranspose_mul_self B
  let U : Op q := hS.eigenvectorUnitary
  let D_pinv := diagonal (fun i =>
    (pinvEigenFun (hS.eigenvalues i) : ℂ))
  let S_pinv := U * D_pinv * star U
  refine ⟨fun k => S_pinv * Bᴴ * A k, ?_, ?_⟩
  · intro k
    exact factorization_identity A B h_ker hS k
  · exact contraction_bound A B h_dom hS

/-- `(Mᵀ)ᴴ * Mᵀ = (M * Mᴴ)ᵀ` — relates `K†K` to `CC†` when `K = Cᵀ`. -/
lemma conjTranspose_transpose_mul_transpose {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) ℂ) :
    (Mᵀ)ᴴ * Mᵀ = (M * Mᴴ)ᵀ := by
  rw [Matrix.transpose_mul]; congr 1

/-- PSD of transpose: `(I - S)` PSD implies `(I - Sᵀ)` PSD. -/
lemma posSemidef_one_sub_transpose {n : ℕ}
    (S : Op n)
    (h : (1 - S).PosSemidef) :
    (1 - Sᵀ).PosSemidef := by
  have := h.transpose
  rwa [Matrix.transpose_sub, Matrix.transpose_one] at this

end -- noncomputable section

end Quantum.Channels
