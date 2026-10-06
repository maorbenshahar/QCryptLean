import QCryptLean.Quantum.Channels.CPTP.DiamondNorm
import QCryptLean.Quantum.Channels.CPTP.SubstateExtraction
import QCryptLean.Quantum.Channels.CPTP.CKRBound.HermitianContractivity
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import QCryptLean.Math.SpectralTheory.Basic

/-!
# Watrous Factorization — reshape identities, PSD decompositions, cross-side contraction

Infrastructure for the Watrous ancilla factorization (TQI Lemma 3.46):
any Z : Op(n*n) with ‖Z‖₁ ≤ 1 factors as Z = (A₀ ⊗ I) σ (B₀ ⊗ I)
with σ PSD, Tr(σ) ≤ 1, ‖A₀‖ ≤ 1, ‖B₀‖ ≤ 1.

## Main results

### Transpose tricks
- `reshapeVec_tensor_one_mulVec`: `reshapeVec((1 ⊗ A₀) *ᵥ v) = reshapeVec(v) * A₀ᵀ`
- `reshapeVec_one_tensor_mulVec`: `reshapeVec((A₀ ⊗ 1) *ᵥ v) = A₀ * reshapeVec(v)`
- `unreshapeVec_mul_transpose`: Inverse right transpose trick
- `unreshapeVec_mul_left`: Inverse left transpose trick
- `tensor_one_mul_mulVec_eq`: Matrix equation form of right transpose trick

### Matrix algebra
- `sum_vecMulVec_star_posSemidef`: Sum of rank-1 PSD matrices is PSD
- `mul_vecMulVec_star_mul`: vecMulVec sandwich identity
- `mul_conjTranspose_eq_sum_vecMulVec`: Column decomposition M * N† = Σ |col_a(M)><col_a(N)|

### PSD operator bounds
- `posSemidef_le_one_of_trace_re_le`: PSD + Tr(P).re ≤ 1 ⟹ P ≤ 1
- `opNorm_le_one_of_posSemidef_trace_le`: PSD + Tr(P).re ≤ 1 ⟹ ‖P‖ ≤ 1

### Contraction bounds
- `one_sub_conjTranspose_mul_psd_of_opNorm_le`: ‖V‖ ≤ 1 ⟹ (1 - V†V) PSD
- `opNorm_sqrt_le_one`: P PSD + ‖P‖ ≤ 1 ⟹ ‖√P‖ ≤ 1
- `conjTranspose_mul_le_conjTranspose_mul`: A ≤ B ⟹ R†AR ≤ R†BR
- `trace_re_le_of_le`: A ≤ B ⟹ Tr(A).re ≤ Tr(B).re

### Square-root and Gram decompositions
- `psd_eq_sum_vecMulVec_sqrt_cols`: PSD matrices as sums of square-root columns
- `mul_psd_eq_sum_vecMulVec_sqrt`: column decomposition of `V * P`
- `partialTraceB_psd_eq_sum_reshapeVec_sqrt_cols`: right Gram partial trace formula
- `partialTraceA_psd_eq_sum_reshapeVec_transpose_sqrt_cols`: left Gram partial trace formula

### Factorization
- `traceNorm_sqrt_conjTranspose_mul_self`: `traceNorm (√(X†X)) = traceNorm X`
- `polar_decomposition_norm`: polar decomposition with PSD part of trace `traceNorm X`
- `watrous_A_side_douglas_factorization`, `watrous_B_side_douglas_factorization`: the two halves
  of the Watrous cross-side factorization (σ PSD, trace ≤ 1)

## References

- Watrous (2018) "Theory of Quantum Information", Lemma 3.46
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Math.SpectralTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

noncomputable section

namespace Quantum.Metrics.WatrousFactorization

private lemma tensor_one_mulVec_apply {n : ℕ} (A₀ : Op n)
    (v : Fin (n * n) → ℂ) (i j : Fin n) :
    (Op.tensor (1 : Op n) A₀).mulVec v (finProdFinEquiv (i, j)) =
      ∑ l : Fin n, v (finProdFinEquiv (i, l)) * A₀ j l := by
  simp only [mulVec, dotProduct, Op.tensor, reindex_apply, submatrix_apply,
    kroneckerMap_apply, one_apply, Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  congr 1
  ext l
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  ring

private lemma one_tensor_mulVec_apply {n : ℕ} (A₀ : Op n)
    (v : Fin (n * n) → ℂ) (i j : Fin n) :
    (Op.tensor A₀ (1 : Op n)).mulVec v (finProdFinEquiv (i, j)) =
      ∑ k : Fin n, A₀ i k * v (finProdFinEquiv (k, j)) := by
  simp only [mulVec, dotProduct, Op.tensor, reindex_apply, submatrix_apply,
    kroneckerMap_apply, one_apply, Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  congr 1
  ext k
  simp only [Equiv.symm_apply_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]

/-- **The Transpose Trick**: The tensor product `(1 ⊗ A₀)` acting on a vectorized
    matrix gives right-multiplication by `A₀ᵀ` after reshaping.

    In formulas: `reshapeVec((1 ⊗ A₀) *ᵥ v) = reshapeVec(v) * A₀ᵀ`

    This is the key identity connecting the tensor product structure on `ℂ^{n²}`
    with matrix multiplication on `ℂ^{n×n}` via the vectorization isomorphism. -/
theorem reshapeVec_tensor_one_mulVec {n : ℕ} (A₀ : Op n) (v : Fin (n * n) → ℂ) :
    reshapeVec (Op.tensor (1 : Op n) A₀ |>.mulVec v) = reshapeVec v * A₀ᵀ := by
  ext i j
  rw [reshapeVec_apply, tensor_one_mulVec_apply, Matrix.mul_apply]
  simp only [reshapeVec_apply, Matrix.transpose_apply]

/-- Inverse form of the transpose trick: `unreshapeVec(M * A₀ᵀ) = (1 ⊗ A₀) *ᵥ unreshapeVec(M)`. -/
theorem unreshapeVec_mul_transpose {n : ℕ} (A₀ : Op n) (M : Op n) :
    unreshapeVec (M * A₀ᵀ) = (Op.tensor (1 : Op n) A₀).mulVec (unreshapeVec M) := by
  have h := reshapeVec_tensor_one_mulVec A₀ (unreshapeVec M)
  rw [reshapeVec_unreshapeVec] at h
  rw [← h, unreshapeVec_reshapeVec]

/-- The matrix equation form: left-multiplying by `(1 ⊗ A₀)` acts as
    right-multiplication by `A₀ᵀ` on reshaped mulVec columns.
    `reshapeVec(((1⊗A₀)*M) *ᵥ e_q) = reshapeVec(M *ᵥ e_q) * A₀ᵀ` -/
theorem tensor_one_mul_mulVec_eq {n : ℕ} (A₀ : Op n) (M : Op (n * n))
    (v : Fin (n * n) → ℂ) :
    reshapeVec ((Op.tensor (1 : Op n) A₀ * M).mulVec v) =
      reshapeVec (M.mulVec v) * A₀ᵀ := by
  rw [← mulVec_mulVec]
  exact reshapeVec_tensor_one_mulVec A₀ (M.mulVec v)

/-- **Left Transpose Trick**: The tensor product `(A₀ ⊗ 1)` acting on a vectorized
    matrix gives left-multiplication by `A₀` after reshaping.

    In formulas: `reshapeVec((A₀ ⊗ 1) *ᵥ v) = A₀ * reshapeVec(v)`

    Proof: `((A₀ ⊗ I) v)_{(i₁,i₂)} = Σ_{k₁} A₀(i₁,k₁) v_{(k₁,i₂)} = (A₀ * reshapeVec(v))_{i₁,i₂}` -/
theorem reshapeVec_one_tensor_mulVec {n : ℕ} (A₀ : Op n) (v : Fin (n * n) → ℂ) :
    reshapeVec (Op.tensor A₀ (1 : Op n) |>.mulVec v) = A₀ * reshapeVec v := by
  ext i j
  rw [reshapeVec_apply, one_tensor_mulVec_apply, Matrix.mul_apply]
  simp only [reshapeVec_apply]

/-- Inverse left transpose trick:
    `unreshapeVec(A₀ * M) = (A₀ ⊗ 1) *ᵥ unreshapeVec(M)` -/
theorem unreshapeVec_mul_left {n : ℕ} (A₀ : Op n) (M : Op n) :
    unreshapeVec (A₀ * M) = (Op.tensor A₀ (1 : Op n)).mulVec (unreshapeVec M) := by
  have h := reshapeVec_one_tensor_mulVec A₀ (unreshapeVec M)
  rw [reshapeVec_unreshapeVec] at h
  rw [← h, unreshapeVec_reshapeVec]

/-- A sum of rank-1 PSD terms `vecMulVec(v)(star(v))` is PSD. -/
theorem sum_vecMulVec_star_posSemidef {n r : ℕ}
    (v : Fin r → (Fin n → ℂ)) :
    (∑ k, vecMulVec (v k) (star (v k))).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact Matrix.posSemidef_vecMulVec_self_star (v i)

/-- **vecMulVec sandwich identity**: Left-multiplying by M and right-multiplying
    by N a rank-1 matrix `vecMulVec x (star y)` gives
    `vecMulVec (M.mulVec x) (star (Nᴴ.mulVec y))`.

    This combines `Matrix.mul_vecMulVec` and `Matrix.vecMulVec_mul` with
    the conjugate transpose vecMul identity. -/
theorem mul_vecMulVec_star_mul {n : ℕ}
    (M N : Op n) (x y : Fin n → ℂ) :
    M * vecMulVec x (star y) * N =
      vecMulVec (M.mulVec x) (star (Nᴴ.mulVec y)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  -- Need: vecMul (star y) N = star (Nᴴ.mulVec y)
  have h := Matrix.star_mulVec Nᴴ y
  rw [conjTranspose_conjTranspose] at h
  exact h.symm

/-- Conjugate transpose of `Op.tensor A₀ (1 : Op n)` is `Op.tensor A₀ᴴ (1 : Op n)`. -/
theorem tensor_one_conjTranspose {n : ℕ} (A₀ : Op n) :
    (Op.tensor A₀ (1 : Op n))ᴴ = Op.tensor A₀ᴴ (1 : Op n) := by
  rw [Op.tensor_conjTranspose, conjTranspose_one]

/-- PSD matrices are closed under conjugation by (A₀ ⊗ I):
    if σ is PSD then (A₀ ⊗ I)ᴴ σ (A₀ ⊗ I) is PSD. -/
theorem posSemidef_tensor_one_conj {n : ℕ}
    (A₀ : Op n) (σ : Op (n * n)) (hσ : σ.PosSemidef) :
    ((Op.tensor A₀ (1 : Op n))ᴴ * σ * Op.tensor A₀ (1 : Op n)).PosSemidef :=
  hσ.conjTranspose_mul_mul_same _

/-- **Column decomposition**: `M * Nᴴ = Σ_a vecMulVec (M col_a) (star (N col_a))`.

    This identity decomposes a matrix product M * N† into a sum of rank-1
    outer products of columns. Used in the Watrous factorization to decompose
    VP = (VP^{1/2}) * (P^{1/2})† into a sum of rank-1 terms. -/
theorem mul_conjTranspose_eq_sum_vecMulVec {d : ℕ}
    (M N : Op d) :
    M * Nᴴ = ∑ a : Fin d, vecMulVec (M.mulVec (Pi.single a 1))
      (star (N.mulVec (Pi.single a 1))) := by
  ext i j
  simp only [Matrix.mul_apply, conjTranspose_apply]
  -- Pull (i, j) inside the sum: (∑ a, f a) i j = ∑ a, f a i j
  rw [Finset.sum_apply _ Finset.univ, Finset.sum_apply _ Finset.univ]
  simp only [vecMulVec_apply, Pi.star_apply, mulVec, dotProduct,
    Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- **Column decomposition (Hermitian)**: For Hermitian N,
    `M * N = Σ_a vecMulVec (M col_a) (star (N col_a))`. -/
theorem mul_hermitian_eq_sum_vecMulVec {d : ℕ}
    (M N : Op d) (hN : N.IsHermitian) :
    M * N = ∑ a : Fin d, vecMulVec (M.mulVec (Pi.single a 1))
      (star (N.mulVec (Pi.single a 1))) := by
  nth_rw 1 [show N = Nᴴ from hN.eq.symm]
  exact mul_conjTranspose_eq_sum_vecMulVec M N

/-- PSD matrices with trace ≤ 1 satisfy P ≤ 1 (in the operator ordering).

    **Proof sketch**: PSD implies eigenvalues ≥ 0. Trace = sum of eigenvalues ≤ 1.
    Since nonneg reals summing to ≤ 1 are individually ≤ 1, all eigenvalues ≤ 1.
    Therefore I - P has nonneg eigenvalues, hence is PSD, i.e., P ≤ I. -/
lemma posSemidef_le_one_of_trace_re_le {d : ℕ}
    (P : Op d) (hP : P.PosSemidef) (htr : P.trace.re ≤ 1) :
    P ≤ 1 := by
  rw [Matrix.le_iff]
  -- Use CFC: 1 - P = cfc (1 - ·) P, and cfc f P ≥ 0 when f ≥ 0 on spectrum
  have hH := hP.isHermitian
  have hsa : IsSelfAdjoint P := hH.isSelfAdjoint
  -- Eigenvalue bounds: nonneg eigenvalues summing to ≤ 1 are individually ≤ 1
  have hP_eig_nn := hH.posSemidef_iff_eigenvalues_nonneg.mp hP
  have htr_eig : ∑ i, hH.eigenvalues i ≤ 1 := by
    rw [hH.trace_eq_sum_eigenvalues] at htr
    exact_mod_cast htr
  have hP_eig_le : ∀ i, hH.eigenvalues i ≤ 1 := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => hP_eig_nn j) (Finset.mem_univ i)) htr_eig
  -- 1 - x ≥ 0 on spectrum of P
  have h_spec : ∀ x ∈ spectrum ℝ P, 0 ≤ 1 - x := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i, rfl⟩; linarith [hP_eig_le i]
  -- cfc (1 - ·) P = 1 - P (by CFC linearity)
  have h_eq : cfc (fun x : ℝ => 1 - x) P = 1 - P := by
    have hfg : (fun x : ℝ => 1 - x) = fun x => (fun _ : ℝ => (1 : ℝ)) x - id x := by
      ext x; simp
    rw [hfg, cfc_sub (fun _ => (1 : ℝ)) id P, cfc_const (1 : ℝ) P, cfc_id ℝ P, map_one]
  -- Conclude: 0 ≤ cfc (1-·) P, so (1-P) is PSD
  have h0 : (0 : Op d) ≤ cfc (fun x : ℝ => 1 - x) P := cfc_nonneg h_spec
  rw [← h_eq]; rwa [Matrix.le_iff, sub_zero] at h0

/-- PSD matrices with trace ≤ 1 have operator norm ≤ 1.

    Follows from `posSemidef_le_one_of_trace_re_le` and C*-algebra norm monotonicity:
    0 ≤ P ≤ 1 implies ‖P‖ ≤ ‖1‖ = 1.

    Uses spectral decomposition: ‖P‖ = max eigenvalue ≤ 1 since eigenvalues
    are nonneg and sum to at most 1. -/
lemma opNorm_le_one_of_posSemidef_trace_le {d : ℕ} [NeZero d]
    (P : Op d) (hP : P.PosSemidef) (htr : P.trace.re ≤ 1) :
    ‖P‖ ≤ 1 := by
  -- Spectral decomposition: P = U * D * U†
  have hH := hP.isHermitian
  set U : Op d := hH.eigenvectorUnitary.val with hU_def
  set evs := hH.eigenvalues with hevs_def
  set D : Op d := diagonal (RCLike.ofReal ∘ evs) with hD_def
  have hP_spec : P = U * D * star U := hH.spectral_theorem
  have hUstarU : star U * U = 1 :=
    Matrix.UnitaryGroup.star_mul_self hH.eigenvectorUnitary
  have hUUstar : U * star U = 1 :=
    mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.prop
  -- Eigenvalue bounds: nonneg eigenvalues summing to ≤ 1 are individually ≤ 1
  have h_nn : ∀ i, 0 ≤ evs i := hH.posSemidef_iff_eigenvalues_nonneg.mp hP
  have htr_eig : ∑ i, evs i ≤ 1 := by
    rw [hH.trace_eq_sum_eigenvalues] at htr; exact_mod_cast htr
  have h_le1 : ∀ i, evs i ≤ 1 := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => h_nn j) (Finset.mem_univ i)) htr_eig
  -- Unitary norms: ‖U‖ = 1, ‖U†‖ = 1
  have hUctU : U.conjTranspose * U = 1 := by change star U * U = 1; exact hUstarU
  have hU_norm : ‖U‖ = 1 := by
    have h1 : ‖U‖ * ‖U‖ = 1 := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hUctU, norm_one]
    nlinarith [norm_nonneg U, sq_nonneg (‖U‖ - 1)]
  have hUstar_norm : ‖star U‖ = 1 := by
    change ‖U.conjTranspose‖ = 1; rw [Matrix.l2_opNorm_conjTranspose, hU_norm]
  -- ‖P‖ ≤ ‖U‖ * ‖D‖ * ‖U†‖ (submultiplicativity)
  have h_sub : ‖P‖ ≤ ‖U‖ * ‖D‖ * ‖star U‖ := by
    rw [hP_spec]
    exact le_trans (Matrix.l2_opNorm_mul _ _)
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
  rw [hU_norm, hUstar_norm, one_mul, mul_one] at h_sub
  -- ‖D‖ = ‖evs‖_∞ ≤ 1
  rw [show ‖D‖ = ‖(RCLike.ofReal ∘ evs : Fin d → ℂ)‖ from
    Matrix.l2_opNorm_diagonal _] at h_sub
  exact le_trans h_sub (by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro i
    simp only [Function.comp, RCLike.norm_ofReal, abs_of_nonneg (h_nn i)]
    exact h_le1 i)

/-- Trace norm of V*P is at most 1 when V is a contraction and P is PSD with Tr ≤ 1.

    Combines left Hölder (`‖VP‖₁ ≤ ‖V‖ · ‖P‖₁`) with
    `traceNorm_posSemidef_eq_trace` (`‖P‖₁ = Tr(P).re` for PSD P). -/
lemma traceNorm_contraction_mul_psd_le {d : ℕ} [NeZero d]
    (V P : Op d) (hP : P.PosSemidef) (hP_tr : P.trace.re ≤ 1) (hV : ‖V‖ ≤ 1) :
    traceNorm (V * P) ≤ 1 := by
  have htn_nn : 0 ≤ traceNorm P := by
    unfold traceNorm; exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  calc traceNorm (V * P)
      ≤ ‖V‖ * traceNorm P :=
        TraceNormHoelder.traceNorm_mul_le_opNorm_mul_traceNorm V P
    _ ≤ 1 * 1 := by
        apply mul_le_mul hV _ htn_nn (by linarith)
        rw [traceNorm_posSemidef_eq_trace P hP]
        exact hP_tr
    _ = 1 := one_mul 1

/-- If `(I - V†V)` is PSD then `‖V‖ ≤ 1`.

    Uses the C*-identity `‖V‖² = ‖V†V‖` and spectral decomposition:
    V†V ≤ I implies all eigenvalues ≤ 1, hence ‖V†V‖ ≤ 1. -/
lemma opNorm_le_one_of_one_sub_conjTranspose_mul_psd {d : ℕ} [NeZero d]
    (V : Op d) (h : (1 - V.conjTranspose * V).PosSemidef) : ‖V‖ ≤ 1 := by
  -- C*-identity: ‖V‖² = ‖V†V‖
  suffices hsq : ‖V‖ * ‖V‖ ≤ 1 by nlinarith [norm_nonneg V]
  rw [← Matrix.l2_opNorm_conjTranspose_mul_self]
  -- Spectral decomposition of M = V†V
  set M := V.conjTranspose * V with hM_def
  have hM_H : M.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  set U : Op d := hM_H.eigenvectorUnitary.val with hU_def
  set evs := hM_H.eigenvalues with hevs_def
  set D : Op d := diagonal (RCLike.ofReal ∘ evs) with hD_def
  have hM_spec : M = U * D * star U := hM_H.spectral_theorem
  have hUstarU : star U * U = 1 :=
    Matrix.UnitaryGroup.star_mul_self hM_H.eigenvectorUnitary
  have hUUstar : U * star U = 1 :=
    mem_unitaryGroup_iff.mp hM_H.eigenvectorUnitary.prop
  -- Eigenvalue bounds: nonneg (from PSD) and ≤ 1 (from V†V ≤ I)
  have h_nn : ∀ i, 0 ≤ evs i :=
    (posSemidef_conjTranspose_mul_self V).eigenvalues_nonneg
  have h_le1 : ∀ i, evs i ≤ 1 := by
    have hU_unit : IsUnit U := IsUnit.of_mul_eq_one (star U) hUUstar
    -- 1 - M = U * (1 - D) * star U
    have h_1M : 1 - M = U * (1 - D) * star U := by
      symm; calc U * (1 - D) * star U
          = (U - U * D) * star U := by rw [mul_sub, Matrix.mul_one]
        _ = U * star U - U * D * star U := by rw [sub_mul]
        _ = 1 - M := by rw [hUUstar, hM_spec]
    have h_1D_psd : (1 - D).PosSemidef := by
      rw [h_1M] at h; exact hU_unit.posSemidef_star_right_conjugate_iff.mp h
    rw [show 1 - D = diagonal (fun i => 1 - (RCLike.ofReal ∘ evs) i)
      from by rw [hD_def, ← diagonal_one, diagonal_sub]] at h_1D_psd
    rw [posSemidef_diagonal_iff] at h_1D_psd
    intro i
    have hle := Complex.le_def.mp (by simpa [Function.comp, sub_nonneg] using h_1D_psd i)
    simpa using hle.1
  -- Norm bound: ‖M‖ ≤ ‖U‖ * ‖D‖ * ‖U†‖ = ‖D‖ = max|evs| ≤ 1
  have hUctU : U.conjTranspose * U = 1 := by change star U * U = 1; exact hUstarU
  have hU_norm : ‖U‖ = 1 := by
    nlinarith [norm_nonneg U, sq_nonneg (‖U‖ - 1),
      show ‖U‖ * ‖U‖ = 1 from by
        rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hUctU, norm_one]]
  have hUstar_norm : ‖star U‖ = 1 := by
    change ‖U.conjTranspose‖ = 1; rw [Matrix.l2_opNorm_conjTranspose, hU_norm]
  have h_sub : ‖M‖ ≤ ‖U‖ * ‖D‖ * ‖star U‖ := by
    rw [hM_spec]
    exact le_trans (Matrix.l2_opNorm_mul _ _)
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
  rw [hU_norm, hUstar_norm, one_mul, mul_one] at h_sub
  rw [show ‖D‖ = ‖(RCLike.ofReal ∘ evs : Fin d → ℂ)‖ from
    Matrix.l2_opNorm_diagonal _] at h_sub
  exact le_trans h_sub (by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro i
    simp only [Function.comp, RCLike.norm_ofReal, abs_of_nonneg (h_nn i)]
    exact h_le1 i)

/-- If `‖V‖ ≤ 1` then `V†V ≤ 1`, i.e., `(1 - V†V)` is PSD.

    Converse of `opNorm_le_one_of_one_sub_conjTranspose_mul_psd`.
    Uses eigenvalue decomposition: eigenvalues of `V†V` are nonneg and bounded by
    `‖V†V‖ = ‖V‖² ≤ 1`. -/
lemma one_sub_conjTranspose_mul_psd_of_opNorm_le {d : ℕ} [NeZero d]
    (V : Op d) (hV : ‖V‖ ≤ 1) : (1 - V.conjTranspose * V).PosSemidef := by
  set M := V.conjTranspose * V with hM_def
  have hM_H : M.IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  set U : Op d := hM_H.eigenvectorUnitary.val with hU_def
  set evs := hM_H.eigenvalues with hevs_def
  set D : Op d := diagonal (RCLike.ofReal ∘ evs) with hD_def
  have hM_spec : M = U * D * star U := hM_H.spectral_theorem
  have hUstarU : star U * U = 1 :=
    Matrix.UnitaryGroup.star_mul_self hM_H.eigenvectorUnitary
  have hUUstar : U * star U = 1 :=
    mem_unitaryGroup_iff.mp hM_H.eigenvectorUnitary.prop
  -- Eigenvalue bounds: nonneg from PSD
  have h_nn : ∀ i, 0 ≤ evs i :=
    (posSemidef_conjTranspose_mul_self V).eigenvalues_nonneg
  -- ‖M‖ = ‖V‖² ≤ 1
  have hM_norm : ‖M‖ ≤ 1 := by
    rw [show ‖M‖ = ‖V‖ * ‖V‖ from Matrix.l2_opNorm_conjTranspose_mul_self V]
    nlinarith [norm_nonneg V]
  -- Unitary norms
  have hUctU : U.conjTranspose * U = 1 := by change star U * U = 1; exact hUstarU
  have hU_norm : ‖U‖ = 1 := by
    nlinarith [norm_nonneg U, sq_nonneg (‖U‖ - 1),
      show ‖U‖ * ‖U‖ = 1 from by
        rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hUctU, norm_one]]
  have hUstar_norm : ‖star U‖ = 1 := by
    change ‖U.conjTranspose‖ = 1; rw [Matrix.l2_opNorm_conjTranspose, hU_norm]
  -- ‖D‖ ≤ 1 via D = U† M U
  have hD_le : ‖D‖ ≤ 1 := by
    have hD_eq : D = star U * M * U := by
      rw [hM_spec, mul_assoc, mul_assoc, mul_assoc, hUstarU, mul_one, ← mul_assoc, hUstarU, one_mul]
    calc ‖D‖ = ‖star U * M * U‖ := by rw [hD_eq]
      _ ≤ ‖star U * M‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖star U‖ * ‖M‖ * ‖U‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖M‖ := by rw [hUstar_norm, hU_norm, one_mul, mul_one]
      _ ≤ 1 := hM_norm
  -- Each eigenvalue ≤ 1
  have h_le1 : ∀ i, evs i ≤ 1 := by
    intro i
    rw [show ‖D‖ = ‖(RCLike.ofReal ∘ evs : Fin d → ℂ)‖ from
      Matrix.l2_opNorm_diagonal _] at hD_le
    have h1 := norm_le_pi_norm (RCLike.ofReal ∘ evs : Fin d → ℂ) i
    simp only [Function.comp, RCLike.norm_ofReal, abs_of_nonneg (h_nn i)] at h1
    linarith
  -- 1 - M = U (1 - D) U†
  have h_1M : 1 - M = U * (1 - D) * star U := by
    symm; calc U * (1 - D) * star U
        = (U - U * D) * star U := by rw [mul_sub, Matrix.mul_one]
      _ = U * star U - U * D * star U := by rw [sub_mul]
      _ = 1 - M := by rw [hUUstar, hM_spec]
  have h_1D_psd : (1 - D).PosSemidef := by
    rw [show 1 - D = diagonal (fun i => 1 - (RCLike.ofReal ∘ evs) i)
      from by rw [hD_def, ← diagonal_one, diagonal_sub]]
    rw [posSemidef_diagonal_iff]
    intro i
    simp only [Function.comp, sub_nonneg]
    exact RCLike.ofReal_le_ofReal.mpr (h_le1 i)
  rw [h_1M]
  exact (IsUnit.of_mul_eq_one (star U) hUUstar).posSemidef_star_right_conjugate_iff.mpr h_1D_psd

/-- **Operator ordering monotonicity under conjugation**: If `A ≤ B` then
    `R† * A * R ≤ R† * B * R` (conjugation by `R†` preserves the ordering). -/
lemma conjTranspose_mul_le_conjTranspose_mul {d : ℕ}
    (A B R : Op d) (hle : A ≤ B) :
    R.conjTranspose * A * R ≤ R.conjTranspose * B * R := by
  rw [Matrix.le_iff] at hle ⊢
  rw [show Rᴴ * B * R - Rᴴ * A * R = Rᴴ * (B - A) * R from by
    rw [mul_sub, sub_mul]]
  exact hle.conjTranspose_mul_mul_same _

/-- **Trace monotonicity**: If `A ≤ B` then `Tr(A).re ≤ Tr(B).re`. -/
lemma trace_re_le_of_le {d : ℕ} (A B : Op d)
    (hle : A ≤ B) : A.trace.re ≤ B.trace.re := by
  rw [Matrix.le_iff] at hle
  have h := hle.trace_nonneg
  rw [Matrix.trace_sub] at h
  -- 0 ≤ (B.trace - A.trace) in ComplexOrder means re ≥ 0
  have hre := (Complex.nonneg_iff.mp h).1
  simp only [Complex.sub_re] at hre
  linarith

/-- The CFC square root of a positive semidefinite operator squares to the operator. -/
lemma cfc_sqrt_mul_self_of_posSemidef {d : ℕ}
    (P : Op d) (hP : P.PosSemidef) :
    CFC.sqrt P * CFC.sqrt P = P := by
  exact CFC.sqrt_mul_sqrt_self P (ha := hP.nonneg)

/-- **PSD column decomposition via square root**: A PSD matrix decomposes as a sum of
    rank-1 PSD terms using columns of its positive square root.

    `P = Σ_a vecMulVec(√P e_a)(star(√P e_a))` where `e_a = Pi.single a 1`. -/
lemma psd_eq_sum_vecMulVec_sqrt_cols {d : ℕ}
    (P : Op d) (hP : P.PosSemidef) :
    P = ∑ a : Fin d, vecMulVec ((CFC.sqrt P).mulVec (Pi.single a 1))
      (star ((CFC.sqrt P).mulVec (Pi.single a 1))) := by
  set R := CFC.sqrt P
  have hR_herm : Rᴴ = R :=
    by simpa [R] using cfc_sqrt_conjTranspose_eq P
  calc P = R * R := by
        simpa [R] using (cfc_sqrt_mul_self_of_posSemidef P hP).symm
    _ = R * Rᴴ := by rw [hR_herm]
    _ = ∑ a, vecMulVec (R.mulVec (Pi.single a 1))
        (star (R.mulVec (Pi.single a 1))) :=
      mul_conjTranspose_eq_sum_vecMulVec R R

/-- **Product column decomposition**: `V * P` decomposes as a sum of rank-1 terms
    using columns of `V * √P` and `√P`.

    `V * P = Σ_a vecMulVec((V√P) e_a)(star(√P e_a))`. -/
lemma mul_psd_eq_sum_vecMulVec_sqrt {d : ℕ}
    (V P : Op d) (hP : P.PosSemidef) :
    V * P = ∑ a : Fin d, vecMulVec ((V * CFC.sqrt P).mulVec (Pi.single a 1))
      (star ((CFC.sqrt P).mulVec (Pi.single a 1))) := by
  set R := CFC.sqrt P
  have hR_herm : Rᴴ = R :=
    by simpa [R] using cfc_sqrt_conjTranspose_eq P
  calc V * P = V * (R * R) := by
        simpa [R] using congrArg (fun M => V * M) (cfc_sqrt_mul_self_of_posSemidef P hP).symm
    _ = V * R * R := by rw [mul_assoc]
    _ = V * R * Rᴴ := by rw [hR_herm]
    _ = ∑ a, vecMulVec ((V * R).mulVec (Pi.single a 1))
        (star (R.mulVec (Pi.single a 1))) :=
      mul_conjTranspose_eq_sum_vecMulVec (V * R) R

/-- Partial trace of a PSD matrix decomposed by square-root columns.

    This isolates the exact `B * Bᴴ` family that appears on the right side of the
    intended Douglas/common-family step for `V * P`. -/
lemma partialTraceB_psd_eq_sum_reshapeVec_sqrt_cols {n : ℕ}
    (P : Op (n * n)) (hP : P.PosSemidef) :
    partialTraceB P =
      ∑ a : Fin (n * n),
        reshapeVec ((CFC.sqrt P).mulVec (Pi.single a 1)) *
          (reshapeVec ((CFC.sqrt P).mulVec (Pi.single a 1)))ᴴ := by
  have h_cols := psd_eq_sum_vecMulVec_sqrt_cols P hP
  calc
    partialTraceB P
      = partialTraceB (∑ a : Fin (n * n),
          vecMulVec ((CFC.sqrt P).mulVec (Pi.single a 1))
            (star ((CFC.sqrt P).mulVec (Pi.single a 1)))) := by
          simpa using congrArg partialTraceB h_cols
    _ = ∑ a : Fin (n * n),
          reshapeVec ((CFC.sqrt P).mulVec (Pi.single a 1)) *
            (reshapeVec ((CFC.sqrt P).mulVec (Pi.single a 1)))ᴴ :=
        partialTraceB_sum_vecMulVec_eq
          (fun a : Fin (n * n) => (CFC.sqrt P).mulVec (Pi.single a 1))

/-- Partial trace of `V * P * V†` decomposed by the columns of `V * √P`.

    Together with `partialTraceB_psd_eq_sum_reshapeVec_sqrt_cols`, this packages
    the concrete matrix families
    `A_a := reshapeVec ((V * √P) e_a)` and `B_a := reshapeVec (√P e_a)`
    that any same-size Douglas-style bridge must compare. -/
lemma partialTraceB_mul_psd_mul_conjTranspose_eq_sum_reshapeVec_mul_sqrt_cols {n : ℕ}
    (V P : Op (n * n)) (hP : P.PosSemidef) :
    partialTraceB (V * P * Vᴴ) =
      ∑ a : Fin (n * n),
        reshapeVec ((V * CFC.sqrt P).mulVec (Pi.single a 1)) *
          (reshapeVec ((V * CFC.sqrt P).mulVec (Pi.single a 1)))ᴴ := by
  set R := CFC.sqrt P
  have hR_herm : Rᴴ = R :=
    by simpa [R] using cfc_sqrt_conjTranspose_eq P
  have h_eq : V * P * Vᴴ = (V * R) * (V * R)ᴴ := by
    calc
      V * P * Vᴴ = V * (R * R) * Vᴴ := by
            simpa [R] using congrArg (fun M => V * M * Vᴴ)
              (cfc_sqrt_mul_self_of_posSemidef P hP).symm
      _ = V * R * R * Vᴴ := by simp [Matrix.mul_assoc]
      _ = V * R * Rᴴ * Vᴴ := by rw [hR_herm]
      _ = (V * R) * (V * R)ᴴ := by simp [Matrix.mul_assoc]
  have h_cols : V * P * Vᴴ =
      ∑ a : Fin (n * n),
        vecMulVec ((V * R).mulVec (Pi.single a 1))
          (star ((V * R).mulVec (Pi.single a 1))) := by
    calc
      V * P * Vᴴ = (V * R) * (V * R)ᴴ := h_eq
      _ = ∑ a : Fin (n * n),
            vecMulVec ((V * R).mulVec (Pi.single a 1))
              (star ((V * R).mulVec (Pi.single a 1))) :=
          mul_conjTranspose_eq_sum_vecMulVec (V * R) (V * R)
  calc
    partialTraceB (V * P * Vᴴ)
      = partialTraceB (∑ a : Fin (n * n),
          vecMulVec ((V * R).mulVec (Pi.single a 1))
            (star ((V * R).mulVec (Pi.single a 1)))) := by
          simpa using congrArg partialTraceB h_cols
    _ = ∑ a : Fin (n * n),
          reshapeVec ((V * R).mulVec (Pi.single a 1)) *
            (reshapeVec ((V * R).mulVec (Pi.single a 1)))ᴴ :=
        partialTraceB_sum_vecMulVec_eq
          (fun a : Fin (n * n) => (V * R).mulVec (Pi.single a 1))

/-- Partial trace over the A-factor of a PSD matrix decomposed by square-root columns.

    This is the `partialTraceA` analogue of
    `partialTraceB_psd_eq_sum_reshapeVec_sqrt_cols`, and isolates the transposed
    families `B_aᵀ` that belong to the right-Gram route. -/
lemma partialTraceA_psd_eq_sum_reshapeVec_transpose_sqrt_cols {n : ℕ}
    (P : Op (n * n)) (hP : P.PosSemidef) :
    partialTraceA P =
      ∑ a : Fin (n * n),
        (reshapeVec ((CFC.sqrt P).mulVec (Pi.single a 1)))ᵀ *
          ((reshapeVec ((CFC.sqrt P).mulVec (Pi.single a 1)))ᵀ)ᴴ := by
  have h_cols := psd_eq_sum_vecMulVec_sqrt_cols P hP
  calc
    partialTraceA P
      = partialTraceA (∑ a : Fin (n * n),
          vecMulVec ((CFC.sqrt P).mulVec (Pi.single a 1))
            (star ((CFC.sqrt P).mulVec (Pi.single a 1)))) := by
          simpa using congrArg partialTraceA h_cols
    _ = ∑ a : Fin (n * n),
          (reshapeVec ((CFC.sqrt P).mulVec (Pi.single a 1)))ᵀ *
            ((reshapeVec ((CFC.sqrt P).mulVec (Pi.single a 1)))ᵀ)ᴴ :=
        partialTraceA_sum_vecMulVec_eq
          (fun a : Fin (n * n) => (CFC.sqrt P).mulVec (Pi.single a 1))

/-- Partial trace over the A-factor of `V * P * V†` decomposed by the columns of
    `V * √P`.

    This packages the exact family
    `A_a := (reshapeVec ((V * √P) e_a))ᵀ`
    whose left-Gram sum is `partialTraceA (V * P * V†)`. -/
lemma partialTraceA_mul_psd_mul_conjTranspose_eq_sum_reshapeVec_transpose_mul_sqrt_cols
    {n : ℕ} (V P : Op (n * n)) (hP : P.PosSemidef) :
    partialTraceA (V * P * Vᴴ) =
      ∑ a : Fin (n * n),
        (reshapeVec ((V * CFC.sqrt P).mulVec (Pi.single a 1)))ᵀ *
          ((reshapeVec ((V * CFC.sqrt P).mulVec (Pi.single a 1)))ᵀ)ᴴ := by
  set R := CFC.sqrt P
  have hR_herm : Rᴴ = R :=
    by simpa [R] using cfc_sqrt_conjTranspose_eq P
  have h_eq : V * P * Vᴴ = (V * R) * (V * R)ᴴ := by
    calc
      V * P * Vᴴ = V * (R * R) * Vᴴ := by
            simpa [R] using congrArg (fun M => V * M * Vᴴ)
              (cfc_sqrt_mul_self_of_posSemidef P hP).symm
      _ = V * R * R * Vᴴ := by simp [Matrix.mul_assoc]
      _ = V * R * Rᴴ * Vᴴ := by rw [hR_herm]
      _ = (V * R) * (V * R)ᴴ := by simp [Matrix.mul_assoc]
  have h_cols : V * P * Vᴴ =
      ∑ a : Fin (n * n),
        vecMulVec ((V * R).mulVec (Pi.single a 1))
          (star ((V * R).mulVec (Pi.single a 1))) := by
    calc
      V * P * Vᴴ = (V * R) * (V * R)ᴴ := h_eq
      _ = ∑ a : Fin (n * n),
            vecMulVec ((V * R).mulVec (Pi.single a 1))
              (star ((V * R).mulVec (Pi.single a 1))) :=
          mul_conjTranspose_eq_sum_vecMulVec (V * R) (V * R)
  calc
    partialTraceA (V * P * Vᴴ)
      = partialTraceA (∑ a : Fin (n * n),
          vecMulVec ((V * R).mulVec (Pi.single a 1))
            (star ((V * R).mulVec (Pi.single a 1)))) := by
          simpa using congrArg partialTraceA h_cols
    _ = ∑ a : Fin (n * n),
          (reshapeVec ((V * R).mulVec (Pi.single a 1)))ᵀ *
            ((reshapeVec ((V * R).mulVec (Pi.single a 1)))ᵀ)ᴴ :=
        partialTraceA_sum_vecMulVec_eq
          (fun a : Fin (n * n) => (V * R).mulVec (Pi.single a 1))

/-- The exact right-Gram domination implied by `1 - V†V ≥ 0`.

    Conjugating `V†V ≤ 1` by `√P` yields the only immediate Douglas-compatible
    inequality on the contraction side:
    `(V√P)† (V√P) ≤ P`. -/
lemma mul_sqrt_right_gram_le_of_one_sub_conjTranspose_mul_psd {d : ℕ}
    (V P : Op d) (hV : (1 - V.conjTranspose * V).PosSemidef) (hP : P.PosSemidef) :
    (V * CFC.sqrt P)ᴴ * (V * CFC.sqrt P) ≤ P := by
  set R := CFC.sqrt P
  have hle : Vᴴ * V ≤ (1 : Op d) := by
    rw [Matrix.le_iff]
    simpa using hV
  have h_conj :=
    conjTranspose_mul_le_conjTranspose_mul
      (A := Vᴴ * V) (B := (1 : Op d)) (R := R) hle
  have hR_herm : Rᴴ = R :=
    by simpa [R] using cfc_sqrt_conjTranspose_eq P
  simpa [R, hR_herm, Matrix.mul_assoc, cfc_sqrt_mul_self_of_posSemidef P hP] using h_conj

/-- PSD reformulation of the right-Gram domination from
    `mul_sqrt_right_gram_le_of_one_sub_conjTranspose_mul_psd`. -/
lemma sub_mul_sqrt_right_gram_psd_of_one_sub_conjTranspose_mul_psd {d : ℕ}
    (V P : Op d) (hV : (1 - V.conjTranspose * V).PosSemidef) (hP : P.PosSemidef) :
    (P - (V * CFC.sqrt P)ᴴ * (V * CFC.sqrt P)).PosSemidef :=
  Matrix.le_iff.mp
    (mul_sqrt_right_gram_le_of_one_sub_conjTranspose_mul_psd V P hV hP)

/-- Douglas applied to the right-Gram domination yields only a contraction-middle
    factorization `V * P = C * P`.

    This is the exact outcome of the `partialTraceA` / right-Gram route before any
    additional tensor-structure argument is supplied. -/
lemma contraction_middle_factorization_of_one_sub_conjTranspose_mul_psd {d : ℕ}
    (V P : Op d) (hV : (1 - V.conjTranspose * V).PosSemidef) (hP : P.PosSemidef) :
    ∃ C : Op d, V * P = C * P ∧ (1 - Cᴴ * C).PosSemidef := by
  set R := CFC.sqrt P
  have hR_herm : Rᴴ = R :=
    by simpa [R] using cfc_sqrt_conjTranspose_eq P
  have h_dom : (R * Rᴴ -
      ∑ k : Fin 1, (fun _ => (V * R)ᴴ) k * ((fun _ => (V * R)ᴴ) k)ᴴ).PosSemidef := by
    simpa [R, Fin.sum_univ_one, hR_herm, Matrix.mul_assoc,
      cfc_sqrt_mul_self_of_posSemidef P hP] using
      sub_mul_sqrt_right_gram_psd_of_one_sub_conjTranspose_mul_psd V P hV hP
  obtain ⟨C, hC_eq, hC_bound⟩ :=
    matrix_douglas_factorization (fun _ : Fin 1 => (V * R)ᴴ) R h_dom
  refine ⟨(C 0)ᴴ, ?_, ?_⟩
  · have h0 := congrArg Matrix.conjTranspose (hC_eq 0)
    calc
      V * P = V * (R * R) := by
            simpa [R] using congrArg (fun M => V * M) (cfc_sqrt_mul_self_of_posSemidef P hP).symm
      _ = (V * R) * R := by simp [Matrix.mul_assoc]
      _ = ((C 0)ᴴ * R) * R := by
            simp only [conjTranspose_mul, conjTranspose_conjTranspose, hR_herm] at h0
            rw [h0]
      _ = (C 0)ᴴ * P := by rw [Matrix.mul_assoc, cfc_sqrt_mul_self_of_posSemidef P hP]
  · simpa [Fin.sum_univ_one]
      using hC_bound

/-- The PSD square root of X†X has trace norm equal to traceNorm X.
    Key identity: `traceNorm(√(X†X)) = traceNorm(X)`. -/
lemma traceNorm_sqrt_conjTranspose_mul_self {d : ℕ} [NeZero d] (X : Op d) :
    traceNorm (CFC.sqrt (X.conjTranspose * X)) = traceNorm X := by
  apply TraceNormHoelder.traceNorm_eq_of_conjTranspose_mul_self_eq
  have hXHX_nn : (0 : Op d) ≤ X.conjTranspose * X :=
    (posSemidef_conjTranspose_mul_self X).nonneg
  have hP_psd : (CFC.sqrt (X.conjTranspose * X)).PosSemidef :=
    (CFC.sqrt_nonneg (X.conjTranspose * X)).posSemidef
  rw [hP_psd.isHermitian.eq]
  exact CFC.sqrt_mul_sqrt_self (X.conjTranspose * X) (ha := hXHX_nn)

/-- **Polar decomposition with operator norm bound**: Any matrix `X` decomposes as
    `X = V * P` where `P` is PSD, `Tr(P).re = traceNorm X`, and `‖V‖ ≤ 1`.

    This is the shared polar-decomposition input used by the Kitaev-Watrous
    contraction reduction. -/
lemma polar_decomposition_norm {d : ℕ} [NeZero d] (X : Op d) :
    ∃ (V P : Op d), P.PosSemidef ∧ X = V * P ∧
      P.trace.re = traceNorm X ∧ ‖V‖ ≤ 1 := by
  set P := CFC.sqrt (X.conjTranspose * X) with hP_def
  have hXHX_nn : (0 : Op d) ≤ X.conjTranspose * X :=
    (posSemidef_conjTranspose_mul_self X).nonneg
  have hP_psd : P.PosSemidef := (CFC.sqrt_nonneg (X.conjTranspose * X)).posSemidef
  have hP_herm : P.conjTranspose = P := hP_psd.isHermitian.eq
  have hPP : P * P = X.conjTranspose * X :=
    CFC.sqrt_mul_sqrt_self (X.conjTranspose * X) (ha := hXHX_nn)
  have hP_trace : P.trace.re = traceNorm X := by
    rw [← traceNorm_sqrt_conjTranspose_mul_self X, ← hP_def]
    exact (traceNorm_posSemidef_eq_trace P hP_psd).symm
  -- Douglas factorization: X† = P * C₀ with (I - C₀C₀†) PSD
  have h_dom : (P * P.conjTranspose -
      ∑ k : Fin 1, (fun _ => X.conjTranspose) k *
        ((fun _ => X.conjTranspose) k).conjTranspose).PosSemidef := by
    simp only [Fin.sum_univ_one, hP_herm, conjTranspose_conjTranspose, hPP, sub_self]
    exact Matrix.PosSemidef.zero
  obtain ⟨C, hC_eq, hC_bound⟩ :=
    matrix_douglas_factorization (fun _ : Fin 1 => X.conjTranspose) P h_dom
  set V := (C 0).conjTranspose with hV_def
  have hVP : X = V * P := by
    have h := hC_eq 0
    have := congr_arg Matrix.conjTranspose h
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP_herm] at this
    exact this
  have hV_norm : ‖V‖ ≤ 1 := by
    apply opNorm_le_one_of_one_sub_conjTranspose_mul_psd
    have hcb := hC_bound
    simp only [Fin.sum_univ_one] at hcb
    convert hcb using 1
    rw [hV_def, conjTranspose_conjTranspose]
  exact ⟨V, P, hP_psd, hVP, hP_trace, hV_norm⟩

/-- Operator norm of PSD square root: `‖√P‖ ≤ 1` when `P` is PSD with `‖P‖ ≤ 1`.
    Proof: `‖√P‖² = ‖(√P)†(√P)‖ = ‖P‖ ≤ 1` by C*-identity and `(√P)² = P`. -/
lemma opNorm_sqrt_le_one {d : ℕ} [NeZero d]
    (P : Op d) (hP : P.PosSemidef) (hP_norm : ‖P‖ ≤ 1) :
    ‖CFC.sqrt P‖ ≤ 1 := by
  set R := CFC.sqrt P
  have hR_herm : R.conjTranspose = R :=
    ((CFC.sqrt_nonneg (A := Op d) P).posSemidef).isHermitian.eq
  suffices h : ‖R‖ * ‖R‖ ≤ 1 by nlinarith [norm_nonneg R]
  calc ‖R‖ * ‖R‖ = ‖R.conjTranspose * R‖ :=
        (Matrix.l2_opNorm_conjTranspose_mul_self R).symm
    _ = ‖R * R‖ := by rw [hR_herm]
    _ = ‖P‖ := by rw [CFC.sqrt_mul_sqrt_self P (ha := hP.nonneg)]
    _ ≤ 1 := hP_norm

/-- `V * P * V†` is positive semidefinite whenever `P` is. -/
lemma conj_conjTranspose_posSemidef {d : ℕ} (V P : Op d) (hP : P.PosSemidef) :
    (V * P * Vᴴ).PosSemidef := by
  have h := hP.conjTranspose_mul_mul_same (B := Vᴴ)
  simpa [conjTranspose_conjTranspose] using h

/-- Trace bound for the conjugation sandwich: if `‖V‖ ≤ 1` and `P` is PSD, then
    `Tr(V * P * V†).re ≤ Tr(P).re`.

    Proof: `Tr(V P V†) = Tr(√P V† V √P)` by cyclicity, and
    `√P V† V √P ≤ √P √P = P` since `V†V ≤ 1`. -/
lemma trace_re_conj_conjTranspose_le {d : ℕ} [NeZero d]
    (V P : Op d) (hP : P.PosSemidef) (hV : (1 - Vᴴ * V).PosSemidef) :
    (V * P * Vᴴ).trace.re ≤ P.trace.re := by
  set R := CFC.sqrt P with hR_def
  have hR_psd : R.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hR_herm : Rᴴ = R := hR_psd.isHermitian.eq
  have hRR : R * R = P := cfc_sqrt_mul_self_of_posSemidef P hP
  -- Cyclicity: Tr(V P V†) = Tr(V R R V†) = Tr(R V† V R) = Tr(V† V R R) = Tr(V† V P)
  -- We use trace_mul_cycle.
  have h_trace_eq : (V * P * Vᴴ).trace = (Rᴴ * Vᴴ * V * R).trace := by
    calc (V * P * Vᴴ).trace
        = (V * (R * R) * Vᴴ).trace := by rw [hRR]
      _ = (V * R * R * Vᴴ).trace := by rw [Matrix.mul_assoc V R R]
      _ = (Vᴴ * (V * R) * R).trace := by
            rw [show V * R * R * Vᴴ = (V * R) * R * Vᴴ from rfl,
                Matrix.trace_mul_cycle (V * R) R Vᴴ, Matrix.mul_assoc]
      _ = (R * (Vᴴ * (V * R))).trace := Matrix.trace_mul_comm _ _
      _ = (Rᴴ * Vᴴ * V * R).trace := by rw [hR_herm, Matrix.mul_assoc, Matrix.mul_assoc]
  -- Now use R† A R ≤ R† B R with A = V†V, B = 1.
  have hle : Vᴴ * V ≤ (1 : Op d) := by
    rw [Matrix.le_iff]; simpa using hV
  have h_conj := conjTranspose_mul_le_conjTranspose_mul
    (A := Vᴴ * V) (B := (1 : Op d)) (R := R) hle
  -- R† (V†V) R ≤ R† 1 R = R† R = P
  have h_rhs_eq : Rᴴ * (1 : Op d) * R = P := by
    rw [Matrix.mul_one, hR_herm, hRR]
  have h_lhs_eq : Rᴴ * (Vᴴ * V) * R = Rᴴ * Vᴴ * V * R := by
    rw [Matrix.mul_assoc Rᴴ Vᴴ V, Matrix.mul_assoc]
  rw [h_rhs_eq, h_lhs_eq] at h_conj
  have h_tr_le := trace_re_le_of_le _ _ h_conj
  rw [← h_trace_eq] at h_tr_le
  exact h_tr_le

/-- Partial trace (B) of `V * P * V†` is PSD. -/
lemma partialTraceB_conj_conjTranspose_posSemidef {n : ℕ}
    (V P : Op (n * n)) (hP : P.PosSemidef) :
    (partialTraceB (V * P * Vᴴ)).PosSemidef :=
  partialTraceB_posSemidef_mathlib _ (conj_conjTranspose_posSemidef V P hP)

/-- Partial trace (A) of `V * P * V†` is PSD. -/
lemma partialTraceA_conj_conjTranspose_posSemidef {n : ℕ}
    (V P : Op (n * n)) (hP : P.PosSemidef) :
    (partialTraceA (V * P * Vᴴ)).PosSemidef :=
  partialTraceA_posSemidef_mathlib _ (conj_conjTranspose_posSemidef V P hP)

/-- Trace bound on `partialTraceB (V P V†)`: if `‖V‖ ≤ 1` and `P` PSD then
    `Tr(partialTraceB(V P V†)).re ≤ Tr(P).re`. -/
lemma trace_re_partialTraceB_conj_le {n : ℕ} [NeZero n]
    (V P : Op (n * n)) (hP : P.PosSemidef) (hV : (1 - Vᴴ * V).PosSemidef) :
    (partialTraceB (V * P * Vᴴ)).trace.re ≤ P.trace.re := by
  rw [show (partialTraceB (V * P * Vᴴ)).trace = (V * P * Vᴴ).trace from
        trace_partialTraceB (V * P * Vᴴ)]
  exact trace_re_conj_conjTranspose_le V P hP hV

/-- Trace bound on `partialTraceA (V P V†)`. -/
lemma trace_re_partialTraceA_conj_le {n : ℕ} [NeZero n]
    (V P : Op (n * n)) (hP : P.PosSemidef) (hV : (1 - Vᴴ * V).PosSemidef) :
    (partialTraceA (V * P * Vᴴ)).trace.re ≤ P.trace.re := by
  rw [show (partialTraceA (V * P * Vᴴ)).trace = (V * P * Vᴴ).trace from
        trace_partialTraceA (V * P * Vᴴ)]
  exact trace_re_conj_conjTranspose_le V P hP hV

/-- `‖√(partialTraceB (V P V†))‖ ≤ 1` when `V` is a contraction and `P` has trace ≤ 1. -/
lemma opNorm_sqrt_partialTraceB_conj_le_one {n : ℕ} [NeZero (n * n)]
    (V P : Op (n * n)) (hP : P.PosSemidef) (hP_tr : P.trace.re ≤ 1)
    (hV : (1 - Vᴴ * V).PosSemidef) :
    ‖CFC.sqrt (partialTraceB (V * P * Vᴴ))‖ ≤ 1 := by
  haveI : NeZero n := by
    refine ⟨fun h => ?_⟩
    have : n * n = 0 := by simp [h]
    exact NeZero.ne _ this
  have hT_psd := partialTraceB_conj_conjTranspose_posSemidef V P hP
  have hT_tr : (partialTraceB (V * P * Vᴴ)).trace.re ≤ 1 :=
    le_trans (trace_re_partialTraceB_conj_le V P hP hV) hP_tr
  have hT_norm := opNorm_le_one_of_posSemidef_trace_le _ hT_psd hT_tr
  exact opNorm_sqrt_le_one _ hT_psd hT_norm

/-- `‖√(partialTraceA (V P V†))‖ ≤ 1` when `V` is a contraction and `P` has trace ≤ 1. -/
lemma opNorm_sqrt_partialTraceA_conj_le_one {n : ℕ} [NeZero (n * n)]
    (V P : Op (n * n)) (hP : P.PosSemidef) (hP_tr : P.trace.re ≤ 1)
    (hV : (1 - Vᴴ * V).PosSemidef) :
    ‖CFC.sqrt (partialTraceA (V * P * Vᴴ))‖ ≤ 1 := by
  haveI : NeZero n := by
    refine ⟨fun h => ?_⟩
    have : n * n = 0 := by simp [h]
    exact NeZero.ne _ this
  have hT_psd := partialTraceA_conj_conjTranspose_posSemidef V P hP
  have hT_tr : (partialTraceA (V * P * Vᴴ)).trace.re ≤ 1 :=
    le_trans (trace_re_partialTraceA_conj_le V P hP hV) hP_tr
  have hT_norm := opNorm_le_one_of_posSemidef_trace_le _ hT_psd hT_tr
  exact opNorm_sqrt_le_one _ hT_psd hT_norm

/-- **A-side Douglas factorization for the Watrous construction.**

    Given `V, P : Op (n*n)` with `P` PSD, set
    `T_A := partialTraceB (V * P * V†)` and `A₀ := √T_A`.
    Then the columns `Xₐ := reshapeVec ((V √P) eₐ)` all lie in the range of `A₀`:
    there exist `Cₐ : Op n` with `Xₐ = A₀ * Cₐ` and
    `Σₐ Cₐ Cₐ† ≤ I`.

    This is the left half of the Watrous cross-side construction. -/
lemma watrous_A_side_douglas_factorization {n : ℕ}
    (V P : Op (n * n)) (hP : P.PosSemidef) :
    ∃ C : Fin (n * n) → Op n,
      (∀ a, reshapeVec ((V * CFC.sqrt P).mulVec (Pi.single a 1))
              = CFC.sqrt (partialTraceB (V * P * Vᴴ)) * C a) ∧
      ((1 : Op n) - ∑ a, C a * (C a)ᴴ).PosSemidef := by
  set TA : Op n := partialTraceB (V * P * Vᴴ) with hTA_def
  set A₀ : Op n := CFC.sqrt TA with hA₀_def
  have hTA_psd : TA.PosSemidef :=
    partialTraceB_conj_conjTranspose_posSemidef V P hP
  have hA₀_psd : A₀.PosSemidef := (CFC.sqrt_nonneg TA).posSemidef
  have hA₀_herm : A₀ᴴ = A₀ := hA₀_psd.isHermitian.eq
  have hA₀A₀ : A₀ * A₀ = TA := cfc_sqrt_mul_self_of_posSemidef TA hTA_psd
  -- Sum decomposition: T_A = Σ_a X_a X_a†
  have h_sum :=
    partialTraceB_mul_psd_mul_conjTranspose_eq_sum_reshapeVec_mul_sqrt_cols V P hP
  -- A₀ A₀† - Σ_a X_a X_a† = 0, PSD
  have h_dom : (A₀ * A₀ᴴ -
      ∑ a : Fin (n * n),
        (fun b : Fin (n * n) =>
          reshapeVec ((V * CFC.sqrt P).mulVec (Pi.single b 1))) a *
        ((fun b : Fin (n * n) =>
          reshapeVec ((V * CFC.sqrt P).mulVec (Pi.single b 1))) a)ᴴ).PosSemidef := by
    rw [hA₀_herm, hA₀A₀, hTA_def, h_sum, sub_self]
    exact Matrix.PosSemidef.zero
  exact matrix_douglas_factorization
    (fun b : Fin (n * n) =>
      reshapeVec ((V * CFC.sqrt P).mulVec (Pi.single b 1)))
    A₀ h_dom

/-- **B-side Douglas factorization for the Watrous construction.**

    Given `P : Op (n*n)` PSD, set `T_B := partialTraceA P` and
    `B₀ᵀ := √T_B`, equivalently `B₀` is the transpose of `√(partialTraceA P)`.
    The transposed columns `Yₐ := (reshapeVec (√P eₐ))ᵀ` lie in the range of `B₀ᵀ`:
    there exist `Dₐ` with `Yₐ = B₀ᵀ * Dₐ` and `Σₐ Dₐ Dₐ† ≤ I`.

    This is the right half of the Watrous cross-side construction, expressed
    on the A-partial-trace (transposed) side. -/
lemma watrous_B_side_douglas_factorization {n : ℕ}
    (P : Op (n * n)) (hP : P.PosSemidef) :
    ∃ D : Fin (n * n) → Op n,
      (∀ a, (reshapeVec ((CFC.sqrt P).mulVec (Pi.single a 1)))ᵀ
              = CFC.sqrt (partialTraceA P) * D a) ∧
      ((1 : Op n) - ∑ a, D a * (D a)ᴴ).PosSemidef := by
  set TB : Op n := partialTraceA P with hTB_def
  set B₀ : Op n := CFC.sqrt TB with hB₀_def
  have hTB_psd : TB.PosSemidef := partialTraceA_posSemidef_mathlib P hP
  have hB₀_psd : B₀.PosSemidef := (CFC.sqrt_nonneg TB).posSemidef
  have hB₀_herm : B₀ᴴ = B₀ := hB₀_psd.isHermitian.eq
  have hB₀B₀ : B₀ * B₀ = TB := cfc_sqrt_mul_self_of_posSemidef TB hTB_psd
  have h_sum :=
    partialTraceA_psd_eq_sum_reshapeVec_transpose_sqrt_cols P hP
  have h_dom : (B₀ * B₀ᴴ -
      ∑ a : Fin (n * n),
        (fun b : Fin (n * n) =>
          (reshapeVec ((CFC.sqrt P).mulVec (Pi.single b 1)))ᵀ) a *
        ((fun b : Fin (n * n) =>
          (reshapeVec ((CFC.sqrt P).mulVec (Pi.single b 1)))ᵀ) a)ᴴ).PosSemidef := by
    rw [hB₀_herm, hB₀B₀, hTB_def, h_sum, sub_self]
    exact Matrix.PosSemidef.zero
  exact matrix_douglas_factorization
    (fun b : Fin (n * n) =>
      (reshapeVec ((CFC.sqrt P).mulVec (Pi.single b 1)))ᵀ)
    B₀ h_dom

end Quantum.Metrics.WatrousFactorization
