import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.Math.SpectralTheory.Basic
import QCryptLean.Math.SpectralTheory.Weyl

/-!
# Trace Norm and Trace Distance — Hermitian formulas, eigenvalue bounds, projector estimates

Trace-norm and trace-distance infrastructure for quantum states, together with
Hermitian spectral lemmas used by downstream distance-bound arguments.

## Main definitions
- `traceNorm`: trace norm `‖A‖₁ = Σᵢ σᵢ` for arbitrary matrices
- `traceNormHermitian`: trace norm `‖A‖₁ = Σᵢ |λᵢ|` for Hermitian matrices
- `traceDistance`: trace distance `D(A,B) = (1/2)‖A-B‖₁`
- `DensityOp.traceDistance`: trace distance for density operators

## Main statements
- `traceNorm_hermitian_eq`: `traceNorm = traceNormHermitian` for Hermitian matrices
- `traceDistance_densityOp_eq_traceNormHermitian`: density-operator bridge to Hermitian trace norm
- `traceDistance_nonneg`, `traceDistance_nonneg_densityOp`: nonnegativity of trace distance
- `sum_eigenbasis_quadraticForm_eq_trace`: eigenbasis quadratic-form sum equals trace
- `traceNormHermitian_eq_zero_iff`: vanishing Hermitian trace norm iff the matrix is zero
- `traceNormHermitian_triangle`: triangle inequality for Hermitian trace norm
- `density_sq_quadform_le`: `⟨v|ρ²|v⟩ ≤ ⟨v|ρ|v⟩` for density operators
- `projector_trace_re_le_traceNormHermitian`: `|Tr(PA).re| ≤ ‖A‖₁` for Hermitian `A`
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-!
## Trace Distance

The trace distance `D(ρ,σ) = (1/2)||ρ - σ||₁` where `||A||₁` is the trace norm.
For Hermitian matrices, this equals the sum of the absolute values of the eigenvalues.
-/

/-- The difference of two density operators is Hermitian. -/
lemma densityOp_sub_isHermitian {n : ℕ} (ρ σ : DensityOp n) :
    (ρ.toOp - σ.toOp).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub]
  rw [ρ.toPosSemidefOp.toHermitianOp.isHermitian]
  rw [σ.toPosSemidefOp.toHermitianOp.isHermitian]

/-- Dotting the `i`-th column of `U` against `A` times that column produces the
    `(i,i)`-entry of `U† A U`. -/
lemma dot_col_eq_entry {n : ℕ} (U A : Op n) (i : Fin n) :
    star (fun j => U j i) ⬝ᵥ (A.mulVec (fun j => U j i)) = (U† * A * U) i i := by
  simp only [dotProduct, mulVec, mul_apply, conjTranspose_apply, Finset.sum_mul, Pi.star_apply]
  rw [Finset.sum_comm]
  congr 1; ext j
  rw [Finset.mul_sum]
  congr 1; ext k
  ring_nf

/-- The sum of ⟨vᵢ|ρ|vᵢ⟩ over an orthonormal eigenbasis equals Tr(ρ). -/
lemma sum_eigenbasis_quadraticForm_eq_trace {n : ℕ} [NeZero n] (ρ : DensityOp n)
    {A : Op n} (hA : A.IsHermitian) :
    ∑ i, (star (hA.eigenvectorUnitary.val · i) ⬝ᵥ
          (ρ.toOp.mulVec (hA.eigenvectorUnitary.val · i))).re = ρ.toOp.trace.re := by
  let U := hA.eigenvectorUnitary.val
  have h_UU' : U * U† = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have h_cyc : (U† * ρ.toOp * U).trace = ρ.toOp.trace := by
    calc (U† * ρ.toOp * U).trace
        = (U† * (ρ.toOp * U)).trace := by rw [mul_assoc]
      _ = (ρ.toOp * U * U†).trace := by rw [trace_mul_comm U† (ρ.toOp * U)]
      _ = (ρ.toOp * (U * U†)).trace := by rw [mul_assoc]
      _ = (ρ.toOp * 1).trace := by rw [h_UU']
      _ = ρ.toOp.trace := by rw [mul_one]
  have h_sum_eq : ∑ i, (star (U · i) ⬝ᵥ (ρ.toOp.mulVec (U · i))) =
      (U† * ρ.toOp * U).trace :=
    Finset.sum_congr rfl (fun i _ => dot_col_eq_entry U ρ.toOp i)
  calc ∑ i, (star (U · i) ⬝ᵥ (ρ.toOp.mulVec (U · i))).re
      = (∑ i, (star (U · i) ⬝ᵥ (ρ.toOp.mulVec (U · i)))).re :=
        (Complex.re_sum _ _).symm
    _ = (U† * ρ.toOp * U).trace.re := by rw [h_sum_eq]
    _ = ρ.toOp.trace.re := by rw [h_cyc]

/-- Trace norm (Schatten 1-norm) of an arbitrary matrix: sum of singular values. -/
noncomputable def traceNorm {n : ℕ} [NeZero n]
    (A : Op n) : ℝ :=
  let hAA : (A.conjTranspose * A).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  ∑ i, Real.sqrt (hAA.eigenvalues i)

/-- Trace norm of a Hermitian matrix: sum of absolute values of eigenvalues. -/
noncomputable def traceNormHermitian {n : ℕ} [NeZero n] (A : Op n)
    (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- Helper: eigenvalues of `A†A` equal squared eigenvalues of Hermitian `A`. -/
private theorem eigenvalues_conjTranspose_mul_eq_sq {n : ℕ} [NeZero n]
    (A : Op n) (hA : A.IsHermitian)
    (hAA : (A.conjTranspose * A).IsHermitian) :
    Multiset.map hAA.eigenvalues Finset.univ.val =
      Multiset.map (fun i => (hA.eigenvalues i) ^ 2) Finset.univ.val := by
  have h_mat_eq : A.conjTranspose * A = cfc (fun x : ℝ => x ^ 2) A := by
    rw [hA.eq, ← sq]; exact (cfc_pow_id A 2 hA).symm
  have hAA_sq : (cfc (fun x : ℝ => x ^ 2) A).IsHermitian := h_mat_eq ▸ hAA
  have h_eig_eq : hAA.eigenvalues = hAA_sq.eigenvalues :=
    (hAA.eigenvalues_eq_eigenvalues_iff hAA_sq).mpr (congr_arg Matrix.charpoly h_mat_eq)
  have h_cp1 := hA.charpoly_cfc_eq (fun x => x ^ 2)
  have h1 := hAA_sq.roots_charpoly_eq_eigenvalues
  rw [h_cp1] at h1
  have h2 : (∏ i : Fin n,
      (Polynomial.X - Polynomial.C (↑(hA.eigenvalues i ^ 2) : ℂ))).roots =
      Multiset.map (fun i => (↑(hA.eigenvalues i ^ 2) : ℂ)) Finset.univ.val := by
    rw [Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · apply Mathlib.Meta.Positivity.prod_ne_zero
      intro i _; exact Polynomial.X_sub_C_ne_zero _
  rw [h_eig_eq]
  apply Multiset.map_injective Complex.ofReal_injective
  simp only [Multiset.map_map]
  exact h1.symm.trans h2

/-- For Hermitian matrices, `traceNorm` equals `traceNormHermitian`. -/
theorem traceNorm_hermitian_eq {n : ℕ} [NeZero n]
    (A : Op n) (hA : A.IsHermitian) :
    traceNorm A = traceNormHermitian A hA := by
  simp only [traceNorm, traceNormHermitian]
  set hAA : (A.conjTranspose * A).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have h_ms := eigenvalues_conjTranspose_mul_eq_sq A hA hAA
  have h_sqrt_ms := congr_arg (Multiset.map Real.sqrt) h_ms
  rw [Multiset.map_map, Multiset.map_map] at h_sqrt_ms
  have h_sum := congr_arg Multiset.sum h_sqrt_ms
  rw [Finset.sum_map_val, Finset.sum_map_val] at h_sum
  simp only [Function.comp_apply] at h_sum
  rw [h_sum]
  congr 1; ext i
  exact Real.sqrt_sq_eq_abs (hA.eigenvalues i)

/-- Trace norm is invariant under reindexing by an equivalence.
    Reindexing preserves singular values (and hence the trace norm). -/
lemma traceNorm_submatrix_equiv {n m : ℕ} [NeZero n] [NeZero m]
    (A : Op n) (e : Fin m ≃ Fin n) :
    traceNorm (A.submatrix e e) = traceNorm A := by
  have h_eq : m = n := Fin.equiv_iff_eq.mp ⟨e⟩
  subst h_eq
  unfold traceNorm
  have hBB : ((A.submatrix (⇑e) (⇑e)).conjTranspose * A.submatrix (⇑e) (⇑e)).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hAA : (A.conjTranspose * A).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have h_prod : (A.submatrix (⇑e) (⇑e)).conjTranspose * A.submatrix (⇑e) (⇑e) =
      (A.conjTranspose * A).submatrix (⇑e) (⇑e) := by
    rw [conjTranspose_submatrix, submatrix_mul_equiv]
  have h_charpoly : hBB.eigenvalues = hAA.eigenvalues := by
    rw [IsHermitian.eigenvalues_eq_eigenvalues_iff, h_prod]
    have : (⇑e : Fin m → Fin m) = ⇑e.symm.symm := by
      simp [Equiv.symm_symm]
    rw [this, ← Matrix.reindex_apply]
    exact charpoly_reindex e.symm _
  simp_rw [h_charpoly]

/-- Trace distance between matrices: `T(A,B) = ½‖A−B‖₁`. -/
noncomputable def traceDistance {n : ℕ} [NeZero n]
    (A B : Op n) : ℝ :=
  (1 / 2) * traceNorm (A - B)

/-- Trace distance between density operators, as a special case of the general definition. -/
noncomputable def DensityOp.traceDistance {n : ℕ} [NeZero n] (ρ σ : DensityOp n) : ℝ :=
  Quantum.Metrics.traceDistance ρ.toOp σ.toOp

/-- For density operators, `traceDistance` equals
    `(1/2) * traceNormHermitian (ρ.toOp - σ.toOp)`. -/
theorem traceDistance_densityOp_eq_traceNormHermitian {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) :
    traceDistance ρ.toOp σ.toOp =
      (1 / 2) * traceNormHermitian (ρ.toOp - σ.toOp) (densityOp_sub_isHermitian ρ σ) := by
  unfold traceDistance
  rw [traceNorm_hermitian_eq (ρ.toOp - σ.toOp) (densityOp_sub_isHermitian ρ σ)]

/-- Trace distance is nonnegative. -/
theorem traceDistance_nonneg {n : ℕ} [NeZero n]
    (A B : Op n) : 0 ≤ traceDistance A B := by
  unfold traceDistance
  apply mul_nonneg
  · norm_num
  · unfold traceNorm
    apply Finset.sum_nonneg
    intro i _
    exact Real.sqrt_nonneg _

/-- Trace distance is nonnegative for density operators. -/
theorem traceDistance_nonneg_densityOp {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    0 ≤ traceDistance ρ.toOp σ.toOp :=
  traceDistance_nonneg ρ.toOp σ.toOp

/-- The specialized `DensityOp.traceDistance` equals
    `(1/2) * traceNormHermitian (ρ.toOp - σ.toOp)`.
    Companion to `traceDistance_densityOp_eq_traceNormHermitian` using the
    `DensityOp.traceDistance` API. -/
theorem DensityOp.traceDistance_eq_traceNormHermitian {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) :
    DensityOp.traceDistance ρ σ =
      (1 / 2) * traceNormHermitian (ρ.toOp - σ.toOp) (densityOp_sub_isHermitian ρ σ) :=
  traceDistance_densityOp_eq_traceNormHermitian ρ σ

/-- `DensityOp.traceDistance` is nonnegative.
    Companion to `traceDistance_nonneg_densityOp` using the `DensityOp.traceDistance` API. -/
theorem DensityOp.traceDistance_nonneg {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    0 ≤ DensityOp.traceDistance ρ σ :=
  traceDistance_nonneg_densityOp ρ σ

/-!
## Spectral Helpers for Density-Operator Bounds
-/

/-- Diagonal matrix applied to vector: `(diag d).mulVec v i = d i * v i`. -/
private lemma diagonal_mulVec_apply' {n : ℕ}
    (d : Fin n → ℂ) (v : Fin n → ℂ) (i : Fin n) :
    (diagonal d).mulVec v i = d i * v i := by
  simp only [mulVec, diagonal_apply, dotProduct]
  have h : ∀ j, (if i = j then d i else 0) * v j = if i = j then d i * v j else 0 := by
    intro j; split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_ite_eq Finset.univ i (fun j => d i * v j)]
  simp [Finset.mem_univ]

/-- Quadratic form with diagonal matrix of real eigenvalues. -/
private lemma diagonal_quadratic_form_re {n : ℕ} (ev : Fin n → ℝ) (φ : Fin n → ℂ) :
    (star φ ⬝ᵥ (diagonal (fun i => (ev i : ℂ))).mulVec φ).re =
    ∑ i, ev i * Complex.normSq (φ i) := by
  simp only [dotProduct, diagonal_mulVec_apply']
  rw [Complex.re_sum]
  congr 1; ext i
  have h_conj : star φ i * φ i = (Complex.normSq (φ i) : ℂ) := by
    have := Complex.mul_conj (φ i)
    rw [mul_comm] at this
    exact this
  calc (star φ i * (↑(ev i) * φ i)).re
      = (star φ i * ↑(ev i) * φ i).re := by ring_nf
    _ = (↑(ev i) * star φ i * φ i).re := by rw [mul_comm (star φ i) (ev i : ℂ)]
    _ = (↑(ev i) * (star φ i * φ i)).re := by ring_nf
    _ = ((ev i : ℂ) * (Complex.normSq (φ i) : ℂ)).re := by rw [h_conj]
    _ = ((ev i * Complex.normSq (φ i) : ℝ) : ℂ).re := by rw [← Complex.ofReal_mul]
    _ = ev i * Complex.normSq (φ i) := Complex.ofReal_re _

/-- Relationship between `vecMul` and `star`. -/
lemma star_vecMul_eq {n : ℕ} [NeZero n] (U : Op n) (v : Fin n → ℂ) :
    star v ᵥ* U = star (U†.mulVec v) := by
  ext i
  simp only [vecMul, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star,
    conjTranspose_apply]
  congr 1; ext j; ring

/-- Spectral quadratic form:
    `star v ⬝ᵥ (U * D * U†).mulVec v = Σᵢ λᵢ |φᵢ|²`. -/
lemma spectral_quadratic_form_re {n : ℕ} [NeZero n]
    (U : Op n) (ev : Fin n → ℝ) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (U * diagonal (fun i => (ev i : ℂ)) * U†).mulVec v).re =
    ∑ i, ev i * Complex.normSq (U†.mulVec v i) := by
  set D := diagonal (fun i => (ev i : ℂ)) with hD
  set φ := U†.mulVec v with hφ
  have h1 : (U * D * U†).mulVec v = U.mulVec (D.mulVec φ) := by
    rw [hφ]
    simp only [mulVec_mulVec, mul_assoc]
  rw [h1, dotProduct_mulVec, star_vecMul_eq, hφ]
  exact diagonal_quadratic_form_re ev φ

/-- For density operators, eigenvalues are non-negative and at most `1`. -/
lemma density_eigenvalues_bound {n : ℕ} [NeZero n] (ρ : DensityOp n) :
    ∀ i, 0 ≤ (ρ.toPosSemidefOp.toHermitianOp.isHermitian).eigenvalues i ∧
         (ρ.toPosSemidefOp.toHermitianOp.isHermitian).eigenvalues i ≤ 1 := by
  intro i
  constructor
  · exact (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).eigenvalues_nonneg i
  · let hH := ρ.toPosSemidefOp.toHermitianOp.isHermitian
    have h_all_nonneg : ∀ j, 0 ≤ hH.eigenvalues j :=
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).eigenvalues_nonneg
    have h_sum_eq_1 : (∑ j, hH.eigenvalues j : ℝ) = 1 := by
      have : (∑ j, (hH.eigenvalues j : ℂ)) = 1 :=
        hH.trace_eq_sum_eigenvalues.symm.trans ρ.trace_one
      simp only [← Complex.ofReal_sum, Complex.ofReal_eq_one] at this
      exact this
    calc hH.eigenvalues i
        ≤ hH.eigenvalues i + ∑ j ∈ Finset.univ.erase i, hH.eigenvalues j := by
          apply le_add_of_nonneg_right
          exact Finset.sum_nonneg (fun j _ => h_all_nonneg j)
      _ = ∑ j, hH.eigenvalues j := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      _ = 1 := h_sum_eq_1

/-- For a PSD operator with all eigenvalues ≤ `1`, `⟨v|A²|v⟩ ≤ ⟨v|A|v⟩`. -/
lemma posSemidef_sq_quadform_le {n : ℕ} [NeZero n] (A : PosSemidefOp n)
    (h_ev_le_one : ∀ j, A.toHermitianOp.isHermitian.eigenvalues j ≤ 1)
    (v : Fin n → ℂ) :
    (star v ⬝ᵥ ((A.toOp * A.toOp).mulVec v)).re ≤
    (star v ⬝ᵥ (A.toOp.mulVec v)).re := by
  let hH := A.toHermitianOp.isHermitian
  let p := hH.eigenvalues
  let U := hH.eigenvectorUnitary.val
  have h_UU : U† * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have h_UU' : U * U† = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have h_spec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  have h_p_nonneg : ∀ j, 0 ≤ p j :=
    (posSemidefOp_implies_mathlib A).eigenvalues_nonneg
  have h_p_le_one : ∀ j, p j ≤ 1 := h_ev_le_one
  have h_sq_le : ∀ j, p j ^ 2 ≤ p j := by
    intro j; nlinarith [h_p_nonneg j, h_p_le_one j]
  set D := diagonal (RCLike.ofReal ∘ p : Fin n → ℂ) with hD_def
  have h_A_eq : A.toOp = U * D * U† := by rw [hD_def]; exact h_spec
  set D_sq := diagonal (fun j => (↑(p j ^ 2) : ℂ)) with hD_sq_def
  have h_D_sq : D * D = D_sq := by
    rw [hD_def, hD_sq_def, diagonal_mul_diagonal]; congr 1; ext j
    simp only [Function.comp_apply, ← sq]; norm_cast
  have h_A_sq_eq : A.toOp * A.toOp = U * D_sq * U† := by
    calc A.toOp * A.toOp = (U * D * U†) * (U * D * U†) := by rw [h_A_eq]
      _ = U * D * (U† * U) * D * U† := by simp only [mul_assoc]
      _ = U * D * 1 * D * U† := by rw [h_UU]
      _ = U * (D * D) * U† := by simp only [mul_one, mul_assoc]
      _ = U * D_sq * U† := by rw [h_D_sq]
  let φ := U†.mulVec v
  have h_φ_nonneg : ∀ j, 0 ≤ Complex.normSq (φ j) := fun j => Complex.normSq_nonneg _
  have h_sq_form : (star v ⬝ᵥ ((A.toOp * A.toOp).mulVec v)).re =
      ∑ j, p j ^ 2 * Complex.normSq (φ j) := by
    rw [h_A_sq_eq]
    convert spectral_quadratic_form_re U (fun j => p j ^ 2) v using 2
  have h_form : (star v ⬝ᵥ (A.toOp.mulVec v)).re =
      ∑ j, p j * Complex.normSq (φ j) := by
    rw [h_A_eq]
    exact spectral_quadratic_form_re U p v
  rw [h_sq_form, h_form]
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul_of_nonneg_right (h_sq_le j) (h_φ_nonneg j)

/-- For density operators, `⟨v|ρ²|v⟩ ≤ ⟨v|ρ|v⟩`. -/
lemma density_sq_quadform_le {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (v : Fin n → ℂ) :
    (star v ⬝ᵥ ((ρ.toOp * ρ.toOp).mulVec v)).re ≤
    (star v ⬝ᵥ (ρ.toOp.mulVec v)).re :=
  posSemidef_sq_quadform_le ρ.toPosSemidefOp
    (fun j => (density_eigenvalues_bound ρ j).2) v

/-- Hermitian trace norm is zero iff the matrix is zero. -/
lemma traceNormHermitian_eq_zero_iff {n : ℕ} [NeZero n]
    (A : Op n) (hA : A.IsHermitian) :
    traceNormHermitian A hA = 0 ↔ A = 0 := by
  unfold traceNormHermitian
  constructor
  · intro h_sum_zero
    have h_all_zero : ∀ i, hA.eigenvalues i = 0 := by
      intro i
      have h_sum_nonneg : ∀ j ∈ Finset.univ, 0 ≤ |hA.eigenvalues j| := fun j _ => abs_nonneg _
      have h_i_zero := (Finset.sum_eq_zero_iff_of_nonneg h_sum_nonneg).mp h_sum_zero
      exact abs_eq_zero.mp (h_i_zero i (Finset.mem_univ i))
    exact (Matrix.IsHermitian.eigenvalues_eq_zero_iff hA).mp (funext h_all_zero)
  · intro hA_zero
    subst hA_zero
    have h_zero_eig : hA.eigenvalues = 0 :=
      (Matrix.IsHermitian.eigenvalues_eq_zero_iff hA).mpr rfl
    simp only [h_zero_eig, Pi.zero_apply, abs_zero, Finset.sum_const_zero]

/-- Hermitian trace norm is proof-irrelevant. -/
lemma traceNormHermitian_proof_irrel {n : ℕ} [NeZero n] (A : Op n)
    (h1 h2 : A.IsHermitian) : traceNormHermitian A h1 = traceNormHermitian A h2 := by
  unfold traceNormHermitian
  have : h1 = h2 := Subsingleton.elim _ _
  rw [this]

/-- Triangle inequality for Hermitian trace norm. -/
lemma traceNormHermitian_triangle {n : ℕ} [NeZero n] (A B : Op n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNormHermitian (A + B) (hA.add hB) ≤ traceNormHermitian A hA + traceNormHermitian B hB := by
  set hAB := hA.add hB
  unfold traceNormHermitian
  have h_split : ∑ i, |hAB.eigenvalues i| ≤
      ∑ i, |hAB.eigenvalues i - hA.eigenvalues i| + ∑ i, |hA.eigenvalues i| := by
    calc ∑ i, |hAB.eigenvalues i|
        ≤ ∑ i, (|hAB.eigenvalues i - hA.eigenvalues i| + |hA.eigenvalues i|) := by
          apply Finset.sum_le_sum; intro i _
          linarith [abs_sub_abs_le_abs_sub (hAB.eigenvalues i) (hA.eigenvalues i)]
      _ = _ := Finset.sum_add_distrib
  have h_weyl : ∑ i, |hAB.eigenvalues i - hA.eigenvalues i| ≤
      ∑ i, |hB.eigenvalues i| := by
    have h_eq : (A + B) - A = B := by abel
    have hB' : ((A + B) - A).IsHermitian := by rw [h_eq]; exact hB
    have h_w := Math.SpectralTheory.weyl_eigenvalue_sum_bound (A + B) A hAB hA hB'
    suffices h : ∀ i, hB'.eigenvalues i = hB.eigenvalues i by
      calc ∑ i, |hAB.eigenvalues i - hA.eigenvalues i|
          ≤ ∑ i, |hB'.eigenvalues i| := h_w
        _ = ∑ i, |hB.eigenvalues i| := by congr 1; ext i; rw [h]
    intro i; unfold Matrix.IsHermitian.eigenvalues
    congr 1
  linarith

/-- The eigenvalues of `ρ - |ψ⟩⟨ψ|` sum to zero. -/
lemma densityOp_sub_pure_eigenvalues_sum_zero {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    let σ := DensityOp.fromPure ψ hψ
    let hA := densityOp_sub_isHermitian ρ σ
    ∑ i, hA.eigenvalues i = 0 := by
  intro σ hA
  have h_tr : (ρ.toOp - σ.toOp).trace = 0 := by
    simp only [Matrix.trace_sub, ρ.trace_one, σ.trace_one, sub_self]
  have h := hA.trace_eq_sum_eigenvalues
  rw [h_tr] at h
  have h' : (∑ j, (hA.eigenvalues j : ℂ)) = 0 := h.symm
  simp only [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h'
  exact h'

/-- Eigenvector equation: `A.mulVec u_i = λ_i • u_i` for eigenvectors of a Hermitian matrix. -/
lemma eigenvector_mulVec_eq {n : ℕ} [NeZero n]
    {A : Op n} (hA : A.IsHermitian) (i : Fin n) :
    A.mulVec (hA.eigenvectorUnitary.val · i) =
      (hA.eigenvalues i : ℂ) • (hA.eigenvectorUnitary.val · i) := by
  let U := hA.eigenvectorUnitary.val
  let D := diagonal (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℂ)
  have h_UU : U† * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  have h_starU : star U = U† := rfl
  have h_AU : A * U = U * D := by
    calc A * U = (U * D * star U) * U := by rw [h_spec]
      _ = U * D * (star U * U) := by simp only [mul_assoc]
      _ = U * D * (U† * U) := by rw [h_starU]
      _ = U * D * 1 := by rw [h_UU]
      _ = U * D := mul_one _
  ext k
  have h_col : A.mulVec (U · i) k = (A * U) k i := by
    simp only [mulVec, dotProduct, mul_apply]
  rw [h_col, h_AU]
  simp only [mul_apply, D, diagonal_apply, Function.comp_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- The quadratic form of `A` on eigenvector `i` equals the eigenvalue. -/
lemma eigenvector_quadraticForm_eq_eigenvalue {n : ℕ} [NeZero n]
    {A : Op n} (hA : A.IsHermitian) (i : Fin n) :
    (star (hA.eigenvectorUnitary.val · i) ⬝ᵥ
      (A.mulVec (hA.eigenvectorUnitary.val · i))).re = hA.eigenvalues i := by
  let U := hA.eigenvectorUnitary.val
  let D := diagonal (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℂ)
  have h_UU : U† * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  rw [dot_col_eq_entry U A i]
  have h_starU : star U = U† := rfl
  have h_conj : U† * A * U = D := by
    calc U† * A * U
        = U† * (U * D * star U) * U := by rw [h_spec]
      _ = U† * (U * D * U†) * U := by rw [h_starU]
      _ = U† * U * D * (U† * U) := by simp only [mul_assoc]
      _ = 1 * D * 1 := by rw [h_UU]
      _ = D := by simp
  simp only [h_conj, D]
  rw [diagonal_apply_eq, Function.comp_apply]
  exact Complex.ofReal_re _

/-- The sum of quadratic forms over an orthonormal eigenbasis equals `Tr(M)`. -/
lemma sum_quadForm_eq_trace_re {n : ℕ} [NeZero n]
    (M : Op n)
    {A : Op n} (hA : A.IsHermitian) :
    ∑ i, (star (hA.eigenvectorUnitary.val · i) ⬝ᵥ
          (M.mulVec (hA.eigenvectorUnitary.val · i))).re = M.trace.re := by
  let U := hA.eigenvectorUnitary.val
  have h_UU' : U * U† = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have h_cyc : (U† * M * U).trace = M.trace := by
    calc (U† * M * U).trace
        = (U† * (M * U)).trace := by rw [mul_assoc]
      _ = (M * U * U†).trace := by rw [trace_mul_comm U† (M * U)]
      _ = (M * (U * U†)).trace := by rw [mul_assoc]
      _ = (M * 1).trace := by rw [h_UU']
      _ = M.trace := by rw [mul_one]
  have h_sum_eq : ∑ i, (star (U · i) ⬝ᵥ (M.mulVec (U · i))) = (U† * M * U).trace :=
    Finset.sum_congr rfl (fun i _ => dot_col_eq_entry U M i)
  calc ∑ i, (star (U · i) ⬝ᵥ (M.mulVec (U · i))).re
      = (∑ i, (star (U · i) ⬝ᵥ (M.mulVec (U · i)))).re := (Complex.re_sum _ _).symm
    _ = (U† * M * U).trace.re := by rw [h_sum_eq]
    _ = M.trace.re := by rw [h_cyc]

/-- For Hermitian matrices with trace `0`, the sum of absolute eigenvalues equals twice
    the sum of positive eigenvalues (which equals twice the sum of absolute values of
    negative eigenvalues, since positive and negative parts balance under trace zero). -/
lemma trace_zero_eigenvalue_bound {n : ℕ} [NeZero n] (A : Op n)
    (hA : A.IsHermitian) (hTr : A.trace = 0) :
    (∑ i, |hA.eigenvalues i|) = 2 * ∑ i, max 0 (hA.eigenvalues i) := by
  have h_trace_sum : (∑ i, (hA.eigenvalues i : ℂ)) = 0 := by
    have h := hA.trace_eq_sum_eigenvalues
    simp only [hTr] at h
    exact h.symm
  have h_abs_split : ∀ x : ℝ, |x| = max 0 x + max 0 (-x) := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), add_zero]
    · push Not at hx
      rw [abs_of_neg hx, max_eq_left (le_of_lt hx), zero_add, max_eq_right (neg_pos.mpr hx).le]
  have h_sum_split : ∑ i, |hA.eigenvalues i| =
      ∑ i, max 0 (hA.eigenvalues i) + ∑ i, max 0 (-hA.eigenvalues i) := by
    rw [← Finset.sum_add_distrib]
    congr 1
    funext i
    exact h_abs_split (hA.eigenvalues i)
  have h_sum_real : (∑ i, hA.eigenvalues i : ℝ) = 0 := by
    have : (∑ i, (hA.eigenvalues i : ℂ)) = 0 := h_trace_sum
    simp only [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at this
    exact this
  have h_pos_neg_balance : ∑ i, max 0 (hA.eigenvalues i) = ∑ i, max 0 (-hA.eigenvalues i) := by
    have h1 : (∑ i, hA.eigenvalues i : ℝ) =
        ∑ i, (max 0 (hA.eigenvalues i) - max 0 (-hA.eigenvalues i)) := by
      congr 1
      funext i
      by_cases hx : 0 ≤ hA.eigenvalues i
      · rw [max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), sub_zero]
      · push Not at hx
        rw [max_eq_left (le_of_lt hx), max_eq_right (neg_pos.mpr hx).le, zero_sub, neg_neg]
    rw [h_sum_real, Finset.sum_sub_distrib] at h1
    linarith
  rw [h_sum_split, h_pos_neg_balance, ← two_mul]

/-- For a Hermitian matrix, `Tr(A²) = ∑ λᵢ²` where `λᵢ` are the eigenvalues. -/
lemma hermitian_trace_sq_eq_sum_eigenvalues_sq {n : ℕ} [NeZero n]
    {A : Op n} (hA : A.IsHermitian) :
    (A * A).trace.re = ∑ i, (hA.eigenvalues i) ^ 2 := by
  let ev := hA.eigenvalues
  let U := hA.eigenvectorUnitary.val
  let D := Matrix.diagonal (fun i => (ev i : ℂ))
  have h_A_eq : A = U * D * U† := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]; rfl
  have h_U_unitary : U† * U = 1 := by
    have := hA.eigenvectorUnitary.2
    simp only [mem_unitaryGroup_iff'] at this; exact this
  have h_A_sq : A * A = U * D * D * U† := by
    calc A * A = (U * D * U†) * (U * D * U†) := by rw [h_A_eq]
      _ = U * D * (U† * U) * D * U† := by noncomm_ring
      _ = U * D * 1 * D * U† := by rw [h_U_unitary]
      _ = U * D * D * U† := by noncomm_ring
  have h_D_sq : D * D = Matrix.diagonal (fun i => ((ev i : ℂ) ^ 2)) := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; ext i; ring
  have h_D_sq_trace : (D * D).trace = ∑ i, ((ev i : ℂ) ^ 2) := by
    rw [h_D_sq, Matrix.trace_diagonal]
  have h_trace_eq : (U * D * D * U†).trace = (D * D).trace := by
    calc (U * D * D * U†).trace
        = (U† * (U * D * D)).trace := Matrix.trace_mul_comm _ _
      _ = (U† * U * D * D).trace := by noncomm_ring
      _ = (1 * D * D).trace := by rw [h_U_unitary]
      _ = (D * D).trace := by rw [Matrix.one_mul]
  calc (A * A).trace.re = (U * D * D * U†).trace.re := by rw [h_A_sq]
    _ = (D * D).trace.re := by rw [h_trace_eq]
    _ = (∑ i, ((ev i : ℂ) ^ 2)).re := by rw [h_D_sq_trace]
    _ = ∑ i, (ev i) ^ 2 := by
        simp only [Complex.re_sum]; congr 1; ext i
        simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]

/-- Algebraic decomposition:
    `A - BAB = (A - BA) + (A - AB) - (I-B)A(I-B)`. -/
lemma a_minus_bab_decomp {m : ℕ} (A B : Op m) :
    A - B * A * B = (A - B * A) + (A - A * B) - (1 - B) * A * (1 - B) := by
  noncomm_ring

/-- Each diagonal entry of a Hermitian projector has real part in `[0, 1]`. -/
lemma hermitian_projector_diag_re_bounds {n : ℕ}
    (P : Op n) (hP_proj : P * P = P) (hP_herm : P† = P)
    (i : Fin n) :
    0 ≤ (P i i).re ∧ (P i i).re ≤ 1 := by
  have h_diag_sum : (P i i).re = ∑ j, Complex.normSq (P j i) := by
    conv_lhs => rw [show P = P† * P from by rw [hP_herm, hP_proj]]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    congr 1
    ext j
    simp [mul_comm, Complex.normSq]
  have h_nonneg : 0 ≤ (P i i).re := by
    rw [h_diag_sum]
    exact Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
  have h_single : Complex.normSq (P i i) ≤ ∑ j, Complex.normSq (P j i) :=
    Finset.single_le_sum (f := fun j => Complex.normSq (P j i))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have h_im : (P i i).im = 0 := by
    have h_self : star (P i i) = P i i := by
      simpa [Matrix.conjTranspose_apply] using congr_fun₂ hP_herm i i
    rw [Complex.star_def] at h_self
    have := congr_arg Complex.im h_self
    simp only [Complex.conj_im] at this
    linarith
  have h_normSq : Complex.normSq (P i i) = (P i i).re ^ 2 := by
    simp [Complex.normSq_apply, h_im]
    ring
  constructor
  · exact h_nonneg
  · nlinarith [h_single, h_normSq, h_nonneg, h_diag_sum]

/-- For a projector `P` and Hermitian matrix `A`,
    `|Tr(PA).re| ≤ traceNormHermitian A hA_herm`. -/
theorem projector_trace_re_le_traceNormHermitian {n : ℕ} [NeZero n]
    (P : Op n) (A : Op n)
    (hP_proj : P * P = P) (hP_herm : P† = P) (hA_herm : A.IsHermitian) :
    |(P * A).trace.re| ≤ traceNormHermitian A hA_herm := by
  unfold traceNormHermitian
  let U := hA_herm.eigenvectorUnitary.val
  let ev := hA_herm.eigenvalues
  let D := Matrix.diagonal (fun i => (ev i : ℂ))
  have hU_r : U * U† = 1 := Unitary.coe_mul_star_self hA_herm.eigenvectorUnitary
  have h_spec : A = U * D * U† := by
    have := hA_herm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h_trace_eq : (P * A).trace = ((U† * P * U) * D).trace := by
    calc (P * A).trace
        = (P * (U * D * U†)).trace := by rw [h_spec]
      _ = (P * U * D * U†).trace := by simp only [Matrix.mul_assoc]
      _ = (U† * (P * U * D)).trace := by rw [Matrix.trace_mul_comm]
      _ = ((U† * P * U) * D).trace := by simp only [Matrix.mul_assoc]
  let Q := U† * P * U
  have hQ_proj : Q * Q = Q := by
    calc Q * Q = U† * P * (U * (U† * P * U)) := by simp only [Q, Matrix.mul_assoc]
      _ = U† * P * ((U * U†) * P * U) := by simp only [Matrix.mul_assoc]
      _ = U† * P * (1 * P * U) := by rw [hU_r]
      _ = U† * P * (P * U) := by rw [Matrix.one_mul]
      _ = U† * (P * P) * U := by simp only [Matrix.mul_assoc]
      _ = U† * P * U := by rw [hP_proj]
  have hQ_herm : Q† = Q := by
    simp only [Q, Matrix.conjTranspose_mul, hP_herm, Matrix.mul_assoc,
      Matrix.conjTranspose_conjTranspose]
  have h_trace_sum : (Q * D).trace = ∑ i, Q i i * (ev i : ℂ) := by
    simp [D, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal]
  rw [h_trace_eq, show (U† * P * U) = Q from rfl, h_trace_sum]
  rw [Complex.re_sum]
  have h_re_terms : ∀ i, (Q i i * (ev i : ℂ)).re = (Q i i).re * ev i := by
    intro i; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp_rw [h_re_terms]
  calc |∑ i, (Q i i).re * ev i|
      ≤ ∑ i, |(Q i i).re * ev i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |(Q i i).re| * |ev i| := by
        congr 1; ext i; exact abs_mul _ _
    _ ≤ ∑ i, 1 * |ev i| := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_right
        · rw [abs_of_nonneg (hermitian_projector_diag_re_bounds Q hQ_proj hQ_herm i).1]
          exact (hermitian_projector_diag_re_bounds Q hQ_proj hQ_herm i).2
        · exact abs_nonneg _
    _ = ∑ i, |ev i| := by simp

end Quantum.Metrics
