import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.Operators.BraKet.Projector
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Pure States and Density Operators — pure-state construction and extraction

This file provides the basic bridge between normalized kets and pure density
operators: constructing `|ψ⟩⟨ψ|` from a ket, and extracting a ket from a pure
density operator.

## Main definitions

* `DensityOp.fromPure` - Construct the pure density operator `|ψ⟩⟨ψ|` from a normalized ket
* `DensityOp.pureKetOf` - Extract a normalized ket ψ from a pure density operator ρ
  such that ρ = |ψ⟩⟨ψ|.

## Mathematical background

A density operator ρ is pure iff ρ² = ρ (idempotent) and Tr(ρ) = 1.
This means ρ has exactly one eigenvalue equal to 1, and the rest are 0.
The eigenvector corresponding to eigenvalue 1 is the ket |ψ⟩ such that ρ = |ψ⟩⟨ψ|.

## Implementation notes

The extraction uses the spectral decomposition via `IsHermitian.eigenvectorUnitary`.
For a pure state, we identify the eigenvector with eigenvalue 1 and construct the ket.
-/

namespace Quantum.Operators

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

/-!
## Pure State Construction
-/

/-- Construct a density operator from a normalized pure state: `ρ = |ψ⟩⟨ψ|`. -/
def DensityOp.fromPure {n : ℕ} (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) : DensityOp n :=
  ⟨⟨⟨ψ * ψ.dag, by
    change (ψ * ψ.dag)† = ψ * ψ.dag
    exact ketbra_hermitian ψ⟩, by
    intro x
    simpa [quadraticForm] using
      (RCLike.nonneg_iff.mp ((ketbra_posSemidef ψ).dotProduct_mulVec_nonneg x)).1⟩, by
    simpa using trace_ketbra_normalized ψ hψ⟩

/-!
## Pure State Properties
-/

/-- A pure density operator has exactly one eigenvalue equal to 1.
    This follows from ρ² = ρ and Tr(ρ) = 1. -/
lemma pure_has_eigenvalue_one {n : ℕ} [NeZero n] (ρ : DensityOp n) (hpure : ρ.IsPure) :
    ∃ i : Fin n, ρ.toPosSemidefOp.toHermitianOp.isHermitian.eigenvalues i = 1 := by
  -- For a pure state ρ² = ρ, the eigenvalues satisfy λ² = λ, so λ ∈ {0, 1}
  -- Since Tr(ρ) = 1 and eigenvalues are non-negative, exactly one must be 1
  let hH := ρ.toPosSemidefOp.toHermitianOp.isHermitian
  let hPSD := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  -- Sum of eigenvalues = 1
  have h_sum : ∑ i, hH.eigenvalues i = 1 := by
    have h_trace := ρ.trace_one
    have h_sum_eq := hH.trace_eq_sum_eigenvalues
    have h_eq : (1 : ℂ) = ∑ k, (hH.eigenvalues k : ℂ) := by
      calc (1 : ℂ) = ρ.toOp.trace := h_trace.symm
        _ = ∑ k, (hH.eigenvalues k : ℂ) := h_sum_eq
    have h_re_rhs : (∑ k, (hH.eigenvalues k : ℂ)).re = ∑ k, hH.eigenvalues k := by
      simp only [Complex.re_sum, Complex.ofReal_re]
    calc ∑ j, hH.eigenvalues j = (∑ j, (hH.eigenvalues j : ℂ)).re := h_re_rhs.symm
      _ = (1 : ℂ).re := by rw [← h_eq]
      _ = 1 := rfl
  -- Eigenvalues are non-negative
  have h_nonneg : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hPSD.eigenvalues_nonneg i
  -- For pure states, eigenvalues satisfy λ² = λ (from ρ² = ρ)
  -- This means λ ∈ {0, 1} for each eigenvalue
  have h_idempotent : ∀ i, hH.eigenvalues i * hH.eigenvalues i = hH.eigenvalues i := by
    intro i
    -- From ρ² = ρ and spectral decomposition:
    -- U * diag(λ²) * U† = U * diag(λ) * U†
    -- Therefore diag(λ²) = diag(λ), so λᵢ² = λᵢ
    -- Get spectral theorem: ρ = U * D * U†
    have h_spectral := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h_spectral
    let U := hH.eigenvectorUnitary.val
    let D := Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ))
    -- Show that spectral theorem's notation matches our D
    have h_D_def : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) = D := rfl
    have h_star_eq : star U = Uᴴ := rfl
    -- Rewrite h_spectral to use our notation
    rw [h_D_def, h_star_eq] at h_spectral
    have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    have h_UU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    -- Compute ρ² = U * D² * U†
    have h_rho_sq' : ρ.toOp * ρ.toOp = U * (D * D) * Uᴴ := by
      calc ρ.toOp * ρ.toOp = (U * D * Uᴴ) * (U * D * Uᴴ) := by rw [h_spectral]
        _ = U * D * (Uᴴ * U) * D * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = U * D * 1 * D * Uᴴ := by rw [h_UU]
        _ = U * D * D * Uᴴ := by simp only [Matrix.mul_one]
        _ = U * (D * D) * Uᴴ := by simp only [Matrix.mul_assoc]
    -- From ρ² = ρ: U * D² * U† = U * D * U†
    have h_eq : U * (D * D) * Uᴴ = U * D * Uᴴ := by
      rw [← h_rho_sq']
      unfold DensityOp.IsPure at hpure
      rw [hpure, h_spectral]
    -- D² = D
    have h_D_eq : D * D = D := by
      have h1 : Uᴴ * (U * (D * D) * Uᴴ) * U = Uᴴ * (U * D * Uᴴ) * U := by rw [h_eq]
      have h_lhs : Uᴴ * (U * (D * D) * Uᴴ) * U = D * D := by
        calc Uᴴ * (U * (D * D) * Uᴴ) * U
          = (Uᴴ * U) * (D * D) * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
          _ = 1 * (D * D) * 1 := by rw [h_UU]
          _ = D * D := by simp only [Matrix.one_mul, Matrix.mul_one]
      have h_rhs : Uᴴ * (U * D * Uᴴ) * U = D := by
        calc Uᴴ * (U * D * Uᴴ) * U
          = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
          _ = 1 * D * 1 := by rw [h_UU]
          _ = D := by simp only [Matrix.one_mul, Matrix.mul_one]
      rw [h_lhs, h_rhs] at h1; exact h1
    -- D * D = diagonal(λᵢ * λᵢ)
    have h_D_sq : D * D = Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ) * (hH.eigenvalues j : ℂ))
        :=
      Matrix.diagonal_mul_diagonal _ _
    -- Extract diagonal entry: λᵢ * λᵢ = λᵢ (as complex)
    have h_diag_eq : (hH.eigenvalues i : ℂ) * (hH.eigenvalues i : ℂ) = (hH.eigenvalues i : ℂ) := by
      have h_entry : (Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ) * (hH.eigenvalues j : ℂ))) i
          i =
                     (Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ))) i i := by rw [← h_D_sq,
                         h_D_eq]
      simp only [Matrix.diagonal_apply_eq] at h_entry; exact h_entry
    -- Convert complex to real
    have h_cplx : ((hH.eigenvalues i * hH.eigenvalues i : ℝ) : ℂ) = ((hH.eigenvalues i : ℝ) : ℂ) :=
        by
      simp only [Complex.ofReal_mul]; exact h_diag_eq
    exact Complex.ofReal_inj.mp h_cplx
  -- From λ² = λ and λ ≥ 0, we get λ ∈ {0, 1}
  have h_zero_or_one : ∀ i, hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := by
    intro i
    have h := h_idempotent i
    have h_nn := h_nonneg i
    -- λ² = λ means λ(λ - 1) = 0, so λ = 0 or λ = 1
    by_cases h0 : hH.eigenvalues i = 0
    · left; exact h0
    · right
      -- λ ≠ 0 and λ² = λ implies λ = 1
      have h_eq : hH.eigenvalues i * (hH.eigenvalues i - 1) = 0 := by linarith
      have h_sub : hH.eigenvalues i - 1 = 0 := by
        by_contra h_ne
        have h_prod := mul_ne_zero h0 h_ne
        exact h_prod h_eq
      linarith
  -- Since ∑ᵢ λᵢ = 1 and each λᵢ ∈ {0, 1}, at least one λᵢ = 1
  by_contra h_none
  push_neg at h_none
  have h_all_zero : ∀ i, hH.eigenvalues i = 0 := by
    intro i
    cases h_zero_or_one i with
    | inl h0 => exact h0
    | inr h1 => exact absurd h1 (h_none i)
  have h_sum_zero : ∑ i, hH.eigenvalues i = 0 := by
    simp only [h_all_zero, Finset.sum_const_zero]
  linarith

/-- The index of the eigenvalue equal to 1 for a pure state. -/
noncomputable def pureEigenIndex {n : ℕ} [NeZero n] (ρ : DensityOp n) (hpure : ρ.IsPure) : Fin n :=
  Classical.choose (pure_has_eigenvalue_one ρ hpure)

/-- The eigenvalue at pureEigenIndex is 1. -/
lemma pureEigenIndex_spec {n : ℕ} [NeZero n] (ρ : DensityOp n) (hpure : ρ.IsPure) :
    ρ.toPosSemidefOp.toHermitianOp.isHermitian.eigenvalues (pureEigenIndex ρ hpure) = 1 :=
  Classical.choose_spec (pure_has_eigenvalue_one ρ hpure)

/-!
## Pure State Extraction
-/

/-- Extract the underlying ket from a pure density operator.
    For a pure state ρ = |ψ⟩⟨ψ|, this returns ψ (the eigenvector for eigenvalue 1).

    The ket is extracted from the eigenvector unitary at the index where
    the eigenvalue equals 1. -/
def DensityOp.pureKetOf {n : ℕ} [NeZero n] (ρ : DensityOp n) (hpure : ρ.IsPure) : Ket n :=
  let hH := ρ.toPosSemidefOp.toHermitianOp.isHermitian
  let U := hH.eigenvectorUnitary.val
  let i := pureEigenIndex ρ hpure
  -- The ket is the i-th column of U (the eigenvector for eigenvalue 1)
  ⟨fun j => U j i⟩

/-- The extracted ket is normalized: ⟨ψ|ψ⟩ = 1. -/
theorem DensityOp.pureKetOf_normalized {n : ℕ} [NeZero n] (ρ : DensityOp n) (hpure : ρ.IsPure) :
    (ρ.pureKetOf hpure).dag * (ρ.pureKetOf hpure) = 1 := by
  unfold pureKetOf
  let hH := ρ.toPosSemidefOp.toHermitianOp.isHermitian
  let U := hH.eigenvectorUnitary.val
  let i := pureEigenIndex ρ hpure
  -- The eigenvector unitary has orthonormal columns, so U†U = I
  have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  -- Therefore the i-th column has norm 1
  rw [bra_mul_ket_eq]
  simp only [Ket.dag_vec]
  -- Goal: ∑ j, conj (U j i) * U j i = 1
  -- This is (U†U)ᵢᵢ = 1ᵢᵢ = 1
  have h_diag : (Uᴴ * U) i i = 1 := by rw [h_UU]; simp
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star] at h_diag
  convert h_diag using 1

/-- The density operator equals |ψ⟩⟨ψ| where ψ is the extracted ket. -/
theorem DensityOp.pureKetOf_spec {n : ℕ} [NeZero n] (ρ : DensityOp n) (hpure : ρ.IsPure) :
    ρ.toOp = (ρ.pureKetOf hpure) * (ρ.pureKetOf hpure).dag := by
  -- From spectral theorem: ρ = U * diag(eigenvalues) * U†
  -- For a pure state, exactly one eigenvalue is 1 and rest are 0
  -- Therefore ρ = |vᵢ⟩⟨vᵢ| where vᵢ is the eigenvector for eigenvalue 1
  let hH := ρ.toPosSemidefOp.toHermitianOp.isHermitian
  let U := hH.eigenvectorUnitary.val
  let i := pureEigenIndex ρ hpure
  -- The eigenvalue at index i is 1
  have h_eig_i : hH.eigenvalues i = 1 := pureEigenIndex_spec ρ hpure
  -- Get positive semidefiniteness to know eigenvalues are nonnegative
  have hPSD := posSemidefOp_implies_mathlib ρ.toPosSemidefOp
  have h_nonneg : ∀ j, 0 ≤ hH.eigenvalues j := fun j => hPSD.eigenvalues_nonneg j
  -- From purity and spectral analysis, other eigenvalues are 0
  have h_trace : ∑ j, hH.eigenvalues j = 1 := by
    have h_trace_one := ρ.trace_one
    have h_sum_eq := hH.trace_eq_sum_eigenvalues
    have h_eq : (1 : ℂ) = ∑ k, (hH.eigenvalues k : ℂ) := by
      calc (1 : ℂ) = ρ.toOp.trace := h_trace_one.symm
        _ = ∑ k, (hH.eigenvalues k : ℂ) := h_sum_eq
    have h_re_rhs : (∑ k, (hH.eigenvalues k : ℂ)).re = ∑ k, hH.eigenvalues k := by
      simp only [Complex.re_sum, Complex.ofReal_re]
    calc ∑ j, hH.eigenvalues j = (∑ j, (hH.eigenvalues j : ℂ)).re := h_re_rhs.symm
      _ = (1 : ℂ).re := by rw [← h_eq]
      _ = 1 := rfl
  -- Since λᵢ = 1 and ∑ⱼ λⱼ = 1 with all λⱼ ≥ 0, we have λⱼ = 0 for j ≠ i
  have h_other_zero : ∀ j, j ≠ i → hH.eigenvalues j = 0 := by
    intro j hji
    have h_sum_split : ∑ k, hH.eigenvalues k =
        hH.eigenvalues i + ∑ k ∈ Finset.univ.erase i, hH.eigenvalues k := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [h_trace, h_eig_i] at h_sum_split
    have h_rest_zero : ∑ k ∈ Finset.univ.erase i, hH.eigenvalues k = 0 := by linarith
    have h_nonneg_rest : ∀ k ∈ Finset.univ.erase i, 0 ≤ hH.eigenvalues k := fun k _ => h_nonneg k
    have h_all_zero := Finset.sum_eq_zero_iff_of_nonneg h_nonneg_rest
    rw [h_rest_zero] at h_all_zero
    exact h_all_zero.mp rfl j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  -- Eigenvalue is 0 or 1 for each j
  have h_eig_val : ∀ j, (hH.eigenvalues j : ℂ) = if j = i then 1 else 0 := by
    intro j
    by_cases hji : j = i
    · simp [hji, h_eig_i]
    · simp [hji, h_other_zero j hji]
  -- Prove entry-wise equality using spectral theorem
  ext j k
  simp only [ket_mul_bra_apply, Ket.dag_vec]
  -- Unfold pureKetOf to get the i-th column of U
  unfold pureKetOf
  simp only
  -- Use spectral theorem: ρ_{jk} = ∑_m ∑_l U_{jm} λ_m δ_{ml} U*_{lk}
  --                             = ∑_m U_{jm} λ_m U*_{mk}
  -- For pure state: = U_{ji} * 1 * U*_{ki} = U_{ji} * conj(U_{ki})
  have h_spectral := hH.spectral_theorem
  -- Extract entry from spectral theorem
  have h_entry : ρ.toOp j k = (U * diagonal (Complex.ofReal ∘ hH.eigenvalues) * Uᴴ) j k := by
    conv_lhs => rw [h_spectral]
    simp only [Unitary.conjStarAlgAut_apply]
    rfl
  rw [h_entry]
  -- Simplify the matrix multiplication
  simp only [mul_apply, diagonal_apply, Function.comp_apply, conjTranspose_apply]
  -- (U * D * U†)_{jk} = ∑_m (∑_l U_{jl} D_{lm}) U†_{mk}
  --                   = ∑_m (∑_l U_{jl} (if l = m then λ_l else 0)) conj(U_{km})
  --                   = ∑_m U_{jm} λ_m conj(U_{km})
  -- For our diagonal, only the i-th eigenvalue is nonzero (= 1)
  -- So this equals U_{ji} * conj(U_{ki})
  -- First simplify the inner sum
  have h_inner : ∀ m, (∑ x_1, U j x_1 * if x_1 = m then ↑(hH.eigenvalues x_1) else 0) =
      U j m * ↑(hH.eigenvalues m) := by
    intro m
    rw [Finset.sum_eq_single m]
    · simp only [↓reduceIte]
    · intro b _ hbm
      simp only [hbm, ↓reduceIte, mul_zero]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  simp only [h_inner]
  -- Now we have ∑_m U_{jm} λ_m conj(U_{km})
  -- Only the i-th term survives (since λ_m = 0 for m ≠ i and λ_i = 1)
  rw [Finset.sum_eq_single i]
  · -- U j i * λ_i * conj(U k i) = U j i * conj(U k i) (since λ_i = 1)
    simp only [h_eig_i, Complex.ofReal_one, mul_one]
    -- Both sides are U j i * conj(U k i), just written differently
    rfl
  · intro b _ hbi
    simp only [h_other_zero b hbi, Complex.ofReal_zero, mul_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Alternative characterization using entry-wise equality. -/
theorem DensityOp.pureKetOf_entry {n : ℕ} [NeZero n] (ρ : DensityOp n) (hpure : ρ.IsPure)
    (j k : Fin n) :
    ρ.toOp j k = (ρ.pureKetOf hpure).vec j * star ((ρ.pureKetOf hpure).vec k) := by
  have h := pureKetOf_spec ρ hpure
  have h_entry := congr_fun₂ h j k
  simp only [ket_mul_bra_apply, Ket.dag_vec, starRingEnd_apply] at h_entry
  exact h_entry

/-!
## Subtype version for dependent types
-/

/-- Extract a normalized ket from a pure density operator, as a subtype.
    Returns ψ with proofs that:
    1. ψ is normalized: ⟨ψ|ψ⟩ = 1
    2. ρ = |ψ⟩⟨ψ| (entry-wise) -/
def DensityOp.pureKetOfSubtype {n : ℕ} [NeZero n] (ρ : DensityOp n) (hpure : ρ.IsPure) :
    { ψ : Ket n // ψ.dag * ψ = 1 ∧
      ρ.toOp = Matrix.of fun i j => ψ.vec i * star (ψ.vec j) } :=
  ⟨ρ.pureKetOf hpure,
   ρ.pureKetOf_normalized hpure,
   by
     ext i j
     simp only [Matrix.of_apply]
     exact ρ.pureKetOf_entry hpure i j⟩

/-!
## Round-trip properties
-/

/-- Purity of fromPure: A density operator constructed from a normalized ket is pure. -/
theorem DensityOp.fromPure_isPure {n : ℕ} (ψ : Ket n) (hψ : ψ.dag * ψ = 1) :
    (DensityOp.fromPure ψ hψ).IsPure := by
  unfold DensityOp.IsPure
  show (DensityOp.fromPure ψ hψ).toOp *
       (DensityOp.fromPure ψ hψ).toOp =
       (DensityOp.fromPure ψ hψ).toOp
  simp only [DensityOp.fromPure]
  rw [ketbra_mul_ketbra, hψ, one_smul]

/-- If we construct a density operator from a ket and extract the ket back,
    we get the original ket (up to a global phase). -/
theorem fromPure_pureKetOf_eq_mod_phase {n : ℕ} [NeZero n] (ψ : Ket n)
    (hψ : ψ.dag * ψ = 1) :
    let ρ := DensityOp.fromPure ψ hψ
    let hpure := DensityOp.fromPure_isPure ψ hψ
    ∃ θ : ℝ, ∀ i : Fin n,
      (ρ.pureKetOf hpure).vec i = Complex.exp (Complex.I * θ) * ψ.vec i := by
  intro ρ hpure
  set v := ρ.pureKetOf hpure
  -- Step 1: |v⟩⟨v| = |ψ⟩⟨ψ| entry-wise
  have h_entry : ∀ j k : Fin n,
      v.vec j * starRingEnd ℂ (v.vec k) =
      ψ.vec j * starRingEnd ℂ (ψ.vec k) := by
    intro j k
    have h_eq : (v * v.dag : Op n) = (ψ * ψ.dag : Op n) :=
      (DensityOp.pureKetOf_spec ρ hpure).symm.trans
        (show ρ.toOp = ψ * ψ.dag by
          simp only [ρ, DensityOp.fromPure])
    have := congr_fun₂ h_eq j k
    simp only [ket_mul_bra_apply, Ket.dag_vec] at this
    exact this
  -- Step 2: Define c = ⟨v|ψ⟩
  set c := ∑ k : Fin n,
    starRingEnd ℂ (v.vec k) * ψ.vec k with hc_def
  -- Step 3: v_j * c = ψ_j (multiply outer product eq by ψ_k, sum)
  have h_vc : ∀ j, v.vec j * c = ψ.vec j := by
    intro j
    rw [hc_def, Finset.mul_sum]
    have h1 : ∀ k,
        v.vec j * (starRingEnd ℂ (v.vec k) * ψ.vec k) =
        ψ.vec j * (starRingEnd ℂ (ψ.vec k) * ψ.vec k) := by
      intro k
      calc v.vec j * (starRingEnd ℂ (v.vec k) * ψ.vec k)
          = (v.vec j * starRingEnd ℂ (v.vec k)) *
            ψ.vec k := by ring
        _ = (ψ.vec j * starRingEnd ℂ (ψ.vec k)) *
            ψ.vec k := by rw [h_entry j k]
        _ = ψ.vec j * (starRingEnd ℂ (ψ.vec k) *
            ψ.vec k) := by ring
    simp_rw [h1, ← Finset.mul_sum]
    have h_norm : (∑ k : Fin n,
        starRingEnd ℂ (ψ.vec k) * ψ.vec k) = 1 := by
      have := bra_mul_ket_eq ψ.dag ψ
      simp only [Ket.dag_vec] at this
      rw [hψ] at this; exact this.symm
    rw [h_norm, mul_one]
  -- Step 4: conj(c) * c = 1 (hence normSq c = 1)
  have h_conj_c_mul_c : starRingEnd ℂ c * c = 1 := by
    -- Expand only the second c, then distribute
    conv_lhs => arg 2; rw [hc_def]
    rw [Finset.mul_sum]
    -- Rearrange: star(c) * star(v_k) * ψ_k = star(v_k * c) * ψ_k
    simp_rw [show ∀ k : Fin n,
        starRingEnd ℂ c *
          (starRingEnd ℂ (v.vec k) * ψ.vec k) =
        starRingEnd ℂ (v.vec k * c) * ψ.vec k from
      fun k => by simp only [map_mul]; ring]
    -- Substitute v_k * c = ψ_k
    simp_rw [h_vc]
    -- ∑ k, star(ψ_k) * ψ_k = ψ.dag * ψ = 1
    have := bra_mul_ket_eq ψ.dag ψ
    simp only [Ket.dag_vec] at this
    rw [hψ] at this; exact this.symm
  have h_c_normSq : Complex.normSq c = 1 := by
    have h := Complex.mul_conj c
    have h2 : (Complex.normSq c : ℂ) = 1 := by
      rw [← h, mul_comm]; exact h_conj_c_mul_c
    exact Complex.ofReal_eq_one.mp h2
  -- Step 5: v_j = conj(c) * ψ_j
  have h_v_eq : ∀ j, v.vec j =
      starRingEnd ℂ c * ψ.vec j := by
    intro j
    have h_cc : c * starRingEnd ℂ c = 1 := by
      rw [Complex.mul_conj]; simp [h_c_normSq]
    calc v.vec j
        = v.vec j * 1 := (mul_one _).symm
      _ = v.vec j * (c * starRingEnd ℂ c) := by
            rw [h_cc]
      _ = (v.vec j * c) * starRingEnd ℂ c := by ring
      _ = ψ.vec j * starRingEnd ℂ c := by rw [h_vc j]
      _ = starRingEnd ℂ c * ψ.vec j := by ring
  -- Step 6: ‖conj(c)‖ = 1, so ∃ θ, exp(θI) = conj(c)
  have h_conj_c_norm : ‖starRingEnd ℂ c‖ = 1 := by
    have h1 : (starRingEnd ℂ c) = star c := rfl
    rw [h1, norm_star]
    have h2 : ‖c‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]; exact h_c_normSq
    nlinarith [norm_nonneg c]
  rw [Complex.norm_eq_one_iff] at h_conj_c_norm
  obtain ⟨θ, hθ⟩ := h_conj_c_norm
  exact ⟨θ, fun i => by
    rw [h_v_eq i, ← hθ,
      show (↑θ : ℂ) * Complex.I = Complex.I * ↑θ
        from mul_comm _ _]⟩

end

end Quantum.Operators
