import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.Metrics.FidelityBound
import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Math.SpectralTheory.Basic
import QCryptLean.Math.SpectralTheory.Weyl
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Quantum Fidelity — Uhlmann fidelity, density-operator bounds, pure-state formulas

Fidelity constructions for positive semidefinite and density operators, together
with the pure-state specialization `F²(ρ, |ψ⟩⟨ψ|) = ⟨ψ|ρ|ψ⟩`.

## Main definitions
- `sqrtPosSemidefOp`: PSD square root `√A` for `PosSemidefOp` via CFC
- `fidelity`: Uhlmann fidelity `F(A,B) = Tr √(√A·B·√A)` for PSD operators
- `fidelitySq`: Uhlmann fidelity squared `F(A,B)^2` for PSD operators
- `DensityOp.fidelitySq`: Uhlmann fidelity squared for density operators
- `DensityOp.fidelity`: Uhlmann fidelity for density operators
- `PosSemidefOp.tensor`: tensor product of two PSD operators

## Main statements
- `fidelitySq_fromPure`: `F²(ρ, |ψ⟩⟨ψ|) = ⟨ψ|ρ|ψ⟩`
- `fidelity_fromPure`: `F(ρ, |ψ⟩⟨ψ|) = √⟨ψ|ρ|ψ⟩`
- `fidelityPureSq_tensor`: pure-state fidelity squared factorizes over tensor products
- `fidelityPureSq_tensor_general`: cast-compatible tensor-product factorization
- `fidelityPureSq_nonneg`, `fidelityPureSq_le_one`: pure-state fidelity bounds
- `fidelityPure_bounds`: `0 ≤ F ≤ 1` for pure states
- `fidelityPure_pure_self`: `F(|ψ⟩⟨ψ|, |ψ⟩⟨ψ|) = 1`
- `sqrtPosSemidefOp_sq`: `(√A)^2 = A`
- `fidelitySq_nonneg`: `0 ≤ F²(ρ,σ)`
- `fidelity_nonneg`: `0 ≤ F(ρ,σ)`
- `fidelitySq_le_one`: `F²(ρ,σ) ≤ 1`
- `fidelity_tensor_mul`: `F(A ⊗ A', B ⊗ B') = F(A,B) · F(A',B')` (Tomamichel 2016 Lemma 3.11)
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-!
## Uhlmann Fidelity

Two fidelity notions are provided:
1. Uhlmann fidelity for general PSD operators
2. Pure-state specializations for `DensityOp.fromPure`
-/

/-- Positive semidefinite square root of a `PosSemidefOp`.

    For `A` PSD with eigendecomposition `A = Σᵢ λᵢ|eᵢ⟩⟨eᵢ|`, this is
    `√A = Σᵢ √λᵢ |eᵢ⟩⟨eᵢ|`. Satisfies
    `sqrtPosSemidefOp A * sqrtPosSemidefOp A = A.toOp`. -/
noncomputable def sqrtPosSemidefOp {n : ℕ} (A : PosSemidefOp n) : Op n :=
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  CFC.sqrt A.toOp

/-- `sqrtPosSemidefOp` squared recovers `A`: `(√A)(√A) = A`. -/
lemma sqrtPosSemidefOp_sq {n : ℕ} (A : PosSemidefOp n) :
    sqrtPosSemidefOp A * sqrtPosSemidefOp A = A.toOp := by
  unfold sqrtPosSemidefOp
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  exact CFC.sqrt_mul_sqrt_self A.toOp (posSemidefOp_implies_mathlib A).nonneg

/-- `√A` is Hermitian. -/
lemma sqrtPosSemidefOp_isHermitian {n : ℕ} (A : PosSemidefOp n) :
    (sqrtPosSemidefOp A).IsHermitian := by
  unfold sqrtPosSemidefOp
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  exact ((CFC.sqrt_nonneg (a := A.toOp)).posSemidef).isHermitian

/-- Uhlmann fidelity for positive semidefinite operators:
    `F(A, B) = Tr √(√A · B · √A)`. -/
noncomputable def fidelity {n : ℕ} [NeZero n] (A B : PosSemidefOp n) : ℝ :=
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  let inner := sqrtPosSemidefOp A * B.toOp * sqrtPosSemidefOp A
  (Matrix.trace (CFC.sqrt inner)).re

/-- Uhlmann fidelity squared for positive semidefinite operators:
    `F²(A, B) = (Tr √(√A · B · √A))²`. -/
noncomputable def fidelitySq {n : ℕ} [NeZero n] (A B : PosSemidefOp n) : ℝ :=
  fidelity A B ^ 2

/-- Uhlmann fidelity is nonnegative for positive semidefinite operators. -/
theorem fidelity_nonneg_posSemidefOp {n : ℕ} [NeZero n]
    (A B : PosSemidefOp n) : 0 ≤ fidelity A B := by
  unfold fidelity
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  let S := sqrtPosSemidefOp A
  let inner := S * B.toOp * S
  have hS : S† = S := sqrtPosSemidefOp_isHermitian A
  have h_inner_psd' : (S† * B.toOp * S).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same (posSemidefOp_implies_mathlib B) S
  have h_inner_psd : inner.PosSemidef := by
    simpa [inner, hS] using h_inner_psd'
  have h_sqrt_psd : (CFC.sqrt inner).PosSemidef :=
    (CFC.sqrt_nonneg (a := inner)).posSemidef
  have htrace_re_nonneg : 0 ≤ (Matrix.trace (CFC.sqrt inner)).re :=
    (RCLike.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg h_sqrt_psd)).1
  simpa [S, inner] using htrace_re_nonneg

/-- Self-fidelity on a positive semidefinite operator:
    `F(A, A) = Tr A`. -/
lemma fidelity_self_posSemidefOp {n : ℕ} [NeZero n] (A : PosSemidefOp n) :
    fidelity A A = (Matrix.trace A.toOp).re := by
  unfold fidelity
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  have h_sq : sqrtPosSemidefOp A * sqrtPosSemidefOp A = A.toOp :=
    sqrtPosSemidefOp_sq A
  have h_inner :
      sqrtPosSemidefOp A * A.toOp * sqrtPosSemidefOp A = A.toOp * A.toOp := by
    set S := sqrtPosSemidefOp A
    have h_comm : S * A.toOp = A.toOp * S := by
      conv_lhs => rw [← h_sq]
      conv_rhs => rw [← h_sq]
      exact (mul_assoc S S S).symm
    rw [h_comm, mul_assoc, h_sq]
  simp only [h_inner, CFC.sqrt_mul_self A.toOp (posSemidefOp_implies_mathlib A).nonneg]

/-- Uhlmann fidelity for density operators:
    `F(ρ, σ) = Tr √(√ρ · σ · √ρ)`. -/
noncomputable def DensityOp.fidelity {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) : ℝ :=
  Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp

/-- Uhlmann fidelity squared for density operators:
    `F²(ρ, σ) = (Tr √(√ρ · σ · √ρ))²`. -/
noncomputable def DensityOp.fidelitySq {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) : ℝ :=
  Quantum.Metrics.fidelitySq ρ.toPosSemidefOp σ.toPosSemidefOp

/-- `F²(ρ,σ) ≥ 0` for density operators. -/
theorem fidelitySq_nonneg {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) : 0 ≤ DensityOp.fidelitySq ρ σ := by
  unfold DensityOp.fidelitySq Quantum.Metrics.fidelitySq
  exact sq_nonneg _

/-- Uhlmann fidelity is nonnegative for density operators. -/
theorem fidelity_nonneg {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) : 0 ≤ DensityOp.fidelity ρ σ := by
  simpa [DensityOp.fidelity] using
    fidelity_nonneg_posSemidefOp ρ.toPosSemidefOp σ.toPosSemidefOp

/-- Uhlmann fidelity is at most `1` for density operators. -/
theorem fidelity_le_one {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) : DensityOp.fidelity ρ σ ≤ 1 := by
  simpa [DensityOp.fidelity, Quantum.Metrics.fidelity, sqrtPosSemidefOp] using
    densityOp_cfcSqrt_sandwich_trace_le_one_viaPurification ρ σ

/-- Uhlmann fidelity squared is at most `1` for density operators. -/
theorem fidelitySq_le_one {n : ℕ} [NeZero n]
    (ρ σ : DensityOp n) : DensityOp.fidelitySq ρ σ ≤ 1 := by
  unfold DensityOp.fidelitySq Quantum.Metrics.fidelitySq
  change DensityOp.fidelity ρ σ ^ 2 ≤ 1
  exact pow_le_one₀ (fidelity_nonneg ρ σ) (fidelity_le_one ρ σ)

/-!
## Pure-State Fidelity as a Special Case

The following lemmas express the pure-state fidelity in terms of the general
Uhlmann fidelity, using `DensityOp.fromPure` (`DensityOperator.lean`).
-/

/-!
### Private Helpers for Pure-State Fidelity
-/

/-- For a Hermitian operator `S` and ket `ψ`, the bra `(S·|ψ⟩)†` equals `⟨ψ|·S`. -/
private lemma hermitian_op_ket_dag {n : ℕ} (S : Op n) (hS : S.IsHermitian) (ψ : Ket n) :
    (⟨S.mulVec ψ.vec⟩ : Ket n).dag = ψ.dag * S := by
  ext j
  simp only [Ket.dag_vec, bra_mul_op_vec, Matrix.mulVec, dotProduct, map_sum, map_mul]
  congr 1; ext i
  have h_herm : starRingEnd ℂ (S j i) = S i j := by
    have h := congrFun (congrFun hS i) j
    simp only [Matrix.conjTranspose_apply] at h
    rw [starRingEnd_apply]
    exact h
  rw [h_herm, mul_comm]

/-- For a Hermitian `S`, `S * (ψ * ψ†) * S = (S * ψ) * (S * ψ)†`. -/
private lemma fidelity_inner_eq_ketbra {n : ℕ} (ρ : DensityOp n) (ψ : Ket n) :
    let S := sqrtPosSemidefOp ρ.toPosSemidefOp
    let v : Ket n := ⟨S.mulVec ψ.vec⟩
    S * (ψ * ψ.dag) * S = v * v.dag := by
  intro S v
  have hv_dag : v.dag = ψ.dag * S :=
    hermitian_op_ket_dag S (sqrtPosSemidefOp_isHermitian ρ.toPosSemidefOp) ψ
  rw [op_mul_ketbra, ketbra_mul_op, ← hv_dag]
  congr 1

/-- `⟨(S·|ψ⟩) | (S·|ψ⟩)⟩ = ⟨ψ|ρ|ψ⟩` where `S = √ρ`. -/
private lemma ketbra_inner_eq_braOpKet {n : ℕ} (ρ : DensityOp n) (ψ : Ket n) :
    let S := sqrtPosSemidefOp ρ.toPosSemidefOp
    let v : Ket n := ⟨S.mulVec ψ.vec⟩
    (v.dag * v : ℂ) = ψ.dag * ρ.toOp * ψ := by
  intro S v
  have hv_dag : v.dag = ψ.dag * S :=
    hermitian_op_ket_dag S (sqrtPosSemidefOp_isHermitian ρ.toPosSemidefOp) ψ
  rw [hv_dag, braop_mul_ket, braop_mul_ket]
  congr 1
  ext i
  have h_SS : S * S = ρ.toOp := sqrtPosSemidefOp_sq ρ.toPosSemidefOp
  have h_eq : S.mulVec (S.mulVec ψ.vec) = ρ.toOp.mulVec ψ.vec := by
    rw [Matrix.mulVec_mulVec, h_SS]
  simp only [op_mul_ket_vec]
  exact congrFun h_eq i

/-- For a nonnegative real `r` and PSD `M`, the matrix `(r : ℂ) • M` is PSD. -/
lemma posSemidef_ofReal_smul {n : ℕ} (M : Op n)
    (hM : M.PosSemidef) (r : ℝ) (hr : 0 ≤ r) : ((r : ℂ) • M).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hM.1]
    simp [RCLike.star_def]
  · intro x
    have hq := hM.dotProduct_mulVec_nonneg x
    have hform : star x ⬝ᵥ ((r : ℂ) • M).mulVec x = (r : ℂ) * (star x ⬝ᵥ M.mulVec x) := by
      simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hform]
    rw [Complex.nonneg_iff] at hq ⊢
    obtain ⟨hq_re, hq_im⟩ := hq
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero] at *
    exact ⟨mul_nonneg hr hq_re, by rw [← hq_im, mul_zero]⟩

/-- When `⟨v|v⟩ = 0`, all components of `v` are zero. -/
private lemma ket_components_zero_of_inner_zero {n : ℕ} (v : Ket n)
    (hv : (v.dag * v : ℂ) = 0) :
    ∀ i, v.vec i = 0 := by
  have h_sum : ∑ i, Complex.normSq (v.vec i) = 0 := by
    have h_expand : (v.dag * v : ℂ) = ∑ i, starRingEnd ℂ (v.vec i) * v.vec i := by
      simp only [bra_mul_ket_eq, Ket.dag_vec]
    rw [h_expand] at hv
    have h_re : (∑ i, starRingEnd ℂ (v.vec i) * v.vec i).re = 0 :=
      Complex.ext_iff.mp hv |>.1
    have h_eq : ∀ i, (starRingEnd ℂ (v.vec i) * v.vec i).re = Complex.normSq (v.vec i) := by
      intro i
      rw [starRingEnd_apply]
      simp only [Complex.star_def, Complex.normSq_apply, Complex.mul_re,
        Complex.conj_re, Complex.conj_im]
      ring
    simp_rw [← h_eq]
    exact Complex.re_sum _ _ ▸ h_re
  intro i
  exact Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp h_sum i
      (Finset.mem_univ i))

/-- `CFC.sqrt` of a rank-1 PSD matrix `v·v†` equals `(√α/α)•(v·v†)` where `α = ⟨v|v⟩`. -/
private lemma cfcSqrt_ketbra {n : ℕ} (v : Ket n) (α : ℝ) (hα : 0 < α)
    (hv : (v.dag * v : ℂ) = (α : ℂ)) :
    letI : PartialOrder (Op n) := Matrix.instPartialOrder
    letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
    letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
    CFC.sqrt (v * v.dag) = ((Real.sqrt α / α : ℝ) : ℂ) • (v * v.dag) := by
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  apply CFC.sqrt_unique
  · rw [smul_mul_smul_comm, ketbra_mul_ketbra, hv, smul_smul]
    have hc : ((Real.sqrt α / α : ℝ) : ℂ) * ((Real.sqrt α / α : ℝ) : ℂ) * (α : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_eq_one]
      have hα_ne : α ≠ 0 := ne_of_gt hα
      field_simp [div_mul_div_comm]
      linarith [Real.mul_self_sqrt (le_of_lt hα)]
    rw [hc, one_smul]
  · rw [nonneg_iff_posSemidef]
    exact posSemidef_ofReal_smul (v * v.dag) (ketbra_posSemidef v) _
      (div_nonneg (Real.sqrt_nonneg α) (le_of_lt hα))

/-- Trace of a rank-1 matrix `v · v†` equals the inner product `⟨v|v⟩`. -/
private lemma trace_ketbra_self {n : ℕ} (v : Ket n) :
    (v * v.dag).trace = v.dag * v := by
  simp only [Matrix.trace, Matrix.diag, ket_mul_bra_apply, Ket.dag_vec, bra_mul_ket_eq,
    starRingEnd_apply]
  congr 1; ext i; ring

/-- The bra-ket expectation `⟨ψ|A|ψ⟩` is the quadratic form of `A` on `ψ.vec`. -/
lemma braOpKet_eq_quadraticForm {n : ℕ} (A : Op n) (ψ : Ket n) :
    ψ.dag * A * ψ = quadraticForm A ψ.vec := by
  rw [braop_mul_ket]
  simp only [bra_mul_ket_eq, op_mul_ket_vec, Ket.dag_vec]
  unfold quadraticForm dotProduct
  rfl

/-- Pure-state case (unsquared): `F(ρ, |ψ⟩⟨ψ|) = √⟨ψ|ρ|ψ⟩`. -/
theorem fidelity_fromPure {n : ℕ} [NeZero n]
    (ρ : DensityOp n) (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    DensityOp.fidelity ρ (DensityOp.fromPure ψ hψ) = Real.sqrt ((ψ.dag * ρ.toOp * ψ).re) := by
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  let S := sqrtPosSemidefOp ρ.toPosSemidefOp
  let v : Ket n := ⟨S.mulVec ψ.vec⟩
  set α := (ψ.dag * ρ.toOp * ψ).re with hα_def
  have hv_inner_eq : (v.dag * v : ℂ) = ψ.dag * ρ.toOp * ψ :=
    ketbra_inner_eq_braOpKet ρ ψ
  have hv_inner : (v.dag * v : ℂ) = (α : ℂ) := by
    rw [hv_inner_eq]
    apply Complex.ext
    · simp [hα_def]
    · simp only [Complex.ofReal_im]
      have h_im : (ψ.dag * ρ.toOp * ψ).im = 0 := by
        have := braOpKet_hermitian_im_zero ρ.toOp ρ.toPosSemidefOp.toHermitianOp.isHermitian ψ
        rwa [← braop_mul_ket] at this
      exact h_im
  have h_inner : sqrtPosSemidefOp ρ.toPosSemidefOp *
      (DensityOp.fromPure ψ hψ).toPosSemidefOp.toOp *
      sqrtPosSemidefOp ρ.toPosSemidefOp = v * v.dag := by
    change S * (ψ * ψ.dag) * S = v * v.dag
    exact fidelity_inner_eq_ketbra ρ ψ
  unfold DensityOp.fidelity Quantum.Metrics.fidelity
  simp only [h_inner]
  have hα_nonneg : 0 ≤ α := by
    rw [hα_def, braOpKet_eq_quadraticForm]
    exact ρ.toPosSemidefOp.pos_semidef ψ.vec
  rcases hα_nonneg.eq_or_lt with hα_zero | hα_pos
  · have hα_eq : α = 0 := hα_zero.symm
    have hv_inner_zero : (v.dag * v : ℂ) = 0 := by
      rw [hv_inner, hα_eq, Complex.ofReal_zero]
    have hv_zero : ∀ i, v.vec i = 0 := ket_components_zero_of_inner_zero v hv_inner_zero
    have h_ketbra_zero : v * v.dag = 0 := by
      ext i j; simp [ket_mul_bra_apply, Ket.dag_vec, hv_zero i, hv_zero j]
    rw [h_ketbra_zero, CFC.sqrt_zero, Matrix.trace_zero, Complex.zero_re, hα_eq]
    simp
  · rw [cfcSqrt_ketbra v α hα_pos hv_inner]
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    rw [Matrix.trace_smul, trace_ketbra_self, hv_inner]
    simp only [smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    field_simp

/-- Pure-state case: `F²(ρ, |ψ⟩⟨ψ|) = ⟨ψ|ρ|ψ⟩`. -/
theorem fidelitySq_fromPure {n : ℕ} [NeZero n]
    (ρ : DensityOp n) (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) = (ψ.dag * ρ.toOp * ψ).re := by
  have h_fid :
      DensityOp.fidelity ρ (DensityOp.fromPure ψ hψ) =
        Real.sqrt ((ψ.dag * ρ.toOp * ψ).re) :=
    fidelity_fromPure ρ ψ hψ
  unfold DensityOp.fidelitySq Quantum.Metrics.fidelitySq DensityOp.fidelity at *
  rw [h_fid]
  exact Real.sq_sqrt (by
    rw [braOpKet_eq_quadraticForm]
    exact ρ.toPosSemidefOp.pos_semidef ψ.vec)

/-- Fidelity squared against a pure product state factorizes over tensor products. -/
lemma fidelityPureSq_tensor {n m : ℕ} [NeZero n] [NeZero m]
    (ρ : DensityOp n) (σ : DensityOp m)
    (ψ : Ket n) (φ : Ket m) (hψ : (ψ.dag * ψ) = 1) (hφ : (φ.dag * φ) = 1) :
    DensityOp.fidelitySq (ρ.tensor σ)
      (DensityOp.fromPure (ψ ⊗ φ)
        (by rw [Ket.dag_tensor, bra_tensor_mul_ket_tensor, hψ, hφ]; ring)) =
    DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) *
    DensityOp.fidelitySq σ (DensityOp.fromPure φ hφ) := by
  haveI : NeZero (n * m) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne m)⟩
  rw [fidelitySq_fromPure, fidelitySq_fromPure, fidelitySq_fromPure]
  have h_assoc :
      (ψ ⊗ φ).dag * (ρ.tensor σ).toOp * (ψ ⊗ φ) =
        (ψ ⊗ φ).dag * ((ρ.tensor σ).toOp * (ψ ⊗ φ)) :=
    braop_mul_ket (ψ ⊗ φ).dag (ρ.tensor σ).toOp (ψ ⊗ φ)
  rw [h_assoc]
  have hmul : (ρ.tensor σ).toOp * (ψ ⊗ φ) = (ρ.toOp * ψ) ⊗ (σ.toOp * φ) := by
    change ((ρ.toOp ⊗ σ.toOp) * (ψ ⊗ φ)) = _
    rw [Op.tensor_mulKet]
  rw [hmul, Ket.dag_tensor, bra_tensor_mul_ket_tensor]
  have h_imψ : (ψ.dag * (ρ.toOp * ψ)).im = 0 :=
    braOpKet_hermitian_im_zero ρ.toOp ρ.toPosSemidefOp.toHermitianOp.isHermitian ψ
  have h_imφ : (φ.dag * (σ.toOp * φ)).im = 0 :=
    braOpKet_hermitian_im_zero σ.toOp σ.toPosSemidefOp.toHermitianOp.isHermitian φ
  simpa [Matrix.mul_assoc] using
    (by rw [Complex.mul_re, h_imψ, h_imφ, mul_zero, sub_zero] :
      ((ψ.dag * (ρ.toOp * ψ)) * (φ.dag * (σ.toOp * φ))).re =
        (ψ.dag * (ρ.toOp * ψ)).re * (φ.dag * (σ.toOp * φ)).re)

/-- Cast-compatible version of `fidelityPureSq_tensor`.
    Note: `[NeZero d]` is required because `DensityOp.fidelitySq` mentions `DensityOp d`
    in its return type and needs `[NeZero d]` for elaboration, even though the value is
    derivable from `h` and `[NeZero n]`, `[NeZero m]`. -/
lemma fidelityPureSq_tensor_general {n m d : ℕ} [NeZero n] [NeZero m] [NeZero d]
    (h : n * m = d) (ρ : DensityOp n) (σ : DensityOp m) (ψ : Ket n) (φ : Ket m)
    (hψ : (ψ.dag * ψ) = 1) (hφ : (φ.dag * φ) = 1) :
    DensityOp.fidelitySq
      (DensityOp.castDim h (ρ.tensor σ))
      (DensityOp.fromPure (Ket.cast h (ψ ⊗ φ))
        (by
          cases h
          simp [Ket.cast, Ket.dag_tensor, bra_tensor_mul_ket_tensor, hψ, hφ])) =
    DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) *
    DensityOp.fidelitySq σ (DensityOp.fromPure φ hφ) := by
  subst h
  exact fidelityPureSq_tensor ρ σ ψ φ hψ hφ

/-!
## Helper Lemmas for Pure-State Fidelity

These helper lemmas establish properties of the pure-state fidelity
`F²(ρ, |ψ⟩⟨ψ|) = ⟨ψ|ρ|ψ⟩`.
-/

/-- The inner product `⟨ψ|ρ|ψ⟩` is non-negative for density operators. -/
lemma braOpKet_nonneg {n : ℕ} (ρ : DensityOp n) (ψ : Ket n) :
    0 ≤ (ψ.dag * ρ.toOp * ψ).re := by
  rw [braOpKet_eq_quadraticForm]
  exact ρ.toPosSemidefOp.pos_semidef ψ.vec

/-- The inner product `⟨ψ|ρ|ψ⟩` is at most `1` for density operators and normalized states. -/
lemma braOpKet_le_one {n : ℕ} (ρ : DensityOp n) (ψ : Ket n)
    (hψ : (ψ.dag * ψ) = 1) : (ψ.dag * ρ.toOp * ψ).re ≤ 1 := by
  by_cases hn : n = 0
  · subst hn
    rw [braOpKet_eq_quadraticForm]
    simp only [quadraticForm, dotProduct, Finset.univ_eq_empty, Finset.sum_empty, Complex.zero_re]
    linarith
  · haveI : NeZero n := ⟨hn⟩
    let hH := ρ.toPosSemidefOp.toHermitianOp.isHermitian
    let ev := hH.eigenvalues
    have h_ev_bounds := density_eigenvalues_bound ρ
    have h_ev_nonneg : ∀ i, 0 ≤ ev i := fun i => (h_ev_bounds i).1
    have h_ev_le_one : ∀ i, ev i ≤ 1 := fun i => (h_ev_bounds i).2
    have h_spec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h_spec
    let U := hH.eigenvectorUnitary.val
    have h_UU : U† * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    have h_UU' : U * U† = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    let φ_vec := U†.mulVec ψ.vec
    let a := fun i => Complex.normSq (φ_vec i)
    have h_a_nonneg : ∀ i, 0 ≤ a i := fun i => Complex.normSq_nonneg _
    have h_a_sum : ∑ i, a i = 1 := by
      have h1 : ∑ i, a i = (star φ_vec ⬝ᵥ φ_vec).re := by
        have h_eq : star φ_vec ⬝ᵥ φ_vec = ∑ i, star (φ_vec i) * φ_vec i := rfl
        rw [h_eq]
        have h_sum_re : (∑ i, star (φ_vec i) * φ_vec i).re = ∑ i, (star (φ_vec i) * φ_vec i).re :=
          Complex.re_sum _ _
        rw [h_sum_re]
        congr 1; ext i
        have h1 : star (φ_vec i) = (starRingEnd ℂ) (φ_vec i) := rfl
        rw [h1, RCLike.conj_mul]
        simp only [a, Complex.normSq_eq_norm_sq]
        norm_cast
      have h2 : star φ_vec ⬝ᵥ φ_vec = star ψ.vec ⬝ᵥ ψ.vec := by
        change star (U†.mulVec ψ.vec) ⬝ᵥ (U†.mulVec ψ.vec) = star ψ.vec ⬝ᵥ ψ.vec
        rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.conjTranspose_conjTranspose]
        rw [Matrix.vecMul_vecMul]
        have h3 : Matrix.vecMul (star ψ.vec) (U * U†) = star ψ.vec := by
          rw [h_UU', Matrix.vecMul_one]
        rw [h3]
      have h3 : star ψ.vec ⬝ᵥ ψ.vec = 1 := by
        have h_bra := hψ
        simp only [bra_mul_ket_eq, Ket.dag_vec] at h_bra
        have h_eq : star ψ.vec ⬝ᵥ ψ.vec = ∑ i, star (ψ.vec i) * ψ.vec i := rfl
        rw [h_eq]
        have h_star_eq : ∀ i, star (ψ.vec i) = (starRingEnd ℂ) (ψ.vec i) := fun _ => rfl
        simp_rw [h_star_eq]
        exact h_bra
      rw [h1, h2, h3, Complex.one_re]
    have h_expect : (ψ.dag * ρ.toOp * ψ).re = ∑ i, ev i * a i := by
      rw [braOpKet_eq_quadraticForm]
      unfold quadraticForm
      rw [h_spec]
      convert spectral_quadratic_form_re U ev ψ.vec using 2
    rw [h_expect]
    calc ∑ i, ev i * a i ≤ ∑ i, 1 * a i := by
          apply Finset.sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_right (h_ev_le_one i) (h_a_nonneg i)
      _ = ∑ i, a i := by simp only [one_mul]
      _ = 1 := h_a_sum

/-- Pure-state fidelity squared is non-negative. -/
theorem fidelityPureSq_nonneg {n : ℕ} [NeZero n] (ρ : DensityOp n) (ψ : Ket n)
    (hψ : (ψ.dag * ψ) = 1) :
    0 ≤ DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) := by
  rw [fidelitySq_fromPure]
  exact braOpKet_nonneg ρ ψ

/-- Pure-state fidelity squared is at most `1` for normalized states. -/
theorem fidelityPureSq_le_one {n : ℕ} [NeZero n] (ρ : DensityOp n) (ψ : Ket n)
    (hψ : (ψ.dag * ψ) = 1) :
    DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) ≤ 1 := by
  rw [fidelitySq_fromPure]
  exact braOpKet_le_one ρ ψ hψ

/-- Pure-state fidelity is bounded: `0 ≤ F(ρ, |ψ⟩⟨ψ|) ≤ 1`. -/
theorem fidelityPure_bounds {n : ℕ} [NeZero n] (ρ : DensityOp n) (ψ : Ket n)
    (hψ : (ψ.dag * ψ) = 1) :
    0 ≤ DensityOp.fidelity ρ (DensityOp.fromPure ψ hψ) ∧
    DensityOp.fidelity ρ (DensityOp.fromPure ψ hψ) ≤ 1 := by
  rw [fidelity_fromPure]
  constructor
  · exact Real.sqrt_nonneg _
  · rw [Real.sqrt_le_one]
    exact braOpKet_le_one ρ ψ hψ

/-- Pure-state fidelity of a pure state with itself equals `1`. -/
theorem fidelityPure_pure_self {n : ℕ} [NeZero n] (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    DensityOp.fidelity (DensityOp.fromPure ψ hψ) (DensityOp.fromPure ψ hψ) = 1 := by
  rw [fidelity_fromPure (DensityOp.fromPure ψ hψ) ψ hψ]
  change Real.sqrt ((ψ.dag * (ψ * ψ.dag) * ψ).re) = 1
  simp [hψ]

/-- Pure-state fidelity squared is invariant under dimension casting.
    Note: `[NeZero m]` is required because `DensityOp.fidelitySq` mentions `DensityOp m`
    in its return type and needs `[NeZero m]` for elaboration, even though the value is
    derivable from `h : n = m` and `[NeZero n]`. -/
lemma fidelityPureSq_castDim {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) (ρ : DensityOp n)
    (ψ : Ket m) (hψ : (ψ.dag * ψ) = 1) :
    DensityOp.fidelitySq (DensityOp.castDim h ρ) (DensityOp.fromPure ψ hψ) =
    DensityOp.fidelitySq ρ (DensityOp.fromPure (Ket.cast h.symm ψ) (by subst h; exact hψ)) := by
  subst h; rfl

/-!
## Tensor-Product Fidelity Multiplicativity

Tomamichel 2016, Lemma 3.11: Uhlmann fidelity is multiplicative under tensor products.
-/

end Quantum.Metrics

namespace Quantum.Operators

/-- Tensor product of two positive semidefinite operators.

    If `A : PosSemidefOp n` and `B : PosSemidefOp m`, then `A.toOp ⊗ B.toOp` is positive
    semidefinite and Hermitian, giving a `PosSemidefOp (n * m)`.  This is the PSD-layer
    analogue of `DensityOp.tensor` and `SubDensityOp.tensor`. -/
noncomputable def PosSemidefOp.tensor {n m : ℕ} (A : PosSemidefOp n) (B : PosSemidefOp m) :
    PosSemidefOp (n * m) where
  toOp := A.toOp ⊗ B.toOp
  isHermitian := by
    unfold Matrix.IsHermitian
    rw [Op.tensor_conjTranspose, A.isHermitian, B.isHermitian]
  pos_semidef :=
    Op.tensor_posSemidef A.toOp B.toOp A.isHermitian B.isHermitian A.pos_semidef B.pos_semidef

end Quantum.Operators

namespace Quantum.Metrics

open Quantum.Operators in
/-- **Tomamichel 2016 Lemma 3.11 — Uhlmann fidelity is multiplicative under tensor products.**

For positive semidefinite operators `A B : PosSemidefOp n` and `A' B' : PosSemidefOp m`,
`F(A ⊗ A', B ⊗ B') = F(A, B) · F(A', B')`.

We prove this via the Uhlmann form `F = Tr √(√A · B · √A)`. The key steps are:
1. `√(A ⊗ A') = √A ⊗ √A'`, established by uniqueness of the CFC square root (the
   tensor `√A ⊗ √A'` squares to `A ⊗ A'` and is PSD).
2. The inner sandwich `(√A ⊗ √A')(B ⊗ B')(√A ⊗ √A') = (√A · B · √A) ⊗ (√A' · B' · √A')`
   follows from mixed-product of tensor operations.
3. `√(X ⊗ Y) = √X ⊗ √Y` for PSD `X`, `Y`, again by CFC uniqueness.
4. `Tr(X ⊗ Y) = Tr X · Tr Y` together with reality of PSD traces gives the factorization. -/
theorem fidelity_tensor_mul {n m : ℕ} [NeZero n] [NeZero m] [NeZero (n * m)]
    (A B : PosSemidefOp n) (A' B' : PosSemidefOp m) :
    fidelity (A.tensor A') (B.tensor B') = fidelity A B * fidelity A' B' := by
  -- Instantiate the CFC-required instances for Op (n * m).
  letI : PartialOrder (Op (n * m)) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op (n * m)) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op (n * m)) := Matrix.instNonnegSpectrumClass
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  letI : PartialOrder (Op m) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op m) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op m) := Matrix.instNonnegSpectrumClass
  -- Abbreviations for PSD square roots.
  set SA  := sqrtPosSemidefOp A  with hSA_def
  set SA' := sqrtPosSemidefOp A' with hSA'_def
  -- Step 1: √(A ⊗ A') = √A ⊗ √A'.
  -- Witness SA ⊗ SA' satisfies (SA ⊗ SA')² = (A ⊗ A').toOp and is PSD.
  have h_sq_tensor : Op.tensor SA SA' * Op.tensor SA SA' = (A.tensor A').toOp := by
    rw [Op.tensor_mul, sqrtPosSemidefOp_sq A, sqrtPosSemidefOp_sq A']
    rfl
  have h_SA_psd : SA.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]; exact CFC.sqrt_nonneg A.toOp
  have h_SA'_psd : SA'.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]; exact CFC.sqrt_nonneg A'.toOp
  have h_tensor_SA_psd : (Op.tensor SA SA').PosSemidef := by
    have hKron : (Matrix.kroneckerMap (· * ·) SA SA').PosSemidef :=
      h_SA_psd.kronecker h_SA'_psd
    unfold Op.tensor; rw [Matrix.reindex_apply]
    exact (Matrix.posSemidef_submatrix_equiv finProdFinEquiv.symm).mpr hKron
  have h_sqrt_tensor : sqrtPosSemidefOp (A.tensor A') = Op.tensor SA SA' := by
    unfold sqrtPosSemidefOp
    exact CFC.sqrt_unique h_sq_tensor h_tensor_SA_psd.nonneg
  -- Step 2: Unfold fidelity and rewrite using h_sqrt_tensor.
  -- inner(A⊗A', B⊗B') = (SA⊗SA') * (B.toOp⊗B'.toOp) * (SA⊗SA')
  --                    = (SA*B.toOp*SA) ⊗ (SA'*B'.toOp*SA')
  set inner  : Op n      := SA  * B.toOp  * SA   with hinner_def
  set inner' : Op m      := SA' * B'.toOp * SA'  with hinner'_def
  have h_inner_tensor :
      Op.tensor SA SA' * (B.tensor B').toOp * Op.tensor SA SA' = Op.tensor inner inner' := by
    change Op.tensor SA SA' * Op.tensor B.toOp B'.toOp * Op.tensor SA SA' =
      Op.tensor inner inner'
    rw [Op.tensor_mul, Op.tensor_mul]
  -- Step 3: √(inner ⊗ inner') = √inner ⊗ √inner'.
  have h_inner_psd : inner.PosSemidef := by
    have hS : SA† = SA := sqrtPosSemidefOp_isHermitian A
    simpa [inner, hS] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same
        (posSemidefOp_implies_mathlib B) SA
  have h_inner'_psd : inner'.PosSemidef := by
    have hS' : SA'† = SA' := sqrtPosSemidefOp_isHermitian A'
    simpa [inner', hS'] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same
        (posSemidefOp_implies_mathlib B') SA'
  have h_sq_inner_tensor :
      Op.tensor (CFC.sqrt inner) (CFC.sqrt inner') * Op.tensor (CFC.sqrt inner) (CFC.sqrt inner') =
        Op.tensor inner inner' := by
    rw [Op.tensor_mul, CFC.sqrt_mul_sqrt_self inner h_inner_psd.nonneg,
      CFC.sqrt_mul_sqrt_self inner' h_inner'_psd.nonneg]
  have h_cfcSqrt_inner_psd : (CFC.sqrt inner).PosSemidef :=
    (CFC.sqrt_nonneg inner).posSemidef
  have h_cfcSqrt_inner'_psd : (CFC.sqrt inner').PosSemidef :=
    (CFC.sqrt_nonneg inner').posSemidef
  have h_tensor_cfcSqrt_psd : (Op.tensor (CFC.sqrt inner) (CFC.sqrt inner')).PosSemidef := by
    have hKron : (Matrix.kroneckerMap (· * ·) (CFC.sqrt inner) (CFC.sqrt inner')).PosSemidef :=
      h_cfcSqrt_inner_psd.kronecker h_cfcSqrt_inner'_psd
    unfold Op.tensor; rw [Matrix.reindex_apply]
    exact (Matrix.posSemidef_submatrix_equiv finProdFinEquiv.symm).mpr hKron
  have h_sqrt_inner_tensor : CFC.sqrt (Op.tensor inner inner') =
      Op.tensor (CFC.sqrt inner) (CFC.sqrt inner') := by
    exact CFC.sqrt_unique h_sq_inner_tensor h_tensor_cfcSqrt_psd.nonneg
  -- Step 4: Use trace factorization and reality of PSD traces to conclude.
  -- Both CFC.sqrt inner and CFC.sqrt inner' are PSD, so their traces are real (im = 0).
  have h_re_inner : (Matrix.trace (CFC.sqrt inner)).im = 0 := by
    have h := h_cfcSqrt_inner_psd.trace_nonneg
    rw [Complex.le_def] at h
    exact h.2.symm
  have h_re_inner' : (Matrix.trace (CFC.sqrt inner')).im = 0 := by
    have h := h_cfcSqrt_inner'_psd.trace_nonneg
    rw [Complex.le_def] at h
    exact h.2.symm
  -- Unfold both sides and rewrite.
  change (Matrix.trace (CFC.sqrt (sqrtPosSemidefOp (A.tensor A') *
        (B.tensor B').toOp * sqrtPosSemidefOp (A.tensor A')))).re =
      (Matrix.trace (CFC.sqrt (SA * B.toOp * SA))).re *
        (Matrix.trace (CFC.sqrt (SA' * B'.toOp * SA'))).re
  -- The whole inner expression collapses: use h_sqrt_tensor then h_inner_tensor.
  have h_inner_eq : sqrtPosSemidefOp (A.tensor A') * (B.tensor B').toOp *
      sqrtPosSemidefOp (A.tensor A') = Op.tensor inner inner' := by
    rw [h_sqrt_tensor]
    exact h_inner_tensor
  rw [h_inner_eq, h_sqrt_inner_tensor, Op.trace_tensor]
  simp only [Complex.mul_re, h_re_inner, h_re_inner', mul_zero, sub_zero]
  -- inner = SA * B.toOp * SA and inner' = SA' * B'.toOp * SA' by definition.
  rfl

end Quantum.Metrics
