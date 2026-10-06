import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.Metrics.PolarUnitary
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# σ^(−1/2) Functional Calculus — inverse square root for positive-definite operators

Defines the inverse square root `σ^(−1/2)` for positive-definite operators via the
continuous functional calculus, and states the key algebraic and order-theoretic
identities consumed by the quantum LHL proof chain.

## Scope restriction

The inverse square root is defined only for **positive-definite** (PosDef) operators,
because `σ⁻¹` is only well-defined when `σ` is invertible.  The PSD case (rank-deficient
σ) requires a limiting regularization `σ ↦ σ + ε·I` and is deferred to a future PR.

## Main definitions

- `Matrix.PosDef.inverseSqrt`: `σ^(−1/2) := CFC.sqrt σ⁻¹`

## Main statements

1. `Matrix.PosDef.inverseSqrt_posSemidef` — `σ^(−1/2)` is PSD
2. `Matrix.PosDef.inverseSqrt_isHermitian` — `σ^(−1/2)` is self-adjoint
3. `Matrix.PosDef.inverseSqrt_one` — `1^(−1/2) = 1`
4. `Matrix.PosDef.inverseSqrt_sq` — `(σ^(−1/2))² = σ⁻¹`
5. `Matrix.PosDef.inverseSqrt_sandwich_eq_one` — `σ^(−1/2) · σ · σ^(−1/2) = 1`
6. `Matrix.PosDef.inverseSqrt_sandwich_mono` — Löwner sandwich monotonicity
7. `Matrix.PosDef.inverseSqrt_sandwich_of_opLe` — feasibility-to-sandwich conversion
8. `traceNorm_sq_le_sandwich_trace` — σ-weighted operator Cauchy–Schwarz

The two-sided σ-coordinate order dictionary and the conjugation-transport identity
built on these are in `QCryptLean.Quantum.Operators.InverseSqrtSandwichIff`.

## Tomamichel reference

Tomamichel 2016, §7.3.2, Proposition 7.1, eq. 7.37–7.41.  The sandwich identity (5)
and the feasibility conversion (7) are the two key steps that convert `ρ ≤_PSD t·σ`
into `σ^(−1/2)·ρ·σ^(−1/2) ≤_PSD t·I`, which the LHL Jensen step then consummates.

## Consumer

`InfoTheory.QuantumLHL.joint_traceNorm_le_sqrt_card_mul_lambda` in
`InfoTheory/QuantumLHL/Main.lean`.  The chain is:
 - `inverseSqrt_sandwich_of_opLe` — turn feasibility into bounded sandwich
 - `traceNorm_sq_le_sandwich_trace` — σ-weighted Cauchy–Schwarz
 - Jensen's inequality on √
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder BigOperators

noncomputable section

namespace Matrix.PosDef

/-!
## The inverse square root operator
-/

/-- The inverse square root of a positive-definite operator, defined via the
continuous functional calculus.

For `hσ : σ.PosDef`, `hσ.inverseSqrt = CFC.sqrt σ⁻¹`.

The CFC square root applied to `σ⁻¹` (which is itself positive definite by
`Matrix.PosDef.inv`) gives a self-adjoint, positive-semidefinite operator whose
square equals `σ⁻¹`.  This is the standard `σ^(−1/2)` used in quantum information.

Reference: Tomamichel 2016, §7.3.2.  The `PosDef` hypothesis is essential: it ensures
`σ` is invertible (`Matrix.PosDef.isUnit`) so that `σ⁻¹` is well-defined and also PosDef
(`Matrix.PosDef.inv`). -/
noncomputable def inverseSqrt {n : ℕ} {σ : Op n}
    (_hσ : σ.PosDef) : Op n :=
  CFC.sqrt σ⁻¹

/-!
## Basic properties of the inverse square root
-/

/-- The inverse square root of a positive-definite operator is positive semidefinite.

Proof: `σ⁻¹` is PosDef (hence nonneg in the `MatrixOrder` sense) by
`Matrix.PosDef.inv`, and `CFC.sqrt` applied to a nonneg element yields a nonneg element
by `CFC.sqrt_nonneg`. -/
theorem inverseSqrt_posSemidef {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) : hσ.inverseSqrt.PosSemidef := by
  unfold inverseSqrt
  exact (CFC.sqrt_nonneg σ⁻¹).posSemidef

/-- The inverse square root of a positive-definite operator is Hermitian (self-adjoint).

Consequence of `inverseSqrt_posSemidef`, since every PSD matrix is Hermitian. -/
theorem inverseSqrt_isHermitian {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) : hσ.inverseSqrt.IsHermitian :=
  hσ.inverseSqrt_posSemidef.isHermitian

/-- `1^{-1/2} = 1`.

`inverseSqrt` ignores its `PosDef` argument, so every proof of `(1 : Op n).PosDef`
gives the same value; the statement takes the hypothesis explicitly because
`inverseSqrt` is indexed by it. -/
theorem inverseSqrt_one {n : ℕ} (h : (1 : Op n).PosDef) : h.inverseSqrt = 1 := by
  rw [Matrix.PosDef.inverseSqrt, inv_one, CFC.sqrt_one]

/-- The inverse square root satisfies `(σ^(−1/2))² = σ⁻¹`.

Proof: `CFC.sqrt_mul_sqrt_self` applied to `σ⁻¹` gives
`CFC.sqrt σ⁻¹ * CFC.sqrt σ⁻¹ = σ⁻¹`.

Reference: Tomamichel 2016, definition of σ^(−1/2). -/
theorem inverseSqrt_sq {n : ℕ} {σ : Op n} (hσ : σ.PosDef) :
    hσ.inverseSqrt * hσ.inverseSqrt = σ⁻¹ := by
  unfold inverseSqrt
  exact CFC.sqrt_mul_sqrt_self σ⁻¹ hσ.inv.posSemidef.nonneg

/-- The inverse square root of a positive-definite operator commutes with `σ⁻¹`.

Both arise from applying the continuous functional calculus to the same positive
operator `σ⁻¹`, so they commute by `Commute.cfc_nnreal`. -/
theorem inverseSqrt_commute_inv {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) : Commute hσ.inverseSqrt σ⁻¹ := by
  change Commute (CFC.sqrt σ⁻¹) σ⁻¹
  rw [CFC.sqrt_eq_cfc]
  exact Commute.cfc_nnreal (Commute.refl σ⁻¹) NNReal.sqrt

/-- The inverse square root of a positive-definite operator commutes with `σ`. -/
theorem inverseSqrt_commute {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) : Commute hσ.inverseSqrt σ := by
  have hu_det : IsUnit σ.det := (Matrix.isUnit_iff_isUnit_det σ).mp hσ.isUnit
  have hinv_mul : σ⁻¹ * σ = 1 := Matrix.nonsing_inv_mul σ hu_det
  have hmul_inv : σ * σ⁻¹ = 1 := Matrix.mul_nonsing_inv σ hu_det
  have h1 : hσ.inverseSqrt * σ⁻¹ = σ⁻¹ * hσ.inverseSqrt := hσ.inverseSqrt_commute_inv.eq
  have h2 : σ * (hσ.inverseSqrt * σ⁻¹) * σ = σ * (σ⁻¹ * hσ.inverseSqrt) * σ := by rw [h1]
  have hL : σ * (hσ.inverseSqrt * σ⁻¹) * σ = σ * hσ.inverseSqrt := by
    rw [mul_assoc σ (hσ.inverseSqrt * σ⁻¹) σ, mul_assoc hσ.inverseSqrt σ⁻¹ σ,
        hinv_mul, mul_one]
  have hR : σ * (σ⁻¹ * hσ.inverseSqrt) * σ = hσ.inverseSqrt * σ := by
    rw [← mul_assoc σ σ⁻¹ hσ.inverseSqrt, hmul_inv, one_mul]
  rw [hL, hR] at h2
  exact h2.symm

/-- The sandwich identity: `σ^(−1/2) · σ · σ^(−1/2) = 1`.

Since `σ^(−1/2)` commutes with `σ` and `σ^(−1/2) · σ^(−1/2) = σ⁻¹`,
`σ^(−1/2) · σ · σ^(−1/2) = σ · σ^(−1/2) · σ^(−1/2) = σ · σ⁻¹ = 1`.

Reference: Tomamichel 2016, §7.3.2. -/
theorem inverseSqrt_sandwich_eq_one {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) :
    hσ.inverseSqrt * σ * hσ.inverseSqrt = 1 := by
  have hu_det : IsUnit σ.det := (Matrix.isUnit_iff_isUnit_det σ).mp hσ.isUnit
  have hmul_inv : σ * σ⁻¹ = 1 := Matrix.mul_nonsing_inv σ hu_det
  calc hσ.inverseSqrt * σ * hσ.inverseSqrt
      = (σ * hσ.inverseSqrt) * hσ.inverseSqrt := by rw [hσ.inverseSqrt_commute.eq]
    _ = σ * (hσ.inverseSqrt * hσ.inverseSqrt) := by rw [mul_assoc]
    _ = σ * σ⁻¹ := by rw [hσ.inverseSqrt_sq]
    _ = 1 := hmul_inv

/-!
## Löwner-order lemmas
-/

/-- Löwner sandwich monotonicity for the inverse square root.

If `A` and `B` are operators satisfying `opLe A B` (i.e., `B − A` is PSD in the
quadratic-form sense), then `opLe (σ^(−1/2)·A·σ^(−1/2)) (σ^(−1/2)·B·σ^(−1/2))`.

Proof sketch: Congruence of the semidefinite order under multiplication by a fixed
PSD matrix.  For Hermitian `A, B` with `B − A` PSD and `S := σ^(−1/2)` PSD:
`S·B·S − S·A·S = S·(B−A)·S ≥ 0` (Schur product / PSD congruence).

Reference: standard matrix-analysis fact (Löwner's theorem). -/
theorem inverseSqrt_sandwich_mono {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) {A B : Op n}
    (hAB : opLe A B) :
    opLe (hσ.inverseSqrt * A * hσ.inverseSqrt)
        (hσ.inverseSqrt * B * hσ.inverseSqrt) := by
  intro v
  have hS : hσ.inverseSqrt.IsHermitian := hσ.inverseSqrt_isHermitian
  rw [Quantum.Operators.quadraticForm_sandwich_self_of_isHermitian hS A v,
      Quantum.Operators.quadraticForm_sandwich_self_of_isHermitian hS B v]
  exact hAB (hσ.inverseSqrt.mulVec v)

/-- Feasibility-to-sandwich conversion (key LHL step).

If `ρ ≤_PSD t·σ` (in the `opLe` order), then
`σ^(−1/2)·ρ·σ^(−1/2) ≤_PSD t·I`.

Proof: Apply `inverseSqrt_sandwich_mono` to `h : opLe ρ (t·σ)`, then use
`inverseSqrt_sandwich_eq_one` to simplify
`σ^(−1/2) · (t·σ) · σ^(−1/2) = t · (σ^(−1/2)·σ·σ^(−1/2)) = t · 1`.

This is the step that converts a feasibility constraint `ρ ≤ t·σ` into the bounded
diagonal form `σ^(−1/2)·ρ·σ^(−1/2) ≤ t·I` that the LHL Jensen step requires.

Reference: Tomamichel 2016, Prop 7.1, eq. 7.37–7.38. -/
theorem inverseSqrt_sandwich_of_opLe {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) {ρ : Op n} {t : ℝ}
    (h : opLe ρ (Complex.ofReal t • σ)) :
    opLe (hσ.inverseSqrt * ρ * hσ.inverseSqrt)
        (Complex.ofReal t • (1 : Op n)) := by
  have h1 := hσ.inverseSqrt_sandwich_mono h
  have heq : hσ.inverseSqrt * (Complex.ofReal t • σ) * hσ.inverseSqrt
      = Complex.ofReal t • (1 : Op n) := by
    rw [mul_smul_comm, smul_mul_assoc, hσ.inverseSqrt_sandwich_eq_one]
  rw [heq] at h1
  exact h1

/-!
## The inverse fourth root operator
-/

/-- The inverse fourth root of a positive-definite operator, defined via the
continuous functional calculus as the CFC square root of `hσ.inverseSqrt`.

For `hσ : σ.PosDef`, `hσ.inverseFourthRoot = CFC.sqrt hσ.inverseSqrt = σ^(−1/4)`.

Since `hσ.inverseSqrt` is positive semidefinite, the CFC square root is well-defined
and yields a PSD operator whose square equals `hσ.inverseSqrt = σ^(−1/2)`.

Used in proof bodies of the squared-sandwich α and ε steps in the quantum LHL chain.
Reference: Renner thesis §5.1, Lemma 5.1.3. -/
noncomputable def inverseFourthRoot {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) : Op n :=
  CFC.sqrt hσ.inverseSqrt

/-- The inverse fourth root of a positive-definite operator is positive semidefinite. -/
theorem inverseFourthRoot_posSemidef {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) : hσ.inverseFourthRoot.PosSemidef := by
  unfold inverseFourthRoot
  exact (CFC.sqrt_nonneg hσ.inverseSqrt).posSemidef

/-- The inverse fourth root of a positive-definite operator is Hermitian. -/
theorem inverseFourthRoot_isHermitian {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) : hσ.inverseFourthRoot.IsHermitian :=
  hσ.inverseFourthRoot_posSemidef.isHermitian

/-- The square of the inverse fourth root equals the inverse square root:
`(σ^(−1/4))² = σ^(−1/2)`. -/
theorem inverseFourthRoot_sq {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) :
    hσ.inverseFourthRoot * hσ.inverseFourthRoot = hσ.inverseSqrt :=
  CFC.sqrt_mul_sqrt_self hσ.inverseSqrt hσ.inverseSqrt_posSemidef.nonneg

/-- The inverse fourth root sandwiches `σ^{1/2}` to the identity:
`σ^{−1/4} · σ^{1/2} · σ^{−1/4} = I`.

This is the load-bearing CFC identity used in the squared-sandwich LHL chain.
Proof: `F · CFC.sqrt σ · F` where `F = inverseFourthRoot`. Since `F·F = inverseSqrt`
and `inverseSqrt · CFC.sqrt σ · inverseSqrt = inverseSqrt · inverseSqrt⁻¹ = I`
(as `CFC.sqrt σ = inverseSqrt⁻¹` when `σ = (inverseSqrt)⁻²`), this reduces to the
sandwich identity for `inverseSqrt`. The cleanest route uses commutativity of CFC
operators (both `F` and `CFC.sqrt σ` are functions of `σ` via the spectral theorem,
hence commute) and the chain `F·F·CFC.sqrt σ = inverseSqrt · CFC.sqrt σ = σ⁻¹/² · σ^{1/2} = I`. -/
theorem inverseFourthRoot_sandwich_sigmaSqrt {n : ℕ} {σ : Op n}
    (hσ : σ.PosDef) :
    hσ.inverseFourthRoot * CFC.sqrt σ * hσ.inverseFourthRoot = 1 := by
  have hunit : IsUnit σ := hσ.isUnit
  have hF : hσ.inverseFourthRoot = σ ^ (-(1 / 4) : ℝ) := by
    unfold inverseFourthRoot inverseSqrt
    have h_inv : σ⁻¹ = σ ^ (-1 : ℝ) := by
      simpa using (CFC.rpow_neg_one_eq_inv hunit.unit).symm
    rw [h_inv]
    rw [CFC.sqrt_rpow hunit (by norm_num)]
    rw [CFC.sqrt_rpow hunit (by norm_num)]
    norm_num
  calc hσ.inverseFourthRoot * CFC.sqrt σ * hσ.inverseFourthRoot
      = σ ^ (-(1 / 4) : ℝ) * σ ^ (1 / 2 : ℝ) * σ ^ (-(1 / 4) : ℝ) := by
          rw [hF, CFC.sqrt_eq_rpow]
    _ = σ ^ ((-(1 / 4) : ℝ) + (1 / 2 : ℝ)) * σ ^ (-(1 / 4) : ℝ) := by
          rw [CFC.rpow_add hunit]
    _ = σ ^ (((-(1 / 4) : ℝ) + (1 / 2 : ℝ)) + (-(1 / 4) : ℝ)) := by
          rw [← CFC.rpow_add hunit]
    _ = 1 := by
          norm_num
          exact CFC.rpow_zero σ

end Matrix.PosDef

/-!
## σ-Weighted Operator Cauchy–Schwarz — helper lemmas
-/

namespace Quantum.Metrics

/-- **Connection lemma**: `traceNorm X = Re(Tr(√(X†·X)))`. -/
lemma traceNorm_eq_re_trace_cfcSqrt_conjTranspose_mul {d : ℕ} [NeZero d]
    (X : Op d) :
    Quantum.Metrics.traceNorm X = (CFC.sqrt (X.conjTranspose * X)).trace.re := by
  have hXHX_psd : (X.conjTranspose * X).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self X
  have hP_psd : (CFC.sqrt (X.conjTranspose * X)).PosSemidef :=
    (CFC.sqrt_nonneg (X.conjTranspose * X)).posSemidef
  have hP_sq : CFC.sqrt (X.conjTranspose * X) * CFC.sqrt (X.conjTranspose * X)
      = X.conjTranspose * X :=
    CFC.sqrt_mul_sqrt_self (X.conjTranspose * X) (ha := hXHX_psd.nonneg)
  -- Step 1: traceNorm (CFC.sqrt (X†X)) = traceNorm X (same Gram X†X)
  have h1 : Quantum.Metrics.traceNorm (CFC.sqrt (X.conjTranspose * X))
      = Quantum.Metrics.traceNorm X := by
    apply Quantum.Metrics.TraceNormHoelder.traceNorm_eq_of_conjTranspose_mul_self_eq
    rw [hP_psd.isHermitian.eq]
    exact hP_sq
  -- Step 2: traceNorm of PSD = trace.re
  have h2 : Quantum.Metrics.traceNorm (CFC.sqrt (X.conjTranspose * X))
      = (CFC.sqrt (X.conjTranspose * X)).trace.re := by
    rw [Quantum.Metrics.traceNorm_hermitian_eq _ hP_psd.isHermitian]
    exact Quantum.Metrics.traceNormHermitian_of_posSemidef _ hP_psd
  linarith

/-- Frobenius norm squared: `Re Tr(A·A†) = Σᵢⱼ |Aᵢⱼ|²`. -/
private lemma trace_mul_conjTranspose_re_eq_sum_norm_sq {d : ℕ}
    (A : Op d) :
    (A * A.conjTranspose).trace.re = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  congr 1; ext i
  rw [Complex.re_sum]
  congr 1; ext j
  have h : A i j * star (A i j) = ((Complex.normSq (A i j) : ℝ) : ℂ) := by
    rw [show star (A i j) = (starRingEnd ℂ) (A i j) from rfl, Complex.mul_conj]
  rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- Frobenius norm squared (other side): `Re Tr(A†·A) = Σᵢⱼ |Aⱼᵢ|²`. -/
private lemma trace_conjTranspose_mul_re_eq_sum_norm_sq {d : ℕ}
    (A : Op d) :
    (A.conjTranspose * A).trace.re = ∑ i, ∑ j, ‖A j i‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Complex.re_sum]
  congr 1; ext i
  rw [Complex.re_sum]
  congr 1; ext j
  have h : A j i * star (A j i) = ((Complex.normSq (A j i) : ℝ) : ℂ) := by
    rw [show star (A j i) = (starRingEnd ℂ) (A j i) from rfl, Complex.mul_conj]
  rw [mul_comm (star (A j i)) (A j i), h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **Hilbert–Schmidt Cauchy–Schwarz** (trace pairing form):
`|Tr(A · B)|² ≤ Re Tr(A · A†) · Re Tr(B† · B)`. -/
lemma norm_trace_mul_sq_le_trace_mul_trace_conjTranspose {d : ℕ}
    (A B : Op d) :
    ‖(A * B).trace‖ ^ 2
      ≤ (A * A.conjTranspose).trace.re * (B.conjTranspose * B).trace.re := by
  -- Express `(A * B).trace` as `∑ᵢⱼ Aᵢⱼ · Bⱼᵢ`
  have hexpand : (A * B).trace = ∑ p : Fin d × Fin d, A p.1 p.2 * B p.2 p.1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fintype.sum_prod_type]
  rw [hexpand]
  -- Triangle inequality + |a·b| = |a|·|b|
  have htri : ‖∑ p : Fin d × Fin d, A p.1 p.2 * B p.2 p.1‖
      ≤ ∑ p : Fin d × Fin d, ‖A p.1 p.2‖ * ‖B p.2 p.1‖ := by
    calc ‖∑ p : Fin d × Fin d, A p.1 p.2 * B p.2 p.1‖
        ≤ ∑ p : Fin d × Fin d, ‖A p.1 p.2 * B p.2 p.1‖ := norm_sum_le _ _
      _ = ∑ p : Fin d × Fin d, ‖A p.1 p.2‖ * ‖B p.2 p.1‖ := by
          simp_rw [norm_mul]
  -- Real Cauchy–Schwarz on the product index set
  have hCS : (∑ p : Fin d × Fin d, ‖A p.1 p.2‖ * ‖B p.2 p.1‖) ^ 2
      ≤ (∑ p : Fin d × Fin d, ‖A p.1 p.2‖ ^ 2)
          * (∑ p : Fin d × Fin d, ‖B p.2 p.1‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  -- Identify the two Frobenius sums with the traces
  have hA_sum : ∑ p : Fin d × Fin d, ‖A p.1 p.2‖ ^ 2 = (A * A.conjTranspose).trace.re := by
    rw [Fintype.sum_prod_type, trace_mul_conjTranspose_re_eq_sum_norm_sq]
  have hB_sum : ∑ p : Fin d × Fin d, ‖B p.2 p.1‖ ^ 2 = (B.conjTranspose * B).trace.re := by
    rw [trace_conjTranspose_mul_re_eq_sum_norm_sq, Fintype.sum_prod_type,
        Finset.sum_comm]
  have hsum_nonneg : 0 ≤ ∑ p : Fin d × Fin d, ‖A p.1 p.2‖ * ‖B p.2 p.1‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ‖∑ p : Fin d × Fin d, A p.1 p.2 * B p.2 p.1‖ ^ 2
      ≤ (∑ p : Fin d × Fin d, ‖A p.1 p.2‖ * ‖B p.2 p.1‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ (∑ p : Fin d × Fin d, ‖A p.1 p.2‖ ^ 2)
          * (∑ p : Fin d × Fin d, ‖B p.2 p.1‖ ^ 2) := hCS
    _ = (A * A.conjTranspose).trace.re * (B.conjTranspose * B).trace.re := by
        rw [hA_sum, hB_sum]

end Quantum.Metrics

/-!
## σ-Weighted Operator Cauchy–Schwarz
-/

/-- σ-weighted operator Cauchy–Schwarz (trace-norm form).

For a positive-definite operator `σ` and an arbitrary operator `D`,

  `‖D‖₁² ≤ σ.trace.re · tr(σ^(−1/2) · D · D† · σ^(−1/2)).re`

where `‖·‖₁` is the Schatten 1-norm (`Quantum.Metrics.traceNorm`).

This is the key Cauchy–Schwarz inequality used in the LHL proof (Tomamichel 2016,
Prop 7.1, eq. 7.39).  The inequality follows from the Cauchy–Schwarz inequality
for Hilbert–Schmidt inner products after the substitution
`A = σ^(1/2) · (σ^(−1/2) · D · σ^(−1/2)) · σ^(1/2)`.

`[NeZero n]` is required for the `traceNorm` definition. -/
theorem traceNorm_sq_le_sandwich_trace {n : ℕ} [NeZero n]
    {σ : Op n} (hσ : σ.PosDef)
    (D : Op n) :
    Quantum.Metrics.traceNorm D ^ 2 ≤
      σ.trace.re *
        (hσ.inverseSqrt * D * D.conjTranspose * hσ.inverseSqrt).trace.re := by
  set S := hσ.inverseSqrt with hS_def
  have hS_herm : S.conjTranspose = S := hσ.inverseSqrt_isHermitian.eq
  have hS_sq : S * S = σ⁻¹ := hσ.inverseSqrt_sq
  have hS_sandwich : S * σ * S = 1 := hσ.inverseSqrt_sandwich_eq_one
  -- Step 1: polar unitary for D†
  obtain ⟨U, hU⟩ :=
    Quantum.Metrics.PolarUnitary.exists_unitary_trace_mul_eq_trace_cfcSqrt_mul_conjTranspose
      D.conjTranspose
  rw [show D.conjTranspose.conjTranspose = D from Matrix.conjTranspose_conjTranspose D] at hU
  -- hU : (U.toOp * D.conjTranspose).trace = (CFC.sqrt (D.conjTranspose * D)).trace
  -- Step 2: traceNorm D = (U · D†).trace.re.
  have h_norm_eq : Quantum.Metrics.traceNorm D = (U.toOp * D.conjTranspose).trace.re := by
    rw [hU, ← Quantum.Metrics.traceNorm_eq_re_trace_cfcSqrt_conjTranspose_mul D]
  -- Step 3: (U · D†).trace rewrites to ((σ S U) * (D† S)).trace.
  have hU_uni_rl : U.toOp * U.toOp.conjTranspose = 1 := U.unitary_right
  have hU_uni_lr : U.toOp.conjTranspose * U.toOp = 1 := U.unitary_left
  have h_trace_rewrite :
      (U.toOp * D.conjTranspose).trace
        = ((σ * S * U.toOp) * (D.conjTranspose * S)).trace := by
    -- (U * D†).trace = (U * D† * 1).trace = (U * D† * (S σ S)).trace
    -- = ((σ S) * (U * D† * S)).trace [trace cyclicity]
    -- = (σ S U D† S).trace = ((σ S U) * (D† S)).trace
    have h1 : U.toOp * D.conjTranspose = U.toOp * D.conjTranspose * (S * σ * S) := by
      rw [hS_sandwich, Matrix.mul_one]
    calc (U.toOp * D.conjTranspose).trace
        = (U.toOp * D.conjTranspose * (S * σ * S)).trace := by rw [← h1]
      _ = ((σ * S) * (U.toOp * D.conjTranspose * S)).trace := by
          rw [show U.toOp * D.conjTranspose * (S * σ * S)
                = (U.toOp * D.conjTranspose * S) * (σ * S) from by
                simp [Matrix.mul_assoc]]
          rw [Matrix.trace_mul_comm]
      _ = (σ * S * U.toOp * D.conjTranspose * S).trace := by
          rw [show (σ * S) * (U.toOp * D.conjTranspose * S)
                = σ * S * U.toOp * D.conjTranspose * S from by
                simp [Matrix.mul_assoc]]
      _ = ((σ * S * U.toOp) * (D.conjTranspose * S)).trace := by
          rw [show σ * S * U.toOp * D.conjTranspose * S
                = (σ * S * U.toOp) * (D.conjTranspose * S) from by
                simp [Matrix.mul_assoc]]
  -- Step 4: apply HS-CS.
  set A := σ * S * U.toOp with hA_def
  set B := D.conjTranspose * S with hB_def
  have hCS : ‖(A * B).trace‖ ^ 2
      ≤ (A * A.conjTranspose).trace.re * (B.conjTranspose * B).trace.re :=
    Quantum.Metrics.norm_trace_mul_sq_le_trace_mul_trace_conjTranspose A B
  -- Step 5: Compute Tr(A · A†) = Tr(σ).
  have hAA_eq_sigma :
      (A * A.conjTranspose).trace = σ.trace := by
    have hA_dag : A.conjTranspose = U.toOp.conjTranspose * S * σ := by
      simp [hA_def, Matrix.conjTranspose_mul, hS_herm, hσ.1.eq, Matrix.mul_assoc]
    have hu_det : IsUnit σ.det := (Matrix.isUnit_iff_isUnit_det σ).mp hσ.isUnit
    have hmul_inv : σ * σ⁻¹ = 1 := Matrix.mul_nonsing_inv σ hu_det
    calc (A * A.conjTranspose).trace
        = (σ * S * U.toOp * (U.toOp.conjTranspose * S * σ)).trace := by
            rw [hA_def, hA_dag]
      _ = (σ * S * (U.toOp * U.toOp.conjTranspose) * S * σ).trace := by
            congr 1; simp [Matrix.mul_assoc]
      _ = (σ * S * 1 * S * σ).trace := by rw [hU_uni_rl]
      _ = (σ * (S * S) * σ).trace := by
            rw [Matrix.mul_one]; congr 1; simp [Matrix.mul_assoc]
      _ = (σ * σ⁻¹ * σ).trace := by rw [hS_sq]
      _ = (1 * σ).trace := by rw [hmul_inv]
      _ = σ.trace := by rw [Matrix.one_mul]
  -- Step 6: Compute Tr(B† · B) = Tr(S D D† S).
  have hBB_eq_sandwich :
      (B.conjTranspose * B).trace = (S * D * D.conjTranspose * S).trace := by
    have hB_dag : B.conjTranspose = S * D := by
      simp [hB_def, Matrix.conjTranspose_mul, hS_herm, Matrix.conjTranspose_conjTranspose]
    calc (B.conjTranspose * B).trace
        = (S * D * (D.conjTranspose * S)).trace := by rw [hB_dag, hB_def]
      _ = (S * D * D.conjTranspose * S).trace := by
            congr 1; simp [Matrix.mul_assoc]
  -- Step 7: Chain together.
  -- traceNorm² = ((U·D†).trace.re)² ≤ ‖(U·D†).trace‖² = ‖(A·B).trace‖² ≤ Tr(σ).re · Tr(SDD†S).re
  have h_re_sq_le_norm_sq :
      ((U.toOp * D.conjTranspose).trace.re) ^ 2
        ≤ ‖(U.toOp * D.conjTranspose).trace‖ ^ 2 := by
    have habs := Complex.abs_re_le_norm (U.toOp * D.conjTranspose).trace
    -- habs : |z.re| ≤ ‖z‖
    have h_sq : ((U.toOp * D.conjTranspose).trace.re) ^ 2
        = |((U.toOp * D.conjTranspose).trace.re)| ^ 2 := by rw [sq_abs]
    rw [h_sq]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc Quantum.Metrics.traceNorm D ^ 2
      = ((U.toOp * D.conjTranspose).trace.re) ^ 2 := by rw [h_norm_eq]
    _ ≤ ‖(U.toOp * D.conjTranspose).trace‖ ^ 2 := h_re_sq_le_norm_sq
    _ = ‖(A * B).trace‖ ^ 2 := by rw [h_trace_rewrite]
    _ ≤ (A * A.conjTranspose).trace.re * (B.conjTranspose * B).trace.re := hCS
    _ = σ.trace.re * (S * D * D.conjTranspose * S).trace.re := by
        rw [hAA_eq_sigma, hBB_eq_sandwich]

end -- noncomputable section
