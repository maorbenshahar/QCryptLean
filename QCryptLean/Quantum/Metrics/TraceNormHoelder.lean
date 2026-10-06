import QCryptLean.Quantum.Metrics.TraceNormDilation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Trace Norm: Unitary Invariance and Hölder Inequality

## Main results

- `traceNorm_eq_of_conjTranspose_mul_self_eq`: If A†A = B†B then traceNorm A = traceNorm B.
- `Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq`: scalar multiplication scales trace norm by
complex modulus
- `traceNorm_unitary_mul_left`: ‖U * A‖₁ = ‖A‖₁ for unitary U (U†U = 1).
- `traceNorm_mul_unitary_right`: ‖A * U‖₁ = ‖A‖₁ for unitary U (U†U = UU† = 1).
- `traceNorm_mul_le_opNorm_mul_traceNorm`: Left Hölder: ‖A * B‖₁ ≤ ‖A‖_op * ‖B‖₁.
- `traceNorm_mul_le_traceNorm_mul_opNorm`: Right Hölder: ‖X * B‖₁ ≤ ‖X‖₁ * ‖B‖_op.

## References

- Bhatia (1997) "Matrix Analysis", Theorem IV.2.5
- Watrous (2018) "Theory of Quantum Information", Section 1.2
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder Kronecker

noncomputable section

namespace Quantum.Metrics.TraceNormHoelder

/-- If A†A = B†B then traceNorm A = traceNorm B.
    This follows because the eigenvalues of A†A determine the singular values,
    and equal A†A implies equal singular values. -/
lemma traceNorm_eq_of_conjTranspose_mul_self_eq {d : ℕ} [NeZero d]
    (A B : Op d) (h : A.conjTranspose * A = B.conjTranspose * B) :
    traceNorm A = traceNorm B := by
  unfold traceNorm
  have hAA : (A.conjTranspose * A).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have hBB : (B.conjTranspose * B).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
  have h_eig : hAA.eigenvalues = hBB.eigenvalues := by
    rw [IsHermitian.eigenvalues_eq_eigenvalues_iff, h]
  simp_rw [h_eig]

/-- Eigenvalues of `(c • X)†(c • X)` scale by `‖c‖²`. -/
private theorem eigenvalues_smul_conjTranspose_mul {n : ℕ} [NeZero n]
    (c : ℂ) (X : Op n)
    (hcXcX : ((c • X).conjTranspose * (c • X)).IsHermitian)
    (hXX : (X.conjTranspose * X).IsHermitian) :
    Multiset.map hcXcX.eigenvalues Finset.univ.val =
      Multiset.map (fun i => ‖c‖ ^ 2 * hXX.eigenvalues i) Finset.univ.val := by
  have h_mat_c : (c • X).conjTranspose * (c • X) = (star c * c) • (X.conjTranspose * X) := by
    rw [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_star_mul : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [show star c = starRingEnd ℂ c from rfl, Complex.conj_mul']
    push_cast
    ring
  have h_mat_r : (c • X).conjTranspose * (c • X) =
      ((‖c‖ ^ 2 : ℝ) : ℂ) • (X.conjTranspose * X) := by
    rw [h_mat_c, h_star_mul]
  have h_smul_eq : ((‖c‖ ^ 2 : ℝ) : ℂ) • (X.conjTranspose * X) =
      (‖c‖ ^ 2 : ℝ) • (X.conjTranspose * X) :=
    (algebraMap_smul ℂ (‖c‖ ^ 2 : ℝ) (X.conjTranspose * X)).symm
  have h_mat2 : (c • X).conjTranspose * (c • X) =
      (‖c‖ ^ 2 : ℝ) • (X.conjTranspose * X) := by
    rw [h_mat_r, h_smul_eq]
  have h_cfc : (‖c‖ ^ 2 : ℝ) • (X.conjTranspose * X) =
      cfc (fun x : ℝ => ‖c‖ ^ 2 * x) (X.conjTranspose * X) := by
    rw [← cfc_const_mul_id (‖c‖ ^ 2) (X.conjTranspose * X) (by exact hXX)]
  have h_combined := h_mat2.trans h_cfc
  have hcXcX' : (cfc (fun x : ℝ => ‖c‖ ^ 2 * x) (X.conjTranspose * X)).IsHermitian :=
    h_combined ▸ hcXcX
  have h_eig : hcXcX.eigenvalues = hcXcX'.eigenvalues :=
    (hcXcX.eigenvalues_eq_eigenvalues_iff hcXcX').mpr
      (congr_arg Matrix.charpoly h_combined)
  have h_roots := hcXcX'.roots_charpoly_eq_eigenvalues
  rw [hXX.charpoly_cfc_eq (fun x => ‖c‖ ^ 2 * x)] at h_roots
  have h_prod_roots :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (↑(‖c‖ ^ 2 * hXX.eigenvalues i) : ℂ))).roots =
      Multiset.map (fun i => (↑(‖c‖ ^ 2 * hXX.eigenvalues i) : ℂ)) Finset.univ.val := by
    rw [Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · apply Mathlib.Meta.Positivity.prod_ne_zero
      intro i _
      exact Polynomial.X_sub_C_ne_zero _
  rw [h_eig]
  apply Multiset.map_injective Complex.ofReal_injective
  simp only [Multiset.map_map]
  exact h_roots.symm.trans h_prod_roots

/-- Trace norm scales with complex norm: `‖c • X‖₁ = ‖c‖ · ‖X‖₁`. -/
theorem traceNorm_smul_eq {n : ℕ} [NeZero n]
    (c : ℂ) (X : Op n) :
    traceNorm (c • X) = ‖c‖ * traceNorm X := by
  by_cases hc : c = 0
  · subst hc
    have hzero : traceNorm (0 : Op n) = 0 := by
      unfold traceNorm
      apply Finset.sum_eq_zero
      intro i _
      suffices h : ∀ (hAA : (0 : Op n).IsHermitian), hAA.eigenvalues i = 0 by
        simp [h]
      intro hAA
      have := hAA.eigenvalues_eq i
      simp only [Matrix.zero_mulVec, dotProduct_zero, map_zero] at this
      exact_mod_cast this
    simp [hzero]
  · simp only [traceNorm]
    set hcXcX : ((c • X).conjTranspose * (c • X)).IsHermitian := by
      rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
    set hXX : (X.conjTranspose * X).IsHermitian := by
      rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]
    have h_ms := eigenvalues_smul_conjTranspose_mul c X hcXcX hXX
    have h_sqrt_ms := congr_arg (Multiset.map Real.sqrt) h_ms
    rw [Multiset.map_map, Multiset.map_map] at h_sqrt_ms
    have h_sum := congr_arg Multiset.sum h_sqrt_ms
    rw [Finset.sum_map_val, Finset.sum_map_val] at h_sum
    simp only [Function.comp_apply] at h_sum
    rw [h_sum]
    rw [Finset.mul_sum]
    congr 1
    funext i
    rw [Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq (norm_nonneg c)]

/-- **Left unitary invariance of trace norm**: ‖U * A‖₁ = ‖A‖₁ when U†U = 1.

    Proof: (UA)†(UA) = A†U†UA = A†A. -/
lemma traceNorm_unitary_mul_left {d : ℕ} [NeZero d]
    (U A : Op d) (hU : U.conjTranspose * U = 1) :
    traceNorm (U * A) = traceNorm A := by
  apply traceNorm_eq_of_conjTranspose_mul_self_eq
  rw [conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc U.conjTranspose U A, hU, Matrix.one_mul]

/-- **Right unitary invariance of trace norm**: ‖A * U‖₁ = ‖A‖₁ when U is unitary.

    Proof: ‖AU‖₁ = ‖(AU)†‖₁ = ‖U†A†‖₁ = ‖A†‖₁ = ‖A‖₁.
    Uses left invariance on U† (which needs UU† = 1) and conjTranspose invariance. -/
lemma traceNorm_mul_unitary_right {d : ℕ} [NeZero d]
    (A U : Op d) (_hUl : U.conjTranspose * U = 1) (hUr : U * U.conjTranspose = 1) :
    traceNorm (A * U) = traceNorm A := by
  calc traceNorm (A * U)
      = traceNorm (A * U).conjTranspose := (traceNorm_conjTranspose _).symm
    _ = traceNorm (U.conjTranspose * A.conjTranspose) := by
        rw [conjTranspose_mul]
    _ = traceNorm A.conjTranspose := by
        apply traceNorm_unitary_mul_left
        rw [conjTranspose_conjTranspose, hUr]
    _ = traceNorm A := traceNorm_conjTranspose A

-- Use the L2 operator norm (spectral norm) on matrices
-- This gives NormedRing, CStarRing, NormedAlgebra, etc.
open scoped Matrix.Norms.L2Operator

/-- For PSD matrices, trace norm equals the real part of the trace.
    (Re-proved here to avoid a DiamondNorm dependency.) -/
private lemma traceNorm_posSemidef_eq_trace' {d : ℕ} [NeZero d]
    (P : Op d) (hP : P.PosSemidef) :
    traceNorm P = P.trace.re := by
  rw [traceNorm_hermitian_eq P hP.1]
  exact Quantum.Metrics.traceNormHermitian_of_posSemidef P hP

/-- The PSD square root of X†X has trace norm equal to traceNorm X.
    Key identity: traceNorm(√(X†X)) = traceNorm(X). -/
private lemma traceNorm_sqrt_conjTranspose_mul_self' {d : ℕ} [NeZero d] (X : Op d) :
    traceNorm (CFC.sqrt (X.conjTranspose * X)) = traceNorm X := by
  apply traceNorm_eq_of_conjTranspose_mul_self_eq
  have hXHX_nn : (0 : Op d) ≤ X.conjTranspose * X :=
    (posSemidef_conjTranspose_mul_self X).nonneg
  have hP_psd : (CFC.sqrt (X.conjTranspose * X)).PosSemidef :=
    (CFC.sqrt_nonneg (X.conjTranspose * X)).posSemidef
  rw [hP_psd.isHermitian.eq]
  exact CFC.sqrt_mul_sqrt_self (X.conjTranspose * X) (ha := hXHX_nn)

/-- Connection: traceNorm X = (trace (CFC.sqrt (X†X))).re. This combines
    traceNorm = trace for PSD and the sqrt identity. -/
private lemma traceNorm_eq_trace_sqrt {d : ℕ} [NeZero d] (X : Op d) :
    traceNorm X = (Matrix.trace (CFC.sqrt (X.conjTranspose * X))).re := by
  rw [← traceNorm_sqrt_conjTranspose_mul_self' X]
  have hP_psd : (CFC.sqrt (X.conjTranspose * X)).PosSemidef :=
    (CFC.sqrt_nonneg (X.conjTranspose * X)).posSemidef
  exact traceNorm_posSemidef_eq_trace' _ hP_psd

/-- Square roots commute with conjugation by a rectangular isometry. -/
lemma cfc_sqrt_isometry_conj {m n : ℕ}
    (V : Matrix (Fin m) (Fin n) ℂ) (B : Op n)
    (hV : V.conjTranspose * V = 1) (hB : B.PosSemidef) :
    CFC.sqrt (V * B * V.conjTranspose) =
      V * CFC.sqrt B * V.conjTranspose := by
  refine CFC.sqrt_unique ?_ ?_
  · have hSsq : CFC.sqrt B * CFC.sqrt B = B :=
      CFC.sqrt_mul_sqrt_self B hB.nonneg
    calc
      (V * CFC.sqrt B * V.conjTranspose) *
          (V * CFC.sqrt B * V.conjTranspose)
          = V * CFC.sqrt B * (V.conjTranspose * V) * CFC.sqrt B *
              V.conjTranspose := by
              simp only [Matrix.mul_assoc]
      _ = V * CFC.sqrt B * (1 : Op n) * CFC.sqrt B *
              V.conjTranspose := by rw [hV]
      _ = V * (CFC.sqrt B * CFC.sqrt B) * V.conjTranspose := by
              simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = V * B * V.conjTranspose := by rw [hSsq]
  · rw [Matrix.nonneg_iff_posSemidef]
    exact ((CFC.sqrt_nonneg B).posSemidef).mul_mul_conjTranspose_same V

/-- Trace-norm invariance under conjugation by a rectangular isometry. -/
lemma traceNorm_isometry_mul_left {m n : ℕ} [NeZero m] [NeZero n]
    (V : Matrix (Fin m) (Fin n) ℂ) (A : Op n)
    (hV : V.conjTranspose * V = 1) :
    traceNorm (V * A * V.conjTranspose) = traceNorm A := by
  have hB : (A.conjTranspose * A).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self A
  have hgram :
      (V * A * V.conjTranspose).conjTranspose *
          (V * A * V.conjTranspose) =
        V * (A.conjTranspose * A) * V.conjTranspose := by
    have hct :
        (V * A * V.conjTranspose).conjTranspose =
          V * A.conjTranspose * V.conjTranspose := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    calc
      (V * A * V.conjTranspose).conjTranspose *
          (V * A * V.conjTranspose)
          = (V * A.conjTranspose * V.conjTranspose) *
              (V * A * V.conjTranspose) := by rw [hct]
      _ = V * A.conjTranspose * (V.conjTranspose * V) * A *
              V.conjTranspose := by
              simp only [Matrix.mul_assoc]
      _ = V * A.conjTranspose * (1 : Op n) * A *
              V.conjTranspose := by rw [hV]
      _ = V * (A.conjTranspose * A) * V.conjTranspose := by
              simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [traceNorm_eq_trace_sqrt (V * A * V.conjTranspose),
    traceNorm_eq_trace_sqrt A]
  rw [hgram, cfc_sqrt_isometry_conj V (A.conjTranspose * A) hV hB]
  exact congrArg Complex.re <| by
    calc
      (V * CFC.sqrt (A.conjTranspose * A) * V.conjTranspose).trace
          = (V.conjTranspose * (V * CFC.sqrt (A.conjTranspose * A))).trace := by
              rw [Matrix.trace_mul_comm]
      _ = ((V.conjTranspose * V) * CFC.sqrt (A.conjTranspose * A)).trace := by
              rw [← Matrix.mul_assoc]
      _ = (1 * CFC.sqrt (A.conjTranspose * A)).trace := by rw [hV]
      _ = (CFC.sqrt (A.conjTranspose * A)).trace := by rw [Matrix.one_mul]

/-- The rectangular tensor `id ⊗ V` is an isometry whenever `V` is an isometry. -/
lemma idTensorRect_isometry {c m n : ℕ} [NeZero c] [NeZero m] [NeZero n]
    (V : Matrix (Fin m) (Fin n) ℂ)
    (hV : V.conjTranspose * V = (1 : Op n)) :
    let W : Matrix (Fin (c * m)) (Fin (c * n)) ℂ :=
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((1 : Op c) ⊗ₖ V)
    W.conjTranspose * W = (1 : Op (c * n)) := by
  dsimp [Matrix.reindex]
  rw [Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.conjTranspose_one, Matrix.one_mul, hV]
  rw [Matrix.one_kronecker_one]
  exact Matrix.submatrix_one_equiv finProdFinEquiv.symm

/-- **Loewner comparison**: B†A†AB ≤ ‖A‖² • B†B.

    Proof: (‖A‖²•B†B - B†A†AB) is PSD because for all v:
    v†(‖A‖²B†B - B†A†AB)v = ‖A‖²‖Bv‖² - ‖ABv‖² ≥ 0. -/
private lemma loewner_conjTranspose_mul_sq {d : ℕ} [NeZero d]
    (A B : Op d) :
    B.conjTranspose * A.conjTranspose * A * B ≤
      (‖A‖ ^ 2 : ℝ) • (B.conjTranspose * B) := by
  -- Key: ‖A‖²I - A†A is PSD, so B†(‖A‖²I - A†A)B is PSD
  -- The PSD property of ‖A‖²I - A†A comes from operator norm bound
  rw [Matrix.le_iff]
  -- Need: ((‖A‖²) • (B†B) - B†A†AB).PosSemidef
  -- = B†(‖A‖²I - A†A)B is PSD
  have h_eq : (‖A‖ ^ 2 : ℝ) • (B.conjTranspose * B) -
      B.conjTranspose * A.conjTranspose * A * B =
      B.conjTranspose * ((‖A‖ ^ 2 : ℝ) • (1 : Op d) - A.conjTranspose * A) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    · rw [mul_smul_comm, smul_mul_assoc, Matrix.mul_one]
    · simp only [Matrix.mul_assoc]
  rw [h_eq]
  apply Matrix.PosSemidef.conjTranspose_mul_mul_same
  -- Show (‖A‖² • I - A†A).PosSemidef
  -- Proof: ‖A‖² ‖v‖² - ‖Av‖² ≥ 0 for all v, from operator norm bound
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · -- Hermitian: (‖A‖² • I - A†A)† = ‖A‖² • I† - (A†A)† = ‖A‖² • I - A†A
    have h1 : (‖A‖ ^ 2 • (1 : Op d)).IsHermitian := by
      rw [Matrix.IsHermitian, conjTranspose_smul, isHermitian_one.eq]
      simp
    exact h1.sub (isHermitian_conjTranspose_mul_self A)
  · -- Inner product condition: 0 ≤ v†(‖A‖²I - A†A)v
    -- From the C*-algebra identity: star a * a ≤ ‖a‖² • 1
    intro v
    -- We need CStarAlgebra + StarOrderedRing for the C* bound
    -- The scoped instances give CStarRing + NormedAlgebra, and we manually
    -- build CStarAlgebra (which also requires StarOrderedRing for the bound).
    letI : CStarAlgebra (Op d) := { }
    have h_le : star A * A ≤ algebraMap ℝ _ (‖A‖ ^ 2) :=
      CStarAlgebra.star_mul_le_algebraMap_norm_sq
    have h_le2 : Aᴴ * A ≤ ‖A‖ ^ 2 • (1 : Op d) := by
      rwa [star_eq_conjTranspose, Algebra.algebraMap_eq_smul_one] at h_le
    have h_psd := Matrix.le_iff.mp h_le2
    exact h_psd.dotProduct_mulVec_nonneg v

/-- Trace monotonicity: if C ≤ D in Loewner order, then trace(C).re ≤ trace(D).re. -/
private lemma trace_re_le_of_le {d : ℕ}
    (C D : Op d) (h : C ≤ D) :
    C.trace.re ≤ D.trace.re := by
  have h_psd : (D - C).PosSemidef := Matrix.le_iff.mp h
  have h_nn := h_psd.trace_nonneg
  rw [Matrix.trace_sub] at h_nn
  have := (Complex.le_def.mp h_nn).1
  simp only [Complex.sub_re, Complex.zero_re] at this
  linarith

/-- CFC.sqrt of a scalar multiple: CFC.sqrt(c • M) = √c • CFC.sqrt(M)
    for c ≥ 0 and M PSD. -/
private lemma sqrt_smul_eq {d : ℕ} [NeZero d]
    (c : ℝ) (hc : 0 ≤ c)
    (M : Op d) (hM : (0 : Op d) ≤ M) :
    CFC.sqrt (c • M) = Real.sqrt c • CFC.sqrt M := by
  apply CFC.sqrt_unique
  · -- (√c • CFC.sqrt M) * (√c • CFC.sqrt M) = c • M
    simp only [smul_mul_smul_comm, CFC.sqrt_mul_sqrt_self M hM]
    rw [show Real.sqrt c * Real.sqrt c = (c : ℝ) from by
      rw [← Real.sqrt_mul hc, Real.sqrt_mul_self hc]]
  · exact smul_nonneg (by positivity) (CFC.sqrt_nonneg M)

/-- **Trace norm Holder inequality**: traceNorm(A * B) ≤ opNorm(A) * traceNorm(B).

    Here the operator norm is the l2 operator norm (spectral norm, largest singular value).

    **Proof sketch** (standard linear algebra):
    1. `B†A†AB ≤ ‖A‖² • B†B` in the Loewner order (from `‖Av‖ ≤ ‖A‖ * ‖v‖`).
    2. By CFC.sqrt monotonicity: `√(B†A†AB) ≤ √(‖A‖² • B†B)`.
    3. CFC.sqrt of scalar: `√(‖A‖² • B†B) = ‖A‖ • √(B†B)`.
    4. Trace monotonicity + linearity: `Tr(√(B†A†AB)).re ≤ ‖A‖ * Tr(√(B†B)).re`.
    5. Since `traceNorm(X) = Tr(√(X†X)).re`, this gives `traceNorm(AB) ≤ ‖A‖ * traceNorm(B)`. -/
lemma traceNorm_mul_le_opNorm_mul_traceNorm {d : ℕ} [NeZero d]
    (A B : Op d) :
    traceNorm (A * B) ≤ ‖A‖ * traceNorm B := by
  -- Step 1: rewrite traceNorm as trace of sqrt
  rw [traceNorm_eq_trace_sqrt (A * B), traceNorm_eq_trace_sqrt B]
  -- Step 2: rewrite (AB)†(AB) = B†A†AB
  have hAB : (A * B).conjTranspose * (A * B) = B.conjTranspose * A.conjTranspose * A * B := by
    simp [conjTranspose_mul, Matrix.mul_assoc]
  rw [hAB]
  -- Step 3: Loewner bound B†A†AB ≤ ‖A‖² • B†B
  have h_loewner := loewner_conjTranspose_mul_sq A B
  -- Step 4: CFC.sqrt monotonicity (needs CStarAlgebra instance)
  letI : CStarAlgebra (Op d) := { }
  have h_sqrt_le := CFC.sqrt_le_sqrt _ _ h_loewner
  -- Step 5: CFC.sqrt of scalar multiple
  have h_nn_BB : (0 : Op d) ≤ B.conjTranspose * B := (posSemidef_conjTranspose_mul_self B).nonneg
  have h_sqrt_smul := sqrt_smul_eq (‖A‖ ^ 2) (sq_nonneg _) _ h_nn_BB
  -- Step 6: trace monotonicity + simplify
  have h_trace_le : (CFC.sqrt (B.conjTranspose * A.conjTranspose * A * B)).trace.re ≤
      (CFC.sqrt ((‖A‖ ^ 2 : ℝ) • (B.conjTranspose * B))).trace.re :=
    trace_re_le_of_le _ _ h_sqrt_le
  rw [h_sqrt_smul, Matrix.trace_smul] at h_trace_le
  simp only [Complex.real_smul] at h_trace_le
  rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re] at h_trace_le
  ring_nf at h_trace_le
  rw [Real.sqrt_sq (norm_nonneg A)] at h_trace_le
  linarith

/-- **Right Hölder inequality**: traceNorm(X * B) ≤ traceNorm(X) * ‖B‖.
    Proved from the left Hölder via conjugate transpose. -/
lemma traceNorm_mul_le_traceNorm_mul_opNorm {d : ℕ} [NeZero d]
    (X B : Op d) :
    traceNorm (X * B) ≤ traceNorm X * ‖B‖ := by
  calc traceNorm (X * B)
      = traceNorm (X * B).conjTranspose := (traceNorm_conjTranspose _).symm
    _ = traceNorm (B.conjTranspose * X.conjTranspose) := by
        rw [conjTranspose_mul]
    _ ≤ ‖B.conjTranspose‖ * traceNorm X.conjTranspose :=
        traceNorm_mul_le_opNorm_mul_traceNorm _ _
    _ = ‖B‖ * traceNorm X := by
        rw [Matrix.l2_opNorm_conjTranspose, traceNorm_conjTranspose]
    _ = traceNorm X * ‖B‖ := mul_comm _ _

end Quantum.Metrics.TraceNormHoelder

namespace Quantum.Metrics

end Quantum.Metrics
