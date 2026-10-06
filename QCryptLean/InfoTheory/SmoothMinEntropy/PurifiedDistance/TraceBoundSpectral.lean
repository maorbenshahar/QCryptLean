import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.TraceBoundHelpers
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral expansion of Hermitian operators as a sum of rank-1 outer products

We lift the "pure base case" `traceNorm_pure_base_case` to general Hermitian
PSD operators via the spectral decomposition. The module supplies the
algebraic step `M = ∑ i, λ_i • |u_i⟩⟨u_i|`, its corollary
`M − P*M*P = ∑ i, λ_i • (|u_i⟩⟨u_i| − P|u_i⟩⟨u_i|P)`, and the trace-norm and
trace identities derived from the spectral expansion.

## Main results

* `isHermitian_eq_sum_smul_vecMulVec` — for Hermitian `M : Op n`,
  `M = ∑ i, (eigenvalues i : ℂ) • vecMulVec u_i (star u_i)`.
* `isHermitian_sub_projector_sandwich_eq_sum` — the linear image
  `M ↦ M − P*M*P` distributes over the rank-1 sum.
* `norm_ofLp_eigenvectorBasis_eq_one` — eigenvectors are unit vectors in the
  `EuclideanSpace.equiv (Fin n) ℂ` norm.
* `traceNorm_sum_smul_real_le` — finite-sum triangle inequality with
  nonnegative real coefficients.
* `traceNorm_sub_projector_sandwich_le_sum` and
  `traceNorm_sub_projector_sandwich_le_sum_sqrt` — trace-norm bounds on the
  spectral expansion of `M − P*M*P`.
* `cauchySchwarz_sum_sqrt` — Cauchy–Schwarz / Jensen on a sqrt sum.
* `trace_vecMulVec_self_mul_eq_quadraticForm`,
  `trace_projector_sandwich_rank_one_eq_quadraticForm` — rank-one trace
  identities relating to the quadratic form.
* `trace_projector_sandwich_re_eq_sum` — spectral identity for
  `(P * M * P).trace.re`.
* `sum_eigenvalues_eq_re_trace` — sum of eigenvalues equals the real trace.
* `sum_eigenvalues_one_sub_quadraticForm_eq_trace_diff` — eigenvalue-weighted
  `1 − ⟨u_i|P|u_i⟩` sum identifies with `M.trace.re − (P*M*P).trace.re`.
-/

open Quantum.Operators Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy.DistTraceBoundSpectral

variable {n : ℕ}

/-- **Spectral expansion of a Hermitian operator as a sum of rank-1 outer products.**

For Hermitian `M : Op n` with eigenvalues `λ_i := hM.eigenvalues i` and
orthonormal eigenvector family `u_i := (hM.eigenvectorBasis i).ofLp`,
`M = ∑ i, (λ_i : ℂ) • vecMulVec u_i (star u_i)`.

This is the matrix form of `M = ∑_i p_i |x_i⟩⟨x_i|`. The proof unfolds
`Matrix.IsHermitian.spectral_theorem` to `M = U * D * Uᴴ`, then compares
both sides entrywise via `Matrix.IsHermitian.eigenvectorUnitary_apply`. -/
lemma isHermitian_eq_sum_smul_vecMulVec {M : Op n}
    (hM : M.IsHermitian) :
    M = ∑ i, ((hM.eigenvalues i : ℝ) : ℂ) •
        Matrix.vecMulVec ((hM.eigenvectorBasis i).ofLp)
          (star (hM.eigenvectorBasis i).ofLp) := by
  classical
  set U : Matrix (Fin n) (Fin n) ℂ :=
    (↑hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU_def
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
  -- Spectral theorem: M = U * D * star U.
  have hspec : M = U * D * star U := by
    have h := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  -- Compare entrywise; rewriting `M` directly trips the motive checker because
  -- `hM` depends on `M`, so we apply `hspec` only at the entry level.
  ext a b
  have hentry : M a b = (U * D * star U) a b := by rw [← hspec]
  rw [hentry]
  -- Expand the LHS entry: ∑ i, U_{a,i} * (eig i : ℂ) * star (U_{b,i}).
  rw [Matrix.mul_apply]
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- LHS: (U * D)_{a,i} * (star U)_{i,b}.
  rw [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  -- RHS: ((eig i : ℂ) • vecMulVec u_i (star u_i))_{a,b}.
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  -- `(star f) b = star (f b)` for `f : Fin n → ℂ` (definitional).
  rw [show star ((hM.eigenvectorBasis i).ofLp) b
        = star ((hM.eigenvectorBasis i).ofLp b) from rfl]
  -- Identify `U_{a,i}` and `U_{b,i}` with the eigenvector entries.
  rw [hU_def, hM.eigenvectorUnitary_apply a i, hM.eigenvectorUnitary_apply b i]
  -- Unfold `Function.comp` so that `RCLike.ofReal ∘ eig` matches the coercion.
  simp only [Function.comp_apply]
  -- Both sides are `u_i a * λ_i * star (u_i b)`; reorder.
  change ((hM.eigenvectorBasis i).ofLp a) * ((hM.eigenvalues i : ℝ) : ℂ)
        * (star ((hM.eigenvectorBasis i).ofLp b) : ℂ)
      = ((hM.eigenvalues i : ℝ) : ℂ)
        * (((hM.eigenvectorBasis i).ofLp a)
           * (star ((hM.eigenvectorBasis i).ofLp b) : ℂ))
  ring

/-- **Spectral expansion of `M − P*M*P` as a sum of rank-1 differences.**

Linear image of `isHermitian_eq_sum_smul_vecMulVec` under the linear map
`X ↦ X − P*X*P`. -/
lemma isHermitian_sub_projector_sandwich_eq_sum
    {M : Op n} (hM : M.IsHermitian) (P : Op n) :
    M - P * M * P =
      ∑ i, ((hM.eigenvalues i : ℝ) : ℂ) •
        ( Matrix.vecMulVec ((hM.eigenvectorBasis i).ofLp)
            (star (hM.eigenvectorBasis i).ofLp)
          - P
            * Matrix.vecMulVec ((hM.eigenvectorBasis i).ofLp)
                (star (hM.eigenvectorBasis i).ofLp)
            * P) := by
  classical
  -- Distribute the linear map `X ↦ X − P*X*P` over the rank-1 sum on the LHS.
  conv_lhs =>
    rw [isHermitian_eq_sum_smul_vecMulVec hM]
  -- Pull `P * _ * P` through the sum and through the scalar multiplication.
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]

/-- The eigenvectors of a Hermitian matrix are unit vectors in the
`EuclideanSpace.equiv (Fin n) ℂ` norm — exactly the hypothesis required by
`traceNorm_pure_base_case`. -/
lemma norm_ofLp_eigenvectorBasis_eq_one
    {M : Op n} (hM : M.IsHermitian) (i : Fin n) :
    ‖(EuclideanSpace.equiv (Fin n) ℂ).symm
        ((hM.eigenvectorBasis i).ofLp)‖ = 1 := by
  -- The `.symm` of `EuclideanSpace.equiv` undoes `.ofLp`.
  have h_round_trip :
      (EuclideanSpace.equiv (Fin n) ℂ).symm
          ((hM.eigenvectorBasis i).ofLp)
        = hM.eigenvectorBasis i := rfl
  rw [h_round_trip]
  exact OrthonormalBasis.norm_eq_one _ _

/-- **Finite-sum triangle inequality with nonnegative real coefficients.**

For any finite index set `s : Finset ι`, family `A : ι → Op n`, and nonnegative
real coefficients `lam : ι → ℝ`,
`traceNorm (∑ i ∈ s, ((lam i : ℝ) : ℂ) • A i) ≤ ∑ i ∈ s, lam i * traceNorm (A i)`. -/
lemma traceNorm_sum_smul_real_le {n : ℕ} [NeZero n] {ι : Type*}
    (s : Finset ι) (lam : ι → ℝ) (A : ι → Op n)
    (h_lam_nonneg : ∀ i ∈ s, 0 ≤ lam i) :
    Quantum.Metrics.traceNorm (∑ i ∈ s, ((lam i : ℝ) : ℂ) • A i) ≤
      ∑ i ∈ s, lam i * Quantum.Metrics.traceNorm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hzero : Quantum.Metrics.traceNorm (0 : Op n) = 0 := by
      rw [show (0 : Op n) = (0 : ℂ) • (0 : Op n) from (zero_smul _ _).symm,
          Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
      simp
    rw [hzero]
  | @insert i s hi ih =>
    have hi_nn : 0 ≤ lam i := h_lam_nonneg i (Finset.mem_insert_self _ _)
    have h_rest : ∀ j ∈ s, 0 ≤ lam j :=
      fun j hj => h_lam_nonneg j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    calc Quantum.Metrics.traceNorm
            (((lam i : ℝ) : ℂ) • A i + ∑ j ∈ s, ((lam j : ℝ) : ℂ) • A j)
        ≤ Quantum.Metrics.traceNorm (((lam i : ℝ) : ℂ) • A i)
            + Quantum.Metrics.traceNorm (∑ j ∈ s, ((lam j : ℝ) : ℂ) • A j) :=
          Quantum.Metrics.traceNorm_add_le _ _
      _ = lam i * Quantum.Metrics.traceNorm (A i)
            + Quantum.Metrics.traceNorm (∑ j ∈ s, ((lam j : ℝ) : ℂ) • A j) := by
          rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hi_nn]
      _ ≤ lam i * Quantum.Metrics.traceNorm (A i)
            + ∑ j ∈ s, lam j * Quantum.Metrics.traceNorm (A j) := by
          gcongr
          exact ih h_rest

/-- **Trace-norm bound on the spectral expansion of `M − P*M*P`.**

For PSD `M : Op n`,
`traceNorm (M - P*M*P) ≤ ∑ i, λ_i · traceNorm (|u_i⟩⟨u_i| - P|u_i⟩⟨u_i|P)`,
where `λ_i := hM_psd.1.eigenvalues i ≥ 0` and
`u_i := (hM_psd.1.eigenvectorBasis i).ofLp`. -/
lemma traceNorm_sub_projector_sandwich_le_sum
    [NeZero n] {M : Op n} (hM_psd : Matrix.PosSemidef M) (P : Op n) :
    Quantum.Metrics.traceNorm (M - P * M * P) ≤
      ∑ i, hM_psd.1.eigenvalues i *
        Quantum.Metrics.traceNorm
          ( Matrix.vecMulVec ((hM_psd.1.eigenvectorBasis i).ofLp)
              (star (hM_psd.1.eigenvectorBasis i).ofLp)
            - P
              * Matrix.vecMulVec ((hM_psd.1.eigenvectorBasis i).ofLp)
                  (star (hM_psd.1.eigenvectorBasis i).ofLp)
              * P) := by
  classical
  rw [isHermitian_sub_projector_sandwich_eq_sum hM_psd.1 P]
  exact traceNorm_sum_smul_real_le (n := n)
    (s := (Finset.univ : Finset (Fin n)))
    (lam := fun i => hM_psd.1.eigenvalues i)
    (A := fun i =>
      Matrix.vecMulVec ((hM_psd.1.eigenvectorBasis i).ofLp)
          (star (hM_psd.1.eigenvectorBasis i).ofLp)
        - P
          * Matrix.vecMulVec ((hM_psd.1.eigenvectorBasis i).ofLp)
              (star (hM_psd.1.eigenvectorBasis i).ofLp)
          * P)
    (fun i _ => hM_psd.eigenvalues_nonneg i)

/-- **Cauchy–Schwarz / Jensen on the sqrt sum.**

For any finite index set `s : Finset ι` and nonnegative families `p, c : ι → ℝ`,
`∑ i ∈ s, p i · √(c i) ≤ √(∑ i ∈ s, p i) · √(∑ i ∈ s, p i · c i)`. -/
lemma cauchySchwarz_sum_sqrt {ι : Type*} (s : Finset ι) (p c : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hc : ∀ i, 0 ≤ c i) :
    ∑ i ∈ s, p i * Real.sqrt (c i) ≤
      Real.sqrt (∑ i ∈ s, p i) * Real.sqrt (∑ i ∈ s, p i * c i) := by
  classical
  have key :=
    Real.sum_sqrt_mul_sqrt_le (f := p) (g := fun i => p i * c i) s
      hp (fun i => mul_nonneg (hp i) (hc i))
  -- Termwise rewrite: √(p i) * √(p i * c i) = p i * √(c i).
  have hterm : ∀ i ∈ s,
      Real.sqrt (p i) * Real.sqrt (p i * c i) = p i * Real.sqrt (c i) := by
    intro i _
    rw [Real.sqrt_mul (hp i), ← mul_assoc, Real.mul_self_sqrt (hp i)]
  -- Convert the LHS of `key` to our target's LHS via `Finset.sum_congr`.
  have heq : ∑ i ∈ s, Real.sqrt (p i) * Real.sqrt (p i * c i)
              = ∑ i ∈ s, p i * Real.sqrt (c i) :=
    Finset.sum_congr rfl hterm
  rw [← heq]
  exact key

/-- **Termwise pure-base-case bound on the spectral sum.**

For PSD `M : Op n` and a Hermitian projector `P` (`P*P = P`, `P† = P`),
`traceNorm (M - P*M*P) ≤ ∑ i, λ_i · 2 √(1 − ⟨u_i, P u_i⟩.re)`,
combining `traceNorm_sub_projector_sandwich_le_sum` with the pure base case
`traceNorm_pure_base_case` applied to each eigenvector. -/
lemma traceNorm_sub_projector_sandwich_le_sum_sqrt
    [NeZero n] {M : Op n} (hM_psd : Matrix.PosSemidef M) (P : Op n)
    (hP_idem : P * P = P) (hP_herm : P† = P) :
    Quantum.Metrics.traceNorm (M - P * M * P) ≤
      ∑ i, hM_psd.1.eigenvalues i *
        (2 * Real.sqrt
          (1 - (Quantum.Operators.quadraticForm P
                  ((hM_psd.1.eigenvectorBasis i).ofLp)).re)) := by
  classical
  refine le_trans (traceNorm_sub_projector_sandwich_le_sum hM_psd P) ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (hM_psd.eigenvalues_nonneg i)
  exact InfoTheory.SmoothMinEntropy.DistTraceBoundHelpers.traceNorm_pure_base_case
    hP_idem hP_herm ((hM_psd.1.eigenvectorBasis i).ofLp)
    (norm_ofLp_eigenvectorBasis_eq_one hM_psd.1 i)

/-- **Rank-one trace identity.** For `u : Fin n → ℂ` and `X : Op n`,
`Matrix.trace (vecMulVec u (star u) * X) = quadraticForm X u`. -/
lemma trace_vecMulVec_self_mul_eq_quadraticForm
    [NeZero n] (u : Fin n → ℂ) (X : Op n) :
    Matrix.trace (Matrix.vecMulVec u (star u) * X) =
      Quantum.Operators.quadraticForm X u := by
  rw [Matrix.vecMulVec_mul, Matrix.trace_vecMulVec]
  unfold Quantum.Operators.quadraticForm
  rw [dotProduct_comm, ← Matrix.dotProduct_mulVec]

/-- **Projector-sandwich rank-one trace identity.**

For `u : Fin n → ℂ` and an idempotent `P : Op n` (`P * P = P`),
`Matrix.trace (P * vecMulVec u (star u) * P) = quadraticForm P u`. -/
lemma trace_projector_sandwich_rank_one_eq_quadraticForm
    [NeZero n] (u : Fin n → ℂ) {P : Op n} (hP_idem : P * P = P) :
    Matrix.trace (P * Matrix.vecMulVec u (star u) * P) =
      Quantum.Operators.quadraticForm P u := by
  rw [Matrix.trace_mul_cycle, hP_idem, Matrix.trace_mul_comm]
  exact trace_vecMulVec_self_mul_eq_quadraticForm u P

/-- **Spectral trace identity for `(P * M * P).trace.re`.**

For PSD `M : Op n` and an idempotent `P` (`P * P = P`),
`(P * M * P).trace.re = ∑ i, λ_i * (quadraticForm P u_i).re`,
where `λ_i := hM_psd.1.eigenvalues i` and `u_i := (hM_psd.1.eigenvectorBasis i).ofLp`. -/
lemma trace_projector_sandwich_re_eq_sum
    [NeZero n] {M : Op n} (hM_psd : Matrix.PosSemidef M)
    {P : Op n} (hP_idem : P * P = P) :
    (P * M * P).trace.re =
      ∑ i, hM_psd.1.eigenvalues i *
        (Quantum.Operators.quadraticForm P
          ((hM_psd.1.eigenvectorBasis i).ofLp)).re := by
  classical
  -- 1) Spectral expansion of M.
  conv_lhs =>
    rw [isHermitian_eq_sum_smul_vecMulVec hM_psd.1]
  -- 2) Distribute `P * _ * P` over the sum and through each `smul`.
  rw [Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  -- 3) Trace of the sum, pulling the scalar out of each summand and applying
  --    the rank-one projector-sandwich identity.
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul,
    trace_projector_sandwich_rank_one_eq_quadraticForm _ hP_idem]
  -- 4) Real part of a sum and of `(↑r) * z`.
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Complex.re_ofReal_mul _ _

/-- **Sum of eigenvalues equals the real trace.**

For Hermitian `M : Op n`, `∑ i, hM.eigenvalues i = M.trace.re`. -/
lemma sum_eigenvalues_eq_re_trace {n : ℕ}
    {M : Op n} (hM : M.IsHermitian) :
    ∑ i, hM.eigenvalues i = M.trace.re := by
  classical
  have h := hM.trace_eq_sum_eigenvalues
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (Complex.ofReal_re _).symm

/-- **Eigenvalue-weighted `1 − ⟨u_i|P|u_i⟩` sum identifies with the trace difference.**

For PSD `M : Op n` and an idempotent `P` (`P*P = P`),
`∑ i, λ_i · (1 − (quadraticForm P u_i).re) = M.trace.re − (P*M*P).trace.re`. -/
lemma sum_eigenvalues_one_sub_quadraticForm_eq_trace_diff
    [NeZero n] {M : Op n} (hM_psd : Matrix.PosSemidef M)
    {P : Op n} (hP_idem : P * P = P) :
    ∑ i, hM_psd.1.eigenvalues i *
        (1 - (Quantum.Operators.quadraticForm P
                ((hM_psd.1.eigenvectorBasis i).ofLp)).re)
      = M.trace.re - (P * M * P).trace.re := by
  classical
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      hM_psd.1.eigenvalues i *
          (1 - (Quantum.Operators.quadraticForm P
                  ((hM_psd.1.eigenvectorBasis i).ofLp)).re)
        = hM_psd.1.eigenvalues i
            - hM_psd.1.eigenvalues i *
              (Quantum.Operators.quadraticForm P
                ((hM_psd.1.eigenvectorBasis i).ofLp)).re := by
    intro i _; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
      sum_eigenvalues_eq_re_trace hM_psd.1,
      ← trace_projector_sandwich_re_eq_sum hM_psd hP_idem]

end InfoTheory.SmoothMinEntropy.DistTraceBoundSpectral

end -- noncomputable section
