import QCryptLean.InfoTheory.QuantumLHL.LambdaBoundSingleSigma
import QCryptLean.InfoTheory.QuantumLHL.KernelMatrixBridge
import QCryptLean.InfoTheory.QuantumLHL.ScalarTwoUniversalL2

/-!
# Real-arithmetic / Gram core of the variance bound

This module provides the "real-arithmetic + Gram-PSD" infrastructure around the
trace pairing kernel `Tpair x x' := (T · R x · R x' · T).trace.re`.  It
deliberately does **not** know about `CQState`, `extractorWeightedOp`,
`quantumMarginalOp`, or the hash-output averaging algebra.

The infrastructure provided here is:

1. *Gram structure.* The kernel `Tpair` is the real part of a Hilbert–Schmidt
   inner product `⟨T · R x, T · R x'⟩_HS` on `n × n` complex matrices, when
   `T` is Hermitian.

2. *Abstract Gram + bounded-norm matrix bound.* For any real symmetric
   `A : X → X → ℝ` with `vᵀ A v ≤ ‖v‖²` for every real vector `v`, and any
   Gram-PSD kernel `G : X → X → ℝ`, we have `∑_{x,x'} A x x' · G x x' ≤ ∑_x G x x`.
   This is `gram_real_psd_with_bounded_norm`, fully proved.

## Main statements
- `trace_T_A_B_T_re_eq_HS`: Hermitian-trace HS pairing identity (Gram step).
- `sum_pair_trace_T_R_R_T_re_nonneg`: full-pair sum non-negativity for the
  trace pairing kernel (Hermitian `R x` suffices here).
- `Tpair_real_psd`: the trace-pairing kernel is a real PSD kernel (Hermitian `R x`).
- `gram_real_psd_with_bounded_norm`: abstract Gram + bounded-norm matrix inequality,
  fully proved.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-! ## Step 1: Gram structure of the kernel `(T · R x · R x' · T).trace.re` -/

/-- **Gram identity for the real trace pairing.**

For Hermitian `T : Op n` and Hermitian `B : Op n` and arbitrary `A : Op n`,
  `(T · A · B · T).trace.re = ((T · A) · (T · B)†).trace.re`,
i.e. `Tpair(A, B) = ⟨T·A, T·B⟩_HS,re`. The proof is one Hermitian + cyclic
trace step. -/
lemma trace_T_A_B_T_re_eq_HS {n : ℕ} {T : Op n} (hT : T.IsHermitian)
    {A B : Op n} (hB : B.IsHermitian) :
    (T * A * B * T).trace.re = ((T * A) * (T * B)ᴴ).trace.re := by
  -- (T·B)† = B† · T† = B · T  (using Hermiticity of T and B).
  have hConj : (T * B)ᴴ = B * T := by
    rw [Matrix.conjTranspose_mul, hT.eq, hB.eq]
  rw [hConj, Matrix.mul_assoc (T * A) B T]

/-- **Diagonal non-negativity of the Gram kernel.** Immediate from
`tr_S_ASqS_re_nonneg`. Restated here for use with `Tpair`. -/
lemma trace_T_A_A_T_re_nonneg {n : ℕ} {T : Op n} (hT : T.IsHermitian)
    {A : Op n} (hA : A.IsHermitian) :
    0 ≤ (T * A * A * T).trace.re :=
  tr_S_ASqS_re_nonneg hT hA

/-- **Marginal-square non-negativity.** The full pair sum is non-negative.
Follows from `sum_pair_tr_S_RR_S_eq_marginal_sq` and `tr_S_ASqS_re_nonneg`
on the marginal `∑_x R x`, since a sum of Hermitian operators is Hermitian. -/
lemma sum_pair_trace_T_R_R_T_re_nonneg {X : Type*} [Fintype X]
    {n : ℕ} {T : Op n} (hT : T.IsHermitian)
    (R : X → Op n) (hR : ∀ x, (R x).IsHermitian) :
    0 ≤ ∑ x : X, ∑ x' : X, (T * R x * R x' * T).trace.re := by
  rw [sum_pair_tr_S_RR_S_eq_marginal_sq T R]
  -- Marginal is Hermitian.
  have hMarg : (∑ x : X, R x).IsHermitian := by
    change (∑ x : X, R x)ᴴ = ∑ x : X, R x
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun x _ => (hR x).eq
  exact tr_S_ASqS_re_nonneg hT hMarg

/-! ## Step 2: Scalar 2-universal L² identities

The scalar / 2-universal finite-set algebra layer (B0)–(B3) is isolated in
`ScalarTwoUniversalL2.lean`. The scalar quadratic-form bound
`∀ v, ∑ (τ − c·J) v v ≤ ∑ v²` is false (counterexample: `v = (1,−1,1)`,
`|S|=|X|=|Z|=3`), so `gram_real_psd_with_bounded_norm` cannot be applied via
that scalar route. -/

/-! ## Step 3: Abstract Gram + bounded-norm matrix bound -/

/-- **Real Gram + bounded-norm matrix inequality (PSD-kernel form).**

Let `A : X → X → ℝ` be a real symmetric kernel with the
operator-norm-≤-1 bound
  `∀ v : X → ℝ, ∑_{x,x'} A x x' · v x · v x' ≤ ∑_x (v x)^2`.
Let `G : X → X → ℝ` be a real PSD kernel, i.e.
  `∀ c : X → ℝ, 0 ≤ ∑_{x,x'} G x x' · c x · c x'`.
Then
  `∑_{x,x'} A x x' · G x x' ≤ ∑_x G x x`.

This is the cleanest abstract form: it does not require `G` to be presented
as a Gram matrix of any specific feature map, and avoids forcing the caller
to construct a real inner-product structure on complex matrices. -/
lemma gram_real_psd_with_bounded_norm
    {X : Type*} [Fintype X]
    (A : X → X → ℝ) (hA_sym : ∀ x x', A x x' = A x' x)
    (hA_op : ∀ v : X → ℝ,
      (∑ x : X, ∑ x' : X, A x x' * v x * v x') ≤ ∑ x : X, (v x)^2)
    (G : X → X → ℝ)
    (hG_psd : ∀ c : X → ℝ,
      0 ≤ ∑ x : X, ∑ x' : X, G x x' * c x * c x') :
    (∑ x : X, ∑ x' : X, A x x' * G x x') ≤ ∑ x : X, G x x := by
  classical
  -- Symmetrization of `G` (the symmetric kernel `Gs x x' = (G x x' + G x' x) / 2`).
  set Gs : X → X → ℝ := fun x x' => (G x x' + G x' x) / 2 with hGs_def
  -- Operator-norm witness kernel `B := I − A` (entries: `δ x x' - A x x'`).
  set B : X → X → ℝ :=
    fun x x' => (if x = x' then (1:ℝ) else 0) - A x x' with hB_def
  -- (a) `Gs` is symmetric.
  have hGs_sym : ∀ x x', Gs x x' = Gs x' x := by
    intro x x'; simp only [hGs_def]; ring
  -- (b) `B` is symmetric (uses `hA_sym`).
  have hB_sym : ∀ x x', B x x' = B x' x := by
    intro x x'
    simp only [hB_def]
    rw [hA_sym x x']
    rcases eq_or_ne x x' with h | h
    · subst h; rfl
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  -- (c) `Gs` is PSD as a bilinear form (its bilinear form equals that of `G`).
  have hGs_psd : ∀ c : X → ℝ,
      0 ≤ ∑ x : X, ∑ x' : X, Gs x x' * c x * c x' := by
    intro c
    rw [show (∑ x : X, ∑ x' : X, Gs x x' * c x * c x')
        = ∑ x : X, ∑ x' : X, ((G x x' + G x' x) / 2) * c x * c x' from rfl]
    rw [kernel_sym_bilinear]
    exact hG_psd c
  -- (d) `B` is PSD as a bilinear form (uses `hA_op`).
  have hB_psd : ∀ c : X → ℝ,
      0 ≤ ∑ x : X, ∑ x' : X, B x x' * c x * c x' := by
    intro c
    have hexpand :
        (∑ x : X, ∑ x' : X, B x x' * c x * c x') =
          (∑ x : X, (c x)^2) - (∑ x : X, ∑ x' : X, A x x' * c x * c x') := by
      simp only [hB_def]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hdelta :
          (∑ x' : X, (if x = x' then (1:ℝ) else 0) * c x * c x') = (c x)^2 := by
        rw [Finset.sum_eq_single x]
        · simp [sq]
        · intro x' _ hne; rw [ite_eq_right (Ne.symm hne)]; ring
        · intro h; exact (h (Finset.mem_univ x)).elim
      rw [show (c x)^2 - (∑ x' : X, A x x' * c x * c x')
          = (∑ x' : X, (if x = x' then (1:ℝ) else 0) * c x * c x')
            - (∑ x' : X, A x x' * c x * c x') by rw [hdelta]]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x' _ => ?_
      ring
    rw [hexpand]
    have h1 := hA_op c
    linarith
  -- (e) Apply the abstract two-PSD-kernels fact.
  have hmain : 0 ≤ ∑ x : X, ∑ x' : X, B x x' * Gs x x' :=
    sum_kernels_psd_nonneg B Gs hB_sym hGs_sym hB_psd hGs_psd
  -- (f) Translate back to the target inequality. We compute
  --   `∑ B x x' * Gs x x' = (∑ x, G x x) − (∑ x x', A x x' * Gs x x')`,
  -- and `∑ A x x' * Gs x x' = ∑ A x x' * G x x'` (uses `hA_sym`).
  have hBGs_expand :
      (∑ x : X, ∑ x' : X, B x x' * Gs x x') =
        (∑ x : X, G x x) - (∑ x : X, ∑ x' : X, A x x' * Gs x x') := by
    simp only [hB_def]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hdelta :
        (∑ x' : X, (if x = x' then (1:ℝ) else 0) * Gs x x') = G x x := by
      rw [Finset.sum_eq_single x]
      · rw [ite_eq_left rfl, one_mul]; simp only [hGs_def]; ring
      · intro x' _ hne; rw [ite_eq_right (Ne.symm hne)]; ring
      · intro h; exact (h (Finset.mem_univ x)).elim
    rw [show G x x - (∑ x' : X, A x x' * Gs x x')
        = (∑ x' : X, (if x = x' then (1:ℝ) else 0) * Gs x x')
          - (∑ x' : X, A x x' * Gs x x') by rw [hdelta]]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x' _ => ?_
    ring
  have hA_Gs_eq_A_G :
      (∑ x : X, ∑ x' : X, A x x' * Gs x x') =
        (∑ x : X, ∑ x' : X, A x x' * G x x') := by
    change (∑ x : X, ∑ x' : X, A x x' * ((G x x' + G x' x) / 2)) = _
    exact kernel_sym_inner_of_sym_left A G hA_sym
  -- Combine.
  rw [hBGs_expand, hA_Gs_eq_A_G] at hmain
  linarith

/-! ### Helper: bilinearity of the trace pairing on scalar-weighted sums -/

/-- **Bilinearity of `Tpair` against real scalars.** For any `T : Op n`,
family `R : X → Op n`, and real coefficients `c : X → ℝ`,
```
(T · (∑ x, c x • R x) · (∑ y, c y • R y) · T).trace.re
   = ∑ x, ∑ y, c x · c y · (T · R x · R y · T).trace.re.
```
This is the bilinear-form identity behind the Gram-PSD property of the
kernel `Tpair x x' := (T · R x · R x' · T).trace.re`. -/
lemma trace_T_sum_smul_R_sum_smul_R_T_re_eq_pair_sum
    {X : Type*} [Fintype X] {n : ℕ} (T : Op n) (R : X → Op n) (c : X → ℝ) :
    (T * (∑ x : X, (c x : ℂ) • R x) *
        (∑ y : X, (c y : ℂ) • R y) * T).trace.re =
      ∑ x : X, ∑ y : X,
        c x * c y * (T * R x * R y * T).trace.re := by
  -- Use the bilinearity expansion `sum_pair_tr_S_RR_S_eq_marginal_sq` with
  -- the scalar-weighted family `R' x := (c x : ℂ) • R x`.
  rw [← sum_pair_tr_S_RR_S_eq_marginal_sq T (fun x => (c x : ℂ) • R x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  -- Pull the scalars out of the inner product, then take real part.
  have h_smul :
      T * ((c x : ℂ) • R x) * ((c y : ℂ) • R y) * T =
        ((c x : ℂ) * (c y : ℂ)) • (T * R x * R y * T) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    ring
  rw [h_smul, Matrix.trace_smul, smul_eq_mul,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul]

/-! ### Helper: a real-scalar combination of Hermitian operators is Hermitian -/

/-- A real-coefficient combination `∑_x (c x : ℂ) • R x` of Hermitian operators
is Hermitian. -/
lemma isHermitian_sum_real_smul {X : Type*} [Fintype X] {n : ℕ}
    (R : X → Op n) (hR : ∀ x, (R x).IsHermitian) (c : X → ℝ) :
    (∑ x : X, (c x : ℂ) • R x).IsHermitian := by
  change (∑ x : X, (c x : ℂ) • R x)ᴴ = ∑ x : X, (c x : ℂ) • R x
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.conjTranspose_smul, (hR x).eq]
  congr 1
  simp [RCLike.star_def, Complex.conj_ofReal]

/-! ### Helper: the trace pairing kernel is real PSD -/

/-- **`Tpair` is a real PSD kernel.** For Hermitian `T : Op n` and a family
`R : X → Op n` of Hermitian operators, the kernel
`Tpair x x' := (T · R x · R x' · T).trace.re` is real PSD: for every real
vector `c : X → ℝ`,
`0 ≤ ∑_{x,x'} Tpair x x' · c x · c x'`. -/
lemma Tpair_real_psd
    {X : Type*} [Fintype X] {n : ℕ}
    {T : Op n} (hT : T.IsHermitian)
    (R : X → Op n) (hR : ∀ x, (R x).IsHermitian) (c : X → ℝ) :
    0 ≤ ∑ x : X, ∑ x' : X,
      (T * R x * R x' * T).trace.re * c x * c x' := by
  -- The pair sum equals `(T · S · S · T).trace.re` for `S := ∑_x (c x : ℂ) • R x`.
  set S : Op n := ∑ x : X, (c x : ℂ) • R x with hS_def
  have hS_herm : S.IsHermitian := isHermitian_sum_real_smul R hR c
  -- Bilinearity expansion identifies the pair sum with `(T · S · S · T).trace.re`,
  -- and the latter is non-negative by Hermitian sandwich-square trace positivity.
  have h_eq :
      (T * S * S * T).trace.re =
        ∑ x : X, ∑ x' : X,
          (T * R x * R x' * T).trace.re * c x * c x' := by
    rw [trace_T_sum_smul_R_sum_smul_R_T_re_eq_pair_sum T R c]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun x' _ => ?_
    ring
  rw [← h_eq]
  exact tr_S_ASqS_re_nonneg hT hS_herm

end InfoTheory.QuantumLHL

end -- noncomputable section
