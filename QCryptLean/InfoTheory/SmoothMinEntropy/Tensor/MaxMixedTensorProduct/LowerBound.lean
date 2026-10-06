import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.MaxMixedTensorProduct.Basic
import QCryptLean.Quantum.TensorProducts.QuadraticForm

/-!
# Spectral extraction and the lower product bound

The converse direction of the fixed-reference product rule of
`MaxMixedTensorProduct/Basic.lean`. Tensorizing a one-copy domination is elementary; *extracting* a
one-copy domination from an `n`-copy one is the spectral step, and it is where the isotropy of the
maximally mixed reference is used:

* a tensor-power test vector `v^{⊗ n}` turns both quadratic forms into `n`-th powers of the
  one-copy quadratic forms (`exists_tensorPow_quadraticForm_pow_eq`), so an `n`-copy bound at
  scalar `t` becomes the real inequality `x ^ n ≤ t · y ^ n`;
* the real `n`-th root then yields the one-copy bound at scalar `t ^ (1/n)`
  (`le_rpow_inv_mul_of_pow_le`).

Since a one-copy scalar `s` with `s ^ n = t` is feasible, the one-copy optimum satisfies
`λ(ρ₁|M_d) ≤ s`, hence `λ(ρ₁|M_d) ^ n ≤ t` for every feasible `t` of the product state, which is
the `≥` direction of the product rule.

## Main statements

* `le_rpow_inv_mul_of_pow_le` — the real `n`-th-root extraction step.
* `SubDensityOp.tensorFinProd_const_toOp_entry_prod` — entries of a constant tensor power.
* `maxMixed_tensorPow_toOp_entry_prod` — entries of `M_{d^n}` as a one-copy product.
* `exists_tensorPow_quadraticForm_pow_eq` — the tensor-power test-vector identity.
* `single_opLe_rpow_of_tensorFinProd_const` — one-copy domination at the `n`-th root.
* `pow_minFeasibleLambda_le_tensorFinProd_maxMixed_of_stateMap` — the `≥` direction of the
  product rule.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The real `n`-th root step -/

/-- **Real `n`-th-root extraction.** From `x ^ n ≤ t · y ^ n` for nonnegative reals and `0 < n`,
conclude `x ≤ t ^ (1/n) · y`.

This isolates the purely analytic half of the spectral extraction below; it holds for arbitrary
nonnegative reals and mentions no operator. -/
lemma le_rpow_inv_mul_of_pow_le {n : ℕ} (hn : 0 < n) {t x y : ℝ}
    (ht : 0 ≤ t) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ^ n ≤ t * y ^ n) :
    x ≤ t ^ (1 / (n : ℝ)) * y := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hyn : 0 ≤ y ^ n := pow_nonneg hy n
  have htyn : 0 ≤ t * y ^ n := mul_nonneg ht hyn
  have h1 : x ≤ (t * y ^ n) ^ ((n : ℝ)⁻¹) := by
    rw [Real.le_rpow_inv_iff_of_pos hx htyn hn_pos, Real.rpow_natCast]
    exact hxy
  have h2 : (t * y ^ n) ^ ((n : ℝ)⁻¹) = t ^ ((n : ℝ)⁻¹) * y := by
    rw [Real.mul_rpow ht hyn, ← Real.rpow_natCast y n, ← Real.rpow_mul hy,
      mul_inv_cancel₀ hn_ne, Real.rpow_one]
  rw [h2] at h1
  rwa [one_div]

/-! ## Entries of constant tensor powers -/

/-- **Entries of a constant tensor power.** For the constant family `fun _ => a`, the flat entry of
`a^{⊗ n}` at the digit strings `u`, `v` is the product of the one-copy entries.

This is the constant-family form of `SubDensityOp.tensorFinProd_toOp_entry_prod_rev`; the digit
reversal there is absorbed by the bijection `Fin.revPerm`, which a constant family does not see. -/
lemma SubDensityOp.tensorFinProd_const_toOp_entry_prod {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (a : SubDensityOp d) (u v : Fin n → Fin d) :
    (SubDensityOp.tensorFinProd n (fun _ : Fin n => a)).toOp
        (finFunctionFinEquiv u) (finFunctionFinEquiv v) =
      ∏ k : Fin n, a.toOp (u k) (v k) := by
  have hrev :=
    SubDensityOp.tensorFinProd_toOp_entry_prod_rev (fun _ : Fin n => a) (u ∘ Fin.rev) (v ∘ Fin.rev)
  have hu : (u ∘ Fin.rev) ∘ Fin.rev = u := by
    funext i
    simp [Function.comp_def]
  have hv : (v ∘ Fin.rev) ∘ Fin.rev = v := by
    funext i
    simp [Function.comp_def]
  rw [hu, hv] at hrev
  rw [hrev]
  exact Fintype.prod_equiv (Fin.revPerm) _ _ (fun i => rfl)

/-- **Entries of the `n`-copy maximally mixed reference.** The flat entry of `M_{d^n}` at the digit
strings `u`, `v` is the product of the one-copy entries of `M_d`.

Immediate from the multiplicativity `SubDensityOp.tensorFinProd_maxMixed` of the reference. -/
lemma maxMixed_tensorPow_toOp_entry_prod {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (u v : Fin n → Fin d) :
    (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))).toOp
        (finFunctionFinEquiv u) (finFunctionFinEquiv v) =
      ∏ k : Fin n,
        (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp (u k) (v k) := by
  rw [← SubDensityOp.tensorFinProd_maxMixed_toOp (d := d) (n := n),
    SubDensityOp.tensorFinProd_const_toOp_entry_prod]

/-! ## The tensor-power test vector -/

/-- **Tensor-power test-vector identity.** For every one-copy test vector `v` there is an `n`-copy
test vector — namely `tensorPowVec v`, i.e. `v ⊗ ⋯ ⊗ v` — on which the quadratic forms of both
`a^{⊗ n}` and `M_{d^n}` are the `n`-th powers of the corresponding one-copy quadratic forms.

Both operators are Hermitian, so their one-copy quadratic forms are real and the `n`-th power
commutes with taking the real part. -/
lemma exists_tensorPow_quadraticForm_pow_eq {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (a : SubDensityOp d) (v : Fin d → ℂ) :
    ∃ V : Fin (d ^ n) → ℂ,
      (quadraticForm (SubDensityOp.tensorFinProd n (fun _ : Fin n => a)).toOp V).re =
          ((quadraticForm a.toOp v).re) ^ n ∧
      (quadraticForm
            (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))).toOp V).re =
          ((quadraticForm (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp v).re) ^ n := by
  refine ⟨tensorPowVec v, ?_, ?_⟩
  · rw [quadraticForm_tensorPowVec_of_entrywise_prod (A := a.toOp)
      (M := (SubDensityOp.tensorFinProd n (fun _ : Fin n => a)).toOp)
      (fun f g => SubDensityOp.tensorFinProd_const_toOp_entry_prod a f g) v]
    exact complex_re_pow_of_im_eq_zero (quadraticForm a.toOp v)
      (quadraticForm_im_of_isHermitian a.toOp a.isHermitian v) n
  · rw [quadraticForm_tensorPowVec_of_entrywise_prod
      (A := (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp)
      (M := (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))).toOp)
      (fun f g => maxMixed_tensorPow_toOp_entry_prod f g) v]
    exact complex_re_pow_of_im_eq_zero
      (quadraticForm (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp v)
      (quadraticForm_im_of_isHermitian
        (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp
        (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).isHermitian v) n

/-! ## One-copy extraction -/

/-- **Spectral extraction of a one-copy domination.** If the `n`-fold tensor power of a single
sub-density operator `a` is dominated by `t` copies of the `n`-copy maximally mixed reference, then
`a` itself is dominated by `t ^ (1/n)` copies of the one-copy maximally mixed reference.

The maximally mixed reference is isotropic, so a tensor-power test vector separates the `n`-copy
bound into the `n`-th power of the one-copy bound; the real `n`-th root then closes it. -/
lemma single_opLe_rpow_of_tensorFinProd_const {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (a : SubDensityOp d) {t : ℝ} (ht : 0 ≤ t)
    (h : opLe (SubDensityOp.tensorFinProd n (fun _ : Fin n => a)).toOp
      ((t : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))).toOp)) :
    opLe a.toOp
      (Complex.ofReal (t ^ (1 / (n : ℝ))) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp) := by
  intro v
  obtain ⟨V, hV_a, hV_M⟩ := exists_tensorPow_quadraticForm_pow_eq (n := n) a v
  have hV := h V
  rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hV
  rw [hV_a, hV_M] at hV
  rw [quadraticForm_ofReal_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact le_rpow_inv_mul_of_pow_le (Nat.pos_of_neZero n) ht (a.pos_semidef v)
    ((DensityOp.toSubDensityOp (DensityOp.maxMixed d)).pos_semidef v) hV

/-! ## The lower product bound -/

/-- **From `n`-copy domination to the one-copy optimum.** If every block of the `n`-fold product is
dominated by `t` copies of `M_{d^n}`, then `λ(ρ₁|M_d) ^ n ≤ t`.

Each constant string `ω = (x, …, x)` gives a one-copy domination at `t ^ (1/n)`, so `t ^ (1/n)` is
feasible for `ρ₁`; taking `n`-th powers of `λ(ρ₁|M_d) ≤ t ^ (1/n)` gives the claim. -/
theorem pow_minFeasibleLambda_le_of_tensorFinProd_maxMixed_domination
    {X : Type*} [Fintype X] {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (rho1 : CQState X d) {t : ℝ} (ht_nonneg : 0 ≤ t)
    (ht_dom : ∀ ω : Fin n → X,
      opLe (SubDensityOp.tensorFinProd n (fun j => rho1.stateMap (ω j))).toOp
        ((t : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))).toOp)) :
    (minFeasibleLambda rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d))) ^ n ≤ t := by
  set s : ℝ := t ^ (1 / (n : ℝ)) with hs_def
  have hs_nonneg : 0 ≤ s := Real.rpow_nonneg ht_nonneg _
  have h_single : ∀ x : X,
      opLe (rho1.stateMap x).toOp
        (Complex.ofReal s • (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp) := by
    intro x
    exact single_opLe_rpow_of_tensorFinProd_const (rho1.stateMap x) ht_nonneg
      (ht_dom (fun _ : Fin n => x))
  have h_feas : isFeasible rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) s :=
    ⟨hs_nonneg, h_single⟩
  have h_lambda_le :
      minFeasibleLambda rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) ≤ s :=
    csInf_le (minFeasibleLambda_bddBelow _ _) h_feas
  have h_pow_le :
      (minFeasibleLambda rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d))) ^ n ≤ s ^ n :=
    pow_le_pow_left₀
      (minFeasibleLambda_nonneg rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d)))
      h_lambda_le n
  have h_sn : s ^ n = t := by
    rw [hs_def, one_div]
    exact Real.rpow_inv_natCast_pow ht_nonneg (Nat.pos_of_neZero n).ne'
  rwa [h_sn] at h_pow_le

/-- **Every feasible scalar of the product state bounds `λ(ρ₁|M_d) ^ n` from above.** -/
theorem pow_minFeasibleLambda_le_of_tensorFinProd_maxMixed_isFeasible
    {X : Type*} [Fintype X] {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (rhoN : CQState (Fin n → X) (d ^ n)) (rho1 : CQState X d)
    (h_state : ∀ ω : Fin n → X,
      rhoN.stateMap ω = SubDensityOp.tensorFinProd n (fun j => rho1.stateMap (ω j)))
    {t : ℝ}
    (ht : isFeasible rhoN (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))) t) :
    (minFeasibleLambda rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d))) ^ n ≤ t := by
  refine pow_minFeasibleLambda_le_of_tensorFinProd_maxMixed_domination rho1 ht.1 (fun ω => ?_)
  have hω := ht.2 ω
  rwa [h_state ω] at hω

/-- **Lower direction of the fixed-reference product rule.** The `n`-th power of the one-copy
optimum against `M_d` is at most the optimum of the `n`-fold product against `M_{d^n}`. -/
theorem pow_minFeasibleLambda_le_tensorFinProd_maxMixed_of_stateMap
    {X : Type*} [Fintype X] {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (rhoN : CQState (Fin n → X) (d ^ n)) (rho1 : CQState X d)
    (h_state : ∀ ω : Fin n → X,
      rhoN.stateMap ω = SubDensityOp.tensorFinProd n (fun j => rho1.stateMap (ω j))) :
    (minFeasibleLambda rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d))) ^ n ≤
      minFeasibleLambda rhoN (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))) := by
  refine le_csInf ⟨_,
    isFeasible_tensorFinProd_maxMixed_pow_minFeasibleLambda_of_stateMap rhoN rho1 h_state⟩ ?_
  intro t ht
  exact pow_minFeasibleLambda_le_of_tensorFinProd_maxMixed_isFeasible rhoN rho1 h_state ht

end InfoTheory.SmoothMinEntropy

end
