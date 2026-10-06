import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.ProductReference

/-!
# Maximally mixed tensor powers and the upper product bound

The maximally mixed reference is *multiplicative*: the `n`-fold tensor power of `M_d` is `M_{d^n}`.
This file records that identity and the consequence it was built for — the upper (``≤``) direction
of the `n`-fold product rule for the minimal feasible scalar `minFeasibleLambda` of a CQ state
against maximally mixed references.

Writing `λ(ρ|σ) := minFeasibleLambda ρ σ = inf {t ≥ 0 : ∀ x, ρ_A(x) ≼ t·σ}`, so that
`H_min(ρ|σ) = -log₂ λ(ρ|σ)` (Renner, arXiv:quant-ph/0512258v2, Definition 3.1.1 `def:minmaxentr`),
the product rule
`λ(ρ^{(n)} | M_{d^n}) = λ(ρ₁ | M_d)^n`
is the *fixed-reference, nonsmooth* tensor additivity `H_min(ρ⊗ρ'|σ⊗σ') = H_min(ρ|σ) + H_min(ρ'|σ')`
of Renner's Lemma 3.1.11 (`lem:HRindadd`), specialised to `n` equal factors and to the maximally
mixed reference. It is *not* the smooth statement `lem:Hminindaddsmooth`, and it is not a claim
about the reference-optimized `H_min(A|B)`.

## Main statements

* `SubDensityOp.tensor_maxMixed` — `M_a ⊗ M_b = M_{a·b}`.
* `SubDensityOp.tensorFinProd_maxMixed` — `M_d^{⊗n} = M_{d^n}`.
* `SubDensityOp.castDim_maxMixed` — the maximally mixed reference commutes with a dimension cast.
* `isFeasible_minFeasibleLambda_maxMixed` — the optimum is attained at a maximally mixed reference.
* `tensorFinProd_opLe_pow_maxMixed_of_forall` — tensorization of per-factor domination.
* `minFeasibleLambda_tensorFinProd_maxMixed_le_pow_of_stateMap` — the `≤` direction of the
  product rule.

The reverse direction (the spectral `n`-th root extraction) is in
`MaxMixedTensorProduct/LowerBound.lean`, and the two are combined in `MaxMixedTensorProduct.lean`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The maximally mixed reference is multiplicative -/

/-- **A dimension cast carries the maximally mixed reference to the maximally mixed reference.**
Both sides are `dim⁻¹ • 1`, so the relabelling is invisible. -/
lemma SubDensityOp.castDim_maxMixed {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    SubDensityOp.castDim h (DensityOp.toSubDensityOp (DensityOp.maxMixed n)) =
      DensityOp.toSubDensityOp (DensityOp.maxMixed m) := by
  subst h
  rfl

/-- **The maximally mixed references of two registers tensor to the maximally mixed reference of
the joint register**, `M_a ⊗ M_b = M_{a·b}`.

The operator-level statement is also available, for the BB84 announce kernels only, as
`toSubDensityOp_maxMixed_tensor` elsewhere in the BB84 announce-kernel machinery; that module sits
above
the BB84 finite-size stack, so the generic sub-density form is proved here. -/
lemma SubDensityOp.tensor_maxMixed (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] :
    (DensityOp.toSubDensityOp (DensityOp.maxMixed a)).tensor
        (DensityOp.toSubDensityOp (DensityOp.maxMixed b)) =
      DensityOp.toSubDensityOp (DensityOp.maxMixed (a * b)) := by
  refine SubDensityOp.ext ?_
  change (DensityOp.toSubDensityOp (DensityOp.maxMixed a)).toOp ⊗
      (DensityOp.toSubDensityOp (DensityOp.maxMixed b)).toOp = _
  rw [maxMixed_toOp_eq_inv_smul_one, maxMixed_toOp_eq_inv_smul_one,
    maxMixed_toOp_eq_inv_smul_one, Op.smul_tensor_smul, Op.tensor_one,
    ← Complex.ofReal_mul]
  congr 2
  rw [Nat.cast_mul, mul_inv]

/-- Auxiliary induction for `SubDensityOp.tensorFinProd_maxMixed`; the `NeZero (d ^ n)` instance is
derived internally so the statement can be proved by a plain induction on `n`. -/
private lemma tensorFinProd_maxMixed_aux {d : ℕ} [NeZero d] (n : ℕ) :
    haveI : NeZero (d ^ n) := NeZero.pow
    SubDensityOp.tensorFinProd n
        (fun _ : Fin n => DensityOp.toSubDensityOp (DensityOp.maxMixed d)) =
      DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n)) := by
  induction n with
  | zero =>
      refine SubDensityOp.ext ?_
      ext i j
      have hij : i = j := by
        apply Fin.ext
        have hi := i.isLt
        have hj := j.isLt
        simp only [pow_zero] at hi hj
        omega
      subst hij
      simp [SubDensityOp.tensorFinProd, SubDensityOp.castDim, SubDensityOp.trivialOne,
        DensityOp.toSubDensityOp, DensityOp.maxMixed, DensityOp.trivial, Matrix.one_apply_eq]
  | succ k ih =>
      haveI : NeZero (d ^ k) := NeZero.pow
      haveI : NeZero (d * d ^ k) :=
        ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne (d ^ k))⟩
      haveI : NeZero (d ^ (k + 1)) := NeZero.pow
      change SubDensityOp.castDim (by ring : d * d ^ k = d ^ (k + 1))
          ((DensityOp.toSubDensityOp (DensityOp.maxMixed d)).tensor
            (SubDensityOp.tensorFinProd k
              (fun _ : Fin k => DensityOp.toSubDensityOp (DensityOp.maxMixed d)))) = _
      rw [ih, SubDensityOp.tensor_maxMixed, SubDensityOp.castDim_maxMixed]

/-- **The `n`-fold tensor power of the maximally mixed reference is maximally mixed**,
`M_d^{⊗n} = M_{d^n}`.

This is the reference side of Renner's fixed-reference tensor additivity: the `n`-copy calibration
reference of the `n`-fold product experiment is again maximally mixed. -/
lemma SubDensityOp.tensorFinProd_maxMixed {d n : ℕ} [NeZero d] [NeZero (d ^ n)] :
    SubDensityOp.tensorFinProd n
        (fun _ : Fin n => DensityOp.toSubDensityOp (DensityOp.maxMixed d)) =
      DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n)) :=
  tensorFinProd_maxMixed_aux n

/-- Operator-level form of `SubDensityOp.tensorFinProd_maxMixed`. -/
lemma SubDensityOp.tensorFinProd_maxMixed_toOp {d n : ℕ} [NeZero d] [NeZero (d ^ n)] :
    (SubDensityOp.tensorFinProd n
        (fun _ : Fin n => DensityOp.toSubDensityOp (DensityOp.maxMixed d))).toOp =
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))).toOp := by
  rw [SubDensityOp.tensorFinProd_maxMixed]

/-! ## Attainment at a maximally mixed reference -/

/-- **The infimum defining `minFeasibleLambda` is attained against a maximally mixed reference.**
The maximally mixed reference is positive definite, so the feasible set is closed and nonempty and
`isFeasible_minFeasibleLambda_of_posDef` applies. -/
lemma isFeasible_minFeasibleLambda_maxMixed
    {X : Type*} [Fintype X] {d : ℕ} [NeZero d] (ρ : CQState X d) :
    isFeasible ρ (DensityOp.toSubDensityOp (DensityOp.maxMixed d))
      (minFeasibleLambda ρ (DensityOp.toSubDensityOp (DensityOp.maxMixed d))) :=
  isFeasible_minFeasibleLambda_of_posDef ρ
    (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) maxMixed_toSubDensityOp_posDef

/-! ## Tensorization of per-factor domination -/

/-- **Tensorization of per-factor domination by maximally mixed references.** If every factor is
dominated by `t` copies of the one-copy maximally mixed reference, then the `n`-fold product is
dominated by `t ^ n` copies of the `n`-copy maximally mixed reference.

This is the maximally mixed specialisation of the constant-reference bound
`SubDensityOp.tensorFinProd_opLe_pow_const`, combined with the multiplicativity
`SubDensityOp.tensorFinProd_maxMixed` of the reference itself. -/
lemma tensorFinProd_opLe_pow_maxMixed_of_forall
    {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (f : Fin n → SubDensityOp d) {t : ℝ} (ht : 0 ≤ t)
    (hdom : ∀ j : Fin n,
      opLe (f j).toOp
        ((t : ℂ) • (DensityOp.toSubDensityOp (DensityOp.maxMixed d)).toOp)) :
    opLe (SubDensityOp.tensorFinProd n f).toOp
      (((t ^ n : ℝ) : ℂ) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))).toOp) := by
  have h := SubDensityOp.tensorFinProd_opLe_pow_const
    (DensityOp.toSubDensityOp (DensityOp.maxMixed d)) n f ht hdom
  rwa [SubDensityOp.tensorFinProd_maxMixed_toOp] at h

/-- **Tensorized domination at the one-copy optimal scalar.** Every block of the `n`-fold CQ
product is dominated by `λ(ρ₁|M_d) ^ n` copies of the `n`-copy maximally mixed reference. -/
theorem tensorFinProd_opLe_pow_minFeasibleLambda_maxMixed
    {X : Type*} [Fintype X] {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (rho1 : CQState X d) (ω : Fin n → X) :
    opLe (SubDensityOp.tensorFinProd n (fun j => rho1.stateMap (ω j))).toOp
      ((((minFeasibleLambda rho1
            (DensityOp.toSubDensityOp (DensityOp.maxMixed d))) ^ n : ℝ) : ℂ) •
        (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))).toOp) :=
  tensorFinProd_opLe_pow_maxMixed_of_forall
    (fun j => rho1.stateMap (ω j))
    (minFeasibleLambda_nonneg rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d)))
    (fun j => (isFeasible_minFeasibleLambda_maxMixed rho1).2 (ω j))

/-- **The `n`-th power of the one-copy optimum is feasible for the product state.** Stated for any
CQ state `rhoN` on the product alphabet whose blocks factor as the tensor product of the one-copy
blocks. -/
theorem isFeasible_tensorFinProd_maxMixed_pow_minFeasibleLambda_of_stateMap
    {X : Type*} [Fintype X] {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (rhoN : CQState (Fin n → X) (d ^ n)) (rho1 : CQState X d)
    (h_state : ∀ ω : Fin n → X,
      rhoN.stateMap ω = SubDensityOp.tensorFinProd n (fun j => rho1.stateMap (ω j))) :
    isFeasible rhoN (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n)))
      ((minFeasibleLambda rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d))) ^ n) := by
  refine ⟨pow_nonneg
    (minFeasibleLambda_nonneg rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d))) n, ?_⟩
  intro ω
  rw [h_state ω]
  exact tensorFinProd_opLe_pow_minFeasibleLambda_maxMixed rho1 ω

/-- **Upper direction of the fixed-reference product rule.** The optimum of the `n`-fold product
against `M_{d^n}` is at most the `n`-th power of the one-copy optimum against `M_d`:
one-copy feasibility tensorizes, and the infimum is at most any feasible value. -/
theorem minFeasibleLambda_tensorFinProd_maxMixed_le_pow_of_stateMap
    {X : Type*} [Fintype X] {d n : ℕ} [NeZero d] [NeZero (d ^ n)]
    (rhoN : CQState (Fin n → X) (d ^ n)) (rho1 : CQState X d)
    (h_state : ∀ ω : Fin n → X,
      rhoN.stateMap ω = SubDensityOp.tensorFinProd n (fun j => rho1.stateMap (ω j))) :
    minFeasibleLambda rhoN (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))) ≤
      (minFeasibleLambda rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d))) ^ n :=
  csInf_le (minFeasibleLambda_bddBelow rhoN
      (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))))
    (isFeasible_tensorFinProd_maxMixed_pow_minFeasibleLambda_of_stateMap rhoN rho1 h_state)

end InfoTheory.SmoothMinEntropy

end
