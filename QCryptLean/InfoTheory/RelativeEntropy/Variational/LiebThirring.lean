import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.Basic.Basic
import QCryptLean.Math.SpectralTheory.Basic
import QCryptLean.Math.SpectralTheory.LiebThirring
import QCryptLean.Quantum.Operators.Types

/-!
# Lieb-Thirring trace inequality: similarity reduction and the dyadic ladder

This file develops the matrix identities used by the variational Holevo-bound argument:
the similarity reduction of `(P · Q)ⁿ` to the square-root sandwich form, the quadratic
case `n = 2`, and the powers-of-two ladder that the Golden-Thompson dyadic Trotter step
consumes.

## Main statements
- `trace_pq_pow_eq_sqrt_form`: similarity reduction from `(P * Q)^n` to the
  positive square-root form `(sqrt P * Q * sqrt P)^n`
- `re_trace_sq_le_trace_conjTranspose_mul`: the matrix Cauchy-Schwarz trace bound
- `lieb_thirring_two`: the quadratic Lieb-Thirring bound
- `lieb_thirring_doubling_core`, `lieb_thirring_doubling`: the doubling kernel and step
- `lieb_thirring_pow_two`: the inequality at the exponents `2ᵏ`

The general integer inequality `tr((P·Q)ⁿ).re ≤ tr(Pⁿ·Qⁿ).re` for every `n ≥ 1`, and
Araki's fractional form, are proved by complex interpolation in
`QCryptLean.Math.SpectralTheory.ArakiLiebThirring`
(`Math.SpectralTheory.alt_trace_product_form`). The dyadic route below is retained
because it is elementary — matrix Cauchy-Schwarz plus the singular-value inequality
`Math.SpectralTheory.trace_pow_mul_conjTranspose_pow_le` — and is what the
Golden-Thompson chain in this directory actually uses.

## References
- Lieb & Thirring (1976)
- Araki, *On an inequality of Lieb and Thirring*, Lett. Math. Phys. 19 (1990), 167-170
- Bhatia, Matrix Analysis, Chapter IX.2
-/

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

/-! ### Similarity reduction and core inequality -/

-- Provide instances needed for CFC.sqrt on matrices
attribute [local instance] Matrix.instPartialOrder
  Matrix.instStarOrderedRing
  Matrix.instNonnegSpectrumClass

/-- Similarity reduction for trace: using P = sqrt(P)*sqrt(P),
    Tr((PQ)^n) = Tr((sqrt(P)*Q*sqrt(P))^n). -/
lemma trace_pq_pow_eq_sqrt_form {N : ℕ}
    (P Q : Matrix (Fin N) (Fin N) ℂ)
    (hP : P.PosSemidef) (n : ℕ) :
    ((P * Q) ^ n).trace =
    ((CFC.sqrt P * Q * CFC.sqrt P) ^ n).trace := by
  -- P = sqrt(P) * sqrt(P)
  have hP_eq : P = CFC.sqrt P * CFC.sqrt P :=
    (CFC.sqrt_mul_sqrt_self P hP.nonneg).symm
  conv_lhs => rw [hP_eq]
  -- (sqrt(P)*sqrt(P)*Q)^n trace = (sqrt(P)*Q*sqrt(P))^n trace
  -- via Tr((AB)^n) = Tr((BA)^n) with A=sqrt(P), B=sqrt(P)*Q
  rw [Matrix.mul_assoc]
  rw [Math.SpectralTheory.trace_pow_mul_comm (CFC.sqrt P) (CFC.sqrt P * Q)]

/-! ### Core inequality -/

/-- Cauchy-Schwarz for matrix traces:
    `Re(Tr(X²)) ≤ Tr(X^H X).re` for any square matrix X.
    This follows from Re(Xij*Xji) ≤ |Xij|^2 entry-wise. -/
lemma re_trace_sq_le_trace_conjTranspose_mul {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℂ) :
    (X ^ 2).trace.re ≤ (Xᴴ * X).trace.re := by
  simp only [Matrix.trace, Matrix.diag, pow_two,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [Complex.re_sum]
  -- Simplify RHS: star(z)*z = ‖z‖²
  simp_rw [Complex.star_def, Complex.conj_mul']
  norm_cast
  -- Goal: ∑ i j, Re(X i j * X j i) ≤ ∑ i j, ‖X j i‖²
  -- Reindex RHS
  rw [Finset.sum_comm
      (f := fun i j => ‖X j i‖ ^ 2)]
  -- Goal: ∑ i j, Re(X i j * X j i) ≤ ∑ i j, ‖X i j‖²
  calc ∑ i, ∑ j, (X i j * X j i).re
      ≤ ∑ i, ∑ j,
          (‖X i j‖ ^ 2 + ‖X j i‖ ^ 2) / 2 := by
        gcongr with i _ j _
        calc (X i j * X j i).re
            ≤ ‖X i j * X j i‖ :=
              Complex.re_le_norm _
          _ = ‖X i j‖ * ‖X j i‖ := norm_mul _ _
          _ ≤ _ := by
              nlinarith [sq_nonneg (‖X i j‖ - ‖X j i‖)]
    _ = (∑ i, ∑ j, (‖X i j‖ ^ 2 + ‖X j i‖ ^ 2)) / 2 := by
        simp_rw [Finset.sum_div]
    _ = (∑ i, ∑ j, ‖X i j‖ ^ 2 +
         ∑ i, ∑ j, ‖X j i‖ ^ 2) / 2 := by
        congr 1
        simp_rw [← Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
        rw [Finset.sum_comm
            (f := fun i j => ‖X j i‖ ^ 2)]
        ring

/-- Cyclically rewrite the quadratic trace term into the `P²Q²` form. -/
private lemma trace_qp_mul_pq_eq_trace_pow_two_mul_pow_two {N : ℕ}
    (P Q : Matrix (Fin N) (Fin N) ℂ) :
    (Q * P * (P * Q)).trace = (P ^ 2 * Q ^ 2).trace := by
  rw [Matrix.mul_assoc Q P (P * Q)]
  rw [← Matrix.mul_assoc P P Q, ← pow_two]
  rw [Matrix.trace_mul_comm Q (P ^ 2 * Q)]
  rw [Matrix.mul_assoc, ← pow_two]

/-- Lieb-Thirring for n=2: Re(Tr((PQ)²)) ≤ Tr(P²Q²).re
    Proof: Re(Tr(X²)) ≤ Tr(X^H X).re applied to X = PQ,
    then Tr((PQ)^H(PQ)) = Tr(QP²Q) = Tr(P²Q²). -/
lemma lieb_thirring_two {N : ℕ}
    (P Q : Matrix (Fin N) (Fin N) ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    ((P * Q) ^ 2).trace.re
    ≤ (P ^ 2 * Q ^ 2).trace.re := by
  have h1 := re_trace_sq_le_trace_conjTranspose_mul (P * Q)
  rw [Matrix.conjTranspose_mul, hP.isHermitian,
      hQ.isHermitian] at h1
  have heq : (Q * P * (P * Q)).trace.re = (P ^ 2 * Q ^ 2).trace.re := by
    exact congrArg Complex.re (trace_qp_mul_pq_eq_trace_pow_two_mul_pow_two P Q)
  rw [heq] at h1
  exact h1

/-! ### Dyadic (powers-of-two) Araki-Lieb-Thirring ladder

The Golden-Thompson dyadic-Trotter-step argument
consumes the integer Lieb-Thirring inequality `tr((PQ)ⁿ).re ≤ tr(PⁿQⁿ).re`
**only at exponents `n = 2ᵏ`** (the dyadic Trotter subsequence). That dyadic
specialization is provable elementarily from the quadratic case
`lieb_thirring_two` together with the matrix Cauchy-Schwarz trace bound
`re_trace_sq_le_trace_conjTranspose_mul`, by induction on `k`, and does **not**
require the antisymmetric-tensor / log-majorization machinery needed for the
general (in particular odd) exponent.

The genuine open residual of the dyadic route is the single doubling kernel
`lieb_thirring_doubling_core`:
`tr((QP)ᵐ (PQ)ᵐ).re ≤ tr((P²Q²)ᵐ).re` for PSD `P,Q`. Everything above it
(`lieb_thirring_doubling`, `lieb_thirring_pow_two`) is proved from it plus
pieces.

Reference: Araki, *On an inequality of Lieb and Thirring*, Lett. Math. Phys. 19
(1990); Bhatia, *Matrix Analysis*, IX.2 (dyadic "easy half"). Used by the
Golden-Thompson / Gibbs variational chain of Nahar, Tupkary, Zhao, Lütkenhaus, Tan
arXiv:2403.11851. -/

/-- Doubling kernel of the dyadic Araki-Lieb-Thirring ladder.

For positive-semidefinite `P, Q` and any `m`:
`tr((Q·P)ᵐ · (P·Q)ᵐ).re ≤ tr((P²·Q²)ᵐ).re`.

This is the single genuine spectral residual of the powers-of-two route: it is
the half of the doubling step `tr((PQ)^{2m}).re ≤ tr((P²Q²)ᵐ).re` not covered
by the matrix Cauchy-Schwarz bound.
Reference: Araki (1990); Bhatia IX.2. -/
lemma lieb_thirring_doubling_core {N : ℕ}
    (P Q : Matrix (Fin N) (Fin N) ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (m : ℕ) :
    ((Q * P) ^ m * (P * Q) ^ m).trace.re ≤ ((P ^ 2 * Q ^ 2) ^ m).trace.re := by
  -- Set `B = Q * P`. Since `P, Q` are Hermitian, `Bᴴ = (Q * P)ᴴ = P * Q`.
  set B : Matrix (Fin N) (Fin N) ℂ := Q * P with hB
  have hBH : Bᴴ = P * Q := by
    rw [hB, Matrix.conjTranspose_mul, hP.isHermitian, hQ.isHermitian]
  -- The general Araki core: `tr(Bᵐ (Bᴴ)ᵐ).re ≤ tr((Bᴴ B)ᵐ).re`.
  have hAraki := Math.SpectralTheory.trace_pow_mul_conjTranspose_pow_le B m
  rw [hBH] at hAraki
  -- LHS matches directly.
  refine le_trans hAraki ?_
  -- `Bᴴ * B = (P * Q) * (Q * P)`; reduce its `m`-th power trace to `(P²Q²)ᵐ`.
  rw [hB]
  -- `(P * Q) * (Q * P) = P * Q ^ 2 * P`.
  have hmid : (P * Q) * (Q * P) = P * (Q ^ 2 * P) := by
    rw [pow_two]; simp only [Matrix.mul_assoc]
  rw [hmid]
  -- cyclicity: `tr((P * (Q² * P))ᵐ) = tr((Q² * P * P)ᵐ) = tr((Q² * P²)ᵐ)`
  rw [Math.SpectralTheory.trace_pow_mul_comm P (Q ^ 2 * P) m]
  -- `(Q² * P) * P = Q² * P²`
  have hcyc : (Q ^ 2 * P) * P = Q ^ 2 * P ^ 2 := by
    rw [Matrix.mul_assoc, ← pow_two]
  rw [hcyc]
  -- final cyclic swap to `(P² * Q²)ᵐ`
  rw [Math.SpectralTheory.trace_pow_mul_comm (Q ^ 2) (P ^ 2) m]

/-- Doubling step of the dyadic Araki-Lieb-Thirring ladder.

For positive-semidefinite `P, Q` and any `m`:
`tr((P·Q)^{2m}).re ≤ tr((P²·Q²)ᵐ).re`.

Proved from the matrix Cauchy-Schwarz trace bound
`re_trace_sq_le_trace_conjTranspose_mul` applied to `X = (P·Q)ᵐ`
(whose conjugate transpose is `(Q·P)ᵐ` since `P, Q` are Hermitian), followed by
the doubling kernel `lieb_thirring_doubling_core`. -/
lemma lieb_thirring_doubling {N : ℕ}
    (P Q : Matrix (Fin N) (Fin N) ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (m : ℕ) :
    ((P * Q) ^ (2 * m)).trace.re ≤ ((P ^ 2 * Q ^ 2) ^ m).trace.re := by
  -- X = (P*Q)^m; X^2 = (P*Q)^(2m)
  have hX2 : (P * Q) ^ (2 * m) = ((P * Q) ^ m) ^ 2 := by
    rw [← pow_mul]; ring_nf
  -- Xᴴ = (Q*P)^m
  have hXH : ((P * Q) ^ m)ᴴ = (Q * P) ^ m := by
    rw [Matrix.conjTranspose_pow, Matrix.conjTranspose_mul, hP.isHermitian, hQ.isHermitian]
  have hCS := re_trace_sq_le_trace_conjTranspose_mul ((P * Q) ^ m)
  rw [hXH] at hCS
  calc ((P * Q) ^ (2 * m)).trace.re
      = (((P * Q) ^ m) ^ 2).trace.re := by rw [hX2]
    _ ≤ ((Q * P) ^ m * (P * Q) ^ m).trace.re := hCS
    _ ≤ ((P ^ 2 * Q ^ 2) ^ m).trace.re := lieb_thirring_doubling_core P Q hP hQ m

/-- Powers-of-two Araki-Lieb-Thirring inequality.

For positive-semidefinite `P, Q` and any `k`:
`tr((P·Q)^{2ᵏ}).re ≤ tr(P^{2ᵏ} · Q^{2ᵏ}).re`.

Proved by induction on `k`. The base case `k = 0` (`2⁰ = 1`) is reflexivity.
The step doubles via `lieb_thirring_doubling` and applies the induction
hypothesis to the squared pair `(P², Q²)`, using `(P²)^{2ᵏ} = P^{2^{k+1}}`.
This is the only form the Golden-Thompson dyadic Trotter argument consumes. -/
lemma lieb_thirring_pow_two {N : ℕ}
    (P Q : Matrix (Fin N) (Fin N) ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (k : ℕ) :
    ((P * Q) ^ (2 ^ k)).trace.re ≤ (P ^ (2 ^ k) * Q ^ (2 ^ k)).trace.re := by
  induction k generalizing P Q with
  | zero => simp
  | succ j ih =>
    -- 2^(j+1) = 2 * 2^j
    have hpow : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
    have hdoub := lieb_thirring_doubling P Q hP hQ (2 ^ j)
    rw [← hpow] at hdoub
    -- IH on the squared pair
    have hih := ih (P ^ 2) (Q ^ 2) (hP.pow 2) (hQ.pow 2)
    -- (P^2)^(2^j) = P^(2^(j+1)) etc.
    have hPsq : (P ^ 2) ^ (2 ^ j) = P ^ (2 ^ (j + 1)) := by
      rw [← pow_mul, hpow, mul_comm]
    have hQsq : (Q ^ 2) ^ (2 ^ j) = Q ^ (2 ^ (j + 1)) := by
      rw [← pow_mul, hpow, mul_comm]
    rw [hPsq, hQsq] at hih
    exact le_trans hdoub hih

end InfoTheory.RelativeEntropy
