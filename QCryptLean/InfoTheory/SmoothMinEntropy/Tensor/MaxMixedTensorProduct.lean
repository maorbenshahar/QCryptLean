import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.MaxMixedTensorProduct.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.MaxMixedTensorProduct.LowerBound

/-!
# The fixed-reference product rule against maximally mixed references

Entry point of the MaxMixedTensorProduct family. It combines the two directions proved in the
children into the `n`-fold product rule for the minimal feasible scalar of a CQ state against
maximally mixed calibration references.

## The contract

For a one-copy CQ state `ρ₁` on an alphabet `X` with a `d`-dimensional quantum register, and an
`n`-copy CQ state `ρ_N` on `Fin n → X` with a `d^n`-dimensional register whose blocks factor
blockwise as the tensor product of the one-copy blocks,

`λ(ρ_N | M_{d^n}) = λ(ρ₁ | M_d) ^ n`,

where `λ(ρ|σ) = minFeasibleLambda ρ σ = inf {t ≥ 0 : ∀ x, ρ_A(x) ≼ t·σ}` and
`H_min(ρ|σ) = -log₂ λ(ρ|σ)` (Renner, arXiv:quant-ph/0512258v2, Definition 3.1.1). Taking `-log₂`
turns the statement into the tensor additivity `H_min(ρ_N|M_{d^n}) = n · H_min(ρ₁|M_d)`.

## What this is and is not

* It is the **fixed-reference, nonsmooth** additivity of Renner's Lemma 3.1.11 (`lem:HRindadd`),
  specialised to `n` equal factors and to the maximally mixed reference on each factor. The
  reference is not optimized over, and no smoothing is involved.
* It is **not** the smooth superadditivity `lem:Hminindaddsmooth` of the same source, and it makes
  no claim about the reference-optimized `H_min(A|B)` or about `H_min^ε`.
* The blockwise factorization `h_state` is an explicit hypothesis, not a derived property of
  `ρ_N`: it is what identifies `ρ_N` as the `n`-fold product experiment.
* Both `d ≠ 0` and `n ≠ 0` are needed: `d ≠ 0` for the maximally mixed reference to exist, and
  `n ≠ 0` for the `n`-th root in the lower bound.

## Main statement

* `minFeasibleLambda_tensorFinProd_maxMixed_eq_pow_of_stateMap`.
-/

open Quantum.Operators

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Product rule for the minimal feasible scalar against maximally mixed references.**

If every block of the `n`-copy CQ state `rhoN` is the tensor product of the corresponding one-copy
blocks of `rho1`, then the optimal scalar of `rhoN` against the `n`-copy maximally mixed reference
is exactly the `n`-th power of the one-copy optimal scalar against the one-copy maximally mixed
reference. Equivalently, `H_min(ρ_N|M_{d^n}) = n · H_min(ρ₁|M_d)`.

This is Renner, arXiv:quant-ph/0512258v2, Lemma 3.1.11 (`lem:HRindadd`), for `n` equal factors at a
fixed maximally mixed reference; it is nonsmooth and does not optimize over the reference.

The `≤` direction is `minFeasibleLambda_tensorFinProd_maxMixed_le_pow_of_stateMap` (tensorization
of one-copy feasibility) and the `≥` direction is
`pow_minFeasibleLambda_le_tensorFinProd_maxMixed_of_stateMap` (spectral extraction of a one-copy
domination from an `n`-copy one). -/
theorem minFeasibleLambda_tensorFinProd_maxMixed_eq_pow_of_stateMap
    {X : Type*} [Fintype X] {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (rhoN : CQState (Fin n → X) (d ^ n)) (rho1 : CQState X d)
    (h_state : ∀ ω : Fin n → X,
      rhoN.stateMap ω = SubDensityOp.tensorFinProd n (fun j => rho1.stateMap (ω j))) :
    minFeasibleLambda rhoN (DensityOp.toSubDensityOp (DensityOp.maxMixed (d ^ n))) =
      (minFeasibleLambda rho1 (DensityOp.toSubDensityOp (DensityOp.maxMixed d))) ^ n :=
  le_antisymm
    (minFeasibleLambda_tensorFinProd_maxMixed_le_pow_of_stateMap rhoN rho1 h_state)
    (pow_minFeasibleLambda_le_tensorFinProd_maxMixed_of_stateMap rhoN rho1 h_state)

end InfoTheory.SmoothMinEntropy

end
