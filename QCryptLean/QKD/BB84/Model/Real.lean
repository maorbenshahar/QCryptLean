import QCryptLean.Quantum.Channels.CPTP.BlockPinchingChannel
import QCryptLean.QKD.BB84.Constants

/-!
# An outcome/Eve-register resolution-of-identity summation lemma

A generic Kraus-completeness helper: summing the diagonal projector over every
outcome-string/Eve-register pair resolves the identity on the combined register.

## Main results

* `bb84OutcomeEve_single_sum` — the outcome/Eve diagonal projectors sum to the identity.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

namespace bb84

/-- Summing the diagonal projector over every outcome-string/Eve-register pair, under the
`4^n * eveDim` indexing, resolves the identity on the combined register. -/
lemma bb84OutcomeEve_single_sum (n eveDim : ℕ)
    [NeZero (4 ^ n)] [NeZero eveDim] :
    (∑ p : (Fin n → Fin signalDim) × Fin eveDim,
      Matrix.single (finProdFinEquiv (finFunctionFinEquiv p.1, p.2))
        (finProdFinEquiv (finFunctionFinEquiv p.1, p.2)) (1 : ℂ)) =
      (1 : Op (4 ^ n * eveDim)) := by
  let e : ((Fin n → Fin signalDim) × Fin eveDim) ≃
      (Fin (4 ^ n) × Fin eveDim) :=
    (finFunctionFinEquiv (n := n) (m := signalDim)).prodCongr
      (Equiv.refl (Fin eveDim))
  calc
    (∑ p : (Fin n → Fin signalDim) × Fin eveDim,
      Matrix.single (finProdFinEquiv (finFunctionFinEquiv p.1, p.2))
        (finProdFinEquiv (finFunctionFinEquiv p.1, p.2)) (1 : ℂ))
        = ∑ p : Fin (4 ^ n) × Fin eveDim,
            Matrix.single (finProdFinEquiv p) (finProdFinEquiv p) (1 : ℂ) := by
          exact Equiv.sum_comp e
            (fun p : Fin (4 ^ n) × Fin eveDim =>
              Matrix.single (finProdFinEquiv p) (finProdFinEquiv p) (1 : ℂ))
    _ = ∑ i : Fin (4 ^ n * eveDim), Matrix.single i i (1 : ℂ) := by
          exact Equiv.sum_comp finProdFinEquiv
            (fun i : Fin (4 ^ n * eveDim) => Matrix.single i i (1 : ℂ))
    _ = 1 := Matrix.sum_single_one

end bb84

end QKD.BB84.Model

end -- noncomputable section
