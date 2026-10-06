import QCryptLean.InfoTheory.QuantumLHL.CollisionAnnounceCharge

/-!
# Dropping a keep-filter is monotone for the collision quantity

`CQState.filterKeep keep ρ` zeroes every conditional block outside the keep set and leaves the
kept ones untouched (`CQState.filterKeep_stateMap`).  Since `collisionQuantity` is a sum of
`weightedFrobeniusSq` terms and each term is nonnegative
(`InfoTheory.QuantumLHL.weightedFrobeniusSq_nonneg`), discarding blocks can only *lower* the
collision quantity — the filtered state is never harder to extract from than the unfiltered one.

## The gap this closes

The collision route reaches privacy amplification with the LOCC parameter-estimation accept
filter `bb84SiftedLocalPETestPassed` already applied to the round-outcome register, whereas the
kept-block reference chain and the register-extension collapse above it is stated on the
*unfiltered* state.  A collision floor
proved without the filter therefore does not transfer by rewriting — it transfers by this
inequality, which is the one direction that is true and the only one the route needs.

This is the collision-route analogue of the smooth-min-entropy filter step: there filtering can
only *raise* the smooth min entropy, here it can only *lower* `2^{-H₂}`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- **Filtering a CQ state cannot increase its collision quantity.**  Blocks outside the keep set
are replaced by `0`, whose `weightedFrobeniusSq` is `0`, and every surviving block is unchanged;
nonnegativity of `weightedFrobeniusSq` then gives the termwise inequality.

Closes the filter gap on the collision route: a collision-quantity bound proved for the
unfiltered round-outcome state dominates the one for the accept-filtered state, so the PE accept
filter may be dropped before the kept-block reference chain is applied. -/
theorem collisionQuantity_filterKeep_le {Xc : Type*} [Fintype Xc] {d : ℕ}
    (σ : Op d) (keep : Xc → Bool) (ρ : CQState Xc d) :
    collisionQuantity σ (fun x => ((CQState.filterKeep keep ρ).stateMap x).toOp)
      ≤ collisionQuantity σ (fun x => (ρ.stateMap x).toOp) := by
  classical
  refine Finset.sum_le_sum fun x _ => ?_
  simp only [CQState.filterKeep_stateMap]
  by_cases hx : keep x
  · simp only [hx, ite_true, le_refl]
  · simp only [hx, Bool.false_eq_true, ite_false]
    rw [show ((0 : SubDensityOp d).toOp) = 0 from rfl, weightedFrobeniusSq_zero]
    exact weightedFrobeniusSq_nonneg _ _

end InfoTheory.QuantumLHL

end
