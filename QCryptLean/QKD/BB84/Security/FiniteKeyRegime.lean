import QCryptLean.QKD.BB84.RealIdeal

/-!
# The elementary regime of the basic memory-free BB84 security row

The smoothing parameter is positive and the soundness edge is at most one half, where binary
entropy is increasing. Block sizes and acceptance probabilities impose no further public
conditions: empty acceptance gives identical channels, and large budgets cover any channel pair.
-/

namespace QKD.BB84.Parameters

/-- The elementary numerical conditions of the basic security row.

`epsilonAEP` is an analysis parameter; it does not change the configured experiment. -/
structure FiniteKeyRegime (p : Parameters) (epsilonAEP : ℝ) : Prop where
  /-- The soundness edge lies in the increasing domain of binary entropy. -/
  belowThreshold : p.errorRate + 2 * p.tolerance ≤ 1 / 2
  /-- The smoothing parameter is positive. -/
  smoothing_pos : 0 < epsilonAEP

end QKD.BB84.Parameters
