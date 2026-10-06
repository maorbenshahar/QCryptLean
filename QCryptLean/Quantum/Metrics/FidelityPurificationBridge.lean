import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.Metrics.SameAncillaPurification
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Fidelity Purification Bridge

This module isolates the remaining upstream-safe bridge needed to bound the raw
mixed-state fidelity expression without importing the downstream trace-norm
development back into `FidelityBound.lean`.

The intended proof route is the same-ancilla purification overlap argument:
identify `Tr √(√ρ · σ · √ρ)` with an ancilla-unitary overlap of canonical
purifications, then bound that overlap by `1`.
-/

open Quantum.Operators Matrix
open _root_.Quantum.Metrics.KitaevWatrousPurification
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-- Purification bridge for the raw mixed-state fidelity expression.

This is the remaining upstream obligation behind
`densityOp_cfcSqrt_sandwich_trace_le_one_viaPurification`.
It is kept in its own helper module so `FidelityBound.lean` can stay cycle-free
while the purification-overlap proof is developed separately. -/
theorem densityOp_cfcSqrt_sandwich_trace_le_one_viaPurification
    {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    letI : PartialOrder (Op n) := Matrix.instPartialOrder
    letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
    letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
    (Matrix.trace (CFC.sqrt (CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp))).re ≤ 1 := by
  rcases sameAncillaPurificationDensity_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich
      ρ σ with ⟨U, hU⟩
  have hbound :=
    sameAncillaPurificationDensity_pureKet_tensorUnitary_overlap_re_le_one ρ σ U
  dsimp at hU hbound
  rw [hU] at hbound
  exact hbound

end Quantum.Metrics
