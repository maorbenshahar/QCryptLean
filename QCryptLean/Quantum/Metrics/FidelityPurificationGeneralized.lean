import QCryptLean.Quantum.Metrics.FidelityPurificationMax
import QCryptLean.Quantum.Metrics.RectangularPolar

/-!
# Uhlmann Upper Bound — Generalized Ancilla

This file proves the **generalized-ancilla** form of Uhlmann's upper bound
(Watrous Prop. 3.13 (i) with arbitrary ancilla dimension):

For any two density operators `ρ, τ : DensityOp d`, any nonzero ancilla
dimension `a`, and any pair of normalized purifications
`ψρ, ψτ : Ket (d * a)` whose right-factor partial traces recover `ρ` and
`τ` respectively, the bra–ket overlap is bounded by the Uhlmann fidelity:

    `‖⟨ψρ | ψτ⟩‖ ≤ F(ρ, τ)`.

The same-ancilla form `fidelity_ge_purification_overlap_norm` (with
`a = d`) is proved in `FidelityPurificationMax.lean`; the generalized-
ancilla form follows from the rectangular-polar overlap bound
(`Quantum.Metrics.RectangularPolar.norm_overlap_le_fidelity_of_polar`)
and is needed for the density-operator partial-trace monotonicity
statement `fidelity_le_fidelity_partialTraceB_ofDensity` proved in
`FidelityPartialTraceMonotone.lean`.

## Main statements

* `Quantum.Metrics.RectangularPolar.norm_overlap_le_fidelity_of_polar` — generalized-
  ancilla Uhlmann upper bound.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

end Quantum.Metrics

end -- noncomputable section
