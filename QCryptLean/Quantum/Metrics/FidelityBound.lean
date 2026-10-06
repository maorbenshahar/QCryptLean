import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.Metrics.FidelityPurificationBridge
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Fidelity Bound Helper

This module isolates the mixed-state upper bound for the raw matrix expression
appearing in the definition of Uhlmann fidelity, so `TraceNorm/Fidelity.lean`
can remain a thin wrapper around the packaged `DensityOp.fidelity`.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

end Quantum.Metrics
