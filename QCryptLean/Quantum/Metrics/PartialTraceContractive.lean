import QCryptLean.Quantum.Metrics.TraceNorm.Basic
import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.TensorProducts.PartialTrace
import QCryptLean.Quantum.Metrics.TraceNormDilation
import QCryptLean.Quantum.Channels.CPTP.PartialTraceCPTP

/-!
# Data-processing inequality for trace distance under partial trace

Trace distance is contractive under the partial-trace channel:
`D(Tr_B ρ_AB, Tr_B σ_AB) ≤ D(ρ_AB, σ_AB)`.

This is the standard DPI specialization used by Fuchs–van de Graaf
(`InfoTheory/SmoothMinEntropy/PurifiedDistance.lean`) via
`Quantum.Metrics.traceDistance_contractive_under_partialTraceB`.

## Proof strategy

Trace distance `D(ρ,σ) = ½‖ρ-σ‖₁` equals the operator-variational form
  `D(ρ,σ) = max_M (Tr M ρ - Tr M σ)`, max over POVM effects `M`
  with `0 ≤ M ≤ 1`. The partial trace is a CPTP dual to the inclusion
  `M ↦ M ⊗ 1_B`; its contractivity of trace norm follows by restricting
  the variational max to the subset `{M ⊗ 1_B}`.

The minimal lemma chain is:

1. **Partial-trace variational contractivity.** For any POVM effect `M_A`
   on the `A` factor, `Tr((M_A ⊗ 1_B)·ρ_AB) = Tr(M_A · Tr_B ρ_AB)` — this
   is the very defining identity of `partialTraceB`.
2. **Trace norm variational.** `‖X‖₁ = max_{‖Y‖ ≤ 1} |Tr(Y·X)|` or the
   Hermitian variant `‖X‖₁ = max_{-1 ≤ P ≤ 1 Hermitian} Tr(P·X)`.
3. **Contractivity.** `‖Tr_B X_AB‖₁ ≤ ‖X_AB‖₁` follows by taking
   `Y = P_A ⊗ 1_B` in the partial-trace side and noting
   `‖P_A ⊗ 1_B‖ ≤ ‖P_A‖ ≤ 1`.

All three steps live in separate helper lemmas.

## Main statements
- `Quantum.Metrics.traceDistance_contractive_under_partialTraceB` — DPI for
  trace distance on the `B` factor.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix ComplexOrder

noncomputable section

namespace Quantum.Metrics

/-- **Data-processing inequality for trace distance under partial trace**.

For any bipartite operators `ρ_AB, σ_AB : Op (n * m)`, the trace distance
between their `A`-marginals is at most the bipartite trace distance:

  `D(Tr_B ρ_AB, Tr_B σ_AB) ≤ D(ρ_AB, σ_AB)`.

This is the specialization of DPI (contractivity of trace distance under
CPTP channels) to the partial-trace channel. It is the load-bearing
infrastructure fact behind Fuchs–van de Graaf on normalized density
operators. -/
theorem traceDistance_contractive_under_partialTraceB
    {n m : ℕ} [NeZero n] [NeZero m]
    (ρ_AB σ_AB : Op (n * m)) :
    Quantum.Metrics.traceDistance
        (Quantum.TensorProducts.partialTraceB ρ_AB)
        (Quantum.TensorProducts.partialTraceB σ_AB)
      ≤ Quantum.Metrics.traceDistance ρ_AB σ_AB := by
  -- Unfold: D(A,B) = (1/2) * ‖A - B‖₁
  unfold Quantum.Metrics.traceDistance
  -- Push partialTraceB across subtraction
  rw [← Quantum.TensorProducts.partialTraceB_sub]
  -- Trace-norm contraction by the CPTP partialTraceB channel
  have h := Quantum.Metrics.traceNorm_cptp_contractive_general
    (Quantum.TensorProducts.partialTraceB : Op (n * m) → Op n)
    Quantum.Channels.isCPTP_partialTraceB (ρ_AB - σ_AB)
  -- Multiply by nonnegative 1/2
  have h_half : (0 : ℝ) ≤ 1 / 2 := by norm_num
  exact mul_le_mul_of_nonneg_left h h_half

end Quantum.Metrics

end -- noncomputable section
