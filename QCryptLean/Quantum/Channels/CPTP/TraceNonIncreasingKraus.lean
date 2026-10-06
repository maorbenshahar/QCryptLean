import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# Trace-non-increasing Kraus maps (CP sub-channels)

A completely positive **sub-channel** (trace-non-increasing CP map) is the honest
operator-theoretic primitive behind quantum postselection / extraction: it is a Kraus
map whose completeness relation is the Löwner sub-identity `∑ᵢ Kᵢ† Kᵢ ⪯ 1` rather than
the equality `∑ᵢ Kᵢ† Kᵢ = 1` of a trace-preserving channel.  Its action on a positive
operator can lose trace (the postselection / filtering loss), so it sends a normalized
state to a sub-normalized one.

This is exactly the structure CKR postselection / `lem:extractpart` extraction needs:
the extraction map `𝒯` discards the rejected mass, so it is trace-non-increasing, not
trace-preserving.  Modelling it as a `KrausRepresentation` (trace-preserving) would force
its image to carry the same trace as its input — a soundness defect when the input is the
full de Finetti mixture and the output must match a PE-filtered sub-normalized state.

## Main definitions

- `TraceNonIncreasingKraus n m`: Kraus data `{Kᵢ}` with `∑ᵢ Kᵢ† Kᵢ ⪯ 1`
  (phrased as `(1 - ∑ᵢ Kᵢ† Kᵢ).PosSemidef`).
- `TraceNonIncreasingKraus.applyOp`: the map `A ↦ ∑ᵢ Kᵢ A Kᵢ†` (same formula as a
  full channel).

## Main statements

- `TraceNonIncreasingKraus.applyOp_posSemidef`: the image of a PSD operator is PSD
  (complete positivity).
- `TraceNonIncreasingKraus.applyOp_trace_re_le`: `Tr(applyOp ρ).re ≤ Tr(ρ).re` for PSD
  `ρ` (trace non-increase, the postselection loss).
- `KrausRepresentation.toTraceNonIncreasing`: every (trace-preserving) Kraus channel is a
  trace-non-increasing Kraus map (the sub-identity holds with equality).
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- A **completely positive trace-non-increasing** Kraus map (a CP sub-channel).

Kraus operators `{Kᵢ : H_in → H_out}` satisfying the Löwner sub-completeness relation
`∑ᵢ Kᵢ† Kᵢ ⪯ 1`, recorded as the positive-semidefiniteness of `1 - ∑ᵢ Kᵢ† Kᵢ`.  The
action `A ↦ ∑ᵢ Kᵢ A Kᵢ†` is completely positive and trace-non-increasing: it can lose
trace, modelling the postselection / extraction loss that a trace-preserving
`KrausRepresentation` cannot represent. -/
structure TraceNonIncreasingKraus (n m : ℕ) where
  /-- Number of Kraus operators. -/
  numOps : ℕ
  /-- The Kraus operators `Kᵢ : H_in → H_out`. -/
  operators : Fin numOps → Matrix (Fin m) (Fin n) ℂ
  /-- Sub-completeness relation `∑ᵢ Kᵢ† Kᵢ ⪯ 1`, recorded as `1 - ∑ᵢ Kᵢ† Kᵢ ⪰ 0`.
      This is the trace-non-increase condition (with equality it is trace preservation). -/
  subCompleteness : ((1 : Op n) - ∑ i, (operators i)† * (operators i)).PosSemidef

namespace TraceNonIncreasingKraus

/-- The action of a trace-non-increasing Kraus map on a general operator:
`Φ(A) = ∑ᵢ Kᵢ A Kᵢ†`.  Same formula as a full channel; the difference is only the
sub-completeness relation. -/
def applyOp {n m : ℕ} (K : TraceNonIncreasingKraus n m) (A : Op n) : Op m :=
  ∑ i, K.operators i * A * (K.operators i)†

/-- **Complete positivity.**  The image of a positive-semidefinite operator under a
trace-non-increasing Kraus map is positive semidefinite. -/
theorem applyOp_posSemidef {n m : ℕ} (K : TraceNonIncreasingKraus n m)
    {A : Op n} (hA : A.PosSemidef) : (K.applyOp A).PosSemidef := by
  refine Matrix.posSemidef_sum Finset.univ (fun i _ => ?_)
  simpa using hA.mul_mul_conjTranspose_same (K.operators i)

/-- The image of a PSD operator `A` has trace
`Tr(applyOp A) = Tr((∑ᵢ Kᵢ† Kᵢ) A)`: cyclicity of the trace moves each `Kᵢ†` to the
left of `Kᵢ A`, and the sum factors through `∑ᵢ Kᵢ† Kᵢ`. -/
theorem applyOp_trace_eq {n m : ℕ} (K : TraceNonIncreasingKraus n m) (A : Op n) :
    (K.applyOp A).trace = ((∑ i, (K.operators i)† * K.operators i) * A).trace := by
  simp only [applyOp]
  rw [Matrix.trace_sum Finset.univ]
  have h_cyc : ∀ i, (K.operators i * A * (K.operators i)†).trace =
      ((K.operators i)† * K.operators i * A).trace := by
    intro i; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp_rw [h_cyc, ← Matrix.trace_sum Finset.univ, ← Finset.sum_mul]

/-- **Trace non-increase** (the postselection loss).  For a positive-semidefinite input
`ρ`, the real part of the trace does not increase: `Tr(applyOp ρ).re ≤ Tr(ρ).re`.

The gap `Tr(ρ).re - Tr(applyOp ρ).re = Tr((1 - ∑ᵢ Kᵢ† Kᵢ) ρ).re ≥ 0` is non-negative
because both `1 - ∑ᵢ Kᵢ† Kᵢ` (sub-completeness) and `ρ` are PSD. -/
theorem applyOp_trace_re_le {n m : ℕ} (K : TraceNonIncreasingKraus n m)
    {ρ : Op n} (hρ : ρ.PosSemidef) : (K.applyOp ρ).trace.re ≤ ρ.trace.re := by
  have hgap : 0 ≤ (((1 : Op n) - ∑ i, (K.operators i)† * K.operators i) * ρ).trace.re :=
    Quantum.Operators.trace_mul_psd_nonneg _ ρ K.subCompleteness hρ
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul, Complex.sub_re, sub_nonneg] at hgap
  rw [applyOp_trace_eq]
  exact hgap

end TraceNonIncreasingKraus

/-- Every (trace-preserving) Kraus channel is a trace-non-increasing Kraus map: the
sub-completeness `∑ᵢ Kᵢ† Kᵢ ⪯ 1` holds with equality, so `1 - ∑ᵢ Kᵢ† Kᵢ = 0 ⪰ 0`. -/
def KrausRepresentation.toTraceNonIncreasing {n m : ℕ}
    (K : KrausRepresentation n m) : TraceNonIncreasingKraus n m where
  numOps := K.numOps
  operators := K.operators
  subCompleteness := by
    rw [K.completeness, sub_self]
    exact Matrix.PosSemidef.zero

@[simp] lemma KrausRepresentation.toTraceNonIncreasing_applyOp {n m : ℕ}
    (K : KrausRepresentation n m) (A : Op n) :
    K.toTraceNonIncreasing.applyOp A = K.applyOp A := rfl

end Quantum.Channels

end
