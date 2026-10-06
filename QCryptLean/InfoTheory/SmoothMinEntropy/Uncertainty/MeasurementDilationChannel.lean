import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.MeasurementDilation
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.FidelityGenCPTNI
import QCryptLean.Quantum.Channels.CPTP.PartialTraceCPTP
import QCryptLean.Quantum.Channels.CPTP.Reindex

/-!
# The measurement conjugation-trace map is a completely positive sub-channel

`measConjTraceMap W τ = Tr_{X′A}( (W ⊗ 1_B) τ (W ⊗ 1_B)ᴴ )` (`MeasurementDilation.lean`) is the
data-processing map of the Tomamichel–Renner uncertainty argument: conjugate the dilated global
state by the partial isometry `W = U Vᴴ`, then trace out the copy register and the system.  This
file records its **channel certificates**:

* it is `ℂ`-linear and completely positive, unconditionally;
* it is trace-non-increasing on positive-semidefinite inputs when the conjugating operator
  `W ⊗ 1_B` is a sub-isometry, `(W ⊗ 1_B)ᴴ (W ⊗ 1_B) ⪯ 1`.

Together these are the hypotheses of the sub-density-native generalized-fidelity data-processing
inequality `SubDensityOp.fidelityGen_le_fidelityGen_cp_tni` (`FidelityGenCPTNI.lean`), so this file
is what turns the operator-level transport of `MeasurementDilation.lean` into a *metric* transport
on the purified-distance ball (`MeasurementTransport.lean`).

## Proof pattern

Each of the three stages — conjugation, reindex, partial trace — is individually completely
positive: a single-Kraus map, a generalized-permutation Kraus map
(`Quantum.Channels.reindexLinearEquiv_isCPTP`), and the standard `partialTraceB` Kraus map
(`Quantum.Channels.isCPTP_partialTraceB`).  Complete positivity of the composite follows from
closure under composition (`Quantum.Channels.isCompletelyPositive_comp`), and linearity stagewise.
Trace non-increase reduces to the conjugation stage alone: the reindex
(`Matrix.trace_reindex_self`) and the partial trace (`trace_partialTraceB`) preserve the trace
exactly, and the conjugation's trace change is controlled by the Löwner bound through
`trace_mul_le_of_opLe`.

## Main statements

* `InfoTheory.SmoothMinEntropy.measConjTraceMap_isLinearMap`
* `InfoTheory.SmoothMinEntropy.measConjTraceMap_isCompletelyPositive`
* `InfoTheory.SmoothMinEntropy.measConjTraceMap_trace_le`
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **`measConjTraceMap` is linear.** Each stage — conjugation, reindex, partial trace — is
additive and `ℂ`-homogeneous. -/
lemma measConjTraceMap_isLinearMap {d dB : ℕ} (W : Op (d * d * d)) :
    IsLinearMap ℂ (measConjTraceMap (dB := dB) W) where
  map_add := fun τ τ' => by
    unfold measConjTraceMap
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.reindex_add, partialTraceB_add]
  map_smul := fun c τ => by
    unfold measConjTraceMap
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.reindex_smul, partialTraceB_smul]

/-- **`measConjTraceMap` is completely positive**, unconditionally — no isometry hypothesis on `W`
is needed, because complete positivity of a conjugation `τ ↦ K τ Kᴴ` holds for every `K`. The
conjugation by `W ⊗ 1_B` is a single-Kraus CP map (`isCompletelyPositive_of_kraus_sum`), the
reindex is CPTP (`Quantum.Channels.reindexLinearEquiv_isCPTP`), and `partialTraceB` is CPTP
(`Quantum.Channels.isCPTP_partialTraceB`); complete positivity is closed under composition. -/
lemma measConjTraceMap_isCompletelyPositive {d dB : ℕ} [NeZero d] [NeZero dB]
    (W : Op (d * d * d)) :
    Quantum.Channels.IsCompletelyPositive (measConjTraceMap (dB := dB) W) := by
  set K : Op (d * d * d * dB) := Op.tensor W (1 : Op dB) with hK
  set e := measTraceReindex d dB with he
  have hConjCP : Quantum.Channels.IsCompletelyPositive
      (fun τ : Op (d * d * d * dB) => K * τ * Kᴴ) :=
    isCompletelyPositive_of_kraus_sum (fun _ : Unit => K) (fun τ => K * τ * Kᴴ)
      (fun τ => by simp)
  have hReindex := Quantum.Channels.reindexLinearEquiv_isCPTP e
  have hReindexEq : (⇑(Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) =
      (fun N : Op (d * d * d * dB) => Matrix.reindex e e N) := by
    funext N; rfl
  rw [hReindexEq] at hReindex
  have hPartial := Quantum.Channels.isCPTP_partialTraceB (n := d * dB) (m := d * d)
  have hcomp1 : Quantum.Channels.IsCompletelyPositive
      ((fun N : Op (d * d * d * dB) => Matrix.reindex e e N) ∘
        (fun τ : Op (d * d * d * dB) => K * τ * Kᴴ)) :=
    Quantum.Channels.isCompletelyPositive_comp _ _ hReindex.2.1 hConjCP hReindex.1
  have hcomp2 : Quantum.Channels.IsCompletelyPositive
      ((partialTraceB : Op (d * dB * (d * d)) → Op (d * dB)) ∘
        ((fun N : Op (d * d * d * dB) => Matrix.reindex e e N) ∘
          (fun τ : Op (d * d * d * dB) => K * τ * Kᴴ))) :=
    Quantum.Channels.isCompletelyPositive_comp _ _ hPartial.2.1 hcomp1 hPartial.1
  have hEq : measConjTraceMap (dB := dB) W =
      (partialTraceB : Op (d * dB * (d * d)) → Op (d * dB)) ∘
        ((fun N : Op (d * d * d * dB) => Matrix.reindex e e N) ∘
          (fun τ : Op (d * d * d * dB) => K * τ * Kᴴ)) := by
    funext τ; rfl
  rw [hEq]
  exact hcomp2

/-- **Trace non-increase of `measConjTraceMap`** on positive-semidefinite inputs, given the
sub-isometry bound `(W ⊗ 1_B)ᴴ (W ⊗ 1_B) ⪯ 1`. The conjugation is the only lossy stage: the
reindex (`Matrix.trace_reindex_self`) and the partial trace (`trace_partialTraceB`) preserve the
trace exactly, and `Tr(K A Kᴴ) = Tr(A · KᴴK) ≤ Tr(A · 1) = Tr A` by `trace_mul_le_of_opLe`. -/
lemma measConjTraceMap_trace_le {d dB : ℕ}
    (W : Op (d * d * d))
    (hW : opLe ((Op.tensor W (1 : Op dB))ᴴ * (Op.tensor W (1 : Op dB))) 1)
    (A : Op (d * d * d * dB)) (hA : A.PosSemidef) :
    (measConjTraceMap (dB := dB) W A).trace.re ≤ A.trace.re := by
  set K : Op (d * d * d * dB) := Op.tensor W (1 : Op dB) with hK
  unfold measConjTraceMap
  rw [Quantum.TensorProducts.trace_partialTraceB, Matrix.trace_reindex_self]
  have hcyc : (K * A * Kᴴ).trace = (A * (Kᴴ * K)).trace := by
    rw [Matrix.trace_mul_cycle K A Kᴴ, Matrix.trace_mul_comm]
  rw [hcyc]
  calc (A * (Kᴴ * K)).trace.re
      ≤ (A * (1 : Op (d * d * d * dB))).trace.re :=
        trace_mul_le_of_opLe hA (Matrix.posSemidef_conjTranspose_mul_self K).isHermitian
          Matrix.isHermitian_one hW
    _ = A.trace.re := by rw [Matrix.mul_one]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
