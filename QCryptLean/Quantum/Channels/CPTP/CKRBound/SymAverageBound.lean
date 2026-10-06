import QCryptLean.QKD.BB84.Engine.InnerBudget.SiftedPassSupport
import QCryptLean.Quantum.Channels.CPTP.CKRBound.SignalPermutationInvariance

/-!
# The register-generic paired symmetrization lift

The register-generic bridge underlying the paired-permutation-invariant CKR trace-norm reduction:
any CKR tensor trace-norm difference that expands as a `(1/n!)`-scaled permutation average of
per-`π` summands `announce π ∘ (Δbase ∘ permuteSignalLinear n π)` — with each announcement map
CPTP and `Δbase` the fixed-selector base-scheme difference — is bounded by any bound on the base
difference, at a paired permutation-invariant square reference `τ`. The announcement map and the
enlarged output register are left abstract, so both an announce-only symmetrization and a
PE-announce symmetrization instantiate it. Channel-independent; no BB84 or QKD-protocol object.

The lone substantive step — stripping the input-side `permuteSignalLinear n π` pre-factor — is
discharged by the channel-generic lemma
`ckrTensorTraceNorm_precomp_permuteSignal_pairedPermInvariant_eq_aux`, which rests only on
`IsPairedPermInvariant τ` and unitary-conjugation contractivity.

## Main results

* `ckrTensorTraceNorm_symAverage_le_of_baseScheme_bound_generic` — the paired symmetrization lift.

## References

Renner 2005 (`arXiv:quant-ph/0512258v2`, §5/§6.5); Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(`arXiv:2403.11851`, Thm 3).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.QuantumLHL
open Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- **The base-opaque paired symmetrization lift** (register-generic engine).

Any CKR tensor trace-norm difference `symDiff` that expands as the `(1/n!)`-scaled permutation
average of per-`π` summands `announce π ∘ (Δbase ∘ permuteSignalLinear n π)` — with each
announcement map `announce π` CPTP and `Δbase` the fixed-selector base-scheme difference — is
bounded by any bound `B` on the base difference `ckrTensorTraceNorm Δbase τ`, on a paired
permutation-invariant square reference `τ`.

The per-`π` announcement CPTP contraction strips `announce π`, the paired-invariance strip removes
`permuteSignalLinear n π`, and the triangle inequality over `Perm (Fin n)` collapses the
`(1/n!)·n!` factor.  The enlarged output register `dimOut` is a free parameter, so both an
announce-only symmetrization and a PE-announce symmetrization instantiate it. -/
lemma ckrTensorTraceNorm_symAverage_le_of_baseScheme_bound_generic
    {n dimBase dimOut : ℕ} [NeZero n] [NeZero (4 ^ n)]
    [NeZero dimBase] [NeZero dimOut]
    (Δbase : Op (4 ^ n) →ₗ[ℂ] Op dimBase)
    (announce : Equiv.Perm (Fin n) → (Op dimBase →ₗ[ℂ] Op dimOut))
    (hAnnounceCPTP : ∀ π : Equiv.Perm (Fin n), IsCPTP (⇑(announce π)))
    (symDiff : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((4 ^ n) * (4 ^ n)))
    (hτ_paired : IsPairedPermInvariant τ) {B : ℝ}
    (hexpand : symDiff =
      (1 / (n.factorial : ℂ)) •
        ∑ π : Equiv.Perm (Fin n),
          (announce π).comp (Δbase.comp (permuteSignalLinear n π)))
    (hBase : ckrTensorTraceNorm Δbase τ ≤ B) :
    ckrTensorTraceNorm symDiff τ ≤ B := by
  -- Per-`π` summand bound: strip the announcement (CPTP contraction), then the paired-invariant
  -- `permuteSignalLinear`, then the fixed-selector base bound `hBase`.
  have hsummand : ∀ π : Equiv.Perm (Fin n),
      Quantum.Metrics.traceNorm
        (mapTensorId ((announce π).comp (Δbase.comp (permuteSignalLinear n π))) τ.toOp) ≤ B := by
    intro π
    have h : ckrTensorTraceNorm
        ((announce π).comp (Δbase.comp (permuteSignalLinear n π))) τ ≤ B := by
      calc ckrTensorTraceNorm ((announce π).comp (Δbase.comp (permuteSignalLinear n π))) τ
          ≤ ckrTensorTraceNorm (Δbase.comp (permuteSignalLinear n π)) τ :=
            ckrTensorTraceNorm_postcomp_cptp_le (announce π) (hAnnounceCPTP π)
              (Δbase.comp (permuteSignalLinear n π)) τ
        _ = ckrTensorTraceNorm Δbase τ :=
            ckrTensorTraceNorm_precomp_permuteSignal_pairedPermInvariant_eq_aux
              Δbase τ hτ_paired π
        _ ≤ B := hBase
    exact h
  rw [hexpand]
  simp only [ckrTensorTraceNorm, mapTensorId_linearMap_smul, mapTensorId_linearMap_sum]
  rw [Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]
  have htri : Quantum.Metrics.traceNorm
      (∑ π : Equiv.Perm (Fin n),
        mapTensorId ((announce π).comp (Δbase.comp (permuteSignalLinear n π))) τ.toOp) ≤
      ∑ π : Equiv.Perm (Fin n),
        Quantum.Metrics.traceNorm
          (mapTensorId ((announce π).comp (Δbase.comp (permuteSignalLinear n π))) τ.toOp) :=
    Quantum.Metrics.traceNorm_sum_le Finset.univ _
  have hsum_le : ∑ π : Equiv.Perm (Fin n),
      Quantum.Metrics.traceNorm
        (mapTensorId ((announce π).comp (Δbase.comp (permuteSignalLinear n π))) τ.toOp) ≤
      (n.factorial : ℝ) * B := by
    calc ∑ π : Equiv.Perm (Fin n), _ ≤ ∑ _π : Equiv.Perm (Fin n), B :=
          Finset.sum_le_sum (fun π _ => hsummand π)
      _ = (n.factorial : ℝ) * B := by
          simp [Fintype.card_perm, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul]
  have hnorm_fac : ‖(1 / (n.factorial : ℂ))‖ = 1 / (n.factorial : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  calc ‖(1 / (n.factorial : ℂ))‖ * Quantum.Metrics.traceNorm
        (∑ π : Equiv.Perm (Fin n),
          mapTensorId ((announce π).comp (Δbase.comp (permuteSignalLinear n π))) τ.toOp)
      ≤ ‖(1 / (n.factorial : ℂ))‖ * ((n.factorial : ℝ) * B) :=
        mul_le_mul_of_nonneg_left (htri.trans hsum_le) (norm_nonneg _)
    _ = B := by
        rw [hnorm_fac]
        field_simp

end Quantum.Channels
