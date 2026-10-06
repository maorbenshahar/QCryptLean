import QCryptLean.InfoTheory.DistanceBounds.AcceptSplit
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.FidelityGenCPTNI
import QCryptLean.Quantum.Channels.CPTP.CKRBound.GeneralContractivity

/-!
# Trace-distance data processing under CP trace-non-increasing maps

The accept-region split of the CKR de Finetti security argument factors the real and ideal
privacy-amplification outputs through a map `Λ` that is completely positive and
*trace-non-increasing*
(it produces the accepting Eve-marginal block, which carries only the accept-weight `≤ 1`), but is
not
trace-preserving.  The trace-distance data-processing lemma already in the library,
`InfoTheory.CKRPostselection.traceDistanceGen_cptp_le`, needs a genuine CPTP (trace-*preserving*)
map,
so it does not apply to `Λ` directly.

This file supplies the trace-non-increasing strengthening: the generalized trace distance
`D(·,·) = ½‖·−·‖₁ + ½|Δtr.re|` (Tomamichel 2016, eq. 3.23) contracts through any completely
positive,
trace-non-increasing map.  It is the trace-distance counterpart of the generalized-fidelity result
`InfoTheory.SmoothMinEntropy.SubDensityOp.fidelityGen_le_fidelityGen_cp_tni`, and reuses the *same*
block-diagonal CPTP completion `InfoTheory.SmoothMinEntropy.cptnDilationMap` (Tomamichel's
one-extra-
dimension dilation `ρ ↦ ρ ⊕ (1 − tr ρ)`, routing the lost weight into a fresh output dimension)
together
with its already-proved complete-positivity and trace-preservation.

## Main statements
- `traceDistanceGen_le_of_cp_tni`: `D(Φρ, Φσ) ≤ D(ρ, σ)` for `ρ, σ` sub-normalized with explicit
  sub-normalized image witnesses `ρ', σ'` (`ρ'.toOp = Φ ρ.toOp`, `σ'.toOp = Φ σ.toOp`).
- `traceDistanceGen_cp_tni_le`: the bare-`Op` corollary, with the images reconstructed internally
from
  complete positivity (`Quantum.Channels.cp_linear_preserves_posSemidef`) and trace non-increase.

## References
- Christandl-König-Renner (2009), arXiv:0809.3019 (main.tex 489-507): accept-region split.
- Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), arXiv:2403.11851, Theorem 3, main.tex:1341–:1413
(Appendix B's proof of Theorem 3: the accept-block split `\label{eq:tausplit}`
(main.tex:1356–:1362), the Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed
min-entropy bound `\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting
step `\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413): transport of
the
  IID-reference leftover-hashing distance through the accept map `Λ`.
- Tomamichel (2016), §3.2 / Lemma 3.5: generalized trace distance and its data-processing inequality
  via the one-extra-dimension block completion `ρ ↦ ρ ⊕ (1 − tr ρ)`.
-/

open Quantum.Operators Quantum.Channels Quantum.Metrics InfoTheory.SmoothMinEntropy
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.CKRPostselection

/-- **Generalized trace distance is non-increasing under a CP trace-non-increasing map**
(sub-channel data-processing inequality, witness form).

For sub-normalized `ρ, σ : SubDensityOp dIn`, a completely positive map `Φ : Op dIn → Op dOut` that
is
*trace-non-increasing* on PSD inputs (`(Φ A).trace.re ≤ A.trace.re` for `A.PosSemidef`), and
sub-normalized targets `ρ', σ' : SubDensityOp dOut` realizing the images blockwise
(`ρ'.toOp = Φ ρ.toOp`, `σ'.toOp = Φ σ.toOp`), the generalized trace distance does not increase:
`D(Φρ, Φσ) ≤ D(ρ, σ)`.

This is the trace-distance analogue of
`InfoTheory.SmoothMinEntropy.SubDensityOp.fidelityGen_le_fidelityGen_cp_tni` and mirrors its proof.
Completing `Φ` to a *normalized* CPTP dilation on one extra dimension
(`InfoTheory.SmoothMinEntropy.cptnDilationMap`, which is linear, completely positive and
trace-preserving by `cptnDilationMap_isLinearMap`, `cptnDilationMap_isCompletelyPositive` — using
`htni` — and `cptnDilationMap_isTracePreserving`), the dilation sends each normalized extension
`ρ ⊕ (1 − tr ρ)` to the extension of its image (`cptnDilationMap_extendOp`).  The block-diagonal
trace-distance identity `toDensityOpExtend_traceDistance` then turns `D(ρ, σ)` into the *standard*
trace distance of the trace-1 extensions, where the CPTP data-processing inequality
`traceDistanceGen_cptp_le` applies.

Linearity (`hlin`) is a separate hypothesis because this repo's `IsCompletelyPositive` is a Choi-PSD
predicate that does not bundle linearity, exactly as in the fidelity analogue. -/
theorem traceDistanceGen_le_of_cp_tni
    {dIn dOut : ℕ} [NeZero dIn] [NeZero dOut]
    (Φ : Op dIn → Op dOut)
    (hlin : IsLinearMap ℂ Φ)
    (hcp : IsCompletelyPositive Φ)
    (htni : ∀ A : Op dIn, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re)
    (ρ σ : SubDensityOp dIn) (ρ' σ' : SubDensityOp dOut)
    (hρ' : ρ'.toOp = Φ ρ.toOp) (hσ' : σ'.toOp = Φ σ.toOp) :
    traceDistanceGen ρ'.toOp σ'.toOp ≤ traceDistanceGen ρ.toOp σ.toOp := by
  -- The block-diagonal CPTP completion of `Φ` on one extra dimension.
  have hΨ : IsCPTP (cptnDilationMap Φ) :=
    ⟨cptnDilationMap_isLinearMap Φ hlin,
     cptnDilationMap_isCompletelyPositive Φ hlin hcp htni,
     cptnDilationMap_isTracePreserving Φ⟩
  -- Output side: `D(ρ', σ')` is the standard trace distance of the trace-1 extensions.
  have hout : traceDistanceGen ρ'.toOp σ'.toOp
      = traceDistanceGen ρ'.extendOp σ'.extendOp := by
    rw [← toDensityOpExtend_traceDistance ρ' σ']
    exact (traceDistanceGen_eq_traceDistance _ _
      (by rw [toDensityOpExtend_trace ρ', toDensityOpExtend_trace σ'])).symm
  -- Input side: likewise for `D(ρ, σ)`.
  have hin : traceDistanceGen ρ.toOp σ.toOp
      = traceDistanceGen ρ.extendOp σ.extendOp := by
    rw [← toDensityOpExtend_traceDistance ρ σ]
    exact (traceDistanceGen_eq_traceDistance _ _
      (by rw [toDensityOpExtend_trace ρ, toDensityOpExtend_trace σ])).symm
  rw [hout, hin]
  -- The dilation maps the extension of each state to the extension of its image.
  calc traceDistanceGen ρ'.extendOp σ'.extendOp
      = traceDistanceGen (cptnDilationMap Φ ρ.extendOp) (cptnDilationMap Φ σ.extendOp) := by
        rw [cptnDilationMap_extendOp Φ ρ ρ' hρ', cptnDilationMap_extendOp Φ σ σ' hσ']
    _ ≤ traceDistanceGen ρ.extendOp σ.extendOp :=
        traceDistanceGen_cptp_le (cptnDilationMap Φ) hΨ ρ.extendOp σ.extendOp

/-- **Generalized trace distance contraction under a CP trace-non-increasing map** (bare-`Op` form).

The version directly consumable by the BB84 accept-block transfer: for positive-semidefinite,
sub-normalized inputs `ρ, σ : Op dIn` and a completely positive, trace-non-increasing linear map
`Φ`,
`D(Φ ρ, Φ σ) ≤ D(ρ, σ)`.

The sub-normalized wrappers and the image witnesses are reconstructed internally: the images `Φ ρ, Φ
σ`
are PSD by `Quantum.Channels.cp_linear_preserves_posSemidef`, and sub-normalized because `Φ` is
trace-non-increasing (`(Φ ρ).trace.re ≤ ρ.trace.re ≤ 1`).  The result is then
`traceDistanceGen_le_of_cp_tni` with `rfl` image witnesses. -/
theorem traceDistanceGen_cp_tni_le
    {dIn dOut : ℕ} [NeZero dIn] [NeZero dOut]
    (Φ : Op dIn → Op dOut)
    (hlin : IsLinearMap ℂ Φ) (hcp : IsCompletelyPositive Φ)
    (htni : ∀ A : Op dIn, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re)
    (ρ σ : Op dIn) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hρ1 : ρ.trace.re ≤ 1) (hσ1 : σ.trace.re ≤ 1) :
    traceDistanceGen (Φ ρ) (Φ σ) ≤ traceDistanceGen ρ σ := by
  have hΦρ : (Φ ρ).PosSemidef :=
    cp_linear_preserves_posSemidef (IsLinearMap.mk' Φ hlin) hcp ρ hρ
  have hΦσ : (Φ σ).PosSemidef :=
    cp_linear_preserves_posSemidef (IsLinearMap.mk' Φ hlin) hcp σ hσ
  exact traceDistanceGen_le_of_cp_tni Φ hlin hcp htni
    { toOp := ρ, isHermitian := hρ.1,
      pos_semidef := fun v => posSemidef_re_quadraticForm_nonneg hρ v, trace_le_one := hρ1 }
    { toOp := σ, isHermitian := hσ.1,
      pos_semidef := fun v => posSemidef_re_quadraticForm_nonneg hσ v, trace_le_one := hσ1 }
    { toOp := Φ ρ, isHermitian := hΦρ.1,
      pos_semidef := fun v => posSemidef_re_quadraticForm_nonneg hΦρ v,
      trace_le_one := le_trans (htni ρ hρ) hρ1 }
    { toOp := Φ σ, isHermitian := hΦσ.1,
      pos_semidef := fun v => posSemidef_re_quadraticForm_nonneg hΦσ v,
      trace_le_one := le_trans (htni σ hσ) hσ1 }
    rfl rfl

end InfoTheory.CKRPostselection

end -- noncomputable section
