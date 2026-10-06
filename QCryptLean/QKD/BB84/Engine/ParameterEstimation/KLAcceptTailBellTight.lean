/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QCryptLean.QKD.BB84.Engine.ParameterEstimation.KLAcceptTailTightRate
import QCryptLean.QKD.BB84.Engine.Postselection.BellReduction
import QCryptLean.QKD.BB84.Engine.EntropyFloor.BellFloorChain
import QCryptLean.QKD.BB84.Engine.EntropyFloor.PELabelledPerSigmaFloor
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.AnyRefAgreeBlock
import QCryptLean.QKD.BB84.Engine.InnerBudget.InnerBudgetCorrectness

/-!
## The general-`m` labelled Bell mixture as the Bell Haar block integral
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-- **The general-`m` PE-labelled Bell mixture, as a Haar block integral.**

The label block is a fixed operator depending on the outcome string alone, so each entry of the
labelled block is a fixed scalar times the corresponding entry of the unlabelled one, and that
scalar comes out of the Bochner integral (`tensorLeftKernel_blocks_integral_eq`).  The unlabelled
base `bb84BellEnVRhoEtilde_eq_haar_integral_blocks` is `m`-free and is reused verbatim; only the
label register width moves.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, `\label{eq:tausplit}`
(`main.tex:1356`–`:1361`), general `m` at `main.tex:909`, `:913`. -/
theorem bb84_bellPeLabelledEnVRhoEtilde_eq_haar_integral_blocks
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    ∀ (x : Fin n → Fin signalDim)
      (i j : Fin (signalDim ^ (n - bb84KeyRoundCount n m) * (1 * (signalDim ^ n)))),
      (((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel
          xSel Q δ).tensorLeftKernel
          (bb84PELabelKernel (m := m) peSel)).stateMap x).toOp i j =
        ∫ φ : DensityOp 4,
          ((bb84PELabelledPairedHaarPerSigmaFamily (m := m) 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
            (bellWembed φ)).stateMap x).toOp i j ∂(deFinetti_haarMeasure 4).measure := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  intro x i j
  exact tensorLeftKernel_blocks_integral_eq
    (bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q
        δ)
    (fun φ : DensityOp 4 =>
      bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n)
          peSel xSel Q δ (bellWembed φ))
    (bb84PELabelKernel (m := m) peSel)
    (bb84BellEnVRhoEtilde_eq_haar_integral_blocks peSel xSel Q δ) x i j

/-!
# Bell scalars at an abstract accept tail

The Bell `C(n+3,3)` collective inner budget and security budget, parametrised by an abstract
accept-tail scale `E` in place of a closed accept-tail expression, so that a sharper accept tail
can be substituted without re-deriving the budget.

## Main definitions

* `QKD.BB84.Engine.bb84CKRPostselectionInnerBudgetOfEpsPAOfTail` — the free-`epsPA` collective
  scalar at an abstract accept tail `E`.
* `QKD.BB84.Engine.improvedBudgetOfTail` — the Bell-tightened tight-rate security budget at an
  abstract accept tail.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) `\label{eq:condLHL}`
(`main.tex:462`–`:467`), `\label{lem:groupPurification}` (`main.tex:354`), App. B; Renner 2005
(`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`), §5, §6.5;
Christandl–König–Renner 2009 (`arXiv:0809.3019`).
-/

/-- **The Bell collective inner budget at a free `epsPA` and an abstract accept-tail scale `E`.**

```
bb84CKRPostselectionInnerBudgetOfEpsPAOfTail E = epsPA + 2·(ε_AEP + √(2·E)) .
```

The scalar reads neither `n` nor `δ`: every occurrence of them was inside the accept tail, which
is now the parameter `E`, or inside the privacy-amplification term, which is now `epsPA`.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`–`:467`,
`εPA` free); Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
noncomputable def bb84CKRPostselectionInnerBudgetOfEpsPAOfTail
    (E ε_AEP epsPA : ℝ) : ℝ :=
  epsPA + 2 * (ε_AEP + Real.sqrt (2 * E))

/-- At the accept-tail privacy-amplification exponent the abstract-tail free-`εPA` Bell budget
**is** `improvedInnerBudgetOfTail`, definitionally.

The `εPA` slot is `exp(−n·δ²/2)` and does **not** move with the accept tail: it is this library's
δ-scale instantiation of the free `εPA ∈ [0,1]` of Nahar et al.'s `\label{eq:condLHL}`, funded by
the tightened key-rate condition, independent of the accept split. -/
lemma bb84CKRPostselectionInnerBudgetOfEpsPAOfTail_tightRate (E : ℝ) (n : ℕ) (δ ε_AEP : ℝ) :
    bb84CKRPostselectionInnerBudgetOfEpsPAOfTail E ε_AEP
        (Real.exp (-(n : ℝ) * δ ^ 2 / 2)) =
      improvedInnerBudgetOfTail E n δ ε_AEP :=
  rfl

/-- **The Bell-tightened security budget at a free `epsPA` and an abstract accept-tail scale `E`.**

The direct correctness charge `2^(−ℓEV)` plus `C(n+3,3)` times the secrecy budget
`bb84CKRPostselectionInnerBudgetOfEpsPAOfTail E ε_AEP εPA`.
This is the generalized budget behind the `…At` key-rate row: the leftover-hash error `εPA` is a
free parameter (Nahar et al. 2024, `arXiv:2403.11851`, `\label{eq:condLHL}`), funded by
`improvedKeyRateConditionAt`; its contribution is `C(n+3,3)·εPA`. The accept tail `E`
and the prefactor do not depend on it. -/
noncomputable def improvedBudgetAt (E : ℝ) (n ℓEV : ℕ) (ε_AEP εPA : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(ℓEV : ℝ)) +
    (Nat.choose (n + 3) 3 : ℝ) *
    bb84CKRPostselectionInnerBudgetOfEpsPAOfTail E ε_AEP εPA

/-- **The Bell-tightened tight-rate security budget at an abstract accept-tail scale `E`.**

The direct correctness charge `2^(−ℓEV)` plus `C(n+3,3)` times
`improvedInnerBudgetOfTail E`.
The privacy-amplification term `exp(−n·δ²/2)` inside does **not** move with `E`. -/
noncomputable def improvedBudgetOfTail (E : ℝ) (n ℓEV : ℕ) (δ ε_AEP : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(ℓEV : ℝ)) +
    (Nat.choose (n + 3) 3 : ℝ) *
    improvedInnerBudgetOfTail E n δ ε_AEP

/-- At the accept-tail privacy-amplification exponent the generalized budget **is**
`improvedBudgetOfTail`, definitionally (the `εPA` slot `exp(−n·δ²/2)` unfolds to the tight-rate
inner budget). -/
lemma improvedBudgetOfTail_eq_improvedBudgetAt (E : ℝ) (n ℓEV : ℕ) (δ ε_AEP : ℝ) :
    improvedBudgetOfTail E n ℓEV δ ε_AEP =
      improvedBudgetAt E n ℓEV ε_AEP (Real.exp (-(n : ℝ) * δ ^ 2 / 2)) :=
  rfl

end QKD.BB84.Engine

end -- noncomputable section
