import QCryptLean.QKD.BB84.Reduction
import QCryptLean.QKD.BB84.Engine.Improved

/-!
# Improved security of the physical memory-free BB84 program

The main result is a normalized diamond bound on the distance between the *configured* physical
experiment's real map and its derived ideal key resource, at the selector-generic Bell-tight,
Corollary IV.2 sharp, phase-only finite-key budget.  This row carries one extra premise on the
error-correction scheme, `ECScheme.IsTranslationEquivariant`, which is exactly what the Bell
`C(n + 3, 3)` postselection lift requires.

## Route

physical program → analytical model → finite-key budget, as in the standard row:

1. `Parameters.realIdealDistance_le_modelDistance` (`QCryptLean.QKD.BB84.Reduction`): the
   physical experiment's real/ideal distance is at most that of its analytical model
   (`QCryptLean.QKD.BB84.Model`).  The reduction is shared with the standard row and uses
   no property of `ec`.
2. `Parameters.modelDistance_le_improvedBudget` (below): the model is within `improvedBudget`.
   This is the finite-key engine cell
   `ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharp_klTailPhaseOnly` at
   the configuration, with `packedPESel_keyCount` as its selector premise.
   The equivariance premise enters here
   only, through the Bell-twirl invariance of the model.

The free-parameter row `ImprovedConditionsAt` generalizes this further: the key-rate condition is
`improvedKeyRateConditionAtDev` (free `ε_PA` funded by `2·log(1/ε_PA) − 2·log 2` nats, free Rényi
offset
`β ∈ (0, 1)`) and the budget is `improvedBudgetAt epsilonAEP εPA dev`, with
`modelDistance_le_improvedBudgetAt`, `realIdealDistance_le_improvedBudgetAt` and
`isFullInterfaceSecure_improvedAt` as its security statements. The fixed row above is the
free-parameter row at `εPA = exp(−sifted·δ²/2)` and `β = secondOrderSharpBeta …`
whenever the window is nonnegative and the clamped offset is admissible. Larger smoothing
budgets use the channel bound; negative windows always reject.

The free-parameter row also separates the two roles of `δ`: the **window** of the accept test,
`|observed X-error rate − Q| ≤ δ`, is fixed by the protocol and its completeness requirement, while
the **deviation** `dev` between the window edge `Q + δ` and the phase-error rate the entropy floor
is charged at is fixed by soundness (how small the accept tail must be). In `ImprovedConditionsAt`
the deviation is a free parameter `dev ≥ 0`: the entropy floor, the accept tail
`exp(−m_X·klBer (Q+δ) (Q+δ+dev))` and the key-rate condition are charged at `Q + δ + dev`, and the
window `δ` stays the protocol's (Nahar et al., arXiv:2403.11851, Lemma 9 Eq. 44 with §V.C).
The entropy edge must be at most `1/2`. No upper bound on the positive smoothing or PA errors
and no lower bound on the key or X-test count is required. Zero deviation or an empty sifted
block gives tail one, so the channel-distance bound applies. `dev = δ` recovers the pinned tail.

The finite-key row is grounded in Nahar et al., arXiv:2403.11851, Theorem 3, Appendix B and
Section V.C, Dupuis--Fawzi, arXiv:1805.11652, Corollary IV.2, and Christandl--Koenig--Renner,
arXiv:0809.3019, Theorem 1 and Lemma 1.

Neither row dominates the other by fiat: the two budgets are attached to two different key-rate
conditions, and this one additionally constrains `ec`.
-/

noncomputable section

namespace QKD.BB84
open QKD.BB84.Reduction

open QKD.BB84.Engine
open QKD.BB84.Model

namespace Parameters

variable (p : Parameters)

/-- **The conditions of the improved finite-key row.**

The positive smoothing parameter, the entropy edge at most `1/2`, the
Bell-tightened tight-rate sharp-cap key-rate condition, and the
error-correction scheme's translation equivariance.  The latter is a condition on the honest
parties' announced-syndrome format alone — it is what lets the bilateral Bell twirl act on the
transcript by a permutation — and it is *not* assumed by the standard row. -/
structure ImprovedConditions (epsilonAEP : ℝ) : Prop where
  /-- The soundness edge lies in the increasing domain of binary entropy. -/
  belowThreshold : p.errorRate + 2 * p.tolerance ≤ 1 / 2
  /-- The smoothing parameter is positive. -/
  smoothing_pos : 0 < epsilonAEP
  /-- The Bell-tightened tight-rate sharp-cap key-rate condition. -/
  keyRate : improvedKeyRateCondition p.sifted p.tests p.keyLength
    p.tagLength p.leak p.errorRate p.tolerance epsilonAEP
  /-- The error-correction scheme is translation equivariant. -/
  ecTranslationEquivariant : p.ec.IsTranslationEquivariant

/-- **The conditions of the improved finite-key row, with the freedoms free.**

This is `ImprovedConditions` with the `…At` freedoms as free parameters: the key-rate
condition is `improvedKeyRateConditionAtDev`, which charges the Dupuis--Fawzi, arXiv:1805.11652,
Corollary IV.2 sharp penalty at an arbitrary admissible offset `β ∈ (0, 1)` instead of the
clamped optimiser `secondOrderSharpBeta`, and funds a free privacy-amplification error `ε_PA` with
`2·log(1/ε_PA) − 2·log 2` nats (Nahar et al., arXiv:2403.11851, `eq:condLHL`) instead of pinning
it to
`exp(−sifted·δ²/2)`.  The budget contains neither `β` nor the Cor IV.2 penalty, which reach the
security statement only through the key-rate condition together with `beta_pos`/`beta_lt_one`; the
free `ε_PA` also appears in the budget itself as the leftover-hash slot of
`improvedBudgetAt epsilonAEP εPA dev`, with positivity carried by `epsPA_pos`.
The engine uses the channel-distance bound of one when the actual accept tail `E ≥ 1/8`.
For `E < 1/8`, the entropy proof applies at every positive smoothing radius and every
`ε_PA > 0`. The key-rate condition discharges the single hashing-cap obligation.
An empty sifted block has tail one.

The phase-error **deviation** `dev` is free as well, separating it from the accept-test **window**
`δ = p.tolerance` (Nahar et al., arXiv:2403.11851, Lemma 9 Eq. 44 with §V.C): the window is fixed
by the protocol and its completeness requirement, while the deviation — the gap between the window
edge `Q + δ` and the phase-error rate the entropy floor is charged at — is fixed by soundness, i.e.
by how small the accept tail must be.  The key-rate condition, the entropy floor and the accept
tail are charged at the soundness edge `Q + δ + dev` (`improvedKeyRateConditionAtDev`,
`belowThresholdDev` requires this edge to be at most `1/2`, where binary entropy is increasing).
The window `δ` stays the protocol's: it fixes the accept masses and the integrands throughout
the chain. The deviation is nonnegative; at `dev = 0` the tail is one and the budget covers any
channel distance. Positivity of the centre and window is not needed. `dev = δ` recovers the pinned
tail for nonnegative windows; negative windows always reject. -/
structure ImprovedConditionsAt (epsilonAEP εPA β dev : ℝ) : Prop where
  /-- The smoothing parameter is positive. -/
  smoothing_pos : 0 < epsilonAEP
  /-- The Bell-tightened tight-rate sharp-cap key-rate condition at the free `ε_PA`, free `β` and
  the soundness edge `Q + δ + dev`. -/
  keyRate : improvedKeyRateConditionAtDev p.sifted p.tests p.keyLength
    p.tagLength p.leak p.errorRate p.tolerance dev epsilonAEP εPA β
  /-- The error-correction scheme is translation equivariant. -/
  ecTranslationEquivariant : p.ec.IsTranslationEquivariant
  /-- The privacy-amplification error is positive. -/
  epsPA_pos : 0 < εPA
  /-- The Rényi offset is positive. -/
  beta_pos : 0 < β
  /-- The Rényi offset is less than `1`, so Dupuis–Fawzi Corollary IV.2 applies at `1 + β`. -/
  beta_lt_one : β < 1
  /-- The phase-error deviation is nonnegative. -/
  dev_nonneg : 0 ≤ dev
  /-- The soundness edge lies in the increasing domain of binary entropy. -/
  belowThresholdDev : p.errorRate + p.tolerance + dev ≤ 1 / 2

/-- **The improved finite-key budget with a free privacy-amplification error and a free phase-error
deviation.**

The direct verification charge plus the `C(n + 3, 3)` Bell-symmetric lift of secrecy at the
realised X-subsample deviation-scoped KL accept tail
`klAcceptTailPhaseOnlyDev peSel xSel Q δ dev = exp(−m_X·klBer (Q+δ) (Q+δ+dev))`.
Its budget is `2^(−ℓEV) + C(n+3,3)·(ε_PA + 2·ε_AEP + 2·√(2·E))`.
Like `improvedBudget` this is a **normalized** diamond-distance budget;
it does not contain `β`, which reaches the security statement only through the key-rate condition
of `ImprovedConditionsAt`, nor does it depend on the δ-pin of `improvedBudget`.  The window `δ`
stays the protocol's; the tail and the entropy floor are charged at the soundness edge
`Q + δ + dev` (Nahar et al., arXiv:2403.11851, Lemma 9 Eq. 44 with §V.C). -/
def improvedBudgetAt (epsilonAEP εPA dev : ℝ) : ℝ :=
  QKD.BB84.Engine.improvedBudgetAt
    (klAcceptTailPhaseOnlyDev p.peSel p.xSel p.errorRate p.tolerance dev)
    p.sifted p.tagLength epsilonAEP εPA

/-- **The analytical model of the configured experiment is within the improved finite-key budget,
with the freedoms free.**

This is the finite-key engine cell
`ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnlyDev` read
at the configuration, with the free privacy-amplification error `ε_PA` (funded by
`2·log(1/ε_PA) − 2·log 2` nats, Nahar et al. `eq:condLHL`), the Dupuis--Fawzi, arXiv:1805.11652,
Corollary IV.2 penalty charged at the free offset `β ∈ (0, 1)`, and the free phase-error
deviation `dev`: the window `δ` of the accept test stays the protocol's, while the entropy floor,
the accept tail and the key-rate condition are charged at the soundness edge `Q + δ + dev`
(Nahar et al., Lemma 9 Eq. 44 with §V.C).  As in the fixed row the cell's
selector premise holds by `packedPESel_keyCount`. The key-rate condition funds the single
hashing-cap obligation using `ε_PA > 0`, with no upper bound on `ε_PA`. Every other premise is
a field of `ImprovedConditionsAt`. -/
theorem modelDistance_le_improvedBudgetAt [NeZero p.sifted] {epsilonAEP εPA β dev : ℝ}
    (h : p.ImprovedConditionsAt epsilonAEP εPA β dev) :
    p.modelDistance ≤ p.improvedBudgetAt epsilonAEP εPA dev :=
  ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharpAt_klTailPhaseOnlyDev
    p.peSel p.xSel (packedPESel_keyCount p.keyRounds p.zTests p.xTests) p.ec
    h.ecTranslationEquivariant p.errorRate p.tolerance dev epsilonAEP εPA β
    h.dev_nonneg h.belowThresholdDev h.keyRate h.smoothing_pos
    h.epsPA_pos h.beta_pos h.beta_lt_one

/-- An empty sifted block has tail one, so its improved budget covers any channel distance. -/
private lemma one_le_improvedBudgetAt_of_sifted_eq_zero {epsilonAEP εPA dev : ℝ}
    (hn : p.sifted = 0) (hAEP : 0 ≤ epsilonAEP) (hPA : 0 ≤ εPA) :
    1 ≤ p.improvedBudgetAt epsilonAEP εPA dev := by
  have hx : p.xTests = 0 := by simp only [Parameters.sifted] at hn; omega
  have hs : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  unfold improvedBudgetAt Engine.improvedBudgetAt bb84CKRPostselectionInnerBudgetOfEpsPAOfTail
  simp only [klAcceptTailPhaseOnlyDev, Reduction.packedXTestSampleSize, hx, hn,
    Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero]
  norm_num only [Nat.reduceAdd, Nat.choose_self, Nat.cast_one, one_mul, mul_one]
  have hc : 0 ≤ (2 : ℝ) ^ (-(p.tagLength : ℝ)) := by positivity
  linarith

/-- **The configured measure-first BB84 experiment is within the improved finite-key budget of its
ideal key resource, in normalized diamond distance, with the freedoms free.**

As in the fixed row the bound is on the derived real and ideal maps of the actual executable
protocol; the free `ε_PA` (Nahar et al. `eq:condLHL`), free Rényi offset `β` (Dupuis--Fawzi
Corollary IV.2) and free phase-error deviation (window/deviation split, Nahar et al. Lemma 9
Eq. 44 with §V.C) enter only through `ImprovedConditionsAt`'s key-rate condition and admissibility
fields. -/
theorem realIdealDistance_le_improvedBudgetAt {epsilonAEP εPA β dev : ℝ}
    (h : p.ImprovedConditionsAt epsilonAEP εPA β dev) :
    p.protocol.realIdealDistance ≤ p.improvedBudgetAt epsilonAEP εPA dev := by
  by_cases hn : p.sifted = 0
  · have hone : p.protocol.realIdealDistance ≤ 1 := by
      rw [p.realIdealDistance_eq_coordinates,
        QKD.Protocol.NumeralCoordinates.difference_eq_real_sub_ideal]
      change (1 / 2) * Quantum.Channels.diamondNorm
        (p.coordinates.real - p.coordinates.ideal) ≤ 1
      have hnorm := Quantum.Channels.diamondNorm_sub_le_two p.coordinates.real_isCPTP
        p.coordinates.ideal_isCPTP
      linarith only [hnorm]
    exact hone.trans (p.one_le_improvedBudgetAt_of_sifted_eq_zero hn
      h.smoothing_pos.le h.epsPA_pos.le)
  · haveI : NeZero p.sifted := ⟨hn⟩
    exact p.realIdealDistance_le_modelDistance.trans (p.modelDistance_le_improvedBudgetAt h)

/-- The configured experiment is fully interface-secure at the free-`ε_PA`, free-`β`, free-`dev`
improved finite-key budget.

This is the diamond bound above together with the accepted-key classicality of the real output
(`protocol_acceptedKeyClassical`), i.e. the complete full-interface criterion. -/
theorem isFullInterfaceSecure_improvedAt {epsilonAEP εPA β dev : ℝ}
    (h : p.ImprovedConditionsAt epsilonAEP εPA β dev) :
    p.protocol.IsFullInterfaceSecure (p.improvedBudgetAt epsilonAEP εPA dev) :=
  p.isFullInterfaceSecure_of_realIdealDistance_le (p.realIdealDistance_le_improvedBudgetAt h)

/-- **The improved finite-key budget.**

The direct verification charge `2^(−tagLength)` plus `C(n+3,3)` times the secrecy budget
`exp(−sifted·tolerance²/2) + 2·epsilonAEP + 2·√(2E)`, at the realised X-subsample KL accept tail
`E`. The Corollary IV.2 penalty and the `2·log₂ C(n+3,3)` purification cost enter the key-rate
condition. This is a normalized diamond-distance budget. -/
def improvedBudget (epsilonAEP : ℝ) : ℝ :=
  improvedBudgetOfTail
    (klAcceptTailPhaseOnly p.peSel p.xSel p.errorRate p.tolerance)
    p.sifted p.tagLength p.tolerance epsilonAEP

/-- At the window-pinned deviation `dev = δ` and the δ-pinned `ε_PA` the `…At` budget **is** the
fixed improved budget: the Dev tail folds back to the `2δ` tail (`klAcceptTailPhaseOnlyDev_self`,
a `rw` since `Q + δ + δ` and `Q + 2 * δ` agree only propositionally), and at the accept-tail
privacy-amplification exponent the generalized budget is `improvedBudgetOfTail`, definitionally
(`improvedBudgetOfTail_eq_improvedBudgetAt`). -/
theorem improvedBudgetAt_eq_improvedBudget (epsilonAEP : ℝ) :
    p.improvedBudgetAt epsilonAEP (Real.exp (-(p.sifted : ℝ) * p.tolerance ^ 2 / 2)) p.tolerance
      = p.improvedBudget epsilonAEP := by
  unfold improvedBudgetAt improvedBudget
  simp only [klAcceptTailPhaseOnlyDev, klAcceptTailPhaseOnly]
  rw [show p.errorRate + p.tolerance + p.tolerance = p.errorRate + 2 * p.tolerance from by ring]
  exact (improvedBudgetOfTail_eq_improvedBudgetAt _ _ _ _ _).symm

/-- **The analytical model of the configured experiment is within the improved finite-key
budget.**

This is the finite-key engine cell
`ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharp_klTailPhaseOnly` read
at the configuration: the model is that cell's channel pair, and `improvedBudget` is its budget.
The selector premise holds by `packedPESel_keyCount`; the key-rate condition supplies the key
count needed in the entropic branch. A zero window gives tail one, and a negative window rejects
on every outcome. Every other premise, including the translation equivariance of `ec`, is a
field of `ImprovedConditions`. -/
theorem modelDistance_le_improvedBudget [NeZero p.sifted] {epsilonAEP : ℝ}
    (h : p.ImprovedConditions epsilonAEP) :
    p.modelDistance ≤ p.improvedBudget epsilonAEP := by
  exact ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharp_klTailPhaseOnly
    p.peSel p.xSel (packedPESel_keyCount p.keyRounds p.zTests p.xTests) p.ec
    h.ecTranslationEquivariant p.errorRate p.tolerance epsilonAEP
    h.belowThreshold h.keyRate h.smoothing_pos

/-- **The configured measure-first BB84 experiment is within the improved finite-key budget of its
ideal key resource, in normalized diamond distance.**

As in the standard row the bound is on the derived real and ideal maps of the actual executable
protocol, with arbitrary basis laws, arbitrary physical batch size and no reference, entropy,
channel-equality or security premise.  The one additional assumption is the translation
equivariance of the error-correction scheme. -/
theorem realIdealDistance_le_improvedBudget {epsilonAEP : ℝ}
    (h : p.ImprovedConditions epsilonAEP) :
    p.protocol.realIdealDistance ≤ p.improvedBudget epsilonAEP := by
  by_cases hn : p.sifted = 0
  · have hone : p.protocol.realIdealDistance ≤ 1 := by
      rw [p.realIdealDistance_eq_coordinates,
        QKD.Protocol.NumeralCoordinates.difference_eq_real_sub_ideal]
      change (1 / 2) * Quantum.Channels.diamondNorm
        (p.coordinates.real - p.coordinates.ideal) ≤ 1
      have hnorm := Quantum.Channels.diamondNorm_sub_le_two p.coordinates.real_isCPTP
        p.coordinates.ideal_isCPTP
      linarith only [hnorm]
    rw [← p.improvedBudgetAt_eq_improvedBudget]
    exact hone.trans (p.one_le_improvedBudgetAt_of_sifted_eq_zero hn
      h.smoothing_pos.le (Real.exp_pos _).le)
  · haveI : NeZero p.sifted := ⟨hn⟩
    exact p.realIdealDistance_le_modelDistance.trans (p.modelDistance_le_improvedBudget h)

/-- The configured experiment is fully interface-secure at the improved finite-key budget.

This is the diamond bound above together with the accepted-key classicality of the real output
(`protocol_acceptedKeyClassical`), i.e. the complete full-interface criterion. -/
theorem isFullInterfaceSecure_improved {epsilonAEP : ℝ} (h : p.ImprovedConditions epsilonAEP) :
    p.protocol.IsFullInterfaceSecure (p.improvedBudget epsilonAEP) :=
  p.isFullInterfaceSecure_of_realIdealDistance_le (p.realIdealDistance_le_improvedBudget h)

end Parameters

end QKD.BB84
