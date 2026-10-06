import QCryptLean.QKD.BB84.Security.Improved
import QCryptLean.QKD.BB84.Comparison.LiteratureKeyLength
import QCryptLean.Math.Analysis.LogChoose

/-!
# The improved BB84 row certifies a longer key than the lifted literature length

For the configured physical protocol `QKD.BB84.Parameters`, this module compares the key length
the improved finite-key row (`QCryptLean.QKD.BB84.Security.Improved`) certifies with the
key length of Tupkary, Tan and Lütkenhaus, arXiv:2311.01600, `adaptivepaper.tex:294`–`:299`
(`\label{eq:l_ivalue}`), lifted to coherent attacks through arXiv:2403.11851
(`QCryptLean.QKD.BB84.Comparison.LiteratureKeyLength`).

## Which lift is matched, and why

The improved row pays the Bell-symmetric postselection prefactor `C(n + 3, 3)` (lift dimension
`x = 4`, arXiv:2403.11851 `main.tex:354` `\label{lem:groupPurification}`), and it may do so
because it assumes the error-correction scheme to be translation equivariant
(`ImprovedConditions.ecTranslationEquivariant`).  The same symmetric lift is available to the
comparator on the same protocol under the same assumption, so the matched comparator is the
literature length lifted at `x = 4`, not at the generic `x = 16` of `main.tex:498`
(`\label{cor:liftToCoherent}`).  Every comparison statement here reads the `x = 4` lift; since a
larger prefactor only shortens the lifted length
(`Comparison.liftedLiteratureKeyLength_le_of_prefactor_le`), the `x = 16` comparison follows.

## What the comparator is given

The comparator is evaluated at the improved row's own `keyRounds`, `tagLength`, `leak`, accept
test centre `errorRate` and half-width `tolerance`, with its entropy term at the same phase-error
bracket `errorRate + 2·tolerance` (the feasible set of the paper's own `ℓ₁` acceptance test,
`adaptivepaper.tex:549`–`:556`, is not modelled), and its lift taken over the `sifted` rounds
rather than the physical `rounds`.  It pays neither the improved row's `2·log₂ C(n + 3, 3)`
key-length charge nor its `n·δ²/log 2` term, and the key-length half `−2·log₂ g` of
`cor:liftToCoherent` is not charged to it.  The unlifted length — prefactor `1`,
`Comparison.liftedLiteratureKeyLength 1` — is a security claim against IID-collective attacks
only, and it can exceed what the improved row certifies
(`Comparison.
  keyLength_lt_liftedLiteratureKeyLength_one_of_improvedKeyRateConditionAtDev_millionSifted`);
the comparison is
against what the literature proves for coherent attacks.

## Main definitions

* `Parameters.LiteratureAdvantageRegion`: the explicit hypothesis block of the comparison.
* `Parameters.LiteratureAdvantageRegionAt`: the general-row comparison region, with the free
  `ε_PA`, Rényi offset `β` and phase-error deviation `dev` of
  `Security.Improved.ImprovedConditionsAt` free and the comparator evaluated at the phase-error
  deviation `(tolerance + dev)/2`, i.e. the entropy bracket `errorRate + tolerance + dev`;
  the pinned region evaluates the same arithmetic core at `dev = δ`,
  `ε_PA = exp(−sifted·δ²/2)` and `β = secondOrderSharpBeta …`.

## Main statements

* `Comparison.exists_gt_liftedLiteratureKeyLength_improvedKeyRateConditionAtDev`: the
  arithmetic core —
  a penalty gap of at least one bit yields an integer key length above the comparator at which
  the general-row key-rate condition `improvedKeyRateConditionAtDev` holds at the soundness edge
  `Q + δ + dev`; the comparator is at the phase-error deviation `(δ + dev)/2`, i.e. the entropy
  bracket `Q + δ + dev`.
* `improvedBudgetOfTail_le_of_le`, `Parameters.improvedBudget_le_quadraticTail`: the improved
  budget is monotone in its accept tail, hence at most its value at the quadratic X-test tail
  `exp(−4·xTests·δ²)`.
* `Parameters.exists_keyLength_gt_liftedLiteratureKeyLength`: **the comparison theorem.**  On the
  region there is a key length strictly above the `x = 4` lifted literature length at which the
  configured protocol satisfies the improved conditions, has improved budget at most `ε_tot`, and
  is fully interface-secure at `ε_tot`.
* `Parameters.exists_keyLength_gt_liftedLiteratureKeyLength_at`: the general-row comparison
  theorem, against `ImprovedConditionsAt` and `improvedBudgetAt` at the bracket.

A closed instance at `10⁶` sifted rounds is
`QCryptLean.QKD.BB84.Comparison.MillionSiftedRounds`.
-/

open Math.ClassicalEntropy InfoTheory.DeFinetti

noncomputable section

namespace QKD.BB84

open QKD.BB84.Engine

namespace Comparison

/-- **The arithmetic core of the general-row comparison.**

The key-rate condition is the
free-parameter `improvedKeyRateConditionAtDev`, charged at the soundness edge `Q + δ + dev` and
funding the free `ε_PA` with `2·log(1/ε_PA) − 2·log 2` nats, and the comparator is evaluated at the
matching phase-error deviation `(δ + dev)/2`, i.e. the entropy bracket
`Q + 2·((δ + dev)/2) = Q + δ + dev`.  The
penalty gap is in bits: the free-offset Cor IV.2 penalty `P_β`, the postselection charge
`2·log₂ C(n + 3, 3)` and the privacy-amplification funding `2·log₂(1/ε_PA) − 2` must leave one
bit. The
δ-pinned arithmetic core (`improvedKeyRateCondition` at the doubled window edge `Q + 2·δ`) is the
special case `dev = δ` of this theorem, via `improvedKeyRateConditionAtDev_eq`. -/
theorem exists_gt_liftedLiteratureKeyLength_improvedKeyRateConditionAtDev
    {x n m nK ℓEV leak : ℕ} {Q δ dev ε_AEP εPA β ε_tot : ℝ}
    (hK : bb84KeyRoundCount n m = nK)
    (hnonneg : 0 ≤ liftedLiteratureKeyLength x n nK ℓEV leak Q ((δ + dev) / 2) ε_tot)
    (hgap : finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap nK ε_AEP β
        + 2 * Real.log (Nat.choose (n + 3) 3 : ℝ) / Real.log 2
        + 2 * Real.log (1 / εPA) / Real.log 2 - 1
      ≤ literatureFiniteSizePenalty nK (liftedPrivacyAmplificationError x n ε_tot)) :
    ∃ ℓ : ℕ, liftedLiteratureKeyLength x n nK ℓEV leak Q ((δ + dev) / 2) ε_tot < ℓ ∧
      improvedKeyRateConditionAtDev n m ℓ ℓEV leak Q δ dev ε_AEP εPA β := by
  subst hK
  set c : ℝ := liftedLiteratureKeyLength x n (bb84KeyRoundCount n m) ℓEV leak Q
      ((δ + dev) / 2) ε_tot with hc
  refine ⟨⌊c⌋₊ + 1, ?_, ?_⟩
  · push_cast
    exact Nat.lt_floor_add_one c
  · have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hfl : (⌊c⌋₊ : ℝ) * Real.log 2 ≤ c * Real.log 2 :=
      mul_le_mul_of_nonneg_right (Nat.floor_le hnonneg) hL.le
    set S : ℝ := finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap
        (bb84KeyRoundCount n m) ε_AEP β
    set P : ℝ := literatureFiniteSizePenalty (bb84KeyRoundCount n m)
      (liftedPrivacyAmplificationError x n ε_tot)
    set G : ℝ := Real.log (Nat.choose (n + 3) 3 : ℝ)
    -- the comparator's entropy argument `Q + 2·((δ + dev)/2)` is the soundness edge `Q + δ + dev`
    have hhalf : (Q : ℝ) + 2 * ((δ + dev) / 2) = Q + δ + dev := by ring
    have hrate : (bb84KeyRoundCount n m : ℝ) * (Real.log 2 - binaryEntropy (Q + δ + dev))
        = Real.log 2 * (c + (leak : ℝ) + (ℓEV : ℝ) + P) := by
      rw [hc, liftedLiteratureKeyLength, literatureKeyLength, hhalf]
      field_simp
      ring
    have hgap' : Real.log 2 * S + 2 * G + 2 * Real.log (1 / εPA) - Real.log 2
        ≤ Real.log 2 * P := by
      have h := mul_le_mul_of_nonneg_left hgap hL.le
      have hid : Real.log 2 * (S + 2 * G / Real.log 2 + 2 * Real.log (1 / εPA) / Real.log 2 - 1)
          = Real.log 2 * S + 2 * G + 2 * Real.log (1 / εPA) - Real.log 2 := by
        field_simp
      linarith
    rw [improvedKeyRateConditionAtDev, hrate]
    push_cast
    linarith

end Comparison

/-- **The improved budget is monotone in its accept tail.** -/
theorem improvedBudgetOfTail_le_of_le {E E' : ℝ} (n ℓEV : ℕ) (δ ε : ℝ) (hEE' : E ≤ E') :
    improvedBudgetOfTail E n ℓEV δ ε ≤ improvedBudgetOfTail E' n ℓEV δ ε := by
  rw [improvedBudgetOfTail, improvedBudgetOfTail, improvedInnerBudgetOfTail,
    improvedInnerBudgetOfTail]
  gcongr

namespace Parameters

variable (p : Parameters)

/-- The lifted literature comparator at a configured experiment's sifted count and costs. -/
def liftedLiteratureKeyLength (p : Parameters) (x : ℕ) (ε_tot : ℝ) : ℝ :=
  Comparison.liftedLiteratureKeyLength x p.sifted p.keyRounds p.tagLength p.leak
    p.errorRate p.tolerance ε_tot

/-- The lifted literature comparator at a configured experiment's sifted count and costs, with
its entropy term at the general row's phase-error bracket `(tolerance + dev) / 2`: the bracket
`Q + 2·((δ + dev)/2) = Q + δ + dev` at which the free row's key-rate condition
`improvedKeyRateConditionAtDev` is charged. -/
def liftedLiteratureKeyLengthAt (p : Parameters) (x : ℕ) (ε_tot dev : ℝ) : ℝ :=
  Comparison.liftedLiteratureKeyLength x p.sifted p.keyRounds p.tagLength p.leak
    p.errorRate ((p.tolerance + dev) / 2) ε_tot

/-- **The improved budget is at most its value at the quadratic X-test tail**
`exp(−4·xTests·δ²)`.

The realised X-test block of the packed selector has `xTests` rounds
(`Reduction.packedXTestSampleSize`), and
on `0 < Q`, `0 < δ`, `Q + 2δ < errorThreshold` the KL accept tail is dominated by the quadratic one
(`klAcceptTailPhaseOnly_le_sharpXSampleTail`). -/
theorem improvedBudget_le_quadraticTail (hQ : 0 < p.errorRate) (hδ : 0 < p.tolerance)
    (hbelow : p.errorRate + 2 * p.tolerance < errorThreshold) (epsilonAEP : ℝ) :
    p.improvedBudget epsilonAEP ≤
      improvedBudgetOfTail (Real.exp (-4 * (p.xTests : ℝ) * p.tolerance ^ 2))
        p.sifted p.tagLength p.tolerance epsilonAEP := by
  have htail := klAcceptTailPhaseOnly_le_sharpXSampleTail (peSel := p.peSel) (xSel := p.xSel)
    hQ hδ hbelow
  rw [Reduction.packedXTestSampleSize] at htail
  exact improvedBudgetOfTail_le_of_le _ _ _ _ htail

/-- **The explicit comparison region** against the Bell-symmetric (`x = 4`) lift of the
literature key length.

* The positive smoothing parameter, soundness edge at most `1/2`, and
  `ecTranslationEquivariant` are the improved row's conditions other than its key-rate condition,
  which the comparison theorem supplies.
* `acceptanceEdge_pos`, `tolerance_nonneg` and `belowThreshold` put both KL arguments in
  `(0, 1/2]`, with the soundness edge at least the acceptance edge.
* `sifted_pos` prevents zero-round penalties from degenerating under totalized division.
* `improvedBudget_le` puts the improved budget within the shared total budget.
* `literatureKeyLength_nonneg` asks the comparator to deliver a nonnegative key.
* `penaltyGap` says the lifted literature penalty exceeds everything the improved row charges on
  top of the shared rate `keyRounds·(1 − h₂(Q + 2δ)/log 2) − leak − tagLength` — the sharp
  Cor IV.2 penalty, `2·log₂ C(sifted + 3, 3)` and `sifted·δ²/log 2 − 2` — by at least one bit.

None of the fields mentions `keyLength`. -/
structure LiteratureAdvantageRegion (epsilonAEP epsilonTotal : ℝ) : Prop where
  /-- The sifted block is nonempty. -/
  sifted_pos : 0 < p.sifted
  /-- The acceptance edge is strictly positive, as required by both KL logarithms. -/
  acceptanceEdge_pos : 0 < p.errorRate + p.tolerance
  /-- The soundness edge is at least the acceptance edge. -/
  tolerance_nonneg : 0 ≤ p.tolerance
  /-- The soundness edge is at most the midpoint of binary entropy. -/
  belowThreshold : p.errorRate + 2 * p.tolerance ≤ 1 / 2
  /-- The smoothing parameter is positive. -/
  smoothing_pos : 0 < epsilonAEP
  /-- The error-correction scheme is translation equivariant. -/
  ecTranslationEquivariant : p.ec.IsTranslationEquivariant
  /-- The improved budget is within the shared total. -/
  improvedBudget_le : p.improvedBudget epsilonAEP ≤ epsilonTotal
  /-- The `x = 4` lifted literature key length is nonnegative. -/
  literatureKeyLength_nonneg :
    0 ≤ p.liftedLiteratureKeyLength 4 epsilonTotal
  /-- The lifted literature penalty exceeds the improved row's extra charges by one bit. -/
  penaltyGap :
    finiteSizePenaltySecondOrderSharp bb84SharpVarianceCap p.keyRounds epsilonAEP
        + 2 * Real.log (Nat.choose (p.sifted + 3) 3 : ℝ) / Real.log 2
        + (p.sifted : ℝ) * p.tolerance ^ 2 / Real.log 2 - 1
      ≤ Comparison.literatureFiniteSizePenalty p.keyRounds
          (Comparison.liftedPrivacyAmplificationError 4 p.sifted epsilonTotal)

/-- The pinned comparator's entropy bracket is nonnegative. -/
theorem LiteratureAdvantageRegion.entropy_nonneg {p : Parameters}
    {epsilonAEP epsilonTotal : ℝ} (h : p.LiteratureAdvantageRegion epsilonAEP epsilonTotal) :
    0 ≤ p.errorRate + 2 * p.tolerance := by
  linarith [h.acceptanceEdge_pos, h.tolerance_nonneg]

/-- The pinned comparison region excludes a degenerate literature Rényi offset. -/
theorem LiteratureAdvantageRegion.literatureEpsPA_lt_one {p : Parameters}
    {epsilonAEP epsilonTotal : ℝ} (h : p.LiteratureAdvantageRegion epsilonAEP epsilonTotal) :
    Comparison.liftedPrivacyAmplificationError 4 p.sifted epsilonTotal < 1 := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpost := Real.four_le_two_mul_log_choose_add_three_div_log_two h.sifted_pos
  have hpen := finiteSizePenaltySecondOrderSharp_nonneg bb84SharpVarianceCap
    bb84SharpVarianceCap_pos.le p.keyRounds epsilonAEP
  have hcharge : 0 ≤ (p.sifted : ℝ) * p.tolerance ^ 2 / Real.log 2 := by positivity
  by_contra hlt
  have hgap := h.penaltyGap
  rw [Comparison.literatureFiniteSizePenalty_eq_zero_of_one_le p.keyRounds (by linarith)] at hgap
  linarith

/-- The pinned comparison region has a positive key-round count. -/
theorem LiteratureAdvantageRegion.keyRounds_pos {p : Parameters}
    {epsilonAEP epsilonTotal : ℝ} (h : p.LiteratureAdvantageRegion epsilonAEP epsilonTotal) :
    0 < p.keyRounds := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpost := Real.four_le_two_mul_log_choose_add_three_div_log_two h.sifted_pos
  have hpen := finiteSizePenaltySecondOrderSharp_nonneg bb84SharpVarianceCap
    bb84SharpVarianceCap_pos.le p.keyRounds epsilonAEP
  have hcharge : 0 ≤ (p.sifted : ℝ) * p.tolerance ^ 2 / Real.log 2 := by positivity
  by_contra hn
  have hgap := h.penaltyGap
  rw [Nat.eq_zero_of_not_pos hn, Comparison.literatureFiniteSizePenalty_zero] at hgap
  rw [Nat.eq_zero_of_not_pos hn] at hpen
  linarith

/-- The pinned region's shared total and literature PA error are positive. -/
theorem LiteratureAdvantageRegion.literatureEpsPA_pos {p : Parameters}
    {epsilonAEP epsilonTotal : ℝ} (h : p.LiteratureAdvantageRegion epsilonAEP epsilonTotal) :
    0 < Comparison.liftedPrivacyAmplificationError 4 p.sifted epsilonTotal := by
  apply Comparison.liftedPrivacyAmplificationError_pos
  apply lt_of_lt_of_le _ h.improvedBudget_le
  unfold Parameters.improvedBudget improvedBudgetOfTail improvedInnerBudgetOfTail
  have := h.smoothing_pos
  positivity

/-- The pinned region's smoothing parameter is below one. -/
theorem LiteratureAdvantageRegion.smoothing_lt_one {p : Parameters}
    {epsilonAEP epsilonTotal : ℝ} (h : p.LiteratureAdvantageRegion epsilonAEP epsilonTotal) :
    epsilonAEP < 1 := by
  have hg : 0 < (Nat.choose (p.sifted + 3) 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 3 ≤ p.sifted + 3)
  have htotal := h.literatureEpsPA_lt_one
  rw [Comparison.liftedPrivacyAmplificationError, deFinettiPrefactor_four,
    div_lt_one (by positivity)] at htotal
  have hbudget := h.improvedBudget_le
  unfold Parameters.improvedBudget improvedBudgetOfTail improvedInnerBudgetOfTail at hbudget
  have hcorrect : 0 ≤ (2 : ℝ) ^ (-(p.tagLength : ℝ)) := by positivity
  have hpa := Real.exp_pos (-(p.sifted : ℝ) * p.tolerance ^ 2 / 2)
  have hsqrt := Real.sqrt_nonneg
    (2 * klAcceptTailPhaseOnly p.peSel p.xSel p.errorRate p.tolerance)
  nlinarith

/-- The pinned region's clamped Rényi offset lies strictly between zero and one. -/
theorem LiteratureAdvantageRegion.beta_mem_Ioo {p : Parameters}
    {epsilonAEP epsilonTotal : ℝ} (h : p.LiteratureAdvantageRegion epsilonAEP epsilonTotal) :
    secondOrderSharpBeta bb84SharpVarianceCap p.keyRounds epsilonAEP ∈ Set.Ioo (0 : ℝ) 1 := by
  haveI : NeZero p.keyRounds := ⟨h.keyRounds_pos.ne'⟩
  exact ⟨secondOrderSharpBeta_pos bb84SharpVarianceCap bb84SharpVarianceCap_pos
    p.keyRounds epsilonAEP h.smoothing_pos h.smoothing_lt_one,
    (secondOrderSharpBeta_le_one_sixteenth _ _ _).trans_lt (by norm_num)⟩

/-- Both Bernoulli parameters in the pinned region lie strictly between zero and one. -/
theorem LiteratureAdvantageRegion.klParameters_mem_Ioo {p : Parameters}
    {epsilonAEP epsilonTotal : ℝ} (h : p.LiteratureAdvantageRegion epsilonAEP epsilonTotal) :
    p.errorRate + p.tolerance ∈ Set.Ioo (0 : ℝ) 1 ∧
      p.errorRate + 2 * p.tolerance ∈ Set.Ioo (0 : ℝ) 1 := by
  have := h.acceptanceEdge_pos
  have := h.tolerance_nonneg
  have := h.belowThreshold
  constructor <;> constructor <;> linarith

/-- **The explicit comparison region for the general row** against the Bell-symmetric (`x = 4`)
lift of the literature key length evaluated at the phase-error deviation `(tolerance + dev)/2`,
i.e. the entropy bracket `errorRate + tolerance + dev`.

The general-row analogue of `LiteratureAdvantageRegion`, with the `…At` freedoms free: the
elementary regime is carried as the key-length-independent fields of `ImprovedConditionsAt`
and the penalty gap charges the free-offset Cor IV.2 penalty `P_β` and the free
privacy-amplification funding `2·log₂(1/ε_PA) − 2` instead of the δ-pinned `sifted·δ²/log 2 − 2`.
The acceptance and soundness edges lie in `(0, 1/2]`, so both KL logarithms have positive
arguments. The budget and penalty gap force a positive key count;
together with `literatureEpsPA_lt_one`, this keeps the comparator's Rényi offset positive.
Positivity of its PA error follows from the positive improved budget and `improvedBudgetAt_le`.

None of the fields mentions `keyLength`. -/
structure LiteratureAdvantageRegionAt (epsilonAEP εPA β dev epsilonTotal : ℝ) : Prop where
  /-- The smoothing parameter is positive. -/
  smoothing_pos : 0 < epsilonAEP
  /-- The privacy-amplification error is positive. -/
  epsPA_pos : 0 < εPA
  /-- The Rényi offset is positive. -/
  beta_pos : 0 < β
  /-- The Rényi offset is less than `1`. -/
  beta_lt_one : β < 1
  /-- The phase-error deviation is nonnegative. -/
  dev_nonneg : 0 ≤ dev
  /-- The acceptance edge is strictly positive, as required by both KL logarithms. -/
  acceptanceEdge_pos : 0 < p.errorRate + p.tolerance
  /-- The soundness edge is at most the midpoint of binary entropy. -/
  belowThresholdDev : p.errorRate + p.tolerance + dev ≤ 1 / 2
  /-- The error-correction scheme is translation equivariant. -/
  ecTranslationEquivariant : p.ec.IsTranslationEquivariant
  /-- The general-row improved budget is within the shared total. -/
  improvedBudgetAt_le : p.improvedBudgetAt epsilonAEP εPA dev ≤ epsilonTotal
  /-- The comparator's privacy-amplification error lies below one. -/
  literatureEpsPA_lt_one : Comparison.liftedPrivacyAmplificationError 4 p.sifted epsilonTotal < 1
  /-- The `x = 4` lifted literature key length at the bracket is nonnegative. -/
  literatureKeyLength_nonneg : 0 ≤ p.liftedLiteratureKeyLengthAt 4 epsilonTotal dev
  /-- The lifted literature penalty exceeds the general row's extra charges by one bit. -/
  penaltyGapAt :
    finiteSizePenaltySecondOrderSharpAt bb84SharpVarianceCap p.keyRounds epsilonAEP β
        + 2 * Real.log (Nat.choose (p.sifted + 3) 3 : ℝ) / Real.log 2
        + 2 * Real.log (1 / εPA) / Real.log 2 - 1
      ≤ Comparison.literatureFiniteSizePenalty p.keyRounds
          (Comparison.liftedPrivacyAmplificationError 4 p.sifted epsilonTotal)

/-- The general comparator's entropy bracket is nonnegative. -/
theorem LiteratureAdvantageRegionAt.entropy_nonneg {p : Parameters}
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.LiteratureAdvantageRegionAt epsilonAEP εPA β dev epsilonTotal) :
    0 ≤ p.errorRate + p.tolerance + dev := by
  linarith [h.acceptanceEdge_pos, h.dev_nonneg]

/-- The general region's shared total and literature PA error are positive. -/
theorem LiteratureAdvantageRegionAt.literatureEpsPA_pos {p : Parameters}
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.LiteratureAdvantageRegionAt epsilonAEP εPA β dev epsilonTotal) :
    0 < Comparison.liftedPrivacyAmplificationError 4 p.sifted epsilonTotal := by
  apply Comparison.liftedPrivacyAmplificationError_pos
  apply lt_of_lt_of_le _ h.improvedBudgetAt_le
  unfold Parameters.improvedBudgetAt Engine.improvedBudgetAt
    bb84CKRPostselectionInnerBudgetOfEpsPAOfTail
  have := h.smoothing_pos
  have := h.epsPA_pos
  positivity

/-- The general region's smoothing parameter is below one. -/
theorem LiteratureAdvantageRegionAt.smoothing_lt_one {p : Parameters}
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.LiteratureAdvantageRegionAt epsilonAEP εPA β dev epsilonTotal) :
    epsilonAEP < 1 := by
  have hg : 0 < (Nat.choose (p.sifted + 3) 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 3 ≤ p.sifted + 3)
  have htotal := h.literatureEpsPA_lt_one
  rw [Comparison.liftedPrivacyAmplificationError, deFinettiPrefactor_four,
    div_lt_one (by positivity)] at htotal
  have hbudget := h.improvedBudgetAt_le
  unfold Parameters.improvedBudgetAt Engine.improvedBudgetAt
    bb84CKRPostselectionInnerBudgetOfEpsPAOfTail at hbudget
  have hcorrect : 0 ≤ (2 : ℝ) ^ (-(p.tagLength : ℝ)) := by positivity
  have hsqrt := Real.sqrt_nonneg
    (2 * klAcceptTailPhaseOnlyDev p.peSel p.xSel p.errorRate p.tolerance dev)
  nlinarith [h.epsPA_pos]

/-- Both Bernoulli parameters in the general region lie strictly between zero and one. -/
theorem LiteratureAdvantageRegionAt.klParameters_mem_Ioo {p : Parameters}
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.LiteratureAdvantageRegionAt epsilonAEP εPA β dev epsilonTotal) :
    p.errorRate + p.tolerance ∈ Set.Ioo (0 : ℝ) 1 ∧
      p.errorRate + p.tolerance + dev ∈ Set.Ioo (0 : ℝ) 1 := by
  have := h.acceptanceEdge_pos
  have := h.dev_nonneg
  have := h.belowThresholdDev
  constructor <;> constructor <;> linarith

/-- The budget and penalty gap force a positive key count in the general comparison region. -/
theorem LiteratureAdvantageRegionAt.keyRounds_pos {p : Parameters}
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.LiteratureAdvantageRegionAt epsilonAEP εPA β dev epsilonTotal) :
    0 < p.keyRounds := by
  have hg : 0 < (Nat.choose (p.sifted + 3) 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 3 ≤ p.sifted + 3)
  have htotal : epsilonTotal < 2 * (Nat.choose (p.sifted + 3) 3 : ℝ) := by
    have hlt := h.literatureEpsPA_lt_one
    rwa [Comparison.liftedPrivacyAmplificationError, deFinettiPrefactor_four,
      div_lt_one (by positivity)] at hlt
  have hinner : εPA + 2 * (epsilonAEP + Real.sqrt
      (2 * klAcceptTailPhaseOnlyDev p.peSel p.xSel p.errorRate p.tolerance dev)) < 2 := by
    have hbudget := h.improvedBudgetAt_le
    unfold Parameters.improvedBudgetAt Engine.improvedBudgetAt
      bb84CKRPostselectionInnerBudgetOfEpsPAOfTail at hbudget
    have hcorrect : 0 ≤ (2 : ℝ) ^ (-(p.tagLength : ℝ)) := by positivity
    nlinarith
  have hsqrt := Real.sqrt_nonneg
    (2 * klAcceptTailPhaseOnlyDev p.peSel p.xSel p.errorRate p.tolerance dev)
  have hAEP : epsilonAEP < 1 := h.smoothing_lt_one
  have hPA : εPA < 2 := by linarith [h.smoothing_pos]
  have hB : 1 < Real.logb 2 (2 / epsilonAEP ^ 2) :=
    one_lt_logb_two_div_sq epsilonAEP h.smoothing_pos hAEP
  have hpen : 1 < Real.logb 2 (2 / epsilonAEP ^ 2) / β := by
    rw [lt_div_iff₀ h.beta_pos]
    linarith [h.beta_lt_one]
  have hn : 0 < p.sifted := by
    by_contra hn
    have hn0 : p.sifted = 0 := Nat.eq_zero_of_not_pos hn
    have hx : p.xTests = 0 := by simp only [Parameters.sifted] at hn0; omega
    have hs : 1 ≤ Real.sqrt 2 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    simp only [klAcceptTailPhaseOnlyDev, Reduction.packedXTestSampleSize, hx,
      Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, mul_one] at hinner
    linarith [h.smoothing_pos, h.epsPA_pos]
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcharge : -2 < 2 * Real.log (1 / εPA) / Real.log 2 := by
    rw [one_div, Real.log_inv, lt_div_iff₀ hL]
    linarith [Real.log_lt_log h.epsPA_pos hPA]
  have hpost := Real.four_le_two_mul_log_choose_add_three_div_log_two hn
  by_contra hn
  have hzero : p.keyRounds = 0 := Nat.eq_zero_of_not_pos hn
  have hgap := h.penaltyGapAt
  simp only [hzero, finiteSizePenaltySecondOrderSharpAt, Nat.cast_zero, mul_zero, zero_mul,
    zero_add, Comparison.literatureFiniteSizePenalty_zero] at hgap
  linarith

/-- **The general improved row certifies a key strictly longer than the literature length lifted
at the matched Bell-symmetric prefactor `C(n + 3, 3)`, evaluated at the phase-error deviation
`(tolerance + dev)/2`, i.e. the entropy bracket `errorRate + tolerance + dev`.**

On `LiteratureAdvantageRegionAt` there is a key length `ℓ` strictly above
`liftedLiteratureKeyLengthAt 4 ε_tot dev` at which the configured protocol with key length `ℓ`
satisfies `ImprovedConditionsAt`, has general-row improved budget at most the shared total, and
is fully interface-secure at that total (`realIdealDistance_le_improvedBudgetAt`,
`isFullInterfaceSecure_improvedAt`).

The witness is `⌊literature length⌋₊ + 1`
(`Comparison.exists_gt_liftedLiteratureKeyLength_improvedKeyRateConditionAtDev`). -/
theorem exists_keyLength_gt_liftedLiteratureKeyLength_at
    {epsilonAEP εPA β dev epsilonTotal : ℝ}
    (h : p.LiteratureAdvantageRegionAt epsilonAEP εPA β dev epsilonTotal) :
    ∃ ℓ : ℕ,
      p.liftedLiteratureKeyLengthAt 4 epsilonTotal dev < ℓ ∧
        ({ p with keyLength := ℓ }).ImprovedConditionsAt epsilonAEP εPA β dev ∧
        ({ p with keyLength := ℓ }).improvedBudgetAt epsilonAEP εPA dev ≤ epsilonTotal ∧
        ({ p with keyLength := ℓ }).protocol.IsFullInterfaceSecure epsilonTotal := by
  have hK : bb84KeyRoundCount p.sifted p.tests = p.keyRounds := by
    simp only [bb84KeyRoundCount, Parameters.sifted, Parameters.tests]
    omega
  obtain ⟨ℓ, hlt, hkey⟩ :=
    Comparison.exists_gt_liftedLiteratureKeyLength_improvedKeyRateConditionAtDev hK
      h.literatureKeyLength_nonneg h.penaltyGapAt
  have hcond : ({ p with keyLength := ℓ }).ImprovedConditionsAt epsilonAEP εPA β dev :=
    { smoothing_pos := h.smoothing_pos
      keyRate := hkey
      ecTranslationEquivariant := h.ecTranslationEquivariant
      epsPA_pos := h.epsPA_pos
      beta_pos := h.beta_pos
      beta_lt_one := h.beta_lt_one
      dev_nonneg := h.dev_nonneg
      belowThresholdDev := h.belowThresholdDev }
  exact ⟨ℓ, hlt, hcond, h.improvedBudgetAt_le,
    (({ p with keyLength := ℓ }).isFullInterfaceSecure_improvedAt hcond).mono
      h.improvedBudgetAt_le⟩

/-- **The improved row certifies a key strictly longer than the literature length lifted at the
matched Bell-symmetric prefactor `C(n + 3, 3)`.**

On `LiteratureAdvantageRegion` there is a key length `ℓ` strictly above
`liftedLiteratureKeyLength 4 sifted keyRounds tagLength leak errorRate tolerance epsilonTotal` at
which the configured protocol with key length `ℓ` satisfies `ImprovedConditions`, has improved
budget at most the shared total, and is fully interface-secure at that total
(`realIdealDistance_le_improvedBudget`, `isFullInterfaceSecure_of_realIdealDistance_le`).

The arithmetic core is evaluated at `dev = δ`, `ε_PA = exp(−sifted·δ²/2)` and
`β = secondOrderSharpBeta …`; the resulting key-rate condition funds the pinned security theorem. -/
theorem exists_keyLength_gt_liftedLiteratureKeyLength {epsilonAEP epsilonTotal : ℝ}
    (h : p.LiteratureAdvantageRegion epsilonAEP epsilonTotal) :
    ∃ ℓ : ℕ,
      p.liftedLiteratureKeyLength 4 epsilonTotal < ℓ ∧
        ({ p with keyLength := ℓ }).ImprovedConditions epsilonAEP ∧
        ({ p with keyLength := ℓ }).improvedBudget epsilonAEP ≤ epsilonTotal ∧
        ({ p with keyLength := ℓ }).protocol.IsFullInterfaceSecure epsilonTotal := by
  have hK : bb84KeyRoundCount p.sifted p.tests = p.keyRounds := by
    simp only [bb84KeyRoundCount, Parameters.sifted, Parameters.tests]
    omega
  have hhalf : (p.tolerance + p.tolerance) / 2 = p.tolerance := by ring
  have hlog : 2 * Real.log (1 / Real.exp (-(p.sifted : ℝ) * p.tolerance ^ 2 / 2))
      = (p.sifted : ℝ) * p.tolerance ^ 2 := by
    rw [one_div, Real.log_inv, Real.log_exp]
    ring
  obtain ⟨ℓ, hlt, hkey⟩ :=
    Comparison.exists_gt_liftedLiteratureKeyLength_improvedKeyRateConditionAtDev
      (x := 4) (ℓEV := p.tagLength) (leak := p.leak) (Q := p.errorRate)
      (δ := p.tolerance) (dev := p.tolerance) (ε_AEP := epsilonAEP) (ε_tot := epsilonTotal)
      (εPA := Real.exp (-(p.sifted : ℝ) * p.tolerance ^ 2 / 2))
      (β := secondOrderSharpBeta bb84SharpVarianceCap
        (bb84KeyRoundCount p.sifted p.tests) epsilonAEP) hK
      (by simpa only [hhalf] using h.literatureKeyLength_nonneg)
      (by
        rw [hK, ← finiteSizePenaltySecondOrderSharp_eq, hlog]
        exact h.penaltyGap)
  have hcond : ({ p with keyLength := ℓ }).ImprovedConditions epsilonAEP :=
    { belowThreshold := h.belowThreshold
      smoothing_pos := h.smoothing_pos
      keyRate := improvedKeyRateCondition_of_improvedKeyRateConditionAt
        ((improvedKeyRateConditionAtDev_eq _ _ _ _ _ _ _ _ _ _).mp hkey)
      ecTranslationEquivariant := h.ecTranslationEquivariant }
  exact ⟨ℓ, by simpa only [hhalf] using hlt, hcond, h.improvedBudget_le,
    (({ p with keyLength := ℓ }).isFullInterfaceSecure_improved hcond).mono h.improvedBudget_le⟩

end Parameters

end QKD.BB84

end -- noncomputable section
