import QCryptLean.QKD.BB84.QuantitativeRobustness
import QCryptLean.QKD.BB84.LinearReconciliation
import QCryptLean.Math.Analysis.LogBounds
import Mathlib.Util.AssertNoSorry

/-!
# Quantitative BB84 robustness tests

The ten-thousand-round configuration has 1000 key rounds, 1000 tests in each basis,
510 syndrome bits, a 32-bit verification tag, and a one-bit final key. It demonstrates
acceptance of at least nine tenths under its honest decoding assumption; it makes no security
or finite-key-regime claim. The generic examples also check the slack and separating-decoder APIs.
-/

noncomputable section

namespace QCryptLeanTest.QKD.BB84.QuantitativeRobustness

open _root_.LOCC _root_.QKD.BB84 _root_.QKD.BB84.Measurement _root_.QKD.BB84.Sampling

/-- The concrete layout admits a translation-equivariant 510-bit reconciliation scheme. -/
theorem exists_decodesWhp_tenThousandRounds :
    ∃ ec : ECScheme 3000 (@Sampling.packedPESel 1000 1000 1000) 510,
      ec.DecodesWhp (honestKeyErrWeight 3000 0.01
        (@Sampling.packedPESel 1000 1000 1000) (@Sampling.packedXSel 1000 1000 1000))
          (Real.exp (-20) + 1 / 1024) ∧ ec.IsTranslationEquivariant := by
  have hcard := Sampling.card_packedPESel_eq_false 1000 1000 1000
  have hgate : ((0.01 : ℝ) + 0.1) *
      (Fintype.card {i : Fin 3000 // @Sampling.packedPESel 1000 1000 1000 i = false} : ℝ) <
        (110 + 1 : ℝ) := by
    rw [hcard]
    norm_num
  have ht : (110 : ℝ) ≤ 0.11 *
      Fintype.card {i : Fin 3000 // @Sampling.packedPESel 1000 1000 1000 i = false} := by
    rw [hcard]
    norm_num
  have hleak : (Fintype.card
      {i : Fin 3000 // @Sampling.packedPESel 1000 1000 1000 i = false} : ℝ) *
        Math.ClassicalEntropy.binaryEntropyBits 0.11 + 10 ≤ 510 := by
    rw [hcard]
    have hent := Math.ClassicalEntropy.binaryEntropyBits_011_lt_half
    norm_num only [Nat.cast_ofNat]
    linarith
  have h := ECScheme.exists_decodesWhp_linearSyndrome_of_entropy 3000 0.01 0.1 0.11
    (@Sampling.packedPESel 1000 1000 1000) (@Sampling.packedXSel 1000 1000 1000)
    (by norm_num) (by norm_num) (by norm_num) 110 510 10 hgate
    (by norm_num) (by norm_num) ht hleak
  norm_num only [hcard, Nat.cast_ofNat] at h ⊢
  exact h

/-- Uniform-basis parameters with 1000 key rounds, 510 syndrome bits, and a one-bit final key,
configured with the supplied reconciliation scheme. -/
def tenThousandRoundParameters
    (ec : ECScheme 3000 (@Sampling.packedPESel 1000 1000 1000) 510) : Parameters where
  aliceBasis := PMF.uniformOfFintype Basis
  bobBasis := PMF.uniformOfFintype Basis
  rounds := 10000
  keyRounds := 1000
  zTests := 1000
  xTests := 1000
  keyLength := 1
  tagLength := 32
  leak := 510
  ec := ec
  tolerance := 0.06
  errorRate := 0.01

/-- The worked acceptance configuration has a positive final key. -/
example (ec : ECScheme 3000 (@Sampling.packedPESel 1000 1000 1000) 510) :
    0 < (tenThousandRoundParameters ec).keyLength := by
  norm_num [tenThousandRoundParameters]

/-- Its syndrome is shorter than the raw key. -/
example (ec : ECScheme 3000 (@Sampling.packedPESel 1000 1000 1000) 510) :
    (tenThousandRoundParameters ec).leak < (tenThousandRoundParameters ec).keyRounds := by
  norm_num [tenThousandRoundParameters]

/-- Every exponential tail with exponent at most minus five is below one hundredth. -/
private lemma exp_neg_le_one_hundredth {x : ℝ} (hx : 5 ≤ x) : Real.exp (-x) ≤ 1 / 100 := by
  have h := Real.exp_neg_le_inv_two_pow (m := 7) (x := x) (by
    have hlog := Real.log_two_lt_d9
    norm_num only [Nat.cast_ofNat]
    linarith)
  norm_num at h
  linarith

/-- The complete quota, test, decoding-tail, and collision budget is at most one tenth. -/
lemma tenThousandRound_hoeffdingAbortBound_le :
    hoeffdingAbortBound 10000 1000 1000 0.02 0.05 (Real.exp (-20) + 1 / 1024) ≤ 1 / 10 := by
  norm_num [hoeffdingAbortBound,
    Math.Concentration.hoeffdingTwoSidedTail, hoeffdingTestAbortBound,
    Math.Concentration.hoeffdingTwoSidedTail]
  have h8 := exp_neg_le_one_hundredth (x := 8) (by norm_num)
  have h5 := exp_neg_le_one_hundredth (x := 5) (by norm_num)
  have h20 := exp_neg_le_one_hundredth (x := 20) (by norm_num)
  linarith

/-- Every scheme meeting the stated honest decoding budget gives acceptance probability at least
nine tenths at QBER `0.01` in the concrete configuration. -/
theorem tenThousandRoundParameters_acceptProbability_honestSource
    (ec : ECScheme 3000 (@Sampling.packedPESel 1000 1000 1000) 510)
    (hDecode : ec.DecodesWhp (honestKeyErrWeight 3000 0.01
      (@Sampling.packedPESel 1000 1000 1000) (@Sampling.packedXSel 1000 1000 1000))
        (Real.exp (-20) + 1 / 1024)) :
    (9 / 10 : ℝ) ≤ (tenThousandRoundParameters ec).protocol.acceptProbability
      (honestSource (tenThousandRoundParameters ec).rounds 0.01) := by
  have hbudget := tenThousandRound_hoeffdingAbortBound_le
  have h := Parameters.one_sub_hoeffdingAbortBound_le_acceptProbability
    (tenThousandRoundParameters ec)
      (honestSource (tenThousandRoundParameters ec).rounds 0.01) 0.01
      (Real.exp (-20) + 1 / 1024) 0.05 0.02
      ⟨by norm_num, by norm_num [tenThousandRoundParameters], hDecode⟩
      ⟨by norm_num, by norm_num [tenThousandRoundParameters],
        by norm_num [tenThousandRoundParameters]⟩
      (honestOperation_honestSource _ _ (by norm_num) (by norm_num))
  change 1 - hoeffdingAbortBound 10000 1000 1000 0.02 0.05
    (Real.exp (-20) + 1 / 1024) ≤ _ at h
  linarith

/-- The linear-slack API applies directly to the fields of a configured physical program; the
sampling slack `ηS` and parameter-estimation margin `η` remain distinct. -/
example (p : Parameters) (q εEC η ηS : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hη : 0 < η) (hband : |q - p.errorRate| ≤ p.tolerance - η)
    (hDecode : p.ec.DecodesWhp (honestKeyErrWeight p.sifted q p.peSel p.xSel) εEC)
    (hηS : 0 ≤ ηS)
    (hZ : (p.keyRounds + p.zTests : ℝ) ≤
      ((matchedProb p.aliceBasis p.bobBasis .z).toReal - ηS) * p.rounds)
    (hX : (p.xTests : ℝ) ≤
      ((matchedProb p.aliceBasis p.bobBasis .x).toReal - ηS) * p.rounds) :
    p.protocol.abortProbability (honestSource p.rounds q) ≤
      hoeffdingAbortBound p.rounds p.zTests p.xTests ηS η εEC :=
  QKD.BB84.Parameters.HonestBand.abortProbability_honestSource_le_hoeffdingAbortBound p q εEC η ηS
    hq0 hq
    ⟨hη, hband, hDecode⟩ ⟨hηS, hZ, hX⟩

/-- A separating syndrome gives a deterministic decoding guarantee independently of a noise law. -/
example (n : ℕ) (peSel : Fin n → Bool) (t leakEC : ℕ)
    (hvol : ((Finset.univ.filter (fun e : KeyBitString n peSel => hammingDist e 0 ≤ 2 * t)).card :
      ℝ) < (2 : ℝ) ^ leakEC) :
    ∃ ec : ECScheme n peSel leakEC, ec.IsTranslationEquivariant ∧
      ∀ a b, hammingDist a b ≤ t → ec.decode b (ec.syndrome a) = a :=
  ECScheme.exists_decode_eq_of_hammingDist_le n peSel t leakEC hvol

end QCryptLeanTest.QKD.BB84.QuantitativeRobustness
