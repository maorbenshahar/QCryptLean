import QCryptLean.QKD.BB84.Comparison.MillionSiftedRounds

/-!
# Honest-source acceptance at one million sifted rounds

The physical-input certificate specializes to the canonical honest source and implies
acceptance of at least 99 percent.
-/

namespace QCryptLeanTest.QKD.BB84.Comparison

open _root_.QKD.BB84 _root_.QKD.BB84.Comparison

example : ∃ ec : MillionSiftedECScheme,
    (99 : ℝ) / 100 ≤ (millionSiftedUniformParameters ec).protocol.acceptProbability
      (Measurement.honestSource 4000000 (1 / 200)) := by
  obtain ⟨ec, hDecode, -⟩ := exists_decodesWhp_millionSifted
  have h := millionSiftedUniformParameters_one_sub_le_acceptProbability
    ec hDecode (Measurement.honestSource 4000000 (1 / 200))
    (Measurement.honestOperation_honestSource 4000000 (1 / 200) (by norm_num) (by norm_num))
  exact ⟨ec, (by norm_num : (99 : ℝ) / 100 ≤ 1 - ((2 : ℝ) ^ 17)⁻¹).trans h⟩

end QCryptLeanTest.QKD.BB84.Comparison
