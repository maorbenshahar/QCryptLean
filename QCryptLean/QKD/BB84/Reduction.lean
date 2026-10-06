import QCryptLean.QKD.BB84.Model
import QCryptLean.QKD.BB84.RealIdeal
import QCryptLean.QKD.BB84.Reduction.Factorization
import QCryptLean.QKD.BB84.Reduction.ModelBridge

/-!
# Reduction of the physical BB84 experiment to its analytical model

`Parameters.realIdealDistance_le_modelDistance` is the single reduction theorem of the physical
security rows: the configured measure-first experiment's normalized real/ideal diamond distance
p.protocol.realIdealDistance is at most the real/ideal distance p.modelDistance of its
analytical model (`QCryptLean.QKD.BB84.Model`).  The finite-key budgets are then proved
about the model alone (`Parameters.modelDistance_le_basicBudget`,
`Parameters.modelDistance_le_improvedBudget`), and each physical security row is the composition of
this theorem with one of them.

The only hypothesis is `[NeZero p.sifted]`, without which the model is not defined.  No budget,
key-rate condition, smoothing parameter, entropy estimate, state assumption, reachability condition
or condition on the error-correction scheme occurs: this is a comparison of two explicit pairs of
maps, and it holds for arbitrary basis laws and an arbitrary physical batch size.

## Route

1. **Coordinates** (`=`).  `Parameters.realIdealDistance_eq_coordinates`: the coordinate-free
   distance is half the diamond norm of the physical real-minus-ideal map in explicit numeral
   coordinates.
2. **Physical to retained** (`≤`).  `Reduction.coordinates_difference_diamondNorm_le_retained`:
   when `sifted ≤ rounds` the physical real-minus-ideal map is the retained experiment's, lifted
   by a control register and sandwiched between a CPTP preprocessor and a CPTP reconstruction
   (`Reduction.coordinates_difference_eq_retainedFactorizedDifference`), and when
   `rounds < sifted` it vanishes identically.  This is the physical disintegration of the
   measure-first run by its sifting and sampling outcomes.
3. **Retained to the model** (`≤`).  `Reduction.retainedAnalysisDifference_diamondNorm_le_model`:
   the retained real and ideal maps are the model's real and ideal maps followed by one classical
   post-processing channel `Reduction.modelPostprocess`
   (`Reduction.retainedAnalysisReal_eq_modelPostprocess_comp`,
   `Reduction.retainedAnalysisIdeal_eq_modelPostprocess_comp`), and post-composing a channel
   cannot increase the diamond norm.  The two maps read the same round-grouped input register.
   Its one structural fact about the configuration is that the announced test positions are the
   positions the packed selector marks (`QKD.BB84.Reduction.packedPESel_keyCount`).

Step 1 is an equality, step 2 carries the physical mathematics, and step 3 is data processing by a
channel, so no constant is lost anywhere.  The security interface is the normalized full real/ideal
distance of Portmann--Renner and Nahar et al., arXiv:2403.11851, Theorem 3.
-/

open QKD.BB84.Model
noncomputable section

namespace QKD.BB84


namespace Parameters

variable (p : Parameters)

/-- **The configured physical experiment is no farther from its ideal key resource than its
analytical model is.**

The left-hand side is the normalized diamond distance between the real map of the actual
measure-first protocol and its derived ideal key resource; the right-hand side is the normalized
diamond distance between the two maps of the analytical model
(`bb84SymRealChannel`/`bb84SymIdealChannel` at the configuration).  The only hypothesis
is that the sifted block is nonempty, which the model needs in order to be defined; basis laws,
physical batch size and error-correction scheme are arbitrary.  See the module docstring for the
three steps. -/
theorem realIdealDistance_le_modelDistance [NeZero p.sifted] :
    p.protocol.realIdealDistance ≤ p.modelDistance := by
  rw [p.realIdealDistance_eq_coordinates]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact (Reduction.coordinates_difference_diamondNorm_le_retained
      p.aliceBasis p.bobBasis p.rounds p.keyRounds p.zTests p.xTests p.keyLength p.tagLength
      p.leak p.ec p.tolerance p.errorRate).trans
    (Reduction.retainedAnalysisDifference_diamondNorm_le_model p.keyRounds p.zTests p.xTests
      p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate)

end Parameters

end QKD.BB84
