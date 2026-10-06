import QCryptLean.QKD.BB84.Security.FiniteKeyRegime
import QCryptLean.QKD.BB84.Reduction
import QCryptLean.QKD.BB84.Engine.Standard

/-!
# Basic security of the physical memory-free BB84 program

The main result is a normalized diamond bound on the distance between the *configured* physical
experiment's real map and its derived ideal key resource, at the standard packed-selector
finite-key budget.  The error-correction scheme is arbitrary in this row.

## Route

physical program → analytical model → finite-key budget:

1. `Parameters.realIdealDistance_le_modelDistance` (`QCryptLean.QKD.BB84.Reduction`): the
   physical experiment's real/ideal distance is at most that of its analytical model
   `Parameters.modelReal`/`Parameters.modelIdeal` (`QCryptLean.QKD.BB84.Model`), with no
   hypothesis beyond a nonempty sifted block.
2. `Parameters.modelDistance_le_basicBudget` (below): the model is within `basicBudget`.  This is
   the finite-key engine cell `bb84_ckr_security_klTailPhaseOnly` at the configuration, whose
   key-count premise follows from `packedPESel_keyCount`. Its KL tail reads the realised X-test
   sample through the configured selectors.

The finite-key analysis is the phase-only row grounded in Nahar et al., arXiv:2403.11851,
Theorem 3, Appendix B and Section V.C, with the reference analysis of Renner,
arXiv:quant-ph/0512258v2, Section 6.5, and the postselection lift of Christandl--Koenig--Renner,
arXiv:0809.3019, Theorem 1 and Lemma 1. The normalized security distance follows
Portmann--Renner and Nahar et al.
-/

noncomputable section

namespace QKD.BB84
open QKD.BB84.Reduction

open QKD.BB84.Engine
open QKD.BB84.Model

namespace Parameters

variable (p : Parameters)

/-- **The conditions of the standard finite-key row.**

The standard elementary regime plus the standard key-rate condition
`basicKeyRateCondition`, which prices the final key length, the announced syndrome and
verification tag, the de Finetti prefactor and the smoothing penalty against the key block's
entropy at the tested error rate.

There is **no condition on the error-correction scheme** in this row: `ec` is arbitrary.  The
improved row's translation-equivariance premise is not required here, and this row is not a
consequence of that one. -/
structure BasicConditions (epsilonAEP : ℝ) : Prop extends FiniteKeyRegime p epsilonAEP where
  /-- The standard general-`m` key-rate condition at these lengths and this smoothing. -/
  keyRate : basicKeyRateCondition p.sifted p.tests p.keyLength p.tagLength p.leak
    p.errorRate p.tolerance epsilonAEP

/-- The basic normalized diamond-distance budget.

Correctness contributes `2^(-tagLength)` directly. Secrecy contributes
`C(sifted+15,15) * (PA + 2 epsilonAEP + 2 √(2E))`, where `E` is the exact realised-X KL tail
and `PA = ½ exp(-keyRounds/4 * (log 2 - h(errorRate + 2 tolerance)))`.

References: Nahar et al. 2024, arXiv:2403.11851, Appendix B;
Christandl–König–Renner 2009, arXiv:0809.3019, Theorem 1. -/
def basicBudget (epsilonAEP : ℝ) : ℝ :=
  standardBudgetOfTail
    (klAcceptTailPhaseOnly p.peSel p.xSel p.errorRate p.tolerance)
    p.sifted p.tests p.tagLength p.errorRate p.tolerance epsilonAEP

/-- The configured analytical model satisfies the basic budget.
The packed selectors give the engine's key-count identity. Positive smoothing, the soundness
edge at most one half, and the key-rate condition are the fields of `BasicConditions`.
The decoder is arbitrary. -/
theorem modelDistance_le_basicBudget [NeZero p.sifted] {epsilonAEP : ℝ}
    (h : p.BasicConditions epsilonAEP) :
    p.modelDistance ≤ p.basicBudget epsilonAEP :=
  bb84_ckr_security_klTailPhaseOnly p.peSel p.xSel
    (packedPESel_keyCount p.keyRounds p.zTests p.xTests) p.ec p.errorRate p.tolerance
    epsilonAEP h.belowThreshold h.keyRate h.smoothing_pos

/-- **The configured measure-first BB84 experiment is within the standard finite-key budget of its
ideal key resource, in normalized diamond distance.**

The bound is on the derived real and ideal maps of the actual executable protocol: no phase-bad
estimate, reference state, entropy, trace-norm, diamond-norm or security premise is supplied, the
basis laws and the error-correction scheme are arbitrary, and the statement is total in the
physical batch size — an infeasible quota takes the actual all-shortage branch. -/
theorem realIdealDistance_le_basicBudget {epsilonAEP : ℝ}
    (h : p.BasicConditions epsilonAEP) :
    p.protocol.realIdealDistance ≤ p.basicBudget epsilonAEP := by
  by_cases hn : p.sifted = 0
  · have hone : p.protocol.realIdealDistance ≤ 1 := by
      rw [p.realIdealDistance_eq_coordinates,
        QKD.Protocol.NumeralCoordinates.difference_eq_real_sub_ideal]
      change (1 / 2) * Quantum.Channels.diamondNorm
        (p.coordinates.real - p.coordinates.ideal) ≤ 1
      have hnorm := Quantum.Channels.diamondNorm_sub_le_two p.coordinates.real_isCPTP
        p.coordinates.ideal_isCPTP
      linarith only [hnorm]
    refine hone.trans ?_
    have hx : p.xTests = 0 := by simp only [Parameters.sifted] at hn; omega
    have hs : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    unfold basicBudget standardBudgetOfTail bb84CKRPostselectionInnerBudgetOfTail
    simp only [klAcceptTailPhaseOnly, packedXTestSampleSize, hx, hn, Nat.cast_zero,
      neg_zero, zero_mul, Real.exp_zero, bb84KeyRoundCount, Nat.zero_sub, zero_div]
    norm_num only [signalDim, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.choose_self,
      Nat.cast_one, one_mul, mul_one]
    have hc : 0 ≤ (2 : ℝ) ^ (-(p.tagLength : ℝ)) := by positivity
    linarith [h.smoothing_pos]
  · have : NeZero p.sifted := ⟨hn⟩
    exact p.realIdealDistance_le_modelDistance.trans (p.modelDistance_le_basicBudget h)

/-- The configured experiment is fully interface-secure at the standard finite-key budget.

This is the diamond bound above together with the accepted-key classicality of the real output
(`protocol_acceptedKeyClassical`), i.e. the complete full-interface criterion. -/
theorem isFullInterfaceSecure_basic {epsilonAEP : ℝ} (h : p.BasicConditions epsilonAEP) :
    p.protocol.IsFullInterfaceSecure (p.basicBudget epsilonAEP) :=
  p.isFullInterfaceSecure_of_realIdealDistance_le (p.realIdealDistance_le_basicBudget h)

end Parameters

end QKD.BB84
