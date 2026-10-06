import QCryptLean.QKD.BB84.Parameters
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.Quantum.Channels.CPTP.DiamondNorm

-- The single over-long line in this file is the import path of the module defining the channel
-- pair; it is one unbreakable module name.  No prose or expression line is over budget.

/-!
# The analytical model of a configured memory-free BB84 experiment

The finite-key analysis of both security rows is not carried out on the executable program
`QKD.BB84.Parameters.protocol` itself but on one explicit, formula-defined pair of channels: the
**analytical model** of the configured experiment.  This module names that pair and the diamond
distance between its two maps.

**The model is the permute-then-measure virtual protocol**: it averages over the round
permutations first and only then applies the (now IID) sifting rotation and measurement, whereas
the physical experiment measures round by round as it goes.  The reduction from the physical
experiment to the model consists of exact channel identities plus data processing by CPTP maps, so
no slack is introduced.

* `Parameters.modelReal` is `bb84SymRealChannel` at the configuration's own choices: sifted
  block size `sifted = keyRounds + zTests + xTests`, test-set size `tests = zTests + xTests`, final
  key length `keyLength`, verification-tag length `tagLength`, the packed selectors `peSel`/`xSel`,
  syndrome length `leak`, the error-correction scheme `ec`, and the accept test centred at
  `errorRate` with half-width `tolerance`.  On a `4 ^ sifted`-dimensional input (one Alice–Bob
  qubit pair per sifted round) it averages over the `sifted!` permutations of the rounds and, for
  each permutation, applies the local sifting rotation, the destructive two-basis measurement, the
  announced parameter-estimation test on the `tests` test rounds, the announced error-correction
  syndrome, the announced error-verification tag and the key-round hash, and appends the
  permutation as a public register.  This is the classical part of the protocol of Nahar,
  Tupkary, Zhao, Lütkenhaus and Tan, arXiv:2403.11851, Section V.C
  (`main.tex:906-919`), at a general test-set size `m = tests`.
* `Parameters.modelIdeal` is the matching `bb84SymIdealChannel`: on the accepting branch one fresh
  uniform key is written into both key registers, and the abort branch is the real one.
* `Parameters.modelDistance` is half the diamond norm of `modelReal - modelIdeal`, the
  distinguishing-advantage convention of Portmann--Renner and Nahar et al., and exactly the
  left-hand side of the finite-key engine theorems `bb84_ckr_security_klTailPhaseOnly` and
  `ckrSecurity_bellTight_tightRate_sharpCharge_secondOrderSharp_klTailPhaseOnly`.

## An analytical device, not a second protocol

The model is not an alternative executable experiment and no security statement is made about it
as a protocol.  Its only role is to be the object the finite-key analysis is stated on:
`QCryptLean.QKD.BB84.Reduction` proves that the configured physical experiment's
real/ideal distance is at most `modelDistance`, and `Parameters.modelDistance_le_basicBudget`
(`QCryptLean.QKD.BB84.Security.Basic`) and `Parameters.modelDistance_le_improvedBudget`
(`QCryptLean.QKD.BB84.Security.Improved`) bound `modelDistance`.

The average over the `sifted!` round orderings is what makes the model permutation covariant
(`bb84SymChannels_permCov`), the input of the postselection lift.  Its counterpart in the
physical experiment is the announced uniform shuffle of the matched rounds, in the
Measurement.LatePublicControl module.

`[NeZero p.sifted]` is required because the channel pair is only defined on a nonempty sifted block;
the finite-key rows derive it from the positivity of their key block.
-/

noncomputable section

namespace QKD.BB84

open QKD.BB84.Engine
open QKD.BB84.Model

namespace Parameters

variable (p : Parameters) [NeZero p.sifted]

/-- **The real map of the analytical model of the configured experiment.**

The general-`m` symmetrized real channel `bb84SymRealChannel` at sifted block size p.sifted,
test-set size p.tests, key length p.keyLength, verification-tag length p.tagLength, accept-test
centre p.errorRate and half-width p.tolerance, the packed selectors p.peSel/p.xSel, syndrome
length p.leak and the configured scheme p.ec.  See the module docstring for what the channel
does. -/
def modelReal :
    Quantum.Operators.Op (4 ^ p.sifted) →ₗ[ℂ]
      Quantum.Operators.Op
        (bb84EveVisiblePEAnnounceSymOutputDim p.sifted p.tests p.keyLength p.tagLength
          p.peSel p.leak 1) :=
  bb84SymRealChannel p.sifted p.tests p.keyLength p.tagLength p.errorRate p.tolerance
    p.peSel p.xSel p.leak p.ec

/-- **The ideal map of the analytical model of the configured experiment.**

The general-`m` symmetrized ideal channel `bb84SymIdealChannel` at the same arguments as
`modelReal`: key replacement by one uniform shared key on the accepting branch, and the real abort
branch. -/
def modelIdeal :
    Quantum.Operators.Op (4 ^ p.sifted) →ₗ[ℂ]
      Quantum.Operators.Op
        (bb84EveVisiblePEAnnounceSymOutputDim p.sifted p.tests p.keyLength p.tagLength
          p.peSel p.leak 1) :=
  bb84SymIdealChannel p.sifted p.tests p.keyLength p.tagLength p.errorRate p.tolerance
    p.peSel p.xSel p.leak p.ec

/-- **The real/ideal distance of the analytical model**: half the diamond norm of
`modelReal - modelIdeal`.

This is the quantity the finite-key engine bounds, in the distinguishing-advantage convention of
Portmann--Renner and Nahar et al., arXiv:2403.11851, Theorem 3.  The diamond norm quantifies
over arbitrary reference systems. -/
def modelDistance : ℝ :=
  (1 / 2) * Quantum.Channels.diamondNorm (p.modelReal - p.modelIdeal)

end Parameters

end QKD.BB84
