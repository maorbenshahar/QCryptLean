import QCryptLean.QKD.BB84.Security.Basic
import QCryptLean.QKD.BB84.Security.Improved
import QCryptLean.QKD.BB84.Chronology

/-!
# Physical memory-free BB84: security entry point

This module is an import and documentation entry point.  It declares nothing: it exists so that a
client can write

```
import QCryptLean.QKD.BB84.Security
open QKD.BB84.Model
```

and reach the published physical security statements about the *actual* executable memory-free
BB84 experiment, together with the reduction to the analytical model that supports them.  No
alias, wrapper protocol, additional theorem or altered assumption is introduced here.

## Reading the experiment first

The four modules to read, in order, are

1. the Measurement.Weighted and Measurement.Schedule modules — what each
   party measures each round, with independent per-round basis laws;
2. the Measurement.LatePublicControl module — the two basis announcements, the announced
   matched-round shuffle and the sifting or shortage discard;
3. `QCryptLean.QKD.BB84.Program` — the whole experiment in chronological order, with the
   disclosed tests, the fused seed/tag/syndrome announcement and the final decision;
4. `QCryptLean.QKD.BB84.Chronology` — what one finished run looks like: the stage
   decomposition, and `publicTranscriptEquiv`, which identifies a complete public exit with the
   complete public transcript.

`Parameters.acceptFlag_eq_zero_iff` states the accept rule in the physical terms of the
configuration's own fields, and `Parameters.protocol_real` / `protocol_ideal` are the one-step
route from that program to the two maps the bounds below compare.

## The subject

`QKD.BB84.Parameters` is the experiment's physical configuration: the two
per-party basis laws, the physical batch size `rounds`, the packed quotas `keyRounds`, `zTests`,
`xTests`, the key/verification/syndrome lengths, the error-correction scheme for that selector,
and the accept test `|observed − errorRate| ≤ tolerance`.  p.protocol runs the existing
measure-first builder at those choices — definitionally, see `Parameters.protocol_program` — and is
the single subject of every statement below.

Both per-exit quota cases are covered: `Sampling.HasQuotas` and its negation. The inequality
`rounds < sifted` forces every exit into shortage. The complete public transcript, both accepted
keys and the key-free abort payload are retained; the diamond norm quantifies over arbitrary
references.
No caller supplies a channel, an ideal map, a shared key, a coordinate package or a security
premise.

## The distance and the criterion

p.protocol.realIdealDistance is the **normalized** diamond distance between the protocol's real map
and its derived ideal key resource (`QKD.Protocol.realIdealDistance`).  It needs no coordinates:
`QKD.Protocol.realIdealDistance_eq_coordinates` shows that every explicit numeral package — in
particular the low-level `QKD.BB84.coordinates` used by the reduction — computes it.

`p.protocol.IsFullInterfaceSecure ε` is that distance bound **together with**
`Parameters.protocol_acceptedKeyClassical`, the hypothesis-free statement that on every accepting
exit both locally owned key registers are classical.  This is the composable criterion of
Christandl--König--Renner, arXiv:0809.3019, Theorem 1 and Lemma 1, on the full output interface;
it is not Nahar et al.'s Alice-key marginal, half-trace-distance criterion (arXiv:2403.11851,
lines 394--400).

## The route

Both rows run physical program → analytical model → finite-key budget.

* **The analytical model** (`QCryptLean.QKD.BB84.Model`).  `Parameters.modelReal` and
  `Parameters.modelIdeal` are the formula-defined, permutation-symmetrized channel pair
  `bb84SymRealChannel`/`bb84SymIdealChannel` of the sifted, parameter-estimation
  announcing, key-round hashing experiment, at the configuration's own choices, and
  `Parameters.modelDistance` is half the diamond norm of their difference.  The model is an
  analytical device on which the finite-key analysis is stated, not a second protocol.
* **The reduction** (`QCryptLean.QKD.BB84.Reduction`).
  `Parameters.realIdealDistance_le_modelDistance`: `p.protocol.realIdealDistance ≤
  p.modelDistance`, under `[NeZero p.sifted]` only — no budget, security, entropy, reachability,
  state or error-correction hypothesis.  It is shared by both rows.
* **The budgets.**  `Parameters.modelDistance_le_basicBudget` and
  `Parameters.modelDistance_le_improvedBudget` bound the model's distance by the two finite-key
  engine cells, and each security theorem below is the reduction followed by one of them.

## The two finite-key rows

The smoothing parameter `epsilonAEP` is an analysis parameter, not part of the experiment.
Neither row supplies a phase-bad estimate, a reference state, an entropy, a
trace-norm, a diamond-norm or a security premise. Both rows handle an empty sifted block using
the channel-distance bound and invoke the model only for a nonempty block.

* `Parameters.realIdealDistance_le_basicBudget` and `Parameters.isFullInterfaceSecure_basic`
  (`QCryptLean.QKD.BB84.Security.Basic`), under `Parameters.BasicConditions` —
  `Parameters.FiniteKeyRegime` plus `basicKeyRateCondition` — at budget `Parameters.basicBudget`,
  direct correctness `2^(-tagLength)` plus the `C(n+15,15)` lift of the secrecy terms
  `PA + 2 epsilonAEP + 2 √(2E)`, at `n = sifted`. The error-correction scheme is arbitrary: this
  row assumes nothing about `ec` beyond its type.  The finite-key analysis is the phase-only row
  of Nahar et al., arXiv:2403.11851, Theorem 3, Appendix B and Section V.C, with the reference
  analysis of Renner, arXiv:quant-ph/0512258v2, Section 6.5.
* `Parameters.realIdealDistance_le_improvedBudget` and `Parameters.isFullInterfaceSecure_improved`
  (`QCryptLean.QKD.BB84.Security.Improved`), under `Parameters.ImprovedConditions` — the
  positivity of the smoothing parameter, the soundness edge
  `errorRate + 2 * tolerance ≤ 1/2`, the Bell-tight `improvedKeyRateCondition`, and
  `ECScheme.IsTranslationEquivariant`, which is exactly what the Bell `C(n + 3, 3)`
  postselection lift requires — at budget `Parameters.improvedBudget`.  The finite-key analysis adds
  the Dupuis--Fawzi, arXiv:1805.11652, Corollary IV.2 penalty at the sharp variance cap.

Both rows require positive smoothing and a soundness edge at most one half. Each uses the
channel-distance bound of one whenever its smoothing or tail charge makes the budget trivial.
The basic row prices its AEP at Alice's bit register and charges `2 log₂ C(n+15,15)` for the
purifier. The improved row's free-parameter form `Parameters.isFullInterfaceSecure_improvedAt`
also allows every positive privacy-amplification error and every nonnegative deviation `dev`,
with soundness edge `errorRate + tolerance + dev ≤ 1/2`.

Neither row is stronger than the other by fiat: they are two different budgets under two different
key-rate conditions, and the improved one carries the extra equivariance premise.

## Comparison with the literature

`QCryptLean.QKD.BB84.Comparison.ImprovedAdvantage` compares the improved row's key length
against the matched Bell-symmetric lift of Tupkary, Tan and Lütkenhaus, arXiv:2311.01600, at the
same protocol, postselection prefactor and error-correction assumption.
-/
