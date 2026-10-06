import QCryptLean.Quantum.Channels.CPTP.BlockPinchingChannel
import QCryptLean.QKD.BB84.Model.Real
import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.EveVisibleProtocol
import QCryptLean.QKD.BB84.Model.PermAnnounceRegister
import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.Basic

/-!
# The genuine-LOCC PE-announce channel layer

The Alice-hash/Bob-decode PE-announce channel layer, at a general test-set size `m`:

- **Alice-hash / Bob-decode key.** The pass transcript writes `(kA, kB, flag = 0, st, evTag, syn,
pe)`
  with `kA = hash_s(aliceKeyString ω)`, `kB = hash_s(decode(bobKeyString ω, syn))`,
  `syn = ec.syndrome(aliceKeyString ω)` — each key slot a function of ONE party's data plus
  announcements.
- **Announced syndrome and error-verification tag.** The inner transcript carries the `2^leakEC`
  error-correction syndrome factor and the `2^ℓEV` error-verification tag factor, and the seed is
  the announced pair `KeyHashSeedPairEV n ℓ ℓEV peSel` (privacy-amplification seed ×
  error-verification seed) on the Alice-bit domain — all inside the base output, left of the `n!`
  announce register.
- **Fail-closed LOCC two-basis PE, AND error verification.** The pass/fail gate is
  `bb84SiftedLocalPEAndEVPassed`: the fail-closed local two-basis test conjoined with the
  error-verification tag match (Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024, `arXiv:2403.11851`
  §V.C "Classical part", `main.tex:906`–`919`, the error-verification-by-hash-comparison step at
  `main.tex:917`). The EV gate is what makes the `(k, k)` ideal legitimate against an arbitrary
  attack: correctness no longer rests on any property of `ec`.
- **The `(k, k)` ideal.** The ideal pass writes ONE fresh uniform key in BOTH slots, same
  `st/evTag/syn/pe`; the fail branch is literally shared with the real map, seed-indexed and at the
  same seed-pair scale on both.
- **Deliberate over-disclosure on abort.** `st`, `evTag`, `syn` and `pe` are written on BOTH
  branches, so Eve is handed the reconciliation messages even when the protocol aborts. That is more
  than the literature protocol reveals, hence conservative, and it keeps the real and ideal fail
  branches literally identical.

## Main definitions

* `bb84SiftedConjChannel` / `bb84SiftedConjAfterPre` — the LOCC sifted conjugation /
  conjugation-after-pre channels: conjugation by `bb84SiftedRotation peSel xSel ⊗ 1_E` (the local
  `H ⊗ H` sift).
* `bb84PEAnnounceBaseTranscriptDim` … `bb84EveVisiblePEAnnounceSymOutputDim` — the transcript and
  output dimensions (announced seed pair `KeyHashSeedPairEV`, `2^ℓEV` EV-tag factor, `2^leakEC`
  syndrome factor, announced PE block), at a general test-set size `m`.
* `bb84.pePassOutIndex` / `bb84.peFailOutIndex` — the pass `(kA, kB, 0, st, evTag, syn, pe)` /
  fail `(0, 0, 1, st, evTag, syn, pe)` transcript indices.
* `bb84.retainedSiftedPEAnnouncePassBranchKraus` / `…FailBranchKraus` / `…IdealPassKraus` —
  the pass / (shared, seed-indexed) fail / ideal-pass Kraus operators.
* `bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap` / `…IdealKeyAndAbortChannel` —
  the real / ideal privacy-amplification-and-abort maps.
* `bb84SiftedPEAnnounceEveVisibleProtocol` — the `BB84EveVisibleProtocolScheme` instance.
* `bb84SiftedPEAnnounceLinear` / `…LinearEveVisible` — the public-permutation-announcement maps.
* `bb84SymSiftedRealChannelDirect_withPEAnnounce` / `…IdealChannelDirect…` — the symmetrized
  direct retained-Eve channels (threading the LOCC sift-after-pre channel `bb84SiftedConjAfterPre`,
  so completeness and security refer to the same `bb84SiftedRotation`-conjugated protocol).
* `bb84SymRealChannel` / `bb84SymIdealChannel` — the attack-free (bare retained-Eve slot)
  specializations.

## Main results

* `retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap_isCPTP` /
  `…IdealKeyAndAbortChannel_isCPTP` — the real/ideal privacy-amplification-and-abort maps are CPTP.
  The completeness `∑ Kᴴ K = 1` is output-index-independent, so each Kraus adjoint product
  collapses onto the input outcome diagonal; the accept/reject partition is taken per
  `(seed pair, outcome)` and the recombined branches are collapsed over the seed register by
  `keyHashSeedPair_outcomeProjector_card_collapse`.
* `bb84SymChannels_permCov` — the bare real/ideal difference is permutation covariant, proved by
  porting the announcement-correction chain to the enlarged transcript (the equivariance engine
  `bb84SymAverage_permuteSignal_eveVisible_equivariant_withPEAnnounce` takes the whole
  pre-announcement map as an arbitrary linear map over a bare retained-Eve dimension, so it names
  no attack object).
* `bb84SymRealChannel_eq_direct_unitRegisterEmbed` / `…IdealChannel…` — the bare channels are
  definitionally the slot-carrying direct channels at the trivial retained-Eve instantiation.

## References

Renner 2005 (`arXiv:quant-ph/0512258v2`) §5, §6.5; Christandl-König-Renner 2009
(`arXiv:0809.3019`) `main.tex:268`–`:401` (Main Result: Theorem `\label{thm:main}` :291–:301, Lemma
`\label{lem:extractpart}` :319–:328); Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(`arXiv:2403.11851`) Thm 3, §V.C, and `main.tex:909`/`:913` for the general test-set size `m`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open Quantum.Symmetry
open QKD.BB84.Model
open QKD.BB84.Engine
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Model

namespace bb84

/-!
### CPTP machinery for the real privacy-amplification/abort map

For a single-entry Kraus operator the WHOLE output index `(kA, kB, flag, st, evTag, syn, pe)` — the
EV tag included — cancels in the adjoint product, leaving the input-outcome projector.

The accept/reject partition is per `(st, ω)` rather than per `ω` alone, because the gate
`bb84SiftedLocalPEAndEVPassed` reads the error-verification half of the announced seed pair `st`;
and the fail branch is seed-indexed and carries the same `1/|ST|` scale as the pass branch. The two
branch sums therefore do not collapse separately over the seed register — they are recombined
first, at fixed `(st, ω)`, where accept and reject exhaust the cases, and only the recombined sum is
collapsed over the seed pairs.
-/

/-- The uniform seed-pair Kraus normalization `1/√|KeyHashSeedPairEV n ℓ ℓEV peSel|`, so that
    summing its squared modulus over all announced seed pairs gives the uniform-average Kraus
    completeness; it scales both branches. -/
private noncomputable def keyHashSeedKrausScale (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) : ℂ :=
  (Real.sqrt ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ)⁻¹) : ℂ)

private lemma keyHashSeedKrausScale_mul_star (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) :
    keyHashSeedKrausScale n ℓ ℓEV peSel * star (keyHashSeedKrausScale n ℓ ℓEV peSel) =
      (1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) := by
  unfold keyHashSeedKrausScale
  rw [show star ((Real.sqrt ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ)⁻¹) : ℂ)) =
      (Real.sqrt ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ)⁻¹) : ℂ) by
        simp [Complex.conj_ofReal]]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt]
  · simp [one_div]
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

private lemma keyHashSeedKrausScale_star_mul (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) :
    star (keyHashSeedKrausScale n ℓ ℓEV peSel) * keyHashSeedKrausScale n ℓ ℓEV peSel =
      (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ := by
  rw [mul_comm, keyHashSeedKrausScale_mul_star]
  simp [one_div]

/-- **The seed-pair card collapse.**  A per-`(st, ω)` outcome projector weighted by `1/|ST|`, summed
    over all announced seed pairs and all outcomes, is the identity: the seed sum contributes
    exactly `|ST|` copies of the `1/|ST|`-weighted projector, and the outcome/Eve sum resolves the
    identity (`bb84OutcomeEve_single_sum`).

    This is the step the pre-EV chain did not need on the fail branch, which was then unscaled and
    indexed by `ω` alone; with the fail branch seed-indexed and scaled (items 12 and 14) both the
    real and the ideal completeness proofs route through it. -/
private lemma keyHashSeedPair_outcomeProjector_card_collapse
    (n ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)] (peSel : Fin n → Bool) :
    (∑ idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
      ∑ r : Fin eveDim,
        Matrix.single
          (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
          (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
          ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹)) =
      (1 : Op (4 ^ n * eveDim)) := by
  classical
  have hcard : (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ ω : Fin n → Fin signalDim, ∑ _st : KeyHashSeedPairEV n ℓ ℓEV peSel,
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv (finFunctionFinEquiv ω, r))
            (finProdFinEquiv (finFunctionFinEquiv ω, r))
            ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹))
        = ∑ idx : (Fin n → Fin signalDim) × Fin eveDim,
            Matrix.single
              (finProdFinEquiv (finFunctionFinEquiv idx.1, idx.2))
              (finProdFinEquiv (finFunctionFinEquiv idx.1, idx.2)) (1 : ℂ) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.sum_const, Finset.card_univ, Finset.smul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Matrix.smul_single, nsmul_eq_mul, mul_inv_cancel₀ hcard]
    _ = 1 := bb84OutcomeEve_single_sum n eveDim

/-!
### CPTP machinery for the ideal privacy-amplification/abort map

The ideal twin of the chain above.  The fresh-uniform-key average (`2^ℓ`) and the seed-pair average
(`|KeyHashSeedPairEV n ℓ ℓEV peSel|`) combine into the single ideal-pass scale
`idealKeyHashSeedKrausScale`, while the shared fail branch keeps the seed-pair scale
`keyHashSeedKrausScale`.  The `k`-sum on the pass branch cancels the extra `2^ℓ`, after which the
two branches recombine per `(st, ω)` exactly as in the real case.
-/

/-- The uniform key×seed-pair Kraus normalization `1/√(2^ℓ · |KeyHashSeedPairEV n ℓ ℓEV peSel|)` for
    the ideal pass branch: the fresh-uniform-key average (`2^ℓ`) times the seed-pair average. -/
private noncomputable def idealKeyHashSeedKrausScale (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) : ℂ :=
  (Real.sqrt (((2 ^ ℓ : ℝ) * (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ))⁻¹) : ℂ)

private lemma idealKeyHashSeedKrausScale_mul_star (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) :
    idealKeyHashSeedKrausScale n ℓ ℓEV peSel * star (idealKeyHashSeedKrausScale n ℓ ℓEV peSel) =
      (1 / ((2 ^ ℓ : ℂ) * (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ))) := by
  unfold idealKeyHashSeedKrausScale
  rw [show star
      ((Real.sqrt (((2 ^ ℓ : ℝ) * (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ))⁻¹) : ℂ)) =
      (Real.sqrt (((2 ^ ℓ : ℝ) * (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ))⁻¹) : ℂ) by
        simp [Complex.conj_ofReal]]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt]
  · push_cast
    simp [one_div]
  · exact inv_nonneg.mpr (by positivity)

private lemma idealKeyHashSeedKrausScale_star_mul (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) :
    star (idealKeyHashSeedKrausScale n ℓ ℓEV peSel) * idealKeyHashSeedKrausScale n ℓ ℓEV peSel =
      ((2 ^ ℓ : ℂ) * (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ))⁻¹ := by
  rw [mul_comm, idealKeyHashSeedKrausScale_mul_star]
  simp [one_div]

/-- The ideal pass-branch adjoint sum reindexes to the seed-pair form of the real pass branch:
    averaging the `1/(2^ℓ · |ST|)`-weighted projector over the `2^ℓ` fresh keys cancels the `2^ℓ`,
    leaving the `1/|ST|`-weighted projector indexed by `(seed pair, outcome)`. -/
private lemma retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_pass_sum
    (n ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    (∑ idx : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel,
      if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.2.2.2 idx.1 then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv (finFunctionFinEquiv idx.1, r))
            (finProdFinEquiv (finFunctionFinEquiv idx.1, r))
            (((2 ^ ℓ : ℂ) * (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ))⁻¹)
      else 0) =
    (∑ idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
      if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
            (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
            ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹)
      else 0) := by
  classical
  have hcard : (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h2 : ((2 : ℂ) ^ ℓ) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun st _ => ?_
  by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω
  · simp only [h, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Matrix.smul_single, nsmul_eq_mul]
    congr 1
    push_cast
    field_simp
  · simp [h]

end bb84

namespace bb84

end bb84

/-! ## The LOCC sifted conjugation and attack channels -/

/-- **The sifted conjugation channel** `(bb84SiftedRotation peSel xSel ⊗ 1_E)`-conjugation.

A single-Kraus map whose Kraus operator is the LOCC-implementable sift
`bb84SiftedRotation n peSel xSel ⊗ 1_E` (the local `H ⊗ H` on the `peSel ∧ xSel` X-test rounds,
identity elsewhere). Complete positivity is automatic from `krausMapFintype_isCompletelyPositive`;
trace preservation holds because the Kraus operator is unitary
(`bb84SiftedRotation_tensor_one_unitary`). -/
def bb84SiftedConjChannel (n eveDim : ℕ) (peSel xSel : Fin n → Bool) :
    Op (4 ^ n * eveDim) →ₗ[ℂ] Op (4 ^ n * eveDim) :=
  krausMapFintype (n := 4 ^ n * eveDim) (m := 4 ^ n * eveDim) (κ := Unit)
    (fun _ => Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))

/-- The sifted conjugation channel is CPTP (single unitary Kraus operator). -/
theorem bb84SiftedConjChannel_isCPTP (n eveDim : ℕ) [NeZero (4 ^ n * eveDim)]
    (peSel xSel : Fin n → Bool) :
    IsCPTP (⇑(bb84SiftedConjChannel n eveDim peSel xSel)) := by
  refine krausMapFintype_isCPTP (n := 4 ^ n * eveDim) (m := 4 ^ n * eveDim) (κ := Unit)
    (fun _ => Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim)) ?_
  have h := bb84SiftedRotation_tensor_one_unitary n peSel xSel eveDim
  simpa using h

/-- **The sift conjugation composed after a pre-channel**
`(bb84SiftedRotation peSel xSel ⊗ 1_E)-conjugation ∘ pre`.

The LOCC conjugation `bb84SiftedConjChannel` is inserted *after* the pre-channel and before the
computational-basis measurement.

Indexed by a bare retained-Eve dimension `eveDim` and an opaque pre-channel `pre` rather than by an
attack object: the attack instance is `eveDim := atk.eveDim`, `pre := attackChannelLinear atk`; the
bare instance is `eveDim := 1`, `pre := bb84UnitRegisterEmbed n`.  Only the LOCC sift is named here
— the pre-channel is whatever the caller supplies. -/
noncomputable def bb84SiftedConjAfterPre {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ)
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (peSel xSel : Fin n → Bool) :
    Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim) :=
  (bb84SiftedConjChannel n eveDim peSel xSel).comp pre

/-- The sift conjugation after a CPTP pre-channel is CPTP. -/
theorem bb84SiftedConjAfterPre_isCPTP {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) :
    IsCPTP (⇑(bb84SiftedConjAfterPre eveDim pre peSel xSel)) := by
  have h :=
    cptp_comp
      (⇑(bb84SiftedConjChannel n eveDim peSel xSel))
      (⇑pre)
      (bb84SiftedConjChannel_isCPTP n eveDim peSel xSel)
      hpre
  simpa [bb84SiftedConjAfterPre, LinearMap.comp_apply, Function.comp_apply] using h

/-!
### Announcement-correction covariance substrate

The machinery behind `bb84SymChannels_permCov`, at the (Alice-bit seed + `2^leakEC` syndrome
factor) enlarged base: the `2^leakEC` syndrome factor and the Alice-bit seed sit inside
`bb84PEAnnounceBaseOutputDim`, strictly left of the `n!` announce register, so the permutation
correction is the identity on the `base ⊗ PE` block and relabels only the `n!` announce slot.
-/

/-! ## The PE-announce family at a general test-set size `m`

Nahar, Tupkary, Zhao, Lütkenhaus and Tan state the protocol for a **general** test-set size `m`:
arXiv:2403.11851, `main.tex:909` ("They then choose a random subset of $m$ signals, and
announce their measurement outcomes for those rounds in the register $\Cat^m$") and `:913` ("For the
remaining $\nkey=n-m$ signals"), both inside `\subsection{Classical part}` (`:906`) of
`\section{Application to the Three State Protocol}` (`\label{sec:applicationtothreestate}`, `:829`).
The declarations below are stated over `bb84KeyRoundCount n m = n − m`, the general-`m` round
partition `bb84PartEquiv`, and the announced PE register `signalDim ^ (n − bb84KeyRoundCount n m)`,
with no constraint relating `m` to `n`.

The general-`m` forms carry **no** constraint relating `m` to `n`.  The split point enters this file
in exactly two places — the exponent of the announced PE register, and the PE component
`(bb84PartEquiv peSel ω).2` of the round partition that is written into it — and neither the
Kraus completeness nor the announcement covariance ever reads that register: in `…_adjoint_mul` the
whole `(kA, kB, flag, st, evTag, syn, pe)` output index cancels, and the equivariance engine
`bb84SymAverage_permuteSignal_eveVisible_equivariant_withPEAnnounce` quantifies over an
arbitrary `F : Perm (Fin n) → Op (baseOutputDim)`.  In particular no `m ≤ n`, no `m < n`, no
`2·m ≤ n` and no `bb84KeyCount` hypothesis appears below; `m = 0` and `m = n` are covered and
degenerate rather than excluded.
-/

/-- The **base PE-announce transcript dimension at a general test-set size `m`**: `2 · inner`
    (accept flag × seed pair × EV tag × syndrome × PE).
-/
abbrev bb84PEAnnounceBaseTranscriptDim (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) : ℕ :=
  2 * bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC

/-- The **base PE-announce output dimension at a general test-set size `m`**:
    `2^ℓ · 2^ℓ · (2 · inner)` — the two hashed-key copies `(kA, kB)` times the base transcript.
-/
abbrev bb84PEAnnounceBaseOutputDim (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) : ℕ :=
  2 ^ ℓ * 2 ^ ℓ * bb84PEAnnounceBaseTranscriptDim n m ℓ ℓEV peSel leakEC

/-- The **base PE-announce output with Eve retained** as a right tensor factor, at a general
    test-set size `m`.
-/
abbrev bb84EveVisiblePEAnnounceBaseOutputDim (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC eveDim : ℕ) : ℕ :=
  bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * eveDim

/-- The **symmetrized PE-announce transcript dimension at a general test-set size `m`**:
    `2 · (inner · n!)`.
-/
abbrev bb84SymPEAnnounceTranscriptDim (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) : ℕ :=
  2 * bb84SymPEAnnounceTranscriptInnerDim n m ℓ ℓEV peSel leakEC

/-- The **symmetrized PE-announce output with Eve retained** as a right tensor factor, at a
    general test-set size `m`.
-/
abbrev bb84EveVisiblePEAnnounceSymOutputDim (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC eveDim : ℕ) : ℕ :=
  (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) * eveDim

instance bb84PEAnnounceInnerTranscriptDim_neZero (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) :
    NeZero (bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC) :=
  ⟨Nat.mul_ne_zero
    (Nat.mul_ne_zero
      (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ two_ne_zero))
      (pow_ne_zero _ (by norm_num)))
    (pow_ne_zero _ (by norm_num [signalDim]))⟩

instance bb84PEAnnounceBaseOutputDim_neZero (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) :
    NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
    (Nat.mul_ne_zero (by norm_num)
      (NeZero.ne (bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC)))⟩

instance bb84EveVisiblePEAnnounceBaseOutputDim_neZero (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC eveDim : ℕ) [NeZero eveDim] :
    NeZero (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) := by
  unfold bb84EveVisiblePEAnnounceBaseOutputDim
  exact Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _) |> NeZero.mk

instance bb84SymPEAnnounceTranscriptDim_neZero (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) :
    NeZero (bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
  ⟨Nat.mul_ne_zero (by norm_num)
    (Nat.mul_ne_zero (NeZero.ne (bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC))
      (Nat.factorial_ne_zero n))⟩

instance bb84EveVisiblePEAnnounceSymOutputDim_neZero (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC eveDim : ℕ) [NeZero eveDim] :
    NeZero (bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC eveDim) := by
  unfold bb84EveVisiblePEAnnounceSymOutputDim
  exact Nat.mul_ne_zero
    (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (NeZero.ne _)) (NeZero.ne _) |> NeZero.mk

/-- The general-`m` base output tensored with the `n!` permutation register equals the general-`m`
    symmetrized output register (base↔symmetrized tensor factoring; consumed by the general-`m`
    announcement map's `Op.castDim`).
-/
lemma bb84PEAnnounceBaseOutputDim_tensor_eq (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) :
    bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * n.factorial =
      2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC := by
  simp only [bb84PEAnnounceBaseOutputDim, bb84PEAnnounceBaseTranscriptDim,
    bb84SymPEAnnounceTranscriptDim, bb84SymPEAnnounceTranscriptInnerDim, Nat.mul_assoc]

/-! ### Canonical-split bridges for the general-`m` dimensions

`bb84KeyRoundCount n ⌈n/2⌉` reduces to `bb84KeyRoundCountCanonical n`, so each closed dimension is
the `m = ⌈n/2⌉` instance of its general-`m` form, definitionally. -/

/-! ### General-`m` transcript indices, Kraus families and PA/abort maps -/

namespace bb84

/-- **pass transcript index at a general test-set size `m`** `(kA, kB, flag = 0, st, evTag, syn,
    pe)`: two distinct hashed-key copies `(kA, kB)`, accept flag `0`, the announced
    (privacy-amplification, error-verification) seed pair `st`, Alice's announced `ℓEV`-bit
    error-verification tag `evTag`, the `leakEC`-bit announced syndrome `syn`, and the announced
    PE-outcome block `pe` on the `n − bb84KeyRoundCount n m` test rounds.
-/
def pePassOutIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (kA kB : Fin (2 ^ ℓ)) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC))
    (p : Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :
    Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
  finProdFinEquiv
    (finProdFinEquiv (kA, kB),
      finProdFinEquiv ((⟨0, by norm_num⟩ : Fin 2),
        finProdFinEquiv
          (finProdFinEquiv
            (finProdFinEquiv (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel) st, evTag),
              syn), p)))

/-- **fail transcript index at a general test-set size `m`** `(0, 0, flag = 1, st, evTag, syn,
    pe)`: the two key slots zeroed and the accept flag set, with EVERY announcement retained — the
    seed pair `st`, the error-verification tag `evTag`, the syndrome `syn` and the PE-outcome block
    `pe` are all published before the accept decision, so the abort transcript carries them too.
-/
def peFailOutIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Fin (2 ^ ℓEV)) (syn : Fin (2 ^ leakEC))
    (p : Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :
    Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
  finProdFinEquiv
    (finProdFinEquiv
      ((⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ)),
       (⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ))),
      finProdFinEquiv ((⟨1, by norm_num⟩ : Fin 2),
        finProdFinEquiv
          (finProdFinEquiv
            (finProdFinEquiv (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel) st, evTag),
              syn), p)))

/-- **pass Kraus at a general test-set size `m`.** On an outcome `ω` and announced seed pair
    `st = (s, t)` passing the FULL accept gate `bb84SiftedLocalPEAndEVPassed` (PE test AND
    error-verification tag match), writes `(kA, kB, 0, st, evTag, syn, pe)` with
    `kA = hash_s(aliceKeyString ω)`, `kB = hash_s(decode(bobKeyString ω, syn))`,
    `syn = ec.syndrome(aliceKeyString ω)`, `evTag = verificationTag ℓEV t (aliceKeyString ω)` and
    `pe = (bb84PartEquiv peSel ω).2`, the outcomes of the `n − bb84KeyRoundCount n m`
    sorted test rounds (which is the paper's `m` whenever `m ≤ n`).
-/
def retainedSiftedPEAnnouncePassBranchKraus (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim) →
      Matrix (Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
        (Fin (4 ^ n * eveDim)) ℂ :=
  fun ⟨st, ω⟩ =>
    if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·)
          (Matrix.single
            (pePassOutIndex n m ℓ ℓEV peSel leakEC
              ((aliceKeyHashFamily n ℓ peSel).hash st.1 (aliceKeyString peSel ω))
              ((aliceKeyHashFamily n ℓ peSel).hash st.1
                (ec.decode (bobKeyString peSel ω)
                  (ec.syndrome (aliceKeyString peSel ω))))
              st (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
              (ec.syndrome (aliceKeyString peSel ω))
              (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2))
            (finFunctionFinEquiv ω) (1 : ℂ) :
              Matrix (Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)) (Fin (4 ^ n)) ℂ)
          (1 : Op eveDim))
    else 0

/-- **Fail Kraus at a general test-set size `m`** (literally shared by real and ideal). On an
    outcome `ω` and announced seed pair `st` FAILING the full accept gate, writes the abort
    transcript `(0, 0, 1, st, evTag, syn, pe)`: the two key slots are zeroed and every announcement
    — seed pair, error-verification tag, syndrome, PE block — is retained.  It is seed-indexed
    because it must read the error-verification half of `st` both to evaluate the gate and to write
    `evTag`.
-/
def retainedSiftedPEAnnounceFailBranchKraus (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim) →
      Matrix (Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
        (Fin (4 ^ n * eveDim)) ℂ :=
  fun ⟨st, ω⟩ =>
    if ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·)
          (Matrix.single
            (peFailOutIndex n m ℓ ℓEV peSel leakEC st
              (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
              (ec.syndrome (aliceKeyString peSel ω))
              (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2))
            (finFunctionFinEquiv ω) (1 : ℂ) :
              Matrix (Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)) (Fin (4 ^ n)) ℂ)
          (1 : Op eveDim))
    else 0

/-- **ideal pass Kraus at a general test-set size `m`.** On an outcome `ω`, seed pair `st` and
    fresh uniform key `k` passing the full accept gate, writes `(k, k, 0, st, evTag, syn, pe)` — ONE
    fresh uniform key in BOTH slots, the same `st/evTag/syn/pe` announcements as the real pass.
-/
def retainedSiftedPEAnnounceIdealPassKraus (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    (Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel →
      Matrix (Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
        (Fin (4 ^ n * eveDim)) ℂ :=
  fun ⟨ω, k, st⟩ =>
    if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·)
          (Matrix.single
            (pePassOutIndex n m ℓ ℓEV peSel leakEC k k st
              (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
              (ec.syndrome (aliceKeyString peSel ω))
              (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2))
            (finFunctionFinEquiv ω) (1 : ℂ) :
              Matrix (Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)) (Fin (4 ^ n)) ℂ)
          (1 : Op eveDim))
    else 0

/-- **real PA/abort map at a general test-set size `m`**: the uniform seed-pair average
    `1/|KeyHashSeedPairEV n ℓ ℓEV peSel|` on BOTH branches — the fail branch is seed-indexed, so it
    carries the same scale.  Per outcome `ω` the two branches partition the seed pairs,
    `∑_{st} (1/|ST|)·([accept st ω] + [¬accept st ω]) = 1`.
-/
def retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Op (4 ^ n * eveDim) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  (1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
    krausMapFintype
      (retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q) +
  (1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
    krausMapFintype
      (retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)

/-- **ideal PA/abort map at a general test-set size `m`**: fresh uniform key in both slots on the
    pass branch (scale `1/(2^ℓ·|KeyHashSeedPairEV|)`), and the literally-shared fail branch at the
    seed-pair scale `1/|KeyHashSeedPairEV|`.
-/
def retainedSiftedPEAnnounceIdealKeyAndAbortChannel (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    Op (4 ^ n * eveDim) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  (1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
    krausMapFintype
      (retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q) +
  (1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
    krausMapFintype
      (retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)

/-! #### CPTP machinery at a general test-set size `m`

Replay of the `m = ⌈n/2⌉` chain above.  For a single-entry Kraus operator the WHOLE output index
`(kA, kB, flag, st, evTag, syn, pe)` cancels in the adjoint product, so the announced PE block is a
*value* fed into the out-index and never read: the completeness argument does not depend on the
width of that register and therefore carries no constraint on `m`.  The seed-pair normalizers
(`keyHashSeedKrausScale`, `idealKeyHashSeedKrausScale`) and the seed-pair card collapse
(`keyHashSeedPair_outcomeProjector_card_collapse`) mention only the input register and are shared
with the `m = ⌈n/2⌉` chain rather than duplicated, as is the ideal-branch fresh-key average
`retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_pass_sum`, whose statement is already `m`-free.
-/

/-- Adjoint product of a general-`m` pass Kraus operator: the output index
    `(kA, kB, 0, st, evTag, syn, pe)` cancels, leaving the input-outcome projector on the branch
    where the full `PE ∧ EV` gate accepts.

    Public for the same reason as its `m = ⌈n/2⌉` instance
    `retainedSiftedPEAnnouncePassBranchKraus_adjoint_mul`, which it supersedes: the base-scheme
    pass-support estimate reads it to collapse the scaled `∑ KᴴK` of the pass branch onto the
    accept-gated outcome projector. -/
lemma retainedSiftedPEAnnouncePassBranchKraus_adjoint_mul
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel)
    (ω : Fin n → Fin signalDim) :
    (retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q (st, ω))ᴴ *
        retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q (st, ω) =
      if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv (finFunctionFinEquiv ω, r))
            (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)
      else 0 := by
  classical
  have hK :
      retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q (st, ω) =
        if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
          ∑ r : Fin eveDim,
            Matrix.single
              (finProdFinEquiv
                (pePassOutIndex n m ℓ ℓEV peSel leakEC
                  ((aliceKeyHashFamily n ℓ peSel).hash st.1 (aliceKeyString peSel ω))
                  ((aliceKeyHashFamily n ℓ peSel).hash st.1
                    (ec.decode (bobKeyString peSel ω)
                      (ec.syndrome (aliceKeyString peSel ω))))
                  st (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
                  (ec.syndrome (aliceKeyString peSel ω))
                  (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2), r))
              (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)
        else 0 := by
    ext a b
    by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
    · rw [if_pos h]
      simp [retainedSiftedPEAnnouncePassBranchKraus, h, Matrix.kroneckerMap,
        Matrix.single_apply, Matrix.one_apply, finProdFinEquiv_symm_apply,
        sum_single_finProdFinEquiv_apply]
    · rw [if_neg h]
      simp [retainedSiftedPEAnnouncePassBranchKraus, h]
  rw [hK]
  by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
  · rw [if_pos h]
    rw [matrix_single_sum_conjTranspose_mul_of_injective]
    · simp [h]
    · intro r r' hr
      have hmod := congrArg
        (fun x : Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) =>
          x.modNat)
        hr
      simpa [finProdFinEquiv_apply_modNat] using hmod
  · simp [h]

/-- Adjoint product of a general-`m` fail Kraus operator: the abort output index
    `(0, 0, 1, st, evTag, syn, pe)` cancels, leaving the input-outcome projector on the branch where
    the full `PE ∧ EV` gate rejects. -/
private lemma retainedSiftedPEAnnounceFailBranchKraus_adjoint_mul
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel)
    (ω : Fin n → Fin signalDim) :
    (retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q (st, ω))ᴴ *
        retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q (st, ω) =
      if ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv (finFunctionFinEquiv ω, r))
            (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)
      else 0 := by
  classical
  have hK :
      retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q (st, ω) =
        if ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
          ∑ r : Fin eveDim,
            Matrix.single
              (finProdFinEquiv
                (peFailOutIndex n m ℓ ℓEV peSel leakEC st
                  (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
                  (ec.syndrome (aliceKeyString peSel ω))
                  (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2), r))
              (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)
        else 0 := by
    ext a b
    by_cases h : ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω
    · rw [if_pos h]
      simp [retainedSiftedPEAnnounceFailBranchKraus, h, Matrix.kroneckerMap,
        Matrix.single_apply, Matrix.one_apply, finProdFinEquiv_symm_apply,
        sum_single_finProdFinEquiv_apply]
    · rw [if_neg h]
      simp [retainedSiftedPEAnnounceFailBranchKraus, h]
  rw [hK]
  by_cases h : ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω
  · rw [if_pos h]
    rw [matrix_single_sum_conjTranspose_mul_of_injective]
    · simp [h]
    · intro r r' hr
      have hmod := congrArg
        (fun x : Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) =>
          x.modNat)
        hr
      simpa [finProdFinEquiv_apply_modNat] using hmod
  · simp [h]

/-- Combined general-`m` real PA/abort Kraus family, indexed by the pass/fail partition.  BOTH
    branches are indexed by `(seed pair, outcome)` and carry the seed-uniform normalizer
    `keyHashSeedKrausScale n ℓ ℓEV peSel`, which is `m`-independent.  Its `krausMapFintype` is the
    general-`m` real PA/abort linear map. -/
private noncomputable def retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    (KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) ⊕
      (KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) →
      Matrix (Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
        (Fin (4 ^ n * eveDim)) ℂ :=
  fun idx =>
    match idx with
    | Sum.inl idx =>
        keyHashSeedKrausScale n ℓ ℓEV peSel •
          retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx
    | Sum.inr idx =>
        keyHashSeedKrausScale n ℓ ℓEV peSel •
          retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx

/-- The combined general-`m` Kraus family realizes the general-`m` real PA/abort linear map. -/
private lemma retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus_eq
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    krausMapFintype
        (retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
          leakEC ec δ Q) =
      retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel xSel
        leakEC ec δ Q := by
  ext M
  have hscale :
      (starRingEnd ℂ) (keyHashSeedKrausScale n ℓ ℓEV peSel) *
          keyHashSeedKrausScale n ℓ ℓEV peSel =
        (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ :=
    keyHashSeedKrausScale_star_mul n ℓ ℓEV peSel
  -- split the Kraus sum over the pass/fail partition; each term carries the scale `s̄ s = 1/|ST|`
  simp only [krausMapFintype, retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus,
    retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.add_apply, LinearMap.smul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, RCLike.star_def, hscale, one_div,
    Finset.smul_sum]

/-- Pass-branch adjoint product for the combined general-`m` Kraus family. -/
private lemma retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus_pass_adjoint_mul
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) :
    (retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
          leakEC ec δ Q (Sum.inl idx))ᴴ *
        retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
          leakEC ec δ Q (Sum.inl idx) =
      if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
            (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
            ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹)
      else 0 := by
  classical
  have hscale' :
      keyHashSeedKrausScale n ℓ ℓEV peSel *
          (starRingEnd ℂ) (keyHashSeedKrausScale n ℓ ℓEV peSel) =
        (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ := by
    rw [mul_comm]
    change star (keyHashSeedKrausScale n ℓ ℓEV peSel) * keyHashSeedKrausScale n ℓ ℓEV peSel = _
    simpa using keyHashSeedKrausScale_star_mul n ℓ ℓEV peSel
  by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 = true
  · simp only [retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [retainedSiftedPEAnnouncePassBranchKraus_adjoint_mul]
    simp [h, Finset.smul_sum, Matrix.smul_single, smul_eq_mul, hscale']
  · simp only [retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [retainedSiftedPEAnnouncePassBranchKraus_adjoint_mul]
    simp [h]

/-- Fail-branch adjoint product for the combined general-`m` Kraus family. -/
private lemma retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus_fail_adjoint_mul
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) :
    (retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
          leakEC ec δ Q (Sum.inr idx))ᴴ *
        retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
          leakEC ec δ Q (Sum.inr idx) =
      if ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
            (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
            ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹)
      else 0 := by
  classical
  have hscale' :
      keyHashSeedKrausScale n ℓ ℓEV peSel *
          (starRingEnd ℂ) (keyHashSeedKrausScale n ℓ ℓEV peSel) =
        (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ := by
    rw [mul_comm]
    change star (keyHashSeedKrausScale n ℓ ℓEV peSel) * keyHashSeedKrausScale n ℓ ℓEV peSel = _
    simpa using keyHashSeedKrausScale_star_mul n ℓ ℓEV peSel
  by_cases h : ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2
  · simp only [retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [retainedSiftedPEAnnounceFailBranchKraus_adjoint_mul]
    simp [h, Finset.smul_sum, Matrix.smul_single, smul_eq_mul, hscale']
  · simp only [retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [retainedSiftedPEAnnounceFailBranchKraus_adjoint_mul]
    simp [h]

/-- Kraus completeness `∑ Kᴴ K = 1` for the combined general-`m` real PA/abort family.  At each
    `(st, ω)` the accept and reject branches are exclusive and exhaustive, so their
    `1/|ST|`-weighted projectors recombine into one; the seed-pair sum then collapses the `1/|ST|`
    and the outcome/Eve sum resolves the identity (`keyHashSeedPair_outcomeProjector_card_collapse`,
    which is `m`-independent). -/
private lemma retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus_completeness
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    ∑ idx : (KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) ⊕
        (KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)),
      (retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
          leakEC ec δ Q idx)ᴴ *
        retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
          leakEC ec δ Q idx =
      (1 : Op (4 ^ n * eveDim)) := by
  classical
  rw [Fintype.sum_sum_type]
  calc
    (∑ a₁,
          (retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel
              xSel leakEC ec δ Q (Sum.inl a₁))ᴴ *
            retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel
              xSel leakEC ec δ Q (Sum.inl a₁)) +
        ∑ a₂,
          (retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel
              xSel leakEC ec δ Q (Sum.inr a₂))ᴴ *
            retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel
              xSel leakEC ec δ Q (Sum.inr a₂)
        =
          (∑ idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
            if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 then
              ∑ r : Fin eveDim,
                Matrix.single
                  (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
                  (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
                  ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹)
            else 0) +
          ∑ idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
            if ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 then
              ∑ r : Fin eveDim,
                Matrix.single
                  (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
                  (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
                  ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹)
            else 0 := by
          congr 1
          · exact Finset.sum_congr rfl fun idx _ =>
              retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus_pass_adjoint_mul
                n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx
          · exact Finset.sum_congr rfl fun idx _ =>
              retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus_fail_adjoint_mul
                n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx
    _ = ∑ idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
          ∑ r : Fin eveDim,
            Matrix.single
              (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
              (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
              ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun idx _ => ?_
          by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 <;>
            simp [h]
    _ = 1 := keyHashSeedPair_outcomeProjector_card_collapse n ℓ ℓEV eveDim peSel

/-- **The general-`m` real PA/abort map is CPTP.**  Each `Kᴴ K` collapses onto the input diagonal
    indexed by `ω` — the entire `(kA, kB, flag, st, evTag, syn, pe)` output index cancels, so the
    announced PE block, the EV tag and the syndrome are invisible to the completeness — and the
    accept/reject partition, taken per `(st, ω)`, sums to the identity after the seed-pair card
    collapse.  No constraint on `m`.
-/
theorem retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap_isCPTP
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    IsCPTP (⇑(retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel
      xSel leakEC ec δ Q)) := by
  rw [← retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus_eq]
  exact krausMapFintype_isCPTP
    (retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
      leakEC ec δ Q)
    (retainedSiftedPEAnnouncePrivacyAmplifyAndAbortBranchKraus_completeness n m ℓ ℓEV eveDim
      peSel xSel leakEC ec δ Q)

/-- Adjoint product of a general-`m` ideal pass Kraus operator: the output index
    `(k, k, 0, st, evTag, syn, pe)` cancels, leaving the input-outcome projector on the accepting
    branch.

    Public for the same reason as its `m = ⌈n/2⌉` instance
    `retainedSiftedPEAnnounceIdealPassKraus_adjoint_mul`, which it supersedes. -/
lemma retainedSiftedPEAnnounceIdealPassKraus_adjoint_mul
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (ω : Fin n → Fin signalDim)
    (k : Fin (2 ^ ℓ))
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) :
    (retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q (ω, k, st))ᴴ *
        retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q (ω, k, st)
            =
      if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv (finFunctionFinEquiv ω, r))
            (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)
      else 0 := by
  classical
  have hK :
      retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q (ω, k, st) =
        if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
          ∑ r : Fin eveDim,
            Matrix.single
              (finProdFinEquiv
                (pePassOutIndex n m ℓ ℓEV peSel leakEC k k st
                  (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
                  (ec.syndrome (aliceKeyString peSel ω))
                  (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2), r))
              (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)
        else 0 := by
    ext a b
    by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
    · rw [if_pos h]
      simp [retainedSiftedPEAnnounceIdealPassKraus, h, Matrix.kroneckerMap,
        Matrix.single_apply, Matrix.one_apply, finProdFinEquiv_symm_apply,
        sum_single_finProdFinEquiv_apply]
    · rw [if_neg h]
      simp [retainedSiftedPEAnnounceIdealPassKraus, h]
  rw [hK]
  by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
  · rw [if_pos h]
    rw [matrix_single_sum_conjTranspose_mul_of_injective]
    · simp [h]
    · intro r r' hr
      have hmod := congrArg
        (fun x : Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) =>
          x.modNat)
        hr
      simpa [finProdFinEquiv_apply_modNat] using hmod
  · simp [h]

/-- Combined general-`m` ideal PA/abort Kraus family, indexed by the pass/fail partition. -/
private noncomputable def retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    ((Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel) ⊕
      (KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) →
      Matrix (Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
        (Fin (4 ^ n * eveDim)) ℂ :=
  fun idx =>
    match idx with
    | Sum.inl idx =>
        idealKeyHashSeedKrausScale n ℓ ℓEV peSel •
          retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx
    | Sum.inr idx =>
        keyHashSeedKrausScale n ℓ ℓEV peSel •
          retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx

/-- The combined general-`m` ideal Kraus family realizes the general-`m` ideal PA/abort linear
    map. -/
private lemma retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_eq
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    krausMapFintype
        (retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
          leakEC ec δ Q) =
      retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q :=
          by
  ext M
  have hscale :
      (starRingEnd ℂ) (idealKeyHashSeedKrausScale n ℓ ℓEV peSel) *
          idealKeyHashSeedKrausScale n ℓ ℓEV peSel =
        ((2 ^ ℓ : ℂ) * (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ))⁻¹ :=
    idealKeyHashSeedKrausScale_star_mul n ℓ ℓEV peSel
  have hscaleFail :
      (starRingEnd ℂ) (keyHashSeedKrausScale n ℓ ℓEV peSel) *
          keyHashSeedKrausScale n ℓ ℓEV peSel =
        (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ :=
    keyHashSeedKrausScale_star_mul n ℓ ℓEV peSel
  -- split the Kraus sum over the pass/fail partition; the pass terms carry `1/(2^ℓ |ST|)` and the
  -- fail terms `1/|ST|`
  simp only [krausMapFintype, retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus,
    retainedSiftedPEAnnounceIdealKeyAndAbortChannel, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.add_apply, LinearMap.smul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, RCLike.star_def, hscale, hscaleFail, one_div,
    Finset.smul_sum]

/-- Pass-branch adjoint product for the combined general-`m` ideal Kraus family. -/
private lemma retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_pass_adjoint_mul
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (idx : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel) :
    (retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC
          ec δ Q (Sum.inl idx))ᴴ *
        retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC
          ec δ Q (Sum.inl idx) =
      if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.2.2.2 idx.1 then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv (finFunctionFinEquiv idx.1, r))
            (finProdFinEquiv (finFunctionFinEquiv idx.1, r))
            (((2 ^ ℓ : ℂ) * (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ))⁻¹)
      else 0 := by
  classical
  have hscale' :
      idealKeyHashSeedKrausScale n ℓ ℓEV peSel *
          (starRingEnd ℂ) (idealKeyHashSeedKrausScale n ℓ ℓEV peSel) =
        ((2 ^ ℓ : ℂ) * (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ))⁻¹ := by
    change idealKeyHashSeedKrausScale n ℓ ℓEV peSel *
      star (idealKeyHashSeedKrausScale n ℓ ℓEV peSel) = _
    rw [idealKeyHashSeedKrausScale_mul_star]
    simp [one_div]
  by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.2.2.2 idx.1 = true
  · simp only [retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [retainedSiftedPEAnnounceIdealPassKraus_adjoint_mul]
    simp [h, Finset.smul_sum, Matrix.smul_single, smul_eq_mul, hscale']
  · simp only [retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [retainedSiftedPEAnnounceIdealPassKraus_adjoint_mul]
    simp [h]

/-- Fail-branch adjoint product for the combined general-`m` ideal Kraus family (the shared fail
    Kraus at the seed-pair normalizer). -/
private lemma retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_fail_adjoint_mul
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) :
    (retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC
          ec δ Q (Sum.inr idx))ᴴ *
        retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC
          ec δ Q (Sum.inr idx) =
      if ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 then
        ∑ r : Fin eveDim,
          Matrix.single
            (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
            (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
            ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹)
      else 0 := by
  classical
  have hscale' :
      keyHashSeedKrausScale n ℓ ℓEV peSel *
          (starRingEnd ℂ) (keyHashSeedKrausScale n ℓ ℓEV peSel) =
        (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹ := by
    rw [mul_comm]
    change star (keyHashSeedKrausScale n ℓ ℓEV peSel) * keyHashSeedKrausScale n ℓ ℓEV peSel = _
    simpa using keyHashSeedKrausScale_star_mul n ℓ ℓEV peSel
  by_cases h : ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2
  · simp only [retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [retainedSiftedPEAnnounceFailBranchKraus_adjoint_mul]
    simp [h, Finset.smul_sum, Matrix.smul_single, smul_eq_mul, hscale']
  · simp only [retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [retainedSiftedPEAnnounceFailBranchKraus_adjoint_mul]
    simp [h]

/-- Kraus completeness `∑ Kᴴ K = 1` for the combined general-`m` ideal PA/abort family. -/
private lemma retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_completeness
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    ∑ idx : ((Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel) ⊕
        (KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)),
      (retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC
          ec δ Q idx)ᴴ *
        retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC
          ec δ Q idx =
      (1 : Op (4 ^ n * eveDim)) := by
  classical
  rw [Fintype.sum_sum_type]
  calc
    (∑ a₁,
          (retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
              leakEC ec δ Q (Sum.inl a₁))ᴴ *
            retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
              leakEC ec δ Q (Sum.inl a₁)) +
        ∑ a₂,
          (retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
              leakEC ec δ Q (Sum.inr a₂))ᴴ *
            retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel
              leakEC ec δ Q (Sum.inr a₂)
        =
          (∑ idx : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel,
            if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.2.2.2 idx.1 then
              ∑ r : Fin eveDim,
                Matrix.single
                  (finProdFinEquiv (finFunctionFinEquiv idx.1, r))
                  (finProdFinEquiv (finFunctionFinEquiv idx.1, r))
                  (((2 ^ ℓ : ℂ) * (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ))⁻¹)
            else 0) +
          ∑ idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
            if ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 then
              ∑ r : Fin eveDim,
                Matrix.single
                  (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
                  (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
                  ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹)
            else 0 := by
          congr 1
          · exact Finset.sum_congr rfl fun idx _ =>
              retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_pass_adjoint_mul
                n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx
          · exact Finset.sum_congr rfl fun idx _ =>
              retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_fail_adjoint_mul
                n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx
    _ =
          (∑ idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
            if bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 then
              ∑ r : Fin eveDim,
                Matrix.single
                  (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
                  (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
                  ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹)
            else 0) +
          ∑ idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
            if ¬ bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 then
              ∑ r : Fin eveDim,
                Matrix.single
                  (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
                  (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
                  ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹)
            else 0 := by
          rw [retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_pass_sum]
    _ = ∑ idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim),
          ∑ r : Fin eveDim,
            Matrix.single
              (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
              (finProdFinEquiv (finFunctionFinEquiv idx.2, r))
              ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)⁻¹) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun idx _ => ?_
          by_cases h : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q idx.1.2 idx.2 <;>
            simp [h]
    _ = 1 := keyHashSeedPair_outcomeProjector_card_collapse n ℓ ℓEV eveDim peSel

/-- **The general-`m` ideal PA/abort map is CPTP.**  As with the real map, the completeness
    `∑ Kᴴ K = 1` is output-index-independent: the entire `(k, k, flag, st, evTag, syn, pe)` output
    index cancels, the fresh-key average cancels the ideal branch's extra `2^ℓ`, and the
    accept/reject partition per `(st, ω)` sums to the identity after the seed-pair card collapse.
    No constraint on `m`.
-/
theorem retainedSiftedPEAnnounceIdealKeyAndAbortChannel_isCPTP
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    IsCPTP (⇑(retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel
      leakEC ec δ Q)) := by
  rw [← retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_eq]
  exact krausMapFintype_isCPTP
    (retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC
      ec δ Q)
    (retainedSiftedPEAnnounceIdealKeyAndAbortBranchKraus_completeness n m ℓ ℓEV eveDim peSel
      xSel leakEC ec δ Q)

end bb84

/-! ### The general-`m` protocol scheme, announcement map and symmetrized channels -/

/-- **The genuine-LOCC PE-announce protocol scheme at a general test-set size `m`.**
    Alice-hash/Bob-decode key, announced syndrome (`2^leakEC` factor), announced
    error-verification tag (`2^ℓEV` factor), announced PE block on the `n − bb84KeyRoundCount n m`
    test rounds, and the full accept gate `bb84SiftedLocalPEAndEVPassed` — the fail-closed local PE
    test AND the error-verification tag match, threading `xSel`.  Transcript
    `2 · bb84PEAnnounceInnerTranscriptDim`.

    `BB84EveVisibleProtocolScheme` carries `transcriptDim` as a field, so widening the announced PE
    register is a re-instantiation of the same interface.

    Reference: Nahar et al. 2024 (arXiv:2403.11851, `main.tex:909`, `:913`). -/
noncomputable def bb84SiftedPEAnnounceEveVisibleProtocol (n m ℓ ℓEV : ℕ) [NeZero n]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    BB84EveVisibleProtocolScheme n ℓ where
  transcriptDim := 2 * bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC
  transcriptInnerDim := bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC
  transcriptDim_factored := rfl
  transcriptInnerDim_neZero := bb84PEAnnounceInnerTranscriptDim_neZero n m ℓ ℓEV peSel leakEC
  realProtocolMap := fun {eveDim} [NeZero eveDim] =>
    (bb84.retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel xSel
      leakEC ec δ Q).comp (measurementChannel n eveDim)
  idealProtocolMap := fun {eveDim} [NeZero eveDim] =>
    (bb84.retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel
      leakEC ec δ Q).comp (measurementChannel n eveDim)

/-- Append the public permutation announcement to the general-`m` base output. -/
noncomputable def bb84SiftedPEAnnounceLinear (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (perm : Equiv.Perm (Fin n)) :
    Op (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) →ₗ[ℂ]
      Op (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) where
  toFun A :=
    Op.castDim (bb84PEAnnounceBaseOutputDim_tensor_eq n m ℓ ℓEV peSel leakEC)
      (Op.tensor A (permAnnounceProjector n perm))
  map_add' a b := by simp only [Op.tensor_add_left, Op.castDim_add]
  map_smul' c a := by simp only [RingHom.id_apply, Op.tensor_smul_left, Op.castDim_smul]

/-- Eve-visible general-`m` announcement map. -/
noncomputable def bb84SiftedPEAnnounceLinearEveVisible (n m ℓ ℓEV eveDim : ℕ) [NeZero n]
    [NeZero eveDim] (peSel : Fin n → Bool) (leakEC : ℕ) (perm : Equiv.Perm (Fin n)) :
    Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  haveI : NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
    bb84PEAnnounceBaseOutputDim_neZero n m ℓ ℓEV peSel leakEC
  haveI : NeZero (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (NeZero.ne _)⟩
  mapTensorIdLinear (bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC perm)

/-- **General-`m` symmetrized direct real channel**: the `(1/n!)`-normalized permutation average of
    the general-`m` real protocol map post-composed with the general-`m` announcement, at fixed
    PE selector.  The sifted conjugation/attack channels `bb84SiftedConjChannel` and
    `bb84SiftedConjAfterPre` act on `Op (4^n * eveDim)` and carry no split point, so they are
    shared with the `m = ⌈n/2⌉` channel rather than duplicated.
-/
noncomputable def bb84SymSiftedRealChannelDirect_withPEAnnounce (n m ℓ ℓEV : ℕ) [NeZero n]
    [NeZero (4 ^ n)] (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  (1 / (n.factorial : ℂ)) •
    ∑ π : Equiv.Perm (Fin n),
      (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π).comp
        (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
            δ).realProtocolMap
            (eveDim := eveDim)).comp
          ((bb84SiftedConjAfterPre eveDim pre peSel xSel).comp (permuteSignalLinear n π)))

/-- **General-`m` symmetrized direct ideal channel**, using the general-`m` ideal protocol map.
-/
noncomputable def bb84SymSiftedIdealChannelDirect_withPEAnnounce (n m ℓ ℓEV : ℕ) [NeZero n]
    [NeZero (4 ^ n)] (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  (1 / (n.factorial : ℂ)) •
    ∑ π : Equiv.Perm (Fin n),
      (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π).comp
        (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
            δ).idealProtocolMap
            (eveDim := eveDim)).comp
          ((bb84SiftedConjAfterPre eveDim pre peSel xSel).comp (permuteSignalLinear n π)))

/-! #### General-`m` announcement-correction covariance substrate

Replay of the `m = ⌈n/2⌉` correction chain at the general-`m` base.  The announced PE register sits
inside `bb84PEAnnounceBaseOutputDim`, strictly left of the `n!` announce register, so the
correction is the identity on the `base ⊗ PE` block and relabels only the `n!` announce slot; the
substrate `announce_linear_sum_right_mul_eq_correction_map` quantifies over an arbitrary
`F : Perm (Fin n) → Op (bb84PEAnnounceBaseOutputDim …)` with no positivity, CPTP or gate
structure, so the width of the PE register is a spectator and no constraint on `m` arises. -/

/-- **General-`m` PE-announce correction unitary.** Relabels only the public
    permutation-announcement slot. -/
private noncomputable def symPermAnnounceCorrectionUnitary (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n)) :
    Op (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
  Op.castDim (bb84PEAnnounceBaseOutputDim_tensor_eq n m ℓ ℓEV peSel leakEC)
    (Op.tensor (1 : Op (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC))
      (permAnnounceRightMulUnitary n π))

/-- **General-`m` PE-announce correction CPTP map.** Conjugation by
    `symPermAnnounceCorrectionUnitary`. -/
private noncomputable def symPermAnnounceCorrectionMap (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n)) :
    Op (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) →ₗ[ℂ]
      Op (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) where
  toFun M :=
    symPermAnnounceCorrectionUnitary n m ℓ ℓEV peSel leakEC π * M *
      (symPermAnnounceCorrectionUnitary n m ℓ ℓEV peSel leakEC π)ᴴ
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

/-- The general-`m` PE-announce correction map is CPTP (conjugation by a unitary). -/
private theorem symPermAnnounceCorrectionMap_isCPTP (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (π : Equiv.Perm (Fin n)) :
    IsCPTP (⇑(symPermAnnounceCorrectionMap n m ℓ ℓEV peSel leakEC π)) := by
  unfold symPermAnnounceCorrectionMap
  apply isCPTP_unitary_conjugation
  unfold symPermAnnounceCorrectionUnitary
  rw [Op.castDim_conjTranspose, Op.castDim_mul]
  rw [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul, Matrix.one_mul]
  have hperm :
      (permAnnounceRightMulUnitary n π)ᴴ * permAnnounceRightMulUnitary n π =
        (1 : Op n.factorial) := by
    unfold permAnnounceRightMulUnitary
    exact Equiv.Perm.permMatrix_conjTranspose_mul_self _
  rw [hperm, Op.tensor_one, Op.castDim_one]

/-- The general-`m` correction map relabels a general-`m` enlarged announcement:
    `K_π ∘ bb84SiftedPEAnnounceLinear perm = bb84SiftedPEAnnounceLinear (perm * π)`. -/
private lemma symPermAnnounceCorrectionMap_bb84SiftedPEAnnounceLinear (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC : ℕ) (π perm : Equiv.Perm (Fin n))
    (A : Op (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)) :
    symPermAnnounceCorrectionMap n m ℓ ℓEV peSel leakEC π
        (bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC perm A) =
      bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC (perm * π) A := by
  unfold symPermAnnounceCorrectionMap symPermAnnounceCorrectionUnitary
    bb84SiftedPEAnnounceLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Op.castDim_conjTranspose]
  rw [Op.castDim_mul, Op.castDim_mul]
  rw [Op.tensor_conjTranspose, conjTranspose_one]
  rw [Op.tensor_mul, Matrix.one_mul, Op.tensor_mul, Matrix.mul_one]
  rw [permAnnounceRightMulUnitary_projector]

/-- **The general-`m` crux at the enlarged base.** Right multiplication inside an announced
    permutation average is implemented by the general-`m` correction map. -/
private lemma announce_linear_sum_right_mul_eq_correction_map (n m ℓ ℓEV : ℕ) [NeZero n]
    (peSel : Fin n → Bool) (leakEC : ℕ)
    (F : Equiv.Perm (Fin n) → Op (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC))
    (σ : Equiv.Perm (Fin n)) :
    (∑ π : Equiv.Perm (Fin n), bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π (F (π * σ))) =
      symPermAnnounceCorrectionMap n m ℓ ℓEV peSel leakEC σ.symm
        (∑ π : Equiv.Perm (Fin n), bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π (F π)) := by
  calc
    (∑ π : Equiv.Perm (Fin n), bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π (F (π * σ))) =
        ∑ π : Equiv.Perm (Fin n),
          bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC (π * σ.symm) (F π) := by
      let e := permAnnounceRightMulEquiv n σ
      let G : Equiv.Perm (Fin n) →
          Op (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
        fun γ => bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC (γ * σ.symm) (F γ)
      calc
        ∑ π : Equiv.Perm (Fin n), bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π (F (π * σ)) =
            ∑ π : Equiv.Perm (Fin n), G (e π) := by
          apply Finset.sum_congr rfl
          intro π _h
          simp only [G, e, permAnnounceRightMulEquiv, Equiv.coe_fn_mk]
          congr 1
          congr 1
          rw [← Equiv.Perm.inv_def σ, mul_inv_cancel_right]
        _ = ∑ π : Equiv.Perm (Fin n), G π := Equiv.sum_comp e G
        _ =
            ∑ π : Equiv.Perm (Fin n),
              bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC (π * σ.symm) (F π) := rfl
    _ =
      symPermAnnounceCorrectionMap n m ℓ ℓEV peSel leakEC σ.symm
        (∑ π : Equiv.Perm (Fin n), bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π (F π)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro π _h
      rw [symPermAnnounceCorrectionMap_bb84SiftedPEAnnounceLinear]

/-- **General-`m` PE-announce correction CPTP map, Eve-visible lift.** -/
private noncomputable def symPermAnnounceCorrectionMapEveVisible (n m ℓ ℓEV eveDim : ℕ)
    [NeZero eveDim] (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n)) :
    Op (bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC eveDim) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  haveI : NeZero (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (NeZero.ne _)⟩
  mapTensorIdLinear (symPermAnnounceCorrectionMap n m ℓ ℓEV peSel leakEC π)

/-- The Eve-visible general-`m` correction map is CPTP. -/
private theorem symPermAnnounceCorrectionMapEveVisible_isCPTP (n m ℓ ℓEV eveDim : ℕ)
    [NeZero eveDim] (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n)) :
    IsCPTP (⇑(symPermAnnounceCorrectionMapEveVisible n m ℓ ℓEV eveDim peSel leakEC π)) := by
  haveI : NeZero (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (NeZero.ne _)⟩
  simpa [symPermAnnounceCorrectionMapEveVisible, mapTensorIdLinear] using
    (mapTensorId_isCPTP (symPermAnnounceCorrectionMap n m ℓ ℓEV peSel leakEC π)
      (symPermAnnounceCorrectionMap_isCPTP n m ℓ ℓEV peSel leakEC π))

/-- **The Eve-visible general-`m` crux lift.** -/
private theorem announceLinearEveVisible_sum_right_mul_eq_correction_map (n m ℓ ℓEV eveDim : ℕ)
    [NeZero n] [NeZero eveDim] (peSel : Fin n → Bool) (leakEC : ℕ)
    (F : Equiv.Perm (Fin n) →
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
    (σ : Equiv.Perm (Fin n)) :
    (∑ π : Equiv.Perm (Fin n),
        bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π (F (π * σ))) =
      symPermAnnounceCorrectionMapEveVisible n m ℓ ℓEV eveDim peSel leakEC σ.symm
        (∑ π : Equiv.Perm (Fin n),
          bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π (F π)) := by
  classical
  haveI : NeZero (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (NeZero.ne _)⟩
  ext p q
  let G : Equiv.Perm (Fin n) → Op (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
    fun π => Matrix.of fun i j =>
      F π (finProdFinEquiv (i, (finProdFinEquiv.symm p).2))
        (finProdFinEquiv (j, (finProdFinEquiv.symm q).2))
  have hred :=
    congr_fun₂ (announce_linear_sum_right_mul_eq_correction_map n m ℓ ℓEV peSel leakEC G σ)
      (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1
  rw [map_sum] at hred
  simpa [G, bb84SiftedPEAnnounceLinearEveVisible,
    symPermAnnounceCorrectionMapEveVisible,
    mapTensorIdLinear, map_sum, Matrix.sum_apply, mapTensorId_apply_eq_apply_block,
    mapTensorId_comp, LinearMap.comp_apply] using hred

/-- **The general-`m` equivariance engine.** The retained-Eve general-`m` announced average of
    pre-attack signal permutations is equivariant under input conjugation by a round permutation,
    the announce relabel absorbed by the CPTP correction `symPermAnnounceCorrectionMapEveVisible`.
    The engine treats the protocol map as an opaque `base`, so the announced PE register's width
    never enters. -/
private theorem bb84SymAverage_permuteSignal_eveVisible_equivariant_withPEAnnounce
    (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (peSel : Fin n → Bool) (leakEC : ℕ)
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (base : Op (4 ^ n * eveDim) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
    (σ : Equiv.Perm (Fin n)) (ρ : Op (4 ^ n)) :
    ∑ π : Equiv.Perm (Fin n),
        bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π
          (base (pre (permuteSignalLinear n π
            (permutationRepresentation 4 n σ * ρ *
              (permutationRepresentation 4 n σ)ᴴ)))) =
      (symPermAnnounceCorrectionMapEveVisible n m ℓ ℓEV eveDim peSel leakEC σ.symm)
        (∑ π : Equiv.Perm (Fin n),
          bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π
            (base (pre (permuteSignalLinear n π ρ)))) := by
  let F : Equiv.Perm (Fin n) →
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
    fun π => base (pre (permuteSignalLinear n π ρ))
  calc
    (∑ π : Equiv.Perm (Fin n),
        bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π
          (base (pre (permuteSignalLinear n π
            (permutationRepresentation 4 n σ * ρ *
              (permutationRepresentation 4 n σ)ᴴ))))) =
        ∑ π : Equiv.Perm (Fin n),
          bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π
            (F (π * σ)) := by
      apply Finset.sum_congr rfl
      intro π _h
      rw [permuteSignal_after_sigma]
    _ =
        symPermAnnounceCorrectionMapEveVisible n m ℓ ℓEV eveDim peSel leakEC σ.symm
          (∑ π : Equiv.Perm (Fin n),
            bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π
              (base (pre (permuteSignalLinear n π ρ)))) := by
      exact announceLinearEveVisible_sum_right_mul_eq_correction_map
        n m ℓ ℓEV eveDim peSel leakEC F σ

/-! #### The bare (attack-free) general-`m` channels

The general-`m` twins of `bb84SymRealChannel` / `bb84SymIdealChannel`: the protocol as the physical
model states it, with **no attack parameter anywhere**, not even in the type — the retained-Eve slot
is the literal `1` and the pre-channel is the unit-register embedding.  These are the two bare
channels the CKR postselection reduction `ckr_security_reduction_exact` consumes; that reduction is
channel-agnostic and reads no split point, so the general-`m` forms carry the same **no** constraint
relating `m` to `n` as the rest of this section. -/

/-- **The bare (attack-free) general-`m` symmetrized real channel** — permute, embed the
    (one-dimensional) side register, sift-conjugate, measure, postprocess, announce, at a general
    test-set size `m`, with no attack parameter anywhere: the retained-Eve slot is the literal `1`.

    Definitionally equal to the slot-carrying `bb84SymSiftedRealChannelDirect_withPEAnnounce` at
    `1`/`bb84UnitRegisterEmbed n` — see `bb84SymRealChannel_eq_direct_unitRegisterEmbed`, the
    bridge every slot-carrying fact is rewritten through.

    Reference: Nahar, Tupkary, Zhao, Lütkenhaus and Tan 2024
    (arXiv:2403.11851, `main.tex:909`, `:913`). -/
noncomputable def bb84SymRealChannel (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC 1) :=
  (1 / (n.factorial : ℂ)) •
    ∑ π : Equiv.Perm (Fin n),
      (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC π).comp
        (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
              δ).realProtocolMap (eveDim := 1)).comp
          (((bb84SiftedConjChannel n 1 peSel xSel).comp (bb84UnitRegisterEmbed n)).comp
            (permuteSignalLinear n π)))

/-- **The bare (attack-free) general-`m` symmetrized ideal channel** — `bb84SymRealChannel`'s
    twin with key replacement on accept; see that def's docstring for the attack-free reading and
    for the bridge lemma (`bb84SymIdealChannel_eq_direct_unitRegisterEmbed`) that transports
    slot-carrying facts. -/
noncomputable def bb84SymIdealChannel (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceSymOutputDim n m ℓ ℓEV peSel leakEC 1) :=
  (1 / (n.factorial : ℂ)) •
    ∑ π : Equiv.Perm (Fin n),
      (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV 1 peSel leakEC π).comp
        (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
              δ).idealProtocolMap (eveDim := 1)).comp
          (((bb84SiftedConjChannel n 1 peSel xSel).comp (bb84UnitRegisterEmbed n)).comp
            (permuteSignalLinear n π)))

/-- **The general-`m` real bridge**: the bare general-`m` channel IS the slot-carrying general-`m`
    channel at the unit register slot `eveDim := 1`, `pre := bb84UnitRegisterEmbed n`, by `rfl`
    (`bb84SiftedConjAfterPre 1 (bb84UnitRegisterEmbed n)` unfolds to the composite written in
    `bb84SymRealChannel`).  Every fact proved about
    `bb84SymSiftedRealChannelDirect_withPEAnnounce … 1 (bb84UnitRegisterEmbed n) …` is
    transported to `bb84SymRealChannel` by rewriting through this lemma instead of unfolding the
    bare definition.  Both sides carry the literal `1` in the retained-Eve slot, so no dimension
    normalisation is needed under a dimension-indexed head (`trace`, `traceNorm`, `mapTensorId`,
    `Op.castDim`). -/
theorem bb84SymRealChannel_eq_direct_unitRegisterEmbed (n m ℓ ℓEV : ℕ) [NeZero n]
    [NeZero (4 ^ n)] (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec =
      bb84SymSiftedRealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec
        1 (bb84UnitRegisterEmbed n) := rfl

/-- **The general-`m` ideal bridge** — the twin of
    `bb84SymRealChannel_eq_direct_unitRegisterEmbed`; see that lemma's docstring for how it is
    used. -/
theorem bb84SymIdealChannel_eq_direct_unitRegisterEmbed (n m ℓ ℓEV : ℕ) [NeZero n]
    [NeZero (4 ^ n)] (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec =
      bb84SymSiftedIdealChannelDirect_withPEAnnounce n m ℓ ℓEV Q δ peSel xSel leakEC ec
        1 (bb84UnitRegisterEmbed n) := rfl

/-- **The bare general-`m` real/ideal difference is permutation covariant** — the attack-free
    supplier at a general test-set size `m`, and the first of the two bare-channel inputs
    `ckr_security_reduction_exact` requires.

    Stated at the unit register slot `eveDim := 1`, `pre := bb84UnitRegisterEmbed n` written as the
    literal `1`, so the output-dimension `NeZero` resolves by plain instance search with no side
    hypothesis.  The proof runs the general-`m` equivariance engine
    `bb84SymAverage_permuteSignal_eveVisible_equivariant_withPEAnnounce` on the bare
    pre-announcement map `realProtocolMap ∘ bb84SiftedConjChannel` after
    `pre := bb84UnitRegisterEmbed n`.

    The covariance is structural, exactly as for the slot-carrying twin: the PE selector is fixed
    and the symmetrization acts only through `permuteSignalLinear`, the announce relabel being
    absorbed by the CPTP correction `symPermAnnounceCorrectionMapEveVisible`, with the announced PE
    register — like the `2^leakEC` syndrome and `2^ℓEV` EV-tag factors — a spectator inside the
    base, left of the `n!` announce register.  Its width, and hence `m`, never enters.
-/
theorem bb84SymChannels_permCov (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (Q δ : ℝ) (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) :
    PermutationCovariant
      (bb84SymRealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec -
        bb84SymIdealChannel n m ℓ ℓEV Q δ peSel xSel leakEC ec) := by
  refine ⟨?_⟩
  intro σ
  refine ⟨⇑(symPermAnnounceCorrectionMapEveVisible n m ℓ ℓEV 1 peSel leakEC σ.symm), ?_, ?_⟩
  · exact symPermAnnounceCorrectionMapEveVisible_isCPTP n m ℓ ℓEV 1 peSel leakEC σ.symm
  · intro ρ
    have hR := bb84SymAverage_permuteSignal_eveVisible_equivariant_withPEAnnounce n m ℓ ℓEV
      peSel leakEC 1 (bb84UnitRegisterEmbed n)
      (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
            δ).realProtocolMap (eveDim := 1)).comp (bb84SiftedConjChannel n 1 peSel xSel)) σ ρ
    have hI := bb84SymAverage_permuteSignal_eveVisible_equivariant_withPEAnnounce n m ℓ ℓEV
      peSel leakEC 1 (bb84UnitRegisterEmbed n)
      (((bb84SiftedPEAnnounceEveVisibleProtocol n m ℓ ℓEV peSel xSel leakEC ec Q
            δ).idealProtocolMap (eveDim := 1)).comp (bb84SiftedConjChannel n 1 peSel xSel)) σ ρ
    unfold bb84SymRealChannel bb84SymIdealChannel
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.comp_apply]
    rw [map_sub, map_smul, map_smul]
    exact
      congrArg₂
        (fun x y => (1 / (n.factorial : ℂ)) • x - (1 / (n.factorial : ℂ)) • y)
        hR hI

/-- An announced permutation average of any fixed base map is permutation covariant. -/
theorem bb84SymAnnouncedMap_permCov
    (n m ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (peSel : Fin n → Bool) (leakEC eveDim : ℕ)
    [NeZero eveDim]
    (base : Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim)) :
    PermutationCovariant
      ((1 / (n.factorial : ℂ)) •
        ∑ π : Equiv.Perm (Fin n),
          (bb84SiftedPEAnnounceLinearEveVisible
            n m ℓ ℓEV eveDim peSel leakEC π).comp
            (base.comp (permuteSignalLinear n π))) := by
  refine ⟨fun σ => ⟨⇑(symPermAnnounceCorrectionMapEveVisible
    n m ℓ ℓEV eveDim peSel leakEC σ.symm),
    symPermAnnounceCorrectionMapEveVisible_isCPTP
      n m ℓ ℓEV eveDim peSel leakEC σ.symm, ?_⟩⟩
  intro ρ
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul]
  congr 1
  simp_rw [permuteSignal_after_sigma]
  exact announceLinearEveVisible_sum_right_mul_eq_correction_map
    n m ℓ ℓEV eveDim peSel leakEC (fun π => base (permuteSignalLinear n π ρ)) σ

end QKD.BB84.Model

end -- noncomputable section
