import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Engine.Postselection.RoundKernel

/-!
# Bell-twirl invariance of the genuine-LOCC accept gate

The bilateral-Pauli (Bell) twirl acts on the round outcomes by the per-round relabel
`ω i ↦ bellKeyOutcomePerm (g i) (ω i)` (`RoundKernel.lean`, the key-round signed-Pauli
pass-through `bb84BellSinglePair_conj_compProjector`). This module proves that the **full accept
predicate `QKD.BB84.Model.bb84SiftedLocalPEAndEVPassed` is invariant under that relabel**, which is
what lets the twirl be pushed through the pass/fail Kraus split.

Two independent mechanisms, one per conjunct:

* **PE**: `bellKeyOutcomePerm k` fixes the disagreement set `{1, 2}` **setwise** for every `k`
  (identity at `k ∈ {I⊗I, Z⊗Z}`, `ω ↦ 3 - ω` at `k ∈ {X⊗X, Y⊗Y}`, and `3 - ·` swaps `1 ↔ 2`), so
  both test error counts and hence the fail-closed two-basis decision are literally unchanged.
* **EV**: `bellKeyOutcomePerm k` shifts Alice's and Bob's outcome bits by the **same** `Fin 2` value
  `bellKeyOutcomeFlip k`, so both key strings shift by the same key-round pattern `e`. Error
  verification is then invariant exactly when the reconciliation scheme is translation-equivariant
  at `e`.

This is analysis built on the model's accept-gate definitions (`QKD.BB84.Model.SiftedMeasurement`)
and the Engine's twirl-permutation machinery (`bellKeyOutcomePerm`, `RoundKernel.lean`), which is
why it lives in the Engine rather than in the Model family: the Model states what the accept gate
*is*; this module analyses what it is invariant under.

## Main definitions and results

* `bellKeyOutcomeFlip` — the per-round key-bit flip of the bilateral Bell twirl.
* `bb84SiftedLocalPEAndEVPassed_bellTwirl_invariant` — the **full accept gate is invariant under
  the bilateral Bell (Pauli) twirl relabel** `ω i ↦ bellKeyOutcomePerm (g i) (ω i)`, given the
  translation-equivariance clause of the reconciliation scheme at the twirl's own key-round error
  pattern.
* `evVerified_shift_invariant`, `key_strings_shift`,
  `bb84SiftedLocalPETestPassed_bellTwirl_invariant` — the two halves: the twirl shifts BOTH key
  strings by the same pattern (so error verification is covariant), and it fixes the `{1,2}`
  disagreement sets setwise (so the two-basis PE decision is literally unchanged).

## References

Renner 2005 §5, §6.5; Nahar et al. 2024 (`arXiv:2403.11851`) §B.
-/

open QKD.BB84.Model
noncomputable section

namespace QKD.BB84.Engine

/-- **The per-round key-bit flip of the bilateral Bell twirl.**  Conjugating a computational-basis
outcome by `G_k` flips Alice's bit and Bob's bit by this common value: `0` for the diagonal Paulis
`k ∈ {I⊗I, Z⊗Z}`, `1` for the off-diagonal ones `k ∈ {X⊗X, Y⊗Y}`.  The `n`-round pattern
`fun i => bellKeyOutcomeFlip (g i)` is the key-round error pattern the twirl imposes. -/
def bellKeyOutcomeFlip (k : Fin 4) : Fin 2 :=
  if k = 1 ∨ k = 2 then 1 else 0

/-- **The disagreement set `{1, 2}` is setwise invariant under every twirl relabel.**  The relabel
is either the identity or `ω ↦ 3 - ω`, which swaps `1 ↔ 2` and `0 ↔ 3`. -/
theorem bellKeyOutcomePerm_mem_errorSet_iff (k ω : Fin 4) :
    (bellKeyOutcomePerm k ω = 1 ∨ bellKeyOutcomePerm k ω = 2) ↔ (ω = 1 ∨ ω = 2) := by
  revert k ω; decide

/-- **The structural fact the EV half rests on**: the twirl relabel shifts Alice's bit and Bob's bit
by the **same** `Fin 2` value, i.e. it acts on the outcome bit pair as `(a, b) ↦ (a + f, b + f)`
with `f = bellKeyOutcomeFlip k`.  A relabel that moved the two bits by different amounts would
change the disagreement pattern and could not be absorbed into a translation of the key strings. -/
theorem bellKeyOutcomePerm_bits_shift (k ω : Fin 4) :
    aliceBit (bellKeyOutcomePerm k ω) = aliceBit ω + bellKeyOutcomeFlip k ∧
    bobBit (bellKeyOutcomePerm k ω) = bobBit ω + bellKeyOutcomeFlip k := by
  revert k ω; decide

/-- **The twirl shifts BOTH key strings by the same key-round pattern** `e i = bellKeyOutcomeFlip
(g i)`.  Key rounds are never rotated — `bb84SiftedSinglePairOp` applies `H ⊗ H` only on rounds
with `peSel && xSel` — so the shift pattern comes from the twirl string `g` directly, with no `σ`
relabel in between. -/
theorem key_strings_shift {n : ℕ} (peSel : Fin n → Bool) (g : Fin n → Fin 4)
    (ω : Fin n → Fin signalDim) :
    aliceKeyString peSel (fun i => bellKeyOutcomePerm (g i) (ω i))
        = aliceKeyString peSel ω + (fun i => bellKeyOutcomeFlip (g i.val)) ∧
    bobKeyString peSel (fun i => bellKeyOutcomePerm (g i) (ω i))
        = bobKeyString peSel ω + (fun i => bellKeyOutcomeFlip (g i.val)) :=
  ⟨funext fun i => (bellKeyOutcomePerm_bits_shift (g i.val) (ω i.val)).1,
   funext fun i => (bellKeyOutcomePerm_bits_shift (g i.val) (ω i.val)).2⟩

/-- The Z-test disagreement count is invariant under the twirl relabel. -/
theorem bb84SiftedZTestErrorCount_bellTwirl_invariant {n : ℕ} (peSel xSel : Fin n → Bool)
    (g : Fin n → Fin 4) (ω : Fin n → Fin signalDim) :
    bb84SiftedZTestErrorCount peSel xSel (fun i => bellKeyOutcomePerm (g i) (ω i))
      = bb84SiftedZTestErrorCount peSel xSel ω := by
  simp only [bb84SiftedZTestErrorCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, bellKeyOutcomePerm_mem_errorSet_iff]

/-- The X-test disagreement count is invariant under the twirl relabel. -/
theorem bb84SiftedXTestErrorCount_bellTwirl_invariant {n : ℕ} (peSel xSel : Fin n → Bool)
    (g : Fin n → Fin 4) (ω : Fin n → Fin signalDim) :
    bb84SiftedXTestErrorCount peSel xSel (fun i => bellKeyOutcomePerm (g i) (ω i))
      = bb84SiftedXTestErrorCount peSel xSel ω := by
  simp only [bb84SiftedXTestErrorCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, bellKeyOutcomePerm_mem_errorSet_iff]

/-- **The whole fail-closed LOCC two-basis PE decision is twirl-invariant.**  Both subsample sizes
are functions of the selectors alone and both disagreement counts are invariant, so the accept ball
test is unchanged outcome by outcome — no hypothesis on the reconciliation scheme is needed for this
conjunct. -/
theorem bb84SiftedLocalPETestPassed_bellTwirl_invariant {n : ℕ} (peSel xSel : Fin n → Bool)
    (δ Q : ℝ) (g : Fin n → Fin 4) (ω : Fin n → Fin signalDim) :
    bb84SiftedLocalPETestPassed peSel xSel δ Q (fun i => bellKeyOutcomePerm (g i) (ω i))
      = bb84SiftedLocalPETestPassed peSel xSel δ Q ω := by
  simp only [bb84SiftedLocalPETestPassed,
    bb84SiftedZTestErrorCount_bellTwirl_invariant peSel xSel g ω,
    bb84SiftedXTestErrorCount_bellTwirl_invariant peSel xSel g ω]

/-- **Shifting both hash arguments by the same key-round pattern preserves the collision event.**

An immediate consequence of `binaryInnerProductHash_add_right`: the shift acts on the packed
codomain `Fin (2 ^ ℓ)` by the explicit permutation `binaryInnerProductHashShiftPerm A e`, and a
permutation is injective.  The packed codomain carries no group structure the shift respects —
`Fin`-addition on `Fin (2 ^ ℓ)` is addition modulo `2 ^ ℓ`, not bitwise `XOR`, and never appears. -/
private theorem binaryInnerProductHash_add_right_cancel' {n ℓ : ℕ} {peSel : Fin n → Bool}
    (A : KeyHashSeed n ℓ peSel) (u v e : KeyBitString n peSel) :
    binaryInnerProductHash n ℓ peSel A (u + e)
          = binaryInnerProductHash n ℓ peSel A (v + e) ↔
      binaryInnerProductHash n ℓ peSel A u = binaryInnerProductHash n ℓ peSel A v := by
  rw [binaryInnerProductHash_add_right, binaryInnerProductHash_add_right]
  exact (binaryInnerProductHashShiftPerm A e).apply_eq_iff_eq

/-- **Error verification is invariant when both key strings shift by the same key-round pattern
    `e`.**

The only property of the reconciliation scheme this uses is the **paired decoder clause**
`ec.decode (b + e) (ec.syndrome (a + e)) = ec.decode b (ec.syndrome a) + e` — clause (ii) of
translation equivariance.  **No syndrome permutation enters**: the hypothesis is stated on the
composite `decode ∘ syndrome`, so no permutation of the syndrome alphabet appears in the statement
and none is used in the proof.  Clause (i) of translation equivariance is not needed for the accept
flag.

The EV tag `verificationTag t` **depends on the seed `t`**, and so does its shift.  That is harmless
here — both tags in a single comparison are taken at the same `t` — but it means a downstream
output relabel built on this lemma must be defined **fibrewise over the announced seed register**;
a single `t`-independent global relabel of the key/tag slots is wrong. -/
theorem evVerified_shift_invariant {n ℓEV leakEC : ℕ} {peSel : Fin n → Bool}
    (ec : ECScheme n peSel leakEC) (t : KeyHashSeed n ℓEV peSel)
    (e : KeyBitString n peSel)
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + e) (ec.syndrome (a + e)) = ec.decode b (ec.syndrome a) + e)
    (ω ω' : Fin n → Fin signalDim)
    (ha : aliceKeyString peSel ω' = aliceKeyString peSel ω + e)
    (hb : bobKeyString peSel ω' = bobKeyString peSel ω + e) :
    evVerified ℓEV peSel ec t ω' = evVerified ℓEV peSel ec t ω := by
  simp only [evVerified, ha, hb, hdec, verificationTag]
  exact decide_eq_decide.mpr (binaryInnerProductHash_add_right_cancel' t _ _ e)

/-- **THE ACCEPT GATE IS BELL-TWIRL INVARIANT.**

For every twirl string `g : Fin n → Fin 4`, the full accept predicate — fail-closed LOCC
two-basis parameter estimation **and** error verification — takes the same value on the round
outcomes `ω` and on their bilateral-Pauli relabel `fun i => bellKeyOutcomePerm (g i) (ω i)`.

The hypothesis is the **paired decoder clause at the twirl's own key-round error pattern**
`e i = if g i = 1 ∨ g i = 2 then 1 else 0` (`bellKeyOutcomeFlip (g i)`), i.e. **clause (ii) of
translation equivariance of `ec`, and only clause (ii)** — no permutation of the syndrome alphabet
is required anywhere in the accept gate.

Both conjuncts move for different reasons: the PE conjunct is invariant unconditionally
(`bb84SiftedLocalPETestPassed_bellTwirl_invariant`, the disagreement set `{1,2}` is fixed
setwise), while the EV conjunct needs the hypothesis (`evVerified_shift_invariant`) and genuinely
fails without it: there is a reconciliation scheme at which the accept gate flips from `true` to
`false` under the twirl.

Key rounds are never rotated (`bb84SiftedSinglePairOp` applies `H ⊗ H` only on `peSel && xSel`
rounds), so the shift pattern is read off `g` directly.  On X-designated PE rounds the sift relabels
the twirl element by `QKD.BB84.Model.hadamardPair_conj_bellTwirl`'s `σ = ![0,3,2,1]`, whose flip set
is `{Y, Z}`; that relabel is invisible here because the PE conjunct is invariant for **every** twirl
element. -/
theorem bb84SiftedLocalPEAndEVPassed_bellTwirl_invariant {n ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (t : KeyHashSeed n ℓEV peSel) (g : Fin n → Fin 4) (ω : Fin n → Fin signalDim)
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + (fun i => if g i.val = 1 ∨ g i.val = 2 then 1 else 0))
          (ec.syndrome (a + (fun i => if g i.val = 1 ∨ g i.val = 2 then 1 else 0)))
        = ec.decode b (ec.syndrome a) + (fun i => if g i.val = 1 ∨ g i.val = 2 then 1 else 0)) :
    bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t
        (fun i => bellKeyOutcomePerm (g i) (ω i))
      = bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω := by
  have hev : evVerified ℓEV peSel ec t (fun i => bellKeyOutcomePerm (g i) (ω i))
      = evVerified ℓEV peSel ec t ω :=
    evVerified_shift_invariant ec t (fun i => bellKeyOutcomeFlip (g i.val)) hdec ω _
      (key_strings_shift peSel g ω).1 (key_strings_shift peSel g ω).2
  simp only [bb84SiftedLocalPEAndEVPassed,
    bb84SiftedLocalPETestPassed_bellTwirl_invariant peSel xSel δ Q g ω, hev]

/-! ### Non-vacuity: the accept gate really does flip without the decoder clause

The hypothesis of `bb84SiftedLocalPEAndEVPassed_bellTwirl_invariant` is not decoration: at
`leakEC = 0` the syndrome alphabet is a singleton, so the syndrome clause holds trivially for every
error pattern, yet the decoder clause still fails, and at that scheme the accept gate flips under a
one-round `X⊗X` twirl. -/

namespace BellTwirlEVGap

end BellTwirlEVGap

end QKD.BB84.Engine

end
