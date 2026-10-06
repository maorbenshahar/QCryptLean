import QCryptLean.QKD.BB84.ErrorCorrection

/-!
# The differ event

`bb84SiftedKeyStringsDiffer` gates the inner-budget Kraus split by whether Alice's and Bob's
reconciled key strings actually differ. The protocol-level objects it is built from — key strings,
`ECScheme` — live in `QCryptLean.QKD.BB84.ErrorCorrection`; this analysis-layer predicate
stays in the `Engine`, upstream of both the inner-budget Kraus split that gates by it and the
announce-conditioning lemmas about it.

## Main definitions

- `bb84SiftedKeyStringsDiffer`: the `Bool`-valued differ event, Alice's key string against Bob's
  syndrome-decoded string.

## Main results

- `bb84SiftedKeyStringsDiffer_eq_true_iff` (`@[simp]`): identifies the `Bool` differ event
  with the `Prop` it decides.
-/

noncomputable section

namespace QKD.BB84.Engine

/-- **The differ event**, as a `Bool`: Alice's key string differs from Bob's reconciled string.
    Bool-valued so that it can gate a Kraus family alongside the accept predicate
    `bb84SiftedLocalPEAndEVPassed`; `bb84SiftedKeyStringsDiffer_eq_true_iff` identifies it with
    the `Prop` the scalar weight functional `bb84SiftedEveVisible_differAndAcceptWeight` uses. -/
def bb84SiftedKeyStringsDiffer {n : ℕ} (peSel : Fin n → Bool) {leakEC : ℕ}
    (ec : QKD.BB84.ECScheme n peSel leakEC) (ω : Fin n → Fin QKD.BB84.signalDim) : Bool :=
  decide (QKD.BB84.aliceKeyString peSel ω ≠
    ec.decode (QKD.BB84.bobKeyString peSel ω) (ec.syndrome (QKD.BB84.aliceKeyString peSel ω)))

@[simp] lemma bb84SiftedKeyStringsDiffer_eq_true_iff {n : ℕ} (peSel : Fin n → Bool) {leakEC : ℕ}
    (ec : QKD.BB84.ECScheme n peSel leakEC) (ω : Fin n → Fin QKD.BB84.signalDim) :
    bb84SiftedKeyStringsDiffer peSel ec ω = true ↔
      QKD.BB84.aliceKeyString peSel ω ≠
        ec.decode (QKD.BB84.bobKeyString peSel ω)
          (ec.syndrome (QKD.BB84.aliceKeyString peSel ω)) := by
  simp [bb84SiftedKeyStringsDiffer]

end QKD.BB84.Engine

end
