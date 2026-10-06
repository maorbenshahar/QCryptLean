import Mathlib.Tactic.Ring
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.LOCC.ClassicalInstruments
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.KeyHash

/-!
# Classical data for BB84

Functions of a party's local raw register, encodings of public announcements, and the
parameter-estimation and error-verification decisions. These are the classical postprocessing
steps of Nahar et al., arXiv:2403.11851, Section V.C. Protocol actions consume these functions;
this module defines no executable protocol or channel.
-/

noncomputable section

open QKD.BB84.Engine

namespace QKD.BB84.Model

/-- Alice's key string, read off her own register. -/
def aliceKeyOf (n : ℕ) (peSel : Fin n → Bool) (x : Fin (2 ^ n)) : KeyBitString n peSel :=
  fun i => LOCC.registerBit n i.val x

/-- Bob's raw key string, read off his own register. -/
def bobKeyOf (n : ℕ) (peSel : Fin n → Bool) (y : Fin (2 ^ n)) : KeyBitString n peSel :=
  fun i => LOCC.registerBit n i.val y

/-- Alice's error-verification tag and reconciliation syndrome at the selected public seed pair,
computed from her local raw register. -/
def evTagSynOf (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (r : Fin (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) (x : Fin (2 ^ n)) :
    Fin (2 ^ ℓEV * 2 ^ leakEC) :=
  finProdFinEquiv
    (verificationTag n ℓEV peSel
        ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm r).2
        (aliceKeyOf n peSel x),
      ec.syndrome (aliceKeyOf n peSel x))

/-- **The parameter-estimation decision at a general `m`, as a function of the announced bits
alone.** The two subsample *sizes* are functions of the selectors, so nothing but the announced
bits is read. -/
def peOKOfAnnounced {n : ℕ} (m : ℕ) (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (as bs : Fin (n - bb84KeyRoundCount n m) → Fin 2) : Bool :=
  (decide (0 < bb84SiftedZTestSampleSize peSel xSel) &&
    decide (|((Finset.univ.filter fun j => xSel (bb84PERoundIdx peSel j) = false ∧
        as j ≠ bs j).card : ℝ) / bb84SiftedZTestSampleSize peSel xSel - Q| ≤ δ)) &&
  (decide (0 < bb84SiftedXTestSampleSize peSel xSel) &&
    decide (|((Finset.univ.filter fun j => xSel (bb84PERoundIdx peSel j) = true ∧
        as j ≠ bs j).card : ℝ) / bb84SiftedXTestSampleSize peSel xSel - Q| ≤ δ))

/-- **The accept flag at a general `m`, as a function of Bob's register and the announcements.**
`0` accepts. Bob is the party who can evaluate it: the error-verification conjunct compares
Alice's *announced* tag with the tag of Bob's syndrome-decoded string, and only Bob holds that
string. -/
def acceptFlagOf (n m ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (as bs : Fin (n - bb84KeyRoundCount n m) → Fin 2) (t : KeyHashSeed n ℓEV peSel)
    (evTag : Fin (2 ^ ℓEV)) (syn : Fin (2 ^ leakEC)) (y : Fin (2 ^ n)) : Fin 2 :=
  if peOKOfAnnounced m peSel xSel δ Q as bs = true ∧
      evTag = verificationTag n ℓEV peSel t (ec.decode (bobKeyOf n peSel y) syn)
    then 0 else 1

/-- **The parameter-estimation decision, as a function of the announced bits alone**, at the
canonical test-set size — the `peOKOfAnnounced` special case at `m = (n + 1) / 2`. -/
def peOKOfAnnouncedCanonical {n : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (as bs : Fin (n - bb84KeyRoundCountCanonical n) → Fin 2) : Bool :=
  peOKOfAnnounced ((n + 1) / 2) peSel xSel δ Q as bs

/-- **The accept flag, as a function of Bob's register and the announcements**, at the canonical
test-set size — the `acceptFlagOf` special case at `m = (n + 1) / 2`. -/
def acceptFlagOfCanonical (n ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (as bs : Fin (n - bb84KeyRoundCountCanonical n) → Fin 2) (t : KeyHashSeed n ℓEV peSel)
    (evTag : Fin (2 ^ ℓEV)) (syn : Fin (2 ^ leakEC)) (y : Fin (2 ^ n)) : Fin 2 :=
  acceptFlagOf n ((n + 1) / 2) ℓEV peSel xSel leakEC ec δ Q as bs t evTag syn y

/-- The default parameter-estimation decision is the instance with `m = (n + 1) / 2`. -/
theorem peOKOfAnnounced_canonical {n : ℕ} (peSel xSel : Fin n → Bool) (δ Q : ℝ)
    (as bs : Fin (n - bb84KeyRoundCountCanonical n) → Fin 2) :
    peOKOfAnnounced ((n + 1) / 2) peSel xSel δ Q as bs =
      peOKOfAnnouncedCanonical peSel xSel δ Q as bs := rfl

/-- **Alice's key slot**: her hashed key on accept, zero on abort. -/
def aliceKeySlotOf (n ℓ : ℕ) (peSel : Fin n → Bool) (s : KeyHashSeed n ℓ peSel) (f : Fin 2)
    (x : Fin (2 ^ n)) : Fin (2 ^ ℓ) :=
  if f = 0 then (aliceKeyHashFamily n ℓ peSel).hash s (aliceKeyOf n peSel x)
  else ⟨0, Nat.two_pow_pos ℓ⟩

/-- **Bob's key slot**: the hash of his *reconciled* string — his own bits decoded against Alice's
**announced** syndrome, not a recomputation from her raw string. -/
def bobKeySlotOf (n ℓ : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (s : KeyHashSeed n ℓ peSel) (syn : Fin (2 ^ leakEC))
    (f : Fin 2) (y : Fin (2 ^ n)) : Fin (2 ^ ℓ) :=
  if f = 0 then
    (aliceKeyHashFamily n ℓ peSel).hash s (ec.decode (bobKeyOf n peSel y) syn)
  else ⟨0, Nat.two_pow_pos ℓ⟩

/-- The alphabet of Alice's fused `(seed, tag, syndrome)` announcement. -/
abbrev bb84AnnounceCard (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) : ℕ :=
  Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) * (2 ^ ℓEV * 2 ^ leakEC)

/-- The seed pair the transcript digit `r` names. -/
def announcedSeed (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (r : Fin (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) :
    KeyHashSeedPairEV n ℓ ℓEV peSel :=
  (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm r

/-- Cardinality of the finite permutation type. -/
theorem permCardEq (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  simp [Fintype.card_perm]
end QKD.BB84.Model

namespace QKD.BB84.Engine

/-- Dimension of the seed-pair, verification-tag, syndrome and parameter-estimation
transcript, excluding the permutation and final decision flag. -/
abbrev bb84PEAnnounceInnerTranscriptDim (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) : ℕ :=
  Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) * 2 ^ ℓEV * 2 ^ leakEC *
    signalDim ^ (n - bb84KeyRoundCount n m)

/-- Dimension of the pre-decision public transcript, including its permutation cell. -/
abbrev bb84SymPEAnnounceTranscriptInnerDim (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) : ℕ :=
  bb84PEAnnounceInnerTranscriptDim n m ℓ ℓEV peSel leakEC * n.factorial

end QKD.BB84.Engine
