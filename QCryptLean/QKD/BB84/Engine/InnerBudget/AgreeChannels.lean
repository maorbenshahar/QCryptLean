import QCryptLean.Quantum.Channels.CPTP.BlockPinchingChannel
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Engine.InnerBudget.KeyHashEC

/-!
# Agree-branch real and ideal pass channels for the general-`m` PE scheme

Restrictions of the general-`m` real and ideal pass Kraus families
(`bb84.retainedSiftedPEAnnouncePassBranchKraus`, `bb84.retainedSiftedPEAnnounceIdealPassKraus`)
and of the corresponding pass channels to the branch on which Alice's and Bob's sifted key
strings agree (`bb84SiftedKeyStringsDiffer`), zeroing every outcome where they differ. Paired
with the complementary differ-branch pass channels, these split the base-scheme pass channel
into an agree part and a differ part.

## Main definitions

* `bb84RealPassAgreeKraus`, `bb84IdealPassAgreeKraus` — the agree-restricted real/ideal pass
  Kraus families.
* `bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel`,
  `bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel` — the corresponding agree pass channels.

## References

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`), the general test-set
size `m` at `main.tex:909` ("a random subset of $m$ signals") and `:913`
("the remaining $\nkey = n - m$ signals").
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-- The general-`m` real pass Kraus family, zeroed on the outcomes where Alice's and Bob's
sifted key strings differ. -/
def bb84RealPassAgreeKraus (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim) →
      Matrix (Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
        (Fin (4 ^ n * eveDim)) ℂ :=
  fun k =>
    if bb84SiftedKeyStringsDiffer peSel ec k.2 then 0
    else bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim
      peSel xSel leakEC ec δ Q k

/-- The general-`m` ideal pass Kraus family, zeroed on the outcomes where Alice's and Bob's
sifted key strings differ. -/
def bb84IdealPassAgreeKraus (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    (Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel →
      Matrix (Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim))
        (Fin (4 ^ n * eveDim)) ℂ :=
  fun k =>
    if bb84SiftedKeyStringsDiffer peSel ec k.1 then 0
    else bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim
      peSel xSel leakEC ec δ Q k

/-- The accept branch of the general-`m` real privacy-amplification/abort channel, restricted to
the outcomes where Alice's and Bob's sifted key strings agree. -/
noncomputable def bb84SiftedPEAnnounceEveVisibleRealAgreePassChannel
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  ((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
      krausMapFintype (bb84RealPassAgreeKraus n m ℓ ℓEV eveDim
        peSel xSel leakEC ec δ Q)).comp
    ((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel))

/-- The accept branch of the general-`m` ideal privacy-amplification/abort channel, restricted to
the outcomes where Alice's and Bob's sifted key strings agree. -/
noncomputable def bb84SiftedPEAnnounceEveVisibleIdealAgreePassChannel
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim))
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (Q δ : ℝ) :
    Op (4 ^ n) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim) :=
  ((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
      krausMapFintype (bb84IdealPassAgreeKraus n m ℓ ℓEV eveDim
        peSel xSel leakEC ec δ Q)).comp
    ((measurementChannel n eveDim).comp
      (bb84SiftedConjAfterPre eveDim pre peSel xSel))

end QKD.BB84.Engine

end
