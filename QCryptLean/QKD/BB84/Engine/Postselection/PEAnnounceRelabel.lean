import QCryptLean.QKD.BB84.Engine.Postselection.ProtocolMapCovariance
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Engine.Postselection.SiftedAcceptTwirlInvariant
import QCryptLean.Quantum.TensorProducts.TensorRightId
import QCryptLean.QKD.BB84.Engine.Postselection.RegisterTrickReferee

/-!
# The announced-PE relabel unitary of the genuine-LOCC protocol object

The Bell-rotation route reads the parameter-estimation rounds in the Bell basis, so a bilateral
Pauli acts there as a diagonal `±1` phase that the projector measurement absorbs: the twirl
reaching the protocol map vanishes on the PE rounds, and the announced PE register is masked out
of the covariance.

In the genuine-LOCC family the PE rounds are measured locally and their outcomes are **announced**
(`bb84.pePassOutIndex`'s `pe` slot), so no masking is available: the twirl **relabels** the
announced PE block.  This file supplies the replacement machinery — the effective twirl string
after the sift, the key-round error pattern it imposes, and the Kraus-index reindexings the
per-Kraus and channel-level covariance theorems of `PEAnnounceRelabelGeneral.lean` are built from.

## Shape of the relabel

Write `h` for the twirl string as it reaches the computational measurement (see
`bb84SiftedTwirlString` below for how the sift produces it from the physical twirl `g`), and
`e = bellTwirlKeyError peSel h` for the key-round error pattern it imposes.  The relabel
`bb84PEAnnounceBellRelabel` acts on the announced output index by

* `flag = 0` (pass): `(kA, kB) ↦ (σ_{st.1} kA, σ_{st.1} kB)` with
  `σ_A = binaryInnerProductHashShiftPerm A e`;
* `flag = 1` (fail): `(kA, kB) ↦ (kA, kB)`, the identity;
* both branches: `evTag ↦ σ_{st.2} evTag`, `syn ↦ πsyn syn`, `pe ↦ bb84PEBlockRelabelPerm peSel h
pe`.

Two structural constraints are load-bearing and are visible in the statements below.

**The relabel is piecewise on the accept flag.**  `bb84.peFailOutIndex` hard-zeroes both key
slots, and the hash-argument shift does not fix `0` in general, so the relabel must act as the
identity on the abort flag rather than shifting the (zero) key slots there;
`bb84PEAnnounceBellRelabel_failOutIndex` records that the key slots are fixed on the abort
branch.

**The relabel is fibrewise over the announced seed register.**  `verificationTag t` depends on the
error-verification seed `t = st.2` and `binaryInnerProductHash … st.1` on the
privacy-amplification seed, so both shifts do; the relabel reads `st` off the index it is permuting.
That is legitimate precisely because `st` is an announced output coordinate of
`bb84.pePassOutIndex` and `bb84.peFailOutIndex`.  A `t`-independent global relabel is wrong
(`evVerified_shift_invariant`'s docstring records the same point for the accept gate).

## The syndrome permutation is explicit witness data, not a choice

Clause (i) of `ECScheme.IsTranslationEquivariant` supplies the syndrome-alphabet permutation
`π_e` existentially.  Extracting it would need `Classical.choose`, so every declaration here takes
`πsyn : Equiv.Perm (Fin (2 ^ leakEC))` together with its defining hypothesis
`∀ a, ec.syndrome (a + e) = πsyn (ec.syndrome a)` as explicit data.  Consumers holding a proof of
`ECScheme.IsTranslationEquivariant` for `ec` destructure the existential at the point of use.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B and §V.C
(`main.tex:906`–`:919`, the classical post-processing block whose
announcements are the registers relabelled here); Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5;
Christandl–König–Renner (2009), `arXiv:0809.3019`, `main.tex:268`–`:401` (\emph{Main Result}: the
Post-Selection Theorem `\label{thm:main}` :291–:301, the substate-extraction Lemma
`\label{lem:extractpart}` :319–:328). -/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

open QKD.BB84.Model.bb84
open QKD.BB84.Model

/-! ## The twirl string that reaches the computational measurement -/

/-- **The effective twirl string after the sift.**  `bb84SiftedRotation` applies `H ⊗ H` on
rounds that are both PE- and X-designated and the identity elsewhere, and `H ⊗ H` carries the
bilateral Bell twirl group to itself by the sign-free involution `bellHadSwap = ![0,3,2,1]`
(`hadamardPair_conj_bellTwirl`).  So the string the computational measurement sees is `g` relabelled
by `bellHadSwap` exactly on the X-designated PE rounds. -/
def bb84SiftedTwirlString {n : ℕ} (peSel xSel : Fin n → Bool) (g : Fin n → Fin 4) :
    Fin n → Fin 4 :=
  fun i => if peSel i && xSel i then bellHadSwap (g i) else g i

/-- On a key round the sift is the identity, so the effective twirl string is `g` itself.  This
is why the key-round error pattern `bellTwirlKeyError` may be read off either string. -/
theorem bb84SiftedTwirlString_of_key {n : ℕ} (peSel xSel : Fin n → Bool) (g : Fin n → Fin 4)
    (i : Fin n) (hi : peSel i = false) :
    bb84SiftedTwirlString peSel xSel g i = g i := by
  simp [bb84SiftedTwirlString, hi]

/-- **The sift conjugates the Bell twirl to the Bell twirl at the relabelled string.**

`V · U_g · V† = U_{g'}` with `V = bb84SiftedRotation n peSel xSel` and
`g' = bb84SiftedTwirlString peSel xSel g`.  This is an exact operator identity with no phase: the
per-round conjugation `H ⊗ H · G_k · H ⊗ H = G_{bellHadSwap k}` is sign-free
(`hadamardPair_conj_bellTwirl`), so unlike the Bell-rotation route there is no measurement-level
absorption step and no masking. -/
theorem bb84SiftedRotation_bellTwirl_conj (n : ℕ) (peSel xSel : Fin n → Bool)
    (g : Fin n → Fin 4) :
    bb84SiftedRotation n peSel xSel * bellTwirlUnitary n g *
        (bb84SiftedRotation n peSel xSel)ᴴ =
      bellTwirlUnitary n (bb84SiftedTwirlString peSel xSel g) := by
  have hV : bb84SiftedRotation n peSel xSel =
      tensorFamily (fun a => bb84SiftedSinglePairOp (peSel a) (xSel a)) := rfl
  have hU : ∀ g' : Fin n → Fin 4,
      bellTwirlUnitary n g' = tensorFamily (fun a => bb84BellSinglePairTwirlGroup (g' a)) :=
    fun _ => rfl
  rw [hV, hU, hU, conjTranspose_tensorFamily, tensorFamily_mul, tensorFamily_mul]
  refine congrArg tensorFamily (funext fun a => ?_)
  by_cases hx : (peSel a && xSel a) = true
  · rw [show bb84SiftedSinglePairOp (peSel a) (xSel a) = bb84HadamardPair by
        simp [bb84SiftedSinglePairOp, hx],
      bb84HadamardPair_hermitian, hadamardPair_conj_bellTwirl]
    simp [bb84SiftedTwirlString, hx]
  · rw [show bb84SiftedSinglePairOp (peSel a) (xSel a) = (1 : Op signalDim) by
        simp [bb84SiftedSinglePairOp, hx]]
    simp [bb84SiftedTwirlString, hx]

/-! ## Unpacking the base output index

`bb84.pePassOutIndex` and `bb84.peFailOutIndex` pack seven fields into
`Fin (bb84PEAnnounceBaseOutputDim n ℓ ℓEV peSel leakEC)` through nested `finProdFinEquiv`s.  The
relabel must read the accept flag and the announced seed pair, so the index is first unpacked into a
**control** register `(flag, st)` and a **payload** register `((kA, kB), ((evTag, syn), pe))`. -/

/-- The **control register** of a base output index: the accept flag and the announced seed pair.
Both are announced output coordinates, so a permutation of the output register may read them. -/
abbrev PEAnnounceControl (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) : Type :=
  Fin 2 × KeyHashSeedPairEV n ℓ ℓEV peSel

/-! ## The relabel permutation -/

/-- **The key-round error pattern imposed by the twirl string `h`**: `e i = bellKeyOutcomeFlip
    (h i)`
on key rounds.  This is the `e` at which `bb84SiftedLocalPEAndEVPassed_bellTwirl_invariant` needs
the paired decoder clause, and the `e` the hash-argument shifts are taken at. -/
def bellTwirlKeyError {n : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4) :
    KeyBitString n peSel :=
  fun i => bellKeyOutcomeFlip (h i.val)

/-- **The flag- and seed-controlled permutation of the two key slots.**  On the pass flag both key
slots are shifted by the hash-argument shift `σ_{st.1}` at the twirl's key-round error pattern; on
the abort flag it is the identity, because `bb84.peFailOutIndex` writes the zero key in both slots
on **both** the twirled and the untwirled outcome. -/
def bb84PEAnnounceKeyPairPerm {n : ℕ} (ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (h : Fin n → Fin 4)
    (c : PEAnnounceControl n ℓ ℓEV peSel) : Equiv.Perm (Fin (2 ^ ℓ) × Fin (2 ^ ℓ)) :=
  if c.1 = 0 then
    (binaryInnerProductHashShiftPerm c.2.1 (bellTwirlKeyError peSel h)).prodCongr
      (binaryInnerProductHashShiftPerm c.2.1 (bellTwirlKeyError peSel h))
  else Equiv.refl _

/-!
## How the twirl moves the announced fields
-/

/-- Alice's key string shifts by the twirl's key-round error pattern. -/
theorem bb84AliceKeyString_bellStringRelabel {n : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4)
    (ω : Fin n → Fin signalDim) :
    aliceKeyString peSel (bellStringRelabel n h ω) =
      aliceKeyString peSel ω + bellTwirlKeyError peSel h :=
  (key_strings_shift peSel h ω).1

/-- Bob's raw key string shifts by the same pattern. -/
theorem bb84BobKeyString_bellStringRelabel {n : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4)
    (ω : Fin n → Fin signalDim) :
    bobKeyString peSel (bellStringRelabel n h ω) =
      bobKeyString peSel ω + bellTwirlKeyError peSel h :=
  (key_strings_shift peSel h ω).2

/-!
## Kraus-index reindexings for the per-Kraus and channel-level covariance

`bb84SiftedLocalPEAndEVPassed_bellTwirl_invariant` keeps each Kraus operator on the same branch of
the accept split; the column relabels with the unit phase `bellTwirlSign` of the signed twirl. The
two reindexings below carry the row, and are the substrate the per-Kraus and channel-level
covariance theorems of `PEAnnounceRelabelGeneral.lean` are built from — the ideal map's transcript
retains the `ω`-dependent announcements `evTag`, `syn` and `pe`, so unlike a transcript recording
only the fresh key and the seed, it also carries the relabel.
-/

/-- The Kraus-index reindexing of the real/ideal **fail** and real **pass** families: relabel the
outcome string by the twirl.  An involution. -/
def bb84PEAnnounceOutcomeReindex (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (h : Fin n → Fin 4) :
    (KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) ≃
      (KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) :=
  (Equiv.refl (KeyHashSeedPairEV n ℓ ℓEV peSel)).prodCongr (bellStringRelabelEquiv n h)

/-- The Kraus-index reindexing of the **ideal pass** family: relabel the outcome string by the twirl
and translate the fresh uniform key by the privacy-amplification-seed shift at the announced seed.
-/
def bb84PEAnnounceIdealReindex (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (h : Fin n → Fin 4) :
    ((Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel) ≃
      ((Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel) where
  toFun x := (bellStringRelabel n h x.1,
    binaryInnerProductHashShiftPerm x.2.2.1 (bellTwirlKeyError peSel h) x.2.1, x.2.2)
  invFun x := (bellStringRelabel n h x.1,
    (binaryInnerProductHashShiftPerm x.2.2.1 (bellTwirlKeyError peSel h)).symm x.2.1, x.2.2)
  left_inv x := by
    obtain ⟨ω, k, st⟩ := x
    simp [bellStringRelabel_involutive n h ω]
  right_inv x := by
    obtain ⟨ω, k, st⟩ := x
    simp [bellStringRelabel_involutive n h ω]

/-! ## From the physical twirl to the relabel: sift, then measure

The protocol map is `PA/abort ∘ measurementChannel`
(`bb84SiftedPEAnnounceEveVisibleProtocol`), and it is fed the output of the sifted attack
channel.  The physical twirl `U_g` therefore reaches the PA/abort map as `U_{g'}` with
`g' = bb84SiftedTwirlString peSel xSel g` — the sift relabels it exactly on the X-designated PE
rounds (`bb84SiftedRotation_bellTwirl_conj`) and the computational measurement lets it through as a
monomial (`measurementChannel_bellTwirl_outcomeRelabel`).  Since the sift is the identity on key
rounds, the key-round error pattern — and hence every hypothesis on `ec` — may be stated at the
physical `g`. -/

/-- The key-round error pattern is the same for the physical and the sift-relabelled twirl string:
key rounds are never rotated. -/
theorem bellTwirlKeyError_siftedTwirlString {n : ℕ} (peSel xSel : Fin n → Bool)
    (g : Fin n → Fin 4) :
    bellTwirlKeyError peSel (bb84SiftedTwirlString peSel xSel g) =
      bellTwirlKeyError peSel g :=
  funext fun i =>
    show bellKeyOutcomeFlip (bb84SiftedTwirlString peSel xSel g i.val) =
        bellKeyOutcomeFlip (g i.val) by
      rw [bb84SiftedTwirlString_of_key peSel xSel g i.val i.property]

/-- **The sifted conjugation channel carries the Bell twirl to the relabelled Bell twirl.** -/
theorem bb84SiftedConjChannel_bellTwirl_conj (n eveDim : ℕ) (peSel xSel : Fin n → Bool)
    (g : Fin n → Fin 4) (M : Op (4 ^ n * eveDim)) :
    bb84SiftedConjChannel n eveDim peSel xSel
        (Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim) * M *
          (Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim))ᴴ) =
      Op.tensor (bellTwirlUnitary n (bb84SiftedTwirlString peSel xSel g)) (1 : Op eveDim) *
        bb84SiftedConjChannel n eveDim peSel xSel M *
        (Op.tensor (bellTwirlUnitary n (bb84SiftedTwirlString peSel xSel g))
          (1 : Op eveDim))ᴴ := by
  have happly : ∀ A0 : Op (4 ^ n * eveDim),
      bb84SiftedConjChannel n eveDim peSel xSel A0 =
        Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim) * A0 *
          (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))ᴴ := by
    intro A0; simp [bb84SiftedConjChannel, krausMapFintype]
  have hVu : (bb84SiftedRotation n peSel xSel)ᴴ * bb84SiftedRotation n peSel xSel = 1 :=
    bb84SiftedRotation_unitary n peSel xSel
  have hcomm : bb84SiftedRotation n peSel xSel * bellTwirlUnitary n g =
      bellTwirlUnitary n (bb84SiftedTwirlString peSel xSel g) *
        bb84SiftedRotation n peSel xSel := by
    rw [← bb84SiftedRotation_bellTwirl_conj n peSel xSel g, Matrix.mul_assoc, Matrix.mul_assoc,
      hVu, Matrix.mul_one]
  rw [happly, happly]
  rw [show Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim) *
        (Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim) * M *
          (Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim))ᴴ) *
        (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))ᴴ =
      (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim) *
          Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim)) * M *
        (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim) *
          Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim))ᴴ from by
      rw [Matrix.conjTranspose_mul]; noncomm_ring]
  have hsplit : Op.tensor (bellTwirlUnitary n (bb84SiftedTwirlString peSel xSel g))
        (1 : Op eveDim) *
        Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim) =
      Op.tensor (bellTwirlUnitary n (bb84SiftedTwirlString peSel xSel g) *
        bb84SiftedRotation n peSel xSel) (1 : Op eveDim) := by
    rw [Op.tensor_mul, Matrix.mul_one]
  rw [Op.tensor_mul, Matrix.mul_one, hcomm, ← hsplit, Matrix.conjTranspose_mul]
  noncomm_ring

end QKD.BB84.Engine

end
