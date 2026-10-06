import QCryptLean.Quantum.Channels.CPTP.BlockPinchingChannel
import QCryptLean.QKD.BB84.Engine.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Engine.EntropyFloor.AnnounceConditioningCQ
import QCryptLean.Math.LinearAlgebra.PermutationMatrix
import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.CastHelpers

/-!
# The agree-block pass-support / leftover-hashing bridge

The genuine-LOCC counterpart of the referee's sifted pass-support stack,
restricted to the **agree block** — the outcomes on which Alice's key string
equals Bob's syndrome-decoded string. It bounds half the CKR tensor trace norm of the
agree-restricted real/ideal difference by the generalized trace distance between the Alice-bit
seed-key
extractor output and the seed-uniform output, both scored on a τ-side CQ state whose **quantum
(conditioning) register carries every classical announcement**.

## Why the agree block is exactly where the leftover-hashing substrate applies

`keyCopyPostprocessOutputIndex` (`KeyCopyPostprocess/Basic.lean`) emits the key **duplicated**, `(z,
z)`: the generic substrate `classicalKeyCopyPostprocess` can only ever produce `kA = kB`.  The real
pass Kraus (`bb84.retainedSiftedPEAnnouncePassBranchKraus`, `SiftedPEAnnounce.lean`) writes `kA =
hash_s(aliceKeyString ω)` and `kB = hash_s(ec.decode (bobKeyString ω) syn)`.  On the agree block
those two strings coincide, so `kA = kB` and the pass index is literally a
`keyCopyPostprocessOutputIndex`.  The differ block is provably outside the substrate and is charged
separately by the operator correctness leg
(`bb84SiftedPEAnnounceEveVisible_differBlock_ckrTensorTraceNorm_le_two_pow_neg_lEV`).

## Announcements stay on the quantum side

The announced syndrome, error-verification seed and tag, and PE-outcome block are carried by the
**conditioning** register of the leftover-hashing input state, never coarsened away.  Coarsening an
announced register away while the channel writes it into the transcript asserts `‖X‖₁ ≤ ‖Tr X‖₁`,
the data-processing inequality backwards; the exact counterexample has left-hand side `1`,
right-hand side `1/2`.  The corrected register order — announce kernel first, coarsening second — is
realised here by `bb84AliceKeyAnnounceCQ` (`SiftedPrivacyAmplification/AnnounceConditioningCQ.lean`)
followed by `CQState.tensorLeftKernel` at `InfoTheory.SmoothMinEntropy.bb84AnnounceKernel`.

## Where the seed pair splits, and why a relabelling is unavoidable

The transcript index `bb84.pePassOutIndex` writes the announced seed **pair**
`st : KeyHashSeedPairEV n ℓ ℓEV peSel` as the single digit
`Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel) st`.  The two halves of that pair sit on
opposite sides of the leftover-hashing object:

* the privacy-amplification seed (the pair's first component) is the **hash seed**, so it must be
  the classical seed register of `seedKeyExtractorOutputState` (the ideal `seedUniformOutputState`
  is uniform over it);
* the error-verification seed (the pair's second component) must be in the **conditioning**
  register, because the announced tag `verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω)`
  depends on it and the ideal
  arm does **not** randomise the tag.  A conditioning block of `seedKeyExtractorOutputState` cannot
  depend on the seed, so the only way to carry the tag is together with its own uniformly mixed seed
  register — which is exactly the graph-projector shape of
  `InfoTheory.SmoothMinEntropy.uniformSeededAnnounce` that `bb84AnnounceKernel` is built from.

`Fintype.equivFin` on a product type does not factor through `finProdFinEquiv`, so recombining the
two halves into the single transcript digit is a genuine basis relabelling of the output register.
It is a permutation, hence a unitary conjugation and CPTP (`isCPTP_unitary_conjugation`), and it is
folded into the postprocess `Φ` of
`ckrTensorTraceNorm_le_two_traceDistanceGen_of_cptp_postprocess_eq` together with the dimension
cast. The relabelling also fixes the digit order, so the conditioning register is kept
byte-identical to the one the announce charge `bb84_smoothMinEntropy_announce_ge_sub_leak` is stated
on.

## The split point is a parameter

Nahar, Tupkary, Zhao, Lütkenhaus and Tan state the protocol at a **free test-set size `m`**
(arXiv:2403.11851, `main.tex:909`, `:913-915`); `m = ⌈n/2⌉` is this codebase's default
instance, not a value the paper fixes.  Every declaration below that mentions the split point
carries `bb84KeyRoundCount n m = n − m` directly as a parameter.

**No constraint relating `m` to `n` appears anywhere in this file** — no `m ≤ n`, no `m < n`, no
`2·m ≤ n`, no `bb84KeyCount`.  The register dimension `signalDim ^ (n − (n − m))` is
nonzero at every `m`, the relabelling is a permutation at every `m`, and the two pass-output
identities are index algebra; `m = 0` (empty test set, one-dimensional PE register) and `m = n`
(the whole outcome string announced) are covered and degenerate rather than excluded.

## Main definitions
- `keyCopyAnnounceSrcPack`, `keyCopyAnnounceTgtPack`, `keyCopyAnnounceDigitRearrange`,
  `keyCopyAnnounceRelabel`, `keyCopyAnnounceRelabelLinear`: the protocol-free digit packings and the
  output-register relabelling channel.  Already general — the PE register enters them as the
  spectator dimension `dPE`.
- `bb84PEBlockIndex`: the announced PE-outcome digit of an outcome string, at a general test-set
  size `m`.
- `bb84AliceSeedPassTranscript`: the `(flag = 0, privacy-amplification seed)` transcript prefix.
- `bb84SiftedAgreeAcceptCQState`: the agree-and-accept filtered τ-side CQ state.
- `bb84PEAnnounceAgreeLHLInput`: its announce-conditioned,
  Alice-key-coarsened form — the state the leftover-hashing distance is scored on.
- `bb84PEAnnounceAgreeLHLPostprocess`: the CPTP
  postprocess carrying the leftover-hashing output onto the protocol's base output register.

## Main results
- `bb84PEAnnounceAgreeLHLPostprocess_isCPTP`.
- `realAgreePass_mapTensorId_eq_lhlPostprocess_seedKeyOutput`
  and `..._idealAgreePass_mapTensorId_eq_lhlPostprocess_seedUniformOutput`: the two pass-output
  block identities.
- `bb84SiftedPEAnnounceEveVisible_agreeBlock_traceDistance_le_LHL_distance`: the
  bridge.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, Thm 3, App. B
main.tex:1341–:1413 (Appendix B's proof of Theorem 3: the accept-block split `\label{eq:tausplit}`
(main.tex:1356–:1362), the Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed
min-entropy bound `\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting
step `\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413) — (B18)
retains the announcements `Cⁿ C_E` in the leftover-hashing output, §V.C (announced syndrome and
error-verification tag), and `main.tex:909`, `:913-915` for the general test set size `m`; Renner
(2005), `arXiv:quant-ph/0512258v2`, §6.5 and Lemma 3.1.10 / Cor. 3.1.11; Christandl-König-Renner
(2009), `arXiv:0809.3019`, main.tex:268–:401 (\emph{Main Result}: Theorem `\label{thm:main}`
:291–:301, Lemma `\label{lem:extractpart}` :319–:328). -/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.QuantumLHL
open Quantum.Symmetry
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## Protocol-free digit packings for the announce-retaining postprocess

These four declarations mention no BB84 object: they package the output register of
`classicalKeyCopyPostprocess` with a classical-announce conditioning register into its digits, and
relabel those digits into the layout a protocol transcript fixes.  They belong in
`InfoTheory/QuantumLHL/KeyCopyPostprocess/`; they are kept here so that this leaf adds a single
module. -/

/-- Digits of the `classicalKeyCopyPostprocess` output register when the reference register carries
a `(syndrome, seed, tag)` announce block in its high digits and a further announce block below it:

`key | key | flag | hash seed | syndrome | announce seed | tag | extra announce | Eve | reference`.
-/
def keyCopyAnnounceSrcPack (dk dSeed dLeak dSev dEv dPE dE dR : ℕ) :
    ((Fin dk × Fin dk) × (Fin 2 × Fin dSeed)) ×
        ((Fin dLeak × (Fin dSev × Fin dEv)) × (Fin dPE × (Fin dE × Fin dR))) ≃
      Fin ((dk * dk * (2 * dSeed)) * ((dLeak * (dSev * dEv)) * (dPE * (dE * dR)))) :=
  (Equiv.prodCongr
      ((Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans finProdFinEquiv)
      ((Equiv.prodCongr
          ((Equiv.prodCongr (Equiv.refl (Fin dLeak)) finProdFinEquiv).trans finProdFinEquiv)
          ((Equiv.prodCongr (Equiv.refl (Fin dPE)) finProdFinEquiv).trans
            finProdFinEquiv)).trans finProdFinEquiv)).trans
    finProdFinEquiv

/-- Digits of a protocol base output register carrying a merged seed digit:

`key | key | flag | seed pair | tag | syndrome | extra announce`, then `Eve`, then `reference`. -/
def keyCopyAnnounceTgtPack (dk dSpair dEv dLeak dPE dE dR : ℕ) :
    ((((Fin dk × Fin dk) ×
          (Fin 2 × (((Fin dSpair × Fin dEv) × Fin dLeak) × Fin dPE))) × Fin dE) × Fin dR) ≃
      Fin (((dk * dk * (2 * (dSpair * dEv * dLeak * dPE))) * dE) * dR) :=
  (Equiv.prodCongr
      ((Equiv.prodCongr
          ((Equiv.prodCongr finProdFinEquiv
              ((Equiv.prodCongr (Equiv.refl (Fin 2))
                  ((Equiv.prodCongr
                      ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin dLeak))).trans
                        finProdFinEquiv)
                      (Equiv.refl (Fin dPE))).trans finProdFinEquiv)).trans
                finProdFinEquiv)).trans finProdFinEquiv)
          (Equiv.refl (Fin dE))).trans finProdFinEquiv)
      (Equiv.refl (Fin dR))).trans
    finProdFinEquiv

/-- The digit rearrangement: merge the hash-seed digit with the announced-seed digit into a single
seed-pair digit along `μ`, and move the syndrome digit below the tag digit.  Every other digit is
carried through unchanged. -/
def keyCopyAnnounceDigitRearrange {dk dSeed dLeak dSev dEv dPE dE dR dSpair : ℕ}
    (μ : Fin dSeed × Fin dSev ≃ Fin dSpair) :
    (((Fin dk × Fin dk) × (Fin 2 × Fin dSeed)) ×
        ((Fin dLeak × (Fin dSev × Fin dEv)) × (Fin dPE × (Fin dE × Fin dR)))) ≃
      ((((Fin dk × Fin dk) ×
          (Fin 2 × (((Fin dSpair × Fin dEv) × Fin dLeak) × Fin dPE))) × Fin dE) × Fin dR) where
  toFun := fun ⟨⟨⟨zA, zB⟩, ⟨fl, s⟩⟩, ⟨⟨syn, ⟨t, ev⟩⟩, ⟨pe, ⟨e, r⟩⟩⟩⟩ =>
    ((((zA, zB), (fl, (((μ (s, t), ev), syn), pe))), e), r)
  invFun := fun ⟨⟨⟨⟨zA, zB⟩, ⟨fl, ⟨⟨⟨stp, ev⟩, syn⟩, pe⟩⟩⟩, e⟩, r⟩ =>
    ((((zA, zB), (fl, (μ.symm stp).1)),
      ((syn, ((μ.symm stp).2, ev)), (pe, (e, r)))))
  left_inv := by
    rintro ⟨⟨⟨zA, zB⟩, ⟨fl, s⟩⟩, ⟨⟨syn, ⟨t, ev⟩⟩, ⟨pe, ⟨e, r⟩⟩⟩⟩
    simp
  right_inv := by
    rintro ⟨⟨⟨⟨zA, zB⟩, ⟨fl, ⟨⟨⟨stp, ev⟩, syn⟩, pe⟩⟩⟩, e⟩, r⟩
    simp

/-- The dimension identity behind the relabelling: merging the two seed digits and reordering the
syndrome digit preserves the total register dimension. -/
lemma keyCopyAnnounceRelabel_dim (dk dSeed dLeak dSev dEv dPE dE dR dSpair : ℕ)
    (hcard : dSeed * dSev = dSpair) :
    (dk * dk * (2 * dSeed)) * ((dLeak * (dSev * dEv)) * (dPE * (dE * dR))) =
      ((dk * dk * (2 * (dSpair * dEv * dLeak * dPE))) * dE) * dR := by
  subst hcard; ring

/-- The output-register relabelling as a permutation of basis indices. -/
def keyCopyAnnounceRelabel {dk dSeed dLeak dSev dEv dPE dE dR dSpair : ℕ}
    (μ : Fin dSeed × Fin dSev ≃ Fin dSpair) :
    Fin ((dk * dk * (2 * dSeed)) * ((dLeak * (dSev * dEv)) * (dPE * (dE * dR)))) ≃
      Fin (((dk * dk * (2 * (dSpair * dEv * dLeak * dPE))) * dE) * dR) :=
  (keyCopyAnnounceSrcPack dk dSeed dLeak dSev dEv dPE dE dR).symm.trans
    ((keyCopyAnnounceDigitRearrange (dk := dk) (dPE := dPE) (dE := dE) (dR := dR) μ).trans
      (keyCopyAnnounceTgtPack dk dSpair dEv dLeak dPE dE dR))

/-- The relabelling as a permutation of the target register, after the dimension cast. -/
def keyCopyAnnounceRelabelPerm {dk dSeed dLeak dSev dEv dPE dE dR dSpair : ℕ}
    (μ : Fin dSeed × Fin dSev ≃ Fin dSpair) (hcard : dSeed * dSev = dSpair) :
    Equiv.Perm (Fin (((dk * dk * (2 * (dSpair * dEv * dLeak * dPE))) * dE) * dR)) :=
  (finCongr (keyCopyAnnounceRelabel_dim dk dSeed dLeak dSev dEv dPE dE dR dSpair hcard)).symm.trans
    (keyCopyAnnounceRelabel (dk := dk) (dPE := dPE) (dE := dE) (dR := dR) μ)

/-- The relabelling channel: the dimension cast followed by conjugation with the basis permutation.
Both stages are CPTP, the second because a permutation matrix is unitary. -/
def keyCopyAnnounceRelabelLinear {dk dSeed dLeak dSev dEv dPE dE dR dSpair : ℕ}
    (μ : Fin dSeed × Fin dSev ≃ Fin dSpair) (hcard : dSeed * dSev = dSpair) :
    Op ((dk * dk * (2 * dSeed)) * ((dLeak * (dSev * dEv)) * (dPE * (dE * dR)))) →ₗ[ℂ]
      Op (((dk * dk * (2 * (dSpair * dEv * dLeak * dPE))) * dE) * dR) where
  toFun A :=
    Equiv.Perm.permMatrix ℂ
        (keyCopyAnnounceRelabelPerm (dk := dk) (dPE := dPE) (dE := dE) (dR := dR) μ hcard).symm *
      (Op.castDim (keyCopyAnnounceRelabel_dim dk dSeed dLeak dSev dEv dPE dE dR dSpair hcard) A) *
      (Equiv.Perm.permMatrix ℂ
        (keyCopyAnnounceRelabelPerm (dk := dk) (dPE := dPE) (dE := dE) (dR := dR) μ hcard).symm)ᴴ
  map_add' := by
    intro A B
    rw [Op.castDim_add]
    simp only [mul_add, add_mul]
  map_smul' := by
    intro c A
    rw [Op.castDim_smul]
    simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]

/-- The relabelling channel is CPTP. -/
theorem keyCopyAnnounceRelabelLinear_isCPTP (dk dSeed dLeak dSev dEv dPE dE dR dSpair : ℕ)
    [NeZero ((dk * dk * (2 * dSeed)) * ((dLeak * (dSev * dEv)) * (dPE * (dE * dR))))]
    [NeZero (((dk * dk * (2 * (dSpair * dEv * dLeak * dPE))) * dE) * dR)]
    (μ : Fin dSeed × Fin dSev ≃ Fin dSpair) (hcard : dSeed * dSev = dSpair) :
    IsCPTP (⇑(keyCopyAnnounceRelabelLinear (dk := dk) (dLeak := dLeak) (dEv := dEv)
      (dPE := dPE) (dE := dE) (dR := dR) μ hcard)) := by
  have hconj := isCPTP_unitary_conjugation
    (m := ((dk * dk * (2 * (dSpair * dEv * dLeak * dPE))) * dE) * dR)
    (Equiv.Perm.permMatrix ℂ
      (keyCopyAnnounceRelabelPerm (dk := dk) (dLeak := dLeak) (dEv := dEv)
        (dPE := dPE) (dE := dE) (dR := dR) μ hcard).symm)
    (Equiv.Perm.permMatrix_conjTranspose_mul_self _)
  have hcast : IsCPTP (⇑(Op.castDimLinear
      (keyCopyAnnounceRelabel_dim dk dSeed dLeak dSev dEv dPE dE dR dSpair hcard))) :=
    castDimLinear_isCPTP _
  have hcomp := cptp_comp _ _ hconj hcast
  exact hcomp

/-! ## The announced-PE digit, transcript prefix, and agree-block τ-side states -/

/-- **The announced PE-outcome digit at a general test-set size `m`**: the sorted
parameter-estimation block `finFunctionFinEquiv (bb84PartEquiv peSel ω).2` on the
`n − bb84KeyRoundCount n m` test rounds, which is exactly the `pe` slot that
`bb84.pePassOutIndex` and `bb84.peFailOutIndex` (`SiftedPEAnnounce.lean`) write into
the transcript.

Nahar, Tupkary, Zhao, Lütkenhaus and Tan state the protocol at a free test-set size `m`
(arXiv:2403.11851, `main.tex:909`, `:913-915`); substituting `m = ⌈n/2⌉` recovers the
closed instance.  No relation between `m` and `n` is assumed: at `m = 0` the block is the unique
digit of `Fin 1` and at `m = n` it carries the whole outcome string, both honestly. -/
def bb84PEBlockIndex {n m : ℕ} (peSel : Fin n → Bool) (ω : Fin n → Fin signalDim) :
    Fin (signalDim ^ (n - bb84KeyRoundCount n m)) :=
  finFunctionFinEquiv ((bb84PartEquiv (m := m) peSel ω).2)

/-- **The pass-transcript prefix** `(flag = 0, privacy-amplification seed)`: the part of the
pass transcript that the leftover-hashing postprocess produces from its classical register.  The
remaining digits — the error-verification seed and tag, the syndrome and the announced PE block —
are carried by the conditioning register and are put in place by `keyCopyAnnounceRelabel`.

The genuine-LOCC counterpart of the referee's pass transcript, on Alice's bit-hash
seed rather than the referee joint-outcome hash seed. -/
def bb84AliceSeedPassTranscript (n ℓ : ℕ) (peSel : Fin n → Bool)
    (s : KeyHashSeed n ℓ peSel) :
    Fin (2 * Fintype.card (KeyHashSeed n ℓ peSel)) :=
  finProdFinEquiv ((⟨0, by norm_num⟩ : Fin 2),
    Fintype.equivFin (KeyHashSeed n ℓ peSel) s)

/-- **The announced seed-pair digit**, assembled from the privacy-amplification seed digit carried
    by
the leftover-hashing classical register and the error-verification seed digit carried by the
conditioning register.

`Fintype.equivFin` on a product type is not `finProdFinEquiv` of the componentwise enumerations, so
this is a genuine relabelling of the seed register and not a dimension cast. -/
def bb84SeedPairDigitEquiv (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) :
    Fin (Fintype.card (KeyHashSeed n ℓ peSel)) ×
        Fin (Fintype.card (KeyHashSeed n ℓEV peSel)) ≃
      Fin (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel)) :=
  (Equiv.prodCongr (Fintype.equivFin (KeyHashSeed n ℓ peSel)).symm
      (Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm).trans
    (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel))

/-- The seed-pair register dimension factors as the product of the two seed dimensions. -/
lemma bb84KeyHashSeedPairEV_card (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) :
    Fintype.card (KeyHashSeed n ℓ peSel) *
        Fintype.card (KeyHashSeed n ℓEV peSel) =
      Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) :=
  (Fintype.card_prod _ _).symm

/-- **The agree-and-accept filtered τ-side CQ state.**

The τ-side post-measurement CQ state filtered by the seed-free keep
predicate `bb84SiftedAgreeAcceptKeep` (`AnnounceConditioningCQ.lean`) — the fail-closed local
two-basis PE test conjoined with the agree event.  That predicate coincides with the agree
restriction of the full seed-dependent accept gate `bb84SiftedLocalPEAndEVPassed`, so this
state carries exactly the mass the agree pass channels act on; and being seed-free it is a legal
`CQState.filterKeep` predicate, which the full gate is not. -/
def bb84SiftedAgreeAcceptCQState {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    CQState (Fin n → Fin signalDim) (eveDim * dimR) :=
  haveI : NeZero (eveDim * dimR) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  CQState.filterKeep (bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q)
    (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel τ).toCQState

/-- **The leftover-hashing input state of the agree block at a general test-set size `m`.**

The announced PE-outcome block is taken on the `n − bb84KeyRoundCount n m` test rounds;
every other register is unchanged, since neither the agree-and-accept filter, the Alice-key
coarsening nor the `(syndrome, EV seed, EV tag)` kernel reads the split point. Substituting
`m = ⌈n/2⌉` recovers the closed instance.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`,
`main.tex:909`, `:913-915` (general `m`), App. B (B18). -/
def bb84PEAnnounceAgreeLHLInput {n m : ℕ} [NeZero n] [NeZero (4 ^ n)] (ℓEV : ℕ)
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    CQState (KeyBitString n peSel)
      (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
  (bb84AliceKeyAnnounceCQ peSel (bb84PEBlockIndex (m := m) peSel)
      (bb84SiftedAgreeAcceptCQState eveDim pre hpre peSel xSel ec Q δ τ)).tensorLeftKernel
    (bb84AnnounceKernel ℓEV peSel ec)

/-! ## The agree-block leftover-hashing postprocess -/

/-- Dimension identity casting away the dummy one-dimensional Eve factor of the generic key-copy
postprocess input. -/
lemma bb84PEAnnounceAgreeLHLPostprocess_input_dim_eq (n m ℓ ℓEV leakEC : ℕ)
    (peSel : Fin n → Bool) (eveDim dimR : ℕ) :
    (1 * (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR)))) *
      Fintype.card (KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ)) =
    (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) *
      Fintype.card (KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ)) := by
  ring

/-- **The agree-block leftover-hashing postprocess.**

`classicalKeyCopyPostprocess` at Alice's hash-seed classical register, followed by the output
relabelling that merges the two announced seed digits into the single transcript seed-pair digit and
puts the announced tag, syndrome and PE block in the order `bb84.pePassOutIndex` fixes.

Every stage is CPTP: two dimension casts (`castDimLinear_isCPTP`), the generic key-copy postprocess
(`classicalKeyCopyPostprocess_isCPTP`) and a basis permutation
(`keyCopyAnnounceRelabelLinear_isCPTP`).  This is the `Φ` of
`ckrTensorTraceNorm_le_two_traceDistanceGen_of_cptp_postprocess_eq`, whose `Φ` is an arbitrary
`IsCPTP` function.

Stated at the general test-set size `m`: the announced PE register is the spectator dimension `dPE`
of the relabelling and the `refDim` of the generic key-copy postprocess, so no relation between `m`
and `n` is used. -/
def bb84PEAnnounceAgreeLHLPostprocess (n m ℓ ℓEV leakEC : ℕ) (peSel : Fin n → Bool)
    (eveDim dimR : ℕ) [NeZero eveDim] [NeZero dimR] :
    Op ((2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) *
        Fintype.card (KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ))) →ₗ[ℂ]
      Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim * dimR) :=
  (keyCopyAnnounceRelabelLinear (dk := 2 ^ ℓ)
      (dPE := signalDim ^ (n - bb84KeyRoundCount n m)) (dE := eveDim) (dR := dimR)
      (bb84SeedPairDigitEquiv n ℓ ℓEV peSel)
      (bb84KeyHashSeedPairEV_card n ℓ ℓEV peSel)).comp
    ((classicalKeyCopyPostprocess
        (C := KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ))
        (2 ^ ℓ) 1
        (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
          (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR)))
        (2 * Fintype.card (KeyHashSeed n ℓ peSel))
        (fun sz => sz.2)
        (fun sz => bb84AliceSeedPassTranscript n ℓ peSel sz.1)).comp
      (Op.castDimLinear
        (bb84PEAnnounceAgreeLHLPostprocess_input_dim_eq n m ℓ ℓEV leakEC peSel eveDim
          dimR).symm))

/-- The general-`m` agree-block leftover-hashing postprocess is CPTP.

Every stage is CPTP at every `m`: two dimension casts, the generic key-copy postprocess and a
basis permutation.  No relation between `m` and `n` is used. -/
theorem bb84PEAnnounceAgreeLHLPostprocess_isCPTP (n m ℓ ℓEV leakEC : ℕ) (peSel : Fin n → Bool)
    (eveDim dimR : ℕ) [NeZero eveDim] [NeZero dimR] :
    IsCPTP (⇑(bb84PEAnnounceAgreeLHLPostprocess n m ℓ ℓEV leakEC peSel eveDim dimR)) := by
  haveI hCond : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
  haveI hCard : NeZero (Fintype.card (KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ))) :=
    ⟨Fintype.card_ne_zero⟩
  haveI hSeedCard : NeZero (Fintype.card (KeyHashSeed n ℓ peSel)) :=
    ⟨Fintype.card_ne_zero⟩
  haveI hKey : NeZero (2 ^ ℓ) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI hTr : NeZero (2 * Fintype.card (KeyHashSeed n ℓ peSel)) :=
    ⟨Nat.mul_ne_zero two_ne_zero Fintype.card_ne_zero⟩
  haveI hIn : NeZero ((2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) *
      Fintype.card (KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI hIn1 : NeZero ((1 * (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR)))) *
      Fintype.card (KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ))) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero one_ne_zero (NeZero.ne _)) (NeZero.ne _)⟩
  haveI hMid : NeZero ((2 ^ ℓ * 2 ^ ℓ * (2 * Fintype.card (KeyHashSeed n ℓ peSel))) *
      (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR)))) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)) (NeZero.ne _))
      (NeZero.ne _)⟩
  haveI hOut : NeZero (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim *
      dimR) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hcastIn : IsCPTP (⇑(Op.castDimLinear
      (bb84PEAnnounceAgreeLHLPostprocess_input_dim_eq n m ℓ ℓEV leakEC peSel eveDim dimR).symm)) :=
    castDimLinear_isCPTP _
  have hcopy : IsCPTP (⇑(classicalKeyCopyPostprocess
      (C := KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ))
      (2 ^ ℓ) 1
      (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR)))
      (2 * Fintype.card (KeyHashSeed n ℓ peSel))
      (fun sz => sz.2)
      (fun sz => bb84AliceSeedPassTranscript n ℓ peSel sz.1))) :=
    classicalKeyCopyPostprocess_isCPTP _ _ _ _ _ _
  have hrelabel := keyCopyAnnounceRelabelLinear_isCPTP (2 ^ ℓ)
    (Fintype.card (KeyHashSeed n ℓ peSel)) (2 ^ leakEC)
    (Fintype.card (KeyHashSeed n ℓEV peSel)) (2 ^ ℓEV)
    (signalDim ^ (n - bb84KeyRoundCount n m)) eveDim dimR
    (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))
    (bb84SeedPairDigitEquiv n ℓ ℓEV peSel) (bb84KeyHashSeedPairEV_card n ℓ ℓEV peSel)
  have h1 := cptp_comp _ _ hcopy hcastIn
  have h2 := cptp_comp _ _ hrelabel h1
  simpa [bb84PEAnnounceAgreeLHLPostprocess, Function.comp_apply, LinearMap.comp_apply] using h2

/-! ## Entrywise transcription tools

Local, statement-free helpers used by the two pass-output identities below: the entrywise form of
the relabelling channel, the entrywise Kraus sandwiches of the two agree-gated pass branches, the
attack-channel linchpin, and the generic key-copy block expansion at a dummy Eve factor.  The
last three restate, at the agree-gated register, declarations that are `private` upstream. -/

/-- **The relabelling channel reads its argument at the inverse-relabelled coordinates**, evaluated
on an arbitrary operator. -/
private lemma keyCopyAnnounceRelabelLinear_apply {dk dSeed dLeak dSev dEv dPE dE dR dSpair : ℕ}
    (μ : Fin dSeed × Fin dSev ≃ Fin dSpair) (hcard : dSeed * dSev = dSpair)
    (A : Op ((dk * dk * (2 * dSeed)) * ((dLeak * (dSev * dEv)) * (dPE * (dE * dR)))))
    (p q : Fin (((dk * dk * (2 * (dSpair * dEv * dLeak * dPE))) * dE) * dR)) :
    keyCopyAnnounceRelabelLinear (dk := dk) (dPE := dPE) (dE := dE) (dR := dR) μ hcard A p q =
      A ((keyCopyAnnounceRelabel (dk := dk) (dPE := dPE) (dE := dE) (dR := dR) μ).symm p)
        ((keyCopyAnnounceRelabel (dk := dk) (dPE := dPE) (dE := dE) (dR := dR) μ).symm q) := by
  classical
  have h := keyCopyAnnounceRelabel_dim dk dSeed dLeak dSev dEv dPE dE dR dSpair hcard
  rw [show keyCopyAnnounceRelabelLinear (dk := dk) (dPE := dPE) (dE := dE) (dR := dR) μ hcard A =
        Equiv.Perm.permMatrix ℂ
            (keyCopyAnnounceRelabelPerm (dk := dk) (dPE := dPE) (dE := dE) (dR := dR)
              μ hcard).symm *
          (Op.castDim h A) *
          (Equiv.Perm.permMatrix ℂ
            (keyCopyAnnounceRelabelPerm (dk := dk) (dPE := dPE) (dE := dE) (dR := dR)
              μ hcard).symm)ᴴ from rfl]
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  simp only [Matrix.submatrix_apply, id_eq, Equiv.Perm.inv_def, Equiv.symm_symm,
    Op.castDim_apply, keyCopyAnnounceRelabelPerm, Equiv.symm_trans_apply, finCongr_apply]
  rfl

/-- **The agree-gated real pass Kraus sandwich, entrywise.**

The genuine-LOCC counterpart of the referee's pass-branch Kraus sandwich, with the agree gate
folded in: on the agree block Bob's
syndrome-decoded string is Alice's, so the two hashed key slots carry the same value and the
seed-dependent accept gate collapses to the seed-free `bb84SiftedAgreeAcceptKeep`
(`bb84SiftedLocalPEAndEVPassed_eq_PETestPassed_of_not_differ`). -/
private lemma retainedSiftedPEAnnounceAgreePassBranchKraus_mul_conjTranspose_apply
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Fin n → Fin signalDim)
    (M : Op (4 ^ n * eveDim))
    (p q : Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim)) :
    ((if bb84SiftedKeyStringsDiffer peSel ec ω then 0
        else bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
          (st, ω)) * M *
      (if bb84SiftedKeyStringsDiffer peSel ec ω then 0
        else bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
          (st, ω))ᴴ) p q =
      if bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω then
        Matrix.single
          (finProdFinEquiv
            (bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC
              ((aliceKeyHashFamily n ℓ peSel).hash st.1 (aliceKeyString peSel ω))
              ((aliceKeyHashFamily n ℓ peSel).hash st.1 (aliceKeyString peSel ω))
              st (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
              (ec.syndrome (aliceKeyString peSel ω))
              (bb84PEBlockIndex (m := m) peSel ω), p.modNat))
          (finProdFinEquiv
            (bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC
              ((aliceKeyHashFamily n ℓ peSel).hash st.1 (aliceKeyString peSel ω))
              ((aliceKeyHashFamily n ℓ peSel).hash st.1 (aliceKeyString peSel ω))
              st (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
              (ec.syndrome (aliceKeyString peSel ω))
              (bb84PEBlockIndex (m := m) peSel ω), q.modNat))
          (M (finProdFinEquiv (finFunctionFinEquiv ω, p.modNat))
            (finProdFinEquiv (finFunctionFinEquiv ω, q.modNat)))
          p q
      else 0 := by
  classical
  by_cases hd : bb84SiftedKeyStringsDiffer peSel ec ω = true
  · rw [if_pos hd, if_neg (by simp [bb84SiftedAgreeAcceptKeep, hd])]
    simp
  · rw [Bool.not_eq_true] at hd
    have hstr : aliceKeyString peSel ω =
        ec.decode (bobKeyString peSel ω)
          (ec.syndrome (aliceKeyString peSel ω)) := by
      by_contra hne
      exact absurd ((bb84SiftedKeyStringsDiffer_eq_true_iff peSel ec ω).mpr hne) (by simp [hd])
    have hgate : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω =
        bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω := by
      rw [bb84SiftedLocalPEAndEVPassed_eq_PETestPassed_of_not_differ
        peSel xSel ec δ Q st.2 ω hd]
      simp [bb84SiftedAgreeAcceptKeep, hd]
    rw [if_neg (by simp [hd])]
    have hK :
        bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
            (st, ω) =
          if bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω then
            ∑ r : Fin eveDim,
              Matrix.single
                (finProdFinEquiv
                  (bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC
                    ((aliceKeyHashFamily n ℓ peSel).hash st.1
                      (aliceKeyString peSel ω))
                    ((aliceKeyHashFamily n ℓ peSel).hash st.1
                      (aliceKeyString peSel ω))
                    st (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
                    (ec.syndrome (aliceKeyString peSel ω))
                    (bb84PEBlockIndex (m := m) peSel ω), r))
                (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)
          else 0 := by
      ext a b
      by_cases h : bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω = true
      · rw [if_pos h]
        simp [bb84.retainedSiftedPEAnnouncePassBranchKraus, hgate, h, ← hstr,
          bb84PEBlockIndex, Matrix.kroneckerMap, Matrix.single_apply, Matrix.one_apply,
          finProdFinEquiv_symm_apply,
          Quantum.TensorProducts.sum_single_finProdFinEquiv_apply]
      · rw [if_neg h]
        simp [bb84.retainedSiftedPEAnnouncePassBranchKraus, hgate, h]
    rw [hK]
    by_cases h : bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω = true
    · rw [if_pos h]
      rw [matrix_single_sum_mul_mul_conjTranspose]
      simpa [h, Matrix.smul_single, smul_eq_mul] using
        finProdFinEquiv_fixed_left_sum_double_single_apply
          (bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC
            ((aliceKeyHashFamily n ℓ peSel).hash st.1
              (aliceKeyString peSel ω))
            ((aliceKeyHashFamily n ℓ peSel).hash st.1
              (aliceKeyString peSel ω))
            st (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
            (ec.syndrome (aliceKeyString peSel ω))
            (bb84PEBlockIndex (m := m) peSel ω))
          (fun r r' => M (finProdFinEquiv (finFunctionFinEquiv ω, r))
            (finProdFinEquiv (finFunctionFinEquiv ω, r'))) p q
    · simp [h]

/-- **The agree-gated ideal pass Kraus sandwich, entrywise.**

The genuine-LOCC counterpart of the referee's ideal-pass-branch Kraus sandwich.  The ideal Kraus
writes one fresh uniform key into both slots unconditionally, so the agree restriction is a pure
gate on the round outcome. -/
private lemma retainedSiftedPEAnnounceAgreeIdealPassKraus_mul_conjTranspose_apply
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] (peSel xSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (ω : Fin n → Fin signalDim) (z : Fin (2 ^ ℓ))
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel)
    (M : Op (4 ^ n * eveDim))
    (p q : Fin (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim)) :
    ((if bb84SiftedKeyStringsDiffer peSel ec ω then 0
        else bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
          (ω, z, st)) * M *
      (if bb84SiftedKeyStringsDiffer peSel ec ω then 0
        else bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
          (ω, z, st))ᴴ) p q =
      if bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω then
        Matrix.single
          (finProdFinEquiv
            (bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC z z st
              (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
              (ec.syndrome (aliceKeyString peSel ω))
              (bb84PEBlockIndex (m := m) peSel ω), p.modNat))
          (finProdFinEquiv
            (bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC z z st
              (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
              (ec.syndrome (aliceKeyString peSel ω))
              (bb84PEBlockIndex (m := m) peSel ω), q.modNat))
          (M (finProdFinEquiv (finFunctionFinEquiv ω, p.modNat))
            (finProdFinEquiv (finFunctionFinEquiv ω, q.modNat)))
          p q
      else 0 := by
  classical
  by_cases hd : bb84SiftedKeyStringsDiffer peSel ec ω = true
  · rw [if_pos hd, if_neg (by simp [bb84SiftedAgreeAcceptKeep, hd])]
    simp
  · rw [Bool.not_eq_true] at hd
    have hgate : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω =
        bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω := by
      rw [bb84SiftedLocalPEAndEVPassed_eq_PETestPassed_of_not_differ
        peSel xSel ec δ Q st.2 ω hd]
      simp [bb84SiftedAgreeAcceptKeep, hd]
    rw [if_neg (by simp [hd])]
    have hK :
        bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
            (ω, z, st) =
          if bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω then
            ∑ r : Fin eveDim,
              Matrix.single
                (finProdFinEquiv
                  (bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC z z st
                    (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
                    (ec.syndrome (aliceKeyString peSel ω))
                    (bb84PEBlockIndex (m := m) peSel ω), r))
                (finProdFinEquiv (finFunctionFinEquiv ω, r)) (1 : ℂ)
          else 0 := by
      ext a b
      by_cases h : bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω = true
      · rw [if_pos h]
        simp [bb84.retainedSiftedPEAnnounceIdealPassKraus, hgate, h, bb84PEBlockIndex,
          Matrix.kroneckerMap, Matrix.single_apply, Matrix.one_apply, finProdFinEquiv_symm_apply,
          Quantum.TensorProducts.sum_single_finProdFinEquiv_apply]
      · rw [if_neg h]
        simp [bb84.retainedSiftedPEAnnounceIdealPassKraus, hgate, h]
    rw [hK]
    by_cases h : bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω = true
    · rw [if_pos h]
      rw [matrix_single_sum_mul_mul_conjTranspose]
      simpa [h, Matrix.smul_single, smul_eq_mul] using
        finProdFinEquiv_fixed_left_sum_double_single_apply
          (bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC z z st
            (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
            (ec.syndrome (aliceKeyString peSel ω))
            (bb84PEBlockIndex (m := m) peSel ω))
          (fun r r' => M (finProdFinEquiv (finFunctionFinEquiv ω, r))
            (finProdFinEquiv (finFunctionFinEquiv ω, r'))) p q
    · simp [h]

/-- The sifted conjugation channel as an explicit unitary sandwich. -/
private lemma bb84SiftedConjChannel_apply {n eveDim : ℕ} (peSel xSel : Fin n → Bool)
    (M : Op (4 ^ n * eveDim)) :
    bb84SiftedConjChannel n eveDim peSel xSel M =
      Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim) * M *
        (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))ᴴ := by
  simp [bb84SiftedConjChannel, krausMapFintype]

/-- **Linchpin bridge.**  The `mapTensorId`-extension of the sift-after-pre channel
applied to `τ` is the sifted τ-side output density, with the LOCC sift `bb84SiftedRotation` in
place of the referee Bell rotation. -/
private lemma bb84SiftedConjAfterPre_mapTensorId_eq_siftedTauPreOutputDensity
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    mapTensorId (bb84SiftedConjAfterPre eveDim pre peSel xSel) τ.toOp =
      (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel τ).toOp := by
  rw [bb84SiftedConjAfterPre, ← mapTensorId_comp]
  rw [show mapTensorId pre τ.toOp = (bb84TauOutputDensity eveDim pre hpre τ).toOp from rfl]
  rw [bb84SiftedTauPreOutputDensity, densityOpUnitaryConj_toOp]
  ext p q
  rw [mapTensorId_apply_eq_apply_block, bb84SiftedConjChannel_apply]
  conv_rhs => rw [Op.tensor_conjTranspose, Matrix.conjTranspose_one]
  rw [tensor_sandwich_apply_eq_block
      (Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))
      ((Op.tensor (bb84SiftedRotation n peSel xSel) (1 : Op eveDim))ᴴ)
      (bb84TauOutputDensity eveDim pre hpre τ).toOp p q]
  simp only [finProdFinEquiv_symm_apply]

/-- Entry form for copied-key output blocks carrying an unguarded reference sum — the
guard-free companion of `keyCopyPostprocessOutputBlock_sum_smul_sum_ite_apply`, needed because the
conditioning register carries the announcements and the quantum marginal is therefore an
unconditioned sum over the secret. -/
private lemma keyCopyPostprocessOutputBlock_sum_smul_sum_apply
    (keyDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero refDim] [NeZero transcriptDim]
    {S Ω : Type*} [Fintype S] [Fintype Ω]
    (passTranscript : S → Fin transcriptDim) (key : S → Fin keyDim) (c : ℂ) (B : Ω → Op refDim)
    (p q : Fin ((keyDim * keyDim * transcriptDim) * refDim)) :
    (∑ s : S,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim
        (passTranscript s) (key s) (c • ∑ ω : Ω, B ω)) p q =
      ∑ s : S, c * ∑ ω : Ω,
        Matrix.single
          (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
            (transcriptDim := transcriptDim) (passTranscript s) (key s) p.modNat)
          (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
            (transcriptDim := transcriptDim) (passTranscript s) (key s) q.modNat)
          (B ω p.modNat q.modNat) p q := by
  classical
  have h : (∑ ω : Ω, B ω) = ∑ ω : Ω, if (True : Prop) then B ω else 0 := by simp
  rw [h, keyCopyPostprocessOutputBlock_sum_smul_sum_ite_apply keyDim refDim transcriptDim
    passTranscript key c (fun _ => True) B p q]
  simp

/-- Collapse a fiber sum against a factor depending only on the fiber label. -/
private lemma sum_mul_fiber_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (g : β → α) (F : α → ℂ) (G : β → ℂ) :
    (∑ x : α, F x * ∑ ω : β, (if g ω = x then G ω else 0)) = ∑ ω : β, F (g ω) * G ω := by
  classical
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- Split a guarded product into a guarded factor times the unguarded one. -/
private lemma ite_mul_right_zero {P : Prop} [Decidable P] (a b : ℂ) :
    (if P then a * b else 0) = (if P then a else 0) * b := by
  split_ifs <;> simp

/-- A guard is an indicator factor. -/
private lemma ite_one_mul_eq {P : Prop} [Decidable P] (c : ℂ) :
    (if P then c else 0) = (if P then (1 : ℂ) else 0) * c := by
  split_ifs <;> simp

/-- A conjunctive guard factors into indicator times guard. -/
private lemma ite_and_mul {P R : Prop} [Decidable P] [Decidable R] (c : ℂ) :
    (if P ∧ R then c else 0) = (if P then (1 : ℂ) else 0) * (if R then c else 0) := by
  by_cases hP : P <;> by_cases hR : R <;> simp [hP, hR]

/-- Entrywise form of a standard-basis announcement projector. -/
private lemma stdProj_toOp_apply (d : ℕ) (i a b : Fin d) :
    (stdProj d i).toOp a b = (if i = a then (1 : ℂ) else 0) * (if i = b then (1 : ℂ) else 0) := by
  simp [stdProj_toOp, ket_mul_bra_apply, Ket.dag_vec, apply_ite (starRingEnd ℂ)]

/-- **Entrywise form of the announce kernel.**  The syndrome projector pins both the row and the
column syndrome digit; the uniformly seeded `(seed, tag)` graph projector is diagonal in the seed
digit and pins each tag digit to the tag of its own seed. -/
private lemma bb84AnnounceKernel_toOp_apply {n leakEC : ℕ} (ℓEV : ℕ) (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (x : KeyBitString n peSel)
    (pSyn qSyn : Fin (2 ^ leakEC))
    (pT qT : Fin (Fintype.card (KeyHashSeed n ℓEV peSel)))
    (pEv qEv : Fin (2 ^ ℓEV)) :
    (bb84AnnounceKernel ℓEV peSel ec x).toOp
        (finProdFinEquiv (pSyn, finProdFinEquiv (pT, pEv)))
        (finProdFinEquiv (qSyn, finProdFinEquiv (qT, qEv))) =
      (if ec.syndrome x = pSyn then (1 : ℂ) else 0) *
        (if ec.syndrome x = qSyn then (1 : ℂ) else 0) *
        (((1 / (Fintype.card (KeyHashSeed n ℓEV peSel) : ℝ) : ℝ) : ℂ) *
          ((if pT = qT then (1 : ℂ) else 0) *
            ((if verificationTag n ℓEV peSel
                ((Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm pT) x = pEv then
                  (1 : ℂ) else 0) *
              (if verificationTag n ℓEV peSel
                ((Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm qT) x = qEv then
                  (1 : ℂ) else 0)))) := by
  classical
  rw [bb84AnnounceKernel,
    show ((stdProj (2 ^ leakEC) (ec.syndrome x)).tensor
        (uniformSeededAnnounce fun j =>
          verificationTag n ℓEV peSel
            ((Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm j) x)).toOp =
      Op.tensor (stdProj (2 ^ leakEC) (ec.syndrome x)).toOp
        (uniformSeededAnnounce fun j =>
          verificationTag n ℓEV peSel
            ((Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm j) x).toOp from rfl,
    Op_tensor_apply_finProd]
  simp only [Equiv.symm_apply_apply, stdProj_toOp_apply, uniformSeededAnnounce_toOp,
    Matrix.smul_apply, smul_eq_mul, seedGraphProj_eq_diagonal, Matrix.diagonal_apply,
    one_div]
  simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
    Complex.ofReal_inv, Complex.ofReal_natCast]
  by_cases hT : pT = qT
  · subst hT
    by_cases hE : pEv = qEv
    · subst hE
      by_cases hg : verificationTag n ℓEV peSel
          ((Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm pT) x = pEv
      · subst hg; simp [mul_comm]
      · have hg' : ¬ (pEv = verificationTag n ℓEV peSel
            ((Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm pT) x) := fun h => hg h.symm
        simp [hg, hg']
    · have h1 : ¬ (verificationTag n ℓEV peSel
          ((Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm pT) x = pEv ∧
        verificationTag n ℓEV peSel
          ((Fintype.equivFin (KeyHashSeed n ℓEV peSel)).symm pT) x = qEv) := by
        rintro ⟨rfl, h⟩; exact hE h
      simp only [hE, and_false, if_false, mul_zero]
      rcases not_and_or.mp h1 with h | h <;> simp [h]
  · simp [hT]

/-- **Entrywise form of the agree-block leftover-hashing input state.**  The announce kernel
factors off the high digits, and the Alice-key coarsening contributes the fiber sum of
PE-block-tagged τ-side blocks. -/
private lemma bb84PEAnnounceAgreeLHLInput_stateMap_apply
    {n m : ℕ} [NeZero n] [NeZero (4 ^ n)] (ℓEV : ℕ)
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR] (τ : DensityOp ((signalDim ^ n) * dimR))
    (x : KeyBitString n peSel)
    (a1 b1 : Fin (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV)))
    (a2 b2 : Fin (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :
    ((bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ).stateMap x).toOp
        (finProdFinEquiv (a1, a2)) (finProdFinEquiv (b1, b2)) =
      (bb84AnnounceKernel ℓEV peSel ec x).toOp a1 b1 *
        ∑ ω : Fin n → Fin signalDim,
          (if aliceKeyString peSel ω = x then
            (Op.tensor (stdProj (signalDim ^ (n - bb84KeyRoundCount n m))
                (bb84PEBlockIndex (m := m) peSel ω)).toOp
              ((bb84SiftedAgreeAcceptCQState eveDim pre hpre peSel xSel ec Q δ τ).stateMap ω).toOp)
                  a2 b2
          else 0) := by
  classical
  rw [bb84PEAnnounceAgreeLHLInput, CQState.tensorLeftKernel_stateMap,
    show ((bb84AnnounceKernel ℓEV peSel ec x).tensor
        ((bb84AliceKeyAnnounceCQ peSel (bb84PEBlockIndex (m := m) peSel)
          (bb84SiftedAgreeAcceptCQState eveDim pre hpre peSel xSel ec Q δ τ)).stateMap x)).toOp =
      Op.tensor (bb84AnnounceKernel ℓEV peSel ec x).toOp
        ((bb84AliceKeyAnnounceCQ peSel (bb84PEBlockIndex (m := m) peSel)
          (bb84SiftedAgreeAcceptCQState eveDim pre hpre peSel xSel ec Q δ τ)).stateMap x).toOp from
              rfl,
    Op_tensor_apply_finProd]
  simp only [Equiv.symm_apply_apply]
  congr 1
  rw [bb84AliceKeyAnnounceCQ, bb84AnnounceCoarsenCQ_stateMap, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs <;> rfl

/-- **Entrywise form of the agree-and-accept filtered τ-side CQ block**, identified through the
attack-channel linchpin with the measured, attacked `τ` at the outcome-conditioned indices — the
payload the pass Kraus sandwich reads. -/
private lemma bb84SiftedAgreeAcceptCQState_stateMap_apply
    {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR] (τ : DensityOp ((signalDim ^ n) * dimR))
    (ω : Fin n → Fin signalDim) (pE qE : Fin eveDim) (pR qR : Fin dimR) :
    ((bb84SiftedAgreeAcceptCQState eveDim pre hpre peSel xSel ec Q δ τ).stateMap ω).toOp
        (finProdFinEquiv (pE, pR)) (finProdFinEquiv (qE, qR)) =
      if bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω then
        mapTensorId (measurementChannel n eveDim)
          (mapTensorId (bb84SiftedConjAfterPre eveDim pre peSel xSel) τ.toOp)
          (finProdFinEquiv (finProdFinEquiv (finFunctionFinEquiv ω, pE), pR))
          (finProdFinEquiv (finProdFinEquiv (finFunctionFinEquiv ω, qE), qR))
      else 0 := by
  classical
  rw [bb84SiftedAgreeAcceptCQState, CQState.filterKeep_stateMap]
  by_cases h : bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω = true
  · rw [if_pos h, if_pos h]
    rw [show ((bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
        τ).toCQState.stateMap
          ω).toOp =
        (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel τ).toOp.submatrix
          (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR)
            (bb84OutcomeIndex ω))
          (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim) (dimR := dimR)
            (bb84OutcomeIndex ω)) from rfl]
    rw [Matrix.submatrix_apply, bb84TauOutcomeEveRefEmbedding_finProd,
      bb84TauOutcomeEveRefEmbedding_finProd, bb84OutcomeIndex_eq_finFunctionFinEquiv,
      ← bb84SiftedConjAfterPre_mapTensorId_eq_siftedTauPreOutputDensity eveDim pre hpre peSel xSel
          τ]
    symm
    rw [mapTensorId_apply_eq_apply_block]
    simp only [Equiv.symm_apply_apply]
    rw [measurementChannel_apply]
    simp [finProdFinEquiv_apply_divNat, bb84OutcomeEveEmbedding]
  · rw [if_neg h, if_neg h]
    rfl

/-- **Digitwise equality test for the pass output index.**  The transcript packing is a
composite of `finProdFinEquiv`s, hence injective, so an index equation is the conjunction of its
seven digit equations. -/
private lemma bb84_pePassOutIndex_eq_split_iff {n m ℓ ℓEV leakEC : ℕ}
    (peSel : Fin n → Bool)
    (kA kB : Fin (2 ^ ℓ)) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ev : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC)) (pe : Fin (signalDim ^ (n - bb84KeyRoundCount n m)))
    (pkA pkB : Fin (2 ^ ℓ)) (pFl : Fin 2)
    (pStp : Fin (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) (pEv : Fin (2 ^ ℓEV))
    (pSyn : Fin (2 ^ leakEC)) (pPE : Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :
    bb84.pePassOutIndex n m ℓ ℓEV peSel leakEC kA kB st ev syn pe =
        finProdFinEquiv (finProdFinEquiv (pkA, pkB),
          finProdFinEquiv (pFl,
            finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (pStp, pEv), pSyn), pPE))) ↔
      (kA = pkA ∧ kB = pkB ∧ (⟨0, by norm_num⟩ : Fin 2) = pFl ∧
        Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel) st = pStp ∧
        ev = pEv ∧ syn = pSyn ∧ pe = pPE) := by
  rw [bb84.pePassOutIndex]
  simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  tauto

/-- **Digitwise equality test for the key-copy output index at the transcript prefix.**  Companion
of `bb84_pePassOutIndex_eq_split_iff` on the source side of the relabelling. -/
private lemma bb84_keyCopyOutputIndex_eq_split_iff {n ℓ dRef : ℕ} (peSel : Fin n → Bool)
    (s : KeyHashSeed n ℓ peSel) (z : Fin (2 ^ ℓ)) (ann : Fin dRef)
    (pkA pkB : Fin (2 ^ ℓ)) (pFl : Fin 2)
    (ps : Fin (Fintype.card (KeyHashSeed n ℓ peSel))) (pann : Fin dRef) :
    keyCopyPostprocessOutputIndex (keyDim := 2 ^ ℓ) (refDim := dRef)
        (bb84AliceSeedPassTranscript n ℓ peSel s) z ann =
        finProdFinEquiv
          (finProdFinEquiv (finProdFinEquiv (pkA, pkB), finProdFinEquiv (pFl, ps)), pann) ↔
      (z = pkA ∧ z = pkB ∧ (⟨0, by norm_num⟩ : Fin 2) = pFl ∧
        Fintype.equivFin (KeyHashSeed n ℓ peSel) s = ps ∧ ann = pann) := by
  rw [keyCopyPostprocessOutputIndex, bb84AliceSeedPassTranscript]
  simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  tauto

/-- The inverse seed-pair relabelling splits a seed-pair digit into the two enumerated halves of the
seed pair it names. -/
private lemma bb84SeedPairDigitEquiv_symm_apply (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (stp : Fin (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) :
    (bb84SeedPairDigitEquiv n ℓ ℓEV peSel).symm stp =
      (Fintype.equivFin (KeyHashSeed n ℓ peSel)
          ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm stp).1,
        Fintype.equivFin (KeyHashSeed n ℓEV peSel)
          ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm stp).2) := by
  simp [bb84SeedPairDigitEquiv, Prod.map]

/-- **The inverse relabelling on a fully split target index.**  It splits the seed-pair digit
back into the hash-seed digit of the transcript prefix and the announced error-verification seed
digit of the conditioning register, and moves the syndrome digit back above the tag digit. -/
private lemma keyCopyAnnounceRelabel_symm_finProd
    {dk dSeed dLeak dSev dEv dPE dE dR dSpair : ℕ}
    (μ : Fin dSeed × Fin dSev ≃ Fin dSpair)
    (kA kB : Fin dk) (fl : Fin 2) (stp : Fin dSpair) (ev : Fin dEv) (syn : Fin dLeak)
    (pe : Fin dPE) (e : Fin dE) (r : Fin dR) :
    (keyCopyAnnounceRelabel (dk := dk) (dPE := dPE) (dE := dE) (dR := dR) μ).symm
        (finProdFinEquiv
          (finProdFinEquiv
            (finProdFinEquiv (finProdFinEquiv (kA, kB),
              finProdFinEquiv (fl,
                finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (stp, ev), syn), pe))), e), r)) =
      finProdFinEquiv
        (finProdFinEquiv (finProdFinEquiv (kA, kB), finProdFinEquiv (fl, (μ.symm stp).1)),
          finProdFinEquiv (finProdFinEquiv (syn, finProdFinEquiv ((μ.symm stp).2, ev)),
            finProdFinEquiv (pe, finProdFinEquiv (e, r)))) := by
  rw [show finProdFinEquiv
        (finProdFinEquiv
          (finProdFinEquiv (finProdFinEquiv (kA, kB),
            finProdFinEquiv (fl,
              finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (stp, ev), syn), pe))), e), r) =
      keyCopyAnnounceTgtPack dk dSpair dEv dLeak dPE dE dR
        ((((kA, kB), (fl, (((stp, ev), syn), pe))), e), r) from rfl,
    keyCopyAnnounceRelabel]
  simp only [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rfl

/-- **Key-copy postprocessing of a CQ joint density at a dummy one-dimensional Eve factor.**

The reference register is the whole conditioning register, so the input cast pads the trivial Eve
factor the generic channel expects. -/
private lemma classicalKeyCopyPostprocess_castOne_toJointDensity_eq_sum_outputBlocks
    {C : Type*} [Fintype C] [DecidableEq C]
    (keyDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero refDim] [NeZero transcriptDim]
    (key : C → Fin keyDim) (transcript : C → Fin transcriptDim)
    (hdim : refDim * Fintype.card C = (1 * refDim) * Fintype.card C)
    (ρ : CQState C refDim) :
    classicalKeyCopyPostprocess keyDim 1 refDim transcriptDim key transcript
        (Op.castDimLinear hdim ρ.toJointDensity.toOp) =
      ∑ c : C,
        keyCopyPostprocessOutputBlock keyDim refDim transcriptDim
          (transcript c) (key c) ((ρ.stateMap c).toOp) := by
  classical
  let ρ' : CQState C (1 * refDim) := cqStateCastOneLeft refDim ρ
  have hjoint : Op.castDimLinear hdim ρ.toJointDensity.toOp = ρ'.toJointDensity.toOp :=
    cqState_toJointDensity_castDim_toOp (Nat.one_mul refDim).symm ρ ρ' (by intro x; rfl)
  rw [hjoint, classicalKeyCopyPostprocess_toJointDensity_eq_sum_outputBlocks]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  dsimp [ρ', cqStateCastOneLeft]
  rw [InfoTheory.SmoothMinEntropy.SubDensityOp.castDim_toOp]
  exact partialTraceA_cast_one_mul_eq refDim ((ρ.stateMap c).toOp)

/-! ## The two agree-block pass-output identities

The genuine-LOCC counterparts of the referee's real/ideal-pass identities, with the agree gate on
the Kraus family and the announcements in the conditioning register.

The channels are written out as the explicit Kraus composites rather than through the named
`bb84SiftedPEAnnounceEveVisible{Real,Ideal}AgreePassChannel`, which live downstream in
the referee construction; the two expressions are definitionally
equal, so the consumer discharges the difference by unfolding its own definitions. -/

/-- **Real agree pass output as the relabelling of the key-copy output blocks.**  The block-algebra
half of the real identity below, with the announce-carrying relabelling in place of a plain output
dimension cast. -/
private lemma bb84SiftedPEAnnounceEveVisible_realAgreePass_eq_relabel_sum_blocks
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    mapTensorId
        (((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
          krausMapFintype (fun k =>
            if bb84SiftedKeyStringsDiffer peSel ec k.2 then 0
            else bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim
              peSel xSel leakEC ec δ Q k)).comp
          ((measurementChannel n eveDim).comp
            (bb84SiftedConjAfterPre eveDim pre peSel xSel)))
        τ.toOp =
      keyCopyAnnounceRelabelLinear (dk := 2 ^ ℓ)
        (dPE := signalDim ^ (n - bb84KeyRoundCount n m)) (dE := eveDim) (dR := dimR)
        (bb84SeedPairDigitEquiv n ℓ ℓEV peSel) (bb84KeyHashSeedPairEV_card n ℓ ℓEV peSel)
        (∑ sz : KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ),
          keyCopyPostprocessOutputBlock (2 ^ ℓ)
            (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
              (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR)))
            (2 * Fintype.card (KeyHashSeed n ℓ peSel))
            (bb84AliceSeedPassTranscript n ℓ peSel sz.1) sz.2
            ((seedKeyExtractorOutputState (aliceKeyHashFamily n ℓ peSel)
              (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
                  τ)).stateMap sz).toOp) := by
  classical
  haveI hCond : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
  haveI hKey : NeZero (2 ^ ℓ) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI hTr : NeZero (2 * Fintype.card (KeyHashSeed n ℓ peSel)) :=
    ⟨Nat.mul_ne_zero two_ne_zero Fintype.card_ne_zero⟩
  rw [← mapTensorId_comp, ← mapTensorId_comp]
  ext p q
  rw [mapTensorId_apply_eq_apply_block, keyCopyAnnounceRelabelLinear_apply]
  simp only [seedKeyExtractorOutputState, seedPerSeedConditionedOp, seedPerSeedWeightedOp]
  rw [keyCopyPostprocessOutputBlock_sum_hash_smul_sum_ite_apply
    (keyDim := 2 ^ ℓ)
    (refDim := 2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR)))
    (transcriptDim := 2 * Fintype.card (KeyHashSeed n ℓ peSel))
    (S := KeyHashSeed n ℓ peSel) (Ω := KeyBitString n peSel)
    (fun s => bb84AliceSeedPassTranscript n ℓ peSel s)
    (fun s x => (aliceKeyHashFamily n ℓ peSel).hash s x)
    ((1 : ℝ) / (Fintype.card (KeyHashSeed n ℓ peSel) : ℝ))
    (fun _s x =>
        ((bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ).stateMap
        x).toOp)]
  simp only [one_div, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
    krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [retainedSiftedPEAnnounceAgreePassBranchKraus_mul_conjTranspose_apply]
  simp_rw [Finset.mul_sum]
  obtain ⟨⟨pBE, pR⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨pB, pE⟩, rfl⟩ := finProdFinEquiv.surjective pBE
  obtain ⟨⟨pKK, pRest⟩, rfl⟩ := finProdFinEquiv.surjective pB
  obtain ⟨⟨pkA, pkB⟩, rfl⟩ := finProdFinEquiv.surjective pKK
  obtain ⟨⟨pFl, pInner⟩, rfl⟩ := finProdFinEquiv.surjective pRest
  obtain ⟨⟨pSev, pPE⟩, rfl⟩ := finProdFinEquiv.surjective pInner
  obtain ⟨⟨pSevT, pSyn⟩, rfl⟩ := finProdFinEquiv.surjective pSev
  obtain ⟨⟨pStp, pEv⟩, rfl⟩ := finProdFinEquiv.surjective pSevT
  obtain ⟨⟨qBE, qR⟩, rfl⟩ := finProdFinEquiv.surjective q
  obtain ⟨⟨qB, qE⟩, rfl⟩ := finProdFinEquiv.surjective qBE
  obtain ⟨⟨qKK, qRest⟩, rfl⟩ := finProdFinEquiv.surjective qB
  obtain ⟨⟨qkA, qkB⟩, rfl⟩ := finProdFinEquiv.surjective qKK
  obtain ⟨⟨qFl, qInner⟩, rfl⟩ := finProdFinEquiv.surjective qRest
  obtain ⟨⟨qSev, qPE⟩, rfl⟩ := finProdFinEquiv.surjective qInner
  obtain ⟨⟨qSevT, qSyn⟩, rfl⟩ := finProdFinEquiv.surjective qSev
  obtain ⟨⟨qStp, qEv⟩, rfl⟩ := finProdFinEquiv.surjective qSevT
  simp only [keyCopyAnnounceRelabel_symm_finProd, bb84SeedPairDigitEquiv_symm_apply,
    Equiv.symm_apply_apply, finProdFinEquiv_apply_modNat]
  by_cases hStp : pStp = qStp
  · subst hStp
    refine Eq.trans (Finset.sum_eq_single
        ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp) ?hLzero
        (fun h => absurd (Finset.mem_univ _) h)) ?hmain
    case hLzero =>
      intro st _ hst
      refine Finset.sum_eq_zero fun ω _ => ?_
      refine mul_eq_zero_of_right _ ?_
      split_ifs with hg
      · rw [Matrix.single_apply, if_neg]
        rintro ⟨h1, -⟩
        refine hst ((Equiv.eq_symm_apply _).mpr ?_)
        exact ((bb84_pePassOutIndex_eq_split_iff peSel _ _ st _ _ _
          pkA pkB pFl pStp pEv pSyn pPE).mp
            (congrArg Prod.fst (finProdFinEquiv.injective h1))).2.2.2.1
      · rfl
    case hmain =>
      refine Eq.trans ?main (Finset.sum_eq_single
        (((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp).1) ?hRzero
        (fun h => absurd (Finset.mem_univ _) h)).symm
      case hRzero =>
        intro s _ hs
        refine Finset.sum_eq_zero fun x _ => ?_
        refine mul_eq_zero_of_right _ ?_
        rw [Matrix.single_apply, if_neg]
        rintro ⟨h1, -⟩
        exact hs (Equiv.injective _
          ((bb84_keyCopyOutputIndex_eq_split_iff peSel s _ _ pkA pkB pFl _ _).mp h1).2.2.2.1)
      case main =>
        -- read off the entries of the matrix unit, then the state-map entries
        dsimp only [Matrix.single_apply]
        simp_rw [bb84PEAnnounceAgreeLHLInput_stateMap_apply, ite_mul_right_zero, ← mul_assoc]
        rw [sum_mul_fiber_sum]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Op_tensor_apply_finProd]
        simp only [Equiv.symm_apply_apply, stdProj_toOp_apply,
          bb84SiftedAgreeAcceptCQState_stateMap_apply, bb84AnnounceKernel_toOp_apply,
          Matrix.of_apply]
        by_cases hagree : bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω = true
        · rw [if_pos hagree, if_pos hagree]
          rw [ite_one_mul_eq, ite_one_mul_eq]
          simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, and_true,
            bb84_pePassOutIndex_eq_split_iff, bb84_keyCopyOutputIndex_eq_split_iff,
            Equiv.apply_symm_apply, ite_and_mul, if_true, and_self, one_mul, mul_one]
          rw [show ((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ))⁻¹ =
              ((Fintype.card (KeyHashSeed n ℓ peSel) : ℂ))⁻¹ *
                ((Fintype.card (KeyHashSeed n ℓEV peSel) : ℂ))⁻¹ from by
            rw [← bb84KeyHashSeedPairEV_card n ℓ ℓEV peSel, Nat.cast_mul, mul_inv]]
          push_cast
          by_cases hqFl : (0 : Fin 2) = qFl
          · simp only [if_pos hqFl]
            ring
          · simp only [if_neg hqFl]
            ring
        · rw [if_neg hagree, if_neg hagree]
          ring
  · refine Eq.trans (Finset.sum_eq_zero fun st _ => Finset.sum_eq_zero fun ω _ => ?_)
      (Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun x _ => ?_).symm
    · refine mul_eq_zero_of_right _ ?_
      split_ifs with hg
      · rw [Matrix.single_apply, if_neg]
        rintro ⟨h1, h2⟩
        refine hStp ?_
        have e1 := ((bb84_pePassOutIndex_eq_split_iff peSel _ _ st _ _ _
          pkA pkB pFl pStp pEv pSyn pPE).mp
            (congrArg Prod.fst (finProdFinEquiv.injective h1))).2.2.2.1
        have e2 := ((bb84_pePassOutIndex_eq_split_iff peSel _ _ st _ _ _
          qkA qkB qFl qStp qEv qSyn qPE).mp
            (congrArg Prod.fst (finProdFinEquiv.injective h2))).2.2.2.1
        exact e1.symm.trans e2
      · rfl
    · refine mul_eq_zero_of_right _ ?_
      rw [Matrix.single_apply]
      split_ifs with hc
      · obtain ⟨h1, h2⟩ := hc
        have e1 := ((bb84_keyCopyOutputIndex_eq_split_iff peSel s _ _
          pkA pkB pFl _ _).mp h1).2.2.2.1
        have e2 := ((bb84_keyCopyOutputIndex_eq_split_iff peSel s _ _
          qkA qkB qFl _ _).mp h2).2.2.2.1
        have hS : ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp).1 =
            ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm qStp).1 :=
          Equiv.injective _ (e1.symm.trans e2)
        rw [bb84PEAnnounceAgreeLHLInput_stateMap_apply, bb84AnnounceKernel_toOp_apply]
        have hT : ¬ (Fintype.equivFin (KeyHashSeed n ℓEV peSel)
            ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp).2 =
          Fintype.equivFin (KeyHashSeed n ℓEV peSel)
            ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm qStp).2) := by
          intro hT
          refine hStp ?_
          have := Equiv.injective (Fintype.equivFin (KeyHashSeed n ℓEV peSel)) hT
          have hpair : (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp =
              (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm qStp :=
            Prod.ext hS this
          exact (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm.injective hpair
        -- The seed-tag indicator factor vanishes.
        simp only [if_neg hT, zero_mul, mul_zero]
      · rfl

/-- **Real agree pass output as the leftover-hashing postprocess of the seed-key extractor output.**

The `mapTensorId` extension of the agree-restricted real pass channel, applied to a CKR
purification `τ`, equals the agree-block leftover-hashing postprocess applied to the joint density
of the Alice-bit seed-key extractor output on `bb84PEAnnounceAgreeLHLInput`.

On the agree block Bob's syndrome-decoded string equals Alice's, so the two hashed key slots of
`bb84.pePassOutIndex` carry the same value and identify the pass index with a
`keyCopyPostprocessOutputIndex`; the announced digits are supplied by the conditioning register of
`bb84PEAnnounceAgreeLHLInput` and put in place by the relabelling.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024),
`arXiv:2403.11851`, App. B (B18), stated at the paper's free test-set size `m`
(`main.tex:909`, `:913-915`).  No relation between `m` and `n` is
used. -/
theorem realAgreePass_mapTensorId_eq_lhlPostprocess_seedKeyOutput
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    mapTensorId
        (((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
          krausMapFintype (fun k =>
            if bb84SiftedKeyStringsDiffer peSel ec k.2 then 0
            else bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim
              peSel xSel leakEC ec δ Q k)).comp
          ((measurementChannel n eveDim).comp
            (bb84SiftedConjAfterPre eveDim pre peSel xSel)))
        τ.toOp =
      ⇑(bb84PEAnnounceAgreeLHLPostprocess n m ℓ ℓEV leakEC peSel eveDim dimR)
        (seedKeyExtractorOutputState (aliceKeyHashFamily n ℓ peSel)
          (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
              τ)).toJointDensity.toOp := by
  haveI hCond : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
  haveI hKey : NeZero (2 ^ ℓ) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI hTr : NeZero (2 * Fintype.card (KeyHashSeed n ℓ peSel)) :=
    ⟨Nat.mul_ne_zero two_ne_zero Fintype.card_ne_zero⟩
  rw [bb84SiftedPEAnnounceEveVisible_realAgreePass_eq_relabel_sum_blocks]
  · simp only [bb84PEAnnounceAgreeLHLPostprocess, LinearMap.comp_apply]
    congr 1
    exact (classicalKeyCopyPostprocess_castOne_toJointDensity_eq_sum_outputBlocks
      (C := KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ)) (2 ^ ℓ) _
      (2 * Fintype.card (KeyHashSeed n ℓ peSel)) (fun sz => sz.2)
      (fun sz => bb84AliceSeedPassTranscript n ℓ peSel sz.1)
      (bb84PEAnnounceAgreeLHLPostprocess_input_dim_eq n m ℓ ℓEV leakEC peSel
        eveDim dimR).symm
      (seedKeyExtractorOutputState (aliceKeyHashFamily n ℓ peSel)
        (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ))).symm

/-- **Ideal agree pass output as the relabelling of the key-copy output blocks.**  The
block-algebra half of the ideal identity below. -/
private lemma bb84SiftedPEAnnounceEveVisible_idealAgreePass_eq_relabel_sum_blocks
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    haveI : Nonempty (KeyHashSeed n ℓ peSel) :=
      (aliceKeyHashFamily n ℓ peSel).seedNonempty
    mapTensorId
        (((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
          krausMapFintype (fun k =>
            if bb84SiftedKeyStringsDiffer peSel ec k.1 then 0
            else bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim
              peSel xSel leakEC ec δ Q k)).comp
          ((measurementChannel n eveDim).comp
            (bb84SiftedConjAfterPre eveDim pre peSel xSel)))
        τ.toOp =
      keyCopyAnnounceRelabelLinear (dk := 2 ^ ℓ)
        (dPE := signalDim ^ (n - bb84KeyRoundCount n m)) (dE := eveDim) (dR := dimR)
        (bb84SeedPairDigitEquiv n ℓ ℓEV peSel) (bb84KeyHashSeedPairEV_card n ℓ ℓEV peSel)
        (∑ sz : KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ),
          keyCopyPostprocessOutputBlock (2 ^ ℓ)
            (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
              (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR)))
            (2 * Fintype.card (KeyHashSeed n ℓ peSel))
            (bb84AliceSeedPassTranscript n ℓ peSel sz.1) sz.2
            ((seedUniformOutputState (S := KeyHashSeed n ℓ peSel)
              (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
                τ).quantumMarginal).stateMap sz).toOp) := by
  classical
  haveI hSeedNE : Nonempty (KeyHashSeed n ℓ peSel) :=
    (aliceKeyHashFamily n ℓ peSel).seedNonempty
  haveI hCond : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
  haveI hKey : NeZero (2 ^ ℓ) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI hTr : NeZero (2 * Fintype.card (KeyHashSeed n ℓ peSel)) :=
    ⟨Nat.mul_ne_zero two_ne_zero Fintype.card_ne_zero⟩
  rw [← mapTensorId_comp, ← mapTensorId_comp]
  ext p q
  rw [mapTensorId_apply_eq_apply_block, keyCopyAnnounceRelabelLinear_apply]
  simp_rw [seedUniformOutputState_fin_stateMap_toOp]
  rw [show (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
      τ).quantumMarginal.toOp =
      ∑ x : KeyBitString n peSel,
        ((bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ).stateMap
            x).toOp from rfl]
  rw [keyCopyPostprocessOutputBlock_sum_smul_sum_apply (2 ^ ℓ) _
    (2 * Fintype.card (KeyHashSeed n ℓ peSel))
    (fun sz : KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ) =>
      bb84AliceSeedPassTranscript n ℓ peSel sz.1)
    (fun sz : KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ) => sz.2) _
    (fun x : KeyBitString n peSel =>
      ((bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ τ).stateMap
          x).toOp)]
  rw [Fintype.sum_prod_type]
  simp only [one_div, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
    krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [retainedSiftedPEAnnounceAgreeIdealPassKraus_mul_conjTranspose_apply]
  simp_rw [Finset.mul_sum]
  rw [fintype_sum_three_reverse]
  obtain ⟨⟨pBE, pR⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨pB, pE⟩, rfl⟩ := finProdFinEquiv.surjective pBE
  obtain ⟨⟨pKK, pRest⟩, rfl⟩ := finProdFinEquiv.surjective pB
  obtain ⟨⟨pkA, pkB⟩, rfl⟩ := finProdFinEquiv.surjective pKK
  obtain ⟨⟨pFl, pInner⟩, rfl⟩ := finProdFinEquiv.surjective pRest
  obtain ⟨⟨pSev, pPE⟩, rfl⟩ := finProdFinEquiv.surjective pInner
  obtain ⟨⟨pSevT, pSyn⟩, rfl⟩ := finProdFinEquiv.surjective pSev
  obtain ⟨⟨pStp, pEv⟩, rfl⟩ := finProdFinEquiv.surjective pSevT
  obtain ⟨⟨qBE, qR⟩, rfl⟩ := finProdFinEquiv.surjective q
  obtain ⟨⟨qB, qE⟩, rfl⟩ := finProdFinEquiv.surjective qBE
  obtain ⟨⟨qKK, qRest⟩, rfl⟩ := finProdFinEquiv.surjective qB
  obtain ⟨⟨qkA, qkB⟩, rfl⟩ := finProdFinEquiv.surjective qKK
  obtain ⟨⟨qFl, qInner⟩, rfl⟩ := finProdFinEquiv.surjective qRest
  obtain ⟨⟨qSev, qPE⟩, rfl⟩ := finProdFinEquiv.surjective qInner
  obtain ⟨⟨qSevT, qSyn⟩, rfl⟩ := finProdFinEquiv.surjective qSev
  obtain ⟨⟨qStp, qEv⟩, rfl⟩ := finProdFinEquiv.surjective qSevT
  simp only [keyCopyAnnounceRelabel_symm_finProd, bb84SeedPairDigitEquiv_symm_apply,
    Equiv.symm_apply_apply, finProdFinEquiv_apply_modNat]
  by_cases hStp : pStp = qStp
  · subst hStp
    refine Eq.trans (Finset.sum_eq_single
        (((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp).1) ?hLzeroS
        (fun h => absurd (Finset.mem_univ _) h)) ?hmain1
    case hLzeroS =>
      intro s _ hs
      refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun ω _ =>
        Finset.sum_eq_zero fun t _ => ?_
      refine mul_eq_zero_of_right _ ?_
      split_ifs with hg
      · rw [Matrix.single_apply, if_neg]
        rintro ⟨h1, -⟩
        refine hs ?_
        have := ((bb84_pePassOutIndex_eq_split_iff peSel _ _ (s, t) _ _ _
          pkA pkB pFl pStp pEv pSyn pPE).mp
            (congrArg Prod.fst (finProdFinEquiv.injective h1))).2.2.2.1
        exact congrArg Prod.fst ((Equiv.eq_symm_apply _).mpr this)
      · rfl
    case hmain1 =>
      refine Eq.trans ?main2 (Finset.sum_eq_single
        (((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp).1) ?hRzeroS
        (fun h => absurd (Finset.mem_univ _) h)).symm
      case hRzeroS =>
        intro s _ hs
        refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun x _ => ?_
        refine mul_eq_zero_of_right _ ?_
        rw [Matrix.single_apply, if_neg]
        rintro ⟨h1, -⟩
        exact hs (Equiv.injective _
          ((bb84_keyCopyOutputIndex_eq_split_iff peSel s _ _ pkA pkB pFl _ _).mp h1).2.2.2.1)
      case main2 =>
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_comm]
        refine Eq.trans (Finset.sum_eq_single
          (((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp).2) ?hLzeroT
          (fun h => absurd (Finset.mem_univ _) h)) ?main3
        case hLzeroT =>
          intro t _ ht
          refine Finset.sum_eq_zero fun ω _ => ?_
          refine mul_eq_zero_of_right _ ?_
          split_ifs with hg
          · rw [Matrix.single_apply, if_neg]
            rintro ⟨h1, -⟩
            refine ht ?_
            have := ((bb84_pePassOutIndex_eq_split_iff peSel _ _ (_, t) _ _ _
              pkA pkB pFl pStp pEv pSyn pPE).mp
                (congrArg Prod.fst (finProdFinEquiv.injective h1))).2.2.2.1
            exact congrArg Prod.snd ((Equiv.eq_symm_apply _).mpr this)
          · rfl
        case main3 =>
          -- read off the entries of the matrix unit, then the state-map entries
          dsimp only [Matrix.single_apply]
          simp_rw [bb84PEAnnounceAgreeLHLInput_stateMap_apply, ite_mul_right_zero, ← mul_assoc]
          rw [sum_mul_fiber_sum]
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Op_tensor_apply_finProd]
          simp only [Equiv.symm_apply_apply, stdProj_toOp_apply,
            bb84SiftedAgreeAcceptCQState_stateMap_apply, bb84AnnounceKernel_toOp_apply,
            Matrix.of_apply]
          by_cases hagree : bb84SiftedAgreeAcceptKeep peSel xSel ec δ Q ω = true
          · rw [if_pos hagree, if_pos hagree]
            rw [ite_one_mul_eq, ite_one_mul_eq]
            simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, and_true,
              bb84_pePassOutIndex_eq_split_iff, bb84_keyCopyOutputIndex_eq_split_iff,
              Prod.mk.eta, Equiv.apply_symm_apply, ite_and_mul, if_true, and_self, one_mul,
              mul_one]
            rw [show ((2 ^ ℓ : ℂ) *
                  (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ))⁻¹ =
                ((2 ^ ℓ : ℂ) * (Fintype.card (KeyHashSeed n ℓ peSel) : ℂ))⁻¹ *
                  ((Fintype.card (KeyHashSeed n ℓEV peSel) : ℂ))⁻¹ from by
              rw [← bb84KeyHashSeedPairEV_card n ℓ ℓEV peSel, Nat.cast_mul, ← mul_assoc, mul_inv]]
            push_cast
            by_cases hqFl : (0 : Fin 2) = qFl
            · simp only [if_pos hqFl]
              ring
            · simp only [if_neg hqFl]
              ring
          · rw [if_neg hagree, if_neg hagree]
            ring
  · refine Eq.trans (Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun z _ =>
      Finset.sum_eq_zero fun ω _ => Finset.sum_eq_zero fun t _ => ?_)
      (Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun z _ =>
        Finset.sum_eq_zero fun x _ => ?_).symm
    · refine mul_eq_zero_of_right _ ?_
      split_ifs with hg
      · rw [Matrix.single_apply, if_neg]
        rintro ⟨h1, h2⟩
        refine hStp ?_
        have e1 := ((bb84_pePassOutIndex_eq_split_iff peSel _ _ (s, t) _ _ _
          pkA pkB pFl pStp pEv pSyn pPE).mp
            (congrArg Prod.fst (finProdFinEquiv.injective h1))).2.2.2.1
        have e2 := ((bb84_pePassOutIndex_eq_split_iff peSel _ _ (s, t) _ _ _
          qkA qkB qFl qStp qEv qSyn qPE).mp
            (congrArg Prod.fst (finProdFinEquiv.injective h2))).2.2.2.1
        exact e1.symm.trans e2
      · rfl
    · refine mul_eq_zero_of_right _ ?_
      rw [Matrix.single_apply]
      split_ifs with hc
      · obtain ⟨h1, h2⟩ := hc
        have e1 := ((bb84_keyCopyOutputIndex_eq_split_iff peSel s _ _
          pkA pkB pFl _ _).mp h1).2.2.2.1
        have e2 := ((bb84_keyCopyOutputIndex_eq_split_iff peSel s _ _
          qkA qkB qFl _ _).mp h2).2.2.2.1
        have hS : ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp).1 =
            ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm qStp).1 :=
          Equiv.injective _ (e1.symm.trans e2)
        rw [bb84PEAnnounceAgreeLHLInput_stateMap_apply, bb84AnnounceKernel_toOp_apply]
        have hT : ¬ (Fintype.equivFin (KeyHashSeed n ℓEV peSel)
            ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp).2 =
          Fintype.equivFin (KeyHashSeed n ℓEV peSel)
            ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm qStp).2) := by
          intro hT
          refine hStp ?_
          have := Equiv.injective (Fintype.equivFin (KeyHashSeed n ℓEV peSel)) hT
          have hpair : (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm pStp =
              (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm qStp :=
            Prod.ext hS this
          exact (Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).symm.injective hpair
        -- The seed-tag indicator factor vanishes.
        simp only [if_neg hT, zero_mul, mul_zero]
      · rfl

/-- **Ideal agree pass output as the leftover-hashing postprocess of the seed-uniform output.**

The `mapTensorId` extension of the agree-restricted ideal pass channel equals the agree-block
leftover-hashing postprocess applied to the joint density of the seed-uniform output state on the
quantum marginal of `bb84PEAnnounceAgreeLHLInput`.

The ideal pass Kraus writes one fresh uniform key into both slots unconditionally, so on the agree
block the restriction is a pure gate on the round outcome and no key identification is needed; the
announced digits are the same as on the real side, which is exactly why they cancel from the
difference block-diagonally rather than being droppable.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024),
`arXiv:2403.11851`, App. B (B18), stated at the paper's free test-set size `m`
(`main.tex:909`, `:913-915`).  No relation between `m` and `n` is
used. -/
theorem
    idealAgreePass_mapTensorId_eq_lhlPostprocess_seedUniformOutput
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    haveI : Nonempty (KeyHashSeed n ℓ peSel) :=
      (aliceKeyHashFamily n ℓ peSel).seedNonempty
    mapTensorId
        (((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
          krausMapFintype (fun k =>
            if bb84SiftedKeyStringsDiffer peSel ec k.1 then 0
            else bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim
              peSel xSel leakEC ec δ Q k)).comp
          ((measurementChannel n eveDim).comp
            (bb84SiftedConjAfterPre eveDim pre peSel xSel)))
        τ.toOp =
      ⇑(bb84PEAnnounceAgreeLHLPostprocess n m ℓ ℓEV leakEC peSel eveDim dimR)
        (seedUniformOutputState (S := KeyHashSeed n ℓ peSel)
          (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
            τ).quantumMarginal).toJointDensity.toOp := by
  haveI hSeedNE : Nonempty (KeyHashSeed n ℓ peSel) :=
    (aliceKeyHashFamily n ℓ peSel).seedNonempty
  haveI hCond : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
  haveI hKey : NeZero (2 ^ ℓ) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI hTr : NeZero (2 * Fintype.card (KeyHashSeed n ℓ peSel)) :=
    ⟨Nat.mul_ne_zero two_ne_zero Fintype.card_ne_zero⟩
  rw [bb84SiftedPEAnnounceEveVisible_idealAgreePass_eq_relabel_sum_blocks]
  · simp only [bb84PEAnnounceAgreeLHLPostprocess, LinearMap.comp_apply]
    congr 1
    exact (classicalKeyCopyPostprocess_castOne_toJointDensity_eq_sum_outputBlocks
      (C := KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ)) (2 ^ ℓ) _
      (2 * Fintype.card (KeyHashSeed n ℓ peSel)) (fun sz => sz.2)
      (fun sz => bb84AliceSeedPassTranscript n ℓ peSel sz.1)
      (bb84PEAnnounceAgreeLHLPostprocess_input_dim_eq n m ℓ ℓEV leakEC peSel
        eveDim dimR).symm
      (seedUniformOutputState (S := KeyHashSeed n ℓ peSel)
        (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
            τ).quantumMarginal)).symm

/-! ## The bridge -/

/-- **The agree-block pass-support / leftover-hashing bridge.**

Half the CKR tensor trace norm of the agree-restricted real/ideal difference at a CKR de Finetti
purification `τ` is bounded by the generalized trace distance between the Alice-bit seed-key
extractor output and the seed-uniform output, both scored on `bb84PEAnnounceAgreeLHLInput` — the
agree-and-accept filtered τ-side CQ state whose quantum register carries the announced syndrome,
error-verification seed and tag, and PE-outcome block.

**The announcements stay on the quantum side.**  Coarsening any of them away while the channel
writes it into the transcript asserts the data-processing inequality backwards; the exact
counterexample at the PE register has left-hand side `1`, right-hand side `1/2`.

The two agree-block pass-output identities rewrite the tensor-extended difference as a single CPTP
postprocess of the leftover-hashing output difference, and
`ckrTensorTraceNorm_le_two_traceDistanceGen_of_cptp_postprocess_eq` closes.

This is the structural half of the secrecy leaf; the quantitative half is the smooth
min-entropy floor for `bb84PEAnnounceAgreeLHLInput`, whose announce charge is
`InfoTheory.SmoothMinEntropy.bb84_smoothMinEntropy_announce_ge_sub_leak`.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, App. B (B18); Renner (2005),
`arXiv:quant-ph/0512258v2`, §6.5; Christandl-König-Renner (2009), `arXiv:0809.3019`,
main.tex:268–:401 (\emph{Main Result}: Theorem `\label{thm:main}` :291–:301, Lemma
`\label{lem:extractpart}` :319–:328).

Stated at the paper's free test-set size `m` (arXiv:2403.11851, `main.tex:909`,
`:913-915`).  Nothing here relates `m` to `n`: the postprocess is CPTP and the two pass-output
identities hold at every `m`, so `m = 0` and `m = n` are covered and degenerate. -/
theorem bb84SiftedPEAnnounceEveVisible_agreeBlock_traceDistance_le_LHL_distance
    {n m : ℕ} (ℓ ℓEV : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {dimR : ℕ} [NeZero dimR]
    (τ : DensityOp ((signalDim ^ n) * dimR)) :
    haveI : Nonempty (KeyHashSeed n ℓ peSel) :=
      (aliceKeyHashFamily n ℓ peSel).seedNonempty
    haveI : NeZero (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC
        eveDim) := inferInstance
    haveI : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
      ⟨Nat.mul_ne_zero
        (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
          (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
        (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
          (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
    haveI : NeZero ((2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
        (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) *
        Fintype.card (KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ))) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) Fintype.card_ne_zero⟩
    (1 / 2) * ckrTensorTraceNorm
        ((((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
            krausMapFintype (fun k =>
              if bb84SiftedKeyStringsDiffer peSel ec k.2 then 0
              else bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim
                peSel xSel leakEC ec δ Q k)).comp
            ((measurementChannel n eveDim).comp
              (bb84SiftedConjAfterPre eveDim pre peSel xSel))) -
          (((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
            krausMapFintype (fun k =>
              if bb84SiftedKeyStringsDiffer peSel ec k.1 then 0
              else bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim
                peSel xSel leakEC ec δ Q k)).comp
            ((measurementChannel n eveDim).comp
              (bb84SiftedConjAfterPre eveDim pre peSel xSel)))) τ ≤
      Quantum.Metrics.traceDistanceGen
        (seedKeyExtractorOutputState (aliceKeyHashFamily n ℓ peSel)
          (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
              τ)).toJointDensity.toOp
        (seedUniformOutputState (S := KeyHashSeed n ℓ peSel)
          (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
            τ).quantumMarginal).toJointDensity.toOp := by
  haveI hSeedNE : Nonempty (KeyHashSeed n ℓ peSel) :=
    (aliceKeyHashFamily n ℓ peSel).seedNonempty
  haveI hOutDim : NeZero (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC
      eveDim) := inferInstance
  haveI hCond : NeZero (2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) :=
    ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (by norm_num))))
      (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num [signalDim]))
        (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)))⟩
  haveI hIn : NeZero ((2 ^ leakEC * (Fintype.card (KeyHashSeed n ℓEV peSel) * 2 ^ ℓEV) *
      (signalDim ^ (n - bb84KeyRoundCount n m) * (eveDim * dimR))) *
      Fintype.card (KeyHashSeed n ℓ peSel × Fin (2 ^ ℓ))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) Fintype.card_ne_zero⟩
  have hmap :
      mapTensorId
          ((((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
              krausMapFintype (fun k =>
                if bb84SiftedKeyStringsDiffer peSel ec k.2 then 0
                else bb84.retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim
                  peSel xSel leakEC ec δ Q k)).comp
              ((measurementChannel n eveDim).comp
                (bb84SiftedConjAfterPre eveDim pre peSel xSel))) -
            (((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
              krausMapFintype (fun k =>
                if bb84SiftedKeyStringsDiffer peSel ec k.1 then 0
                else bb84.retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim
                  peSel xSel leakEC ec δ Q k)).comp
              ((measurementChannel n eveDim).comp
                (bb84SiftedConjAfterPre eveDim pre peSel xSel)))) τ.toOp =
        ⇑(bb84PEAnnounceAgreeLHLPostprocess n m ℓ ℓEV leakEC peSel eveDim dimR)
          ((seedKeyExtractorOutputState (aliceKeyHashFamily n ℓ peSel)
              (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
                  τ)).toJointDensity.toOp -
            (seedUniformOutputState (S := KeyHashSeed n ℓ peSel)
              (bb84PEAnnounceAgreeLHLInput (m := m) ℓEV eveDim pre hpre peSel xSel ec Q δ
                τ).quantumMarginal).toJointDensity.toOp) := by
    rw [mapTensorId_linearMap_sub,
      realAgreePass_mapTensorId_eq_lhlPostprocess_seedKeyOutput
        (m := m) ℓ ℓEV eveDim pre hpre peSel xSel ec Q δ τ,
      idealAgreePass_mapTensorId_eq_lhlPostprocess_seedUniformOutput
        (m := m) ℓ ℓEV eveDim pre hpre peSel xSel ec Q δ τ,
      ← map_sub]
  have h := ckrTensorTraceNorm_le_two_traceDistanceGen_of_cptp_postprocess_eq _ τ
    (⇑(bb84PEAnnounceAgreeLHLPostprocess n m ℓ ℓEV leakEC peSel eveDim dimR))
    (bb84PEAnnounceAgreeLHLPostprocess_isCPTP n m ℓ ℓEV leakEC peSel eveDim dimR)
    _ _ hmap
  linarith

end QKD.BB84.Engine

end -- noncomputable section
