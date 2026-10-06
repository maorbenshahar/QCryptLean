import QCryptLean.QKD.BB84.Engine.Postselection.PEAnnounceRelabel

/-!
# The announced-PE relabel unitary at a general test-set size `m`

General-`m` forms of the announced-PE relabel chain of `PEAnnounceRelabel.lean`.  Every declaration
there pins the split point through the closed term `bb84KeyRoundCountCanonical n = n − ⌈n/2⌉`; the
declarations here are their forms over `bb84KeyRoundCount n m = n − m`, i.e. over the announced
PE register `Fin (signalDim ^ (n − bb84KeyRoundCount n m))` and the general-`m` round
partition `bb84PartEquiv`.

`m` enters this file in exactly one place — the width of the announced PE-outcome register — and
nothing here reads a property of it.  The relabel of that register acts **positionwise**, by
`bellKeyOutcomePerm (h (bb84PERoundIdx peSel j))` at position `j`, so widening the index type
changes the arity of a product and nothing else.  Accordingly the general-`m` family carries **no**
constraint relating `m` to `n`: no `m ≤ n`, no `m < n`, no `bb84KeyCount` hypothesis, matching
the general-`m` Param family of `SiftedPEAnnounce.lean` this chain is stated over
(`bb84PartEquiv`, `bb84PERoundIdx`, `pePassOutIndex`, `peFailOutIndex`, the
three Param Kraus families, the two Param PA/abort maps and
`bb84SiftedPEAnnounceLinearEveVisible`, all unconditional).  `m = 0` and `m = n` are covered
and degenerate rather than excluded.

## What is shared with the pinned chain rather than duplicated

The `m`-free objects of `PEAnnounceRelabel.lean` are used unchanged: the effective twirl string
`bb84SiftedTwirlString` and its key-round transparency `bellTwirlKeyError_siftedTwirlString`, the
sift conjugation `bb84SiftedRotation_bellTwirl_conj` / `bb84SiftedConjChannel_bellTwirl_conj`, the
key-round error pattern `bellTwirlKeyError`, the control register `PEAnnounceControl`, the key-slot
permutation `bb84PEAnnounceKeyPairPerm` (which lands in `Equiv.Perm (Fin (2^ℓ) × Fin (2^ℓ))` and
reads only the control register), the key-string shifts
`bb84{Alice,Bob}KeyString_bellStringRelabel`, and the two Kraus-index reindexings
`bb84PEAnnounceOutcomeReindex` / `bb84PEAnnounceIdealReindex` (both `Equiv`s of index types with no
output register in them).  So are the flag-blind refutation witnesses, whose content — that
`binaryInnerProductHashShiftPerm` does not fix the zero key, forcing the accept-flag case split — is
a statement about the key slots at `n = 1` and carries no PE register.

## Shape of the relabel

Unchanged from the pinned chain.  Write `h` for the twirl string as it reaches the computational
measurement and `e = bellTwirlKeyError peSel h` for the key-round error pattern it imposes.
`bb84PEAnnounceBellRelabel` acts on the announced output index by

* `flag = 0` (pass): `(kA, kB) ↦ (σ_{st.1} kA, σ_{st.1} kB)` with
  `σ_A = binaryInnerProductHashShiftPerm A e`;
* `flag = 1` (fail): `(kA, kB) ↦ (kA, kB)`, the identity;
* both branches: `evTag ↦ σ_{st.2} evTag`, `syn ↦ πsyn syn`,
  `pe ↦ bb84PEBlockRelabelPerm peSel h pe`.

## The syndrome permutation is explicit witness data, not a choice

Clause (i) of `ECScheme.IsTranslationEquivariant` supplies the syndrome-alphabet permutation
`π_e` existentially.  Extracting it would need `Classical.choose`, so every declaration here takes
`πsyn : Equiv.Perm (Fin (2 ^ leakEC))` together with its defining hypothesis
`∀ a, ec.syndrome (a + e) = πsyn (ec.syndrome a)` as explicit data.  Consumers holding a proof
of `ECScheme.IsTranslationEquivariant` for `ec` destructure the existential at the point of use.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B and §V.C
(`main.tex:906`–`:919`, the classical post-processing block whose
announcements are the registers relabelled here; `m` is the paper's test-set size, and this module
only widens the announced-PE register from the `⌈n/2⌉`-split to a free `m`); Renner (2005),
`arXiv:quant-ph/0512258v2`, §6.5; Christandl–König–Renner (2009), `arXiv:0809.3019`,
`main.tex:268`–`:401` (\emph{Main Result}: the Post-Selection Theorem `\label{thm:main}` :291–:301,
the substate-extraction Lemma `\label{lem:extractpart}` :319–:328).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics Math.RepresentationTheory
open QKD.BB84.Model
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

open QKD.BB84.Model.bb84

/-! ## Unpacking the general-`m` base output index

`bb84.pePassOutIndex` and `bb84.peFailOutIndex` pack seven fields into
`Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)` through nested `finProdFinEquiv`s.
The relabel must read the accept flag and the announced seed pair, so the index is first unpacked
into the (`m`-free) **control** register `(flag, st)` and a **payload** register
`((kA, kB), ((evTag, syn), pe))`. -/

/-- The **payload registers** of a general-`m` base output index: the two hashed key slots, the
error-verification tag, the announced syndrome, and the announced PE-outcome block on the
`n − bb84KeyRoundCount n m` test rounds. -/
abbrev PEAnnouncePayload (n m ℓ ℓEV leakEC : ℕ) : Type :=
  (Fin (2 ^ ℓ) × Fin (2 ^ ℓ)) ×
    ((Fin (2 ^ ℓEV) × Fin (2 ^ leakEC)) × Fin (signalDim ^ (n - bb84KeyRoundCount n m)))

/-- The nested-`finProdFinEquiv` packing of the seven general-`m` output fields, in the
association `bb84.pePassOutIndex` uses. -/
def peOutRawEncode (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :
    (Fin (2 ^ ℓ) × Fin (2 ^ ℓ)) ×
        (Fin 2 ×
          (((KeyHashSeedPairEV n ℓ ℓEV peSel × Fin (2 ^ ℓEV)) × Fin (2 ^ leakEC)) ×
            Fin (signalDim ^ (n - bb84KeyRoundCount n m)))) ≃
      Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
  let e1 := ((Fintype.equivFin (KeyHashSeedPairEV n ℓ ℓEV peSel)).prodCongr
    (Equiv.refl (Fin (2 ^ ℓEV)))).trans finProdFinEquiv
  let e2 := (e1.prodCongr (Equiv.refl (Fin (2 ^ leakEC)))).trans finProdFinEquiv
  let e3 := (e2.prodCongr
    (Equiv.refl (Fin (signalDim ^ (n - bb84KeyRoundCount n m))))).trans finProdFinEquiv
  let e4 := ((Equiv.refl (Fin 2)).prodCongr e3).trans finProdFinEquiv
  ((finProdFinEquiv : Fin (2 ^ ℓ) × Fin (2 ^ ℓ) ≃ Fin (2 ^ ℓ * 2 ^ ℓ)).prodCongr e4).trans
    finProdFinEquiv

/-- The pure product reshuffle putting the control register `(flag, st)` first. -/
def peOutFieldReshuffle (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :
    (Fin (2 ^ ℓ) × Fin (2 ^ ℓ)) ×
        (Fin 2 ×
          (((KeyHashSeedPairEV n ℓ ℓEV peSel × Fin (2 ^ ℓEV)) × Fin (2 ^ leakEC)) ×
            Fin (signalDim ^ (n - bb84KeyRoundCount n m)))) ≃
      PEAnnounceControl n ℓ ℓEV peSel × PEAnnouncePayload n m ℓ ℓEV leakEC where
  toFun x := ((x.2.1, x.2.2.1.1.1), (x.1, ((x.2.2.1.1.2, x.2.2.1.2), x.2.2.2)))
  invFun y := (y.2.1, (y.1.1, (((y.1.2, y.2.2.1.1), y.2.2.1.2), y.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The general-`m` base output index decode**: `(kA, kB, flag, st, evTag, syn, pe)` unpacked
into the control register `(flag, st)` and the payload `((kA, kB), ((evTag, syn), pe))`. -/
def peOutDecode (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :
    Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) ≃
      PEAnnounceControl n ℓ ℓEV peSel × PEAnnouncePayload n m ℓ ℓEV leakEC :=
  (peOutRawEncode n m ℓ ℓEV peSel leakEC).symm.trans
    (peOutFieldReshuffle n m ℓ ℓEV peSel leakEC)

theorem peOutRawEncode_pass (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (kA kB : Fin (2 ^ ℓ)) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC)) (p : Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :
    peOutRawEncode n m ℓ ℓEV peSel leakEC
        ((kA, kB), ((0 : Fin 2), (((st, evTag), syn), p))) =
      pePassOutIndex n m ℓ ℓEV peSel leakEC kA kB st evTag syn p := rfl

theorem peOutRawEncode_fail (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC)) (p : Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :
    peOutRawEncode n m ℓ ℓEV peSel leakEC
        (((⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ)),
          (⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ))),
          ((1 : Fin 2), (((st, evTag), syn), p))) =
      peFailOutIndex n m ℓ ℓEV peSel leakEC st evTag syn p := rfl

/-- The decode of a general-`m` pass transcript index. -/
theorem peOutDecode_passOutIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (kA kB : Fin (2 ^ ℓ)) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC)) (p : Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :
    peOutDecode n m ℓ ℓEV peSel leakEC
        (pePassOutIndex n m ℓ ℓEV peSel leakEC kA kB st evTag syn p) =
      (((0 : Fin 2), st), ((kA, kB), ((evTag, syn), p))) := by
  rw [peOutDecode, Equiv.trans_apply, ← peOutRawEncode_pass, Equiv.symm_apply_apply]
  rfl

/-- The decode of a general-`m` abort transcript index: both key slots are the zero key. -/
theorem peOutDecode_failOutIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC)) (p : Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :
    peOutDecode n m ℓ ℓEV peSel leakEC
        (peFailOutIndex n m ℓ ℓEV peSel leakEC st evTag syn p) =
      (((1 : Fin 2), st),
        (((⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ)),
          (⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ))), ((evTag, syn), p))) := by
  rw [peOutDecode, Equiv.trans_apply, ← peOutRawEncode_fail, Equiv.symm_apply_apply]
  rfl

/-! ## The general-`m` relabel permutation -/

/-- **The relabel of the general-`m` announced PE-outcome block.**  The `pe` slot records the
outcomes of the `n − bb84KeyRoundCount n m` test rounds in sorted order
(`bb84PartEquiv`), so the twirl relabels it position by position, by
`bellKeyOutcomePerm (h (bb84PERoundIdx peSel j))` at position `j`. -/
def bb84PEBlockRelabelPerm {n m : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4) :
    Equiv.Perm (Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :=
  finFunctionFinEquiv.symm.trans
    ((Equiv.piCongrRight fun j => bellKeyOutcomePermEquiv (h (bb84PERoundIdx peSel j))).trans
      finFunctionFinEquiv)

theorem bb84PEBlockRelabelPerm_apply {n m : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4)
    (u : Fin (n - bb84KeyRoundCount n m) → Fin signalDim) :
    bb84PEBlockRelabelPerm (m := m) peSel h (finFunctionFinEquiv u) =
      finFunctionFinEquiv
        (fun j => bellKeyOutcomePerm (h (bb84PERoundIdx peSel j)) (u j)) := by
  simp only [bb84PEBlockRelabelPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- **The permutation of the general-`m` announced non-key registers**: the error-verification tag
by the hash-argument shift at the error-verification half of the announced seed pair `st`, the
syndrome by the supplied `πsyn`, the PE block by `bb84PEBlockRelabelPerm`.  Unlike the key slots
this acts the same way on both branches, since `bb84.peFailOutIndex` retains all three
announcements. -/
def bb84PEAnnounceAnnouncementPerm {n m : ℕ} (ℓ ℓEV leakEC : ℕ) (peSel : Fin n → Bool)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (c : PEAnnounceControl n ℓ ℓEV peSel) :
    Equiv.Perm ((Fin (2 ^ ℓEV) × Fin (2 ^ leakEC)) ×
      Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :=
  ((binaryInnerProductHashShiftPerm c.2.2 (bellTwirlKeyError peSel h)).prodCongr
    πsyn).prodCongr (bb84PEBlockRelabelPerm (m := m) peSel h)

/-- The general-`m` payload permutation at a fixed control value `(flag, st)`.  The key-slot
component is the `m`-free `bb84PEAnnounceKeyPairPerm`. -/
def bb84PEAnnouncePayloadPerm {n m : ℕ} (ℓ ℓEV leakEC : ℕ) (peSel : Fin n → Bool)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (c : PEAnnounceControl n ℓ ℓEV peSel) :
    Equiv.Perm (PEAnnouncePayload n m ℓ ℓEV leakEC) :=
  (bb84PEAnnounceKeyPairPerm ℓ ℓEV peSel h c).prodCongr
    (bb84PEAnnounceAnnouncementPerm (m := m) ℓ ℓEV leakEC peSel h πsyn c)

/-- **The announced-PE relabel permutation of the general-`m` base output register.**

Explicit: a `Fin`-indexed permutation obtained by decoding the announced output index, permuting the
payload by a permutation controlled by the announced `(flag, st)`, and re-encoding.  No
`Classical.choose`: the syndrome-alphabet permutation `πsyn` is a parameter.

Direction: `bb84PEAnnounceBellRelabel` maps the transcript written on an outcome `ω` to the
transcript written on the twirled outcome `bellStringRelabel n h ω` (see
`retainedSiftedPEAnnouncePassBranchKraus_bellTwirl_intertwining`). -/
def bb84PEAnnounceBellRelabel (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC))) :
    Equiv.Perm (Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)) :=
  (peOutDecode n m ℓ ℓEV peSel leakEC).symm.permCongr
    (Equiv.prodCongrRight (bb84PEAnnouncePayloadPerm ℓ ℓEV leakEC peSel h πsyn))

/-- **The relabel carries the pass transcript**: both key slots by the privacy-amplification-seed
shift, the EV tag by the error-verification-seed shift, the syndrome by `πsyn`, the PE block by the
round-wise outcome relabel.  The seed pair `st` itself is fixed — it is public randomness the twirl
does not touch. -/
theorem bb84PEAnnounceBellRelabel_passOutIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (kA kB : Fin (2 ^ ℓ)) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC)) (p : Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :
    bb84PEAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn
        (pePassOutIndex n m ℓ ℓEV peSel leakEC kA kB st evTag syn p) =
      pePassOutIndex n m ℓ ℓEV peSel leakEC
        (binaryInnerProductHashShiftPerm st.1 (bellTwirlKeyError peSel h) kA)
        (binaryInnerProductHashShiftPerm st.1 (bellTwirlKeyError peSel h) kB) st
        (binaryInnerProductHashShiftPerm st.2 (bellTwirlKeyError peSel h) evTag)
        (πsyn syn) (bb84PEBlockRelabelPerm (m := m) peSel h p) := by
  rw [bb84PEAnnounceBellRelabel, Equiv.permCongr_apply, Equiv.symm_symm,
    peOutDecode_passOutIndex, Equiv.prodCongrRight_apply]
  rw [show bb84PEAnnouncePayloadPerm (m := m) ℓ ℓEV leakEC peSel h πsyn ((0 : Fin 2), st)
        ((kA, kB), ((evTag, syn), p)) =
      ((binaryInnerProductHashShiftPerm st.1 (bellTwirlKeyError peSel h) kA,
        binaryInnerProductHashShiftPerm st.1 (bellTwirlKeyError peSel h) kB),
        ((binaryInnerProductHashShiftPerm st.2 (bellTwirlKeyError peSel h) evTag, πsyn syn),
          bb84PEBlockRelabelPerm (m := m) peSel h p)) by
      simp [bb84PEAnnouncePayloadPerm, bb84PEAnnounceKeyPairPerm,
        bb84PEAnnounceAnnouncementPerm]]
  rw [peOutDecode, Equiv.symm_trans_apply]
  rw [show (peOutFieldReshuffle n m ℓ ℓEV peSel leakEC).symm
        (((0 : Fin 2), st),
          ((binaryInnerProductHashShiftPerm st.1 (bellTwirlKeyError peSel h) kA,
            binaryInnerProductHashShiftPerm st.1 (bellTwirlKeyError peSel h) kB),
            ((binaryInnerProductHashShiftPerm st.2 (bellTwirlKeyError peSel h) evTag, πsyn syn),
              bb84PEBlockRelabelPerm (m := m) peSel h p))) =
      ((binaryInnerProductHashShiftPerm st.1 (bellTwirlKeyError peSel h) kA,
        binaryInnerProductHashShiftPerm st.1 (bellTwirlKeyError peSel h) kB),
        ((0 : Fin 2),
          (((st, binaryInnerProductHashShiftPerm st.2 (bellTwirlKeyError peSel h) evTag),
            πsyn syn), bb84PEBlockRelabelPerm (m := m) peSel h p))) from rfl,
    Equiv.symm_symm, peOutRawEncode_pass]

/-- **The relabel fixes the abort transcript's key slots.**  `bb84.peFailOutIndex` writes the
zero key in both slots regardless of the outcome, so on the abort flag the key-slot permutation must
be the identity; the three announcements still move.  A flag-blind "shift both key slots"
permutation fails here. -/
theorem bb84PEAnnounceBellRelabel_failOutIndex (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (evTag : Fin (2 ^ ℓEV))
    (syn : Fin (2 ^ leakEC)) (p : Fin (signalDim ^ (n - bb84KeyRoundCount n m))) :
    bb84PEAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn
        (peFailOutIndex n m ℓ ℓEV peSel leakEC st evTag syn p) =
      peFailOutIndex n m ℓ ℓEV peSel leakEC st
        (binaryInnerProductHashShiftPerm st.2 (bellTwirlKeyError peSel h) evTag)
        (πsyn syn) (bb84PEBlockRelabelPerm (m := m) peSel h p) := by
  rw [bb84PEAnnounceBellRelabel, Equiv.permCongr_apply, Equiv.symm_symm,
    peOutDecode_failOutIndex, Equiv.prodCongrRight_apply]
  rw [show bb84PEAnnouncePayloadPerm (m := m) ℓ ℓEV leakEC peSel h πsyn ((1 : Fin 2), st)
        (((⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ)),
          (⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ))), ((evTag, syn), p)) =
      (((⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ)),
        (⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ))),
        ((binaryInnerProductHashShiftPerm st.2 (bellTwirlKeyError peSel h) evTag, πsyn syn),
          bb84PEBlockRelabelPerm (m := m) peSel h p)) by
      simp [bb84PEAnnouncePayloadPerm, bb84PEAnnounceKeyPairPerm,
        bb84PEAnnounceAnnouncementPerm]]
  rw [peOutDecode, Equiv.symm_trans_apply]
  rw [show (peOutFieldReshuffle n m ℓ ℓEV peSel leakEC).symm
        (((1 : Fin 2), st),
          (((⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ)),
            (⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ))),
            ((binaryInnerProductHashShiftPerm st.2 (bellTwirlKeyError peSel h) evTag, πsyn syn),
              bb84PEBlockRelabelPerm (m := m) peSel h p))) =
      (((⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ)),
        (⟨0, pow_pos (by norm_num : 0 < 2) ℓ⟩ : Fin (2 ^ ℓ))),
        ((1 : Fin 2),
          (((st, binaryInnerProductHashShiftPerm st.2 (bellTwirlKeyError peSel h) evTag),
            πsyn syn), bb84PEBlockRelabelPerm (m := m) peSel h p))) from rfl,
    Equiv.symm_symm, peOutRawEncode_fail]

/-! ## The general-`m` relabel unitary -/

/-- **The unitary implementing the general-`m` announced-PE relabel** on basis vectors.

Convention: `bb84PEAnnounceBellRelabelUnitary · |out⟩⟨col| = |R⁻¹ out⟩⟨col|`
(`bb84PEAnnounceBellRelabelUnitary_mul_single`), so left-multiplying the Kraus written on the
**twirled** outcome returns the Kraus row of the **untwirled** one. -/
def bb84PEAnnounceBellRelabelUnitary (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC))) :
    Op (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) :=
  Equiv.Perm.permMatrix ℂ (bb84PEAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn)

/-- **The relabel operator is unitary** (it is a permutation matrix). -/
theorem bb84PEAnnounceBellRelabelUnitary_unitary (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC))) :
    (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)ᴴ *
        bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn = 1 :=
  Equiv.Perm.permMatrix_conjTranspose_mul_self _

/-- **`W ⊗ 1_E` is unitary**, the form the per-block trace-norm steps consume. -/
theorem bb84PEAnnounceBellRelabelUnitary_tensor_one_unitary (n m ℓ ℓEV : ℕ)
    (peSel : Fin n → Bool) (leakEC eveDim : ℕ) (h : Fin n → Fin 4)
    (πsyn : Equiv.Perm (Fin (2 ^ leakEC))) :
    (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
          (1 : Op eveDim))ᴴ *
        Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
          (1 : Op eveDim) = 1 := by
  rw [Op.tensor_conjTranspose, Op.tensor_mul, Matrix.conjTranspose_one, Matrix.one_mul,
    bb84PEAnnounceBellRelabelUnitary_unitary, Op.tensor_one]

/-- The general-`m` relabel unitary's action on a matrix-unit row.  Uses the generic
(dimension-independent) `permMatrix_mul_single` (`ProtocolMapCovariance.lean`) directly. -/
theorem bb84PEAnnounceBellRelabelUnitary_mul_single (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool)
    (leakEC : ℕ) (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    {γ : Type*} [DecidableEq γ]
    (out : Fin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)) (col : γ) (v : ℂ) :
    bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn *
        Matrix.single out col v =
      Matrix.single ((bb84PEAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn).symm out)
        col v := by
  rw [bb84PEAnnounceBellRelabelUnitary, permMatrix_mul_single]

/-! ## How the twirl moves the general-`m` announced fields

The key-string shifts `bb84AliceKeyString_bellStringRelabel` and
`bb84BobKeyString_bellStringRelabel` are `m`-free and are used unchanged. -/

/-- The general-`m` announced PE-outcome block is relabelled by `bb84PEBlockRelabelPerm`. -/
theorem bb84PEBlock_bellStringRelabel {n m : ℕ} (peSel : Fin n → Bool) (h : Fin n → Fin 4)
    (ω : Fin n → Fin signalDim) :
    (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel (bellStringRelabel n h ω)).2 :
        Fin (signalDim ^ (n - bb84KeyRoundCount n m))) =
      bb84PEBlockRelabelPerm (m := m) peSel h
        (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2) := by
  rw [bb84PEBlockRelabelPerm_apply]
  refine congrArg _ (funext fun j => ?_)
  rw [bb84PartEquiv_apply_snd, bb84PartEquiv_apply_snd]
  rfl

/-- **The general-`m` pass transcript index is carried by the relabel.**  Every announced field of
`bb84.pePassOutIndex` written on the twirled outcome is the relabel's image of the field
written on the untwirled one: the two hashed key slots by `σ_{st.1}` (Alice's by linearity of the
hash, Bob's by the paired decoder clause), the EV tag by `σ_{st.2}`, the syndrome by `πsyn`, the PE
block by the round-wise outcome relabel. -/
theorem pePassOutIndex_bellStringRelabel {n m ℓ ℓEV leakEC : ℕ} (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Fin n → Fin signalDim) :
    pePassOutIndex n m ℓ ℓEV peSel leakEC
        ((aliceKeyHashFamily n ℓ peSel).hash st.1
          (aliceKeyString peSel (bellStringRelabel n h ω)))
        ((aliceKeyHashFamily n ℓ peSel).hash st.1
          (ec.decode (bobKeyString peSel (bellStringRelabel n h ω))
            (ec.syndrome (aliceKeyString peSel (bellStringRelabel n h ω)))))
        st
        (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel (bellStringRelabel n h ω)))
        (ec.syndrome (aliceKeyString peSel (bellStringRelabel n h ω)))
        (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel (bellStringRelabel n h ω)).2) =
      bb84PEAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn
        (pePassOutIndex n m ℓ ℓEV peSel leakEC
          ((aliceKeyHashFamily n ℓ peSel).hash st.1 (aliceKeyString peSel ω))
          ((aliceKeyHashFamily n ℓ peSel).hash st.1
            (ec.decode (bobKeyString peSel ω)
              (ec.syndrome (aliceKeyString peSel ω))))
          st (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
          (ec.syndrome (aliceKeyString peSel ω))
          (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2)) := by
  rw [bb84PEAnnounceBellRelabel_passOutIndex]
  rw [bb84AliceKeyString_bellStringRelabel, bb84BobKeyString_bellStringRelabel,
    hdec, hsyn, bb84PEBlock_bellStringRelabel]
  rw [show (aliceKeyHashFamily n ℓ peSel).hash st.1
        (aliceKeyString peSel ω + bellTwirlKeyError peSel h) =
      binaryInnerProductHash n ℓ peSel st.1
        (aliceKeyString peSel ω + bellTwirlKeyError peSel h) from rfl,
    show (aliceKeyHashFamily n ℓ peSel).hash st.1
        (ec.decode (bobKeyString peSel ω) (ec.syndrome (aliceKeyString peSel ω)) +
          bellTwirlKeyError peSel h) =
      binaryInnerProductHash n ℓ peSel st.1
        (ec.decode (bobKeyString peSel ω) (ec.syndrome (aliceKeyString peSel ω)) +
          bellTwirlKeyError peSel h) from rfl,
    binaryInnerProductHash_add_right, binaryInnerProductHash_add_right, verificationTag_add_right]
  rfl

/-- **The general-`m` abort transcript index is carried by the relabel.**  Its key slots are the
zero key on both outcomes, so only the three announcements move. -/
theorem peFailOutIndex_bellStringRelabel {n m ℓ ℓEV leakEC : ℕ} (peSel : Fin n → Bool)
    (ec : ECScheme n peSel leakEC) (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) (ω : Fin n → Fin signalDim) :
    peFailOutIndex n m ℓ ℓEV peSel leakEC st
        (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel (bellStringRelabel n h ω)))
        (ec.syndrome (aliceKeyString peSel (bellStringRelabel n h ω)))
        (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel (bellStringRelabel n h ω)).2) =
      bb84PEAnnounceBellRelabel n m ℓ ℓEV peSel leakEC h πsyn
        (peFailOutIndex n m ℓ ℓEV peSel leakEC st
          (verificationTag n ℓEV peSel st.2 (aliceKeyString peSel ω))
          (ec.syndrome (aliceKeyString peSel ω))
          (finFunctionFinEquiv (bb84PartEquiv (m := m) peSel ω).2)) := by
  rw [bb84PEAnnounceBellRelabel_failOutIndex]
  rw [bb84AliceKeyString_bellStringRelabel, hsyn, bb84PEBlock_bellStringRelabel,
    verificationTag_add_right]

/-! ## Per-Kraus covariance of the three general-`m` branches

`bb84SiftedLocalPEAndEVPassed_bellTwirl_invariant` keeps each Kraus operator on the same branch of
the accept split — it reads only `peSel`, `xSel`, `ec`, `δ`, `Q`, the error-verification half of
`st` and `ω`, so it is `m`-free and shared — and `pePassOutIndex_bellStringRelabel` /
`peFailOutIndex_bellStringRelabel` carry its row; the column relabels with the unit phase
`bellTwirlSign` of the signed twirl. -/

/-- A scalar factors out of the rectangular `K ⊗ 1_E` embedding.  Dimension-generic; a module-local
copy of the same fact `PEAnnounceRelabel.lean` keeps `private`. -/
private theorem rtid_smul_peAnnounce {a b e : ℕ} (c : ℂ) (K : Matrix (Fin b) (Fin a) ℂ) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (c • K) (1 : Op e)) =
      c • Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) K (1 : Op e)) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply,
    Matrix.smul_kronecker]

/-- **Real pass-branch per-Kraus covariance at a general test-set size `m`.**
`K^{pass}_{st,ω} · (U_h ⊗ 1) = ε_{h,ω} · (W ⊗ 1) · K^{pass}_{st, h·ω}`. -/
theorem retainedSiftedPEAnnouncePassBranchKraus_bellTwirl_intertwining
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) :
    retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx *
        Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) =
      bellTwirlSign n h idx.2 •
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
            (1 : Op eveDim) *
          retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
            (idx.1, bellStringRelabel n h idx.2)) := by
  obtain ⟨st, ω⟩ := idx
  have hguard : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
      (bellStringRelabel n h ω) = bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω :=
    bb84SiftedLocalPEAndEVPassed_bellTwirl_invariant peSel xSel ec δ Q st.2 h ω hdec
  by_cases hp : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
  · have hp' : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellStringRelabel n h ω) = true := by rw [hguard]; exact hp
    simp only [retainedSiftedPEAnnouncePassBranchKraus, hp, hp', if_true]
    rw [tensorRightId_mul_tensorRightId, single_mul_bellTwirlUnitary, rtid_smul_peAnnounce,
      tensorRightId_mul_tensorRightId_left, bb84PEAnnounceBellRelabelUnitary_mul_single,
      pePassOutIndex_bellStringRelabel peSel ec h πsyn hsyn hdec st ω,
      Equiv.symm_apply_apply]
    rfl
  · have hp' : ¬ (bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellStringRelabel n h ω) = true) := by rw [hguard]; exact hp
    simp [retainedSiftedPEAnnouncePassBranchKraus, hp, hp']

/-- **Fail-branch per-Kraus covariance at a general test-set size `m`** (the branch shared by the
real and ideal maps).  `K^{fail}_{st,ω} · (U_h ⊗ 1) = ε_{h,ω} · (W ⊗ 1) · K^{fail}_{st, h·ω}`.  The
key slots are the zero key on both outcomes; the relabel is the identity on them, and only the
announcements move. -/
theorem retainedSiftedPEAnnounceFailBranchKraus_bellTwirl_intertwining
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : KeyHashSeedPairEV n ℓ ℓEV peSel × (Fin n → Fin signalDim)) :
    retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx *
        Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) =
      bellTwirlSign n h idx.2 •
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
            (1 : Op eveDim) *
          retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
            (idx.1, bellStringRelabel n h idx.2)) := by
  obtain ⟨st, ω⟩ := idx
  have hguard : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
      (bellStringRelabel n h ω) = bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω :=
    bb84SiftedLocalPEAndEVPassed_bellTwirl_invariant peSel xSel ec δ Q st.2 h ω hdec
  by_cases hp : ¬ (bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true)
  · have hp' : ¬ (bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellStringRelabel n h ω) = true) := by rw [hguard]; exact hp
    simp only [retainedSiftedPEAnnounceFailBranchKraus]
    rw [if_pos hp, if_pos hp', tensorRightId_mul_tensorRightId, single_mul_bellTwirlUnitary,
      rtid_smul_peAnnounce, tensorRightId_mul_tensorRightId_left,
      bb84PEAnnounceBellRelabelUnitary_mul_single,
      peFailOutIndex_bellStringRelabel peSel ec h πsyn hsyn st ω, Equiv.symm_apply_apply]
    rfl
  · have hp' : ¬ ¬ (bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellStringRelabel n h ω) = true) := by rw [hguard]; exact hp
    simp [retainedSiftedPEAnnounceFailBranchKraus, hp, hp']

/-- **Ideal pass-branch per-Kraus covariance at a general test-set size `m`.**  The ideal Kraus
writes ONE fresh uniform key in both slots but keeps the same `ω`-dependent announcements as the
real pass, so it too carries the relabel, at the cost of translating the fresh key by the
privacy-amplification-seed shift: `K^{ideal}_{ω,k,st} · (U_h ⊗ 1) = ε_{h,ω} · (W ⊗ 1) ·
K^{ideal}_{h·ω, σ_{st.1} k, st}`. -/
theorem retainedSiftedPEAnnounceIdealPassKraus_bellTwirl_intertwining
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (idx : (Fin n → Fin signalDim) × Fin (2 ^ ℓ) × KeyHashSeedPairEV n ℓ ℓEV peSel) :
    retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q idx *
        Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) =
      bellTwirlSign n h idx.1 •
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
            (1 : Op eveDim) *
          retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
            (bellStringRelabel n h idx.1,
              binaryInnerProductHashShiftPerm idx.2.2.1 (bellTwirlKeyError peSel h) idx.2.1,
              idx.2.2)) := by
  obtain ⟨ω, k, st⟩ := idx
  have hguard : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
      (bellStringRelabel n h ω) = bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω :=
    bb84SiftedLocalPEAndEVPassed_bellTwirl_invariant peSel xSel ec δ Q st.2 h ω hdec
  by_cases hp : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω = true
  · have hp' : bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellStringRelabel n h ω) = true := by rw [hguard]; exact hp
    simp only [retainedSiftedPEAnnounceIdealPassKraus, hp, hp', if_true]
    rw [tensorRightId_mul_tensorRightId, single_mul_bellTwirlUnitary, rtid_smul_peAnnounce,
      tensorRightId_mul_tensorRightId_left, bb84PEAnnounceBellRelabelUnitary_mul_single]
    rw [bb84AliceKeyString_bellStringRelabel, hsyn, bb84PEBlock_bellStringRelabel,
      verificationTag_add_right, ← bb84PEAnnounceBellRelabel_passOutIndex, Equiv.symm_apply_apply]
    rfl
  · have hp' : ¬ (bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2
        (bellStringRelabel n h ω) = true) := by rw [hguard]; exact hp
    simp [retainedSiftedPEAnnounceIdealPassKraus, hp, hp']

/-! ## Channel-level covariance of the general-`m` base maps

The three per-Kraus intertwinings lift to the two general-`m` base PA/abort maps, hence to their
difference.  The two Kraus-index reindexings `bb84PEAnnounceOutcomeReindex` and
`bb84PEAnnounceIdealReindex` are `Equiv`s of the (`m`-free) index types and are reused unchanged. -/

/-- Reindexing a finite Kraus family along a bijection of the index type leaves the Kraus map
unchanged.  Dimension-generic; a module-local copy of the same fact `PEAnnounceRelabel.lean` keeps
`private`. -/
private theorem krausMapFintype_reindex_peAnnounce {κ : Type*} [Fintype κ] {a b : ℕ}
    (K : κ → Matrix (Fin b) (Fin a) ℂ) (e : κ ≃ κ) (A : Op a) :
    krausMapFintype (fun i => K (e i)) A = krausMapFintype K A := by
  simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk]
  exact Equiv.sum_comp e (fun i => K i * A * (K i)ᴴ)

/-- **The general-`m` real base PA/abort map is Bell-twirl covariant**, with the general-`m`
announced-PE relabel unitary on the output. -/
theorem retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap_bellTwirl_conj
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (M : Op (4 ^ n * eveDim)) :
    retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel xSel leakEC
        ec δ Q
        (Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) * M *
          (Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim))ᴴ) =
      Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
          (1 : Op eveDim) *
        retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel xSel
          leakEC ec δ Q M *
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
          (1 : Op eveDim))ᴴ := by
  set U := Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) with hU
  set W := Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
    (1 : Op eveDim) with hW
  have hpass : krausMapFintype
      (retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
      (U * M * Uᴴ) =
      W * krausMapFintype
        (retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
        M * Wᴴ := by
    rw [krausMapFintype_conj_of_phased_intertwining
      (retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
      (fun idx => retainedSiftedPEAnnouncePassBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC
        ec δ Q (bb84PEAnnounceOutcomeReindex n ℓ ℓEV peSel h idx))
      U W (fun idx => bellTwirlSign n h idx.2) (fun idx => bellTwirlSign_unit n h idx.2)
      (fun idx => retainedSiftedPEAnnouncePassBranchKraus_bellTwirl_intertwining
        n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx) M,
      krausMapFintype_reindex_peAnnounce]
  have hfail : krausMapFintype
      (retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
      (U * M * Uᴴ) =
      W * krausMapFintype
        (retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
        M * Wᴴ := by
    rw [krausMapFintype_conj_of_phased_intertwining
      (retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
      (fun idx => retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC
        ec δ Q (bb84PEAnnounceOutcomeReindex n ℓ ℓEV peSel h idx))
      U W (fun idx => bellTwirlSign n h idx.2) (fun idx => bellTwirlSign_unit n h idx.2)
      (fun idx => retainedSiftedPEAnnounceFailBranchKraus_bellTwirl_intertwining
        n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx) M,
      krausMapFintype_reindex_peAnnounce]
  simp only [retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap, LinearMap.add_apply,
    LinearMap.smul_apply, hpass, hfail]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul]

/-- **The general-`m` ideal base key/abort map is Bell-twirl covariant**, with the same relabel
unitary. -/
theorem retainedSiftedPEAnnounceIdealKeyAndAbortChannel_bellTwirl_conj
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (M : Op (4 ^ n * eveDim)) :
    retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q
        (Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) * M *
          (Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim))ᴴ) =
      Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
          (1 : Op eveDim) *
        retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel leakEC
          ec δ Q M *
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
          (1 : Op eveDim))ᴴ := by
  set U := Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) with hU
  set W := Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
    (1 : Op eveDim) with hW
  have hideal : krausMapFintype
      (retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
      (U * M * Uᴴ) =
      W * krausMapFintype
        (retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
        M * Wᴴ := by
    rw [krausMapFintype_conj_of_phased_intertwining
      (retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
      (fun idx => retainedSiftedPEAnnounceIdealPassKraus n m ℓ ℓEV eveDim peSel xSel leakEC
        ec δ Q (bb84PEAnnounceIdealReindex n ℓ ℓEV peSel h idx))
      U W (fun idx => bellTwirlSign n h idx.1) (fun idx => bellTwirlSign_unit n h idx.1)
      (fun idx => retainedSiftedPEAnnounceIdealPassKraus_bellTwirl_intertwining
        n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx) M,
      krausMapFintype_reindex_peAnnounce]
  have hfail : krausMapFintype
      (retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
      (U * M * Uᴴ) =
      W * krausMapFintype
        (retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
        M * Wᴴ := by
    rw [krausMapFintype_conj_of_phased_intertwining
      (retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q)
      (fun idx => retainedSiftedPEAnnounceFailBranchKraus n m ℓ ℓEV eveDim peSel xSel leakEC
        ec δ Q (bb84PEAnnounceOutcomeReindex n ℓ ℓEV peSel h idx))
      U W (fun idx => bellTwirlSign n h idx.2) (fun idx => bellTwirlSign_unit n h idx.2)
      (fun idx => retainedSiftedPEAnnounceFailBranchKraus_bellTwirl_intertwining
        n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h πsyn hsyn hdec idx) M,
      krausMapFintype_reindex_peAnnounce]
  simp only [retainedSiftedPEAnnounceIdealKeyAndAbortChannel, LinearMap.add_apply,
    LinearMap.smul_apply, hideal, hfail]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul]

/-- **The general-`m` base real−ideal difference intertwines the Bell twirl with the announced-PE
relabel.**

Nothing is masked: the announced PE block, the announced syndrome and the announced
error-verification tag are all relabelled, and the key slots are relabelled only on the accept
branch. -/
theorem retainedSiftedPEAnnounce_diff_bellTwirl_conj
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (M : Op (4 ^ n * eveDim)) :
    (retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel xSel
          leakEC ec δ Q -
        retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel leakEC
          ec δ Q)
        (Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) * M *
          (Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim))ᴴ) =
      Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
          (1 : Op eveDim) *
        (retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel xSel
              leakEC ec δ Q -
            retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel
              leakEC ec δ Q) M *
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
          (1 : Op eveDim))ᴴ := by
  rw [LinearMap.sub_apply, LinearMap.sub_apply,
    retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap_bellTwirl_conj
      n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h πsyn hsyn hdec M,
    retainedSiftedPEAnnounceIdealKeyAndAbortChannel_bellTwirl_conj
      n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h πsyn hsyn hdec M,
    Matrix.mul_sub, Matrix.sub_mul]

/-! ## From the physical twirl to the relabel: sift, then measure

The general-`m` protocol map is `PA/abort ∘ measurementChannel`
(`bb84SiftedPEAnnounceEveVisibleProtocol`), and it is fed the output of the sifted attack
channel.  The physical twirl `U_g` therefore reaches the PA/abort map as `U_{g'}` with
`g' = bb84SiftedTwirlString peSel xSel g`.  The sift conjugation
`bb84SiftedConjChannel_bellTwirl_conj` and the key-round transparency
`bellTwirlKeyError_siftedTwirlString` act on `Op (4^n * eveDim)` and carry no split point, so they
are the `m`-free originals. -/

/-- **The general-`m` protocol-map difference intertwines the twirl reaching the measurement with
the announced-PE relabel.**

The two maps differenced here are the general-`m` real and ideal protocol maps, written out
rather than taken through the `BB84EveVisibleProtocolScheme` projection so that the output
dimension is the syntactic `bb84EveVisiblePEAnnounceBaseOutputDim`, which the `HMul` instance for
the conjugation needs.

The `measurementChannel` between the sift and the PA/abort map lets the monomial twirl through
unchanged (`measurementChannel_bellTwirl_outcomeRelabel`). -/
theorem bb84SiftedPEAnnounceEveVisible_measuredDiff_bellTwirl_conj
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel h) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel h)
          (ec.syndrome (a + bellTwirlKeyError peSel h)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel h)
    (M : Op (4 ^ n * eveDim)) :
    ((retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel xSel
            leakEC ec δ Q -
          retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel leakEC
            ec δ Q).comp (measurementChannel n eveDim))
        (Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim) * M *
          (Op.tensor (bellTwirlUnitary n h) (1 : Op eveDim))ᴴ) =
      Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
          (1 : Op eveDim) *
        ((retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel xSel
                leakEC ec δ Q -
              retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel
                leakEC ec δ Q).comp (measurementChannel n eveDim)) M *
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC h πsyn)
          (1 : Op eveDim))ᴴ := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, measurementChannel_bellTwirl_outcomeRelabel,
    retainedSiftedPEAnnounce_diff_bellTwirl_conj n m ℓ ℓEV eveDim peSel xSel leakEC ec δ Q h
      πsyn hsyn hdec]

/-- **The end-to-end general-`m` base covariance: physical twirl in, announced-PE relabel out.**

`Δ(sift (U_g · M · U_g†)) = (W ⊗ 1) · Δ(sift M) · (W ⊗ 1)†` with
`W = bb84PEAnnounceBellRelabelUnitary … (bb84SiftedTwirlString peSel xSel g) πsyn`.

The hypotheses on `ec` are stated at the **physical** twirl string `g`, which is legitimate because
the sift is the identity on key rounds (`bellTwirlKeyError_siftedTwirlString`); the announced PE
block, in contrast, is relabelled at the sift-relabelled string `bb84SiftedTwirlString peSel xSel
g`, i.e. by `bellHadSwap (g i)` on the X-designated PE rounds. -/
theorem bb84SiftedPEAnnounceEveVisible_siftedDiff_bellTwirl_conj
    (n m ℓ ℓEV eveDim : ℕ) [NeZero eveDim] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (g : Fin n → Fin 4) (πsyn : Equiv.Perm (Fin (2 ^ leakEC)))
    (hsyn : ∀ a : KeyBitString n peSel,
      ec.syndrome (a + bellTwirlKeyError peSel g) = πsyn (ec.syndrome a))
    (hdec : ∀ a b : KeyBitString n peSel,
      ec.decode (b + bellTwirlKeyError peSel g)
          (ec.syndrome (a + bellTwirlKeyError peSel g)) =
        ec.decode b (ec.syndrome a) + bellTwirlKeyError peSel g)
    (M : Op (4 ^ n * eveDim)) :
    ((retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel xSel
            leakEC ec δ Q -
          retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel leakEC
            ec δ Q).comp (measurementChannel n eveDim))
        (bb84SiftedConjChannel n eveDim peSel xSel
          (Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim) * M *
            (Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim))ᴴ)) =
      Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC
          (bb84SiftedTwirlString peSel xSel g) πsyn) (1 : Op eveDim) *
        ((retainedSiftedPEAnnouncePrivacyAmplifyAndAbortLinearMap n m ℓ ℓEV eveDim peSel xSel
                leakEC ec δ Q -
              retainedSiftedPEAnnounceIdealKeyAndAbortChannel n m ℓ ℓEV eveDim peSel xSel
                leakEC ec δ Q).comp (measurementChannel n eveDim))
          (bb84SiftedConjChannel n eveDim peSel xSel M) *
        (Op.tensor (bb84PEAnnounceBellRelabelUnitary n m ℓ ℓEV peSel leakEC
          (bb84SiftedTwirlString peSel xSel g) πsyn) (1 : Op eveDim))ᴴ := by
  have hkey := bellTwirlKeyError_siftedTwirlString peSel xSel g
  rw [bb84SiftedConjChannel_bellTwirl_conj n eveDim peSel xSel g M]
  exact bb84SiftedPEAnnounceEveVisible_measuredDiff_bellTwirl_conj n m ℓ ℓEV eveDim peSel xSel
    leakEC ec δ Q (bb84SiftedTwirlString peSel xSel g) πsyn (by rw [hkey]; exact hsyn)
    (by rw [hkey]; exact hdec) _

/-! ## The general-`m` announcement register preserves trace norm

These carry **no** relabel unitary: the announcement appends the rank-one projector `|π⟩⟨π|` on the
`n!` public-permutation register, and the relabel `bb84PEAnnounceBellRelabelUnitary` is an operator
on the base register `Fin (bb84PEAnnounceBaseOutputDim …)`, left of it.  The generic pieces
(`appendSingleLinear`, `mapTensorId_appendSingleLinear`, `traceNorm_mapTensorId_castDimLinear`,
`traceNorm_tensor_single_diag`, `prodAssocFin`, `mapTensorId_mapTensorIdLinear_reassoc`) are
dimension-generic and are reused verbatim. -/

/-- `bb84SiftedPEAnnounceLinear … π` is the dimension cast of "append the rank-one announcement
projector". -/
lemma bb84SiftedPEAnnounceLinear_eq_castDimLinear_comp_appendSingle {n m : ℕ} [NeZero n]
    (ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n)) :
    bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π =
      (Op.castDimLinear (bb84PEAnnounceBaseOutputDim_tensor_eq n m ℓ ℓEV peSel leakEC)).comp
        (appendSingleLinear (a := bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
          (permAnnounceIndexEquiv n π)) := by
  apply LinearMap.ext
  intro A
  simp only [LinearMap.comp_apply, bb84SiftedPEAnnounceLinear, LinearMap.coe_mk,
    AddHom.coe_mk, appendSingleLinear, Op.castDimLinear]
  rw [permAnnounceProjector_eq_single']

/-- The retained-Eve general-`m` announcement as a `castDim` of the projector-append
`mapTensorId`. -/
lemma bb84SiftedPEAnnounceLinearEveVisible_eq_mapTensorId_castDim_append
    {n m ℓ ℓEV eveDim : ℕ} [NeZero n] [NeZero eveDim] (peSel : Fin n → Bool) (leakEC : ℕ)
    (π : Equiv.Perm (Fin n))
    (M : Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim)) :
    haveI : NeZero (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
      ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
        (NeZero.ne _)⟩
    haveI : NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * n.factorial) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (Nat.factorial_ne_zero n)⟩
    bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π M =
      mapTensorId
        (Op.castDimLinear (bb84PEAnnounceBaseOutputDim_tensor_eq n m ℓ ℓEV peSel leakEC))
        (mapTensorId
          (appendSingleLinear (a := bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC)
            (permAnnounceIndexEquiv n π)) M) := by
  haveI : NeZero (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (NeZero.ne _)⟩
  haveI : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
  haveI : NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * n.factorial) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  rw [show bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π M =
      mapTensorId (bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π) M from rfl,
    bb84SiftedPEAnnounceLinear_eq_castDimLinear_comp_appendSingle, ← mapTensorId_comp]

/-- **The general-`m` retained-Eve announcement preserves trace norm.** -/
theorem bb84_announceLinearEveVisible_traceNorm_eq {n m ℓ ℓEV eveDim : ℕ} [NeZero n]
    [NeZero eveDim] (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n))
    (A0 : Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim)) :
    traceNorm (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π A0) =
      traceNorm A0 := by
  haveI : NeZero (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (NeZero.ne _)⟩
  haveI : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
  haveI : NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * n.factorial) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  rw [bb84SiftedPEAnnounceLinearEveVisible_eq_mapTensorId_castDim_append peSel leakEC π,
    traceNorm_mapTensorId_castDimLinear, mapTensorId_appendSingleLinear,
    traceNorm_submatrix_equiv, traceNorm_tensor_single_diag]

/-- Threading the substate-extraction register `dimR` through the general-`m` announcement is the
general-`m` announcement over the combined register `eveDim * dimR`, up to the associativity
reindex. -/
lemma bb84SiftedPEAnnounceLinearEveVisible_mapTensorId_reassoc {n m ℓ ℓEV eveDim dimR : ℕ}
    [NeZero n] [NeZero eveDim] [NeZero dimR] [NeZero (eveDim * dimR)]
    (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n))
    (W : Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim * dimR)) :
    mapTensorId (k := dimR)
        (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π) W =
      (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV (eveDim * dimR) peSel leakEC π
        (W.submatrix
          (prodAssocFin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) eveDim dimR)
          (prodAssocFin (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC) eveDim
            dimR))).submatrix
        (prodAssocFin (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC)
          eveDim dimR).symm
        (prodAssocFin (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC)
          eveDim dimR).symm := by
  haveI : NeZero (2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (NeZero.ne _)⟩
  haveI : NeZero (bb84PEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC * eveDim) :=
    bb84EveVisiblePEAnnounceBaseOutputDim_neZero n m ℓ ℓEV peSel leakEC eveDim
  haveI : NeZero ((2 ^ ℓ * 2 ^ ℓ * bb84SymPEAnnounceTranscriptDim n m ℓ ℓEV peSel leakEC) *
      eveDim) :=
    bb84EveVisiblePEAnnounceSymOutputDim_neZero n m ℓ ℓEV peSel leakEC eveDim
  exact mapTensorId_mapTensorIdLinear_reassoc
    (bb84SiftedPEAnnounceLinear n m ℓ ℓEV peSel leakEC π) W

/-- **Threading the substate-extraction register `dimR` through a single retained-Eve general-`m`
announcement preserves trace norm**: `‖(announce_π ⊗ id_R)(W)‖₁ = ‖W‖₁`. -/
theorem bb84_announceLinearEveVisible_mapTensorId_traceNorm_eq
    {n m ℓ ℓEV eveDim dimR : ℕ} [NeZero n] [NeZero eveDim] [NeZero dimR] [NeZero (eveDim * dimR)]
    (peSel : Fin n → Bool) (leakEC : ℕ) (π : Equiv.Perm (Fin n))
    (W : Op (bb84EveVisiblePEAnnounceBaseOutputDim n m ℓ ℓEV peSel leakEC eveDim * dimR)) :
    traceNorm (mapTensorId (k := dimR)
        (bb84SiftedPEAnnounceLinearEveVisible n m ℓ ℓEV eveDim peSel leakEC π) W) =
      traceNorm W := by
  rw [bb84SiftedPEAnnounceLinearEveVisible_mapTensorId_reassoc peSel leakEC π W,
    traceNorm_submatrix_equiv, bb84_announceLinearEveVisible_traceNorm_eq,
    traceNorm_submatrix_equiv]

/-! ## Canonical-split bridges

`bb84KeyRoundCount n ⌈n/2⌉` reduces to `bb84KeyRoundCountCanonical n`, so each pinned object of
`PEAnnounceRelabel.lean` is the `m = ⌈n/2⌉` instance of its general-`m` form, definitionally. -/

end QKD.BB84.Engine

end
