import QCryptLean.QKD.BB84.ClassicalData
import QCryptLean.QKD.BB84.Model.PEAnnouncement
import QCryptLean.QKD.BB84.Model.DePaddedQuantumStack

-- Several of the module paths above exceed 100 characters; this is the same suppression
-- `QCryptLean/QKD/BB84/Model/BB84Bridge.lean` already carries for the same imports.

/-!
# The classical layer of BB84: its register dictionary and announced digits

`BB84Bridge.lean` reduces the headline channel to `QKD.BB84.Model.bb84RealProtocolMapBare` —
measure, then privacy-amplify-or-abort.  This module reads BB84's data off the two laboratory
registers, names the digit each classical step announces, and proves the index arithmetic
identifying the announced transcript with the output index.

## The peeling

`bb84.retainedSiftedPEAnnouncePassBranchKraus` and its fail twin are **single-entry** Kraus
operators: on a computational-basis input `ω` they write one output index
`(kA, kB, flag, st, evTag, syn, p)`. The steps below produce exactly those digits, one at a time,
each reading one party's own register plus what has already been announced.

| # | step | party | mode | digit |
|---|---|---|---|---|
| 1 | computational measurement | A | private | — |
| 2 | computational measurement | B | private | — |
| 3.j.a | announce Bob's PE bit of the `j`-th sorted PE round | B | announced | `2j` |
| 3.j.b | announce Alice's PE bit of the `j`-th sorted PE round | A | announced | `2j+1` |
| 4 | draw the seed pair, announce `(st, evTag, syn)` | A | announced | `2m` |
| 5 | announce the accept flag | B | announced | `2m+1` |
| 6 | hash-and-forget Alice's key | A | private | — |
| 7 | decode-hash-and-forget Bob's key | B | private | — |

The **first-executed** announced outcome occupies the **lowest** transcript digit, so the table's
digit column is the execution order read backwards, and the resulting transcript is
`flag | st | evTag | syn | p` high-to-low: exactly the layout.

Three design points are load-bearing.

* **The PE block is announced one round at a time, Bob's bit before Alice's.** The block
  `p = finFunctionFinEquiv (bb84PartEquiv peSel ω).2` *interleaves* the two parties' bits per round
  (`ω i = 2·aliceBit + bobBit`), whereas two block announcements of `Fin (2^m)` each would
  *concatenate* them. Interleaving is not a relabelling of concatenation, so announcing the block
  in one piece per party would force a nontrivial permutation of the output register into the
  bridge's relabelling. With `2m` single-bit announcements the transcript value **is** `p` on the
  nose.
* **`(st, evTag, syn)` is one fused Alice step.** `evTag` reads the error-verification seed
  (the second component of `st`),
  so it cannot be announced before `st`; but it sits *below* `st` in the digit order, so
  as separate steps it would have to be announced *first*. Fusing the three into a single Alice
  alphabet removes the clash.
* **The accept flag is Bob's.** Its error-verification conjunct compares Alice's announced tag with
  the tag of Bob's syndrome-decoded string, and only Bob holds that string.

## The count hypothesis, and why it is not optional

`bb84SiftedLocalPETestPassed` filters over **every** round with `peSel i = true`, while the
announced PE block carries `ω` only at the `m = n - bb84KeyRoundCountCanonical n` sorted positions
`bb84PERoundIdxCanonical peSel j`. Those cover every PE round exactly when `bb84KeyCount peSel`
holds (`bb84_peRound_eq_peIdx` is stated *with* that hypothesis). Without it some PE round is
invisible to every announced digit while the accept flag still reads it, and the flag becomes the
equality function of two bits neither party can see — which no two-party experiment reproduces. It
is free where the chain uses it: the headlines instantiate at `bb84CanonicalPESelector n`, for which
`bb84KeyCount` is a proved lemma.

## Main definitions

- `QKD.BB84.Model.jointOutcome`, `QKD.BB84.Model.aliceKeyString_jointOutcome` and twins: BB84's
  data, read off the two registers.

The instruments the announced steps are built from — `LOCC.pinnedReadout`, `LOCC.seededReadout`
and `LOCC.hashForget` — mention no BB84 object. Their Kraus formulas and computational-basis
column laws are declared in `ClassicalInstruments.lean`.

## Main results

- `QKD.BB84.Model.roundGroupEquiv_symm_finProd`: the register dictionary — the round regrouping
  carries the product basis vector of the two parties' registers to the joint-outcome basis
  vector of the signal register.
- `QKD.BB84.Model.evTagSynOf_eq`: the fused announcement, computed.
-/
open Equiv

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Quantum.Channels Matrix
open Math.RepresentationTheory InfoTheory.Postselection QKD.BB84.Engine
open LOCC
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Model

/-! ## Reading BB84's data off the two registers

Everything the classical layer needs is a function of **one** party's register plus values already
announced. This section says which function, and ties each to the object it must
reproduce. -/

/-- The round-outcome string a pair of computational-basis registers determines: round `k` carries
Alice's bit high and Bob's low, which is `aliceBit`/`bobBit`'s own encoding. -/
def jointOutcome (n : ℕ) (x y : Fin (2 ^ n)) : Fin n → Fin signalDim :=
  fun k => finProdFinEquiv (registerBit n k x, registerBit n k y)

theorem aliceBit_jointOutcome (n : ℕ) (x y : Fin (2 ^ n)) (k : Fin n) :
    aliceBit (jointOutcome n x y k) = registerBit n k x := by
  have h := finProdFinEquiv_aliceBit_bobBit (jointOutcome n x y k)
  have h2 : (aliceBit (jointOutcome n x y k), bobBit (jointOutcome n x y k)) =
      (registerBit n k x, registerBit n k y) := finProdFinEquiv.injective h
  exact congrArg Prod.fst h2

theorem bobBit_jointOutcome (n : ℕ) (x y : Fin (2 ^ n)) (k : Fin n) :
    bobBit (jointOutcome n x y k) = registerBit n k y := by
  have h := finProdFinEquiv_aliceBit_bobBit (jointOutcome n x y k)
  have h2 : (aliceBit (jointOutcome n x y k), bobBit (jointOutcome n x y k)) =
      (registerBit n k x, registerBit n k y) := finProdFinEquiv.injective h
  exact congrArg Prod.snd h2

/-- **The register dictionary.** The round regrouping carries the product basis vector `|x⟩|y⟩` of
the two parties' registers to the joint-outcome basis vector `|ω(x,y)⟩` of the signal register.
This is the one place the bridge's input `reindex` is used. -/
theorem roundGroupEquiv_symm_finProd (n : ℕ) (x y : Fin (2 ^ n)) :
    (roundGroupEquiv 2 2 n).symm (finProdFinEquiv (x, y)) =
      finFunctionFinEquiv (jointOutcome n x y) := by
  have h := finFunctionFinEquiv_symm_roundGroupEquiv_symm (dA := 2) (dB := 2) (n := n)
    (finProdFinEquiv (x, y))
  have h2 : (roundGroupEquiv 2 2 n).symm (finProdFinEquiv (x, y)) =
      finFunctionFinEquiv (finFunctionFinEquiv.symm
        ((roundGroupEquiv 2 2 n).symm (finProdFinEquiv (x, y)))) := by
    rw [Equiv.apply_symm_apply]
  rw [h2, h]
  refine congrArg finFunctionFinEquiv (funext fun k => ?_)
  simp only [Equiv.symm_apply_apply, jointOutcome, registerBit]

theorem aliceKeyString_jointOutcome (n : ℕ) (peSel : Fin n → Bool) (x y : Fin (2 ^ n)) :
    aliceKeyString peSel (jointOutcome n x y) = aliceKeyOf n peSel x :=
  funext fun i => aliceBit_jointOutcome n x y i.val

theorem bobKeyString_jointOutcome (n : ℕ) (peSel : Fin n → Bool) (x y : Fin (2 ^ n)) :
    bobKeyString peSel (jointOutcome n x y) = bobKeyOf n peSel y :=
  funext fun i => bobBit_jointOutcome n x y i.val

/-! ## The map, on a basis projector

The two branch Kraus operators are single-entry, so the whole privacy-amplification/abort map is a
classical kernel: on `|c⟩⟨c|` it writes one output index per announced seed pair. The two
`Op.castDim (Nat.mul_one _)` paddings of the unit Eve slot are absorbed by the value-preserving
`finProdFinEquiv (·, 0)`. -/

/-- Conjugating a basis projector by a single-entry Kraus operator. -/
theorem singleKraus_conj_single {p q : ℕ} (u : Fin q) (v d : Fin p) :
    Matrix.single u v (1 : ℂ) * Matrix.single d d (1 : ℂ) * (Matrix.single u v (1 : ℂ))ᴴ =
      if d = v then Matrix.single u u (1 : ℂ) else 0 := by
  by_cases h : d = v
  · subst h
    rw [ite_eq_left rfl]
    have := krausConj_single_of_col (Matrix.single u d (1 : ℂ)) d u 1
      (fun i => by simp [Matrix.single_apply, eq_comm])
    simp only [star_one, one_mul, one_smul] at this
    exact this
  · rw [ite_eq_right h]
    exact krausConj_single_of_col_zero _ _ (fun i => by simp [Ne.symm h])

/-- The unit-Eve padding is the value-preserving `(·, 0)` embedding. -/
theorem castDim_mul_one_symm_eq (N : ℕ) (c : Fin N) :
    Fin.cast (Nat.mul_one N).symm c = finProdFinEquiv (c, (0 : Fin 1)) :=
  Fin.ext (by simp)

/-! ## The parameter-estimation test, from the announced bits alone

This is the one place `bb84KeyCount peSel` is used, and the one place it is needed.
`bb84SiftedLocalPETestPassed` filters over **every** PE round; the announced block carries only the
`m` sorted rounds `bb84PERoundIdxCanonical peSel j`. Under the count hypothesis the sorted rounds
are exactly the PE rounds (`bb84PERoundIdx_isPE` one way, `bb84_peRound_eq_peIdx` the other), so the
two agree. Without it a PE round is invisible to every announced digit, and the flag becomes a
function of a bit neither party holds. -/

/-- A round disagrees exactly when the two parties' bits on it differ — the `{1, 2}` disagreement
set of the local frame, read on the two registers. -/
theorem jointOutcome_disagree_iff (n : ℕ) (x y : Fin (2 ^ n)) (i : Fin n) :
    (jointOutcome n x y i = 1 ∨ jointOutcome n x y i = 2) ↔
      registerBit n i x ≠ registerBit n i y := by
  have key : ∀ a b : Fin 2,
      ((finProdFinEquiv (a, b) : Fin signalDim) = 1 ∨
        (finProdFinEquiv (a, b) : Fin signalDim) = 2) ↔ a ≠ b := by decide
  exact key (registerBit n i x) (registerBit n i y)

/-! ## The measurement prefix, and the accept flag against the gate -/

/-- Sandwiching by a basis projector reads one diagonal entry. -/
theorem single_conj_general {N : ℕ} (d : Fin N) (M : Op N) :
    Matrix.single d d (1 : ℂ) * M * Matrix.single d d (1 : ℂ) =
      M d d • Matrix.single d d (1 : ℂ) := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  have hrow : ∀ a : Fin N, (M * Matrix.single d d (1 : ℂ)) a j =
      if j = d then M a d else 0 := by
    intro a
    rw [Matrix.mul_apply]
    by_cases hj : j = d
    · subst hj
      simp [Matrix.single_apply]
    · simp [hj, Ne.symm hj]
  simp_rw [hrow]
  simp only [mul_ite, mul_zero]
  by_cases hj : j = d
  · subst hj
    simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hi : i = j
    · subst hi
      simp
    · simp [Ne.symm hi]
  · simp [hj, Matrix.smul_apply, Ne.symm hj]

/-! ## The output index, as a value

The bridge's relabelling is a `finCongr`, so the whole match reduces to one identity between two
natural numbers: the transcript the program writes and the
`bb84.pePassOutIndex` / `bb84.peFailOutIndex`.

The value of a packed pair — "the second component is the low digit" — is
`Quantum.TensorProducts.finProdFinEquiv_val`, which this namespace's `open LOCC` brings into scope
under a bare name; no local re-declaration should shadow it. -/

theorem evTagSynOf_eq (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (r : Fin (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) (x : Fin (2 ^ n)) :
    evTagSynOf n ℓ ℓEV peSel leakEC ec r x =
      finProdFinEquiv
        (verificationTag n ℓEV peSel (announcedSeed n ℓ ℓEV peSel r).2 (aliceKeyOf n peSel x),
          ec.syndrome (aliceKeyOf n peSel x)) := rfl

end QKD.BB84.Model

end
