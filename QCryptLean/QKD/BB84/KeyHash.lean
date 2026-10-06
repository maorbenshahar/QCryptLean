import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.InfoTheory.QuantumLHL.BinaryInnerProductHash
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.Math.ClassicalEntropy.HammingBall

/-!
# BB84 key hashing and the error-verification tag

The privacy-amplification key hash and the error-verification tag, both instances of the
protocol-independent binary inner-product hash family in the InfoTheory.QuantumLHL module, at the
key-round bit-string domain `KeyBitString n peSel`.

## Main definitions
- `KeyHashSeed`: seed type for the binary key-round inner-product hash, an `ℓ × n_K` matrix over
  `Fin 2`.
- `binaryInnerProductHash`: the binary inner-product hash on key-round bit strings, specializing
  `InfoTheory.QuantumLHL.binaryInnerProductHash` to the key-round domain.
- `aliceKeyHashFamily`: the binary Carter–Wegman inner-product hash family on Alice's key-round bit
  domain. This REPLACES a joint Alice∧Bob outcome hash — the key is a function of Alice's bits
  alone (Bob reconstructs his copy by decoding against Alice's announced syndrome, `ECScheme`).
- `KeyHashSeedPairEV`: the announced public randomness of a BB84 run — the privacy-amplification
  seed paired with the error-verification seed.
- `verificationTag`: Alice's announced error-verification tag, the `ℓEV`-bit hash of her key
  string.
- `evVerified`: the error-verification gate — Alice's tag against the tag of Bob's
  syndrome-decoded string.

## Main statements
- `aliceKeyHashFamily_isUniversal2Star`: **exact** `2*`-universality of the binary key
  hash (specializes `InfoTheory.QuantumLHL.binaryInnerProductHashFamily_isUniversal2Star`). This is
  the form the collision-route privacy amplification
  (`seedKeyExtractor_traceDistanceGen_le_collisionRoot`) consumes.
- `aliceKeyHashFamily_isUniversal`: the `≤`-form 2-universality corollary.
- `binaryInnerProductHash_add_right` / `verificationTag_add_right`: translation covariance
  of the key hash and of the error-verification tag, at the explicit permutation
  `binaryInnerProductHashShiftPerm`.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C (error correction
with `λEC(Fobs)` bits followed by error verification comparing hash values of length
`log(1/ε_EV)`); Renner 2005 §6.5; Carter–Wegman 1979.
-/

open InfoTheory.QuantumLHL

noncomputable section

namespace QKD.BB84

/-- Seed type for the binary key-round inner-product hash: an `ℓ × n_K` matrix over `Fin 2`,
one linear functional (row) per output bit over the key-round bit domain. -/
abbrev KeyHashSeed (n ℓ : ℕ) (peSel : Fin n → Bool) : Type :=
  Fin ℓ → KeyBitString n peSel

/-- Binary inner-product hash on key-round bit strings: output bit `j` is
`(∑ key rounds i, A_j_i · x_i) mod 2`, the `ℓ` bits packed into `Fin (2 ^ ℓ)`. The Carter–Wegman
construction on the key-round bit domain — the single-party functional that replaces a joint
Alice∧Bob outcome hash. Specializes `InfoTheory.QuantumLHL.binaryInnerProductHash` at
`I := KeyBitString n peSel`. -/
def binaryInnerProductHash (n ℓ : ℕ) (peSel : Fin n → Bool)
    (A : KeyHashSeed n ℓ peSel) (x : KeyBitString n peSel) : Fin (2 ^ ℓ) :=
  InfoTheory.QuantumLHL.binaryInnerProductHash ℓ A x

/-- **Alice's binary key hash family**: the Carter–Wegman binary inner-product family over
key-round bit strings, seed uniform over the `ℓ × n_K` bit matrices. This REPLACES a joint
Alice∧Bob outcome hash as the key family — the key is now a function of Alice's bits alone (Bob
reconstructs his copy by decoding against Alice's announced syndrome, see `ECScheme`), not of the
joint Alice∧Bob outcome. -/
def aliceKeyHashFamily (n ℓ : ℕ) (peSel : Fin n → Bool) :
    QuantumHashFamily (KeyHashSeed n ℓ peSel) (KeyBitString n peSel) (Fin (2 ^ ℓ)) :=
  InfoTheory.QuantumLHL.binaryInnerProductHashFamily {i : Fin n // peSel i = false} ℓ

/-- **The announced public randomness of a BB84 run**: the privacy-amplification seed
(`KeyHashSeed n ℓ peSel`, output length `ℓ`) paired with the error-verification seed
(`KeyHashSeed n ℓEV peSel`, output length `ℓEV`). Both are drawn uniformly and announced; the
channel averages over the pair with the single Kraus scale
`1 / Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel)`.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C: privacy amplification and
error verification each consume their own announced hash choice. -/
abbrev KeyHashSeedPairEV (n ℓ ℓEV : ℕ) (peSel : Fin n → Bool) : Type :=
  KeyHashSeed n ℓ peSel × KeyHashSeed n ℓEV peSel

/-- **Alice's announced error-verification tag**: the `ℓEV`-bit Carter–Wegman inner-product hash of
her key string under the error-verification seed `t`.

This is the same binary hash construction as the privacy-amplification key, instantiated at output
length `ℓEV`; its collision fraction on distinct inputs is exactly `2 ^ (−ℓEV)`
(`aliceKeyHashFamily_isUniversal n ℓEV peSel`, which is an exact halving per seed row, not
merely a bound).

Nahar et al. 2024 (arXiv:2403.11851) §V.C: "error-verification by comparing hash values of length
`log(1/ε_EV)`". -/
def verificationTag (n ℓEV : ℕ) (peSel : Fin n → Bool)
    (t : KeyHashSeed n ℓEV peSel) (x : KeyBitString n peSel) : Fin (2 ^ ℓEV) :=
  binaryInnerProductHash n ℓEV peSel t x

/-- **Exact (`2*`-universality) of the binary key hash family.**

For any two distinct key strings `x ≠ x' : KeyBitString n peSel`, the number of seeds on which
they collide, times the output alphabet size `2 ^ ℓ`, equals the seed-count **exactly**.

The exact form is what the collision-route privacy amplification consumes:
`seedKeyExtractor_traceDistanceGen_le_collisionRoot` takes `IsUniversal2Star`, not the weaker
`isUniversal`, because the centred off-diagonal coefficient must vanish *exactly*
(`QuantumHashFamily.IsUniversal2Star.centred_second_moment`). -/
theorem aliceKeyHashFamily_isUniversal2Star (n ℓ : ℕ) (peSel : Fin n → Bool) :
    (aliceKeyHashFamily n ℓ peSel).IsUniversal2Star :=
  InfoTheory.QuantumLHL.binaryInnerProductHashFamily_isUniversal2Star
    {i : Fin n // peSel i = false} ℓ

/-- **2-universality of the binary key hash family.**

For any two distinct key strings `x ≠ x' : KeyBitString n peSel`:
`Pr_{A uniform}[hash A x = hash A x'] ≤ 1 / 2^ℓ`.

The `≤`-form corollary of the exact statement `aliceKeyHashFamily_isUniversal2Star`. -/
theorem aliceKeyHashFamily_isUniversal (n ℓ : ℕ) (peSel : Fin n → Bool) :
    (aliceKeyHashFamily n ℓ peSel).isUniversal :=
  (aliceKeyHashFamily_isUniversal2Star n ℓ peSel).isUniversal

/-- **The error-verification gate.** Alice announces `verificationTag n ℓEV peSel t
    (aliceKeyString ω)`;
Bob recomputes the tag of his syndrome-decoded string and the protocol accepts iff the two agree.

Because the seed `t` is drawn uniformly and independently of the round outcomes, and neither
`ec.decode` nor ec.syndrome can read `t` (`ECScheme` has no seed field), the joint probability that
the two key strings **differ** and the gate nonetheless accepts is at most `2 ^ (−ℓEV)` for every
input state — the joint (never conditional) correctness bound of
`InfoTheory.Postselection.ErrorVerification.errorVerification_joint_correctness_indexed` at the
exactly universal family `aliceKeyHashFamily n ℓEV peSel`. The conditional form `Pr[differ |
accept]` is NOT bounded (`conditional_correctness_fails` in the same file proves it false), so the
charge must always be taken jointly.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C "Classical part"
(main.tex:906–919, the error-verification-by-hash-comparison step at main.tex:917). -/
def evVerified {n : ℕ} (ℓEV : ℕ) (peSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (t : KeyHashSeed n ℓEV peSel)
    (ω : Fin n → Fin signalDim) : Bool :=
  decide (verificationTag n ℓEV peSel t (aliceKeyString peSel ω) =
    verificationTag n ℓEV peSel t
      (ec.decode (bobKeyString peSel ω) (ec.syndrome (aliceKeyString peSel ω))))

/-- **The shift of the key-hash argument, realised on the packed codomain as an explicit
permutation.** Specializes `InfoTheory.QuantumLHL.binaryInnerProductHashShiftPerm` at
`I := KeyBitString n peSel`. -/
def binaryInnerProductHashShiftPerm {n ℓ : ℕ} {peSel : Fin n → Bool}
    (A : KeyHashSeed n ℓ peSel) (e : KeyBitString n peSel) : Equiv.Perm (Fin (2 ^ ℓ)) :=
  InfoTheory.QuantumLHL.binaryInnerProductHashShiftPerm A e

/-- **Translation covariance of the binary key hash.** Shifting the hashed string by `e` relabels
the hash value by the permutation `binaryInnerProductHashShiftPerm A e`, uniformly in the string.
This is clause (i) of `ECScheme.IsTranslationEquivariant` for every `𝔽₂`-linear syndrome. -/
theorem binaryInnerProductHash_add_right {n ℓ : ℕ} {peSel : Fin n → Bool}
    (A : KeyHashSeed n ℓ peSel) (e x : KeyBitString n peSel) :
    binaryInnerProductHash n ℓ peSel A (x + e)
      = binaryInnerProductHashShiftPerm A e (binaryInnerProductHash n ℓ peSel A x) :=
  InfoTheory.QuantumLHL.binaryInnerProductHash_add_right A e x

/-- **Translation covariance of Alice's error-verification tag** — the same construction at output
length `ℓEV`. -/
theorem verificationTag_add_right {n ℓEV : ℕ} {peSel : Fin n → Bool}
    (t : KeyHashSeed n ℓEV peSel) (e x : KeyBitString n peSel) :
    verificationTag n ℓEV peSel t (x + e)
      = binaryInnerProductHashShiftPerm t e (verificationTag n ℓEV peSel t x) :=
  binaryInnerProductHash_add_right t e x

end QKD.BB84

end
