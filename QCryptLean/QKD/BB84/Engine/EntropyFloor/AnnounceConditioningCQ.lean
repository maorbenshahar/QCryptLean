import QCryptLean.QKD.BB84.Engine.EntropyFloor.SiftedRoundFactorizationReferee
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Engine.EntropyFloor.ClassicalAnnounceKernel
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQState.FilterKeepContraction

/-!
# Announce-conditioned, coarsened CQ states: the announcement stays on the quantum side

The classical announcements of the BB84 privacy-amplification chain — the error-correction
syndrome, the error-verification tag, and the parameter-estimation outcome block — are carried
into the **conditioning (quantum) register** of a CQ state and are kept there when the classical
register is coarsened to the key rounds.  They are never traced out.

## Why the order is `coarsen ∘ tensorLeftKernel` and not the reverse

`bb84AnnounceCoarsenCQ` applies the announce kernel **first** and coarsens **second**.  The
`y`-block of the result is

`A_y = ∑_{ω : g ω = y} |ann ω⟩⟨ann ω| ⊗ ρ_ω`,

which is block diagonal in the announcement register: distinct announcement values land on
orthogonal `|a⟩⟨a|` subspaces, so the `(a,a)` diagonal block of `A_y` is exactly the fiber sum
`∑_{ω : g ω = y, ann ω = a} ρ_ω`.  The coarsening therefore reduces the *secret* register to the
key rounds while losing nothing about the announcement.  Coarsening first (or, equivalently,
tracing the announcement register out afterwards) collapses those orthogonal blocks into their
sum `∑_{ω : g ω = y} ρ_ω` and destroys the announcement.

That distinction is quantitative and it is the reason this object exists.  Writing
`real = ∑_a |a⟩⟨a| ⊗ R_a`, `ideal = ∑_a |a⟩⟨a| ⊗ I_a`, one has
`∑_y ‖A_y − B_y‖₁ = ∑_{y,a} ‖R_{y,a} − I_{y,a}‖₁ ≥ ∑_y ‖Tr_ann(A_y − B_y)‖₁`, strictly at a
generic point.  A statement whose left-hand side writes the announcement into the transcript while
its right-hand side coarsens the announcement away asserts that inequality backwards, i.e. the
data-processing inequality backwards; the exact counterexample has left-hand side `1` and
right-hand side `1/2`.  The construction here keeps the announcement on the quantum side so that
no such reversal is needed.

## Register orientation: announcements HIGH

The kernel is `CQState.tensorLeftKernel`, not `CQState.tensorRightKernel`.  `Op.tensor A B` places
`A` in the high digit, so the left kernel puts the announcement in the **high** digits,
`d_ann * dE`.  That is the layout the transcript index `bb84.pePassOutIndex`
(`SiftedPEAnnounce.lean`) fixes, and it is the orientation in which the announce charge
`InfoTheory.SmoothMinEntropy.bb84_smoothMinEntropy_announce_ge_sub_leak` is stated.

## What the announcements cost — `(syn, evTag)` and `pe` are different cases

* `syn = ec.syndrome (aliceKeyString peSel ω)` and
  `evTag = verificationTag n ℓEV peSel t (aliceKeyString peSel ω)` are functions of
  Alice's **key-round** bits, hence measurable with respect to the coarsened register.  They are
  charged `leakEC + ℓEV` bits by
  `InfoTheory.SmoothMinEntropy.smoothMinEntropy_tensorLeftKernel_ge_sub_log`, instantiated at
  `bb84AnnounceKernel`.  Being key-measurable does **not** make them droppable: they are still
  side information about the secret, and the one-sided `log|C|` charge is exactly what the
  protocol's key-rate budget funds.
* `pe`, the announced PE-outcome block, is **not** key-round measurable.  It attaches at the
  ω-register and is neither free nor chargeable that way.  The decoupled-ancilla seam
  `InfoTheory.SmoothMinEntropy.smoothMinEntropy_le_condTensor_decoupled_ancilla`
  (`ExtensionPenalty.lean`) needs an `x`-independent `τ` and fails at the mixture level, where the
  PE block becomes `σ`-correlated; the maximally-mixed extension route would cost `2m = Θ(n)` bits
  and destroy the rate.  The decoupled-ancilla seam applies instead **per Carathéodory point**,
  where `τ` is the PE-round product's own quantum marginal and is genuinely key-independent,
  followed by Nahar et al. Lemma 14 / `\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), which
  takes an **infimum over the components** — not a log-charge.  This file supplies the register
  object; the entropy statement is not made here.

## `filterKeep` legality

`CQState.filterKeep` (`CQState/FilterKeepContraction.lean`) takes `keep : X → Bool`, a predicate on
the classical index alone, and every one of its contraction lemmas is stated at that generality.
The accept gate `bb84SiftedLocalPEAndEVPassed` reads the announced seed `t` as well as `ω`, so it
is **not** a legal `keep`.  On the agree event — where Alice's key string equals Bob's
syndrome-decoded string — `bb84SiftedLocalPEAndEVPassed_eq_PETestPassed_of_not_differ` collapses it
to the seed-free `bb84SiftedLocalPETestPassed`, which is legal.  Without that collapse the
agree-restricted filtered CQ state does not exist as a well-formed `filterKeep` object.

`bb84PostMeasurementCQSiftedLocalPEPassFilter_eq_filterKeep` identifies the hand-rolled filter of
`SiftedMeasurement.lean` with `CQState.filterKeep` at the PE-only predicate, so the
filter route in this lane is `CQState.filterKeep` throughout and the hand-rolled declaration is a
notation for it rather than a second implementation.

## Main definitions
- `bb84AnnounceCoarsenCQ`: announce kernel then classical coarsening, on a BB84 outcome-indexed CQ
  state.
- `bb84AliceKeyAnnounceCQ`: the instance at the Alice-key-bit coarsening `aliceKeyString`,
  the register `aliceKeyHashFamily` hashes.
- `bb84SiftedAgreeAcceptKeep`: the seed-free agree-and-PE-accept keep predicate, phrased at the
  differ predicate `bb84SiftedKeyStringsDiffer` (`KeyHashEC.lean`).

## Main results
- `bb84AnnounceCoarsenCQ_stateMap`: the blockwise form of the announce-coarsened state.
- `bb84_evVerified_of_keyStrings_eq`, `bb84_evVerified_of_not_differ`: agreeing (equivalently,
  non-differing) key strings pass error verification, for every seed.
- `bb84SiftedLocalPEAndEVPassed_eq_PETestPassed_of_not_differ`: the seed-dependent accept gate
  collapses to the seed-free PE test on the agree event.
- `bb84PostMeasurementCQSiftedLocalPEPassFilter_eq_filterKeep`: the PE pass filter is
  `CQState.filterKeep`.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) App. B
(main.tex:1341–:1413 (Appendix B's proof of Theorem 3: the accept-block split `\label{eq:tausplit}`
(main.tex:1356–:1362), the Hoeffding/purified-distance steps main.tex:1364–:1378, the smoothed
min-entropy bound `\label{eq:boundingsmoothedmin}` (main.tex:1379–:1387), the register-splitting
step `\label{eq:splittingoffV}` (main.tex:1393–:1396), closing at main.tex:1411–:1413)) and §V.C
(announced syndrome, error-verification tag); Renner 2005 (arXiv:quant-ph/0512258v2) §6.5 and Lemma
3.1.10 / Cor. 3.1.11 (classical side information, one-sided `log|C|`). -/

open Quantum.Operators Quantum.TensorProducts Matrix
open InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder BigOperators
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-! ## The announce-then-coarsen constructor -/

/-- **Announce kernel first, classical coarsening second.**

Starting from a CQ state `ρ` indexed by full BB84 outcome strings, tensor every block on the
**left** by the announcement projector `|ann ω⟩⟨ann ω|` (announcement in the high digits) and then
push the classical register forward along `g`.

The `y`-block is `∑_{ω : g ω = y} |ann ω⟩⟨ann ω| ⊗ ρ_ω` — block diagonal in the announcement
register, so the announcement survives the coarsening on the quantum side while the classical
register is reduced to `Ycl`.  See the module docstring for why the reverse order (or tracing the
announcement out afterwards) is a strictly weaker object. -/
def bb84AnnounceCoarsenCQ {n dE dAnn : ℕ} {Ycl : Type*} [Fintype Ycl] [DecidableEq Ycl]
    (g : (Fin n → Fin signalDim) → Ycl)
    (ann : (Fin n → Fin signalDim) → Fin dAnn)
    (ρ : CQState (Fin n → Fin signalDim) dE) : CQState Ycl (dAnn * dE) :=
  CQState.coarsen g (ρ.tensorLeftKernel fun ω => stdProj dAnn (ann ω))

/-- **The blockwise form of the announce-coarsened state.**  Fiberwise sum of announcement-tagged
blocks; the summands at distinct announcement values are supported on orthogonal `|a⟩⟨a|`
subspaces of the high register. -/
theorem bb84AnnounceCoarsenCQ_stateMap {n dE dAnn : ℕ} {Ycl : Type*} [Fintype Ycl] [DecidableEq Ycl]
    (g : (Fin n → Fin signalDim) → Ycl)
    (ann : (Fin n → Fin signalDim) → Fin dAnn)
    (ρ : CQState (Fin n → Fin signalDim) dE) (y : Ycl) :
    ((bb84AnnounceCoarsenCQ g ann ρ).stateMap y).toOp =
      ∑ ω : Fin n → Fin signalDim,
        if g ω = y then (stdProj dAnn (ann ω)).toOp ⊗ (ρ.stateMap ω).toOp else 0 :=
  rfl

/-! ## The two BB84 coarsenings -/

/-- **The announce-conditioned, Alice-key-bit-coarsened CQ state.**

`bb84AnnounceCoarsenCQ` at the Alice key-string map `aliceKeyString peSel`
(`KeyHashEC.lean`): the classical register is `KeyBitString n peSel`, Alice's key-round bits,
which is the domain of `aliceKeyHashFamily` and therefore the secret register of the
privacy-amplification statement.

A coarsening to the joint key-round outcome does not substitute for it: since
`Hmin(f(X)|E) ≤ Hmin(X|E)`, a floor on the joint outcome gives nothing for Alice's bits alone.
`bb84AnnounceKernel` and `bb84_smoothMinEntropy_announce_ge_sub_leak` are stated on this
register. -/
def bb84AliceKeyAnnounceCQ {n dE dAnn : ℕ} (peSel : Fin n → Bool)
    (ann : (Fin n → Fin signalDim) → Fin dAnn)
    (ρ : CQState (Fin n → Fin signalDim) dE) :
    CQState (KeyBitString n peSel) (dAnn * dE) :=
  bb84AnnounceCoarsenCQ (aliceKeyString peSel) ann ρ

/-! ## The agree event makes the accept gate seed-free -/

/-- **Agreeing key strings pass error verification, for every seed.**

`evVerified` compares the error-verification tags of Alice's key string and of Bob's
syndrome-decoded string.  When the two strings are equal the two tags are equal by `congrArg`, so
the gate accepts whatever the announced seed `t` is.

Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C.  This is the *soundness*
direction of the error-verification gate and carries no probability; the converse — that
disagreeing strings are rejected — holds only with probability `1 − 2^(−ℓEV)` and is charged
jointly by `errorVerification_joint_correctness_indexed`. -/
theorem bb84_evVerified_of_keyStrings_eq {n ℓEV : ℕ} (peSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (t : KeyHashSeed n ℓEV peSel)
    (ω : Fin n → Fin signalDim)
    (h : aliceKeyString peSel ω =
      ec.decode (bobKeyString peSel ω)
        (ec.syndrome (aliceKeyString peSel ω))) :
    evVerified ℓEV peSel ec t ω = true := by
  unfold evVerified
  rw [← h]
  simp

/-! ## The differ-predicate forms, and the seed-free agree-and-accept keep predicate

These restate `bb84_evVerified_of_keyStrings_eq` and the accept-gate collapse above at the
`bb84SiftedKeyStringsDiffer` predicate instead of key-string equality, and give the seed-free keep
predicate they build towards. -/

/-- **Not differing implies error verification passes**, for every announced seed.

`bb84SiftedKeyStringsDiffer = false` says Alice's key string equals Bob's syndrome-decoded
string; `bb84_evVerified_of_keyStrings_eq` then gives `evVerified = true` by `congrArg` on the
error-verification tag. -/
theorem bb84_evVerified_of_not_differ {n ℓEV : ℕ} (peSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (t : KeyHashSeed n ℓEV peSel)
    (ω : Fin n → Fin signalDim)
    (h : bb84SiftedKeyStringsDiffer peSel ec ω = false) :
    evVerified ℓEV peSel ec t ω = true := by
  refine bb84_evVerified_of_keyStrings_eq peSel ec t ω ?_
  by_contra hne
  exact absurd ((bb84SiftedKeyStringsDiffer_eq_true_iff peSel ec ω).mpr hne) (by simp [h])

/-- **The accept gate is seed-free on the agree block**, phrased at the differ predicate the
Kraus split uses (`bb84RealPassAgreeKraus` / `bb84IdealPassAgreeKraus`,
`InnerBudgetPinned.lean`). -/
theorem bb84SiftedLocalPEAndEVPassed_eq_PETestPassed_of_not_differ {n ℓEV : ℕ}
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (t : KeyHashSeed n ℓEV peSel) (ω : Fin n → Fin signalDim)
    (h : bb84SiftedKeyStringsDiffer peSel ec ω = false) :
    bb84SiftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q t ω =
      bb84SiftedLocalPETestPassed peSel xSel δ Q ω := by
  unfold bb84SiftedLocalPEAndEVPassed
  rw [bb84_evVerified_of_not_differ peSel ec t ω h, Bool.and_true]

/-- **The seed-free agree-and-accept keep predicate**: the fail-closed LOCC two-basis PE test passes
and Alice's key string agrees with Bob's syndrome-decoded string.

A function of the round outcome `ω` alone, hence a legal `keep : X → Bool` for
`CQState.filterKeep`.  It coincides with the agree restriction of the full seed-dependent accept
gate, so filtering by it filters by the protocol's actual accept event on the agree block. -/
def bb84SiftedAgreeAcceptKeep {n : ℕ} (peSel xSel : Fin n → Bool) {leakEC : ℕ}
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (ω : Fin n → Fin signalDim) : Bool :=
  bb84SiftedLocalPETestPassed peSel xSel δ Q ω && !bb84SiftedKeyStringsDiffer peSel ec ω

/-- The fail-closed local-PE pass filter of `SiftedMeasurement.lean` **is**
`CQState.filterKeep` at the PE-only predicate.  Stated so that this lane uses `CQState.filterKeep`
and its contraction lemmas throughout, with the hand-rolled declaration identified with it rather
than kept as a parallel implementation. -/
theorem bb84PostMeasurementCQSiftedLocalPEPassFilter_eq_filterKeep {n dE : ℕ} [NeZero dE]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ρ : CQState (Fin n → Fin signalDim) dE) :
    bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ ρ =
      CQState.filterKeep (bb84SiftedLocalPETestPassed peSel xSel δ Q) ρ :=
  CQState.ext_stateMap rfl

end QKD.BB84.Engine

end -- noncomputable section
