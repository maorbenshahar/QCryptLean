import QCryptLean.QKD.OutputLayout.Graft
import QCryptLean.QKD.BB84.Reduction.PackedSelector
import QCryptLean.QKD.BB84.TailTranscript
import QCryptLean.QKD.BB84.Measurement.LatePublicControl
import QCryptLean.QKD.BB84.ParameterEstimation
import QCryptLean.QKD.BB84.SeedTagSyndrome
import QCryptLean.QKD.Protocol
import QCryptLean.QKD.BB84.Model.RealChannelEntrywise

/-!
# The measure-first BB84 experiment, in the order it happens

This module is the authoritative quantum-memory-free BB84 program.  Reading it top to bottom is
reading the experiment in chronological order; the two finished objects are `program` (the typed
LOCC program) and `protocol` (that program together with the local key ownership of its
heterogeneous output).  Nothing here asserts security: the two published bounds about this same
program are collected in `QCryptLean.QKD.BB84.Security`, and the physical configuration
record that names these arguments is `QKD.BB84.Parameters`.

## The five stages

Each stage below lists who acts, what becomes public, and what survives it.

1. **Destructive per-round measurement.**  Both parties, independently in each round, draw a basis
   from their own law and measure; nothing is announced, and each ends with one completed local
   record — its basis string and its outcome bits, with no signal register left.
2. **Basis announcement, matched-round shuffle, sifting.**  Alice announces her stored basis
   string, Bob announces his, then Alice samples and announces one uniform ordering of the rounds
   where the two strings agree.  If that public control supplies every quota, each party keeps its
   selected record — own basis string plus the `nK + mZ + mX` selected bits; otherwise both
   discard their complete records and the branch ends with no key register.
3. **Erase the private basis copies.**  Alice then Bob, privately, keep only the packed
   `2 ^ (nK + mZ + mX)`-element register of selected bits.  Nothing is announced.
4. **Disclose the tests, then the seed, tag and syndrome.**  Bob and then Alice announce the bit
   at each disclosed test round; Alice then announces one fused cell carrying the
   privacy-amplification seed index, the verification tag and the error-correction syndrome.  Both
   raw registers survive.
5. **Accept/abort decision, then reconciliation, verification, privacy amplification.**  Bob
   announces the accept flag.  On acceptance Alice hashes her raw string and Bob decodes his
   against the announced syndrome and hashes the result, so both hold a `2 ^ keyLength`-element
   key; on abort both discard their raw registers and no key register is created.

Stages 1 and 2 are `Measurement.weightedLatePublicSelectionProgram`: the destructive schedule of
the Measurement.Weighted module grafted to the late public control of the
Measurement.LatePublicControl module.  Stage 3 is `selectedBitsToRawProgram` below.
Stage 4 is `directPreDecisionProgram`: the test disclosure `peAnnouncementLoop` of
`QCryptLean.QKD.BB84.ParameterEstimation` followed by the fused announcement `fusedStage`
of `QCryptLean.QKD.BB84.SeedTagSyndrome`; its cells are numbered by
`QCryptLean.QKD.BB84.TailTranscript`.  Stage 5 is `QKD.BB84.FinalStage.program`,
reached through `rawClassicalTailProgram`.

**Every branch point is an already announced value.** The quota test `Sampling.HasQuotas` is a
predicate of the three public cells of stage 2 alone, so `completeContinuationBoundary` and
`completeContinuation` branch on public information; the accept/abort branch of stage 5 is indexed
by the flag Bob announces.  `QCryptLean.QKD.BB84.Chronology` states these stage facts and
decodes a complete public exit into the whole transcript.

## Scope

Renner, arXiv:quant-ph/0512258v2, source lines 673--736, motivates measurement and sifting before
the classical tail.  Nahar et al., arXiv:2403.11851, lines 908--919, motivates announcing test
outcomes before reconciliation and publicly seeded hashing.  The grafts, output layout and index
arithmetic below are explicit library constructions, not identities quoted verbatim from either
paper.  This construction does not by itself prove a no-cross-round-memory witness, a sampling
transfer, or either physical security theorem.
-/

open scoped Matrix BigOperators ENNReal

noncomputable section

namespace QKD.BB84

open TypedLOCC
open QKD.BB84
open QKD.BB84.Reduction
open TypedLOCC.TwoParty
open QKD.BB84.Engine

/-! ## Stage 3 — erase the private basis copies and keep the selected bits -/

/-- Alice locally converts her selected record to raw bits and forgets her full basis copy. -/
def selectedBitsToRawAliceAction (N n : ℕ) :
    PrivateAction (Measurement.weightedSelectedRecordSystem N n) :=
  PrivateAction.ofInstrument .alice
    (Instrument.functionAndForget selectedBitsToRaw)

/-- Bob locally converts his selected record to raw bits and forgets his full basis copy. -/
def selectedBitsToRawBobAction (N n : ℕ) :
    PrivateAction (selectedBitsToRawAliceAction N n).out :=
  PrivateAction.ofInstrument .bob
    (Instrument.functionAndForget selectedBitsToRaw)

/-- Run the two local basis-erasure conversions in Alice-then-Bob order. -/
def selectedBitsToRawProgram (N n : ℕ) :
    Program (Measurement.weightedSelectedRecordSystem N n)
      (.leaf (FinalStage.rawSystem n)) :=
  cast (by
    apply congrArg (fun R => Program (Measurement.weightedSelectedRecordSystem N n) (.leaf R))
    change ((Measurement.weightedSelectedRecordSystem N n).set .alice
      (Fin (2 ^ n))).set .bob (Fin (2 ^ n)) = _
    rw [Measurement.weightedSelectedRecordSystem, TwoParty.set_alice, TwoParty.set_bob])
    ((selectedBitsToRawAliceAction N n).then (selectedBitsToRawBobAction N n).run)

/-! ## Stage 4 — disclose the tests, the seed, the tag and the syndrome -/

/-- Run the retained Bob-then-Alice PE announcement loop followed by Alice's fused
seed/tag/syndrome announcement, stopping immediately before the final decision. -/
noncomputable def directPreDecisionProgram
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) :
    Program (FinalStage.rawSystem n)
      (classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC) :=
  peAnnouncementLoop n
    (n - bb84KeyRoundCount n m)
    (bb84PERoundIdx (m := m) peSel) fun _ _ =>
      fusedStage n ℓ ℓEV peSel leakEC ec
        (fun _ => Program.done)

/-! ## Stage 5 — the decision, and the classical tail as a whole -/

/-- Public boundary obtained by attaching the semantic final decision and key/abort leaves to
every complete pre-decision transcript. -/
def rawClassicalTailBoundary
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) : Boundary Party :=
  (classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).graft
    (fun _ => FinalStage.boundary ℓ)

/-- Complete retained classical tail: announce PE and fused data, decode that same public exit,
and run the parameterized final decision and local key/abort continuation. -/
noncomputable def rawClassicalTailProgram
    (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ) :
    Program (FinalStage.rawSystem n)
      (rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC) :=
  (directPreDecisionProgram n m ℓ ℓEV peSel leakEC ec).graft fun e =>
    let d := classicalTailExitEquiv n m ℓ ℓEV peSel leakEC e
    by
      simpa only [Boundary.uniform_system] using
        FinalStage.program n m ℓ ℓEV peSel xSel leakEC ec delta Q
          d.alicePE d.bobPE d.seedPair d.evTag d.syndrome

/-! ## Attaching the classical tail beneath the late public control -/

/-- The quota-dependent terminal leaf has one complete public exit. -/
instance lateSelectionLeafUnique (N nK mZ mX : ℕ) (omega : Sampling.RawControl N) :
    Unique (Measurement.lateSelectionLeaf N nK mZ mX omega).Exit := by
  unfold Measurement.lateSelectionLeaf
  split <;> exact inferInstance

/-- The final multipartite system of the quota-dependent terminal leaf is selected by the same quota
test. -/
theorem lateSelectionLeaf_system (N nK mZ mX : ℕ) (omega : Sampling.RawControl N)
    (e : (Measurement.lateSelectionLeaf N nK mZ mX omega).Exit) :
    (Measurement.lateSelectionLeaf N nK mZ mX omega).system e =
      if Sampling.HasQuotas nK mZ mX omega then
        Measurement.weightedSelectedRecordSystem N (nK + mZ + mX)
      else Measurement.lateSelectionAbortSystem := by
  revert e
  unfold Measurement.lateSelectionLeaf
  split
  · rename_i h
    rw [ite_eq_left h]
    intro e
    rfl
  · rename_i h
    rw [ite_eq_right h]
    intro e
    rfl

/-- Complete late-selection exits are exactly the announced basis strings and exact dependent
shuffle.  The quota-dependent leaf exit is `Unit` and contributes no extra choice. -/
def lateSelectionExitEquiv (N nK mZ mX : ℕ) :
    (Measurement.lateSelectionBoundary N nK mZ mX).Exit ≃
      Sampling.RawControl N where
  toFun e := ⟨e.1, e.2.1, e.2.2.1⟩
  invFun := Measurement.lateSelectionExit N nK mZ mX
  left_inv e := by
    rcases e with ⟨a, b, order, leaf⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    refine Sigma.ext rfl (heq_of_eq ?_)
    refine Sigma.ext rfl (heq_of_eq ?_)
    exact Subsingleton.elim _ _
  right_inv omega := by
    rcases omega with ⟨a, b, order⟩
    rfl

/-- Boundary attached to one complete late-public control: the retained classical tail on quota
success and the existing key-free Unit/Unit leaf on shortage. -/
def completeContinuationBoundary
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) : Boundary Party :=
  if Sampling.HasQuotas nK mZ mX (lateSelectionExitEquiv N nK mZ mX e) then
    rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC
  else .leaf Measurement.lateSelectionAbortSystem

/-- **A quota-feasible announced control really runs the classical tail.**

The test is a predicate of the three public cells of stage 2 alone, read off the exit by
`lateSelectionExitEquiv`; this is the sense in which the announced values — and nothing
private — select the continuation. -/
theorem completeContinuationBoundary_of_hasQuotas
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit)
    (h : Sampling.HasQuotas nK mZ mX (lateSelectionExitEquiv N nK mZ mX e)) :
    completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e =
      rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC := by
  simp [completeContinuationBoundary, h]

/-- **A short announced control really ends the run with no key register.** -/
theorem completeContinuationBoundary_of_shortage
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit)
    (h : ¬Sampling.HasQuotas nK mZ mX (lateSelectionExitEquiv N nK mZ mX e)) :
    completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e =
      .leaf Measurement.lateSelectionAbortSystem := by
  simp [completeContinuationBoundary, h]

/-- Successful continuation after one late-public control: erase both private basis copies,
retain the selected bits, and run the complete retained classical tail. -/
noncomputable def successfulCompleteContinuation
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Program (Measurement.weightedSelectedRecordSystem N (nK + mZ + mX))
      (rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC) :=
  (selectedBitsToRawProgram N (nK + mZ + mX)).graft fun _ =>
    rawClassicalTailProgram (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX)
      (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q

/-- Quota-dependent continuation at one actual late-public exit.  Success uses the selected
embedding already chosen by that exit; shortage performs no further action on the existing
Unit/Unit abort leaf. -/
noncomputable def completeContinuation
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) :
    Program ((Measurement.lateSelectionBoundary N nK mZ mX).system e)
      (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e) := by
  by_cases h : Sampling.HasQuotas nK mZ mX
      (lateSelectionExitEquiv N nK mZ mX e)
  · have hstart : (Measurement.lateSelectionBoundary N nK mZ mX).system e =
        Measurement.weightedSelectedRecordSystem N (nK + mZ + mX) := by
      rcases e with ⟨a, b, order, leaf⟩
      have h' : Sampling.HasQuotas nK mZ mX ⟨a, b, order⟩ := by
        simpa [lateSelectionExitEquiv] using h
      change (Measurement.lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩).system leaf = _
      rw [lateSelectionLeaf_system, ite_eq_left h']
    have hout : completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e =
        rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          (@Sampling.packedPESel nK mZ mX) leakEC := by
      simp [completeContinuationBoundary, h]
    rw [hstart, hout]
    exact successfulCompleteContinuation N nK mZ mX ℓ ℓEV leakEC ec delta Q
  · have hstart : (Measurement.lateSelectionBoundary N nK mZ mX).system e =
        Measurement.lateSelectionAbortSystem := by
      rcases e with ⟨a, b, order, leaf⟩
      have h' : ¬Sampling.HasQuotas nK mZ mX ⟨a, b, order⟩ := by
        simpa [lateSelectionExitEquiv] using h
      change (Measurement.lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩).system leaf = _
      rw [lateSelectionLeaf_system, ite_eq_right h']
    have hout : completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e =
        .leaf Measurement.lateSelectionAbortSystem := by
      simp [completeContinuationBoundary, h]
    rw [hstart, hout]
    exact Program.done

/-! ## The complete experiment -/

/-- Complete public output boundary, preserving all late basis/shuffle metadata and every later
PE, fused, and final-decision announcement. -/
noncomputable def boundary
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) : Boundary Party :=
  (Measurement.lateSelectionBoundary N nK mZ mX).graft
    (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC)

/-- Complete measure-first BB84 program: destructive local measurement, late public sifting and
shuffle, selected-bit retention or shortage discard, then the retained classical tail. -/
noncomputable def program
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Program (Measurement.weightedStreamSystem Unit N)
      (boundary N nK mZ mX ℓ ℓEV leakEC) :=
  (Measurement.weightedLatePublicSelectionProgram pA pB N nK mZ mX).graft
    (completeContinuation N nK mZ mX ℓ ℓEV leakEC ec delta Q)

/-- Expose an outer late-public exit together with the complete exit of its attached
quota-dependent continuation. -/
def exitEquiv
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    (boundary N nK mZ mX ℓ ℓEV leakEC).Exit ≃
      Σ e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit,
        (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e).Exit :=
  Boundary.graftExitEquiv _ _

/-! ## Locally owned output layout and protocol package -/

/-- Explicit key-free layout for the Unit/Unit shortage leaf. -/
def lateSelectionAbortOutputLayout :
    QKD.OutputLayout (.leaf Measurement.lateSelectionAbortSystem) where
  alice := .alice
  bob := .bob
  alice_ne_bob := by decide
  disposition _ := .abort
  AliceResidual _ := Unit
  BobResidual _ := Unit
  finAliceResidual _ := inferInstance
  decAliceResidual _ := inferInstance
  nonemptyAliceResidual _ := inferInstance
  finBobResidual _ := inferInstance
  decBobResidual _ := inferInstance
  nonemptyBobResidual _ := inferInstance
  aliceSplit e := by
    rcases e with ⟨⟩
    exact (Equiv.prodPUnit Unit).symm
  bobSplit e := by
    rcases e with ⟨⟩
    exact (Equiv.prodPUnit Unit).symm

/-- Lift the final-stage local key ownership through the retained pre-decision public prefix. -/
noncomputable def rawClassicalTailOutputLayout
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :
    QKD.OutputLayout (rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC) :=
  QKD.OutputLayout.graftFixedParties .alice .bob (by decide)
    (fun _ => FinalStage.outputLayout ℓ) (fun _ => rfl) (fun _ => rfl)

/-- Output layout for the continuation attached at one late-public exit. -/
noncomputable def completeContinuationOutputLayout
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) :
    QKD.OutputLayout
      (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e) := by
  by_cases h : Sampling.HasQuotas nK mZ mX
      (lateSelectionExitEquiv N nK mZ mX e)
  · exact QKD.OutputLayout.transport (by simp [completeContinuationBoundary, h])
      (rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC)
  · exact QKD.OutputLayout.transport (by simp [completeContinuationBoundary, h])
      lateSelectionAbortOutputLayout

/-- The quota-dependent continuation layout keeps Alice as its named key owner. -/
theorem completeContinuationOutputLayout_alice
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) :
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC e).alice = .alice := by
  unfold completeContinuationOutputLayout
  split <;> exact QKD.OutputLayout.transport_alice _ _

/-- The quota-dependent continuation layout keeps Bob as its named key owner. -/
theorem completeContinuationOutputLayout_bob
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) :
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC e).bob = .bob := by
  unfold completeContinuationOutputLayout
  split <;> exact QKD.OutputLayout.transport_bob _ _

/-- Local Alice/Bob key ownership across quota success, shortage abort, and the final semantic
accept/abort flag, while preserving the complete public exit. -/
noncomputable def outputLayout
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    QKD.OutputLayout
      (boundary N nK mZ mX ℓ ℓEV leakEC) :=
  QKD.OutputLayout.graftFixedParties .alice .bob (by decide)
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC)
    (completeContinuationOutputLayout_alice N nK mZ mX ℓ ℓEV leakEC)
    (completeContinuationOutputLayout_bob N nK mZ mX ℓ ℓEV leakEC)

/-- The complete measure-first BB84 program and its heterogeneous locally owned output layout.

The physical program has fixed per-party basis PMFs, retains every late public control value, and
uses the retained general-`m` classical tail with `m = mZ + mX`.  This data package contains no
security assertion and is not itself the separate no-cross-round-memory witness. -/
noncomputable def protocol
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) : QKD.Protocol Party where
  start := Measurement.weightedStreamSystem Unit N
  boundary := boundary N nK mZ mX ℓ ℓEV leakEC
  program := program pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q
  layout := outputLayout N nK mZ mX ℓ ℓEV leakEC

end QKD.BB84
