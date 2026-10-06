import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.ClassicalContinuation
import QCryptLean.QKD.Protocol

/-!
# Configured measure-first BB84 experiments

The physical choices of one memory-free BB84 experiment — the two basis laws, the physical batch
size, the three packed quotas, the key/verification/syndrome lengths, the error-correction scheme
and the accept test — form a single structure `Parameters`, and `Parameters.protocol` runs the
existing measure-first builder at those choices.

The structure contains **only** physical choices.  There is no channel, ideal map, shared key,
coordinate package or security assertion in it, and no smoothing or analysis parameter: the
smoothing parameter `epsilonAEP` of the finite-key rows is an argument of the analysis conditions
and budgets, not of the experiment.  The dependent error-correction scheme is a field, so the
quotas it depends on need not be repeated by a caller.

`Parameters.protocol` is *definitionally* `QKD.BB84.protocol` at the same arguments
(`protocol_program`, `protocol_boundary`, `protocol_layout`, all `rfl`): this is a configuration of
the existing program, not a second executable protocol.  The raw-parameter builder remains the
low-level constructor used by the retained-factorization analysis.

## The reader's route

* the chronological construction is `QCryptLean.QKD.BB84.Program`, and
  `QCryptLean.QKD.BB84.Chronology` decodes one finished run's complete public transcript;
* `protocol_real`, `protocol_ideal` and `protocol_difference` are the derived maps the security
  rows compare — the real map is the program's own denotation, and the ideal key resource is read
  off the same output ownership data;
* `acceptFlag` and `acceptFlag_eq_zero_iff` say, in the physical terms of these fields, when the
  experiment accepts; `decisionAnnouncement_eq` pins that flag to the protocol's decision stage;
* `QCryptLean.QKD.BB84.Security` collects the two published bounds and their reduction
  to the analytical model.

`errorRate` and `tolerance` are the **centre** and the **half-width** of the accept test.  Both are
real and reach the low-level builders positionally, so `acceptFlag_eq_zero_iff` is where that
convention is fixed by a theorem rather than by a call site.
-/

noncomputable section

namespace QKD.BB84
open TypedLOCC
open QKD.BB84
open QKD.BB84.Reduction

open TypedLOCC.TwoParty
open QKD.BB84.Engine

/-- **The physical choices of one measure-first BB84 experiment.**

The packed selector partitions the `keyRounds + zTests + xTests` sifted rounds into the key block,
the Z-test block and the X-test block, in that order; `ec` is the error-correction scheme for that
selector and syndrome length, and is arbitrary unless a row's conditions say otherwise.

Alice and Bob measure `rounds` signals with independent per-round basis laws `aliceBasis` and
`bobBasis`; nothing forces these to be uniform, equal, or of full support, and `rounds` may be
smaller than the total quota, in which case the experiment takes its shortage branch. -/
structure Parameters where
  /-- Alice's per-round basis law. -/
  aliceBasis : PMF Measurement.Basis
  /-- Bob's per-round basis law. -/
  bobBasis : PMF Measurement.Basis
  /-- Number of physical signal rounds actually measured. -/
  rounds : ℕ
  /-- Number of sifted rounds retained as key rounds. -/
  keyRounds : ℕ
  /-- Number of sifted rounds spent on the Z-basis test. -/
  zTests : ℕ
  /-- Number of sifted rounds spent on the X-basis test. -/
  xTests : ℕ
  /-- Length in bits of the final key produced on acceptance. -/
  keyLength : ℕ
  /-- Length in bits of the verification tag. -/
  tagLength : ℕ
  /-- Length in bits of the announced error-correction syndrome. -/
  leak : ℕ
  /-- The error-correction scheme for the packed selector and this syndrome length. -/
  ec : ECScheme (keyRounds + zTests + xTests)
    (@Sampling.packedPESel keyRounds zTests xTests) leak
  /-- Half-width `δ` of the parameter-estimation accept test. -/
  tolerance : ℝ
  /-- Centre `Q` of the parameter-estimation accept test: a test block is accepted when its
  observed mismatch frequency lies within `tolerance` of this value. -/
  errorRate : ℝ

namespace Parameters

variable (p : Parameters)

/-- The number of sifted rounds, `nK + mZ + mX`. -/
abbrev sifted : ℕ := p.keyRounds + p.zTests + p.xTests

/-- The number of test rounds, `mZ + mX`. -/
abbrev tests : ℕ := p.zTests + p.xTests

/-- The packed parameter-estimation mask: the first `keyRounds` sifted rounds are key rounds. -/
abbrev peSel : Fin p.sifted → Bool := @Sampling.packedPESel p.keyRounds p.zTests p.xTests

/-- The packed X-test mask: the last `xTests` sifted rounds are X-basis test rounds. -/
abbrev xSel : Fin p.sifted → Bool := @Sampling.packedXSel p.keyRounds p.zTests p.xTests

/-- **The configured measure-first BB84 protocol.**

This is the existing `QKD.BB84.protocol` construction at these choices: destructive local
measurement of `rounds` signals, late public sifting and shuffle, selected-bit retention or
shortage discard, the retained classical tail, and the final decision with its two ordered keys or
key-free abort.  The complete public transcript is retained. -/
def protocol : QKD.Protocol Party :=
  QKD.BB84.protocol p.aliceBasis p.bobBasis p.rounds p.keyRounds p.zTests p.xTests
    p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate

/-- The configured protocol starts at the physical two-party stream multipartite system. -/
theorem protocol_start :
    p.protocol.start = Measurement.weightedStreamSystem Unit p.rounds := rfl

/-- The configured protocol's complete output boundary is the existing one. -/
theorem protocol_boundary :
    p.protocol.boundary =
      QKD.BB84.boundary p.rounds p.keyRounds p.zTests p.xTests p.keyLength p.tagLength
        p.leak := rfl

/-- **The configured protocol runs the existing measure-first program**, by definition — not by a
transfer theorem or a conditional identification. -/
theorem protocol_program :
    p.protocol.program =
      QKD.BB84.program p.aliceBasis p.bobBasis p.rounds p.keyRounds p.zTests p.xTests
        p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate := rfl

/-- **The real map of the configured experiment is the denotation of that same program.**

There is no separately supplied analysis channel: the derived map is
`TypedLOCC.Program.denote` of the chronological construction, on the complete output boundary. -/
theorem protocol_real :
    p.protocol.real =
      (QKD.BB84.program p.aliceBasis p.bobBasis p.rounds p.keyRounds p.zTests p.xTests
        p.keyLength p.tagLength p.leak p.ec p.tolerance p.errorRate).denote := rfl

/-- **The ideal map of the configured experiment is its own output resource after its real map.**

`QKD.Protocol.resource` is the full-exit key replacement read off the locally owned layout, so the
ideal key resource is derived from the same program and ownership data rather than chosen. -/
theorem protocol_ideal : p.protocol.ideal = p.protocol.resource.comp p.protocol.real := rfl

/-- The real-minus-ideal map compared by both security rows is the difference of those two derived
maps. -/
theorem protocol_difference : p.protocol.difference = p.protocol.real - p.protocol.ideal := rfl

/-- The configured protocol uses the existing locally owned output layout. -/
theorem protocol_layout :
    p.protocol.layout =
      QKD.BB84.outputLayout p.rounds p.keyRounds p.zTests p.xTests p.keyLength
        p.tagLength p.leak := rfl

/-- **The configured protocol declares an inhabited complete public exit.**

Derived from the construction (`boundary_space_nonempty`) in both the
quota-feasible and the shortage branch; it is not a caller premise, and no claim is made about
arbitrary syntactic boundaries. -/
instance instNonemptyProtocolExit : Nonempty p.protocol.boundary.Exit :=
  boundaryExitNonempty p.rounds p.keyRounds p.zTests p.xTests p.keyLength
    p.tagLength p.leak

/-! ## What the accept test actually tests

`errorRate` and `tolerance` are both real numbers and reach the underlying builders through
positional arguments, so their roles have to be readable off a theorem rather than off a call.
The three declarations below do that: `acceptFlag` is the very flag function the configured
protocol's final decision reads (`decisionAnnouncement_eq` is that pin, by `rfl`), and
`acceptFlag_eq_zero_iff` says in physical terms when it accepts. -/

/-- The window an observed test frequency must lie in to be accepted:
`[errorRate - tolerance, errorRate + tolerance]`. -/
def acceptWindow : Set ℝ :=
  Set.Icc (p.errorRate - p.tolerance) (p.errorRate + p.tolerance)

/-- Membership of the accept window is the accept test `|observed − errorRate| ≤ tolerance`. -/
theorem mem_acceptWindow_iff (f : ℝ) :
    f ∈ p.acceptWindow ↔ |f - p.errorRate| ≤ p.tolerance := by
  rw [acceptWindow, Set.mem_Icc, abs_le]
  constructor
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Disclosed test bits, as the retained final stage indexes them: one value per disclosed test
round of the sifted block. -/
abbrev TestBits : Type :=
  Fin (p.sifted - bb84KeyRoundCount p.sifted p.tests) → Fin 2

/-- The number of disclosed Z-basis test rounds at which Alice's and Bob's announced bits
disagree. -/
def zTestMismatches (as bs : p.TestBits) : ℕ :=
  (Finset.univ.filter fun j =>
    p.xSel (bb84PERoundIdx (m := p.tests) p.peSel j) = false ∧ as j ≠ bs j).card

/-- The number of disclosed X-basis test rounds at which Alice's and Bob's announced bits
disagree. -/
def xTestMismatches (as bs : p.TestBits) : ℕ :=
  (Finset.univ.filter fun j =>
    p.xSel (bb84PERoundIdx (m := p.tests) p.peSel j) = true ∧ as j ≠ bs j).card

/-- The observed Z-basis test frequency: mismatching disclosed Z-test rounds per Z-test round. -/
def zTestFrequency (as bs : p.TestBits) : ℝ :=
  (p.zTestMismatches as bs : ℝ) / (p.zTests : ℝ)

/-- The observed X-basis test frequency: mismatching disclosed X-test rounds per X-test round. -/
def xTestFrequency (as bs : p.TestBits) : ℝ :=
  (p.xTestMismatches as bs : ℝ) / (p.xTests : ℝ)

/-- **The parameter-estimation decision of the configured experiment.**

It passes exactly when both disclosed test blocks are nonempty and each block's observed mismatch
frequency lies in `acceptWindow`.  The denominators are the realised block sizes `zTests` and
`xTests` (`packedZTestSampleSize`, `packedXTestSampleSize`), and the centre of the window is
`errorRate` while its half-width is `tolerance` — not the other way round. -/
theorem peOK_iff (as bs : p.TestBits) :
    QKD.BB84.Model.peOKOfAnnounced p.tests p.peSel p.xSel p.tolerance p.errorRate as bs = true ↔
      ((0 < p.zTests ∧ p.zTestFrequency as bs ∈ p.acceptWindow) ∧
        (0 < p.xTests ∧ p.xTestFrequency as bs ∈ p.acceptWindow)) := by
  rw [QKD.BB84.Model.peOKOfAnnounced]
  rw [show bb84SiftedZTestSampleSize p.peSel p.xSel = p.zTests from
      packedZTestSampleSize p.keyRounds p.zTests p.xTests,
    show bb84SiftedXTestSampleSize p.peSel p.xSel = p.xTests from
      packedXTestSampleSize p.keyRounds p.zTests p.xTests]
  simp only [Bool.and_eq_true, decide_eq_true_eq, p.mem_acceptWindow_iff, zTestFrequency,
    xTestFrequency, zTestMismatches, xTestMismatches]

/-- **The accept flag the configured experiment's final decision announces.**

It is a function of the announced test bits, the announced verification seed, the announced
verification tag, the announced syndrome and Bob's own raw register; `0` accepts. -/
def acceptFlag (as bs : p.TestBits)
    (evSeed : KeyHashSeed p.sifted p.tagLength p.peSel)
    (evTag : Fin (2 ^ p.tagLength)) (syn : Fin (2 ^ p.leak))
    (y : Fin (2 ^ p.sifted)) : Fin 2 :=
  QKD.BB84.Model.acceptFlagOf p.sifted p.tests p.tagLength p.peSel p.xSel p.leak p.ec
    p.tolerance p.errorRate as bs evSeed evTag syn y

/-- **The configured experiment's classical tail runs at these named choices.**

`tolerance` occupies the accept test's half-width slot of `rawClassicalTailProgram` and
`errorRate` its centre slot.  Together with `decisionAnnouncement_eq` and
`acceptFlag_eq_zero_iff` below, this identifies how the two named fields determine the
flag the experiment announces. -/
theorem successfulContinuation_eq :
    successfulCompleteContinuation p.rounds p.keyRounds p.zTests p.xTests p.keyLength p.tagLength
        p.leak p.ec p.tolerance p.errorRate =
      (selectedBitsToRawProgram p.rounds p.sifted).graft fun _ =>
        rawClassicalTailProgram p.sifted p.tests p.keyLength p.tagLength p.peSel p.xSel p.leak
          p.ec p.tolerance p.errorRate := rfl

/-- **The final decision of the configured experiment is Bob's nondestructive readout of
`acceptFlag`, announced verbatim.**

The configured protocol's decision stage is definitionally the readout of the flag function above,
whose physical meaning is `acceptFlag_eq_zero_iff`. -/
theorem decisionAnnouncement_eq (as bs : p.TestBits)
    (evSeed : KeyHashSeed p.sifted p.tagLength p.peSel)
    (evTag : Fin (2 ^ p.tagLength)) (syn : Fin (2 ^ p.leak)) :
    FinalStage.decisionAnnouncement p.sifted p.tests p.tagLength p.peSel p.xSel p.leak p.ec
        p.tolerance p.errorRate as bs evSeed evTag syn =
      AnnouncedAction.ofInstrument .bob
        (Instrument.nondemolitionReadout (p.acceptFlag as bs evSeed evTag syn)) id := rfl

/-- **When the configured experiment accepts.**

Both disclosed test blocks must be nonempty with observed mismatch frequency inside
`acceptWindow`, *and* the announced verification tag must equal the tag recomputed from Bob's
reconciled string.  Nothing else is tested. -/
theorem acceptFlag_eq_zero_iff (as bs : p.TestBits)
    (evSeed : KeyHashSeed p.sifted p.tagLength p.peSel)
    (evTag : Fin (2 ^ p.tagLength)) (syn : Fin (2 ^ p.leak))
    (y : Fin (2 ^ p.sifted)) :
    p.acceptFlag as bs evSeed evTag syn y = 0 ↔
      (((0 < p.zTests ∧ p.zTestFrequency as bs ∈ p.acceptWindow) ∧
          (0 < p.xTests ∧ p.xTestFrequency as bs ∈ p.acceptWindow)) ∧
        evTag = verificationTag p.sifted p.tagLength p.peSel evSeed
          (p.ec.decode (QKD.BB84.Model.bobKeyOf p.sifted p.peSel y) syn)) := by
  rw [acceptFlag, QKD.BB84.Model.acceptFlagOf]
  by_cases h : QKD.BB84.Model.peOKOfAnnounced p.tests p.peSel p.xSel p.tolerance p.errorRate
        as bs = true ∧
      evTag = verificationTag p.sifted p.tagLength p.peSel evSeed
        (p.ec.decode (QKD.BB84.Model.bobKeyOf p.sifted p.peSel y) syn)
  · rw [if_pos h]
    simp only [true_iff, ← p.peOK_iff]
    exact h
  · rw [if_neg h]
    simp only [← p.peOK_iff]
    exact ⟨fun hone => absurd hone (by decide), fun hgood => absurd hgood h⟩

end Parameters

end QKD.BB84
