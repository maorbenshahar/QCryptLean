import QCryptLean.QKD.BB84.Security
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the physical memory-free BB84 security entry point

This module imports **only** `QCryptLean.QKD.BB84.Security` and checks that the published
physical security interface is reachable and usable through that single import.  It demonstrates
the existing names; it introduces no alias, no wrapper and no new claim.

Four things are checked:

* a worked **client example** consumes the published results exactly as an external user would,
  deriving the improved-row security of the actual executable protocol together with its reduction
  to the analytical model, from the conditions those results actually take;
* a **fully concrete client** configures one experiment, discharges the conditions it is given, and
  reads off the diamond bound — with no coordinate package, no dimension instance and no
  raw-parameter list anywhere in the statement;
* two **reader clients** decode a finished run's complete public transcript and read off which
  registers survive it, for an arbitrary configuration; and
* one **fully instantiated operational experiment** — every physical choice a literal — with its
  realised test-block sizes, its accept window, and its accept rule.  It is explicitly *not* a
  finite-key example: no rate condition is discharged there, and none may be inferred from the
  fact that it elaborates.
-/

assert_no_sorry QKD.BB84.Parameters.isFullInterfaceSecure_improved
assert_no_sorry QKD.BB84.Parameters.isFullInterfaceSecure_improvedAt
assert_no_sorry QKD.BB84.Parameters.isFullInterfaceSecure_basic

namespace QCryptLeanTest.BB84.PublicAPI

open QKD.BB84
open QKD.BB84
open QKD.BB84.Reduction
open QKD.BB84.Measurement
open QKD.BB84.Sampling
open QKD.BB84.Engine

/-! ## A client of the entry point

The example below is what an external user gets from
`import QCryptLean.QKD.BB84.Security`: for the *actual* executable protocol of an arbitrary
configuration — arbitrary physical batch size, arbitrary basis laws, arbitrary
translation-equivariant error-correction scheme — the improved full-interface security row **and**
the reduction to the analytical model, under exactly the conditions those published results take.
Its proof is the pair of the two published proofs; no new mathematical content is introduced. -/

example (p : Parameters) [NeZero p.sifted] {epsilonAEP : ℝ}
    (h : p.ImprovedConditions epsilonAEP) :
    p.protocol.IsFullInterfaceSecure (p.improvedBudget epsilonAEP) ∧
      p.protocol.realIdealDistance ≤ p.modelDistance :=
  ⟨p.isFullInterfaceSecure_improved h, p.realIdealDistance_le_modelDistance⟩

/-- The public improved theorem uses only its genuine scalar conditions at a free PA error. -/
example (p : Parameters) {epsilonAEP epsPA beta dev : ℝ}
    (hAEP : 0 < epsilonAEP) (hPA : 0 < epsPA)
    (hbeta : 0 < beta) (hbeta1 : beta < 1) (hdev : 0 ≤ dev)
    (hbelow : p.errorRate + p.tolerance + dev ≤ 1 / 2)
    (hRate : improvedKeyRateConditionAtDev p.sifted p.tests p.keyLength p.tagLength p.leak
      p.errorRate p.tolerance dev epsilonAEP epsPA beta)
    (hec : p.ec.IsTranslationEquivariant) :
    p.protocol.IsFullInterfaceSecure
      ((2 : ℝ) ^ (-(p.tagLength : ℝ)) +
        (Nat.choose (p.sifted + 3) 3 : ℝ) *
          (epsPA + 2 * (epsilonAEP + Real.sqrt
            (2 * Engine.klAcceptTailPhaseOnlyDev p.peSel p.xSel
              p.errorRate p.tolerance dev)))) :=
  p.isFullInterfaceSecure_improvedAt
    { smoothing_pos := hAEP
      keyRate := hRate
      ecTranslationEquivariant := hec
      epsPA_pos := hPA
      beta_pos := hbeta
      beta_lt_one := hbeta1
      dev_nonneg := hdev
      belowThresholdDev := hbelow }

/-- The basic theorem charges correctness directly and lifts only secrecy by `C(n+15,15)`. -/
example (p : Parameters) {epsilonAEP : ℝ} (h : p.BasicConditions epsilonAEP) :
    p.protocol.IsFullInterfaceSecure
      ((2 : ℝ) ^ (-(p.tagLength : ℝ)) +
        (Nat.choose (p.sifted + 16 - 1) 15 : ℝ) *
        (2 * Real.sqrt (2 * Engine.klAcceptTailPhaseOnly p.peSel p.xSel
            p.errorRate p.tolerance) + 2 * epsilonAEP +
          (1 / 2) * Real.exp (-(Engine.bb84KeyRoundCount p.sifted p.tests : ℝ) / 4 *
            (Real.log 2 - Math.ClassicalEntropy.binaryEntropy
              (p.errorRate + 2 * p.tolerance))))) :=
  p.isFullInterfaceSecure_basic h

/-! ## The basic row keeps an arbitrary error-correction scheme

The same client, for the standard row, takes no hypothesis on the error-correction scheme at all:
`Parameters.BasicConditions` has no field about `ec`. -/

example (p : Parameters) {epsilonAEP : ℝ} (h : p.BasicConditions epsilonAEP) :
    p.protocol.IsFullInterfaceSecure (p.basicBudget epsilonAEP) :=
  p.isFullInterfaceSecure_basic h

/-! ## Reading a finished run through the public API

The two clients below use only `QKD.BB84.publicTranscriptEquiv` and the two register
readings.  They say what survives a run, for an arbitrary configuration: two `2 ^ keyLength`-element
key registers exactly on a quota-feasible run whose announced flag accepts, and no key register on
a short or rejecting run. -/

example (p : Parameters)
    (e : (QKD.BB84.boundary p.rounds p.keyRounds p.zTests p.xTests p.keyLength
      p.tagLength p.leak).Exit)
    (h : Sampling.HasQuotas p.keyRounds p.zTests p.xTests
      (publicTranscriptEquiv p.rounds p.keyRounds p.zTests p.xTests p.keyLength p.tagLength
        p.leak e).control)
    (haccept : ((publicTranscriptEquiv p.rounds p.keyRounds p.zTests p.xTests p.keyLength
      p.tagLength p.leak e).sifted h).2 = 0) :
    (QKD.BB84.boundary p.rounds p.keyRounds p.zTests p.xTests p.keyLength
      p.tagLength p.leak).system e = FinalStage.keySystem p.keyLength := by
  rw [system_eq_of_sifted _ _ _ _ _ _ _ e h, if_pos haccept]

example (p : Parameters)
    (e : (QKD.BB84.boundary p.rounds p.keyRounds p.zTests p.xTests p.keyLength
      p.tagLength p.leak).Exit)
    (h : ¬Sampling.HasQuotas p.keyRounds p.zTests p.xTests
      (publicTranscriptEquiv p.rounds p.keyRounds p.zTests p.xTests p.keyLength p.tagLength
        p.leak e).control) :
    (QKD.BB84.boundary p.rounds p.keyRounds p.zTests p.xTests p.keyLength
      p.tagLength p.leak).system e = Measurement.lateSelectionAbortSystem :=
  system_eq_of_shortage p.rounds p.keyRounds p.zTests p.xTests p.keyLength p.tagLength p.leak e h

/-! ## One fully instantiated operational experiment

Every physical choice below is a literal: both basis laws, the batch size, the three quotas, the
three lengths, the error-correction scheme and the two numbers of the accept test.  The facts that
follow are about *this* experiment, and each is decided or is an instance of a published theorem.

🚨 **This is not a finite-key example.**  Nothing here discharges `BasicConditions` or
`ImprovedConditions`; in particular `basicKeyRateCondition` is not claimed at these sizes, and
elaborating the configuration says nothing at all about whether its key rate is positive.  A
nonvacuous finite-key parameter demonstration is separate work. -/

/-- A concrete reconciliation scheme: announce the empty syndrome and keep Bob's own string.  No
correctness property is part of `ECScheme`, and the basic row assumes none. -/
def demoEC : ECScheme 16 (@Sampling.packedPESel 8 4 4) 2 :=
  ⟨fun _ => 0, fun b _ => b⟩

/-- This scheme is translation equivariant, so the improved row's extra premise is dischargeable
at it: the constant syndrome is shifted by the identity permutation, and the identity decoder
commutes with a common shift. -/
theorem demoEC_isTranslationEquivariant : demoEC.IsTranslationEquivariant :=
  fun _ => ⟨⟨Equiv.refl _, fun _ => rfl⟩, fun _ _ => rfl⟩

/-- The unbiased per-round basis law: `Z` and `X` with probability `1/2` each. -/
noncomputable def uniformBasisLaw : PMF Measurement.Basis :=
  PMF.map (fun b : Bool => if b then Measurement.Basis.x else Measurement.Basis.z)
    (PMF.bernoulli ⟨(1 : ℝ) / 2, by positivity⟩ (by
      change (1 : ℝ) / 2 ≤ 1
      norm_num))

/-- **One fully instantiated measure-first BB84 experiment**: 64 measured signals, an unbiased
basis choice on both sides, 8 sifted key rounds with 4 Z-basis and 4 X-basis test rounds, a 4-bit
final key, a 2-bit verification tag, a 2-bit syndrome, the scheme `demoEC`, and the accept test
"observed mismatch frequency within `1/40` of `1/50`". -/
noncomputable def demoParameters : Parameters where
  aliceBasis := uniformBasisLaw
  bobBasis := uniformBasisLaw
  rounds := 64
  keyRounds := 8
  zTests := 4
  xTests := 4
  keyLength := 4
  tagLength := 2
  leak := 2
  ec := demoEC
  tolerance := 1 / 40
  errorRate := 1 / 50

/-- The configuration keeps 16 sifted rounds. -/
theorem demoParameters_sifted : demoParameters.sifted = 16 := by decide

/-- Of those, 8 are disclosed test rounds. -/
theorem demoParameters_tests : demoParameters.tests = 8 := by decide

/-- The key block is a proper part of the sifted block. -/
theorem demoParameters_tests_lt_sifted : demoParameters.tests < demoParameters.sifted := by
  decide

/-- The batch contains at least as many signals as the total sifted quota. -/
theorem demoParameters_sifted_le_rounds : demoParameters.sifted ≤ demoParameters.rounds := by
  decide

/-- The realised Z-test sample size is the configured quota `zTests = 4`. -/
theorem demoParameters_zTestSampleSize :
    bb84SiftedZTestSampleSize demoParameters.peSel demoParameters.xSel = 4 :=
  packedZTestSampleSize 8 4 4

/-- The realised X-test sample size is the configured quota `xTests = 4`. -/
theorem demoParameters_xTestSampleSize :
    bb84SiftedXTestSampleSize demoParameters.peSel demoParameters.xSel = 4 :=
  packedXTestSampleSize 8 4 4

/-- **The accept test of this experiment**, with its centre and half-width in the stated roles:
an observed test frequency passes exactly when it is within `1/40` of `1/50`. -/
theorem demoParameters_mem_acceptWindow (f : ℝ) :
    f ∈ demoParameters.acceptWindow ↔ |f - 1 / 50| ≤ 1 / 40 :=
  demoParameters.mem_acceptWindow_iff f

/-- **The configured experiment runs the chronological program at these literals**, with `1/40`
in the half-width slot and `1/50` in the centre slot of the low-level builder.  This `rfl` is the
concrete check that the two positional real arguments are not exchanged. -/
theorem demoProtocol_program :
    demoParameters.protocol.program =
      QKD.BB84.program uniformBasisLaw uniformBasisLaw 64 8 4 4 4 2 2 demoEC
        (1 / 40) (1 / 50) := rfl

/-- The configured experiment starts at the physical 64-round two-party stream multipartite system.
-/
theorem demoProtocol_start :
    demoParameters.protocol.start = Measurement.weightedStreamSystem Unit 64 := rfl

/-- **When this experiment accepts**: both 4-round test blocks are nonempty — they are — and
each observed mismatch frequency is within `1/40` of `1/50`, and the announced verification
tag matches the tag recomputed from Bob's reconciled string. -/
theorem demoParameters_acceptFlag_eq_zero_iff (as bs : demoParameters.TestBits)
    (evSeed : KeyHashSeed demoParameters.sifted demoParameters.tagLength
      demoParameters.peSel)
    (evTag : Fin (2 ^ demoParameters.tagLength)) (syn : Fin (2 ^ demoParameters.leak))
    (y : Fin (2 ^ demoParameters.sifted)) :
    demoParameters.acceptFlag as bs evSeed evTag syn y = 0 ↔
      (((0 < demoParameters.zTests ∧
            demoParameters.zTestFrequency as bs ∈ demoParameters.acceptWindow) ∧
          (0 < demoParameters.xTests ∧
            demoParameters.xTestFrequency as bs ∈ demoParameters.acceptWindow)) ∧
        evTag = verificationTag demoParameters.sifted demoParameters.tagLength
          demoParameters.peSel evSeed
          (demoParameters.ec.decode
            (QKD.BB84.Model.bobKeyOf demoParameters.sifted demoParameters.peSel y) syn)) :=
  demoParameters.acceptFlag_eq_zero_iff as bs evSeed evTag syn y

/-- Concrete accepted data for the actual decision function: Alice and Bob disclose the same
all-zero test string, use the all-zero verification seed and zero syndrome/Bob register, and
announce the verification tag recomputed from those choices.  This establishes only that the
decision function is nonvacuous; it is not a support or finite-key statement. -/
theorem demoParameters_acceptFlag_explicit_zero_data :
    let bits : demoParameters.TestBits := fun _ => 0
    let evSeed : KeyHashSeed demoParameters.sifted demoParameters.tagLength
        demoParameters.peSel := fun _ _ => 0
    demoParameters.acceptFlag bits bits evSeed
        (verificationTag demoParameters.sifted demoParameters.tagLength demoParameters.peSel
          evSeed
          (demoParameters.ec.decode
            (QKD.BB84.Model.bobKeyOf demoParameters.sifted demoParameters.peSel 0) 0))
        0 0 = 0 := by
  dsimp only
  rw [demoParameters_acceptFlag_eq_zero_iff]
  refine ⟨⟨⟨by decide, ?_⟩, ⟨by decide, ?_⟩⟩, rfl⟩
  · rw [demoParameters_mem_acceptWindow]
    norm_num [Parameters.zTestFrequency, Parameters.zTestMismatches]
  · rw [demoParameters_mem_acceptWindow]
    norm_num [Parameters.xTestFrequency, Parameters.xTestMismatches]

/-- The published normalized diamond distance of this experiment, as a real number: the public API
needs no coordinate package, dimension instance or reference system to name it. -/
noncomputable def demoRealIdealDistance : ℝ := demoParameters.protocol.realIdealDistance

/-- It is a distance, hence nonnegative.  **No bound on it is claimed here**: a bound requires the
conditions of one of the two published rows, which this configuration is not asserted to
satisfy. -/
theorem demoRealIdealDistance_nonneg : 0 ≤ demoRealIdealDistance :=
  demoParameters.protocol.realIdealDistance_nonneg

/-- Accepted-key classicality is hypothesis-free, so it holds at this configuration outright. -/
theorem demoParameters_acceptedKeyClassical :
    demoParameters.protocol.AcceptedKeyClassical :=
  demoParameters.protocol_acceptedKeyClassical

/-- The sifted block of this configuration is nonempty (demoParameters_sifted computes it to be
`16`), which is what the analytical model needs in order to be defined. -/
instance demoParameters_sifted_neZero : NeZero demoParameters.sifted := ⟨by decide⟩

/-- The reduction to the analytical model needs no condition beyond a nonempty sifted block, so it
holds at this configuration outright. -/
theorem demoParameters_realIdealDistance_le_modelDistance :
    demoParameters.protocol.realIdealDistance ≤ demoParameters.modelDistance :=
  demoParameters.realIdealDistance_le_modelDistance

/-! ## A fully concrete client

Nothing but the physical configuration is supplied here: no numeral coordinates, no dimension
instances, no channel and no ideal map.  The conditions are elementary inequalities, so a caller
who has them writes them down directly. -/

example (pA pB : PMF Measurement.Basis) (nK mZ mX ell ellEV leakEC N : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (Q delta epsilonAEP : ℝ)
    (hbelow : Q + 2 * delta ≤ 1 / 2) (hAEP : 0 < epsilonAEP)
    (hRate : basicKeyRateCondition (nK + mZ + mX) (mZ + mX) ell ellEV leakEC Q delta
      epsilonAEP) :
    let p : Parameters :=
      { aliceBasis := pA, bobBasis := pB, rounds := N, keyRounds := nK, zTests := mZ,
        xTests := mX, keyLength := ell, tagLength := ellEV, leak := leakEC, ec := ec,
        tolerance := delta, errorRate := Q }
    p.protocol.realIdealDistance ≤ p.basicBudget epsilonAEP :=
  Parameters.realIdealDistance_le_basicBudget _
    { belowThreshold := hbelow
      smoothing_pos := hAEP
      keyRate := hRate }

end QCryptLeanTest.BB84.PublicAPI
