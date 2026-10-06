import QCryptLean.QKD.BB84.Program

/-!
# Reading one run of the measure-first BB84 experiment

`QCryptLean.QKD.BB84.Program` builds the experiment stage by stage.  This module says what
one *finished* run looks like: it decomposes the program into its stages, records that every branch
is taken on an already announced value, and decodes a complete public exit into the whole public
transcript — Alice's basis string, Bob's basis string, the sampled matched-round ordering, and then
either the disclosed test bits with the seed/tag/syndrome and the final accept flag, or nothing
further because a quota was short.

Everything here is an equivalence or an equality of the existing objects.  No output is discarded,
no alternative program is introduced, and nothing is claimed about secrecy.

## The stages

`program_eq_stages` writes the authoritative program as the destructive measurement schedule, then
the late public basis/shuffle control with its sifting, then the quota-dependent classical
continuation.

## The branch points

`completeContinuationBoundary_of_hasQuotas` / `..._of_shortage` (in
`QCryptLean.QKD.BB84.Program`) show that the sifting branch is a predicate of the three
announced stage-2 cells alone, and `QKD.BB84.FinalStage.exitEquiv` shows that a complete final-stage
exit *is* the announced accept flag.  Together with `FinalStage.system_eq` that is the operational
reading of abort: a run aborts because a quota was short or because the announced flag is one, and
in both cases no key register is created.

## The transcript

`PublicTranscript` is the decoded public record of a run and `publicTranscriptEquiv` the equivalence
with the program's complete public exits.  `system_eq_of_sifted` and `system_eq_of_shortage` read
the surviving registers off that record.
-/

noncomputable section

namespace QKD.BB84
open TypedLOCC
open QKD.BB84
open QKD.BB84.Reduction

open TypedLOCC.TwoParty
open QKD.BB84.Engine

/-! ## The chronological decomposition -/

/-- **The experiment, stage by stage.**

Reading the right-hand side left to right is reading the experiment in time: the destructive
per-round measurement schedule; the late public basis announcements, the announced matched-round
shuffle and the resulting sifting; and then, at each complete stage-2 transcript, the continuation
that quota-feasible controls send through the classical tail and short controls end at once.  The
equality is definitional: this is the same program, not a second presentation of it. -/
theorem program_eq_stages
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    program pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q =
      ((Measurement.weightedMeasurementSchedule pA pB N).graft
            (fun _ => Measurement.latePublicSelectionProgram N nK mZ mX)).graft
        (completeContinuation N nK mZ mX ℓ ℓEV leakEC ec delta Q) := rfl

/-- **The successful continuation is stage 3 followed by stages 4 and 5.**

Erase both private basis copies and keep the selected bits, then run the classical tail: disclose
the test bits and the fused seed/tag/syndrome cell, decode that same public exit, and run the
announced decision with its reconciliation, verification and privacy amplification.  The equality
is definitional; what it makes visible in one place is that the *half-width* argument `delta`
reaches `rawClassicalTailProgram` before the accept test's *centre* `Q`. -/
theorem successfulCompleteContinuation_eq_stages
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    successfulCompleteContinuation N nK mZ mX ℓ ℓEV leakEC ec delta Q =
      (selectedBitsToRawProgram N (nK + mZ + mX)).graft fun _ =>
        rawClassicalTailProgram (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec
          delta Q := rfl

/-! ## One complete exit of the classical tail -/

/-- **A complete public exit of the classical tail is its disclosed data together with the
announced accept flag.**

The first component is everything announced before the decision — the disclosed test bits in
Alice/Bob order, the privacy-amplification seed pair, the verification tag and the
error-correction syndrome — and the second is the flag Bob then announces.  It is an equivalence,
so no announced value is dropped. -/
def rawClassicalTailExitEquiv (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ) :
    (rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).Exit ≃
      ClassicalTailData n m ℓ ℓEV peSel leakEC × Fin 2 :=
  (Boundary.graftExitEquiv (classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC)
      (fun _ => FinalStage.boundary ℓ)).trans
    ((Equiv.sigmaCongr (classicalTailExitEquiv n m ℓ ℓEV peSel leakEC)
        (fun _ => FinalStage.exitEquiv ℓ)).trans
      (Equiv.sigmaEquivProd _ _))

/-- **What survives one complete run of the classical tail**: the two `2 ^ ℓ`-element key
registers when the announced flag accepts, and no key register when it aborts. -/
theorem system_rawClassicalTailBoundary (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (e : (rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).Exit) :
    (rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).system e =
      if (rawClassicalTailExitEquiv n m ℓ ℓEV peSel leakEC e).2 = 0 then FinalStage.keySystem ℓ
      else FinalStage.abortSystem := by
  refine (Boundary.system_graftExitEquiv
    (classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC)
    (fun _ => FinalStage.boundary ℓ) e).trans ?_
  rw [FinalStage.system_eq]
  rfl

/-! ## The complete public transcript of one run -/

/-- Everything the experiment announces *after* its sifting stage, at an announced control
`omega`: on quota success the disclosed test data and the final accept flag, and on shortage
nothing further, because both complete local records are discarded immediately. -/
def TailAnnouncements (nK mZ mX ℓ ℓEV leakEC : ℕ) {N : ℕ}
    (omega : Sampling.RawControl N) : Type :=
  if Sampling.HasQuotas nK mZ mX omega then
    ClassicalTailData (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC × Fin 2
  else Unit

/-- On a quota-feasible control the later announcements are the disclosed tail data and the flag. -/
theorem tailAnnouncements_of_hasQuotas (nK mZ mX ℓ ℓEV leakEC : ℕ) {N : ℕ}
    {omega : Sampling.RawControl N} (h : Sampling.HasQuotas nK mZ mX omega) :
    TailAnnouncements nK mZ mX ℓ ℓEV leakEC omega =
      (ClassicalTailData (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC × Fin 2) := by
  simp [TailAnnouncements, h]

/-- On a short control there is nothing further to announce. -/
theorem tailAnnouncements_of_shortage (nK mZ mX ℓ ℓEV leakEC : ℕ) {N : ℕ}
    {omega : Sampling.RawControl N} (h : ¬Sampling.HasQuotas nK mZ mX omega) :
    TailAnnouncements nK mZ mX ℓ ℓEV leakEC omega = Unit := by
  simp [TailAnnouncements, h]

/-- The announcements attached to one complete stage-2 exit, read through the quota test that the
same exit determines. -/
def tailAnnouncementsEquiv (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (Measurement.lateSelectionBoundary N nK mZ mX).Exit) :
    (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC e).Exit ≃
      TailAnnouncements nK mZ mX ℓ ℓEV leakEC (lateSelectionExitEquiv N nK mZ mX e) :=
  if h : Sampling.HasQuotas nK mZ mX (lateSelectionExitEquiv N nK mZ mX e) then
    (Equiv.cast (congrArg Boundary.Exit
        (completeContinuationBoundary_of_hasQuotas N nK mZ mX ℓ ℓEV leakEC e h))).trans
      ((rawClassicalTailExitEquiv (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          (@Sampling.packedPESel nK mZ mX) leakEC).trans
        (Equiv.cast (tailAnnouncements_of_hasQuotas nK mZ mX ℓ ℓEV leakEC h).symm))
  else
    (Equiv.cast (congrArg Boundary.Exit
        (completeContinuationBoundary_of_shortage N nK mZ mX ℓ ℓEV leakEC e h))).trans
      (Equiv.cast (tailAnnouncements_of_shortage nK mZ mX ℓ ℓEV leakEC h).symm)

/-- **The complete public transcript of one run of the experiment.**

`control` is what stage 2 makes public: Alice's announced basis string, Bob's announced basis
string and the announced ordering of the matched rounds.  `tail` is everything announced after
it, which the quota test applied to `control` decides the shape of. -/
structure PublicTranscript (N nK mZ mX ℓ ℓEV leakEC : ℕ) where
  /-- The two announced basis strings and the announced matched-round ordering. -/
  control : Sampling.RawControl N
  /-- Everything announced after sifting: the disclosed tests, the fused seed/tag/syndrome cell
  and the accept flag on quota success; nothing on shortage. -/
  tail : TailAnnouncements nK mZ mX ℓ ℓEV leakEC control

/-- The transcript record is exactly its two fields. -/
def publicTranscriptSigmaEquiv (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    PublicTranscript N nK mZ mX ℓ ℓEV leakEC ≃
      Σ omega : Sampling.RawControl N,
        TailAnnouncements nK mZ mX ℓ ℓEV leakEC omega where
  toFun t := ⟨t.control, t.tail⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A complete public exit of the experiment is exactly one complete public transcript.**

Being an equivalence is the precise sense in which the construction keeps the whole transcript:
the announced basis strings and ordering survive into the output, and so does every later
disclosure. -/
def publicTranscriptEquiv (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    (boundary N nK mZ mX ℓ ℓEV leakEC).Exit ≃
      PublicTranscript N nK mZ mX ℓ ℓEV leakEC :=
  (exitEquiv N nK mZ mX ℓ ℓEV leakEC).trans
    ((Equiv.sigmaCongr (lateSelectionExitEquiv N nK mZ mX)
        (tailAnnouncementsEquiv N nK mZ mX ℓ ℓEV leakEC)).trans
      (publicTranscriptSigmaEquiv N nK mZ mX ℓ ℓEV leakEC).symm)

/-- The announced control of the transcript read off an exit is the control that exit announced. -/
@[simp] theorem publicTranscriptEquiv_control (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (boundary N nK mZ mX ℓ ℓEV leakEC).Exit) :
    (publicTranscriptEquiv N nK mZ mX ℓ ℓEV leakEC e).control =
      lateSelectionExitEquiv N nK mZ mX
        (exitEquiv N nK mZ mX ℓ ℓEV leakEC e).1 := rfl

/-- The disclosed tail data and final accept flag of a quota-feasible run. -/
def PublicTranscript.sifted {N nK mZ mX ℓ ℓEV leakEC : ℕ}
    (t : PublicTranscript N nK mZ mX ℓ ℓEV leakEC)
    (h : Sampling.HasQuotas nK mZ mX t.control) :
    ClassicalTailData (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC × Fin 2 :=
  Equiv.cast (tailAnnouncements_of_hasQuotas nK mZ mX ℓ ℓEV leakEC h) t.tail

/-- A quota-feasible run **accepts** exactly when the announced final flag is zero. -/
def PublicTranscript.Accepted {N nK mZ mX ℓ ℓEV leakEC : ℕ}
    (t : PublicTranscript N nK mZ mX ℓ ℓEV leakEC) : Prop :=
  ∃ h : Sampling.HasQuotas nK mZ mX t.control, (t.sifted h).2 = 0

/-- Transporting a complete exit along an equality of boundaries does not change the registers
that survive it.  This is the only bookkeeping step the two readings below need. -/
private theorem system_of_boundary_eq {B C : Boundary Party} (hBC : B = C) (x : B.Exit) :
    B.system x = C.system (Equiv.cast (congrArg Boundary.Exit hBC) x) := by
  cases hBC
  rfl

/-- **What survives a quota-feasible run**, read off its public transcript: two
`2 ^ ℓ`-element key registers when the announced flag accepts, and no key register otherwise. -/
theorem system_eq_of_sifted (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (boundary N nK mZ mX ℓ ℓEV leakEC).Exit)
    (h : Sampling.HasQuotas nK mZ mX
      (publicTranscriptEquiv N nK mZ mX ℓ ℓEV leakEC e).control) :
    (boundary N nK mZ mX ℓ ℓEV leakEC).system e =
      if ((publicTranscriptEquiv N nK mZ mX ℓ ℓEV leakEC e).sifted h).2 = 0 then
        FinalStage.keySystem ℓ
      else FinalStage.abortSystem := by
  refine (Boundary.system_graftExitEquiv (Measurement.lateSelectionBoundary N nK mZ mX)
    (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC) e).trans ?_
  set f := Boundary.graftExitEquiv (Measurement.lateSelectionBoundary N nK mZ mX)
    (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC) e with hf
  have hquota : Sampling.HasQuotas nK mZ mX
      (lateSelectionExitEquiv N nK mZ mX f.1) := h
  have hboundary := completeContinuationBoundary_of_hasQuotas
    N nK mZ mX ℓ ℓEV leakEC f.1 hquota
  have hflag : ((publicTranscriptEquiv N nK mZ mX ℓ ℓEV leakEC e).sifted h).2 =
      (rawClassicalTailExitEquiv (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC
          (Equiv.cast (congrArg Boundary.Exit hboundary) f.2)).2 := by
    have htail : (publicTranscriptEquiv N nK mZ mX ℓ ℓEV leakEC e).tail =
        tailAnnouncementsEquiv N nK mZ mX ℓ ℓEV leakEC f.1 f.2 := rfl
    simp only [PublicTranscript.sifted, htail, tailAnnouncementsEquiv, dif_pos hquota,
      Equiv.trans_apply, Equiv.cast_apply, cast_cast, cast_eq]
  rw [hflag, system_of_boundary_eq hboundary f.2, system_rawClassicalTailBoundary]

/-- **A run whose announced control is short of a quota ends with no key register**, and both
complete local measurement records have been discarded. -/
theorem system_eq_of_shortage (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (e : (boundary N nK mZ mX ℓ ℓEV leakEC).Exit)
    (h : ¬Sampling.HasQuotas nK mZ mX
      (publicTranscriptEquiv N nK mZ mX ℓ ℓEV leakEC e).control) :
    (boundary N nK mZ mX ℓ ℓEV leakEC).system e =
      Measurement.lateSelectionAbortSystem := by
  refine (Boundary.system_graftExitEquiv (Measurement.lateSelectionBoundary N nK mZ mX)
    (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC) e).trans ?_
  set f := Boundary.graftExitEquiv (Measurement.lateSelectionBoundary N nK mZ mX)
    (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC) e with hf
  have hquota : ¬Sampling.HasQuotas nK mZ mX
      (lateSelectionExitEquiv N nK mZ mX f.1) := h
  rw [system_of_boundary_eq
    (completeContinuationBoundary_of_shortage N nK mZ mX ℓ ℓEV leakEC f.1 hquota) f.2]
  rfl

end QKD.BB84
