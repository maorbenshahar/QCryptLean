import QCryptLean.QKD.BB84.Measurement.Streaming
import QCryptLean.QKD.BB84.Program

/-!
# Streaming witness for the complete measure-first BB84 program

This module identifies the explicit classical continuation of the complete measure-first program
and states that the existing destructive schedule is its measurement prefix.  The certificate
covers local measurement timing and the accumulator block invariant; it does not assert that the
entire later tail is classical and does not prove either BB84 security theorem.

Renner, arXiv:quant-ph/0512258v2, source lines 673--736, and Pfister et al.,
arXiv:1506.07502v3, Sections IV--V motivate measurement before later announcements.  The exact
graft identity is specific to the program constructors in this library.
-/

noncomputable section

namespace QKD.BB84

open TypedLOCC
open QKD.BB84
open QKD.BB84.Engine

/-- The actual late-public selection and retained classical tail, starting only after the future
quantum stream is empty and all local records have been accumulated. -/
noncomputable def classicalContinuation
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Program (Measurement.weightedStreamSystem
      (Measurement.finishAcc Unit N) 0)
      (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC) :=
  (Measurement.latePublicSelectionProgram N nK mZ mX).graft
    (QKD.BB84.completeContinuation N nK mZ mX ℓ ℓEV leakEC ec delta Q)

/-- The actual complete program is the destructive schedule grafted to the exact classical
continuation.  This named equality fixes the continuation consumed by the recursive certificate.
-/
theorem program_eq_schedule_graft_classicalContinuation
    (pA pB : PMF Measurement.Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    QKD.BB84.program pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q =
      (Measurement.weightedMeasurementSchedule pA pB N).graft (fun _ =>
        classicalContinuation
          N nK mZ mX ℓ ℓEV leakEC ec delta Q) := by
  have schedule_graft_assoc
      (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (m : ℕ)
      {B : Boundary TwoParty.Party}
      (k : Program (Measurement.weightedStreamSystem
        (Measurement.finishAcc F m) 0) B)
      {C : B.Exit → Boundary TwoParty.Party}
      (l : ∀ e : B.Exit, Program (B.system e) (C e)) :
      ((Measurement.weightedMeasurementScheduleAux pA pB F m).graft
          (C := fun _ => B) (fun _ => k)).graft l =
        (Measurement.weightedMeasurementScheduleAux pA pB F m).graft
          (C := fun _ => B.graft C) (fun _ => k.graft l) := by
    induction m generalizing F with
    | zero => rfl
    | succ m ih =>
        rw [Measurement.weightedMeasurementScheduleAux_succ]
        simp only [Program.graft_priv]
        apply congrArg (Program.priv
          (Measurement.weightedStreamAliceAction pA F m))
        apply congrArg (Program.priv
          (Measurement.weightedStreamBobAction pA pB F m))
        have h : Measurement.weightedStreamSystem (F × Measurement.StoredRecord) m =
            (Measurement.weightedStreamBobAction pA pB F m).out := by
          simp only [Measurement.weightedStreamBobAction, Measurement.weightedStreamAliceAction,
            PrivateAction.out_ofInstrument, Measurement.weightedStreamSystem,
            TwoParty.set_alice, TwoParty.set_bob]
        refine (congrArg (fun p : Program
          (Measurement.weightedStreamBobAction pA pB F m).out B => p.graft l)
          (Program.graft_castInput h
            (Measurement.weightedMeasurementScheduleAux pA pB (F × Measurement.StoredRecord) m)
            (fun _ => k))).trans ?_
        refine (Program.graft_castInput h _ l).trans ?_
        refine Eq.trans ?_ (Program.graft_castInput h
          (Measurement.weightedMeasurementScheduleAux pA pB (F × Measurement.StoredRecord) m)
          (fun _ => k.graft l)).symm
        exact congrArg (cast _) (ih (F := F × Measurement.StoredRecord) k)
  unfold QKD.BB84.program classicalContinuation
    Measurement.weightedLatePublicSelectionProgram
  exact schedule_graft_assoc Unit N
      (Measurement.latePublicSelectionProgram N nK mZ mX)
      (QKD.BB84.completeContinuation N nK mZ mX ℓ ℓEV leakEC ec delta Q)

/-- The complete physical program begins with all `N` private destructive Alice-then-Bob rounds
and reaches its explicit late-public/classical continuation only after the future stream is empty.
The per-step online identity and accumulator block invariant are included in the certificate; no
sampling or security transfer is concluded here. -/
theorem program_streaming
    (pA pB : PMF Measurement.Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Measurement.Streaming.StreamingMeasurementPrefix pA pB N
      (QKD.BB84.program pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q) := by
  refine ⟨classicalContinuation
    N nK mZ mX ℓ ℓEV leakEC ec delta Q, ?_, ?_, ?_⟩
  · exact program_eq_schedule_graft_classicalContinuation
      pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q
  · intro F _ _ _ n
    exact Measurement.Streaming.weightedStreamRoundProgram_denote_eq_online
      pA pB F n
  · intro F _ _ _ n rho fA fA' fB fB' hzero rA rA' rB rB'
    exact Measurement.weightedMeasurementScheduleAux_preserves_accumulator_block_zero
      pA pB F n rho fA fA' fB fB' hzero rA rA' rB rB'

end QKD.BB84
