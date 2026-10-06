import QCryptLean.QKD.BB84.FinalStage
import Mathlib.Util.AssertNoSorry

/-!
# Regression probes for the direct BB84 final stage

These fixtures exercise the semantic flag, heterogeneous boundary, local key actions, and direct
abort path. The local and abort checks retain arbitrary and non-Hermitian operator inputs.
-/

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace QKD.BB84.FinalStage.Probes
open TypedLOCC

open TypedLOCC.TwoParty
open QKD.BB84.Engine

/-! ## Public semantic flag and conditional boundary -/

theorem decision_announce_is_id
    (n m ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ)
    (as bs : Fin (n - bb84KeyRoundCount n m) → Fin 2)
    (evSeed : KeyHashSeed n ellEV peSel) (evTag : Fin (2 ^ ellEV))
    (syn : Fin (2 ^ leakEC)) (flag : Fin 2) :
    (decisionAnnouncement n m ellEV peSel xSel leakEC ec delta Q
      as bs evSeed evTag syn).announce flag = flag := rfl

/-- A fixture with `delta = 0` and `Q = 1` freezes their distinct argument positions in the raw
semantic readout; it does not add a parameter-range hypothesis. -/
theorem decision_delta_ne_Q_rawKraus
    (n m ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (as bs : Fin (n - bb84KeyRoundCount n m) → Fin 2)
    (evSeed : KeyHashSeed n ellEV peSel) (evTag : Fin (2 ^ ellEV))
    (syn : Fin (2 ^ leakEC)) (flag : Fin 2) :
    (decisionAnnouncement n m ellEV peSel xSel leakEC ec 0 1
      as bs evSeed evTag syn).kraus flag () =
      Instrument.nondemolitionReadoutKraus
        (QKD.BB84.Model.acceptFlagOf n m ellEV peSel xSel leakEC ec 0 1
          as bs evSeed evTag syn) flag := rfl

theorem flagBoundary_accept (ell : ℕ) :
    flagBoundary ell 0 = .leaf (keySystem ell) := by
  simp [flagBoundary]

theorem flagBoundary_abort (ell : ℕ) :
    flagBoundary ell 1 = .leaf abortSystem := by
  simp [flagBoundary]

theorem disposition_accept (ell : ℕ) : disposition ell 0 = .accept ell := by
  simp [disposition]

theorem disposition_abort (ell : ℕ) : disposition ell 1 = .abort := by
  simp [disposition]

/-- A dependent exit can be destructed only after reducing the conditional boundary. -/
theorem flagBoundary_exit_unique (ell : ℕ) (flag : Fin 2)
    (e f : (flagBoundary ell flag).Exit) : e = f := by
  by_cases hflag : flag = 0
  · subst flag
    change Unit at e f
    cases e
    cases f
    rfl
  · have hflag_one : flag = 1 := Fin.eq_one_of_ne_zero flag hflag
    subst flag
    change Unit at e f
    cases e
    cases f
    rfl

def acceptExit (ell : ℕ) : (boundary ell).Exit := ⟨0, ()⟩
def abortExit (ell : ℕ) : (boundary ell).Exit := ⟨1, ()⟩

theorem outputLayout_accept_disposition (ell : ℕ) :
    (outputLayout ell).disposition (acceptExit ell) = .accept ell := by
  simp [outputLayout, acceptExit, disposition]

theorem outputLayout_abort_disposition (ell : ℕ) :
    (outputLayout ell).disposition (abortExit ell) = .abort := by
  simp [outputLayout, abortExit, disposition]

theorem accept_alice_register (ell : ℕ) :
    ((boundary ell).system (acceptExit ell)).reg .alice = Fin (2 ^ ell) := by
  change (keySystem ell).reg .alice = Fin (2 ^ ell)
  rfl

theorem abort_alice_register (ell : ℕ) :
    ((boundary ell).system (abortExit ell)).reg .alice = Unit := by
  change abortSystem.reg .alice = Unit
  rfl

/-! Concrete reduction of the continuation is checked only after the semantic flag is known. -/

theorem continuation_accept
    (n ell : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ell peSel) (syn : Fin (2 ^ leakEC)) :
    continuation n ell peSel leakEC ec seed syn 0 =
      acceptContinuation n ell peSel leakEC ec seed syn 0 := by
  simp [continuation]

theorem continuation_abort
    (n ell : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ell peSel) (syn : Fin (2 ^ leakEC)) :
    continuation n ell peSel leakEC ec seed syn 1 = discardKeys n := by
  simp [continuation]

/-! ## Arbitrary-operator local key classicality -/

/-- The instrument stored by Alice's actual action is definitionally the advertised local
measure-and-prepare instrument. -/
theorem aliceKeyAction_instrument
    (n ell : ℕ) (peSel : Fin n → Bool)
    (seed : KeyHashSeed n ell peSel) (flag : Fin 2) :
    (aliceKeyAction n ell peSel seed flag).instrument =
      Instrument.functionAndForget
        (QKD.BB84.Model.aliceKeySlotOf n ell peSel seed flag) := rfl

/-- Alice's actual final-stage action destroys every output off-diagonal, for an arbitrary raw
operator and without a count, reconciliation-success, positivity, or trace-one hypothesis. -/
theorem aliceKeyAction_local_offDiagonal
    (n ell : ℕ) (peSel : Fin n → Bool)
    (seed : KeyHashSeed n ell peSel) (flag : Fin 2)
    (rho : Op (Fin (2 ^ n))) (a a' : Fin (2 ^ ell)) (haa' : a ≠ a') :
    ((Instrument.functionAndForget
      (QKD.BB84.Model.aliceKeySlotOf n ell peSel seed flag)).operation () rho) a a' = 0 := by
  rw [Instrument.functionAndForget_operation_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases ha : a = QKD.BB84.Model.aliceKeySlotOf n ell peSel seed flag x
  · have ha' : a' ≠ QKD.BB84.Model.aliceKeySlotOf n ell peSel seed flag x := by
      intro h
      exact haa' (ha.trans h.symm)
    simp [ha, ha']
  · simp [ha]

/-- The corresponding statement for Bob's actual reconciliation-and-hash action, again on every
operator and with no correctness assumption. -/
theorem bobKeyAction_instrument
    (n ell : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ell peSel) (syn : Fin (2 ^ leakEC))
    (flag : Fin 2) :
    (bobKeyAction n ell peSel leakEC ec seed syn flag).instrument =
      Instrument.functionAndForget
        (QKD.BB84.Model.bobKeySlotOf n ell peSel leakEC ec seed syn flag) := rfl

theorem bobKeyAction_local_offDiagonal
    (n ell : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ell peSel) (syn : Fin (2 ^ leakEC))
    (flag : Fin 2) (rho : Op (Fin (2 ^ n)))
    (b b' : Fin (2 ^ ell)) (hbb' : b ≠ b') :
    ((Instrument.functionAndForget
      (QKD.BB84.Model.bobKeySlotOf n ell peSel leakEC ec seed syn flag)).operation () rho) b b' = 0
          := by
  rw [Instrument.functionAndForget_operation_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hb : b = QKD.BB84.Model.bobKeySlotOf n ell peSel leakEC ec seed syn flag x
  · have hb' : b' ≠ QKD.BB84.Model.bobKeySlotOf n ell peSel leakEC ec seed syn flag x := by
      intro h
      exact hbb' (hb.trans h.symm)
    simp [hb, hb']
  · simp [hb]

/-! ## Direct abort trace absorption on a non-Hermitian input -/

def rawJoint (alice bob : Fin 2) : (rawSystem 1).total :=
  (pairEquiv (Fin 2) (Fin 2)).symm (alice, bob)

def rawOffDiagonal : Op (rawSystem 1).total :=
  Matrix.single (rawJoint 0 0) (rawJoint 1 0) 1

def rawDiagonal : Op (rawSystem 1).total :=
  Matrix.single (rawJoint 0 0) (rawJoint 0 0) 1

theorem rawOffDiagonal_not_selfAdjoint : rawOffDiagonalᴴ ≠ rawOffDiagonal := by
  have hne : rawJoint 1 0 ≠ rawJoint 0 0 := by
    intro h
    have hp := congrArg (pairEquiv (Fin 2) (Fin 2)) h
    simp [rawJoint] at hp
  intro h
  have h01 := congrFun (congrFun h (rawJoint 0 0)) (rawJoint 1 0)
  simp [rawOffDiagonal, Matrix.conjTranspose_apply, hne, hne.symm] at h01

/-- The direct raw-register abort program preserves the trace of every operator. -/
theorem discardKeys_trace (n : ℕ) (rho : Op (rawSystem n).total) :
    ∑ z, (discardKeys n).denote rho z z = ∑ x, rho x x := by
  simpa [Program.denote] using
    Instrument.channel_trace_eq ((discardKeys n).toInstrument) rho

/-- Hence the explicit non-Hermitian matrix unit is absorbed to the zero scalar on abort. -/
theorem discardKeys_rawOffDiagonal_trace :
    ∑ z, (discardKeys 1).denote rawOffDiagonal z z = 0 := by
  rw [discardKeys_trace]
  change Matrix.trace rawOffDiagonal = 0
  rw [rawOffDiagonal, Matrix.trace_single_eq_of_ne]
  intro h
  have hp := congrArg (pairEquiv (Fin 2) (Fin 2)) h
  simp [rawJoint] at hp

theorem discardKeys_rawDiagonal_trace :
    ∑ z, (discardKeys 1).denote rawDiagonal z z = 1 := by
  rw [discardKeys_trace]
  change Matrix.trace rawDiagonal = 1
  exact Matrix.trace_single_eq_same _ _

end QKD.BB84.FinalStage.Probes

