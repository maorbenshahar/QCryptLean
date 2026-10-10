import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.LOCC.Program.ExitWeight
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
open _root_.LOCC

open _root_.LOCC.TwoParty
open QKD.BB84.FiniteKey QKD.BB84.Measurement

/-! ## Public semantic flag and conditional boundary -/

theorem decision_announce_is_id
    (n m ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (delta Q : ℝ)
    (as bs : Fin (min n m) → Fin 2)
    (evSeed : KeyHashSeed n ellEV peSel) (evTag : Bits ellEV)
    (syn : Bits leakEC) (flag : Bool) :
    (announceAccept (A := Bits n) (xSel := xSel) ec delta Q
      as bs evSeed evTag syn).announce flag = flag := rfl

/-- A fixture with `delta = 0` and `Q = 1` freezes their distinct argument positions in the raw
semantic readout; it does not add a parameter-range hypothesis. -/
theorem decision_delta_ne_Q_rawKraus
    (n m ellEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (as bs : Fin (min n m) → Fin 2)
    (evSeed : KeyHashSeed n ellEV peSel) (evTag : Bits ellEV)
    (syn : Bits leakEC) (flag : Bool) :
    (announceAccept (A := Bits n) (xSel := xSel) ec 0 1
      as bs evSeed evTag syn).kraus flag () =
      Instrument.nondemolitionReadoutKraus
        (QKD.BB84.acceptFlag n m ellEV peSel xSel leakEC ec 0 1
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
    ((boundary ell).system (acceptExit ell)).reg .alice = Bits ell := by
  change (keySystem ell).reg .alice = Bits ell
  rfl

theorem abort_alice_register (ell : ℕ) :
    ((boundary ell).system (abortExit ell)).reg .alice = Unit := by
  change abortSystem.reg .alice = Unit
  rfl

/-! ## Arbitrary-operator local key classicality -/

/-- The instrument stored by Alice's actual action is definitionally the advertised local
measure-and-prepare instrument. -/
theorem aliceKeyAction_instrument
    (n ell : ℕ) (peSel : Fin n → Bool)
    (seed : KeyHashSeed n ell peSel) :
    (hashAlice (B := Bits n) seed).instrument =
      Instrument.functionAndForget
        (QKD.BB84.aliceKey n ell peSel seed) := rfl

/-- Alice's actual final-stage action destroys every output off-diagonal, for an arbitrary raw
operator and without a count, reconciliation-success, positivity, or trace-one hypothesis. -/
theorem aliceKeyAction_local_offDiagonal
    (n ell : ℕ) (peSel : Fin n → Bool)
    (seed : KeyHashSeed n ell peSel)
    (rho : Quantum.Operators.Op (Bits n)) (a a' : Bits ell) (haa' : a ≠ a') :
    ((Instrument.functionAndForget
      (QKD.BB84.aliceKey n ell peSel seed)).operation () rho) a a' = 0 := by
  rw [Instrument.functionAndForget_operation_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases ha : a = QKD.BB84.aliceKey n ell peSel seed x
  · have ha' : a' ≠ QKD.BB84.aliceKey n ell peSel seed x := by
      intro h
      exact haa' (ha.trans h.symm)
    simp [ha, ha']
  · simp [ha]

/-- The corresponding statement for Bob's actual
-- reconciliation-and-hash action, again on every
operator and with no correctness assumption. -/
theorem bobKeyAction_instrument
    (n ell : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ell peSel) (syn : Bits leakEC)
    :
    (correctAndHashBob (A := Bits ell) ec seed syn).instrument =
      Instrument.functionAndForget
        (QKD.BB84.bobKey n ell peSel leakEC ec seed syn) := rfl

theorem bobKeyAction_local_offDiagonal
    (n ell : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC)
    (seed : KeyHashSeed n ell peSel) (syn : Bits leakEC)
    (rho : Quantum.Operators.Op (Bits n))
    (b b' : Bits ell) (hbb' : b ≠ b') :
    ((Instrument.functionAndForget
      (QKD.BB84.bobKey n ell peSel leakEC ec seed syn)).operation () rho) b b' = 0
          := by
  rw [Instrument.functionAndForget_operation_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hb : b = QKD.BB84.bobKey n ell peSel leakEC ec seed syn x
  · have hb' : b' ≠ QKD.BB84.bobKey n ell peSel leakEC ec seed syn x := by
      intro h
      exact hbb' (hb.trans h.symm)
    simp [hb, hb']
  · simp [hb]

/-! ## Direct abort trace absorption on a non-Hermitian input -/

def rawJoint (alice bob : Fin 2) : (rawSystem 1).total :=
  (pairEquiv (Bits 1) (Bits 1)).symm (fun _ => alice, fun _ => bob)

def rawOffDiagonal : Quantum.Operators.Op (rawSystem 1).total :=
  Matrix.single (rawJoint 0 0) (rawJoint 1 0) 1

def rawDiagonal : Quantum.Operators.Op (rawSystem 1).total :=
  Matrix.single (rawJoint 0 0) (rawJoint 0 0) 1

theorem rawOffDiagonal_not_selfAdjoint : rawOffDiagonalᴴ ≠ rawOffDiagonal := by
  have hne : rawJoint 1 0 ≠ rawJoint 0 0 := by
    intro h
    exact Fin.zero_ne_one
      (congrArg (fun q : (rawSystem 1).total => q .alice 0) h).symm
  intro h
  have h01 := congrFun (congrFun h (rawJoint 0 0)) (rawJoint 1 0)
  simp [rawOffDiagonal, Matrix.conjTranspose_apply, hne, hne.symm] at h01

/-- The direct raw-register abort program preserves the trace of every operator. -/
theorem discardKeys_trace (n : ℕ) (rho : Quantum.Operators.Op (rawSystem n).total) :
    ∑ z, ((discardAlice (A := Bits n) (B := Bits n)).then
      (discardBob.then (.done KeyEnd.abort))).denote rho z z = ∑ x, rho x x := by
  exact Program.trace_denote _ rho

/-- Hence the explicit non-Hermitian matrix unit is absorbed to the zero scalar on abort. -/
theorem discardKeys_rawOffDiagonal_trace :
    ∑ z, ((discardAlice (A := Bits 1) (B := Bits 1)).then
      (discardBob.then (.done KeyEnd.abort))).denote rawOffDiagonal z z = 0 := by
  rw [discardKeys_trace]
  change Matrix.trace rawOffDiagonal = 0
  rw [rawOffDiagonal, Matrix.trace_single_eq_of_ne]
  intro h
  exact Fin.zero_ne_one (congrArg (fun q : (rawSystem 1).total => q .alice 0) h)

theorem discardKeys_rawDiagonal_trace :
    ∑ z, ((discardAlice (A := Bits 1) (B := Bits 1)).then
      (discardBob.then (.done KeyEnd.abort))).denote rawDiagonal z z = 1 := by
  rw [discardKeys_trace]
  change Matrix.trace rawDiagonal = 1
  exact Matrix.trace_single_eq_same _ _

end QKD.BB84.FinalStage.Probes

