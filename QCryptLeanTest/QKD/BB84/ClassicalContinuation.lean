import QCryptLean.QKD.BB84.ClassicalContinuation
import Mathlib.Util.AssertNoSorry
import QCryptLean.QKD.BB84.CompleteOutput

/-!
# Tests for recursive classical continuation

The test enforces the proved recursive-classicality, CQ-creation, and endpoint surfaces and
exercises the explicit predicates, instrument/program syntax, public metadata, quota branches,
final leaves, and reference coordinates.
The negative fixture constructs a coherent intermediate that is later erased: its endpoint is
diagonal, but the recursive all-step certificate fails independently of those theorems.
-/

open Quantum.Operators (Op)

open Quantum.Channels (
  mapTensorId)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

open _root_.LOCC
open _root_.LOCC.TwoParty
open QKD.BB84
open QKD.BB84.Measurement
open QKD.BB84.Sampling
open QKD.BB84.FiniteKey

namespace QCryptLeanTest.BB84.ClassicalContinuation

/-! ## Complete physical-protocol CQ regression -/

/-- The complete physical protocol kills every off-diagonal public/honest-register block while
retaining independently chosen reference row and column coordinates.  This is a direct application
of the full CQ endpoint theorem, so the executable test exercises the actual weighted BB84
program rather than only the generic predicate eliminator. -/
theorem protocol_real_referenceBlock_offDiagonal
    (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ)
    {E : Type}
    (rho : Op ((weightedStreamSystem Unit N).total × E))
    (x x' : (construction pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).boundary.space)
    (e e' : E) (hxx' : x ≠ x') :
    mapTensorId (QKD.BB84.protocol
          pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real E rho
        (x, e) (x', e') = 0 :=
  QKD.BB84.protocol_real_isClassicalOnFirst
    pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q rho x x' e e' hxx'

/-! ## Endpoint-only witness rejection -/

/-- The normalized column that prepares an equal coherent superposition from `Unit`. -/
def coherentPrepareKraus : Matrix (Fin 2) Unit ℂ :=
  fun _ _ => (Real.sqrt 2 : ℂ)⁻¹

/-- The coherent preparation column is normalized. -/
theorem coherentPrepareKraus_complete :
    coherentPrepareKrausᴴ * coherentPrepareKraus = 1 := by
  have hsqrt :
      (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    rw [← mul_inv]
    have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      norm_cast
      rw [← sq]
      exact Real.sq_sqrt (by norm_num)
    rw [h]
    norm_num
  ext i j
  rcases i with ⟨⟩
  rcases j with ⟨⟩
  simp [coherentPrepareKraus, Matrix.mul_apply, hsqrt]

/-- One-outcome coherent preparation with an explicit completeness certificate. -/
def coherentPrepareInstrument : Instrument Unit (Fin 2) Unit :=
  Instrument.ofFine (fun _ => coherentPrepareKraus) (by
    simpa only [Fintype.sum_unique] using coherentPrepareKraus_complete)

/-- Initial and erased terminal multipartite system of the negative fixture. -/
def unitUnitSystem : MultipartiteSystem Party := TwoParty.system Unit Unit

/-- Alice coherently prepares her intermediate qubit. -/
@[implicit_reducible] def coherentPrepareAction : PrivateAction unitUnitSystem :=
  PrivateAction.ofInstrument Party.alice
     coherentPrepareInstrument

/-- Alice subsequently erases the coherent intermediate by a real measure-and-prepare action. -/
@[implicit_reducible] def erasePreparedAction : PrivateAction (system (Fin 2) Unit) :=
  PrivateAction.ofInstrument Party.alice
    (Instrument.functionAndForget (fun _ : Fin 2 => ()))

/-- Coherent preparation followed by erasure has a diagonal endpoint but a nonclassical first
intermediate branch. -/
def coherentThenEraseProgram : Program unitUnitSystem :=
  coherentPrepareAction.then (erasePreparedAction.then (.done PUnit.unit))

/-- The scalar input operator with entry one. -/
def unitInput : Op unitUnitSystem.total := fun _ _ => 1

/-- Output coordinate with Alice bit zero. -/
def bitOutputZero : coherentPrepareAction.out.total :=
  coherentPrepareAction.out.pairEquiv.symm ((0 : Fin 2), ())

/-- Output coordinate with Alice bit one. -/
def bitOutputOne : coherentPrepareAction.out.total :=
  coherentPrepareAction.out.pairEquiv.symm ((1 : Fin 2), ())

/-- The unique input is honest-register diagonal. -/
theorem unitInput_diagonal : unitUnitSystem.HonestRegistersDiagonal unitInput := by
  intro q q' h
  exfalso
  rcases h with h | h
  · apply h
    cases q .alice
    cases q' .alice
    rfl
  · apply h
    cases q .bob
    cases q' .bob
    rfl

/-- The first raw branch has a nonzero off-diagonal Alice entry. -/
theorem coherentPrepareAction_offDiagonal :
    (coherentPrepareAction.liftedOperation () unitInput)
        bitOutputZero bitOutputOne = (1 / 2 : ℂ) := by
  refine (Instrument.liftAt_alice_operation_apply unitUnitSystem coherentPrepareInstrument
    () unitInput (0 : Fin 2) (1 : Fin 2) () ()).trans ?_
  have hsub (f g : Unit → unitUnitSystem.total) :
      unitInput.submatrix f g = (1 : Matrix Unit Unit ℂ) := by
    ext i j
    rcases i with ⟨⟩
    rcases j with ⟨⟩
    rfl
  refine (congrArg (fun M => coherentPrepareInstrument.operation () M 0 1)
    (hsub _ _)).trans ?_
  have hsqrt :
      (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    rw [← mul_inv]
    have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      norm_cast
      rw [← sq]
      exact Real.sq_sqrt (by norm_num)
    rw [h]
    norm_num
  change (∑ _ : Unit, (coherentPrepareKraus * (1 : Matrix Unit Unit ℂ) *
    coherentPrepareKrausᴴ) 0 1) = _
  rw [Fintype.sum_unique]
  simp [coherentPrepareKraus, Matrix.mul_apply, hsqrt]

/-- The first action does not preserve honest-register diagonality. -/
theorem coherentPrepareAction_not_preserving :
    ¬ coherentPrepareAction.PreservesHonestRegistersDiagonal := by
  intro h
  have hz := h () unitInput unitInput_diagonal bitOutputZero bitOutputOne
    (Or.inl (by decide))
  rw [coherentPrepareAction_offDiagonal] at hz
  norm_num at hz

/-- The final Unit/Unit output is diagonal for every input, independently of the main
certificate. -/
theorem coherentThenErase_endpointDiagonal (rho : Op unitUnitSystem.total) :
    (Boundary.leaf unitUnitSystem).HonestRegistersDiagonal
      (coherentThenEraseProgram.denote rho) := by
  intro e q q' h
  rcases e with ⟨⟩
  exfalso
  rcases h with h | h
  · apply h
    cases q .alice
    cases q' .alice
    rfl
  · apply h
    cases q .bob
    cases q' .bob
    rfl

/-- Endpoint diagonality does not suffice for the recursive all-step certificate. -/
theorem coherentThenErase_rejected :
    ¬ coherentThenEraseProgram.IsHonestClassical := by
  intro h
  exact coherentPrepareAction_not_preserving
    ((Program.isHonestClassical_priv_iff _ _).mp h).1

/-- A matrix unit carrying coherence between the two computational basis values. -/
def coherentBitMatrixUnit : Op (Fin 2) := Matrix.single 0 1 1

/-- A constant nondemolition readout retains coherence inside its unique outcome fibre, so the
generic preservation theorem cannot be read as classicalization of arbitrary input. -/
theorem constantReadout_retainsCoherence :
    ((Instrument.nondemolitionReadout (fun _ : Fin 2 => ())).operation ()
      coherentBitMatrixUnit) 0 1 = 1 := by
  simp [coherentBitMatrixUnit]

/-! ## Actual public-control and complete-program syntax

The basis/shuffle announcement identities and the late-public program shape are checked once, in
`LatePublicControlAudit` (`QCryptLeanTest/QKD/BB84/Measurement/LatePublicControl.lean`);
this section continues directly with the quota-dependent continuation. -/

/-- Canonical zero-round raw control. -/
def emptyControl : RawControl 0 := defaultRawControl 0

/-- Zero rounds and zero quotas select the actual successful child boundary. -/
theorem zeroRound_zeroQuota_success :
    QKD.BB84.completeContinuationBoundary 0 0 0 0 0 0 0
        (lateSelectionExit 0 0 0 0 emptyControl) =
      QKD.BB84.rawClassicalTailBoundary 0 0 0 0 (@packedPESel 0 0 0) 0 := by
  have h : HasQuotas 0 0 0 emptyControl := by decide
  change (if HasQuotas 0 0 0
      ((QKD.BB84.lateSelectionExitEquiv 0 0 0 0)
        ((QKD.BB84.lateSelectionExitEquiv 0 0 0 0).symm emptyControl)) then
      QKD.BB84.rawClassicalTailBoundary 0 0 0 0 (@packedPESel 0 0 0) 0
    else .leaf lateSelectionAbortSystem) = _
  rw [Equiv.apply_symm_apply, ite_eq_left h]

/-- A positive quota at zero rounds selects the actual key-free shortage boundary. -/
theorem zeroRound_positiveQuota_shortage :
    QKD.BB84.completeContinuationBoundary 0 1 0 0 0 0 0
        (lateSelectionExit 0 1 0 0 emptyControl) =
      .leaf lateSelectionAbortSystem := by
  have h : ¬ HasQuotas 1 0 0 emptyControl := by decide
  change (if HasQuotas 1 0 0
      ((QKD.BB84.lateSelectionExitEquiv 0 1 0 0)
        ((QKD.BB84.lateSelectionExitEquiv 0 1 0 0).symm emptyControl)) then
      QKD.BB84.rawClassicalTailBoundary 1 0 0 0 (@packedPESel 1 0 0) 0
    else .leaf lateSelectionAbortSystem) = _
  rw [Equiv.apply_symm_apply, ite_eq_right h]

/-- One mismatched round retains its announced raw metadata and has no positive key quota. -/
def mismatchControl : RawControl 1 :=
  ⟨(fun _ => Basis.z), (fun _ => Basis.x),
    increasingShuffle (fun _ => Basis.z) (fun _ => Basis.x)⟩

/-- The all-mismatched control takes the shortage branch. -/
theorem mismatchControl_shortage : ¬ HasQuotas 1 0 0 mismatchControl := by
  decide

/-- The shortage exit retains both basis strings and the exact empty shuffle. -/
theorem mismatchExit_metadata :
    let e := lateSelectionExit 1 1 0 0 mismatchControl
    e.1 = mismatchControl.a ∧ e.2.1 = mismatchControl.b ∧
      e.2.2.1 = mismatchControl.order := by
  exact ⟨rfl, rfl, rfl⟩

/-- Equal two-round Z strings with their increasing matched order. -/
def twoZControl : RawControl 2 := defaultRawControl 2

/-- One key position is available in the concrete nonzero-round control. -/
theorem twoZControl_hasStrictQuota : HasQuotas 1 0 0 twoZControl := by
  decide

/-- The nonzero-round successful public branch reaches the actual classical-tail boundary. -/
theorem twoZControl_success :
    QKD.BB84.completeContinuationBoundary 2 1 0 0 0 0 0
        (lateSelectionExit 2 1 0 0 twoZControl) =
      QKD.BB84.rawClassicalTailBoundary 1 0 0 0 (@packedPESel 1 0 0) 0 := by
  change (if HasQuotas 1 0 0
      ((QKD.BB84.lateSelectionExitEquiv 2 1 0 0)
        ((QKD.BB84.lateSelectionExitEquiv 2 1 0 0).symm twoZControl)) then
      QKD.BB84.rawClassicalTailBoundary 1 0 0 0 (@packedPESel 1 0 0) 0
    else .leaf lateSelectionAbortSystem) = _
  rw [Equiv.apply_symm_apply, ite_eq_left twoZControl_hasStrictQuota]

/-- A nondegenerate basis law: probability `1/3` selects `X`, while `2/3` selects `Z`. -/
noncomputable def biasedBasisLaw : PMF Basis :=
  PMF.map (fun b : Bool => if b then Basis.x else Basis.z)
    (ProbabilityTheory.bernoulliMeasure true false
      ⟨(1 : ℝ) / 3, by constructor <;> norm_num⟩).toPMF

/-- Distinct local basis laws occur in the actual first round before its continuation. -/
theorem biased_zeroSupport_lateProgram_shape
    (k : Program (weightedStreamSystem (finishAcc Unit 1) 0)) :
    measureRounds biasedBasisLaw (PMF.pure Basis.z) Unit 1 k =
      (measureAlice biasedBasisLaw Unit 0).then
        ((measureBob (PMF.pure Basis.z) Unit 0).then k) := rfl

/-- The native construction hands its completed records to an honest-classical continuation. -/
theorem program_shape
    (pA pB : PMF Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    ∃ k : Program (weightedStreamSystem (finishAcc Unit N) 0) (QKD.KeyEnd Party.alice Party.bob),
      construction pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q =
        measureRounds pA pB Unit N k ∧ k.IsHonestClassical :=
  exists_eq_measureRounds_isHonestClassical pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q

/-! ## Arbitrary complex reference coordinates

(The final accepting/aborting exit multipartite systems are checked once, in `ClassicalTailAudit`
(`QCryptLeanTest/QKD/BB84/MemoryFree.lean`).) -/

/-- A non-Hermitian matrix unit with unequal reference row and column indices. -/
def unequalReferenceMatrixUnit (d : ℕ) [NeZero d] : Op (Fin d × Fin 2) :=
  Matrix.single (0, 0) (0, 1) 1

/-- The selected unequal-reference entry of the matrix unit is nonzero. -/
theorem unequalReferenceMatrixUnit_entry (d : ℕ) [NeZero d] :
    unequalReferenceMatrixUnit d
      (0, 0) (0, 1) = 1 := by
  simp [unequalReferenceMatrixUnit]

/-- The reference row and column coordinates used above are genuinely distinct. -/
theorem unequalReference_indices : (0 : Fin 2) ≠ 1 := by
  decide

end QCryptLeanTest.BB84.ClassicalContinuation
