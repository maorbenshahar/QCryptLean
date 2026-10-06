import QCryptLean.QKD.Protocol
import QCryptLeanTest.QKD.OutputLayoutProbes
import Mathlib.Util.AssertNoSorry

/-!
# Definition-level probes for the direct QKD protocol surface

The fixtures reuse the heterogeneous output-layout test boundary.  Positive claims unfold the
protocol definitions or invoke typed-program/channel lemmas; no security conclusion is
provided by the constructor.
-/

open Quantum.Operators

noncomputable section

namespace QCryptLeanTest.ProtocolProbes

open TypedLOCC

open QKD
open OutputLayoutProbes

/-- Restrict the heterogeneous layout to one terminal public exit. -/
def leafLayout (e₀ : OutputLayoutProbes.boundary.Exit) :
    OutputLayout (.leaf (OutputLayoutProbes.boundary.system e₀)) where
  alice := OutputLayoutProbes.layout.alice
  bob := OutputLayoutProbes.layout.bob
  alice_ne_bob := OutputLayoutProbes.layout.alice_ne_bob
  disposition _ := OutputLayoutProbes.layout.disposition e₀
  AliceResidual _ := OutputLayoutProbes.layout.AliceResidual e₀
  BobResidual _ := OutputLayoutProbes.layout.BobResidual e₀
  finAliceResidual _ := inferInstance
  decAliceResidual _ := inferInstance
  nonemptyAliceResidual _ := inferInstance
  finBobResidual _ := inferInstance
  decBobResidual _ := inferInstance
  nonemptyBobResidual _ := inferInstance
  aliceSplit _ := OutputLayoutProbes.layout.aliceSplit e₀
  bobSplit _ := OutputLayoutProbes.layout.bobSplit e₀

/-- A genuine three-party typed program terminating at the selected leaf. -/
def leafProtocol (e₀ : OutputLayoutProbes.boundary.Exit) : Protocol Party where
  start := OutputLayoutProbes.boundary.system e₀
  boundary := .leaf (OutputLayoutProbes.boundary.system e₀)
  program := .done
  layout := leafLayout e₀

def abortProtocol : Protocol Party := leafProtocol abortExit

/-- The terminal fixtures declare their single complete public exit. -/
instance leafProtocolExitNonempty (e₀ : OutputLayoutProbes.boundary.Exit) :
    Nonempty (leafProtocol e₀).boundary.Exit := ⟨()⟩

instance : Nonempty abortProtocol.boundary.Exit := leafProtocolExitNonempty abortExit
def acceptZeroProtocol : Protocol Party := leafProtocol acceptZeroExit
def acceptOneProtocol : Protocol Party := leafProtocol acceptOneExit

/-! The three terminal protocols retain distinct dispositions. -/

theorem abort_protocol_disposition :
    abortProtocol.layout.disposition () = .abort := rfl
theorem accept_zero_protocol_disposition :
    acceptZeroProtocol.layout.disposition () = .accept 0 := rfl
theorem accept_one_protocol_disposition :
    acceptOneProtocol.layout.disposition () = .accept 1 := rfl

theorem abort_protocol_acceptedKeyClassical : abortProtocol.AcceptedKeyClassical := by
  intro rho e ℓ haccept alice bob alice' bob' u v hmismatch
  cases e
  simp [abortProtocol, leafProtocol, leafLayout, OutputLayoutProbes.layout, abortExit] at haccept

theorem accept_zero_protocol_acceptedKeyClassical :
    acceptZeroProtocol.AcceptedKeyClassical := by
  intro rho e ℓ haccept alice bob alice' bob' u v hmismatch
  cases e
  have hdisp : (.accept 0 : BoundaryKeyLayout.Disposition) = .accept ℓ := by
    simpa [acceptZeroProtocol, leafProtocol, leafLayout, OutputLayoutProbes.layout,
      acceptZeroExit] using haccept
  have hℓ : 0 = ℓ := BoundaryKeyLayout.Disposition.accept.inj hdisp
  subst ℓ
  exact (hmismatch
    ⟨(Fin.eq_zero alice).trans (Fin.eq_zero alice').symm,
      (Fin.eq_zero bob).trans (Fin.eq_zero bob').symm⟩).elim

/-- `Program.done` preserves an off-diagonal mismatched-key matrix unit; this rules out a
constructor that manufactures classicality for a no-communication program. -/
def testResidual : acceptOneProtocol.layout.Residual () :=
  (acceptOneProtocol.layout.coordinates () (acceptOneJoint 0 0 0 0 0)).2.2
def rowZero : acceptOneProtocol.start.total :=
  (acceptOneProtocol.layout.toBoundaryKeyLayout.acceptCoordinates rfl).symm (0, 0, testResidual)
def rowOne : acceptOneProtocol.start.total :=
  (acceptOneProtocol.layout.toBoundaryKeyLayout.acceptCoordinates rfl).symm (1, 0, testResidual)
def offDiagonal : Op acceptOneProtocol.start.total := Matrix.single rowZero rowOne 1

theorem done_real_offDiagonal_entry :
    acceptOneProtocol.real offDiagonal ⟨(), rowZero⟩ ⟨(), rowOne⟩ = 1 := by
  change (Program.done : Program acceptOneProtocol.start acceptOneProtocol.boundary).denote
      offDiagonal ⟨(), rowZero⟩ ⟨(), rowOne⟩ = 1
  rw [Program.denote_done]
  change Matrix.single rowZero rowOne (1 : ℂ) rowZero rowOne = 1
  exact Matrix.single_apply_same rowZero rowOne (1 : ℂ)

theorem done_not_acceptedKeyClassical : ¬ acceptOneProtocol.AcceptedKeyClassical := by
  intro hclassical
  have hzero := hclassical offDiagonal () 1 rfl 0 0 1 0 testResidual testResidual (by decide)
  have hone : acceptOneProtocol.real offDiagonal
      ⟨(), (acceptOneProtocol.layout.toBoundaryKeyLayout.acceptCoordinates rfl).symm
        (0, 0, testResidual)⟩
      ⟨(), (acceptOneProtocol.layout.toBoundaryKeyLayout.acceptCoordinates rfl).symm
        (1, 0, testResidual)⟩ = 1 := by
    simpa only [rowZero, rowOne] using done_real_offDiagonal_entry
  rw [hone] at hzero
  exact one_ne_zero hzero

theorem acceptedKeyClassical_specialize {A : Protocol Party} (h : A.AcceptedKeyClassical)
    (rho : Op A.start.total) (e : A.boundary.Exit) (ℓ : ℕ)
    (haccept : A.layout.disposition e = .accept ℓ)
    (alice bob alice' bob' : Fin (2 ^ ℓ)) (u v : A.layout.Residual e)
    (hmismatch : ¬ (alice = alice' ∧ bob = bob')) :
    A.real rho
        ⟨e, (A.layout.toBoundaryKeyLayout.acceptCoordinates haccept).symm (alice, bob, u)⟩
        ⟨e, (A.layout.toBoundaryKeyLayout.acceptCoordinates haccept).symm
          (alice', bob', v)⟩ = 0 :=
  h rho e ℓ haccept alice bob alice' bob' u v hmismatch

theorem direct_real_isCPTP {A : Protocol Party} (C : A.NumeralCoordinates) :
    Quantum.Channels.IsCPTP ⇑C.real :=
  A.program.coordinateDenote_isCPTP C.inputEquiv C.outputEquiv
theorem direct_resource_isCPTP {A : Protocol Party} (C : A.NumeralCoordinates) :
    Quantum.Channels.IsCPTP ⇑C.resource :=
  A.layout.toBoundaryKeyLayout.coordinateIdeal_isCPTP C.outputEquiv
theorem direct_ideal_isCPTP {A : Protocol Party} (C : A.NumeralCoordinates) :
    Quantum.Channels.IsCPTP ⇑C.ideal := by
  rw [C.ideal_eq_resource_comp_real]
  simpa [Function.comp_def] using Quantum.Channels.cptp_comp (⇑C.resource) (⇑C.real)
    (direct_resource_isCPTP C) (direct_real_isCPTP C)

/-- Two numberings of the protocol's difference map are conjugate by basis renumberings.  This is
the generic coordinate fact `TypedLOCC.Numbering.map_conj_eq`, read at the protocol's own
difference map. -/
private theorem direct_change_coordinates {A : Protocol Party} (C D : A.NumeralCoordinates) :
    D.difference = (((Matrix.reindexLinearEquiv ℂ ℂ
          (C.outputEquiv.symm.trans D.outputEquiv)
          (C.outputEquiv.symm.trans D.outputEquiv)).toLinearMap.comp C.difference).comp
        (Matrix.reindexLinearEquiv ℂ ℂ (D.inputEquiv.symm.trans C.inputEquiv)
          (D.inputEquiv.symm.trans C.inputEquiv)).toLinearMap) :=
  TypedLOCC.Numbering.map_conj_eq C D A.difference

theorem direct_diamondNorm_coordinate_choice {A : Protocol Party} (C D : A.NumeralCoordinates) :
    Quantum.Channels.diamondNorm D.difference = Quantum.Channels.diamondNorm C.difference := by
  rw [direct_change_coordinates C D]
  exact Quantum.Channels.diamondNorm_reindex_conj_eq
    (D.inputEquiv.symm.trans C.inputEquiv) (C.outputEquiv.symm.trans D.outputEquiv) C.difference

/-! ## The coordinate-free interface

The re-derivation above is the reason `Protocol.realIdealDistance` may be defined without a
coordinate argument.  The probes below check that the public interface really is coordinate-free
and that it computes the expected value on a fixture whose real and ideal maps coincide. -/

/-- Any explicit numeral package of a protocol computes its coordinate-free distance. -/
theorem direct_realIdealDistance_eq_any_coordinates {A : Protocol Party}
    (C : A.NumeralCoordinates) :
    A.realIdealDistance = (1 / 2) * Quantum.Channels.diamondNorm C.difference :=
  A.realIdealDistance_eq_coordinates C

/-! Opaque protocols require neither an exit witness nor a numbering to state security. -/

section OpaqueProtocol

variable {P : Type} [Fintype P] [DecidableEq P] (A : Protocol P)

example : Nonempty A.boundary.Exit := A.nonempty_exit

example : 0 ≤ A.realIdealDistance := A.realIdealDistance_nonneg

example (epsilon : ℝ) (h : A.IsFullInterfaceSecure epsilon) :
    A.AcceptedKeyClassical ∧ A.realIdealDistance ≤ epsilon :=
  ⟨h.acceptedKeyClassical, h.realIdealDistance_le⟩

example :
    letI : Nonempty A.boundary.Exit := A.nonempty_exit
    A.realIdealDistance = (1 / 2) * TypedLOCC.diamondNorm A.difference :=
  A.realIdealDistance_eq_half_diamondNorm_difference

/-- The derived witness leaves the old distance expression unchanged for every supplied witness. -/
theorem realIdealDistance_eq_with_witness [Nonempty A.boundary.Exit] :
    A.realIdealDistance = TypedLOCC.diamondDist A.real A.ideal := rfl

end OpaqueProtocol

/-- The aborting fixture's ideal map is its real map: on its single aborting exit the ambient
key-replacement resource preserves every entry, and there is no second exit to decohere. -/
theorem abort_protocol_ideal_eq_real : abortProtocol.ideal = abortProtocol.real := by
  apply LinearMap.ext
  intro rho
  ext i j
  obtain ⟨e, a⟩ := i
  obtain ⟨f, b⟩ := j
  cases e
  cases f
  have hdisposition :
      abortProtocol.layout.toBoundaryKeyLayout.disposition () =
        BoundaryKeyLayout.Disposition.abort := abort_protocol_disposition
  exact abortProtocol.layout.toBoundaryKeyLayout.ideal_coordinate_abort
    (abortProtocol.real rho) () hdisposition a b

/-- **An always-aborting protocol is at diamond distance zero from its ideal resource.**

A client of the canonical interface writes this without choosing any numbering of the registers. -/
theorem abort_protocol_realIdealDistance_eq_zero :
    abortProtocol.realIdealDistance = 0 := by
  have hdist : abortProtocol.realIdealDistance =
      TypedLOCC.diamondDist abortProtocol.real abortProtocol.ideal := rfl
  rw [hdist, abort_protocol_ideal_eq_real, TypedLOCC.diamondDist_self]

/-- Hence it is fully interface-secure at budget `0`: its accepted-key classicality is vacuous and
its real map is its own ideal. -/
theorem abort_protocol_isFullInterfaceSecure_zero :
    abortProtocol.IsFullInterfaceSecure 0 :=
  ⟨abort_protocol_acceptedKeyClassical, le_of_eq abort_protocol_realIdealDistance_eq_zero⟩

/-! Each forbidden caller-supplied field must be rejected during elaboration. -/

example : True := by
  fail_if_success
    let _bad : Protocol Party := { acceptOneProtocol with real := acceptOneProtocol.real }
  trivial
example : True := by
  fail_if_success
    let _bad : Protocol Party := { acceptOneProtocol with ideal := acceptOneProtocol.ideal }
  trivial
example : True := by
  fail_if_success
    let _bad : Protocol Party :=
    { acceptOneProtocol with IsFullInterfaceSecure := fun _ _ => True }
  trivial
example : True := by
  fail_if_success
    let _bad : Protocol Party :=
    { acceptOneProtocol with realIdealDistance := (0 : ℝ) }
  trivial

end QCryptLeanTest.ProtocolProbes
