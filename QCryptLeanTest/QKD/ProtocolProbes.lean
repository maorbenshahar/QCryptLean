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

open _root_.LOCC

open QKD
open OutputLayoutProbes

/-- Read a terminal ownership value from one heterogeneous test exit. -/
def leafEnd (e₀ : OutputLayoutProbes.boundary.Exit) :
    KeyEnd OutputLayoutProbes.layout.alice OutputLayoutProbes.layout.bob
      (OutputLayoutProbes.boundary.system e₀) where
  disposition := OutputLayoutProbes.layout.disposition e₀
  AliceResidual := OutputLayoutProbes.layout.AliceResidual e₀
  BobResidual := OutputLayoutProbes.layout.BobResidual e₀
  aliceSplit := OutputLayoutProbes.layout.aliceSplit e₀
  bobSplit := OutputLayoutProbes.layout.bobSplit e₀

/-- A three-party program terminates with ownership at the selected leaf. -/
def leafProtocol (e₀ : OutputLayoutProbes.boundary.Exit) : Protocol Party :=
  (Program.done (leafEnd e₀)).toProtocol OutputLayoutProbes.layout.alice_ne_bob

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
  change (.abort : BoundaryKeyLayout.Disposition) = .accept ℓ at haccept
  cases haccept

theorem accept_zero_protocol_acceptedKeyClassical :
    acceptZeroProtocol.AcceptedKeyClassical := by
  intro rho e ℓ haccept alice bob alice' bob' u v hmismatch
  cases e
  have hdisp : (.accept 0 : BoundaryKeyLayout.Disposition) = .accept ℓ := by
    exact haccept
  have hℓ : 0 = ℓ := BoundaryKeyLayout.Disposition.accept.inj hdisp
  subst ℓ
  exact (hmismatch
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩).elim

/-- `Program.done` preserves an off-diagonal mismatched-key matrix unit; this rules out a
constructor that manufactures classicality for a no-communication program. -/
def testResidual : acceptOneProtocol.layout.Residual () :=
  (acceptOneProtocol.layout.coordinates () (acceptOneJoint 0 0 0 0 0)).2.2
def rowZero : acceptOneProtocol.start.total :=
  (acceptOneProtocol.layout.toBoundaryKeyLayout.acceptCoordinates rfl).symm (0, 0, testResidual)
def rowOne : acceptOneProtocol.start.total :=
  (acceptOneProtocol.layout.toBoundaryKeyLayout.acceptCoordinates rfl).symm (1, 0, testResidual)
def offDiagonal : Quantum.Operators.Op acceptOneProtocol.start.total := Matrix.single
  rowZero rowOne 1

theorem done_real_offDiagonal_entry :
    acceptOneProtocol.real offDiagonal ⟨(), rowZero⟩ ⟨(), rowOne⟩ = 1 := by
  change (Program.done (leafEnd acceptOneExit)).denote
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
    (rho : Quantum.Operators.Op A.start.total) (e : A.boundary.Exit) (ℓ : ℕ)
    (haccept : A.layout.disposition e = .accept ℓ)
    (alice bob alice' bob' : (Fin ℓ → Fin 2)) (u v : A.layout.Residual e)
    (hmismatch : ¬ (alice = alice' ∧ bob = bob')) :
    A.real rho
        ⟨e, (A.layout.toBoundaryKeyLayout.acceptCoordinates haccept).symm (alice, bob, u)⟩
        ⟨e, (A.layout.toBoundaryKeyLayout.acceptCoordinates haccept).symm
          (alice', bob', v)⟩ = 0 :=
  h rho e ℓ haccept alice bob alice' bob' u v hmismatch

theorem direct_real_isChannel (A : Protocol Party) :
    Quantum.Channels.IsChannel A.real := A.isChannel_real

theorem direct_resource_isChannel (A : Protocol Party) :
    Quantum.Channels.IsChannel A.resource := A.isChannel_resource

theorem direct_ideal_isChannel (A : Protocol Party) :
    Quantum.Channels.IsChannel A.ideal := A.isChannel_resource.comp A.isChannel_real

/-! Opaque protocols require neither an exit witness nor a numbering to state security. -/

section OpaqueProtocol

variable {P : Type} [Fintype P] [DecidableEq P] (A : Protocol P)

example [Nonempty A.start.total] : Nonempty A.boundary.Exit := A.nonempty_exit

example : 0 ≤ A.realIdealDistance := A.realIdealDistance_nonneg

example (epsilon : ℝ) (h : A.IsSecure epsilon) :
    A.AcceptedKeyClassical ∧ A.realIdealDistance ≤ epsilon :=
  ⟨h.acceptedKeyClassical, h.realIdealDistance_le⟩

example :
    A.realIdealDistance = (1 / 2) * Quantum.Channels.diamondNorm A.difference :=
  A.realIdealDistance_eq_half_diamondNorm_difference

/-- The derived witness leaves the old distance expression unchanged for every supplied witness. -/
theorem realIdealDistance_eq_with_witness [Nonempty A.boundary.Exit] :
    A.realIdealDistance = Quantum.Channels.diamondDist A.real A.ideal := rfl

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
      Quantum.Channels.diamondDist abortProtocol.real abortProtocol.ideal := rfl
  rw [hdist, abort_protocol_ideal_eq_real, Quantum.Channels.diamondDist_self]

/-- Hence it is fully interface-secure at budget `0`: its accepted-key classicality is vacuous and
its real map is its own ideal. -/
theorem isSecure_abortProtocol_zero :
    abortProtocol.IsSecure 0 :=
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
    { acceptOneProtocol with IsSecure := fun _ _ => True }
  trivial
example : True := by
  fail_if_success
    let _bad : Protocol Party :=
    { acceptOneProtocol with realIdealDistance := (0 : ℝ) }
  trivial

end QCryptLeanTest.ProtocolProbes
