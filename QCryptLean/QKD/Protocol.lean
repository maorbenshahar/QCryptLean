import QCryptLean.QKD.OutputLayout
import QCryptLean.LOCC.Typed.Program.Denotation
import QCryptLean.LOCC.Typed.ChannelCoordinates.Numbering
import QCryptLean.Quantum.Channels.CPTP.DiamondNormReindex

/-!
# QKD protocols with locally owned output keys

A protocol consists only of a typed LOCC program and a local-register description of its
heterogeneous output.  Its real channel, ambient key-replacement resource, ideal channel,
real--ideal difference, and the normalized diamond distance between the first and the third are
derived from those data.  Security — `IsFullInterfaceSecure` — is a statement about the protocol
and a budget; explicit numeral coordinates (`NumeralCoordinates`, the shared `TypedLOCC.Numbering`
record at this protocol's two registers) remain available as a low-level transport tool for
low-level channel estimates, and `realIdealDistance_eq_coordinates` says that any such package
computes the same distance.

Christandl--König--Renner, arXiv:0809.3019, lines 423--448, compare the full real and ideal QKD
outputs containing both keys and the public transcript.  Nahar--Tupkary--Zhao--Lütkenhaus--Tan,
arXiv:2403.11851, lines 394--400, distinguish the two key registers before passing to an
Alice-key marginal.  The criterion here retains both key registers and uses the normalized diamond
norm on the full output interface.
-/

open Quantum.Operators

noncomputable section

namespace QKD
open TypedLOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- A typed LOCC program together with a locally owned decomposition of every final key register.

The program supplies the physical real map, while `layout` identifies Alice's and Bob's key
factors within their own output registers.  Neither a channel nor a security assertion is
caller-supplied. -/
structure Protocol (P : Type) [Fintype P] [DecidableEq P] where
  /-- Initial laboratory registers. -/
  start : MultipartiteSystem P
  /-- Branch-dependent final laboratory registers and complete public exits. -/
  boundary : Boundary P
  /-- The finite typed LOCC program from `start` to `boundary`. -/
  program : Program start boundary
  /-- Local ownership witnesses for Alice's and Bob's final key factors. -/
  layout : OutputLayout boundary

namespace Protocol

variable (A : Protocol P)

/-- The complete protocol program supplies a complete public exit. -/
theorem nonempty_exit (A : Protocol P) : Nonempty A.boundary.Exit :=
  A.program.nonempty_exit

/-- The real protocol map is the denotation of the typed LOCC program. -/
def real : Op A.start.total →ₗ[ℂ] Op A.boundary.space :=
  A.program.denote

/-- The ambient full-exit-pinching resource replaces accepted keys and preserves residual data.

This is a postprocessor on the whole output boundary.  It is distinct from the ideal protocol
map, which first runs the real protocol. -/
def resource : Op A.boundary.space →ₗ[ℂ] Op A.boundary.space :=
  A.layout.toBoundaryKeyLayout.ideal

/-- The ideal protocol map is the boundary resource after the real protocol. -/
def ideal : Op A.start.total →ₗ[ℂ] Op A.boundary.space :=
  A.resource.comp A.real

/-- The real-minus-ideal map on the complete typed output interface. -/
def difference : Op A.start.total →ₗ[ℂ] Op A.boundary.space :=
  A.real - A.ideal

/-- The real-minus-ideal map is the difference of the two derived maps, by definition. -/
theorem difference_eq_real_sub_ideal (A : Protocol P) : A.difference = A.real - A.ideal := rfl

/-- **The normalized diamond distance between the protocol's real map and its ideal map.**

Both maps are derived from the program and the output layout, so this real number belongs to the
protocol alone: no coordinate package, reference system, ideal channel or security premise is
supplied by a caller.  The diamond norm quantifies over arbitrary references.

The complete program supplies a public exit by `nonempty_exit`; no exit witness is requested
from the caller. Every explicit numbering computes the same value
(`realIdealDistance_eq_coordinates`). -/
noncomputable def realIdealDistance (A : Protocol P) : ℝ :=
  letI : Nonempty A.boundary.Exit := A.nonempty_exit
  TypedLOCC.diamondDist A.real A.ideal

/-- The real/ideal distance is half the diamond norm of the real-minus-ideal map. -/
theorem realIdealDistance_eq_half_diamondNorm_difference
    (A : Protocol P) :
    letI : Nonempty A.boundary.Exit := A.nonempty_exit
    A.realIdealDistance = (1 / 2) * TypedLOCC.diamondNorm A.difference := rfl

/-- The real/ideal distance is nonnegative. -/
theorem realIdealDistance_nonneg (A : Protocol P) : 0 ≤ A.realIdealDistance := by
  letI : Nonempty A.boundary.Exit := A.nonempty_exit
  exact TypedLOCC.diamondDist_nonneg _ _

/-- Every real output has zero coherences between distinct complete public exits.

This is the classical-public-output property of the full QKD maps in
Christandl--König--Renner, arXiv:0809.3019, lines 423--448, derived here from the typed program. -/
theorem real_isExitBlockDiagonal (rho : Op A.start.total) :
    Boundary.IsExitBlockDiagonal A.boundary (A.real rho) := by
  exact A.program.denote_isExitBlockDiagonal rho

/-- Explicit positive numeral coordinates for a protocol's input and complete output spaces.

This is `TypedLOCC.Numbering` at those two registers.  The equivalences expose the typed channels
to finite-dimensional channel APIs; they do not supply a key factorization or alter the protocol.
The generic transport, composition, subtraction and norm-invariance laws are `Numbering.map`,
`Numbering.post`, `Numbering.map_comp`, `Numbering.map_sub` and `Numbering.diamondNorm_map`; only
the four maps below are specific to a QKD protocol.

The output register is the heterogeneous boundary space, in which aborting exits carry no
key factor. -/
abbrev NumeralCoordinates (A : Protocol P) : Type :=
  Numbering A.start.total A.boundary.space

namespace NumeralCoordinates

variable {A : Protocol P}

/-- The real protocol map in explicit numeral coordinates. -/
def real (C : NumeralCoordinates A) :
    Quantum.Operators.Op C.inputDim →ₗ[ℂ] Quantum.Operators.Op C.outputDim :=
  C.map A.real

/-- The ambient boundary resource in explicit output coordinates. -/
def resource (C : NumeralCoordinates A) :
    Quantum.Operators.Op C.outputDim →ₗ[ℂ] Quantum.Operators.Op C.outputDim :=
  C.post A.resource

/-- The ideal protocol map in explicit numeral coordinates. -/
def ideal (C : NumeralCoordinates A) :
    Quantum.Operators.Op C.inputDim →ₗ[ℂ] Quantum.Operators.Op C.outputDim :=
  C.map A.ideal

/-- The real-minus-ideal map in explicit numeral coordinates. -/
def difference (C : NumeralCoordinates A) :
    Quantum.Operators.Op C.inputDim →ₗ[ℂ] Quantum.Operators.Op C.outputDim :=
  C.map A.difference

/-- Coordinate transport preserves the definition of the ideal protocol as resource after real. -/
theorem ideal_eq_resource_comp_real (C : NumeralCoordinates A) :
    C.ideal = C.resource.comp C.real :=
  C.map_comp A.real A.resource

/-- Coordinate transport preserves the real-minus-ideal difference. -/
theorem difference_eq_real_sub_ideal (C : NumeralCoordinates A) :
    C.difference = C.real - C.ideal := by
  rfl

/-- A typed LOCC program denotes a CPTP real channel in every numeral coordinate choice. -/
theorem real_isCPTP (C : NumeralCoordinates A) :
    Quantum.Channels.IsCPTP ⇑C.real := by
  exact A.program.coordinateDenote_isCPTP C.inputEquiv C.outputEquiv

/-- The boundary-derived key-replacement resource is CPTP in every numeral coordinate choice. -/
theorem resource_isCPTP (C : NumeralCoordinates A) :
    Quantum.Channels.IsCPTP ⇑C.resource := by
  exact A.layout.toBoundaryKeyLayout.coordinateIdeal_isCPTP C.outputEquiv

/-- The derived ideal protocol map is CPTP in every numeral coordinate choice. -/
theorem ideal_isCPTP (C : NumeralCoordinates A) :
    Quantum.Channels.IsCPTP ⇑C.ideal := by
  simpa [ideal_eq_resource_comp_real C, Function.comp_def] using
    Quantum.Channels.cptp_comp (⇑C.resource) (⇑C.real)
      (resource_isCPTP C) (real_isCPTP C)

end NumeralCoordinates

/-- A protocol with an explicit numeral coordinate package declares a complete public exit.

The output numbering is a bijection onto `Fin C.outputDim` with `C.outputDim ≠ 0`, so the output
space, hence the exit type, is inhabited (`Numbering.nonempty_target`). -/
theorem nonempty_exit_of_coordinates (A : Protocol P) (C : NumeralCoordinates A) :
    Nonempty A.boundary.Exit :=
  C.nonempty_target.elim fun p => ⟨p.1⟩

/-- **Every explicit numeral coordinate package computes the protocol's real/ideal distance.**

This is the exact relationship between the coordinate-free interface and the low-level transport
coordinates: a half-diamond-norm estimate for C.difference is an estimate for the protocol. -/
theorem realIdealDistance_eq_coordinates (A : Protocol P)
    (C : NumeralCoordinates A) :
    A.realIdealDistance = (1 / 2) * Quantum.Channels.diamondNorm C.difference := by
  letI : Nonempty A.boundary.Exit := A.nonempty_exit
  exact congrArg ((1 / 2 : ℝ) * ·) (C.diamondNorm_map A.difference).symm

/-- The diamond norm of the real-minus-ideal map is independent of numeral coordinates: two
numberings of one typed map are conjugate by basis renumberings
(`Numbering.diamondNorm_map_eq`), with no nonemptiness side condition. -/
theorem diamondNorm_differenceInCoordinates_eq
    (A : Protocol P) (C D : NumeralCoordinates A) :
    Quantum.Channels.diamondNorm D.difference =
      Quantum.Channels.diamondNorm C.difference :=
  Numbering.diamondNorm_map_eq C D A.difference

/-- On every accepting exit, both locally owned key registers are classical for every input.

Entries may retain arbitrary coherence in the residual coordinates.  This is the two-key output
condition preceding the Alice-key marginal criterion in
Nahar--Tupkary--Zhao--Lütkenhaus--Tan, arXiv:2403.11851, lines 394--400. -/
def AcceptedKeyClassical (A : Protocol P) : Prop :=
  ∀ (rho : Op A.start.total) (e : A.boundary.Exit) (ℓ : ℕ)
    (haccept : A.layout.disposition e = .accept ℓ)
    (alice bob alice' bob' : Fin (2 ^ ℓ))
    (u v : A.layout.Residual e),
    ¬ (alice = alice' ∧ bob = bob') →
      A.real rho
          ⟨e, (A.layout.toBoundaryKeyLayout.acceptCoordinates haccept).symm
            (alice, bob, u)⟩
          ⟨e, (A.layout.toBoundaryKeyLayout.acceptCoordinates haccept).symm
            (alice', bob', v)⟩ = 0

/-- Full-interface QKD security: accepted local keys are classical and the normalized diamond
distance from the derived ideal protocol is at most `epsilon`.

The subject is the protocol and the budget alone.  Both maps being compared are derived from the
program and the output layout, and the distance is the coordinate-free `realIdealDistance`, so no
caller supplies a channel, an ideal map or a numbering of the registers.

This retains both keys and all public and residual outputs as in the full maps of
Christandl--König--Renner, arXiv:0809.3019, lines 423--448.  It is not Nahar et al.'s Alice-key
marginal, half-trace-distance criterion (arXiv:2403.11851, lines 394--400). -/
def IsFullInterfaceSecure (A : Protocol P) (epsilon : ℝ) : Prop :=
  A.AcceptedKeyClassical ∧ A.realIdealDistance ≤ epsilon

/-- Full-interface security includes the accepted-key classicality claim. -/
theorem IsFullInterfaceSecure.acceptedKeyClassical {A : Protocol P}
    {epsilon : ℝ} (h : A.IsFullInterfaceSecure epsilon) : A.AcceptedKeyClassical := h.1

/-- Full-interface security includes the normalized real/ideal diamond bound. -/
theorem IsFullInterfaceSecure.realIdealDistance_le {A : Protocol P}
    {epsilon : ℝ} (h : A.IsFullInterfaceSecure epsilon) : A.realIdealDistance ≤ epsilon := h.2

/-- Increasing the allowed error preserves full-interface security. -/
theorem IsFullInterfaceSecure.mono {A : Protocol P} {ε ε' : ℝ}
    (h : A.IsFullInterfaceSecure ε) (hε : ε ≤ ε') : A.IsFullInterfaceSecure ε' :=
  ⟨h.1, h.2.trans hε⟩

/-- Full-interface security is exactly accepted-key classicality together with the normalized
real/ideal diamond bound. -/
theorem isFullInterfaceSecure_iff (A : Protocol P) (epsilon : ℝ) :
    A.IsFullInterfaceSecure epsilon ↔
      A.AcceptedKeyClassical ∧ A.realIdealDistance ≤ epsilon := Iff.rfl

end Protocol

end QKD
