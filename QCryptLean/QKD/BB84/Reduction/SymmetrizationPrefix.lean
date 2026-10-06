import QCryptLean.QKD.BB84.SiftOperation
import QCryptLean.QKD.BB84.FinalStage
import QCryptLean.LOCC.Typed.Instrument.UniformChoice
import QCryptLean.LOCC.Typed.LocalAction.ComputationalMeasurement

/-!
# The symmetrization prefix of the BB84 analysis

This module belongs to the security analysis, not to the measure-first protocol: none of its stages
occurs in `QKD.BB84.program`.  It constructs the permutation-first prefix of the analytical
experiment on the raw multipartite system `FinalStage.rawSystem n`.  Alice samples a uniform
permutation, applies the corresponding sift/permutation operator and announces the permutation
(`alicePermutationAnnouncement`); Bob applies the operator selected by that public value, with the
literal public `Unit` cell of the source construction (`bobSiftUnitAnnouncement`).
`permutationStage` runs both before a continuation indexed by the same permutation, and
`privateMeasurements` measures Alice's and then Bob's raw register in the computational basis before
a continuation, without announcing either outcome.  The retained analysis composes them as
`QKD.BB84.Reduction.retainedAnalysisPrefix`.

The communicated permutation is the public symmetrization of Christandl--König--Renner,
arXiv:0809.3019, lines 447--455.  The local instrument stages follow the finite-round LOCC
construction of Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section II.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Reduction

open TypedLOCC QKD.BB84
open TypedLOCC.TwoParty
open QKD.BB84.Engine

/-! ## Communicated uniform permutation -/

/-- The one-outcome typed instrument for one party's BB84 sift/permutation operator.

The matrix is the explicit `QKD.BB84.Model.siftPermHalf` operator. Its completeness proof is the
already-proved unitary law for that operator. The random choice is introduced separately below,
so this definition contains no shared-randomness input and no sampling scalar. -/
def siftPermutationInstrument
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    Instrument (Fin (2 ^ n)) (Fin (2 ^ n)) Unit :=
  Instrument.ofFine (fun _ => QKD.BB84.Model.siftPermHalf n peSel xSel π) (by
    simpa only [Fintype.sum_unique] using
      QKD.BB84.Model.siftPermHalf_unitary n peSel xSel π)

/-- Alice's uniform permutation instrument.

The observed physical outcome is `(π, ())`. The only randomness is the explicit finite-uniform
choice made by `Instrument.uniformChoice`; at a fixed `π` its operation has weight
`1 / Fintype.card (Equiv.Perm (Fin n))`. -/
noncomputable def alicePermutationInstrument
    (n : ℕ) (peSel xSel : Fin n → Bool) :
    Instrument (Fin (2 ^ n)) (Fin (2 ^ n)) (Equiv.Perm (Fin n) × Unit) :=
  Instrument.uniformChoice
    (fun π : Equiv.Perm (Fin n) => siftPermutationInstrument n peSel xSel π)

/-- Alice applies her sampled sift/permutation operator and publicly announces exactly the sampled
permutation. The hidden Kraus fibre is still `Unit`; the continuation receives `π`, not an
independently supplied shared seed. -/
noncomputable def alicePermutationAnnouncement
    (n : ℕ) (peSel xSel : Fin n → Bool) :
    AnnouncedAction (FinalStage.rawSystem n)
      (Equiv.Perm (Fin n)) :=
  AnnouncedAction.ofInstrument .alice
    (alicePermutationInstrument n peSel xSel) Prod.fst

/-- Bob applies the sift/permutation operator selected by Alice's public permutation. Its sole
physical outcome stays private at this layer. -/
def bobSiftPermutationPrivate
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    PrivateAction ((alicePermutationAnnouncement n peSel xSel).out π) :=
  PrivateAction.ofInstrument .bob
    (siftPermutationInstrument n peSel xSel π)

/-- Bob's sift/permutation action with the model's literal public `Unit` cell.

`PrivateAction.asUnitAnnouncement` changes neither the actor nor the local Kraus family. It records
one singleton public node, so the typed public word retains the source constructor chronology. -/
def bobSiftUnitAnnouncement
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    AnnouncedAction ((alicePermutationAnnouncement n peSel xSel).out π) Unit :=
  (bobSiftPermutationPrivate n peSel xSel π).asUnitAnnouncement

/-- The permutation stage over an arbitrary typed continuation.

The public boundary contains Alice's permutation cell followed by Bob's literal `Unit` cell.
The continuation is indexed by the same `π` that Alice announced and Bob used. -/
def permutationStage
    (n : ℕ) (peSel xSel : Fin n → Bool)
    {B : Equiv.Perm (Fin n) → Boundary Party}
    (k : ∀ π, Program (FinalStage.rawSystem n) (B π)) :
    Program (FinalStage.rawSystem n)
      (.announce (Equiv.Perm (Fin n)) fun π => .announce Unit fun _ => B π) :=
  (alicePermutationAnnouncement n peSel xSel).then fun π =>
    (bobSiftUnitAnnouncement n peSel xSel π).then fun _ =>
      cast (by
        simp only [bobSiftUnitAnnouncement, PrivateAction.asUnitAnnouncement_out,
          bobSiftPermutationPrivate, alicePermutationAnnouncement,
          PrivateAction.out_ofInstrument, AnnouncedAction.out_ofInstrument,
          FinalStage.rawSystem, TwoParty.set_alice, TwoParty.set_bob]) (k π)

/-- Alice's action exposes exactly the sampled permutation to public control flow. -/
@[simp] theorem alicePermutationAnnouncement_announce
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    (alicePermutationAnnouncement n peSel xSel).announce (π, ()) = π := by
  rfl

/-- Exact joint-register operation of Alice's uniformly sampled permutation branch.

The formula holds for every operator and independent output row and column coordinates. The local
lift tensors Alice's matrix with the spectator identity; no equality between Bob's row and column
coordinates is assumed. -/
theorem alicePermutationAnnouncement_liftedOperation_apply
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (rho : Op (FinalStage.rawSystem n).total)
    (q q' : ((alicePermutationAnnouncement n peSel xSel).out π).total) :
    ((alicePermutationAnnouncement n peSel xSel).liftedOperation (π, ()) rho) q q' =
      (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
        (matrixConjLinear
          (localKrausLift (FinalStage.rawSystem n) .alice (Fin (2 ^ n))
            (QKD.BB84.Model.siftPermHalf n peSel xSel π)) rho) q q' := by
  change ((alicePermutationInstrument n peSel xSel).liftAt
    (FinalStage.rawSystem n) .alice).operation (π, ()) rho q q' = _
  rw [Instrument.liftAt_operation_apply]
  unfold alicePermutationInstrument
  refine (congrFun (congrFun (LinearMap.congr_fun
    (Instrument.uniformChoice_operation (fun π => siftPermutationInstrument n peSel xSel π)
      π ()) _) _) _).trans ?_
  simp only [LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul]
  apply congrArg (fun z : ℂ => (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ * z)
  calc
    _ = ((siftPermutationInstrument n peSel xSel π).liftAt
        (FinalStage.rawSystem n) .alice).operation () rho q q' :=
      (Instrument.liftAt_operation_apply .alice
        (siftPermutationInstrument n peSel xSel π) () rho q q').symm
    _ = _ := by
      simp [siftPermutationInstrument, Instrument.operation, Instrument.liftAt,
        Instrument.ofFine]

/-- Bob's action contributes exactly the unique public value. -/
@[simp] theorem bobSiftUnitAnnouncement_announce
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    (bobSiftUnitAnnouncement n peSel xSel π).announce () = () := by
  rfl

/-- Exact joint-register operation of Bob's sift/permutation branch.

The formula holds for every operator and independent output row and column coordinates. Bob's
local lift acts as the identity on Alice's two independent spectator coordinates. -/
theorem bobSiftUnitAnnouncement_liftedOperation_apply
    (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (rho : Op ((alicePermutationAnnouncement n peSel xSel).out π).total)
    (q q' : ((bobSiftUnitAnnouncement n peSel xSel π).out ()).total) :
    ((bobSiftUnitAnnouncement n peSel xSel π).liftedOperation () rho) q q' =
      (matrixConjLinear
        (localKrausLift ((alicePermutationAnnouncement n peSel xSel).out π) .bob (Fin (2 ^ n))
          (QKD.BB84.Model.siftPermHalf n peSel xSel π)) rho) q q' := by
  change ((siftPermutationInstrument n peSel xSel π).liftAt
    ((alicePermutationAnnouncement n peSel xSel).out π) .bob).operation () rho q q' = _
  simp [siftPermutationInstrument, Instrument.operation, Instrument.liftAt,
    Instrument.ofFine]

/-! ## Private raw-register measurements -/

/-- Alice privately measures her `2 ^ n`-dimensional raw register in the computational basis. -/
def alicePrivateMeasurement (n : ℕ) :
    PrivateAction (FinalStage.rawSystem n) :=
  PrivateAction.computationalMeasurement (FinalStage.rawSystem n) .alice

/-- Bob privately measures his `2 ^ n`-dimensional raw register in the computational basis. -/
def bobPrivateMeasurement (n : ℕ) :
    PrivateAction (alicePrivateMeasurement n).out :=
  PrivateAction.computationalMeasurement (alicePrivateMeasurement n).out .bob

/-- Run Alice's and then Bob's private computational measurements before an arbitrary typed
continuation. Neither physical measurement outcome becomes a public cell. -/
def privateMeasurements {B : Boundary Party} (n : ℕ)
    (k : Program (FinalStage.rawSystem n) B) :
    Program (FinalStage.rawSystem n) B :=
  (alicePrivateMeasurement n).then ((bobPrivateMeasurement n).then
    (cast (by
      simp only [bobPrivateMeasurement, alicePrivateMeasurement,
        PrivateAction.computationalMeasurement_out]) k))

end QKD.BB84.Reduction
