import QCryptLean.QKD.BB84.Measurement.Classicality
import QCryptLean.LOCC.Typed.ChannelCoordinates
import QCryptLean.LOCC.Typed.Instrument.ClassicalTransition
import QCryptLean.LOCC.Typed.Program.TwoPartyClassicalStorage
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction

/-!
# Reference-stable record classicality for the weighted BB84 schedule

This statement transports the proved all-record block diagonality of the finite destructive
measurement schedule through explicit finite coordinates and `Quantum.Channels.mapTensorId`.
The reference indices are proof-side matrix coordinates and are not an additional physical
register of the typed program.

The `K ⊗ 1` interpretation is the finite local-instrument structure described by
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2.  The exact coordinate
block identity used here is existing library infrastructure rather than a theorem attributed to
that paper.  This file makes no sampling, batch-equivalence, or security assertion.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open TypedLOCC

open TypedLOCC.TwoParty

attribute [local instance] storedRecordVectorDecidableEq

/-- The physical input coordinate dimension is nonzero, derived from its explicit inhabited
finite type rather than supplied by a caller. -/
@[implicit_reducible]
def weightedStreamInputCardNeZero (N : ℕ) :
    NeZero (Fintype.card (weightedStreamSystem Unit N).total) :=
  ⟨Fintype.card_ne_zero⟩

/-- The terminal record-coordinate dimension is nonzero, derived from its explicit inhabited
finite type rather than supplied by a caller. -/
@[implicit_reducible]
def weightedScheduleRecordCardNeZero (N : ℕ) :
    NeZero (Fintype.card
      ((Unit × (Fin N → StoredRecord)) ×
        (Unit × (Fin N → StoredRecord)))) :=
  ⟨Fintype.card_ne_zero⟩

attribute [local instance] weightedStreamInputCardNeZero
attribute [local instance] weightedScheduleRecordCardNeZero

/-- The actual destructive schedule produces an honest-register diagonal terminal operator after
exposing its chronological record coordinates.

This holds for every complex input operator, including `N = 0` and arbitrary fixed, biased, pure,
or zero-support basis laws.  It is the source-level record-classicality consequence of the local
finite instruments described structurally in Chitambar et al., arXiv:1210.4583, Section 2. -/
theorem weightedMeasurementSchedule_honestRegistersDiagonal
    (pA pB : PMF Basis) (N : ℕ)
    (rho : TypedLOCC.Op (weightedStreamSystem Unit N).total) :
    let R := weightedStreamSystem (finishAcc Unit N) 0
    R.HonestRegistersDiagonal
      (reindexOp (Boundary.leafSpaceEquiv R)
        ((weightedMeasurementSchedule pA pB N).denote rho)) := by
  dsimp only
  intro q q' hqq'
  let a := finishedStreamEquiv Unit N (q .alice)
  let a' := finishedStreamEquiv Unit N (q' .alice)
  let b := finishedStreamEquiv Unit N (q .bob)
  let b' := finishedStreamEquiv Unit N (q' .bob)
  have hrecords : a.2 ≠ a'.2 ∨ b.2 ≠ b'.2 := by
    rcases hqq' with hAlice | hBob
    · exact Or.inl (by
        intro h
        apply hAlice
        apply (finishedStreamEquiv Unit N).injective
        exact Prod.ext (Subsingleton.elim _ _) h)
    · exact Or.inr (by
        intro h
        apply hBob
        apply (finishedStreamEquiv Unit N).injective
        exact Prod.ext (Subsingleton.elim _ _) h)
  have hdiag := weightedMeasurementSchedule_recordsDiagonal pA pB N rho
    a.1 a'.1 b.1 b'.1 a.2 a'.2 b.2 b'.2 hrecords
  have hrow :
      (weightedScheduleOutputEquiv Unit N).symm ((a.1, a.2), (b.1, b.2)) =
        (Boundary.leafSpaceEquiv
          (weightedStreamSystem (finishAcc Unit N) 0)).symm q := by
    apply (Boundary.leafSpaceEquiv
      (weightedStreamSystem (finishAcc Unit N) 0)).injective
    simp only [a, b, Prod.mk.eta, weightedScheduleOutputEquiv_symm_apply,
      finishedStreamEquiv_symm_apply, Equiv.apply_symm_apply]
    rw [← finishedStreamEquiv_symm_apply Unit N
        (finishedStreamEquiv Unit N (q .alice)),
      ← finishedStreamEquiv_symm_apply Unit N
        (finishedStreamEquiv Unit N (q .bob))]
    simp only [Equiv.symm_apply_apply]
    exact (TwoParty.pairEquiv _ _).symm_apply_apply q
  have hrow' :
      (weightedScheduleOutputEquiv Unit N).symm ((a'.1, a'.2), (b'.1, b'.2)) =
        (Boundary.leafSpaceEquiv
          (weightedStreamSystem (finishAcc Unit N) 0)).symm q' := by
    apply (Boundary.leafSpaceEquiv
      (weightedStreamSystem (finishAcc Unit N) 0)).injective
    simp only [a', b', Prod.mk.eta, weightedScheduleOutputEquiv_symm_apply,
      finishedStreamEquiv_symm_apply, Equiv.apply_symm_apply]
    rw [← finishedStreamEquiv_symm_apply Unit N
        (finishedStreamEquiv Unit N (q' .alice)),
      ← finishedStreamEquiv_symm_apply Unit N
        (finishedStreamEquiv Unit N (q' .bob))]
    simp only [Equiv.symm_apply_apply]
    exact (TwoParty.pairEquiv _ _).symm_apply_apply q'
  change (weightedMeasurementSchedule pA pB N).denote rho
    ((weightedScheduleOutputEquiv Unit N).symm ((a.1, a.2), (b.1, b.2)))
    ((weightedScheduleOutputEquiv Unit N).symm ((a'.1, a'.2), (b'.1, b'.2))) = 0 at hdiag
  change (weightedMeasurementSchedule pA pB N).denote rho
    ((Boundary.leafSpaceEquiv
      (weightedStreamSystem (finishAcc Unit N) 0)).symm q)
    ((Boundary.leafSpaceEquiv
      (weightedStreamSystem (finishAcc Unit N) 0)).symm q') = 0
  simpa [hrow, hrow'] using hdiag

/-- All off-record-diagonal entries remain zero after adjoining an arbitrary finite reference.

The physical schedule has no reference parameter.  `eIn` and `eRecords` only enumerate its typed
input and terminal record coordinates, while `eOut` first exposes the terminal records and then
enumerates that explicit record tuple.  The arbitrary complex operator `W` may contain distinct
reference row and column indices `s,t`; no positivity, trace, or support condition is assumed.
-/
theorem weightedMeasurementSchedule_recordsDiagonal_mapTensorId
    (pA pB : PMF Basis) (N k : ℕ) [NeZero k]
    (W : Quantum.Operators.Op
      (Fintype.card (weightedStreamSystem Unit N).total * k))
    (rA rA' rB rB' : Fin N → StoredRecord) (s t : Fin k)
    (hdiff : rA ≠ rA' ∨ rB ≠ rB') :
    let eIn := Fintype.equivFin (weightedStreamSystem Unit N).total
    let eRecords := Fintype.equivFin
      ((Unit × (Fin N → StoredRecord)) ×
        (Unit × (Fin N → StoredRecord)))
    let eOut := (weightedScheduleOutputEquiv Unit N).trans eRecords
    Quantum.Channels.mapTensorId
        (coordinateLinear eIn eOut
          (weightedMeasurementSchedule pA pB N).denote) W
        (finProdFinEquiv (eRecords (((), rA), ((), rB)), s))
        (finProdFinEquiv (eRecords (((), rA'), ((), rB')), t)) = 0 := by
  dsimp only
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  simp only [Equiv.symm_apply_apply]
  let ρ : Op (weightedStreamSystem Unit N).total := fun i j =>
    W (finProdFinEquiv
        (Fintype.equivFin (weightedStreamSystem Unit N).total i, s))
      (finProdFinEquiv
        (Fintype.equivFin (weightedStreamSystem Unit N).total j, t))
  have hblock :
      (Matrix.of fun i j =>
        W (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))) =
        Matrix.reindex
          (Fintype.equivFin (weightedStreamSystem Unit N).total)
          (Fintype.equivFin (weightedStreamSystem Unit N).total) ρ := by
    ext i j
    simp [ρ, Matrix.reindex_apply]
  rw [hblock]
  calc
    coordinateLinear
          (Fintype.equivFin (weightedStreamSystem Unit N).total)
          ((weightedScheduleOutputEquiv Unit N).trans
            (Fintype.equivFin
              ((Unit × (Fin N → StoredRecord)) ×
                (Unit × (Fin N → StoredRecord)))))
          (weightedMeasurementSchedule pA pB N).denote
          (Matrix.reindex
            (Fintype.equivFin (weightedStreamSystem Unit N).total)
            (Fintype.equivFin (weightedStreamSystem Unit N).total) ρ)
          (Fintype.equivFin
            ((Unit × (Fin N → StoredRecord)) ×
              (Unit × (Fin N → StoredRecord))) (((), rA), ((), rB)))
          (Fintype.equivFin
            ((Unit × (Fin N → StoredRecord)) ×
              (Unit × (Fin N → StoredRecord))) (((), rA'), ((), rB'))) =
        (weightedMeasurementSchedule pA pB N).denote ρ
          ((weightedScheduleOutputEquiv Unit N).symm
            (((), rA), ((), rB)))
          ((weightedScheduleOutputEquiv Unit N).symm
            (((), rA'), ((), rB'))) := by
      simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
        coordinateLinear_reindex_apply
        (Fintype.equivFin (weightedStreamSystem Unit N).total)
        ((weightedScheduleOutputEquiv Unit N).trans
          (Fintype.equivFin
            ((Unit × (Fin N → StoredRecord)) ×
              (Unit × (Fin N → StoredRecord)))))
        (weightedMeasurementSchedule pA pB N).denote ρ
        ((weightedScheduleOutputEquiv Unit N).symm
          (((), rA), ((), rB)))
        ((weightedScheduleOutputEquiv Unit N).symm
          (((), rA'), ((), rB')))
    _ = 0 := by
      have hdiag := weightedMeasurementSchedule_recordsDiagonal pA pB N ρ
      exact hdiag () () () () rA rA' rB rB' hdiff

/-- The complete destructive schedule creates classical honest records against an arbitrary
finite reference from an otherwise arbitrary quantum input operator. -/
theorem weightedMeasurementSchedule_isClassicalOnFirst
    (pA pB : PMF Basis) (N : ℕ)
    {E : Type} [Fintype E] [DecidableEq E]
    (rho : Op ((weightedStreamSystem Unit N).total × E)) :
    IsClassicalOnFirst
      (Alpha := (Boundary.leaf (weightedStreamSystem (finishAcc Unit N) 0)).space)
      (Ref := E)
      (tensorIdLinear E (weightedMeasurementSchedule pA pB N).denote rho) := by
  intro x x' e e' hxx
  rcases x with ⟨⟨⟩, q⟩
  rcases x' with ⟨⟨⟩, q'⟩
  rw [tensorIdLinear_apply]
  have hdiff : q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob := by
    by_cases hAlice : q .alice = q' .alice
    · right
      intro hBob
      apply hxx
      congr
      funext i
      cases i with
      | alice => exact hAlice
      | bob => exact hBob
    · exact Or.inl hAlice
  have hdiag := weightedMeasurementSchedule_honestRegistersDiagonal pA pB N
    (Matrix.of fun i j => rho (i, e) (j, e'))
  simpa [reindexOp, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply,
    Boundary.leafSpaceEquiv] using hdiag q q' hdiff

end QKD.BB84.Measurement
