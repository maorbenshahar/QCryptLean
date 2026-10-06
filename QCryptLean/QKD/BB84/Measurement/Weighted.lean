import QCryptLean.LOCC.Typed.Instrument.WeightedChoice
import QCryptLean.QKD.BB84.Measurement

/-!
# PMF-weighted one-round BB84 measurement

This module replaces the uniform local basis seed in the destructive BB84 measurement by an
arbitrary fixed PMF. Alice and Bob receive separate PMFs and act in two separate private nodes.
The branch formula specializes the finite weighted instrument mixture of
Chitambar et al., arXiv:1210.4583, Section 2.

Renner, arXiv:quant-ph/0512258v2, source lines 673--736 motivates the prepare-and-measure order but
does not prove this arbitrary-bipartite-input statement.  Pfister et al., arXiv:1506.07502v3,
Sections IV--V motivate fixed independent local basis laws and late announcements.  No multi-round,
channel-security, or memory-freeness theorem is asserted here.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open TypedLOCC

open TypedLOCC.TwoParty

/-- Measure in a PMF-distributed BB84 basis and retain the local basis/outcome record. -/
def weightedMeasureAndRecord (p : PMF Basis) : Instrument Bit StoredRecord Record :=
  (Instrument.weightedChoice p fixedBasisMeasurement).keeping

/-- Exact recorded Kraus entry for a PMF-weighted BB84 basis choice.

The stored coordinate and observed branch remain distinct.  A matching block has amplitude
`sqrt(p basis)` times the selected row of the basis-change matrix; every other block vanishes. -/
theorem weightedMeasureAndRecord_kraus_apply (p : PMF Basis)
    (observed : Record) (stored : StoredRecord) (j : Bit) :
    (weightedMeasureAndRecord p).kraus observed () stored j =
      if stored.2 = observed then
        (Real.sqrt (p observed.1).toReal : ℂ) *
          basisUnitary observed.1 observed.2 j
      else 0 := by
  simp [weightedMeasureAndRecord, Instrument.keeping,
    Instrument.weightedChoice, Instrument.weightedChoiceKraus,
    Instrument.weightedChoiceScale, fixedBasisMeasurement, Instrument.ofFine,
    fixedBasisKraus]

/-- Each raw branch of the destructive one-qubit measurement creates a diagonal stored record
from an arbitrary input operator.  The raw observed outcome is retained. -/
theorem weightedMeasureAndRecord_operation_storedDiagonal
    (p : PMF Basis) (observed : Record) (rho : Op Bit)
    (stored stored' : StoredRecord) (hne : stored ≠ stored') :
    ((weightedMeasureAndRecord p).operation observed rho) stored stored' = 0 := by
  unfold weightedMeasureAndRecord
  rw [Instrument.keeping_operation_apply, if_neg]
  intro hboth
  apply hne
  exact Prod.ext (Subsingleton.elim _ _) (hboth.1.trans hboth.2.symm)

/-- Measure Alice's qubit with basis law `p`, leaving an arbitrary spectator untouched. -/
def weightedMeasureAliceWithSpectator (p : PMF Basis)
    (S : Type) [Nonempty S] [Fintype S] [DecidableEq S] :
    PrivateAction (system Bit S) :=
  PrivateAction.ofInstrument .alice
    (weightedMeasureAndRecord p)

/-- Measure Bob's qubit with basis law `p`, leaving an arbitrary spectator untouched. -/
def weightedMeasureBobWithSpectator (p : PMF Basis)
    (S : Type) [Nonempty S] [Fintype S] [DecidableEq S] :
    PrivateAction (system S Bit) :=
  PrivateAction.ofInstrument .bob
    (weightedMeasureAndRecord p)

/-- Alice's PMF-weighted first measurement action. -/
def weightedMeasureAlice (pA : PMF Basis) : PrivateAction inputSystem :=
  weightedMeasureAliceWithSpectator pA Bit

/-- Bob's separately PMF-weighted measurement action after Alice. -/
def weightedMeasureBob (pA pB : PMF Basis) : PrivateAction (weightedMeasureAlice pA).out :=
  PrivateAction.ofInstrument .bob (weightedMeasureAndRecord pB)

/-- One physical round with separate local basis laws: Alice, then Bob, then termination. -/
def weightedSingleQubitRoundProgram (pA pB : PMF Basis) :
    Program inputSystem (.leaf outputSystem) :=
  cast (by
    simp only [weightedMeasureBob, weightedMeasureAlice, weightedMeasureAliceWithSpectator,
      PrivateAction.out_ofInstrument, inputSystem, TwoParty.set_alice, TwoParty.set_bob])
    ((weightedMeasureAlice pA).then ((weightedMeasureBob pA pB).then .done))

/-- Exact lifted Alice branch operation for arbitrary PMF, spectator, and input operator.

The two spectator coordinates remain independent.  The coefficient is the selected basis
probability, and no positivity, self-adjointness, or trace normalization of `rho` is assumed. -/
theorem weightedMeasureAliceWithSpectator_liftedOperation_apply
    {S : Type} [Nonempty S] [Fintype S] [DecidableEq S]
    (p : PMF Basis) (observed : Record) (rho : Op (system Bit S).total)
    (stored stored' : StoredRecord) (s s' : S) :
    ((weightedMeasureAliceWithSpectator p S).liftedOperation observed rho)
        (aliceOutputAt stored s) (aliceOutputAt stored' s') =
      if stored.2 = observed ∧ stored'.2 = observed then
        ((p observed.1).toReal : ℂ) *
          ∑ j : Bit, ∑ k : Bit,
            basisUnitary observed.1 observed.2 j *
              rho (aliceInputAt j s) (aliceInputAt k s') *
                star (basisUnitary observed.1 observed.2 k)
      else 0 := by
  have hout_fst (a : StoredRecord) (t : S) :
      (((system Bit S).splitAtSet .alice StoredRecord)
        (aliceOutputAt a t)).1 = a := by
    simp [aliceOutputAt]
  have hrestore (j : Bit) (a : StoredRecord) (t : S) :
      ((system Bit S).splitAt .alice).symm
          (j, (((system Bit S).splitAtSet .alice StoredRecord)
              (aliceOutputAt a t)).2) = aliceInputAt j t := by
    apply (TwoParty.pairEquiv Bit S).injective
    apply Prod.ext <;>
      simp [aliceInputAt, aliceOutputAt, MultipartiteSystem.splitAt, TwoParty.pairEquiv]
  change (((weightedMeasureAndRecord p).liftAt (system Bit S) .alice).operation observed rho)
    (aliceOutputAt stored s) (aliceOutputAt stored' s') = _
  rw [Instrument.liftAt_operation_apply (R := system Bit S) .alice
    (weightedMeasureAndRecord p)]
  rw [hout_fst stored s, hout_fst stored' s']
  simp_rw [hrestore]
  unfold weightedMeasureAndRecord
  rw [Instrument.keeping_operation_apply]
  by_cases hstored : stored.2 = observed ∧ stored'.2 = observed
  · rw [if_pos hstored, if_pos hstored]
    rw [Instrument.weightedChoice_operation]
    simp [fixedBasisMeasurement, Instrument.operation,
      Instrument.ofFine, matrixConjLinear, fixedBasisKraus,
      Matrix.mul_apply, TwoParty.system]
    ring
  · simp [hstored]

/-- Summing the private weighted outcomes yields an output diagonal in Alice's stored record.

`StoredRecord` is still a quantum-register index in the typed syntax; this theorem, rather than
the record type alone, supplies the CQ block-diagonal invariant. -/
theorem weightedMeasureAliceWithSpectator_sum_isRecordDiagonal
    {S : Type} [Nonempty S] [Fintype S] [DecidableEq S]
    (p : PMF Basis) (rho : Op (system Bit S).total) :
    AliceRecordDiagonal
      ((∑ observed : Record,
          (weightedMeasureAliceWithSpectator p S).liftedOperation observed) rho) := by
  intro stored stored' s s' hne
  simp only [LinearMap.sum_apply, Matrix.sum_apply]
  simp_rw [weightedMeasureAliceWithSpectator_liftedOperation_apply]
  apply Finset.sum_eq_zero
  intro observed _
  rw [if_neg]
  intro hboth
  exact hne (hboth.1.trans hboth.2.symm)

/-- At the uniform PMF, weighted recording has the existing branch operations. -/
theorem weightedMeasureAndRecord_uniform_operation (observed : Record) :
    (weightedMeasureAndRecord (PMF.uniformOfFintype Basis)).operation observed =
      uniformMeasureAndRecord.operation observed := by
  unfold weightedMeasureAndRecord uniformMeasureAndRecord
  apply LinearMap.ext
  intro rho
  ext stored stored'
  rcases stored with ⟨h, record⟩
  rcases stored' with ⟨h', record'⟩
  rw [Instrument.keeping_operation_apply,
    Instrument.keeping_operation_apply]
  by_cases hstored : record = observed ∧ record' = observed
  · rw [if_pos hstored, if_pos hstored,
      Instrument.weightedChoice_uniform_operation]
  · simp [hstored]

/-- At the uniform PMF, weighted recording has the existing total channel. -/
theorem weightedMeasureAndRecord_uniform_channel :
    (weightedMeasureAndRecord (PMF.uniformOfFintype Basis)).channel =
      uniformMeasureAndRecord.channel := by
  unfold Instrument.channel
  apply Finset.sum_congr rfl
  intro observed _
  exact weightedMeasureAndRecord_uniform_operation observed

/-! ## Definition-driven probes -/

/-- A pure-Z law has zero Kraus amplitude in every observed X-basis branch. -/
theorem weightedMeasureAndRecord_pureZ_x_kraus_zero
    (x : Bit) (stored : StoredRecord) (j : Bit) :
    (weightedMeasureAndRecord (PMF.pure Basis.z)).kraus (Basis.x, x) () stored j = 0 := by
  rw [weightedMeasureAndRecord_kraus_apply]
  simp

/-- A pure-Z law has the zero operation in every observed X-basis branch. -/
theorem weightedMeasureAndRecord_pureZ_x_operation_zero (x : Bit) :
    (weightedMeasureAndRecord (PMF.pure Basis.z)).operation (Basis.x, x) = 0 := by
  unfold weightedMeasureAndRecord
  apply LinearMap.ext
  intro rho
  ext stored stored'
  rcases stored with ⟨⟨⟩, record⟩
  rcases stored' with ⟨⟨⟩, record'⟩
  simp [Instrument.keeping_operation_apply,
    Instrument.weightedChoice_operation_of_eq_zero]

/-- The program retains the separate local basis laws in two private nodes, with its computed
output boundary transported to the stated record-register system. -/
theorem weightedSingleQubitRoundProgram_shape (pA pB : PMF Basis) :
    weightedSingleQubitRoundProgram pA pB ≍
      Program.priv (weightedMeasureAlice pA)
        (Program.priv (weightedMeasureBob pA pB) Program.done) := by
  exact cast_heq _ _

end QKD.BB84.Measurement
