import QCryptLean.LOCC.Typed.Instrument.UniformChoice
import QCryptLean.LOCC.Typed.Program
import QCryptLean.LOCC.Typed.TwoParty
import QCryptLean.Quantum.Gates

/-!
# Destructive BB84 measurements

This module constructs a single-qubit private measure-and-record primitive and a one-round
Alice-then-Bob private program.  Alice and Bob choose the Z or X basis uniformly, measure
immediately, and retain their local basis/outcome records.  The exact branch operation and
stored-record diagonality are proved for arbitrary finite spectator registers.

The Z/X measurement and late-announcement order follow
arXiv:quant-ph/0512258v2, `main.tex:673-736`.  Independent private basis choices and
fixed-batch late sifting follow Pfister et al., arXiv:1506.07502, Sections IV--V.  Nahar et al.,
arXiv:2403.11851, Appendix B discusses the separate permutation/measurement identity.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open TypedLOCC

open TypedLOCC.TwoParty

/-- The two BB84 measurement bases used by the one-round physical primitive. -/
inductive Basis | z | x
  deriving DecidableEq, Fintype, Nonempty

/-- A local BB84 measurement result. -/
abbrev Bit := Fin 2

/-- The private basis and outcome retained by one laboratory. -/
abbrev Record := Basis × Bit

/-- The output of a destructive qubit measurement: no quantum carrier, followed by its record. -/
abbrev StoredRecord := Unit × Record

/-- There are exactly two basis choices. -/
theorem cardBasis : Fintype.card Basis = 2 := by
  decide

/-- The basis-change matrix: identity for Z and Hadamard for X. -/
def basisUnitary (theta : Basis) : Matrix Bit Bit ℂ :=
  match theta with
  | Basis.z => 1
  | Basis.x => Quantum.Gates.hadamard

/-- The rank-one row Kraus matrix for outcome `x` in basis `theta`. -/
def fixedBasisKraus (theta : Basis) (x : Bit) : Matrix Unit Bit ℂ :=
  fun _ j => basisUnitary theta x j

/-- The two row Kraus matrices of either fixed basis resolve the qubit identity.

This is the single-qubit completeness equation for the Z/X measurements in
arXiv:quant-ph/0512258v2, `main.tex:673-736`. -/
theorem fixedBasisKraus_complete (theta : Basis) :
    ∑ x : Bit, (fixedBasisKraus theta x)ᴴ * fixedBasisKraus theta x = 1 := by
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
  cases theta with
  | z =>
      fin_cases i <;> fin_cases j <;>
        simp [fixedBasisKraus, basisUnitary, Matrix.mul_apply, Fin.sum_univ_two]
  | x =>
      fin_cases i <;> fin_cases j <;>
        simp [fixedBasisKraus, basisUnitary, Quantum.Gates.hadamard,
          Matrix.mul_apply, Fin.sum_univ_two,
          Quantum.Operators.ket_mul_bra_apply, Quantum.Operators.Ket.dag,
          hsqrt] <;>
        norm_num

/-- Measure one qubit in a fixed BB84 basis and discard the measured qubit. -/
def fixedBasisMeasurement (theta : Basis) : Instrument Bit Unit Bit :=
  Instrument.ofFine (fixedBasisKraus theta) (fixedBasisKraus_complete theta)

/-- Choose Z or X uniformly, measure immediately, and retain the local basis/outcome record. -/
def uniformMeasureAndRecord : Instrument Bit StoredRecord Record :=
  (Instrument.uniformChoice fixedBasisMeasurement).keeping

/-- Exact recorded Kraus entry, keeping the observed branch distinct from the stored coordinate.

The amplitude is the uniform-basis factor `1 / sqrt 2` times the selected row of the Z/X
basis-change matrix, and all other stored-record blocks vanish. -/
theorem uniformMeasureAndRecord_kraus_apply
    (observed : Record) (stored : StoredRecord) (j : Bit) :
    uniformMeasureAndRecord.kraus observed () stored j =
      if stored.2 = observed then
        ((1 : ℂ) / (Real.sqrt 2 : ℂ)) *
          basisUnitary observed.1 observed.2 j
      else 0 := by
  simp [uniformMeasureAndRecord, Instrument.keeping,
    Instrument.uniformChoice, Instrument.uniformChoiceKraus,
    Instrument.uniformChoiceScale, fixedBasisMeasurement, Instrument.ofFine,
    fixedBasisKraus, cardBasis]

/-! ## Local actions and the concrete Alice-then-Bob schedule -/

/-- Measure Alice's qubit while leaving an arbitrary finite spectator register untouched. -/
def measureAliceWithSpectator
    (S : Type) [Nonempty S] [Fintype S] [DecidableEq S] :
    PrivateAction (system Bit S) :=
  PrivateAction.ofInstrument .alice
    uniformMeasureAndRecord

/-- Measure Bob's qubit while leaving an arbitrary finite spectator register untouched. -/
def measureBobWithSpectator
    (S : Type) [Nonempty S] [Fintype S] [DecidableEq S] :
    PrivateAction (system S Bit) :=
  PrivateAction.ofInstrument .bob
    uniformMeasureAndRecord

/-- The two-qubit input multipartite system. -/
abbrev inputSystem : MultipartiteSystem Party := system Bit Bit

/-- The multipartite system after both laboratories have measured and retained only classical
records. -/
abbrev outputSystem : MultipartiteSystem Party := system StoredRecord StoredRecord

/-- Alice's first private measurement action. -/
def measureAlice : PrivateAction inputSystem :=
  measureAliceWithSpectator Bit

/-- Bob's independent private measurement action after Alice's action. -/
def measureBob : PrivateAction measureAlice.out :=
  PrivateAction.ofInstrument .bob uniformMeasureAndRecord

/-- Embed an Alice qubit value and spectator coordinate into the input joint register. -/
def aliceInputAt
    {S : Type} [Nonempty S] [Fintype S] [DecidableEq S]
    (j : Bit) (s : S) : (system Bit S).total :=
  (TwoParty.pairEquiv Bit S).symm (j, s)

/-- Embed Alice's stored record and spectator coordinate into the output joint register. -/
def aliceOutputAt
    {S : Type} [Nonempty S] [Fintype S] [DecidableEq S]
    (stored : StoredRecord) (s : S) : (measureAliceWithSpectator S).out.total :=
  ((system Bit S).splitAtSet .alice StoredRecord).symm
    (stored, fun j => match h : j.1 with
      | .alice => (j.2 h).elim
      | .bob => s)

/-- Exact lifted branch operation for Alice with an arbitrary spectator and arbitrary operator.

The two spectator coordinates are independent.  The coefficient is the probability `1/2` of
the observed basis, and the final factor is the explicitly conjugated row entry.  No positivity,
self-adjointness, or trace normalization of `rho` is assumed. -/
theorem measureAliceWithSpectator_liftedOperation_apply
    {S : Type} [Nonempty S] [Fintype S] [DecidableEq S]
    (observed : Record) (rho : Op (system Bit S).total)
    (stored stored' : StoredRecord) (s s' : S) :
    ((measureAliceWithSpectator S).liftedOperation observed rho)
        (aliceOutputAt stored s) (aliceOutputAt stored' s') =
      if stored.2 = observed ∧ stored'.2 = observed then
        (1 / 2 : ℂ) *
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
  change ((uniformMeasureAndRecord.liftAt (system Bit S) .alice).operation observed rho)
    (aliceOutputAt stored s) (aliceOutputAt stored' s') = _
  rw [Instrument.liftAt_operation_apply (R := system Bit S) .alice uniformMeasureAndRecord]
  rw [hout_fst stored s, hout_fst stored' s']
  simp_rw [hrestore]
  unfold uniformMeasureAndRecord
  have hkeep := Instrument.keeping_operation_apply
    (Instrument.uniformChoice fixedBasisMeasurement) observed
    (rho.submatrix (fun x => aliceInputAt x s) (fun y => aliceInputAt y s'))
    stored.1 stored'.1 stored.2 stored'.2
  refine hkeep.trans ?_
  by_cases hstored : stored.2 = observed ∧ stored'.2 = observed
  · rw [if_pos hstored, if_pos hstored]
    rw [Instrument.uniformChoice_operation]
    simp [cardBasis, fixedBasisMeasurement, Instrument.operation,
      Instrument.ofFine, matrixConjLinear, fixedBasisKraus,
      Matrix.mul_apply, TwoParty.system]
    ring
  · simp [hstored]

/-- Block-diagonality in Alice's retained record, with an otherwise arbitrary spectator. -/
def AliceRecordDiagonal
    {S : Type} [Nonempty S] [Fintype S] [DecidableEq S]
    (sigma : Op (measureAliceWithSpectator S).out.total) : Prop :=
  ∀ stored stored' : StoredRecord, ∀ s s' : S,
    stored.2 ≠ stored'.2 →
      sigma (aliceOutputAt stored s) (aliceOutputAt stored' s') = 0

/-- Summing the private physical outcomes yields an output diagonal in the stored record.

This is the precise CQ invariant asserted here.  `StoredRecord` remains a quantum-register index
type in the typed syntax; the theorem supplies the diagonal invariant rather than treating that
type alone as a ban on coherent actions. -/
theorem measureAliceWithSpectator_sum_isRecordDiagonal
    {S : Type} [Nonempty S] [Fintype S] [DecidableEq S]
    (rho : Op (system Bit S).total) :
    AliceRecordDiagonal
      ((∑ observed : Record,
          (measureAliceWithSpectator S).liftedOperation observed) rho) := by
  intro stored stored' s s' hne
  simp only [LinearMap.sum_apply, Matrix.sum_apply]
  simp_rw [measureAliceWithSpectator_liftedOperation_apply]
  apply Finset.sum_eq_zero
  intro observed _
  rw [if_neg]
  intro hboth
  exact hne (hboth.1.trans hboth.2.symm)

/-- One physical round: Alice measures privately, Bob measures privately, then the program ends. -/
def singleQubitRoundProgram : Program inputSystem (.leaf outputSystem) := by
  simpa only [measureBob, measureAlice, measureAliceWithSpectator,
    PrivateAction.out_ofInstrument, inputSystem, TwoParty.set_alice, TwoParty.set_bob] using
    measureAlice.then (measureBob.then .done)

/-! ## Definition-driven constructor probes -/

/-- The fixed-basis object is literally a one-row Kraus matrix. -/
theorem fixedBasisKraus_is_row (theta : Basis) (x j : Bit) :
    fixedBasisKraus theta x () j = basisUnitary theta x j := by
  rfl

/-- The actual recorded Kraus matrix has no support in a different stored-record block. -/
theorem uniformMeasureAndRecord_wrongStored_zero
    (observed : Record) (stored : StoredRecord) (j : Bit)
    (h : stored.2 ≠ observed) :
    uniformMeasureAndRecord.kraus observed () stored j = 0 := by
  simp [uniformMeasureAndRecord, Instrument.keeping, h]

/-- The program is two private nodes followed by termination, with its output boundary transported
from the computed system to the stated record-register system. -/
theorem singleQubitRoundProgram_shape :
    singleQubitRoundProgram ≍
      Program.priv measureAlice (Program.priv measureBob Program.done) := by
  exact cast_heq _ _

end QKD.BB84.Measurement
