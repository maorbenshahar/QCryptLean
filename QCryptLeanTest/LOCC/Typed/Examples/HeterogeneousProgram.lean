import QCryptLean.LOCC.Typed.Program.Denotation

/-!
# Heterogeneous typed LOCC programs

These finite examples exercise the public/private control-flow distinction in `Program` and a
boundary whose terminal quantum-register dimension depends on the announced outcome.  All Kraus
families are written explicitly.
-/

open scoped Matrix BigOperators
open Matrix

namespace TypedLOCC.Examples.HeterogeneousProgram

/-- The two named laboratories used in the examples. -/
inductive Party
  | alice
  | bob
  deriving DecidableEq, Fintype

/-- Alice initially holds a bit and Bob holds the trivial register. -/
def inputSystem : MultipartiteSystem Party where
  reg
    | .alice => Bool
    | .bob => Unit
  nonemptyReg p := by cases p <;> infer_instance
  finReg p := by cases p <;> infer_instance
  decReg p := by cases p <;> infer_instance

/-- Alice's public bit selects either a trivial or a four-dimensional output register. -/
def outputRegister (y : Bool) : Type :=
  match y with
  | false => Unit
  | true => Bool × Bool

instance (y : Bool) : Nonempty (outputRegister y) := by
  cases y <;> dsimp [outputRegister] <;> infer_instance
instance (y : Bool) : Fintype (outputRegister y) := by
  cases y <;> dsimp [outputRegister] <;> infer_instance
instance (y : Bool) : DecidableEq (outputRegister y) := by
  cases y <;> dsimp [outputRegister] <;> infer_instance

/-! ## Coarse-graining raw outcomes -/

/-- Computational-basis measurement, with one Kraus operator per observed result. -/
def computationalMeasure (A : Type) [Fintype A] [DecidableEq A] : Instrument A A A where
  krausIndex _ := Unit
  kraus a _ := Matrix.of fun i j => if i = a ∧ j = a then 1 else 0
  complete := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply, ite_and]
    simp [eq_comm]

/-- Alice privately measures her bit without changing the multipartite system. -/
def privateMeasure : PrivateAction inputSystem :=
  PrivateAction.ofInstrument .alice
    (computationalMeasure Bool)

/-- Alice measures a bit, while both raw outcomes are coarse-grained to the sole public value. -/
def coarseAction : AnnouncedAction inputSystem Unit :=
  AnnouncedAction.ofInstrument (P := Party) .alice
    (computationalMeasure Bool) (fun _ => ())

/-- Both distinct raw outcomes have the same public announcement. -/
theorem coarseAction_announces_one_value :
    coarseAction.announce false = coarseAction.announce true :=
  rfl

/-- The one-step coarse-grained program. -/
def coarseProgram : Program inputSystem coarseAction.boundary :=
  coarseAction.run

/-- The identity channel as a one-outcome instrument. -/
def identityInstrument : Instrument Bool Bool Unit where
  krausIndex _ := Unit
  kraus _ _ := 1
  complete := by simp

/-- An announced action whose public alphabet contains an unused value: its sole raw outcome
always announces `false`, although `true` remains a well-typed public branch. -/
def unusedLabelAction : AnnouncedAction inputSystem Bool :=
  AnnouncedAction.ofInstrument (P := Party) .alice
    identityInstrument (fun _ : Unit => false)

/-- No raw outcome of `unusedLabelAction` announces the public value `true`. -/
theorem unusedLabelAction_ne_true (o : unusedLabelAction.Outcome) :
    unusedLabelAction.announce o ≠ true := by
  cases o
  decide

/-- The boundary retains both declared public values even though only `false` is physically
reached by this action. -/
def unusedLabelProgram : Program inputSystem unusedLabelAction.boundary :=
  unusedLabelAction.run

/-- Every hidden branch of the unused-label example exits through the `false` public block. -/
theorem unusedLabelProgram_exit_false (b : unusedLabelProgram.Branch) :
    b.exit.1 = false := by
  rcases b with ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩
  rfl

/-! ## Branch-dependent successor dimensions -/

/-- A dependent family of Kraus matrices.  The `false` branch maps Alice's input bit to `Unit`;
the `true` branch maps it into one distinguished coordinate of `Bool × Bool`. -/
def branchKraus (o : Bool) :
    Matrix (outputRegister o) (inputSystem.reg .alice) ℂ :=
  match o with
  | false => Matrix.of fun _ j => if j = false then 1 else 0
  | true => Matrix.of fun i j => if i = (false, false) ∧ j = true then 1 else 0

/-- The two branch-dependent Kraus matrices form a complete instrument on Alice's input bit. -/
theorem branchKraus_complete :
    ∑ o : Bool, (branchKraus o)ᴴ * branchKraus o = 1 := by
  rw [Fintype.sum_bool]
  let Kt : Matrix (Bool × Bool) Bool ℂ := branchKraus true
  let Kf : Matrix Unit Bool ℂ := branchKraus false
  change Ktᴴ * Kt + Kfᴴ * Kf = (1 : Matrix Bool Bool ℂ)
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hKt (a : Bool × Bool) (b : Bool) :
      Kt a b = if a = (false, false) ∧ b = true then 1 else 0 := rfl
  have hKf (a : Unit) (b : Bool) : Kf a b = if b = false then 1 else 0 := rfl
  cases i <;> cases j <;> simp [hKt, hKf]

/-- Alice announces the raw bit and obtains a successor multipartite system whose register dimension
depends on that bit. -/
def branchAction : AnnouncedAction privateMeasure.out Bool where
  actor := .alice
  Output := outputRegister
  Outcome := Bool
  announce := id
  krausIndex _ := Unit
  kraus o _ := branchKraus o
  complete := by simpa using branchKraus_complete

/-- The two public branches have different Alice-register dimensions. -/
theorem successor_actor_dimensions :
    Fintype.card ((branchAction.out false).reg .alice) = 1 ∧
      Fintype.card ((branchAction.out true).reg .alice) = 4 := by
  decide

/-- The branch-dependent boundary selected by `branchAction`. -/
abbrev branchBoundary : Boundary Party :=
  branchAction.boundary

/-- The input coordinate dimension is nonzero. -/
instance instNeZeroInputSystemTotalCard : NeZero (Fintype.card privateMeasure.out.total) :=
  ⟨Fintype.card_ne_zero⟩

/-- The heterogeneous output space is inhabited by its small public branch. -/
instance instNonemptyBranchBoundarySpace : Nonempty branchBoundary.space :=
  (inferInstance : Nonempty (branchAction.out false).total).elim fun q => ⟨⟨⟨false, ()⟩, q⟩⟩

/-- The heterogeneous output coordinate dimension is nonzero. -/
instance instNeZeroBranchBoundarySpaceCard : NeZero (Fintype.card branchBoundary.space) :=
  ⟨Fintype.card_ne_zero⟩

/-- A one-action program whose two terminal multipartite systems have different output dimensions.
-/
def branchProgram : Program privateMeasure.out branchBoundary :=
  branchAction.run

/-- The heterogeneous program denotes a CPTP channel in canonical finite coordinates. -/
theorem branchProgram_isCPTP :
    Quantum.Channels.IsCPTP ⇑(coordinateLinear
      (Fintype.equivFin privateMeasure.out.total)
      (Fintype.equivFin branchBoundary.space)
      branchProgram.denote) := by
  exact branchProgram.coordinateDenote_isCPTP
    (Fintype.equivFin privateMeasure.out.total)
    (Fintype.equivFin branchBoundary.space)

/-- Distinct public exits have a zero off-diagonal output block for every input operator `rho`;
no positivity, Hermiticity, or block-diagonality assumption is made on the input. -/
theorem branchProgram_cross_exit_zero (rho : Op privateMeasure.out.total)
    (a : (branchAction.out false).total) (b : (branchAction.out true).total) :
    branchProgram.denote rho ⟨⟨false, ()⟩, a⟩ ⟨⟨true, ()⟩, b⟩ = 0 := by
  exact Program.denote_public_block_zero
    (next := fun y : Bool => Boundary.leaf (branchAction.out y))
    (p := branchProgram) rho (y := false) (z := true) (by decide) () () a b

/-- The joint input basis vector with Alice's coordinate fixed to `bit`. -/
def inputBasis (bit : Bool) : privateMeasure.out.total :=
  fun p =>
    match p with
    | .alice => bit
    | .bob => ()

/-- A single off-diagonal coherence between Alice's two input basis values. -/
def offDiagonalInput : Op privateMeasure.out.total :=
  Matrix.of fun i j => if i = inputBasis false ∧ j = inputBasis true then 1 else 0

/-- Cross-exit coherence remains zero on an explicitly off-diagonal input. -/
theorem branchProgram_cross_exit_zero_on_offDiagonalInput
    (a : (branchAction.out false).total) (b : (branchAction.out true).total) :
    branchProgram.denote offDiagonalInput ⟨⟨false, ()⟩, a⟩ ⟨⟨true, ()⟩, b⟩ = 0 :=
  branchProgram_cross_exit_zero offDiagonalInput a b

/-! ## Private and nested authoring -/

/-- A private action has one outcome-independent continuation: the continuation below is a
single value, not a function from the private `Bool` outcome. -/
def privateThenBranch :
    Program inputSystem branchBoundary :=
  privateMeasure.then branchProgram

/-- The complete hidden path that first records the private outcome at the private measurement and
then takes the public outcome at the announced action.  Both syntactic paths exist even when their
composite Kraus matrix has zero support. -/
def privateThenBranchBranch (privateOutcome publicOutcome : Bool) :
    privateThenBranch.Branch :=
  ⟨privateOutcome, ⟨(), ⟨publicOutcome, ⟨(), ()⟩⟩⟩⟩

/-- The announced and private lifted Kraus matrices have incompatible support when their Boolean
outcomes differ.  This is a support calculation, not public control over the private outcome. -/
theorem privateThenBranch_liftedKraus_mul_eq_zero_of_ne
    (privateOutcome publicOutcome : Bool) (h : publicOutcome ≠ privateOutcome) :
    branchAction.liftedKraus publicOutcome () *
        privateMeasure.liftedKraus privateOutcome () = 0 := by
  cases privateOutcome <;> cases publicOutcome
  · exact (h rfl).elim
  · ext a b
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro x _
    cases hx : x .alice <;>
      simp only [AnnouncedAction.liftedKraus, inputSystem, privateMeasure, computationalMeasure,
        PrivateAction.ofInstrument, branchAction, branchKraus, outputRegister, id_eq,
        localKrausLift_apply, MultipartiteSystem.splitAtSet_apply, ne_eq,
        MultipartiteSystem.splitAt, Equiv.piSplitAt_apply, hx, PrivateAction.liftedKraus,
        Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff, and_imp]
    · intro _ _ _ _
      change (if _ then (1 : ℂ) else 0) = 0
      simp
    · intro _ hc
      exact Bool.noConfusion hc
  · ext a b
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro x _
    cases hx : x .alice <;>
      simp only [AnnouncedAction.liftedKraus, inputSystem, privateMeasure, computationalMeasure,
        PrivateAction.ofInstrument, branchAction, branchKraus, outputRegister, id_eq,
        localKrausLift_apply, MultipartiteSystem.splitAtSet_apply, ne_eq,
        MultipartiteSystem.splitAt, Equiv.piSplitAt_apply, hx, PrivateAction.liftedKraus,
        Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff, and_imp]
    · intro _ hc
      exact Bool.noConfusion hc
    · intro _ _ _ _
      rfl
  · exact (h rfl).elim

/-- A syntactically present private-then-announced path with mismatched outcomes has zero path
Kraus matrix.  Thus the later public result agrees with the retained bit on every nonzero path. -/
theorem privateThenBranch_pathKraus_eq_zero_of_ne
    (privateOutcome publicOutcome : Bool) (h : publicOutcome ≠ privateOutcome) :
    Program.Branch.pathKraus (p := privateThenBranch)
        (privateThenBranchBranch privateOutcome publicOutcome) = 0 := by
  simp only [privateThenBranchBranch, privateThenBranch, PrivateAction.then, branchProgram,
    AnnouncedAction.run, AnnouncedAction.then, Program.Branch.pathKraus]
  change (1 : Op (branchAction.out (branchAction.announce publicOutcome)).total) *
    branchAction.liftedKraus publicOutcome () * privateMeasure.liftedKraus privateOutcome () = 0
  rw [Matrix.one_mul]
  exact privateThenBranch_liftedKraus_mul_eq_zero_of_ne privateOutcome publicOutcome h

/-- Function-style nested authoring: first coarse-grain a measurement to `Unit`, then branch on a
second public action with heterogeneous successor multipartite systems. -/
def nestedProgram :
    Program inputSystem
      (.announce Unit fun _ => .announce Bool fun y => .leaf (branchAction.out y)) :=
  coarseAction.then fun _ =>
    branchAction.then fun _ =>
      .done

/-- A complete hidden branch of `nestedProgram`, exposing both raw outcomes only for semantic
inspection.  Neither raw outcome is an argument to the public authoring continuations above. -/
def nestedBranch (first : coarseAction.Outcome) (second : Bool) : nestedProgram.Branch :=
  ⟨first, ⟨(), ⟨second, ⟨(), ()⟩⟩⟩⟩

/-- Along two consecutive actions, the later joint Kraus matrix multiplies on the left of the
earlier one. -/
theorem nestedProgram_pathKraus_order (first : coarseAction.Outcome) (second : Bool) :
    Program.Branch.pathKraus (p := nestedProgram) (nestedBranch first second) =
      branchAction.liftedKraus second () *
        (show Matrix privateMeasure.out.total inputSystem.total ℂ from
          coarseAction.liftedKraus first ()) := by
  simp only [nestedBranch, nestedProgram, AnnouncedAction.then, Program.Branch.pathKraus]
  change (1 : Op (branchAction.out (branchAction.announce second)).total) *
    branchAction.liftedKraus second () *
    (show Matrix privateMeasure.out.total inputSystem.total ℂ from
      coarseAction.liftedKraus first ()) = _
  rw [Matrix.one_mul]

end TypedLOCC.Examples.HeterogeneousProgram
