import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.LOCC.Typed.Program.ExitWeight
import QCryptLean.LOCC.Typed.Instrument.TwoParty

/-!
# Chronological all-record classicality for the destructive measurement schedule

This external statement fixture gives explicit coordinates for the terminal registers of the
finite private measurement schedule and states their all-record block-diagonality.  The generic
auxiliary accumulator remains an arbitrary coherent finite factor: only the newly generated
chronological `StoredRecord` vectors are asserted diagonal.

The local `K ⊗ 1` semantics and private sequential instrument tree follow
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2.  Renner,
arXiv:quant-ph/0512258v2, source lines 673--736 and Pfister et al., arXiv:1506.07502v3,
Sections IV--V motivate the prepare-and-measure schedule and late announcement; they do not state
this exact arbitrary-operator typed-coordinate theorem.  No batch identity, sampling law,
reference extension, memory-freedom, or security conclusion is included here.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open TypedLOCC

open TypedLOCC.TwoParty

/-- Explicit decidable equality for finite chronological stored-record vectors. -/
@[implicit_reducible] def storedRecordVectorDecidableEq (N : ℕ) :
    DecidableEq (Fin N → StoredRecord) :=
  Fintype.decidablePiFintype

attribute [local instance] storedRecordVectorDecidableEq

/-! ## Explicit terminal coordinates -/

/-- Remove the unique empty remaining stream and expose the chronological accumulator records.

This pure equivalence requires no finiteness, decidable-equality, or inhabitance instance for `F`.
-/
def finishedStreamEquiv (F : Type) (N : ℕ) :
    streamRegister (finishAcc F N) 0 ≃ F × (Fin N → StoredRecord) where
  toFun q := finishAccEquiv F N q.1
  invFun q := ((finishAccEquiv F N).symm q, fun i => Fin.elim0 i)
  left_inv q := by
    rcases q with ⟨acc, tail⟩
    apply Prod.ext
    · exact (finishAccEquiv F N).symm_apply_apply acc
    · funext i
      exact Fin.elim0 i
  right_inv q := (finishAccEquiv F N).apply_symm_apply q

/-- Forward coordinate formula for the finished stream equivalence. -/
@[simp] theorem finishedStreamEquiv_apply (F : Type) (N : ℕ)
    (q : streamRegister (finishAcc F N) 0) :
    finishedStreamEquiv F N q = finishAccEquiv F N q.1 := by
  rfl

/-- Inverse coordinate formula, with the unique empty remaining stream made explicit. -/
@[simp] theorem finishedStreamEquiv_symm_apply (F : Type) (N : ℕ)
    (q : F × (Fin N → StoredRecord)) :
    (finishedStreamEquiv F N).symm q =
      ((finishAccEquiv F N).symm q, fun i => Fin.elim0 i) := by
  rfl

/-- Product coordinates of the two-party input stream multipartite system. -/
def weightedStreamPairEquiv (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (N : ℕ) :
    (weightedStreamSystem F N).total ≃
      streamRegister F N × streamRegister F N :=
  TwoParty.pairEquiv (streamRegister F N) (streamRegister F N)

/-- Forward input coordinate formula: Alice's local stream followed by Bob's local stream. -/
@[simp] theorem weightedStreamPairEquiv_apply (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (N : ℕ)
    (q : (weightedStreamSystem F N).total) :
    weightedStreamPairEquiv F N q = (q .alice, q .bob) := by
  rfl

/-- Terminal boundary coordinates displaying both initial accumulators and both record vectors. -/
def weightedScheduleOutputEquiv (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (N : ℕ) :
    (Boundary.leaf (weightedStreamSystem (finishAcc F N) 0)).space ≃
      (F × (Fin N → StoredRecord)) ×
        (F × (Fin N → StoredRecord)) :=
  (Boundary.leafSpaceEquiv (weightedStreamSystem (finishAcc F N) 0)).trans
    ((TwoParty.pairEquiv
      (streamRegister (finishAcc F N) 0)
      (streamRegister (finishAcc F N) 0)).trans
      (Equiv.prodCongr (finishedStreamEquiv F N) (finishedStreamEquiv F N)))

/-- Forward terminal coordinate formula for Alice and Bob's chronological records. -/
@[simp] theorem weightedScheduleOutputEquiv_apply (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (N : ℕ)
    (q : (Boundary.leaf (weightedStreamSystem (finishAcc F N) 0)).space) :
    weightedScheduleOutputEquiv F N q =
      (finishAccEquiv F N
          ((Boundary.leafSpaceEquiv (weightedStreamSystem (finishAcc F N) 0) q) .alice).1,
        finishAccEquiv F N
          ((Boundary.leafSpaceEquiv (weightedStreamSystem (finishAcc F N) 0) q) .bob).1) := by
  rfl

/-- Inverse terminal coordinate formula, including each unique empty remaining stream. -/
@[simp] theorem weightedScheduleOutputEquiv_symm_apply (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (N : ℕ)
    (q : (F × (Fin N → StoredRecord)) ×
      (F × (Fin N → StoredRecord))) :
    (weightedScheduleOutputEquiv F N).symm q =
      (Boundary.leafSpaceEquiv (weightedStreamSystem (finishAcc F N) 0)).symm
        ((TwoParty.pairEquiv
          (streamRegister (finishAcc F N) 0)
          (streamRegister (finishAcc F N) 0)).symm
          ((finishedStreamEquiv F N).symm q.1,
            (finishedStreamEquiv F N).symm q.2)) := by
  rfl

/-! ## Record diagonality -/

/-- Block-diagonality in both chronological record vectors, preserving arbitrary accumulator
row/column coherence.

All four `F` coordinates are independent.  The predicate constrains an entry only when Alice's
record vectors differ or Bob's record vectors differ; it makes no classicality assertion about
the auxiliary accumulator itself. -/
def ScheduleRecordsDiagonal (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (N : ℕ)
    (sigma : Op (Boundary.leaf (weightedStreamSystem (finishAcc F N) 0)).space) : Prop :=
  ∀ (fA fA' fB fB' : F)
    (rA rA' rB rB' : Fin N → StoredRecord),
    rA ≠ rA' ∨ rB ≠ rB' →
      (reindexOp (weightedScheduleOutputEquiv F N) sigma)
          ((fA, rA), (fB, rB)) ((fA', rA'), (fB', rB')) = 0

/-! ## One head step in two-party coordinates -/

/-- Alice's head step acts on her local stream, separately at each pair of Bob coordinates. -/
theorem weightedStreamAliceAction_liftedOperation_apply
    (p : PMF Basis) (G : Type) [Nonempty G] [Fintype G] [DecidableEq G] (n : ℕ)
    (observed : Record) (sigma : Op (weightedStreamSystem G (n + 1)).total)
    (a a' : streamRegister (G × StoredRecord) n)
    (b b' : streamRegister G (n + 1)) :
    ((weightedStreamAliceAction p G n).liftedOperation observed sigma)
      ((MultipartiteSystem.pairEquiv _).symm (a, b))
      ((MultipartiteSystem.pairEquiv _).symm (a', b')) =
    ((weightedStreamStep p G n).operation observed
      (sigma.submatrix
        (fun x => (TwoParty.pairEquiv _ _).symm (x, b))
        (fun x => (TwoParty.pairEquiv _ _).symm (x, b')))) a a' := by
  change (((weightedStreamStep p G n).liftAt (weightedStreamSystem G (n + 1))
    .alice).operation observed sigma) _ _ = _
  exact Instrument.liftAt_alice_operation_apply _ _ _ _ _ _ _ _

/-- Bob's head step acts on his local stream, separately at each pair of Alice coordinates. -/
theorem weightedStreamBobAction_liftedOperation_apply
    (pA pB : PMF Basis) (G : Type) [Nonempty G] [Fintype G] [DecidableEq G] (n : ℕ)
    (observed : Record) (sigma : Op (weightedStreamAliceAction pA G n).out.total)
    (a a' b b' : streamRegister (G × StoredRecord) n) :
    ((weightedStreamBobAction pA pB G n).liftedOperation observed sigma)
      ((MultipartiteSystem.pairEquiv _).symm (a, b))
      ((MultipartiteSystem.pairEquiv _).symm (a', b')) =
    ((weightedStreamStep pB G n).operation observed
      (sigma.submatrix
        (fun x => (MultipartiteSystem.pairEquiv _).symm (a, x))
        (fun x => (MultipartiteSystem.pairEquiv _).symm (a', x)))) b b' := by
  change (((weightedStreamStep pB G n).liftAt (weightedStreamAliceAction pA G n).out
    .bob).operation observed sigma) _ _ = _
  exact Instrument.liftAt_bob_operation_apply _ _ _ _ _ _ _ _

/-- A zero block between fixed initial accumulator row/column coordinates remains zero after the
entire private destructive schedule.

The premise ranges over every input qubit stream in that fixed accumulator block.  The conclusion
ranges over every output record vector in the same block.  This is the accumulator-preservation
step needed by the recursive CQ argument; it assumes no positivity, normalization, classicality,
or PMF support condition. -/
theorem weightedMeasurementScheduleAux_preserves_accumulator_block_zero
    (pA pB : PMF Basis) (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (N : ℕ)
    (rho : Op (weightedStreamSystem F N).total)
    (fA fA' fB fB' : F)
    (hzero : ∀ (xA xA' xB xB' : Fin N → Bit),
      (reindexOp (weightedStreamPairEquiv F N) rho)
        ((fA, xA), (fB, xB)) ((fA', xA'), (fB', xB')) = 0) :
    ∀ (rA rA' rB rB' : Fin N → StoredRecord),
      (reindexOp (weightedScheduleOutputEquiv F N)
        ((weightedMeasurementScheduleAux pA pB F N).denote rho))
          ((fA, rA), (fB, rB)) ((fA', rA'), (fB', rB')) = 0 := by
  induction N generalizing F with
  | zero =>
      -- With no rounds the schedule is the identity on the empty streams.
      intro rA rA' rB rB'
      rw [weightedMeasurementScheduleAux_zero]
      have hdone := LinearMap.congr_fun
        (Program.denote_done (R := weightedStreamSystem F 0)) rho
      refine (congrArg (fun M => reindexOp (weightedScheduleOutputEquiv F 0) M
        ((fA, rA), (fB, rB)) ((fA', rA'), (fB', rB'))) hdone).trans ?_
      exact hzero (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
        (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | succ n ih =>
      intro rA rA' rB rB'
      have hout := weightedStreamBobAction_out pA pB F n
      -- Alice's head step reads only the zero block of `rho` ...
      have hAliceZero
          (observed : Record)
          (stored stored' : StoredRecord)
          (tailA tailA' : Fin n → Bit)
          (xB xB' : Fin (n + 1) → Bit) :
          ((weightedStreamAliceAction pA F n).liftedOperation observed rho)
            ((MultipartiteSystem.pairEquiv _).symm
              (((fA, stored), tailA), (fB, xB)))
            ((MultipartiteSystem.pairEquiv _).symm
              (((fA', stored'), tailA'), (fB', xB'))) = 0 := by
        rw [weightedStreamAliceAction_liftedOperation_apply, weightedStreamStep_operation_apply]
        have hlocal :
            ((rho.submatrix
              (fun x => (MultipartiteSystem.pairEquiv _).symm (x, (fB, xB)))
              (fun x => (MultipartiteSystem.pairEquiv _).symm (x, (fB', xB')))).submatrix
                (fun j => (fA, Fin.cons j tailA))
                (fun j => (fA', Fin.cons j tailA'))) = 0 := by
          ext j k
          exact hzero (Fin.cons j tailA) (Fin.cons k tailA') xB xB'
        have h :=
          congrArg (fun M => (weightedMeasureAndRecord pA).operation observed M stored stored')
            hlocal
        simp only [map_zero, Matrix.zero_apply] at h
        exact h
      -- ... and Bob's head step reads only the zero block left by Alice's.
      have hBobZero
          (observedA observedB : Record)
          (storedA storedA' storedB storedB' : StoredRecord)
          (tailA tailA' tailB tailB' : Fin n → Bit) :
          ((weightedStreamBobAction pA pB F n).liftedOperation observedB
            ((weightedStreamAliceAction pA F n).liftedOperation observedA rho))
              ((MultipartiteSystem.pairEquiv _).symm
                (((fA, storedA), tailA), ((fB, storedB), tailB)))
              ((MultipartiteSystem.pairEquiv _).symm
                (((fA', storedA'), tailA'), ((fB', storedB'), tailB'))) = 0 := by
        rw [weightedStreamBobAction_liftedOperation_apply, weightedStreamStep_operation_apply]
        have hlocal :
            ((((weightedStreamAliceAction pA F n).liftedOperation observedA rho).submatrix
              (fun x => (MultipartiteSystem.pairEquiv _).symm (((fA, storedA), tailA), x))
              (fun x => (MultipartiteSystem.pairEquiv _).symm
                (((fA', storedA'), tailA'), x))).submatrix
                (fun j => (fB, Fin.cons j tailB))
                (fun j => (fB', Fin.cons j tailB'))) = 0 := by
          ext j k
          exact hAliceZero observedA storedA storedA' tailA tailA'
            (Fin.cons j tailB) (Fin.cons k tailB')
        have h :=
          congrArg (fun M => (weightedMeasureAndRecord pB).operation observedB M storedB storedB')
            hlocal
        simp only [map_zero, Matrix.zero_apply] at h
        exact h
      change ((weightedMeasurementScheduleAux pA pB F (n + 1)).denote rho)
        ((weightedScheduleOutputEquiv F (n + 1)).symm
          ((fA, rA), (fB, rB)))
        ((weightedScheduleOutputEquiv F (n + 1)).symm
          ((fA', rA'), (fB', rB'))) = 0
      rw [weightedMeasurementScheduleAux_succ,
        Program.denote_priv_eq_sum_liftedOperation]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro observedA _
      rw [Program.denote_priv_eq_sum_liftedOperation]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro observedB _
      let rhoAB : Op (weightedStreamBobAction pA pB F n).out.total :=
        (weightedStreamBobAction pA pB F n).liftedOperation observedB
          ((weightedStreamAliceAction pA F n).liftedOperation observedA rho)
      change (cast (congrArg (fun R => Program R
        (.leaf (weightedStreamSystem (finishAcc (F × StoredRecord) n) 0))) hout.symm)
          (weightedMeasurementScheduleAux pA pB (F × StoredRecord) n)).denote _ _ _ = _
      refine (Program.denote_cast_apply hout rfl
        (weightedMeasurementScheduleAux pA pB (F × StoredRecord) n)
        rhoAB
        ((weightedScheduleOutputEquiv F (n + 1)).symm ((fA, rA), (fB, rB)))
        ((weightedScheduleOutputEquiv F (n + 1)).symm ((fA', rA'), (fB', rB')))).trans ?_
      have hrec := ih (F := F × StoredRecord)
        (rho := (rhoAB.submatrix
            (Equiv.cast (congrArg MultipartiteSystem.total hout)).symm
            (Equiv.cast (congrArg MultipartiteSystem.total hout)).symm))
        (fA := (fA, rA 0)) (fA' := (fA', rA' 0))
        (fB := (fB, rB 0)) (fB' := (fB', rB' 0))
        (hzero := fun xA xA' xB xB' => by
          exact (congrArg₂ rhoAB
            (weightedStreamBobAction_out_cast_pairEquiv_symm pA pB F n
              ((fA, rA 0), xA) ((fB, rB 0), xB))
            (weightedStreamBobAction_out_cast_pairEquiv_symm pA pB F n
              ((fA', rA' 0), xA') ((fB', rB' 0), xB'))).trans
            (hBobZero observedA observedB (rA 0) (rA' 0) (rB 0) (rB' 0) xA xA' xB xB'))
        (Fin.tail rA) (Fin.tail rA') (Fin.tail rB) (Fin.tail rB')
      exact hrec

/-- The auxiliary schedule makes every generated Alice and Bob record vector diagonal.

The input operator is arbitrary and the initial accumulator remains coherent.  This theorem has
no caller-supplied block-zero, positivity, trace, classical-input, or support premise. -/
theorem weightedMeasurementScheduleAux_recordsDiagonal
    (pA pB : PMF Basis) (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (N : ℕ)
    (rho : Op (weightedStreamSystem F N).total) :
    ScheduleRecordsDiagonal F N
      ((weightedMeasurementScheduleAux pA pB F N).denote rho) := by
  unfold ScheduleRecordsDiagonal
  induction N generalizing F with
  | zero =>
      intro fA fA' fB fB' rA rA' rB rB' h
      exfalso
      apply h.elim
      · intro hA
        apply hA
        funext i
        exact Fin.elim0 i
      · intro hB
        apply hB
        funext i
        exact Fin.elim0 i
  | succ n ih =>
      intro fA fA' fB fB' rA rA' rB rB' hdiff
      have hout := weightedStreamBobAction_out pA pB F n
      have hAliceHeadZero
          (observed : Record) (hne : (rA 0).2 ≠ (rA' 0).2)
          (tailA tailA' : Fin n → Bit) (xB xB' : Fin (n + 1) → Bit) :
          ((weightedStreamAliceAction pA F n).liftedOperation observed rho)
              ((MultipartiteSystem.pairEquiv _).symm
                (((fA, rA 0), tailA), (fB, xB)))
              ((MultipartiteSystem.pairEquiv _).symm
                (((fA', rA' 0), tailA'), (fB', xB'))) = 0 := by
        rw [weightedStreamAliceAction_liftedOperation_apply]
        exact weightedStreamStep_operation_newRecordDiagonal
          pA F n observed _ fA fA' (rA 0) (rA' 0) tailA tailA'
            (fun h => hne (congrArg Prod.snd h))
      have hBobHeadZero
          (observedA observedB : Record) (hne : (rB 0).2 ≠ (rB' 0).2)
          (tailA tailA' tailB tailB' : Fin n → Bit) :
          ((weightedStreamBobAction pA pB F n).liftedOperation observedB
            ((weightedStreamAliceAction pA F n).liftedOperation observedA rho))
              ((MultipartiteSystem.pairEquiv _).symm
                (((fA, rA 0), tailA), ((fB, rB 0), tailB)))
              ((MultipartiteSystem.pairEquiv _).symm
                (((fA', rA' 0), tailA'), ((fB', rB' 0), tailB'))) = 0 := by
        rw [weightedStreamBobAction_liftedOperation_apply]
        exact weightedStreamStep_operation_newRecordDiagonal
          pB F n observedB _ fB fB' (rB 0) (rB' 0) tailB tailB'
            (fun h => hne (congrArg Prod.snd h))
      have hBobAfterAliceHeadZero
          (observedA observedB : Record) (hne : (rA 0).2 ≠ (rA' 0).2)
          (tailA tailA' tailB tailB' : Fin n → Bit) :
          ((weightedStreamBobAction pA pB F n).liftedOperation observedB
            ((weightedStreamAliceAction pA F n).liftedOperation observedA rho))
              ((MultipartiteSystem.pairEquiv _).symm
                (((fA, rA 0), tailA), ((fB, rB 0), tailB)))
              ((MultipartiteSystem.pairEquiv _).symm
                (((fA', rA' 0), tailA'), ((fB', rB' 0), tailB'))) = 0 := by
        rw [weightedStreamBobAction_liftedOperation_apply, weightedStreamStep_operation_apply]
        have hlocal :
            ((((weightedStreamAliceAction pA F n).liftedOperation observedA rho).submatrix
              (fun x => (MultipartiteSystem.pairEquiv _).symm
                (((fA, rA 0), tailA), x))
              (fun x => (MultipartiteSystem.pairEquiv _).symm
                (((fA', rA' 0), tailA'), x))).submatrix
                (fun j => (fB, Fin.cons j tailB))
                (fun j => (fB', Fin.cons j tailB'))) = 0 := by
          ext j k
          exact hAliceHeadZero observedA hne tailA tailA'
            (Fin.cons j tailB) (Fin.cons k tailB')
        have h :=
          congrArg (fun M => (weightedMeasureAndRecord pB).operation observedB M (rB 0) (rB' 0))
            hlocal
        simp only [map_zero, Matrix.zero_apply] at h
        exact h
      change ((weightedMeasurementScheduleAux pA pB F (n + 1)).denote rho)
        ((weightedScheduleOutputEquiv F (n + 1)).symm
          ((fA, rA), (fB, rB)))
        ((weightedScheduleOutputEquiv F (n + 1)).symm
          ((fA', rA'), (fB', rB'))) = 0
      rw [weightedMeasurementScheduleAux_succ,
        Program.denote_priv_eq_sum_liftedOperation]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro observedA _
      rw [Program.denote_priv_eq_sum_liftedOperation]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro observedB _
      let rhoAB : Op (weightedStreamBobAction pA pB F n).out.total :=
        (weightedStreamBobAction pA pB F n).liftedOperation observedB
          ((weightedStreamAliceAction pA F n).liftedOperation observedA rho)
      change (cast (congrArg (fun R => Program R
        (.leaf (weightedStreamSystem (finishAcc (F × StoredRecord) n) 0))) hout.symm)
          (weightedMeasurementScheduleAux pA pB (F × StoredRecord) n)).denote _ _ _ = _
      refine (Program.denote_cast_apply hout rfl
        (weightedMeasurementScheduleAux pA pB (F × StoredRecord) n)
        rhoAB
        ((weightedScheduleOutputEquiv F (n + 1)).symm ((fA, rA), (fB, rB)))
        ((weightedScheduleOutputEquiv F (n + 1)).symm ((fA', rA'), (fB', rB')))).trans ?_
      let sigma : Op (weightedStreamSystem (F × StoredRecord) n).total := rhoAB.submatrix
          (Equiv.cast (congrArg MultipartiteSystem.total hout)).symm
          (Equiv.cast (congrArg MultipartiteSystem.total hout)).symm
      by_cases hA0 : (rA 0).2 ≠ (rA' 0).2
      · have hrec := weightedMeasurementScheduleAux_preserves_accumulator_block_zero
          pA pB (F × StoredRecord) n sigma
          (fA, rA 0) (fA', rA' 0) (fB, rB 0) (fB', rB' 0)
          (fun xA xA' xB xB' => by
            exact (congrArg₂ rhoAB
              (weightedStreamBobAction_out_cast_pairEquiv_symm pA pB F n
                ((fA, rA 0), xA) ((fB, rB 0), xB))
              (weightedStreamBobAction_out_cast_pairEquiv_symm pA pB F n
                ((fA', rA' 0), xA') ((fB', rB' 0), xB'))).trans
              (hBobAfterAliceHeadZero observedA observedB hA0 xA xA' xB xB'))
          (Fin.tail rA) (Fin.tail rA') (Fin.tail rB) (Fin.tail rB')
        exact hrec
      · by_cases hB0 : (rB 0).2 ≠ (rB' 0).2
        · have hrec := weightedMeasurementScheduleAux_preserves_accumulator_block_zero
            pA pB (F × StoredRecord) n sigma
            (fA, rA 0) (fA', rA' 0) (fB, rB 0) (fB', rB' 0)
            (fun xA xA' xB xB' => by
              exact (congrArg₂ rhoAB
                (weightedStreamBobAction_out_cast_pairEquiv_symm pA pB F n
                  ((fA, rA 0), xA) ((fB, rB 0), xB))
                (weightedStreamBobAction_out_cast_pairEquiv_symm pA pB F n
                  ((fA', rA' 0), xA') ((fB', rB' 0), xB'))).trans
                (hBobHeadZero observedA observedB hB0 xA xA' xB xB'))
            (Fin.tail rA) (Fin.tail rA') (Fin.tail rB) (Fin.tail rB')
          exact hrec
        · have hheadA : rA 0 = rA' 0 := by
            apply Prod.ext
            · exact Subsingleton.elim _ _
            · exact not_ne_iff.mp hA0
          have hheadB : rB 0 = rB' 0 := by
            apply Prod.ext
            · exact Subsingleton.elim _ _
            · exact not_ne_iff.mp hB0
          have htail : Fin.tail rA ≠ Fin.tail rA' ∨
              Fin.tail rB ≠ Fin.tail rB' := by
            rcases hdiff with hA | hB
            · left
              intro ht
              apply hA
              rw [← Fin.cons_self_tail rA, ← Fin.cons_self_tail rA', hheadA, ht]
            · right
              intro ht
              apply hB
              rw [← Fin.cons_self_tail rB, ← Fin.cons_self_tail rB', hheadB, ht]
          have hrec := ih (F := F × StoredRecord) (rho := sigma)
            (fA, rA 0) (fA', rA' 0) (fB, rB 0) (fB', rB' 0)
            (Fin.tail rA) (Fin.tail rA') (Fin.tail rB) (Fin.tail rB') htail
          exact hrec

/-- The physical Unit-accumulator schedule outputs Alice and Bob chronological record vectors
that are jointly block diagonal.

This holds for every complex input operator and arbitrary separate fixed basis laws `pA,pB`,
including `N = 0` and degenerate PMFs. -/
theorem weightedMeasurementSchedule_recordsDiagonal
    (pA pB : PMF Basis) (N : ℕ)
    (rho : Op (weightedStreamSystem Unit N).total) :
    ScheduleRecordsDiagonal Unit N
      ((weightedMeasurementSchedule pA pB N).denote rho) := by
  simpa [weightedMeasurementSchedule] using
    weightedMeasurementScheduleAux_recordsDiagonal pA pB Unit N rho

end QKD.BB84.Measurement
