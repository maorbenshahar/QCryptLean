import QCryptLean.QKD.BB84.Measurement.ClassicalityReference
import QCryptLean.LOCC.Typed.Program.Denotation
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity

/-!
# Streaming witness for one destructive BB84 measurement round

This module exposes the existing Alice-then-Bob one-round program as an instrument on the arriving
pair tensored with an explicit untouched spectator.  The spectator contains the two accumulators
and both undelivered stream tails; its row and column coordinates remain independent.

The sequential local operation follows the finite LOCC instrument model of Chitambar et al.,
arXiv:1210.4583, Section 2.  Renner, arXiv:quant-ph/0512258v2, source lines 673--736, and Pfister et
al., arXiv:1506.07502v3, Sections IV--V motivate destructive measurement before later public
processing.  The coordinate identities below are implementation-specific and are not attributed
to those papers.  This module states a measurement-prefix witness, not a security theorem or a
claim that the later classical tail has already been analyzed.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement.Streaming
open TypedLOCC

open TypedLOCC.TwoParty

attribute [local instance] storedRecordVectorDecidableEq

/-- The untouched part of one online round: both accumulators and both undelivered tails. -/
abbrev roundSpectator (F : Type) (n : ℕ) :=
  (F × F) × ((Fin n → Bit) × (Fin n → Bit))

/-- Reassociate two locally split stream heads into the physical arriving pair and one spectator. -/
def streamRoundInputRegroup (F : Type) (n : ℕ) :
    ((Bit × streamRegister F n) × (Bit × streamRegister F n)) ≃
      inputSystem.total × roundSpectator F n where
  toFun q :=
    ((TwoParty.pairEquiv Bit Bit).symm (q.1.1, q.2.1),
      ((q.1.2.1, q.2.2.1), (q.1.2.2, q.2.2.2)))
  invFun q :=
    let heads := TwoParty.pairEquiv Bit Bit q.1
    ((heads.1, (q.2.1.1, q.2.2.1)),
      (heads.2, (q.2.1.2, q.2.2.2)))
  left_inv q := by
    rcases q with ⟨⟨xA, fA, tailA⟩, ⟨xB, fB, tailB⟩⟩
    rfl
  right_inv q := by
    rcases q with ⟨active, ⟨⟨fA, fB⟩, ⟨tailA, tailB⟩⟩⟩
    apply Prod.ext
    · exact (TwoParty.pairEquiv Bit Bit).symm_apply_apply active
    · rfl

/-- Reassociate two newly recorded local outputs into the physical one-round output and the same
spectator. -/
def streamRoundOutputRegroup (F : Type) (n : ℕ) :
    ((StoredRecord × streamRegister F n) ×
      (StoredRecord × streamRegister F n)) ≃
      (Boundary.leaf outputSystem).space × roundSpectator F n where
  toFun q :=
    ((Boundary.leafSpaceEquiv outputSystem).symm
        ((TwoParty.pairEquiv StoredRecord StoredRecord).symm (q.1.1, q.2.1)),
      ((q.1.2.1, q.2.2.1), (q.1.2.2, q.2.2.2)))
  invFun q :=
    let records := TwoParty.pairEquiv StoredRecord StoredRecord
      (Boundary.leafSpaceEquiv outputSystem q.1)
    ((records.1, (q.2.1.1, q.2.2.1)),
      (records.2, (q.2.1.2, q.2.2.2)))
  left_inv q := by
    rcases q with ⟨⟨rA, fA, tailA⟩, ⟨rB, fB, tailB⟩⟩
    rfl
  right_inv q := by
    rcases q with ⟨active, ⟨⟨fA, fB⟩, ⟨tailA, tailB⟩⟩⟩
    apply Prod.ext
    · simp
    · rfl

/-- Split the physical two-party stream input into the arriving qubit pair and the untouched
accumulator/tail spectator. -/
def streamRoundInputSplit (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (weightedStreamSystem F (n + 1)).total ≃
      inputSystem.total × roundSpectator F n :=
  (TwoParty.pairEquiv (streamRegister F (n + 1))
      (streamRegister F (n + 1))).trans
    ((Equiv.prodCongr (streamInputSplit F n) (streamInputSplit F n)).trans
      (streamRoundInputRegroup F n))

/-- Split the physical two-party stream output into the new record pair and the unchanged
accumulator/tail spectator. -/
def streamRoundOutputSplit (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Boundary.leaf (weightedStreamSystem (F × StoredRecord) n)).space ≃
      (Boundary.leaf outputSystem).space × roundSpectator F n :=
  (Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n)).trans
    ((TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
      (streamRegister (F × StoredRecord) n)).trans
      ((Equiv.prodCongr (streamOutputSplit F n) (streamOutputSplit F n)).trans
        (streamRoundOutputRegroup F n)))

/-- Forward input coordinates expose the two stream heads and preserve both accumulator/tail
coordinates in Alice/Bob order. -/
@[simp] theorem streamRoundInputSplit_apply (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ)
    (fA fB : F) (xA xB : Fin (n + 1) → Bit) :
    streamRoundInputSplit F n
        ((TwoParty.pairEquiv (streamRegister F (n + 1))
          (streamRegister F (n + 1))).symm ((fA, xA), (fB, xB))) =
      ((TwoParty.pairEquiv Bit Bit).symm (xA 0, xB 0),
        ((fA, fB), (Fin.tail xA, Fin.tail xB))) := by
  rfl

/-- Inverse input coordinates rebuild each physical stream with `Fin.cons`. -/
@[simp] theorem streamRoundInputSplit_symm_apply (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ)
    (active : inputSystem.total) (fA fB : F)
    (tailA tailB : Fin n → Bit) :
    (streamRoundInputSplit F n).symm
        (active, ((fA, fB), (tailA, tailB))) =
      (TwoParty.pairEquiv (streamRegister F (n + 1))
        (streamRegister F (n + 1))).symm
        ((fA, Fin.cons (TwoParty.pairEquiv Bit Bit active).1 tailA),
          (fB, Fin.cons (TwoParty.pairEquiv Bit Bit active).2 tailB)) := by
  rfl

/-- Forward output coordinates expose the two new records and preserve both accumulator/tail
coordinates in Alice/Bob order. -/
@[simp] theorem streamRoundOutputSplit_apply (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ)
    (fA fB : F) (rA rB : StoredRecord)
    (tailA tailB : Fin n → Bit) :
    streamRoundOutputSplit F n
        ((Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n)).symm
          ((TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
            (streamRegister (F × StoredRecord) n)).symm
              (((fA, rA), tailA), ((fB, rB), tailB)))) =
      ((Boundary.leafSpaceEquiv outputSystem).symm
          ((TwoParty.pairEquiv StoredRecord StoredRecord).symm (rA, rB)),
        ((fA, fB), (tailA, tailB))) := by
  rfl

/-- Inverse output coordinates rebuild the two stored-record accumulators without changing either
tail. -/
@[simp] theorem streamRoundOutputSplit_symm_apply (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ)
    (active : (Boundary.leaf outputSystem).space) (fA fB : F)
    (tailA tailB : Fin n → Bit) :
    (streamRoundOutputSplit F n).symm
        (active, ((fA, fB), (tailA, tailB))) =
      (Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n)).symm
        ((TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
          (streamRegister (F × StoredRecord) n)).symm
          (((fA, (TwoParty.pairEquiv StoredRecord StoredRecord
              (Boundary.leafSpaceEquiv outputSystem active)).1), tailA),
            ((fB, (TwoParty.pairEquiv StoredRecord StoredRecord
              (Boundary.leafSpaceEquiv outputSystem active)).2), tailB))) := by
  rfl

/-- The actual one-round private program at a stream head: Alice measures first, then Bob, then
the remaining stream is exposed at the next leaf. -/
def weightedStreamRoundProgram (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    Program (weightedStreamSystem F (n + 1))
      (.leaf (weightedStreamSystem (F × StoredRecord) n)) :=
  cast (by simp only [weightedStreamBobAction_out])
    ((weightedStreamAliceAction pA F n).then (weightedStreamBobAction pA pB F n).run)

/-- The actual Alice-then-Bob round instrument acting only on the arriving pair, reindexed onto
the full accumulator and remaining-stream registers. -/
noncomputable def onlineWeightedStreamRound (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    Instrument (weightedStreamSystem F (n + 1)).total
      (Boundary.leaf (weightedStreamSystem (F × StoredRecord) n)).space Unit :=
  Instrument.onFactor (streamRoundInputSplit F n) (streamRoundOutputSplit F n)
    (weightedSingleQubitRoundProgram pA pB).toInstrument

/-- Entrywise arbitrary-operator identity for one arriving pair and independent spectator row and
column coordinates.  This is the explicit `K ⊗ 1` implementation identity specialized to the
actual Alice-then-Bob BB84 round. -/
theorem onlineWeightedStreamRound_operation_apply (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ)
    (rho : Op (weightedStreamSystem F (n + 1)).total)
    (q q' : (Boundary.leaf (weightedStreamSystem (F × StoredRecord) n)).space) :
    ((onlineWeightedStreamRound pA pB F n).operation () rho) q q' =
      ((weightedSingleQubitRoundProgram pA pB).toInstrument.operation ()
        (rho.submatrix
          (fun a => (streamRoundInputSplit F n).symm
            (a, (streamRoundOutputSplit F n q).2))
          (fun a => (streamRoundInputSplit F n).symm
            (a, (streamRoundOutputSplit F n q').2))))
        (streamRoundOutputSplit F n q).1
        (streamRoundOutputSplit F n q').1 := by
  rw [onlineWeightedStreamRound, Instrument.onFactor_operation_apply]

/-- The denotation of the existing stream-head program equals the online arriving-pair instrument
channel for all fixed local PMFs, including biased and zero-support laws. -/
theorem weightedStreamRoundProgram_denote_eq_online
    (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (weightedStreamRoundProgram pA pB F n).denote =
      (onlineWeightedStreamRound pA pB F n).channel := by
  have hstream := weightedStreamBobAction_out pA pB F n
  have hround : (weightedMeasureBob pA pB).out = outputSystem := by
    simp only [weightedMeasureBob, weightedMeasureAlice, weightedMeasureAliceWithSpectator,
      PrivateAction.out_ofInstrument, inputSystem, TwoParty.set_alice, TwoParty.set_bob]
  apply LinearMap.ext
  intro rho
  ext q q'
  simp only [Instrument.channel, Fintype.sum_unique]
  rw [onlineWeightedStreamRound_operation_apply]
  have hactive :
      (weightedSingleQubitRoundProgram pA pB).toInstrument.operation () =
        (weightedSingleQubitRoundProgram pA pB).denote := by
    unfold Program.denote Instrument.channel
    simp
  rw [hactive]
  change ((weightedStreamRoundProgram pA pB F n).denote rho) q q' =
    ((weightedSingleQubitRoundProgram pA pB).denote
      (rho.submatrix
        (fun a => (streamRoundInputSplit F n).symm
          (a, (streamRoundOutputSplit F n q).2))
        (fun a => (streamRoundInputSplit F n).symm
          (a, (streamRoundOutputSplit F n q').2))))
      (streamRoundOutputSplit F n q).1
      (streamRoundOutputSplit F n q').1
  unfold weightedStreamRoundProgram weightedSingleQubitRoundProgram
  rw [Program.denote_cast_apply rfl (congrArg Boundary.leaf hstream.symm),
    Program.denote_cast_apply rfl (congrArg Boundary.leaf hround.symm)]
  simp only [Equiv.cast_refl, Matrix.reindex_refl_refl]
  unfold PrivateAction.then PrivateAction.run
  rw [Program.denote_priv_eq_sum_liftedOperation
    (A := weightedStreamAliceAction pA F n)]
  rw [Program.denote_priv_eq_sum_liftedOperation
    (A := weightedMeasureAlice pA)]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro observedA _
  unfold PrivateAction.then
  rw [Program.denote_priv_eq_sum_liftedOperation
    (A := weightedStreamBobAction pA pB F n)]
  rw [Program.denote_priv_eq_sum_liftedOperation
    (A := weightedMeasureBob pA pB)]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro observedB _
  simp only [Program.denote_done, LinearEquiv.coe_coe,
    Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.submatrix_apply]
  generalize hqraw :
      (TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
        (streamRegister (F × StoredRecord) n))
        (Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n) q) =
      outq
  rcases outq with
    ⟨⟨⟨fA, rA⟩, tailA⟩, ⟨⟨fB, rB⟩, tailB⟩⟩
  generalize hqraw' :
      (TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
        (streamRegister (F × StoredRecord) n))
        (Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n) q') =
      outq'
  rcases outq' with
    ⟨⟨⟨fA', rA'⟩, tailA'⟩, ⟨⟨fB', rB'⟩, tailB'⟩⟩
  have hleafq :
      Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n) q =
        (TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
          (streamRegister (F × StoredRecord) n)).symm
          (((fA, rA), tailA), ((fB, rB), tailB)) := by
    apply (TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
      (streamRegister (F × StoredRecord) n)).injective
    simpa using hqraw
  have hleafq' :
      Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n) q' =
        (TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
          (streamRegister (F × StoredRecord) n)).symm
          (((fA', rA'), tailA'), ((fB', rB'), tailB')) := by
    apply (TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
      (streamRegister (F × StoredRecord) n)).injective
    simpa using hqraw'
  have hq : q =
      (Boundary.leafSpaceEquiv
        (weightedStreamSystem (F × StoredRecord) n)).symm
        ((TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
          (streamRegister (F × StoredRecord) n)).symm
          (((fA, rA), tailA), ((fB, rB), tailB))) := by
    apply (Boundary.leafSpaceEquiv
      (weightedStreamSystem (F × StoredRecord) n)).injective
    simpa using hleafq
  have hq' : q' =
      (Boundary.leafSpaceEquiv
        (weightedStreamSystem (F × StoredRecord) n)).symm
        ((TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
          (streamRegister (F × StoredRecord) n)).symm
          (((fA', rA'), tailA'), ((fB', rB'), tailB'))) := by
    apply (Boundary.leafSpaceEquiv
      (weightedStreamSystem (F × StoredRecord) n)).injective
    simpa using hleafq'
  rw [hq, hq']
  simp only [streamRoundOutputSplit_apply]
  simp only [Equiv.cast_apply, Boundary.leafSpaceEquiv_cast hstream.symm,
    Boundary.leafSpaceEquiv_cast hround.symm, Equiv.apply_symm_apply]
  have hroundCoord (a b : StoredRecord) :
      cast (congrArg MultipartiteSystem.total hround.symm)
          ((TwoParty.pairEquiv _ _).symm (a, b)) =
        (weightedMeasureBob pA pB).out.pairEquiv.symm (a, b) := by
    change cast (congrArg MultipartiteSystem.total hround.symm)
      (outputSystem.pairEquiv.symm (a, b)) = _
    rw [MultipartiteSystem.cast_pairEquiv_symm hround.symm]
    rfl
  simp only [weightedStreamBobAction_out_cast_pairEquiv_symm pA pB F n]
  rw [hroundCoord, hroundCoord]
  rw [weightedStreamBobAction_liftedOperation_apply, weightedStreamStep_operation_apply]
  change _ = ((weightedMeasureAndRecord pB).liftAt (weightedMeasureAlice pA).out .bob).operation
    observedB _
      (((weightedMeasureAlice pA).out.set .bob StoredRecord).pairEquiv.symm (rA, rB))
      (((weightedMeasureAlice pA).out.set .bob StoredRecord).pairEquiv.symm (rA', rB'))
  rw [Instrument.liftAt_bob_operation_apply]
  apply congrArg (fun sigma : Op Bit =>
    ((weightedMeasureAndRecord pB).operation observedB sigma) rB rB')
  funext j k
  simp only [Matrix.submatrix_apply]
  rw [weightedStreamAliceAction_liftedOperation_apply, weightedStreamStep_operation_apply]
  change _ = ((weightedMeasureAndRecord pA).liftAt inputSystem .alice).operation observedA _
    ((inputSystem.set .alice StoredRecord).pairEquiv.symm (rA, j))
    ((inputSystem.set .alice StoredRecord).pairEquiv.symm (rA', k))
  rw [Instrument.liftAt_alice_operation_apply]
  apply congrArg (fun sigma : Op Bit =>
    ((weightedMeasureAndRecord pA).operation observedA sigma) rA rA')
  funext l m
  simp only [Matrix.submatrix_apply]
  rw [streamRoundInputSplit_symm_apply, streamRoundInputSplit_symm_apply]
  rfl

/-- Nonzero input dimension derived from the explicit inhabited stream multipartite system. -/
def streamRoundInputCardNeZero (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    NeZero (Fintype.card (weightedStreamSystem F (n + 1)).total) :=
  ⟨Fintype.card_ne_zero⟩

/-- Nonzero output dimension derived from the explicit inhabited next-round leaf. -/
def streamRoundOutputCardNeZero (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ) :
    NeZero (Fintype.card
      (Boundary.leaf (weightedStreamSystem (F × StoredRecord) n)).space) :=
  by
    letI : Nonempty
        (Boundary.leaf (weightedStreamSystem (F × StoredRecord) n)).space :=
      Nonempty.map
        (Boundary.leafSpaceEquiv
          (weightedStreamSystem (F × StoredRecord) n)).symm inferInstance
    exact ⟨Fintype.card_ne_zero⟩

attribute [local instance] streamRoundInputCardNeZero streamRoundOutputCardNeZero

/-- The one-round implementation identity remains exact after adjoining an arbitrary finite
reference.  The physical program has no reference parameter; this is the proof-side completely
bounded coordinate extension. -/
theorem weightedStreamRoundProgram_denote_eq_online_mapTensorId
    (pA pB : PMF Basis)
    (F : Type) [Nonempty F] [Fintype F] [DecidableEq F]
    (n k : ℕ) [NeZero k] :
    Quantum.Channels.mapTensorIdLinear (k := k)
      (coordinateLinear
        (Fintype.equivFin (weightedStreamSystem F (n + 1)).total)
        (Fintype.equivFin
          (Boundary.leaf (weightedStreamSystem (F × StoredRecord) n)).space)
        (weightedStreamRoundProgram pA pB F n).denote) =
    Quantum.Channels.mapTensorIdLinear (k := k)
      (coordinateLinear
        (Fintype.equivFin (weightedStreamSystem F (n + 1)).total)
        (Fintype.equivFin
          (Boundary.leaf (weightedStreamSystem (F × StoredRecord) n)).space)
        (onlineWeightedStreamRound pA pB F n).channel) := by
  rw [weightedStreamRoundProgram_denote_eq_online]

/-- The existing recursive schedule preserves a zero block between any fixed accumulator row and
column while processing all later stream heads. -/
def SchedulePreservesAccumulatorBlockZero
    (pA pB : PMF Basis) (F : Type)
    [Nonempty F] [Fintype F] [DecidableEq F] (N : ℕ) : Prop :=
  ∀ (rho : Op (weightedStreamSystem F N).total)
    (fA fA' fB fB' : F),
    (∀ (xA xA' xB xB' : Fin N → Bit),
      (reindexOp (weightedStreamPairEquiv F N) rho)
        ((fA, xA), (fB, xB)) ((fA', xA'), (fB', xB')) = 0) →
    ∀ (rA rA' rB rB' : Fin N → StoredRecord),
      (reindexOp (weightedScheduleOutputEquiv F N)
        ((weightedMeasurementScheduleAux pA pB F N).denote rho))
          ((fA, rA), (fB, rB)) ((fA', rA'), (fB', rB')) = 0

/-- Certificate that a concrete program begins with the actual destructive private schedule, that
each head step equals the online arriving-pair instrument, and that the accumulator zero-block
invariant holds at every remaining length.  The existential continuation begins only after all
`N` private rounds and contains no claim that its later actions are classical. -/
def StreamingMeasurementPrefix
    (pA pB : PMF Basis) (N : ℕ) {B : Boundary Party}
    (P : Program (weightedStreamSystem Unit N) B) : Prop :=
  ∃ continuation : Program (weightedStreamSystem (finishAcc Unit N) 0) B,
    P = (weightedMeasurementSchedule pA pB N).graft
      (fun _ => continuation) ∧
    (∀ (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ),
      (weightedStreamRoundProgram pA pB F n).denote =
        (onlineWeightedStreamRound pA pB F n).channel) ∧
    (∀ (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ),
      SchedulePreservesAccumulatorBlockZero pA pB F n)

end QKD.BB84.Measurement.Streaming
