import QCryptLean.QKD.Acceptance
import QCryptLean.QKD.BB84.Reduction.BasisErasure
import QCryptLean.QKD.BB84.Reduction.ClassicalTail
import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.Parameters

/-!
# Acceptance of the measure-first BB84 experiment

The complete measure-first program (`program`) measures, announces the basis
strings and one uniform matched-round ordering, and then branches on the announced control: a
control failing a quota ends the run in the key-free abort leaf, while a control meeting the quotas
erases both private basis strings and runs the real retained classical tail on the selected bits.
This module computes the acceptance weight, a linear functional on arbitrary input operators.
For a density operator this is the program's acceptance probability.

* `rawClassicalTailFlag` is the flag the real tail announces on raw registers `x` and seed pair
  `st` (`0` accepts), and `rawClassicalTail_acceptWeight_apply` says that the tail's acceptance
  weight on any input is the seed-averaged acceptance `rawClassicalTailAcceptFraction` of each raw
  diagonal entry.
* `selectedBitsToRawProgram_denote_diag` is the basis-erasure stage as a map of diagonals.
* `protocol_acceptProbability` is the resulting decomposition: the acceptance
  weight is the sum over the quota-feasible public controls `ω` and over the selected records
  of the tail's acceptance of the selected bits, weighted by the corresponding diagonal entry of the
  late-public-control stage.  Shortage controls contribute nothing; no control is conditioned.
* Two degenerate configurations never accept, whatever the input: an empty Z-test or X-test block,
  because the parameter-estimation test is fail-closed
  (`Parameters.acceptProbability_eq_zero_of_testBlock_empty`), and a batch shorter than the total
  quota, because no public control can meet it (`Parameters.acceptProbability_eq_zero_of_lt`).

Combined with an exact law for the late-public-control stage — for instance the product-source law
in the ProductInput module — this is the full acceptance probability of the
physical experiment.
-/

open scoped Matrix BigOperators

noncomputable section

namespace QKD.BB84
open TypedLOCC
open QKD.BB84
open QKD.BB84.Reduction

open TypedLOCC.TwoParty
open QKD.BB84.Measurement
open QKD.BB84.Sampling
open QKD.BB84.Engine

/-! ## The real retained classical tail -/

/-- **The accept flag of the real retained tail** on raw registers `x` with sampled seed pair `st`:
the flag Bob announces at `rawClassicalTailOutputPoint`, `0` accepting. -/
def rawClassicalTailFlag (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (x : (FinalStage.rawSystem n).total)
    (st : KeyHashSeedPairEV n ℓ ℓEV peSel) : Fin 2 :=
  let d := rawClassicalTailDataOf n m ℓ ℓEV peSel leakEC ec x st
  QKD.BB84.Model.acceptFlagOf n m ℓEV peSel xSel leakEC ec δ Q d.alicePE d.bobPE d.seedPair.2
    d.evTag d.syndrome (x .bob)

/-- **The seed-averaged acceptance of the real retained tail** at raw registers `x`: the fraction of
seed pairs at which the announced flag accepts. -/
def rawClassicalTailAcceptFraction (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool) (leakEC : ℕ)
    (ec : ECScheme n peSel leakEC) (δ Q : ℝ) (x : (FinalStage.rawSystem n).total) : ℝ :=
  (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ)⁻¹ *
    ∑ st, if rawClassicalTailFlag n m ℓ ℓEV peSel xSel leakEC ec δ Q x st = 0 then 1 else 0

/-- The tail's acceptance fraction is a number in `[0, 1]`. -/
theorem rawClassicalTailAcceptFraction_nonneg (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (x : (FinalStage.rawSystem n).total) :
    0 ≤ rawClassicalTailAcceptFraction n m ℓ ℓEV peSel xSel leakEC ec δ Q x := by
  unfold rawClassicalTailAcceptFraction
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => ?_)
  split_ifs <;> norm_num

/-- The tail's acceptance fraction is at most one. -/
theorem rawClassicalTailAcceptFraction_le_one (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (x : (FinalStage.rawSystem n).total) :
    rawClassicalTailAcceptFraction n m ℓ ℓEV peSel xSel leakEC ec δ Q x ≤ 1 := by
  unfold rawClassicalTailAcceptFraction
  have hcard : (0 : ℝ) < Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) := by
    exact_mod_cast Fintype.card_pos
  rw [inv_mul_le_iff₀ hcard, mul_one]
  calc
    _ ≤ ∑ _st : KeyHashSeedPairEV n ℓ ℓEV peSel, (1 : ℝ) :=
      Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
    _ = _ := by simp

/-- The decision recorded at the literal final-stage output point is the flag computed from the
announced data and Bob's raw register. -/
theorem rawClassicalTailFinalPoint_flag (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (d : ClassicalTailData n m ℓ ℓEV peSel leakEC) (x : (FinalStage.rawSystem n).total) :
    (rawClassicalTailFinalPoint n m ℓ ℓEV peSel xSel leakEC ec δ Q d x).1.1 =
      QKD.BB84.Model.acceptFlagOf n m ℓEV peSel xSel leakEC ec δ Q d.alicePE d.bobPE
        d.seedPair.2 d.evTag d.syndrome (x .bob) := by
  simp only [rawClassicalTailFinalPoint]
  split <;> rfl

/-- At the output point generated by raw registers `x` and seed pair `st`, the tail's output layout
has the disposition of the announced flag. -/
theorem rawClassicalTailOutputLayout_disposition_outputPoint (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (x : (FinalStage.rawSystem n).total) (st : KeyHashSeedPairEV n ℓ ℓEV peSel) :
    (rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).disposition
        (rawClassicalTailOutputPoint n m ℓ ℓEV peSel xSel leakEC ec δ Q x st).1 =
      FinalStage.disposition ℓ (rawClassicalTailFlag n m ℓ ℓEV peSel xSel leakEC ec δ Q x st) := by
  simp only [rawClassicalTailOutputPoint, Boundary.graftSpaceEquiv_symm_fst,
    rawClassicalTailOutputLayout, QKD.OutputLayout.graftFixedParties_disposition,
    FinalStage.outputLayout_disposition, rawClassicalTailFinalPoint_flag, rawClassicalTailFlag]

/-- **Acceptance of the real retained tail on any input.**  The tail dephases the raw registers and
pushes each raw diagonal entry to its output points with the uniform seed weight
(`rawClassicalTailProgram_output_apply`); the accepting output points of raw registers `x` are
those whose seed pair makes the announced flag accept. -/
theorem rawClassicalTail_acceptWeight_apply (n m ℓ ℓEV : ℕ) (peSel xSel : Fin n → Bool)
    (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (τ : Op (FinalStage.rawSystem n).total) :
    (rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout.acceptWeight
        ((rawClassicalTailProgram n m ℓ ℓEV peSel xSel leakEC ec δ Q).denote τ) =
      ∑ x, rawClassicalTailAcceptFraction n m ℓ ℓEV peSel xSel leakEC ec δ Q x * (τ x x).re := by
  classical
  have hdiag (q : (rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).space) :
      (rawClassicalTailProgram n m ℓ ℓEV peSel xSel leakEC ec δ Q).denote τ q q =
        ∑ y : (FinalStage.rawSystem n).total × KeyHashSeedPairEV n ℓ ℓEV peSel,
          if rawClassicalTailOutputPoint n m ℓ ℓEV peSel xSel leakEC ec δ Q y.1 y.2 = q then
            (((Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℝ)⁻¹ : ℝ) : ℂ) *
              τ y.1 y.1
          else 0 := by
    rw [rawClassicalTailProgram_output_apply, if_pos rfl, ← Fintype.sum_prod_type']
    push_cast
    rfl
  rw [BoundaryKeyLayout.acceptWeight, Boundary.exitWeight_eq_sum_of_diag _ _ _ _ _ hdiag,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rawClassicalTailAcceptFraction, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun st _ => ?_
  rw [QKD.OutputLayout.toBoundaryKeyLayout_disposition,
    rawClassicalTailOutputLayout_disposition_outputPoint, Complex.re_ofReal_mul]
  by_cases hflag : rawClassicalTailFlag n m ℓ ℓEV peSel xSel leakEC ec δ Q x st = 0
  · simp [hflag, FinalStage.disposition]
  · simp [hflag, FinalStage.disposition]

/-! ## The two kinds of late-public branch -/

/-- At the literal exit of a quota-feasible control, the late-public-control stage ends at the
selected-record multipartite system. -/
theorem lateSelectionBoundary_system_success (N nK mZ mX : ℕ) (ω : RawControl N)
    (h : HasQuotas nK mZ mX ω) :
    (lateSelectionBoundary N nK mZ mX).system (lateSelectionExit N nK mZ mX ω) =
      weightedSelectedRecordSystem N (nK + mZ + mX) := by
  rcases ω with ⟨a, b, order⟩
  change (lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩).system _ = _
  rw [lateSelectionLeaf_system, if_pos h]

/-- A selected-record point of a quota-feasible control is the literal exit of that control with
the selected records transported along `lateSelectionBoundary_system_success`. -/
theorem lateSelectionSuccessAt_eq (N nK mZ mX : ℕ) (ω : RawControl N)
    (h : HasQuotas nK mZ mX ω)
    (r : SelectedLocalRecord N (nK + mZ + mX) × SelectedLocalRecord N (nK + mZ + mX)) :
    lateSelectionSuccessAt N nK mZ mX ω h r =
      ⟨lateSelectionExit N nK mZ mX ω,
        (Equiv.cast (congrArg MultipartiteSystem.total (lateSelectionBoundary_system_success N nK mZ
          mX ω h))).symm
          ((TwoParty.pairEquiv _ _).symm r)⟩ := by
  have hSystem := lateSelectionBoundary_system_success N nK mZ mX ω h
  rcases ω with ⟨a, b, order⟩
  have hleaf : lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩ =
      .leaf (weightedSelectedRecordSystem N (nK + mZ + mX)) := by
    simp [lateSelectionLeaf, h]
  apply (Boundary.publicSpaceEquiv (fun a : Fin N → Basis =>
    .announce (Fin N → Basis) fun b =>
      .announce (Shuffle a b) fun order =>
        lateSelectionLeaf N nK mZ mX ⟨a, b, order⟩)).injective
  -- Peel the three public layers off both sides; what is left is the leaf point, a cast of
  -- `⟨(), pairEquiv.symm r⟩` along `hleaf.symm`, against the exit and transported record.
  simp only [lateSelectionSuccessAt, id_eq, Equiv.apply_symm_apply]
  simp only [Boundary.publicSpaceEquiv_apply, Equiv.symm_apply_eq, lateSelectionExit, id_eq,
    eq_mpr_eq_cast, Sigma.mk.injEq, heq_eq_eq, true_and]
  have castBoundarySnd {B C : Boundary Party} (hBC : B = C) (z : B.space) :
      (cast (congrArg Boundary.space hBC) z).2 ≍ z.2 := by
    cases hBC
    rfl
  have castSymm {α β : Type} (e : α = β) (x : β) : (Equiv.cast e).symm x ≍ x := by
    subst e
    rfl
  -- The leaf exit is unique; the records agree up to the two casts.
  exact Sigma.ext (Subsingleton.elim _ _)
    ((castBoundarySnd hleaf.symm _).trans (castSymm (congrArg MultipartiteSystem.total hSystem)
      _).symm)

/-- **A shortage branch never accepts.**  At the literal exit of a control failing a quota the run
ends in the key-free abort leaf, whatever operator reaches it. -/
theorem completeContinuationOutputLayout_acceptWeight_shortage (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ω : RawControl N) (h : ¬ HasQuotas nK mZ mX ω)
    (M : Op (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
      (lateSelectionExit N nK mZ mX ω)).space) :
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
      (lateSelectionExit N nK mZ mX ω)).toBoundaryKeyLayout.acceptWeight M = 0 := by
  have hquota : ¬ HasQuotas nK mZ mX
      (lateSelectionExitEquiv N nK mZ mX (lateSelectionExit N nK mZ mX ω)) := by
    rw [show lateSelectionExitEquiv N nK mZ mX (lateSelectionExit N nK mZ mX ω) = ω from
      (lateSelectionExitEquiv N nK mZ mX).apply_symm_apply ω]
    exact h
  apply BoundaryKeyLayout.acceptWeight_eq_zero_of_forall_abort
  intro e
  rw [QKD.OutputLayout.toBoundaryKeyLayout_disposition]
  unfold completeContinuationOutputLayout
  rw [dif_neg hquota]
  exact QKD.OutputLayout.transport_disposition_of_forall _ _ (fun _ => rfl) e

/-- **The successful continuation erases the bases and runs the real tail.**  Its acceptance weight
on any selected-record operator is the tail's acceptance of the erased diagonal. -/
theorem successfulCompleteContinuation_acceptWeight (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ)
    (σ : Op (weightedSelectedRecordSystem N (nK + mZ + mX)).total) :
    (rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout.acceptWeight
        ((successfulCompleteContinuation N nK mZ mX ℓ ℓEV leakEC ec δ Q).denote σ) =
      ∑ x, rawClassicalTailAcceptFraction (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q x *
        ((selectedBitsToRawProgram N (nK + mZ + mX)).denote σ ⟨(), x⟩ ⟨(), x⟩).re := by
  have hgraft := Program.exitWeight_graft_denote (selectedBitsToRawProgram N (nK + mZ + mX))
    (C := fun _ => rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (fun _ => rawClassicalTailProgram (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q)
    (fun e => (rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout.disposition e ≠ .abort) σ
  rw [Fintype.sum_unique] at hgraft
  rw [BoundaryKeyLayout.acceptWeight]
  refine hgraft.trans ?_
  have htail := rawClassicalTail_acceptWeight_apply (nK + mZ + mX) (mZ + mX) ℓ ℓEV
    (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q
    (BoundaryKeyLayout.leafBlock () ((selectedBitsToRawProgram N (nK + mZ + mX)).denote σ))
  rw [BoundaryKeyLayout.acceptWeight] at htail
  refine (Boundary.exitWeight_congr _ (fun _ => Iff.rfl) _).trans (htail.trans ?_)
  simp only [BoundaryKeyLayout.leafBlock_apply]

/-- **Acceptance of the complete experiment at a quota-feasible control.**  The continuation's
acceptance weight on the block of the late-public-control stage at the literal exit of `ω` is the
sum over selected records of the tail's acceptance of their selected bits, weighted by the
diagonal entry of the stage output at the corresponding selected-record point. -/
theorem completeContinuation_acceptWeight_success (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ)
    (ρ : Op (weightedStreamSystem Unit N).total) (ω : RawControl N) (h : HasQuotas nK mZ mX ω) :
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC
        (lateSelectionExit N nK mZ mX ω)).toBoundaryKeyLayout.acceptWeight
        ((completeContinuation N nK mZ mX ℓ ℓEV leakEC ec δ Q
          (lateSelectionExit N nK mZ mX ω)).denote
          (BoundaryKeyLayout.leafBlock (lateSelectionExit N nK mZ mX ω)
            ((weightedLatePublicSelectionProgram pA pB N nK mZ mX).denote ρ))) =
      ∑ r : SelectedLocalRecord N (nK + mZ + mX) × SelectedLocalRecord N (nK + mZ + mX),
        rawClassicalTailAcceptFraction (nK + mZ + mX) (mZ + mX) ℓ ℓEV
            (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q
            ((TwoParty.pairEquiv _ _).symm (selectedBitsToRaw r.1, selectedBitsToRaw r.2)) *
          ((weightedLatePublicSelectionProgram pA pB N nK mZ mX).denote ρ
            (lateSelectionSuccessAt N nK mZ mX ω h r)
            (lateSelectionSuccessAt N nK mZ mX ω h r)).re := by
  have hquota : HasQuotas nK mZ mX
      (lateSelectionExitEquiv N nK mZ mX (lateSelectionExit N nK mZ mX ω)) := by
    rw [show lateSelectionExitEquiv N nK mZ mX (lateSelectionExit N nK mZ mX ω) = ω from
      (lateSelectionExitEquiv N nK mZ mX).apply_symm_apply ω]
    exact h
  have hstart := lateSelectionBoundary_system_success N nK mZ mX ω h
  have hout := completeContinuationBoundary_success N nK mZ mX ℓ ℓEV leakEC ω h
  rw [completeContinuationOutputLayout_success N nK mZ mX ℓ ℓEV leakEC ω h]
  unfold completeContinuation
  rw [dif_pos hquota]
  dsimp only
  change (QKD.OutputLayout.transport hout.symm _).toBoundaryKeyLayout.acceptWeight
      ((cast (congrArg (fun R => Program R
          (completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC
            (lateSelectionExit N nK mZ mX ω))) hstart.symm)
        (cast (congrArg (fun B => Program (weightedSelectedRecordSystem N (nK + mZ + mX)) B)
            hout.symm)
          (successfulCompleteContinuation N nK mZ mX ℓ ℓEV leakEC ec δ Q))).denote _) = _
  rw [cast_cast, QKD.OutputLayout.acceptWeight_transport_denote_cast hstart hout.symm,
    successfulCompleteContinuation_acceptWeight]
  have hblock (r : SelectedLocalRecord N (nK + mZ + mX) × SelectedLocalRecord N (nK + mZ + mX)) :
      reindexOp (Equiv.cast (congrArg MultipartiteSystem.total hstart))
          (BoundaryKeyLayout.leafBlock (lateSelectionExit N nK mZ mX ω)
            ((weightedLatePublicSelectionProgram pA pB N nK mZ mX).denote ρ))
          ((TwoParty.pairEquiv _ _).symm r) ((TwoParty.pairEquiv _ _).symm r) =
        (weightedLatePublicSelectionProgram pA pB N nK mZ mX).denote ρ
          (lateSelectionSuccessAt N nK mZ mX ω h r) (lateSelectionSuccessAt N nK mZ mX ω h r) := by
    rw [lateSelectionSuccessAt_eq]
    simp only [reindexOp, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply,
      BoundaryKeyLayout.leafBlock_apply]
  simp_rw [selectedBitsToRawProgram_denote_diag]
  have hpair (x : (FinalStage.rawSystem (nK + mZ + mX)).total) (a b : Fin (2 ^ (nK + mZ + mX))) :
      (x .alice = a ∧ x .bob = b) ↔ x = (TwoParty.pairEquiv _ _).symm (a, b) := by
    constructor
    · rintro ⟨ha, hb⟩
      apply (TwoParty.pairEquiv _ _).injective
      simp [TwoParty.pairEquiv, ha, hb]
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp_rw [hpair, hblock, Complex.re_sum, apply_ite Complex.re, Complex.zero_re, Finset.mul_sum,
    mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun qB _ => ?_).trans (Fintype.sum_prod_type_right _).symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun qA _ => ?_
  rw [Finset.sum_ite_eq']
  simp

/-! ## The acceptance weight of the experiment -/

/-- **Acceptance weight of the measure-first experiment on any input operator.**

The acceptance weight is the sum, over the quota-feasible public controls `ω` and over the
selected records `r`, of the real tail's acceptance of the selected bits of `r` weighted by the
diagonal entry of the late-public-control stage output at the selected-record point of `r`.
Controls failing a quota contribute nothing.  No positivity, normalization or product structure of
the input is used; zero-mass controls appear with zero weight rather than being excluded.
For a density operator this weight is the acceptance probability. -/
theorem protocol_acceptProbability (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ)
    (ρ : Op (weightedStreamSystem Unit N).total) :
    (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).acceptProbability ρ =
      ∑ ω : RawControl N, if h : HasQuotas nK mZ mX ω then
        ∑ r : SelectedLocalRecord N (nK + mZ + mX) × SelectedLocalRecord N (nK + mZ + mX),
          rawClassicalTailAcceptFraction (nK + mZ + mX) (mZ + mX) ℓ ℓEV
              (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) leakEC ec δ Q
              ((TwoParty.pairEquiv _ _).symm (selectedBitsToRaw r.1, selectedBitsToRaw r.2)) *
            ((weightedLatePublicSelectionProgram pA pB N nK mZ mX).denote ρ
              (lateSelectionSuccessAt N nK mZ mX ω h r)
              (lateSelectionSuccessAt N nK mZ mX ω h r)).re
      else 0 := by
  have hgraft := QKD.OutputLayout.acceptWeight_graftFixedParties_denote
    (weightedLatePublicSelectionProgram pA pB N nK mZ mX)
    (completeContinuation N nK mZ mX ℓ ℓEV leakEC ec δ Q)
    (completeContinuationOutputLayout N nK mZ mX ℓ ℓEV leakEC) .alice .bob (by decide)
    (completeContinuationOutputLayout_alice N nK mZ mX ℓ ℓEV leakEC)
    (completeContinuationOutputLayout_bob N nK mZ mX ℓ ℓEV leakEC) ρ
  refine hgraft.trans ?_
  rw [← (lateSelectionExitEquiv N nK mZ mX).symm.sum_comp]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs with h
  · exact completeContinuation_acceptWeight_success pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q ρ ω h
  · exact completeContinuationOutputLayout_acceptWeight_shortage N nK mZ mX ℓ ℓEV leakEC ω h _

/-! ## Configurations that never accept -/

/-- **An empty test block makes the real tail reject every input.**  The parameter-estimation test
is fail-closed: with no Z-test round or no X-test round the announced flag is `1` at every raw
register and seed pair. -/
theorem rawClassicalTailAcceptFraction_eq_zero_of_testBlock_empty (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ)
    (h : bb84SiftedZTestSampleSize peSel xSel = 0 ∨ bb84SiftedXTestSampleSize peSel xSel = 0)
    (x : (FinalStage.rawSystem n).total) :
    rawClassicalTailAcceptFraction n m ℓ ℓEV peSel xSel leakEC ec δ Q x = 0 := by
  unfold rawClassicalTailAcceptFraction
  rw [Finset.sum_eq_zero, mul_zero]
  intro st _
  rw [if_neg]
  simp only [rawClassicalTailFlag, QKD.BB84.Model.acceptFlagOf, QKD.BB84.Model.peOKOfAnnounced]
  rcases h with h | h <;> simp [h]

/-- With an empty Z-test or X-test block the measure-first experiment never accepts, whatever its
input. -/
theorem protocol_acceptProbability_eq_zero_of_testBlock_empty (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ)
    (h : mZ = 0 ∨ mX = 0) (ρ : Op (weightedStreamSystem Unit N).total) :
    (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).acceptProbability ρ = 0 := by
  have hblock : bb84SiftedZTestSampleSize (@Sampling.packedPESel nK mZ mX)
        (@Sampling.packedXSel nK mZ mX) = 0 ∨
      bb84SiftedXTestSampleSize (@Sampling.packedPESel nK mZ mX)
        (@Sampling.packedXSel nK mZ mX) = 0 := by
    rwa [packedZTestSampleSize, packedXTestSampleSize]
  rw [protocol_acceptProbability]
  refine Finset.sum_eq_zero fun ω _ => ?_
  split_ifs
  · refine Finset.sum_eq_zero fun r _ => ?_
    rw [rawClassicalTailAcceptFraction_eq_zero_of_testBlock_empty _ _ _ _ _ _ _ _ _ _ hblock,
      zero_mul]
  · rfl

/-- A batch shorter than the total quota never accepts, whatever its input: no public control can
select `nK + mZ + mX` distinct rounds out of `N`. -/
theorem protocol_acceptProbability_eq_zero_of_lt (pA pB : PMF Basis)
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX) (@Sampling.packedPESel nK mZ mX) leakEC) (δ Q : ℝ)
    (hN : N < nK + mZ + mX) (ρ : Op (weightedStreamSystem Unit N).total) :
    (protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec δ Q).acceptProbability ρ = 0 := by
  rw [protocol_acceptProbability]
  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [dif_neg]
  intro h
  have hcard := Fintype.card_le_of_injective _ (selectedEmbedding ω h).injective
  simp only [Fintype.card_fin] at hcard
  omega

namespace Parameters

variable (p : Parameters)

/-- The configured experiment never accepts when one of its test blocks is empty. -/
theorem acceptProbability_eq_zero_of_testBlock_empty (h : p.zTests = 0 ∨ p.xTests = 0)
    (ρ : Op p.protocol.start.total) : p.protocol.acceptProbability ρ = 0 :=
  protocol_acceptProbability_eq_zero_of_testBlock_empty _ _ _ _ _ _ _ _ _ _ _ _ h ρ

/-- The configured experiment never accepts when it measures fewer rounds than it must sift. -/
theorem acceptProbability_eq_zero_of_lt (h : p.rounds < p.sifted)
    (ρ : Op p.protocol.start.total) : p.protocol.acceptProbability ρ = 0 :=
  protocol_acceptProbability_eq_zero_of_lt _ _ _ _ _ _ _ _ _ _ _ _ h ρ

end Parameters

end QKD.BB84
