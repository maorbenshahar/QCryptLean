import QCryptLean.QKD.BB84.Reduction.ClassicalTail
import QCryptLean.QKD.BB84.Reduction.RetainedExperiment
import QCryptLean.QKD.BB84.Program

/-!
# Reference blocks of the retained-analysis program

This module gives literal reference-block coordinates for the retained experiment: one uniformly
announced inner permutation, Alice's and Bob's private basis-dependent measurements, and the actual
raw classical tail.  The entry formula is an implementation-specific finite-program identity.

Christandl--König--Renner, arXiv:0809.3019, Theorem 1 and Lemma 1, and Renner,
arXiv:quant-ph/0512258v2, Section 6.5 motivate the later security use; they do not state this
coordinate formula.
-/

namespace QKD.BB84.Reduction
open TypedLOCC

open scoped BigOperators Matrix
open Quantum.Operators
open TypedLOCC QKD
open TypedLOCC.TwoParty
open QKD.BB84.Engine
open Measurement Sampling

noncomputable section

attribute [local instance] retainedAnalysisRoundDimNeZero
attribute [local instance] retainedAnalysisBlockDimNeZero
attribute [local instance] retainedAnalysisOutputDimNeZero

/-- One external-reference block, reindexed into the actual retained input multipartite system. -/
def retainedAnalysisProgramInputReferenceBlock {n k : ℕ}
    (W : Quantum.Operators.Op ((2 ^ n * 2 ^ n) * k)) (s t : Fin k) :
    TypedLOCC.Op (FinalStage.rawSystem n).total :=
  Matrix.reindex (retainedAnalysisBlockInputEquiv n).symm
    (retainedAnalysisBlockInputEquiv n).symm
    (Matrix.of fun i j =>
      W (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t)))

/-- The state the two private measurements read after the announced inner permutation.

Alice's and Bob's local sift/permutation operators act in sequence on their computed systems;
the final operator is reindexed into the retained raw-system coordinates. -/
noncomputable def retainedAnalysisSiftedState {n : ℕ}
    (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (rho : TypedLOCC.Op (FinalStage.rawSystem n).total) :
    TypedLOCC.Op (FinalStage.rawSystem n).total :=
  let h : (bobSiftUnitAnnouncement n peSel xSel pi).out () = FinalStage.rawSystem n := by
    change ((FinalStage.rawSystem n).set .alice (Fin (2 ^ n))).set .bob (Fin (2 ^ n)) = _
    rw [TwoParty.set_alice, TwoParty.set_bob]
  reindexOp (Equiv.cast (congrArg MultipartiteSystem.total h))
    (matrixConjLinear
      (localKrausLift ((alicePermutationAnnouncement n peSel xSel).out pi) .bob (Fin (2 ^ n))
        (QKD.BB84.Model.siftPermHalf n peSel xSel pi))
      (matrixConjLinear
        (localKrausLift (FinalStage.rawSystem n) .alice (Fin (2 ^ n))
          (QKD.BB84.Model.siftPermHalf n peSel xSel pi)) rho))

/-- Reference block after the local sift/permutation operators and both private computational
measurements, at the retained raw outcome `x`. -/
noncomputable def retainedAnalysisMeasuredReferenceBlock {n k : ℕ}
    (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (W : Quantum.Operators.Op ((2 ^ n * 2 ^ n) * k))
    (x : (FinalStage.rawSystem n).total) : Quantum.Operators.Op k :=
  Matrix.of fun s t =>
    retainedAnalysisSiftedState peSel xSel pi
      (retainedAnalysisProgramInputReferenceBlock W s t) x x

/-- **The channel of the retained-analysis program, entrywise.**

For an arbitrary operator `rho` on the raw input multipartite system, the output is diagonal in the
complete output space.  At a complete output point with announced permutation `pi` and raw-tail
output `w` (`retainedAnalysisOutputDataEquiv`), its weight is the uniform permutation weight times
the uniform seed weight, summed over the raw outcomes `x` and seed pairs `st` whose raw-tail output
point is `w`, of the diagonal entry at `x` of the sifted state `retainedAnalysisSiftedState` of
`pi`. -/
theorem retainedAnalysisProgram_denote_apply
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ)
    (rho : TypedLOCC.Op (FinalStage.rawSystem (nK + mZ + mX)).total)
    (q q' : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space) :
    let d := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q
    (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote rho q q' =
      if q = q' then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV
              (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint
                (nK + mZ + mX) (mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = d.2 then
              (Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹ *
                ((Fintype.card (KeyHashSeedPairEV
                    (nK + mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                  retainedAnalysisSiftedState
                    (@Sampling.packedPESel nK mZ mX)
                    (@Sampling.packedXSel nK mZ mX) d.1 rho x x)
            else 0
      else 0 := by
  classical
  dsimp only
  let n := nK + mZ + mX
  let peSel : Fin n → Bool := @Sampling.packedPESel nK mZ mX
  let xSel : Fin n → Bool := @Sampling.packedXSel nK mZ mX
  let tail := QKD.BB84.rawClassicalTailProgram n (mZ + mX) ell ellEV peSel xSel leakEC ec delta Q
  have hprogram :
      retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q =
        QKD.BB84.Reduction.permutationStage n peSel xSel
          (fun _ => QKD.BB84.Reduction.privateMeasurements n tail) := by
    have hp (pi : Equiv.Perm (Fin n)) : FinalStage.rawSystem n =
        (bobSiftUnitAnnouncement n peSel xSel pi).out () := by
      change FinalStage.rawSystem n =
        ((FinalStage.rawSystem n).set .alice (Fin (2 ^ n))).set .bob (Fin (2 ^ n))
      rw [TwoParty.set_alice, TwoParty.set_bob]
    have hm : FinalStage.rawSystem n = (bobPrivateMeasurement n).out := by
      simp only [bobPrivateMeasurement, alicePrivateMeasurement,
        PrivateAction.computationalMeasurement_out]
    unfold retainedAnalysisProgram retainedAnalysisPrefix permutationStage
    simp only [AnnouncedAction.then]
    change Program.announced _ _ = Program.announced _ _
    congr 1
    funext pi
    change Program.announced _ _ = Program.announced _ _
    congr 1
    funext u
    cases u
    change (cast (congrArg (fun R => Program R (.leaf (FinalStage.rawSystem n))) (hp pi))
      (privateMeasurements n Program.done)).graft (fun _ => tail) = _
    refine (Program.graft_castInput (hp pi) (privateMeasurements n Program.done)
      (fun _ => tail)).trans ?_
    apply congrArg (cast (congrArg (fun R => Program R
      (rawClassicalTailBoundary n (mZ + mX) ell ellEV peSel leakEC)) (hp pi)))
    unfold privateMeasurements
    apply congrArg (Program.priv (alicePrivateMeasurement n))
    apply congrArg (Program.priv (bobPrivateMeasurement n))
    exact Program.graft_castInput hm Program.done (fun _ => tail)
  have hPrivate {R : MultipartiteSystem Party} {B : Boundary Party}
      (A : PrivateAction R) (cont : Program A.out B) (sigma : TypedLOCC.Op R.total) :
      (A.then cont).denote sigma =
        cont.denote ((∑ o : A.Outcome, A.liftedOperation o) sigma) := by
    simp only [PrivateAction.then, Program.denote_priv_eq_sum_liftedOperation,
      LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  let measure (R : MultipartiteSystem Party) (i : Party) :=
    ∑ o : (PrivateAction.computationalMeasurement R i).Outcome,
      (PrivateAction.computationalMeasurement R i).liftedOperation o
  have hMeasureDiagonal (R : MultipartiteSystem Party) (i : Party)
      (sigma : TypedLOCC.Op R.total) (x : R.total) :
      measure R i sigma (cast (congrArg MultipartiteSystem.total (R.set_self i).symm) x)
        (cast (congrArg MultipartiteSystem.total (R.set_self i).symm) x) = sigma x x := by
    refine (congrArg₂ (fun u v => measure R i sigma u v)
      (R.splitAtSet_self_symm i x) (R.splitAtSet_self_symm i x)).symm.trans ?_
    have h := PrivateAction.computationalMeasurement_liftedChannel_apply R i sigma x x
    simp only [ite_true] at h
    exact h
  have hMeasurements (sigma : TypedLOCC.Op (FinalStage.rawSystem n).total)
      (a b : (QKD.BB84.rawClassicalTailBoundary n (mZ + mX) ell ellEV peSel leakEC).space) :
      (QKD.BB84.Reduction.privateMeasurements n tail).denote sigma a b =
        tail.denote sigma a b := by
    let ha := (FinalStage.rawSystem n).set_self .alice
    let hb := (alicePrivateMeasurement n).out.set_self .bob
    let hf : (bobPrivateMeasurement n).out = FinalStage.rawSystem n := hb.trans ha
    have hdiag (x : (FinalStage.rawSystem n).total) :
        (Matrix.reindex (Equiv.cast (congrArg MultipartiteSystem.total hf))
          (Equiv.cast (congrArg MultipartiteSystem.total hf))
          (measure (alicePrivateMeasurement n).out .bob
            (measure (FinalStage.rawSystem n) .alice sigma))) x x = sigma x x := by
      change (measure (alicePrivateMeasurement n).out .bob
        (measure (FinalStage.rawSystem n) .alice sigma))
        (cast (congrArg MultipartiteSystem.total hf).symm x)
        (cast (congrArg MultipartiteSystem.total hf).symm x) = _
      have hcoord : cast (congrArg MultipartiteSystem.total hf).symm x =
          cast (congrArg MultipartiteSystem.total hb).symm
            (cast (congrArg MultipartiteSystem.total ha).symm x) := by
        exact (cast_cast _ _ x).symm
      refine (congrArg₂ (fun u v => measure (alicePrivateMeasurement n).out .bob
        (measure (FinalStage.rawSystem n) .alice sigma) u v) hcoord hcoord).trans ?_
      exact (hMeasureDiagonal (alicePrivateMeasurement n).out .bob _ _).trans
        (hMeasureDiagonal (FinalStage.rawSystem n) .alice sigma x)
    dsimp only [QKD.BB84.Reduction.privateMeasurements]
    rw [hPrivate, hPrivate]
    rw [Program.denote_cast_apply hf rfl]
    simp only [Equiv.cast_refl, Equiv.refl_apply]
    dsimp only [tail]
    rw [rawClassicalTailProgram_output_apply, rawClassicalTailProgram_output_apply]
    dsimp only [measure, alicePrivateMeasurement, bobPrivateMeasurement] at hdiag
    dsimp only [alicePrivateMeasurement, bobPrivateMeasurement]
    apply if_congr Iff.rfl _ rfl
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro st _
    exact if_congr Iff.rfl (congrArg (fun z : ℂ => _ * z) (hdiag x)) rfl
  let KA (pi : Equiv.Perm (Fin n)) :=
    localKrausLift (FinalStage.rawSystem n) .alice (Fin (2 ^ n))
      (QKD.BB84.Model.siftPermHalf n peSel xSel pi)
  let KB (pi : Equiv.Perm (Fin n)) :=
    localKrausLift ((alicePermutationAnnouncement n peSel xSel).out pi) .bob (Fin (2 ^ n))
      (QKD.BB84.Model.siftPermHalf n peSel xSel pi)
  let hout (pi : Equiv.Perm (Fin n)) :
      (bobSiftUnitAnnouncement n peSel xSel pi).out () = FinalStage.rawSystem n := by
    change ((FinalStage.rawSystem n).set .alice (Fin (2 ^ n))).set .bob (Fin (2 ^ n)) = _
    rw [TwoParty.set_alice, TwoParty.set_bob]
  let weight : ℂ := (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹
  -- Alice's branch at the outcome `(pi, ())` read off her public announcement `pi` (stated at
  -- the outcome type of the announcement, as `denote_then_publicSpaceEquiv_symm_apply` reads it).
  have hAlice (pi : Equiv.Perm (Fin n)) (sigma : TypedLOCC.Op (FinalStage.rawSystem n).total) :
      (QKD.BB84.Reduction.alicePermutationAnnouncement n peSel xSel).liftedOperation
          (pi, ()) sigma =
        weight • matrixConjLinear (KA pi) sigma := by
    ext u v
    exact QKD.BB84.Reduction.alicePermutationAnnouncement_liftedOperation_apply
      n peSel xSel pi sigma u v
  -- Bob's unit announcement has a single outcome.
  have hBob (pi : Equiv.Perm (Fin n))
      (o : (QKD.BB84.Reduction.bobSiftUnitAnnouncement n peSel xSel pi).Outcome)
      (sigma : TypedLOCC.Op ((alicePermutationAnnouncement n peSel xSel).out pi).total) :
      (QKD.BB84.Reduction.bobSiftUnitAnnouncement n peSel xSel pi).liftedOperation o sigma =
        matrixConjLinear (KB pi) sigma := by
    ext u v
    exact QKD.BB84.Reduction.bobSiftUnitAnnouncement_liftedOperation_apply
      n peSel xSel pi sigma u v
  let B := QKD.BB84.rawClassicalTailBoundary n (mZ + mX) ell ellEV peSel leakEC
  let E := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
  let U := Boundary.publicSpaceEquiv (fun _ : Unit => B)
  let V := Boundary.publicSpaceEquiv
    (fun _ : Equiv.Perm (Fin n) => Boundary.announce Unit (fun _ => B))
  have hPoint (pi : Equiv.Perm (Fin n)) (a : B.space) :
      E.symm (pi, a) = V.symm ⟨pi, U.symm ⟨(), a⟩⟩ := by
    rfl
  have hSame (pi : Equiv.Perm (Fin n)) (a b : B.space) :
      (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote rho
          (E.symm (pi, a)) (E.symm (pi, b)) =
        weight * tail.denote (retainedAnalysisSiftedState peSel xSel pi rho) a b := by
    rw [hPoint, hPoint, hprogram]
    dsimp only [QKD.BB84.Reduction.permutationStage]
    -- Read Alice's announcement at `pi`, then Bob's unit announcement, then the measurements.
    refine (Program.denote_then_publicSpaceEquiv_symm_apply
      (alicePermutationAnnouncement n peSel xSel) (Equiv.prodUnique _ _) (fun _ => rfl)
      (fun _ => Boundary.announce Unit (fun _ => B)) _ rho (pi, ())
      (U.symm ⟨(), a⟩) (U.symm ⟨(), b⟩)).trans ?_
    refine (Program.denote_then_publicSpaceEquiv_symm_apply
      (bobSiftUnitAnnouncement n peSel xSel pi) (Equiv.refl Unit) (fun _ => rfl)
      (fun _ => B) _ _ () a b).trans ?_
    refine (Program.denote_cast_apply (hout pi) rfl _ _ _ _).trans ?_
    simp only [Equiv.cast_refl, Equiv.refl_apply]
    refine (hMeasurements _ a b).trans ?_
    let F (tau : TypedLOCC.Op ((bobSiftUnitAnnouncement n peSel xSel pi).out ()).total) :=
      tail.denote (Matrix.reindex (Equiv.cast (congrArg MultipartiteSystem.total (hout pi)))
        (Equiv.cast (congrArg MultipartiteSystem.total (hout pi))) tau) a b
    refine (congrArg F (hBob pi () _)).trans ?_
    refine (congrArg (fun tau => F (matrixConjLinear (KB pi) tau)) (hAlice pi rho)).trans ?_
    refine (congrArg (fun tau :
      TypedLOCC.Op ((bobSiftUnitAnnouncement n peSel xSel pi).out ()).total =>
      tail.denote (Matrix.reindex (Equiv.cast (congrArg MultipartiteSystem.total (hout pi)))
        (Equiv.cast (congrArg MultipartiteSystem.total (hout pi))) tau) a b)
      ((matrixConjLinear (KB pi)).map_smul weight _)).trans ?_
    change tail.denote (weight • retainedAnalysisSiftedState peSel xSel pi rho) a b = _
    exact congrFun (congrFun (tail.denote.map_smul weight _) a) b
  have hCross (pi pj : Equiv.Perm (Fin n)) (hpi : pi ≠ pj) (a b : B.space) :
      (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote rho
          (E.symm (pi, a)) (E.symm (pj, b)) = 0 := by
    rw [hPoint, hPoint, hprogram]
    exact Program.denote_public_block_zero _ rho hpi _ _ _ _
  have hData (pi : Equiv.Perm (Fin n)) (a : B.space) :
      retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
          (E.symm (pi, a)) = (pi, a) :=
    E.apply_symm_apply (pi, a)
  obtain ⟨⟨pi, a⟩, rfl⟩ := E.symm.surjective q
  obtain ⟨⟨pj, b⟩, rfl⟩ := E.symm.surjective q'
  simp only [hData]
  by_cases hpi : pi = pj
  · subst pj
    rw [hSame]
    by_cases hab : a = b
    · subst b
      rw [ite_eq_left rfl]
      dsimp only [tail]
      rw [rawClassicalTailProgram_output_apply, ite_eq_left rfl]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro st _
      split_ifs <;> first | rfl | exact mul_zero _
    · have hne : E.symm (pi, a) ≠ E.symm (pi, b) := by
        intro h
        exact hab (congrArg Prod.snd (E.symm.injective h))
      rw [ite_eq_right hne]
      dsimp only [tail]
      rw [rawClassicalTailProgram_output_apply, ite_eq_right hab, mul_zero]
  · have hne : E.symm (pi, a) ≠ E.symm (pj, b) := by
      intro h
      exact hpi (congrArg Prod.fst (E.symm.injective h))
    rw [ite_eq_right hne]
    exact hCross pi pj hpi a b

/-- Complete-output reference blocks of the actual retained-analysis program.

Every public coordinate is retained: `retainedAnalysisOutputDataEquiv` exposes the announced
permutation and the entire raw-tail output.  The tail point contains the PE transcript, hash and
verification seeds, tag, syndrome, final flag, ordered Alice/Bob keys, and the actual residual
coordinate.  The reference row and column are independent. -/
theorem retainedAnalysisProgram_reference_blocks
    (nK mZ mX ell ellEV leakEC k : ℕ) [NeZero k]
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ)
    (W : Quantum.Operators.Op
      ((2 ^ (nK + mZ + mX) * 2 ^ (nK + mZ + mX)) * k))
    (q q' : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space)
    (s t : Fin k) :
    let eOut := retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
    let d := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q
    Quantum.Channels.mapTensorId
        (coordinateLinear (retainedAnalysisBlockInputEquiv (nK + mZ + mX)) eOut
          (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote) W
        (finProdFinEquiv (eOut q, s)) (finProdFinEquiv (eOut q', t)) =
      if q = q' then
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV
              (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            if rawClassicalTailOutputPoint
                (nK + mZ + mX) (mZ + mX) ell ellEV
                (@Sampling.packedPESel nK mZ mX)
                (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q x st = d.2 then
              (Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹ *
                ((Fintype.card (KeyHashSeedPairEV
                    (nK + mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                  retainedAnalysisMeasuredReferenceBlock
                    (@Sampling.packedPESel nK mZ mX)
                    (@Sampling.packedXSel nK mZ mX) d.1 W x s t)
            else 0
      else 0 := by
  classical
  dsimp only
  let n := nK + mZ + mX
  let eIn := retainedAnalysisBlockInputEquiv n
  let eOut := retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
  let block : Quantum.Operators.Op (2 ^ n * 2 ^ n) := Matrix.of fun i j =>
    W (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))
  let rho : TypedLOCC.Op (FinalStage.rawSystem n).total :=
    retainedAnalysisProgramInputReferenceBlock W s t
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  simp only [Equiv.symm_apply_apply]
  have hblock : block = Matrix.reindex eIn eIn rho := by
    ext i j
    simp [block, rho, retainedAnalysisProgramInputReferenceBlock, eIn, n]
  change
    (coordinateLinear eIn eOut
      (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote)
        block (eOut q) (eOut q') = _
  rw [hblock, coordinateLinear_reindex_apply]
  exact retainedAnalysisProgram_denote_apply nK mZ mX ell ellEV leakEC ec delta Q rho q q'

/-- **The channel of the retained-analysis program as a classical mixture.**

The output is the sum, over the announced permutation `pi`, the raw outcome `x` and the seed pair
`st`, of the rank-one projector onto the complete output point `(pi, raw-tail output of x and st)`,
weighted by the uniform permutation and seed weights and the diagonal entry at `x` of the sifted
state of `pi`.  Arbitrary complex input operators. -/
theorem retainedAnalysisProgram_denote_eq_sum
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ)
    (rho : TypedLOCC.Op (FinalStage.rawSystem (nK + mZ + mX)).total) :
    (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote rho =
      ∑ pi : Equiv.Perm (Fin (nK + mZ + mX)),
        ∑ x : (FinalStage.rawSystem (nK + mZ + mX)).total,
          ∑ st : KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
              (@Sampling.packedPESel nK mZ mX),
            ((Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℂ)⁻¹ *
                ((Fintype.card (KeyHashSeedPairEV (nK + mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX)) : ℂ)⁻¹ *
                  retainedAnalysisSiftedState
                    (@Sampling.packedPESel nK mZ mX)
                    (@Sampling.packedXSel nK mZ mX) pi rho x x)) •
              Matrix.single
                ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
                  (pi, rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX)
                    leakEC ec delta Q x st))
                ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm
                  (pi, rawClassicalTailOutputPoint (nK + mZ + mX) (mZ + mX) ell ellEV
                    (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX)
                    leakEC ec delta Q x st)) (1 : ℂ) := by
  classical
  ext q q'
  rw [retainedAnalysisProgram_denote_apply]
  obtain ⟨⟨pi, a⟩, rfl⟩ :=
    (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm.surjective q
  rw [Equiv.apply_symm_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hqq : (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm (pi, a) = q'
  · subst hqq
    simp only [ite_true, Equiv.apply_eq_iff_eq, Prod.mk.injEq, and_self]
    rw [Finset.sum_eq_single pi]
    · simp only [true_and]
    · intro pj _ hpj
      exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun st _ => by simp [hpj]
    · intro h
      exact absurd (Finset.mem_univ pi) h
  · rw [ite_eq_right hqq]
    symm
    refine Finset.sum_eq_zero fun pj _ => Finset.sum_eq_zero fun x _ =>
      Finset.sum_eq_zero fun st _ => ?_
    rw [ite_eq_right]
    rintro ⟨⟨rfl, hb⟩, hq'⟩
    exact hqq (by rw [← hq', hb])

/-- **The two local sift-after-permutation operators, in Alice/Bob block coordinates.**

Read in the block coordinates `retainedAnalysisBlockInputEquiv`, the sifted state of `pi` is the
conjugation of the input by the two-party product `siftPermHalf ⊗ siftPermHalf`. -/
theorem reindex_retainedAnalysisSiftedState {n : ℕ}
    (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (sigma : Quantum.Operators.Op (2 ^ n * 2 ^ n)) :
    Matrix.reindex (retainedAnalysisBlockInputEquiv n) (retainedAnalysisBlockInputEquiv n)
        (retainedAnalysisSiftedState peSel xSel pi
          (Matrix.reindex (retainedAnalysisBlockInputEquiv n).symm
            (retainedAnalysisBlockInputEquiv n).symm sigma)) =
      Quantum.TensorProducts.Op.tensor (QKD.BB84.Model.siftPermHalf n peSel xSel pi)
          (QKD.BB84.Model.siftPermHalf n peSel xSel pi) * sigma *
        (Quantum.TensorProducts.Op.tensor (QKD.BB84.Model.siftPermHalf n peSel xSel pi)
          (QKD.BB84.Model.siftPermHalf n peSel xSel pi))ᴴ := by
  let e := retainedAnalysisBlockInputEquiv n
  let eA := ((alicePermutationAnnouncement n peSel xSel).out pi).pairEquiv.trans
    finProdFinEquiv
  let eB := ((bobSiftUnitAnnouncement n peSel xSel pi).out ()).pairEquiv.trans
    finProdFinEquiv
  let kappa := QKD.BB84.Model.siftPermHalf n peSel xSel pi
  let ka : Matrix ((alicePermutationAnnouncement n peSel xSel).out pi).total
      (FinalStage.rawSystem n).total ℂ :=
    localKrausLift (FinalStage.rawSystem n) .alice (Fin (2 ^ n)) kappa
  let kb := localKrausLift ((alicePermutationAnnouncement n peSel xSel).out pi)
    .bob (Fin (2 ^ n)) kappa
  have hliftA : Matrix.reindex eA e ka =
      Quantum.TensorProducts.Op.tensor kappa (1 : Quantum.Operators.Op (2 ^ n)) := by
    ext i j
    change localKrausLift (FinalStage.rawSystem n) .alice (Fin (2 ^ n)) kappa
      (((alicePermutationAnnouncement n peSel xSel).out pi).pairEquiv.symm
        (finProdFinEquiv.symm i))
      ((FinalStage.rawSystem n).pairEquiv.symm (finProdFinEquiv.symm j)) = _
    refine (localKrausLift_alice_apply (FinalStage.rawSystem n) kappa
      i.divNat i.modNat j.modNat j.divNat).trans ?_
    simp [Quantum.TensorProducts.Op.tensor, Matrix.reindex_apply, Matrix.one_apply]
    rfl
  have hliftB : Matrix.reindex eB eA kb =
      Quantum.TensorProducts.Op.tensor (1 : Quantum.Operators.Op (2 ^ n)) kappa := by
    ext i j
    change localKrausLift ((alicePermutationAnnouncement n peSel xSel).out pi)
      .bob (Fin (2 ^ n)) kappa
      (((bobSiftUnitAnnouncement n peSel xSel pi).out ()).pairEquiv.symm
        (finProdFinEquiv.symm i))
      (((alicePermutationAnnouncement n peSel xSel).out pi).pairEquiv.symm
        (finProdFinEquiv.symm j)) = _
    refine (localKrausLift_bob_apply ((alicePermutationAnnouncement n peSel xSel).out pi)
      kappa i.divNat j.divNat i.modNat j.modNat).trans ?_
    simp [Quantum.TensorProducts.Op.tensor, Matrix.reindex_apply, Matrix.one_apply]
    rfl
  have hprefix : Matrix.reindex eB e (kb * ka) =
      Quantum.TensorProducts.Op.tensor kappa kappa := by
    change (kb * ka).submatrix eB.symm e.symm = _
    rw [← Matrix.submatrix_mul_equiv kb ka eB.symm eA.symm e.symm]
    change Matrix.reindex eB eA kb * Matrix.reindex eA e ka = _
    rw [hliftB, hliftA, Quantum.TensorProducts.Op.tensor_mul]
    simp only [one_mul, mul_one]
  let hout : (bobSiftUnitAnnouncement n peSel xSel pi).out () = FinalStage.rawSystem n := by
    change ((FinalStage.rawSystem n).set .alice (Fin (2 ^ n))).set .bob (Fin (2 ^ n)) = _
    rw [TwoParty.set_alice, TwoParty.set_bob]
  have hcoord (i : Fin (2 ^ n * 2 ^ n)) :
      cast (congrArg MultipartiteSystem.total hout).symm (e.symm i) = eB.symm i := by
    change cast (congrArg MultipartiteSystem.total hout.symm)
      ((FinalStage.rawSystem n).pairEquiv.symm (finProdFinEquiv.symm i)) = _
    exact MultipartiteSystem.cast_pairEquiv_symm hout.symm (finProdFinEquiv.symm i)
  have htransport (tau : TypedLOCC.Op ((bobSiftUnitAnnouncement n peSel xSel pi).out ()).total) :
      Matrix.reindex e e (reindexOp (Equiv.cast (congrArg MultipartiteSystem.total hout)) tau) =
        Matrix.reindex eB eB tau := by
    ext i j
    change tau (cast (congrArg MultipartiteSystem.total hout).symm (e.symm i))
      (cast (congrArg MultipartiteSystem.total hout).symm (e.symm j)) = _
    rw [hcoord, hcoord]
    rfl
  refine (htransport (matrixConjLinear kb
    (matrixConjLinear ka (Matrix.reindex e.symm e.symm sigma)))).trans ?_
  change coordinateLinear e eB ((matrixConjLinear kb).comp (matrixConjLinear ka)) sigma = _
  rw [← matrixConjLinear_mul]
  refine (congrArg (fun F => F sigma) (coordinateMatrixConj_eq e eB (kb * ka))).trans ?_
  rw [hprefix]
  rfl

/-- Apply the genuine round-to-Alice/Bob regrouping independently in every reference block. -/
def retainedAnalysisRoundReferenceToBlock {n k : ℕ}
    (W : Quantum.Operators.Op (4 ^ n * k)) :
    Quantum.Operators.Op ((2 ^ n * 2 ^ n) * k) :=
  Matrix.of fun i j =>
    let a := finProdFinEquiv.symm i
    let b := finProdFinEquiv.symm j
    retainedAnalysisRoundToBlock n
      (Matrix.of fun u v =>
        W (finProdFinEquiv (u, a.2)) (finProdFinEquiv (v, b.2))) a.1 b.1

/-- The numeral retained real map is the program-coordinate map after the explicit round-grouped
reference reindex. -/
theorem retainedAnalysisReal_referenceBlock_eq_program
    (nK mZ mX ell ellEV leakEC k : ℕ) [NeZero k]
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (W : Quantum.Operators.Op (4 ^ (nK + mZ + mX) * k))
    (q q' : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space)
    (s t : Fin k) :
    let eOut := retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
    Quantum.Channels.mapTensorId
        (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q) W
        (finProdFinEquiv (eOut q, s)) (finProdFinEquiv (eOut q', t)) =
      Quantum.Channels.mapTensorId
        (coordinateLinear (retainedAnalysisBlockInputEquiv (nK + mZ + mX)) eOut
          (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote)
        (retainedAnalysisRoundReferenceToBlock W)
        (finProdFinEquiv (eOut q, s)) (finProdFinEquiv (eOut q', t)) := by
  let := retainedAnalysisRoundDimNeZero (nK + mZ + mX)
  let := retainedAnalysisBlockDimNeZero (nK + mZ + mX)
  let := retainedAnalysisOutputDimNeZero nK mZ mX ell ellEV leakEC
  dsimp only
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  simp only [retainedAnalysisReal, LinearMap.comp_apply]
  simp only [finProdFinEquiv_symm_apply,
    Quantum.Channels.finProdFinEquiv_apply_divNat,
    Quantum.Channels.finProdFinEquiv_apply_modNat]
  have hblock :
      retainedAnalysisRoundToBlock (nK + mZ + mX)
          (Matrix.of fun i j =>
            W (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))) =
        Matrix.of fun i j =>
          retainedAnalysisRoundReferenceToBlock W
            (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t)) := by
    ext i j
    simp [retainedAnalysisRoundReferenceToBlock, retainedAnalysisRoundToBlock_apply,
      Quantum.Channels.finProdFinEquiv_apply_divNat,
      Quantum.Channels.finProdFinEquiv_apply_modNat]
  rw [hblock]

end

end QKD.BB84.Reduction
