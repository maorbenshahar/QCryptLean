import QCryptLean.QKD.BB84.Program

/-!
# Basis erasure as a map of diagonals

After both parties of the measure-first BB84 experiment forget their private basis strings, the
basis-erasure stage (`QKD.BB84.selectedBitsToRawProgram`) sends the selected-record diagonal mass to
the raw registers.  This module states that transport as an exact diagonal identity.  It sits
directly above the chronological construction and is the shared low home used by the acceptance
analysis (`QCryptLean.QKD.BB84.Acceptance`) and by the success sector of the retained-round
factorization (`QCryptLean.QKD.BB84.Reduction.Factorization.Real.Success`). -/

open scoped Matrix BigOperators

noncomputable section

namespace QKD.BB84.Reduction
open TypedLOCC

open TypedLOCC.TwoParty
open Measurement Sampling

/-- **The basis-erasure stage as a map of diagonals.**  After both parties forget their private
basis strings, the diagonal entry at raw registers `x` is the total diagonal mass of the selected
records whose selected bits are `x`. -/
theorem selectedBitsToRawProgram_denote_diag (N n : ℕ)
    (σ : Op (weightedSelectedRecordSystem N n).total) (x : (FinalStage.rawSystem n).total) :
    (QKD.BB84.selectedBitsToRawProgram N n).denote σ ⟨(), x⟩ ⟨(), x⟩ =
      ∑ qB : SelectedLocalRecord N n, ∑ qA : SelectedLocalRecord N n,
        @ite ℂ
          (x .alice = QKD.BB84.selectedBitsToRaw qA ∧ x .bob = QKD.BB84.selectedBitsToRaw qB)
          (@instDecidableAnd _ _
            ((inferInstance : DecidableEq (Fin (2 ^ n))) (x .alice) (selectedBitsToRaw qA))
            ((inferInstance : DecidableEq (Fin (2 ^ n))) (x .bob) (selectedBitsToRaw qB)))
          (σ ((TwoParty.pairEquiv _ _).symm (qA, qB))
            ((TwoParty.pairEquiv _ _).symm (qA, qB))) 0 := by
  have hx : x = (TwoParty.pairEquiv _ _).symm (x .alice, x .bob) := by
    funext i
    cases i <;> rfl
  have hout : (QKD.BB84.selectedBitsToRawBobAction N n).out = FinalStage.rawSystem n := by
    change ((weightedSelectedRecordSystem N n).set .alice (Fin (2 ^ n))).set .bob
      (Fin (2 ^ n)) = _
    rw [weightedSelectedRecordSystem, TwoParty.set_alice, TwoParty.set_bob]
  have hcoord (a b : Fin (2 ^ n)) :
      (Equiv.cast (congrArg Boundary.space (congrArg Boundary.leaf hout.symm)))
          ((Boundary.leafSpaceEquiv (FinalStage.rawSystem n)).symm
            ((TwoParty.pairEquiv _ _).symm (a, b))) =
        (Boundary.leafSpaceEquiv (QKD.BB84.selectedBitsToRawBobAction N n).out).symm
          ((QKD.BB84.selectedBitsToRawBobAction N n).out.pairEquiv.symm (a, b)) := by
    change cast (congrArg (fun T => (Boundary.leaf T).space) hout.symm)
      ((Boundary.leafSpaceEquiv (FinalStage.rawSystem n)).symm
        ((FinalStage.rawSystem n).pairEquiv.symm (a, b))) = _
    rw [Boundary.cast_leafSpaceEquiv_symm hout.symm,
      MultipartiteSystem.cast_pairEquiv_symm hout.symm]
    rfl
  conv_lhs => rw [hx]
  change (QKD.BB84.selectedBitsToRawProgram N n).denote σ
    ((Boundary.leafSpaceEquiv (FinalStage.rawSystem n)).symm
      ((TwoParty.pairEquiv _ _).symm ((x .alice), (x .bob))))
    ((Boundary.leafSpaceEquiv (FinalStage.rawSystem n)).symm
      ((TwoParty.pairEquiv _ _).symm ((x .alice), (x .bob)))) = _
  unfold QKD.BB84.selectedBitsToRawProgram
  refine (Program.denote_cast_apply rfl (congrArg Boundary.leaf hout.symm) _ _ _ _).trans ?_
  refine (congrArg₂ (((selectedBitsToRawAliceAction N n).then
    (selectedBitsToRawBobAction N n).run).denote σ)
    (hcoord (x .alice) (x .bob)) (hcoord (x .alice) (x .bob))).trans ?_
  unfold PrivateAction.then PrivateAction.run
  rw [Program.denote_priv_eq_sum_liftedOperation]
  change ((∑ o : Unit, ((QKD.BB84.selectedBitsToRawBobAction N n).then Program.done).denote ∘ₗ
    (QKD.BB84.selectedBitsToRawAliceAction N n).liftedOperation o) σ) _ _ = _
  rw [Fintype.sum_unique]
  simp only [LinearMap.comp_apply]
  unfold PrivateAction.then
  rw [Program.denote_priv_eq_sum_liftedOperation]
  change ((∑ o : Unit, Program.done.denote ∘ₗ (QKD.BB84.selectedBitsToRawBobAction N
    n).liftedOperation o)
    ((QKD.BB84.selectedBitsToRawAliceAction N n).liftedOperation () σ)) _ _ = _
  rw [Fintype.sum_unique]
  simp only [LinearMap.comp_apply, Program.denote_done]
  change ((QKD.BB84.selectedBitsToRawBobAction N n).liftedOperation ()
    ((QKD.BB84.selectedBitsToRawAliceAction N n).liftedOperation () σ))
      ((QKD.BB84.selectedBitsToRawBobAction N n).out.pairEquiv.symm ((x .alice), (x .bob)))
      ((QKD.BB84.selectedBitsToRawBobAction N n).out.pairEquiv.symm ((x .alice), (x .bob))) = _
  change (((Instrument.functionAndForget (QKD.BB84.selectedBitsToRaw)).liftAt
    (QKD.BB84.selectedBitsToRawAliceAction N n).out .bob).operation ()
      ((QKD.BB84.selectedBitsToRawAliceAction N n).liftedOperation () σ))
        (((QKD.BB84.selectedBitsToRawAliceAction N n).out.set .bob (Fin (2 ^ n))).pairEquiv.symm
          ((x .alice), (x .bob)))
        (((QKD.BB84.selectedBitsToRawAliceAction N n).out.set .bob (Fin (2 ^ n))).pairEquiv.symm
          ((x .alice), (x .bob))) = _
  refine (Instrument.liftAt_bob_operation_apply (selectedBitsToRawAliceAction N n).out
    (Instrument.functionAndForget (@selectedBitsToRaw N n)) ()
    ((selectedBitsToRawAliceAction N n).liftedOperation () σ)
    (x .alice) (x .alice) (x .bob) (x .bob)).trans ?_
  refine (Instrument.functionAndForget_operation_apply
    (@QKD.BB84.selectedBitsToRaw N n) _ _ _).trans ?_
  have hAliceApply (a a' : Fin (2 ^ n))
      (rB : SelectedLocalRecord N n) :
      ((QKD.BB84.selectedBitsToRawAliceAction N n).liftedOperation () σ)
          ((QKD.BB84.selectedBitsToRawAliceAction N n).out.pairEquiv.symm (a, rB))
          ((QKD.BB84.selectedBitsToRawAliceAction N n).out.pairEquiv.symm (a', rB)) =
        ∑ rA : SelectedLocalRecord N n,
          if a = QKD.BB84.selectedBitsToRaw rA ∧ a' = QKD.BB84.selectedBitsToRaw rA then
            σ ((TwoParty.pairEquiv _ _).symm (rA, rB))
              ((TwoParty.pairEquiv _ _).symm (rA, rB))
          else 0 := by
    change (((Instrument.functionAndForget (QKD.BB84.selectedBitsToRaw)).liftAt
      (weightedSelectedRecordSystem N n) .alice).operation () σ)
        (((weightedSelectedRecordSystem N n).set .alice
          (Fin (2 ^ n))).pairEquiv.symm (a, rB))
        (((weightedSelectedRecordSystem N n).set .alice
          (Fin (2 ^ n))).pairEquiv.symm (a', rB)) = _
    refine (Instrument.liftAt_alice_operation_apply (weightedSelectedRecordSystem N n)
      (Instrument.functionAndForget (@selectedBitsToRaw N n)) () σ a a' rB rB).trans ?_
    exact Instrument.functionAndForget_operation_apply (@QKD.BB84.selectedBitsToRaw N n) _ _ _
  let xa : Fin (2 ^ n) := x .alice
  let xb : Fin (2 ^ n) := x .bob
  refine Finset.sum_congr rfl fun qB _ => ?_
  by_cases hB : xb = selectedBitsToRaw qB
  · refine (ite_eq_left ⟨hB, hB⟩).trans ?_
    refine (hAliceApply xa xa qB).trans ?_
    refine Finset.sum_congr rfl fun qA _ => ?_
    by_cases hA : xa = selectedBitsToRaw qA
    · exact (ite_eq_left ⟨hA, hA⟩).trans (ite_eq_left ⟨hA, hB⟩).symm
    · exact (ite_eq_right (fun h => hA h.1)).trans
        (ite_eq_right (fun h => hA h.1)).symm
  · refine (ite_eq_right (fun h => hB h.1)).trans ?_
    symm
    exact Finset.sum_eq_zero fun qA _ => ite_eq_right (fun h => hB h.2)

end QKD.BB84.Reduction
