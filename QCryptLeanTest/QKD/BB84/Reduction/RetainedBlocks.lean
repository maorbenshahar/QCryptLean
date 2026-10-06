import QCryptLean.QKD.BB84.Reduction.RetainedBlocks
import QCryptLeanTest.QKD.BB84.Reduction.RetainedExperiment.Layout
import Mathlib.Util.AssertNoSorry

/-!
# Test fixtures for retained-analysis reference blocks

These fixtures check the explicit reference-block coordinates, the single nonidentity permutation
branch, complete-output discrimination, the zero-round edge, and the genuine two-round regrouping.
They do not use the program-kernel theorem as proof evidence.
-/

open Equiv

open scoped Matrix BigOperators
open Matrix Quantum.Operators

noncomputable section

namespace QKD.BB84.Reduction.RetainedBlocksAudit
open TypedLOCC

open TypedLOCC.TwoParty
open QKD.BB84.Engine
open Measurement Sampling
open RetainedAnalysisLayoutProbe
open QKD.BB84

/-- A literal Alice/Bob raw point in the two-round multipartite system. -/
def twoRawPoint (a b : Fin 4) : (FinalStage.rawSystem 2).total :=
  (TwoParty.pairEquiv (Fin 4) (Fin 4)).symm (a, b)

/-- A non-Hermitian matrix unit whose row and column carry different external-reference indices. -/
def twoRoundBlockReferenceUnit :
    Quantum.Operators.Op ((2 ^ 2 * 2 ^ 2) * 2) :=
  Matrix.single
    (finProdFinEquiv
      (retainedAnalysisBlockInputEquiv 2
        (twoRawPoint (⟨1, by decide⟩ : Fin 4) (⟨0, by decide⟩ : Fin 4)),
        (0 : Fin 2)))
    (finProdFinEquiv
      (retainedAnalysisBlockInputEquiv 2
        (twoRawPoint (⟨0, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4)),
        (1 : Fin 2))) 1

/-- The explicit block reindex recovers the ordered non-Hermitian matrix-unit entry at independent
reference row zero and column one. -/
theorem twoRoundBlockReferenceUnit_forward_entry :
    retainedAnalysisProgramInputReferenceBlock twoRoundBlockReferenceUnit
        (0 : Fin 2) (1 : Fin 2)
        (twoRawPoint (⟨1, by decide⟩ : Fin 4) (⟨0, by decide⟩ : Fin 4))
        (twoRawPoint (⟨0, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4)) = 1 := by
  simp [retainedAnalysisProgramInputReferenceBlock, twoRoundBlockReferenceUnit,
    twoRawPoint, Matrix.single_apply]

/-- Reversing both physical and reference axes gives zero, so the preceding fixture is not a
Hermitian-symmetry test. -/
theorem twoRoundBlockReferenceUnit_reverse_entry :
    retainedAnalysisProgramInputReferenceBlock twoRoundBlockReferenceUnit
        (1 : Fin 2) (0 : Fin 2)
        (twoRawPoint (⟨0, by decide⟩ : Fin 4) (⟨1, by decide⟩ : Fin 4))
        (twoRawPoint (⟨1, by decide⟩ : Fin 4) (⟨0, by decide⟩ : Fin 4)) = 0 := by
  simp [retainedAnalysisProgramInputReferenceBlock, twoRoundBlockReferenceUnit,
    twoRawPoint]

/-- The non-involutive public branch used to expose permutation orientation. -/
def rotateThree : Equiv.Perm (Fin 3) := finRotate 3

/-- Forward and inverse images of zero distinguish the two orientations of the three-cycle. -/
theorem rotateThree_orientation :
    rotateThree (0 : Fin 3) = 1 ∧ rotateThree.symm (0 : Fin 3) = 2 := by
  decide

/-- At the three-cycle branch, the measured reference block literally applies Alice's operator
first and Bob's operator second, with independently supplied reference indices. -/
theorem rotateThree_measuredReferenceBlock_chronology
    (W : Quantum.Operators.Op ((2 ^ 3 * 2 ^ 3) * 2))
    (x : (FinalStage.rawSystem 3).total) (s t : Fin 2) :
    retainedAnalysisMeasuredReferenceBlock
        (fun _ : Fin 3 => false) (fun _ : Fin 3 => false)
        rotateThree W x s t =
      let h : (QKD.BB84.Reduction.bobSiftUnitAnnouncement 3
          (fun _ => false) (fun _ => false) rotateThree).out () = FinalStage.rawSystem 3 := by
        change ((FinalStage.rawSystem 3).set .alice (Fin (2 ^ 3))).set .bob (Fin (2 ^ 3)) = _
        exact (congrArg (fun R : MultipartiteSystem Party => R.set .bob (Fin (2 ^ 3)))
          (TwoParty.set_alice (Fin (2 ^ 3)) (Fin (2 ^ 3)) (Fin (2 ^ 3)))).trans
          (TwoParty.set_bob (Fin (2 ^ 3)) (Fin (2 ^ 3)) (Fin (2 ^ 3)))
      let rho := retainedAnalysisProgramInputReferenceBlock W s t
      let KA := localKrausLift (FinalStage.rawSystem 3) .alice (Fin (2 ^ 3))
        (QKD.BB84.Model.siftPermHalf 3 (fun _ => false) (fun _ => false) rotateThree)
      let KB := localKrausLift ((QKD.BB84.Reduction.alicePermutationAnnouncement 3
        (fun _ => false) (fun _ => false)).out rotateThree) .bob (Fin (2 ^ 3))
        (QKD.BB84.Model.siftPermHalf 3 (fun _ => false) (fun _ => false) rotateThree)
      (reindexOp (Equiv.cast (congrArg MultipartiteSystem.total h))
        (matrixConjLinear KB (matrixConjLinear KA rho))) x x := by
  rfl

/-- Alice's actual nonidentity branch contributes the single uniform permutation coefficient. -/
theorem rotateThree_alicePrefix_hasOneUniformWeight
    (rho : TypedLOCC.Op (FinalStage.rawSystem 3).total)
    (q q' : ((QKD.BB84.Reduction.alicePermutationAnnouncement 3
      (fun _ : Fin 3 => false) (fun _ : Fin 3 => false)).out rotateThree).total) :
    ((QKD.BB84.Reduction.alicePermutationAnnouncement 3
        (fun _ : Fin 3 => false) (fun _ : Fin 3 => false)).liftedOperation
          (rotateThree, ()) rho) q q' =
      (Fintype.card (Equiv.Perm (Fin 3)) : ℂ)⁻¹ *
        (matrixConjLinear
          (localKrausLift (FinalStage.rawSystem 3) .alice (Fin (2 ^ 3))
            (QKD.BB84.Model.siftPermHalf 3 (fun _ => false) (fun _ => false) rotateThree))
          rho) q q' := by
  exact QKD.BB84.Reduction.alicePermutationAnnouncement_liftedOperation_apply
    3 (fun _ => false) (fun _ => false) rotateThree rho q q'

/-- Bob's use of the same oriented three-cycle contributes no second probability coefficient. -/
theorem rotateThree_bobPrefix_hasNoSecondWeight
    (rho : TypedLOCC.Op ((QKD.BB84.Reduction.alicePermutationAnnouncement 3
      (fun _ : Fin 3 => false) (fun _ : Fin 3 => false)).out rotateThree).total)
    (q q' : ((QKD.BB84.Reduction.bobSiftUnitAnnouncement 3
      (fun _ : Fin 3 => false) (fun _ : Fin 3 => false) rotateThree).out ()).total) :
    ((QKD.BB84.Reduction.bobSiftUnitAnnouncement 3
        (fun _ : Fin 3 => false) (fun _ : Fin 3 => false) rotateThree).liftedOperation
          () rho) q q' =
      (matrixConjLinear
        (localKrausLift ((QKD.BB84.Reduction.alicePermutationAnnouncement 3
      (fun _ : Fin 3 => false) (fun _ : Fin 3 => false)).out rotateThree)
          .bob (Fin (2 ^ 3))
          (QKD.BB84.Model.siftPermHalf 3 (fun _ => false) (fun _ => false) rotateThree))
        rho) q q' := by
  exact QKD.BB84.Reduction.bobSiftUnitAnnouncement_liftedOperation_apply
    3 (fun _ => false) (fun _ => false) rotateThree rho q q'

/-- A complete accepted output with ordered one-bit Alice/Bob keys. -/
def acceptedAtKeys (keys : Fin 2 × Fin 2) :
    (retainedAnalysisBoundary 0 0 0 1 0 0).space :=
  zeroAcceptedRetainedOutput keys

/-- Two accepted points with unequal ordered key pairs share their complete public exit. -/
theorem acceptedAtKeys_same_exit :
    (acceptedAtKeys (0, 0)).1 = (acceptedAtKeys (0, 1)).1 := by
  rfl

/-- Those two points are nevertheless unequal complete output points. -/
theorem acceptedAtKeys_ne : acceptedAtKeys (0, 0) ≠ acceptedAtKeys (0, 1) := by
  unfold acceptedAtKeys zeroAcceptedRetainedOutput
  apply (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0).symm.injective.ne
  intro hdata
  have hraw := congrArg Prod.snd hdata
  unfold zeroAcceptedRawOutput at hraw
  have hchildren :=
    (Boundary.graftSpaceEquiv
      (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (fun i => Fin.elim0 i) 0)
      (fun _ => FinalStage.boundary 1)).symm.injective hraw
  have hfinal := congrArg (fun w :
      Σ _ : (QKD.BB84.classicalPreDecisionBoundary
        0 0 1 0 (fun i => Fin.elim0 i) 0).Exit,
        (FinalStage.boundary 1).space => w.2) hchildren
  have hsum := (finalStageOutputEquiv 1).symm.injective hfinal
  have hpairs : ((0 : Fin 2), (0 : Fin 2)) = ((0 : Fin 2), (1 : Fin 2)) :=
    Sum.inl.inj hsum
  exact Fin.zero_ne_one (congrArg Prod.snd hpairs)

/-- The theorem's complete-point branch is zero for equal public exits carrying unequal keys. -/
theorem acceptedAtKeys_offDiagonal_branch (z : ℂ) :
    (if acceptedAtKeys (0, 0) = acceptedAtKeys (0, 1) then z else 0) = 0 := by
  rw [ite_eq_right acceptedAtKeys_ne]

/-- A complete two-round output with a supplied actual announced permutation. -/
def twoRoundOutputAt (pi : Equiv.Perm (Fin 2)) :
    (retainedAnalysisBoundary 0 1 1 0 0 0).space :=
  (retainedAnalysisOutputDataEquiv 0 1 1 0 0 0).symm
    (pi, retainedAnalysisDefaultRawTailOutput 0 1 1 0 0 0)

/-- Different actual announced permutations give unequal complete output points. -/
theorem twoRoundOutputAt_ne :
    twoRoundOutputAt (Equiv.refl (Fin 2)) ≠
      twoRoundOutputAt (Equiv.swap 0 1) := by
  apply (retainedAnalysisOutputDataEquiv 0 1 1 0 0 0).symm.injective.ne
  intro h
  have hp := congrArg Prod.fst h
  exact (by decide : (Equiv.refl (Fin 2)) ≠ Equiv.swap 0 1) hp

/-- The theorem's complete-point branch is also zero between distinct public permutations. -/
theorem twoRoundOutputAt_crossPermutation_branch (z : ℂ) :
    (if twoRoundOutputAt (Equiv.refl (Fin 2)) =
        twoRoundOutputAt (Equiv.swap 0 1) then z else 0) = 0 := by
  rw [ite_eq_right twoRoundOutputAt_ne]

/-- The unique zero-round raw point. -/
def zeroRawPoint : (FinalStage.rawSystem 0).total :=
  (TwoParty.pairEquiv (Fin 1) (Fin 1)).symm (0, 0)

/-- A zero-round reference-off-diagonal matrix unit. -/
def zeroRoundReferenceUnit : Quantum.Operators.Op ((2 ^ 0 * 2 ^ 0) * 2) :=
  Matrix.single
    (finProdFinEquiv (retainedAnalysisBlockInputEquiv 0 zeroRawPoint, (0 : Fin 2)))
    (finProdFinEquiv (retainedAnalysisBlockInputEquiv 0 zeroRawPoint, (1 : Fin 2))) 1

/-- The block construction remains total at zero retained rounds and preserves unequal reference
row and column coordinates. -/
theorem zeroRoundReferenceUnit_entry :
    retainedAnalysisProgramInputReferenceBlock zeroRoundReferenceUnit
        (0 : Fin 2) (1 : Fin 2) zeroRawPoint zeroRawPoint = 1 := by
  simp [retainedAnalysisProgramInputReferenceBlock, zeroRoundReferenceUnit, zeroRawPoint,
    Matrix.single_apply]

/-- Two-round reference matrix unit whose quantum coordinates are round-grouped and whose external
reference row and column are unequal. -/
def asymmetricRoundReferenceUnit : Quantum.Operators.Op (4 ^ 2 * 2) :=
  Matrix.single
    (finProdFinEquiv ((⟨2, by decide⟩ : Fin (4 ^ 2)), (0 : Fin 2)))
    (finProdFinEquiv ((⟨1, by decide⟩ : Fin (4 ^ 2)), (1 : Fin 2))) 1

/-- The explicit reference-preserving regrouping uses the genuine asymmetric two-round
`roundGroupEquiv` direction on both axes. -/
theorem asymmetricRoundReferenceUnit_regrouped :
    retainedAnalysisRoundReferenceToBlock asymmetricRoundReferenceUnit
        (finProdFinEquiv
          ((⟨4, by decide⟩ : Fin (2 ^ 2 * 2 ^ 2)), (0 : Fin 2)))
        (finProdFinEquiv
          ((⟨1, by decide⟩ : Fin (2 ^ 2 * 2 ^ 2)), (1 : Fin 2))) = 1 := by
  simp only [retainedAnalysisRoundReferenceToBlock, Matrix.of_apply,
    finProdFinEquiv_symm_apply,
    Quantum.Channels.finProdFinEquiv_apply_divNat,
    Quantum.Channels.finProdFinEquiv_apply_modNat]
  rw [retainedAnalysisRoundToBlock_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hrow :
      (Equiv.roundGroupEquiv 2 2 2).symm
          (⟨4, by decide⟩ : Fin (2 ^ 2 * 2 ^ 2)) =
        (⟨2, by decide⟩ : Fin (4 ^ 2)) := by
    decide
  have hcol :
      (Equiv.roundGroupEquiv 2 2 2).symm
          (⟨1, by decide⟩ : Fin (2 ^ 2 * 2 ^ 2)) =
        (⟨1, by decide⟩ : Fin (4 ^ 2)) := by
    decide
  rw [hrow, hcol]
  simp [asymmetricRoundReferenceUnit, Matrix.single_apply]

end QKD.BB84.Reduction.RetainedBlocksAudit
