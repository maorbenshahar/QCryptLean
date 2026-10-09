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
open _root_.LOCC

open _root_.LOCC.TwoParty
open QKD.BB84.FiniteKey
open Measurement Sampling
open RetainedAnalysisLayoutProbe
open QKD.BB84

/-- A literal Alice/Bob raw point in the two-round multipartite system. -/
def twoRawPoint (a b : Bits 2) : (FinalStage.rawSystem 2).total :=
  (TwoParty.pairEquiv (Bits 2) (Bits 2)).symm (a, b)

/-- A non-Hermitian matrix unit whose row and column carry different external-reference indices. -/
def twoRoundBlockReferenceUnit :
    Op ((Bits 2 × Bits 2) × Fin 2) :=
  Matrix.single
    (TwoParty.pairEquiv (Bits 2) (Bits 2) (twoRawPoint ![1, 0] 0), (0 : Fin 2))
    (TwoParty.pairEquiv (Bits 2) (Bits 2) (twoRawPoint 0 ![1, 0]), (1 : Fin 2)) 1

/-- The explicit block reindex recovers the ordered non-Hermitian matrix-unit entry at independent
reference row zero and column one. -/
theorem twoRoundBlockReferenceUnit_forward_entry :
    retainedAnalysisProgramInputReferenceBlock twoRoundBlockReferenceUnit
        (0 : Fin 2) (1 : Fin 2)
        (twoRawPoint ![1, 0] 0)
        (twoRawPoint 0 ![1, 0]) = 1 := by
  simp [retainedAnalysisProgramInputReferenceBlock, twoRoundBlockReferenceUnit,
    twoRawPoint, Matrix.single_apply]

/-- Reversing both physical and reference axes gives zero, so the preceding fixture is not a
Hermitian-symmetry test. -/
theorem twoRoundBlockReferenceUnit_reverse_entry :
    retainedAnalysisProgramInputReferenceBlock twoRoundBlockReferenceUnit
        (1 : Fin 2) (0 : Fin 2)
        (twoRawPoint 0 ![1, 0])
        (twoRawPoint ![1, 0] 0) = 0 := by
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
    (W : Op ((Bits 3 × Bits 3) × Fin 2))
    (x : (FinalStage.rawSystem 3).total) (s t : Fin 2) :
    retainedAnalysisMeasuredReferenceBlock
        (fun _ : Fin 3 => false) (fun _ : Fin 3 => false)
        rotateThree W x s t =
      let R := FinalStage.rawSystem 3
      let rho := retainedAnalysisProgramInputReferenceBlock W s t
      let kappa := Model.siftPermHalf 3 (fun _ => false) (fun _ => false) rotateThree
      let KA := (localKrausLift R .alice (Bits 3)
        kappa).submatrix
        (Equiv.cast (congrArg MultipartiteSystem.total (R.set_self .alice).symm)) id
      let KB := (localKrausLift R .bob (Bits 3)
        kappa).submatrix
        (Equiv.cast (congrArg MultipartiteSystem.total (R.set_self .bob).symm)) id
      Matrix.conjLinearMap KB (Matrix.conjLinearMap KA rho) x x := by
  dsimp only [retainedAnalysisMeasuredReferenceBlock, retainedAnalysisSiftedState,
    Matrix.of_apply]

/-- Alice's actual nonidentity branch contributes the single uniform permutation coefficient. -/
theorem rotateThree_alicePrefix_hasOneUniformWeight
    (rho : Quantum.Operators.Op (FinalStage.rawSystem 3).total)
    (q q' : ((QKD.BB84.Reduction.alicePermutationAnnouncement 3
      (fun _ : Fin 3 => false) (fun _ : Fin 3 => false)).out rotateThree).total) :
    ((QKD.BB84.Reduction.alicePermutationAnnouncement 3
        (fun _ : Fin 3 => false) (fun _ : Fin 3 => false)).liftedOperation
          (rotateThree, ()) rho) q q' =
      (Fintype.card (Equiv.Perm (Fin 3)) : ℂ)⁻¹ *
        (Matrix.conjLinearMap
          (localKrausLift (FinalStage.rawSystem 3) .alice (Bits 3)
            (QKD.BB84.Model.siftPermHalf 3 (fun _ => false) (fun _ => false) rotateThree))
          rho) q q' := by
  exact QKD.BB84.Reduction.alicePermutationAnnouncement_liftedOperation_apply
    3 (fun _ => false) (fun _ => false) rotateThree rho q q'

/-- Bob's use of the same oriented three-cycle contributes no second probability coefficient. -/
theorem rotateThree_bobPrefix_hasNoSecondWeight
    (rho : Quantum.Operators.Op (FinalStage.rawSystem 3).total)
    (q q' : ((QKD.BB84.Reduction.bobSiftUnitAnnouncement 3
      (fun _ : Fin 3 => false) (fun _ : Fin 3 => false) rotateThree).out ()).total) :
    ((QKD.BB84.Reduction.bobSiftUnitAnnouncement 3
        (fun _ : Fin 3 => false) (fun _ : Fin 3 => false) rotateThree).liftedOperation
          () rho) q q' =
      (Matrix.conjLinearMap
        (localKrausLift (FinalStage.rawSystem 3)
          .bob (Bits 3)
          (QKD.BB84.Model.siftPermHalf 3 (fun _ => false) (fun _ => false) rotateThree))
        rho) q q' := by
  exact QKD.BB84.Reduction.bobSiftUnitAnnouncement_liftedOperation_apply
    3 (fun _ => false) (fun _ => false) rotateThree rho q q'

/-- A complete accepted output with ordered one-bit Alice/Bob keys. -/
def acceptedAtKeys (keys : Bits 1 × Bits 1) :
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
      (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@packedPESel 0 0 0) 0)
      (fun _ => FinalStage.boundary 1)).symm.injective hraw
  have hfinal := congrArg (fun w :
      Σ _ : (QKD.BB84.classicalPreDecisionBoundary
        0 0 1 0 (@packedPESel 0 0 0) 0).Exit,
        (FinalStage.boundary 1).space => w.2) hchildren
  have hsum := (FinalStage.outputEquiv 1).symm.injective hfinal
  have hpairs : ((0 : Bits 1), (0 : Bits 1)) = ((0 : Bits 1), (1 : Bits 1)) :=
    Sum.inl.inj hsum
  exact Fin.zero_ne_one (congrArg (fun ks : Bits 1 × Bits 1 => ks.2 0) hpairs)

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
  (TwoParty.pairEquiv (Bits 0) (Bits 0)).symm (0, 0)

/-- A zero-round reference-off-diagonal matrix unit. -/
def zeroRoundReferenceUnit : Op ((Bits 0 × Bits 0) × Fin 2) :=
  Matrix.single
    (TwoParty.pairEquiv (Bits 0) (Bits 0) zeroRawPoint, (0 : Fin 2))
    (TwoParty.pairEquiv (Bits 0) (Bits 0) zeroRawPoint, (1 : Fin 2)) 1

/-- The block construction remains total at zero retained rounds and preserves unequal reference
row and column coordinates. -/
theorem zeroRoundReferenceUnit_entry :
    retainedAnalysisProgramInputReferenceBlock zeroRoundReferenceUnit
        (0 : Fin 2) (1 : Fin 2) zeroRawPoint zeroRawPoint = 1 := by
  simp [retainedAnalysisProgramInputReferenceBlock, zeroRoundReferenceUnit, zeroRawPoint,
    Matrix.single_apply]

/-- An asymmetric pair of round strings, with independent external-reference axes. -/
def asymmetricRoundReferenceUnit : Op (Signals 2 × Fin 2) :=
  Matrix.single ((fun i => if i = 0 then (1, 0) else (0, 0)), 0)
    ((fun i => if i = 0 then (0, 1) else (0, 0)), 1) 1

/-- Structural regrouping preserves both the quantum and the external-reference orientations. -/
theorem asymmetricRoundReferenceUnit_regrouped :
    Matrix.reindex
      ((Quantum.Symmetry.pairFunctions Bit Bit 2).prodCongr (Equiv.refl (Fin 2)))
      ((Quantum.Symmetry.pairFunctions Bit Bit 2).prodCongr (Equiv.refl (Fin 2)))
      asymmetricRoundReferenceUnit
      ((![(1 : Bit), 0], 0), 0) ((0, ![(1 : Bit), 0]), 1) = 1 := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.refl_symm]
  have h1 : (fun i : Fin 2 => if i = 0 then ((1 : Bit), (0 : Bit)) else (0, 0)) =
      (fun i => ((![(1 : Bit), 0]) i, (0 : Bits 2) i)) := by
    funext i
    fin_cases i <;> rfl
  have h2 : (fun i : Fin 2 => if i = 0 then ((0 : Bit), (1 : Bit)) else (0, 0)) =
      (fun i => ((0 : Bits 2) i, (![(1 : Bit), 0]) i)) := by
    funext i
    fin_cases i <;> rfl
  simp [asymmetricRoundReferenceUnit, h1, h2, Quantum.Symmetry.pairFunctions,
    Equiv.arrowProdEquivProdArrow]

end QKD.BB84.Reduction.RetainedBlocksAudit
