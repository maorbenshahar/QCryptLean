import QCryptLean.QKD.BB84.Reduction.ClassicalTail
import QCryptLeanTest.QKD.BB84.Reduction.ClassicalTail.Constructor
import QCryptLean.QKD.BB84.TailOutput
import Mathlib.Util.AssertNoSorry
import QCryptLean.QKD.BB84.Program

/-!
# Tests of the retained-tail block kernel

The constructor probes below are independent of the complete-output kernel theorem.  The two
actual-channel regressions are kernel-backed: they instantiate that theorem and test its usable
consequences without claiming an independent proof.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Reduction.DirectTailAudit
open TypedLOCC

open TypedLOCC.TwoParty
open QKD.BB84.Engine
open QKD.BB84

/-- The one-round selector used by the concrete direct-tail probes. -/
def oneKeySelector : Fin 1 → Bool := fun _ => false

/-- A concrete error-correction scheme whose syndrome is trivial and whose decoder returns Bob's
raw key string. -/
def oneBitEC : ECScheme 1 oneKeySelector 0 :=
  ⟨fun _ => 0, fun b _ => b⟩

/-- A raw pair in the actual Alice/Bob register order. -/
def rawPair (alice bob : Fin 2) : (FinalStage.rawSystem 1).total :=
  (TwoParty.pairEquiv (Fin 2) (Fin 2)).symm (alice, bob)

/-- Two raw inputs that agree on Alice and differ on Bob. -/
theorem rawPair00_ne_rawPair01 : rawPair 0 0 ≠ rawPair 0 1 := by
  intro h
  have hp := congrArg (TwoParty.pairEquiv (Fin 2) (Fin 2)) h
  simp [rawPair] at hp

/-- An explicit non-Hermitian cross-raw matrix unit. -/
def crossRaw : TypedLOCC.Op (FinalStage.rawSystem 1).total :=
  Matrix.single (rawPair 0 0) (rawPair 0 1) 1

/-- The cross-raw fixture is genuinely nonzero. -/
theorem crossRaw_ne_zero : crossRaw ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h (rawPair 0 0)) (rawPair 0 1)
  simp [crossRaw] at hentry

/-- A nonconstant privacy-amplification seed paired with the unique zero-length EV seed. -/
def nontrivialSeedPair : KeyHashSeedPairEV 1 1 0 oneKeySelector :=
  (fun _ _ => 1, fun i => Fin.elim0 i)

/-- The explicit data constructor retains the sampled seed and computes the actual fused tag and
syndrome from Alice's raw coordinate. -/
theorem nontrivialData_coordinates :
    let d := rawClassicalTailDataOf 1 0 1 0 oneKeySelector 0 oneBitEC
      (rawPair 0 1) nontrivialSeedPair
    d.seedPair = nontrivialSeedPair ∧
      d.evTag = (finProdFinEquiv.symm
        (QKD.BB84.Model.evTagSynOf 1 1 0 oneKeySelector 0 oneBitEC
          (Fintype.equivFin _ nontrivialSeedPair) ((rawPair 0 1) .alice))).1 ∧
      d.syndrome = (finProdFinEquiv.symm
        (QKD.BB84.Model.evTagSynOf 1 1 0 oneKeySelector 0 oneBitEC
          (Fintype.equivFin _ nontrivialSeedPair) ((rawPair 0 1) .alice))).2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The complete output point decodes through the actual graft into the literal pre-decision exit
and final-stage point. -/
theorem outputPoint_graft_coordinates
    (delta Q : ℝ) (x : (FinalStage.rawSystem 1).total)
    (st : KeyHashSeedPairEV 1 1 0 oneKeySelector) :
    (Boundary.graftSpaceEquiv
      (QKD.BB84.classicalPreDecisionBoundary 1 0 1 0 oneKeySelector 0)
      (fun _ => FinalStage.boundary 1))
      (rawClassicalTailOutputPoint 1 0 1 0 oneKeySelector oneKeySelector 0 oneBitEC
        delta Q x st) =
      ⟨(QKD.BB84.classicalTailExitEquiv 1 0 1 0 oneKeySelector 0).symm
          (rawClassicalTailDataOf 1 0 1 0 oneKeySelector 0 oneBitEC x st),
        rawClassicalTailFinalPoint 1 0 1 0 oneKeySelector oneKeySelector 0 oneBitEC
          delta Q (rawClassicalTailDataOf 1 0 1 0 oneKeySelector 0 oneBitEC x st) x⟩ := by
  exact Equiv.apply_symm_apply _ _

/-- A literal accepted final-stage output with Alice's key first and Bob's key second. -/
def literalAcceptedPoint (alice bob : Fin 2) : (FinalStage.boundary 1).space :=
  (finalStageOutputEquiv 1).symm (Sum.inl (alice, bob))

/-- Decoding the independently constructed accepted point recovers the ordered key pair. -/
theorem literalAcceptedPoint_ordered (alice bob : Fin 2) :
    finalStageOutputEquiv 1 (literalAcceptedPoint alice bob) = Sum.inl (alice, bob) :=
  (finalStageOutputEquiv 1).apply_symm_apply _

/-- Swapping unequal Alice and Bob keys changes the literal accepted output. -/
theorem literalAcceptedPoint_unequal_order :
    literalAcceptedPoint 0 1 ≠ literalAcceptedPoint 1 0 := by
  intro h
  have hout := congrArg (finalStageOutputEquiv 1) h
  simp [literalAcceptedPoint] at hout

/-- In the aborting branch, the literal final point has flag one and the actual Unit/Unit
payload. -/
theorem finalPoint_aborts_to_units
    (d : QKD.BB84.ClassicalTailData 1 0 0 0 oneKeySelector 0)
    (x : (FinalStage.rawSystem 1).total) (delta Q : ℝ)
    (hflag : QKD.BB84.Model.acceptFlagOf 1 0 0 oneKeySelector oneKeySelector 0 oneBitEC
      delta Q d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob) ≠ 0) :
    let q := rawClassicalTailFinalPoint 1 0 0 0 oneKeySelector oneKeySelector 0 oneBitEC
      delta Q d x
    (Boundary.publicSpaceEquiv (FinalStage.flagBoundary 0) q).1 =
      QKD.BB84.Model.acceptFlagOf 1 0 0 oneKeySelector oneKeySelector 0 oneBitEC
        delta Q d.alicePE d.bobPE d.seedPair.2 d.evTag d.syndrome (x .bob) := by
  simp [rawClassicalTailFinalPoint, hflag]

/-- A CQ input can retain an off-diagonal reference entry within a fixed raw diagonal. -/
def referenceOffDiagonal : Quantum.Operators.Op 2 := Matrix.single 0 1 1

/-- Kernel-backed regression: both accepting and aborting complete outputs kill the same concrete
cross-raw non-Hermitian matrix unit by the complete-output kernel law. -/
theorem actualTail_crossRaw_vanishes_kernelBacked (Q : ℝ)
    (q q' : (QKD.BB84.rawClassicalTailBoundary 1 0 0 0 oneKeySelector 0).space) :
    (QKD.BB84.rawClassicalTailProgram 1 0 0 0 oneKeySelector oneKeySelector 0 oneBitEC 0 Q).denote
      crossRaw q q' = 0 := by
  rw [rawClassicalTailProgram_output_apply]
  have hdiag (x : (FinalStage.rawSystem 1).total) : crossRaw x x = 0 := by
    rw [crossRaw, Matrix.single_apply]
    split
    · rename_i h
      exact (rawPair00_ne_rawPair01 (h.1.trans h.2.symm)).elim
    · rfl
  split
  · simp_rw [hdiag]
    simp
  · rfl

/-- Kernel-backed diagonal regression: the actual channel formula retains exactly the raw
diagonal selected by the concrete matrix unit and averages over all seed pairs. -/
theorem actualTail_diagonal_weight_kernelBacked
    (q q' : (QKD.BB84.rawClassicalTailBoundary 1 0 0 0 oneKeySelector 0).space) :
    let x := rawPair 0 0
    (QKD.BB84.rawClassicalTailProgram 1 0 0 0 oneKeySelector oneKeySelector 0 oneBitEC 0 1).denote
        (Matrix.single x x 1) q q' =
      if q = q' then
        ∑ st : KeyHashSeedPairEV 1 0 0 oneKeySelector,
          if rawClassicalTailOutputPoint 1 0 0 0 oneKeySelector oneKeySelector 0 oneBitEC
              0 1 x st = q then
            (Fintype.card (KeyHashSeedPairEV 1 0 0 oneKeySelector) : ℂ)⁻¹
          else 0
      else 0 := by
  dsimp only
  rw [rawClassicalTailProgram_output_apply]
  split
  · rw [Finset.sum_eq_single (rawPair 0 0)]
    · congr 1
      funext st
      split <;> simp
    · intro x _ hx
      simp [Ne.symm hx]
    · intro hx
      exact (hx (Finset.mem_univ _)).elim
  · rfl

end QKD.BB84.Reduction.DirectTailAudit

