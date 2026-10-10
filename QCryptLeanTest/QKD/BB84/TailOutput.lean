import QCryptLean.QKD.BB84.TailOutput
import Mathlib.Util.AssertNoSorry

/-!
# Regression checks for the BB84 classical-tail output

The fixtures build a literal accepted point of the raw classical-tail graft, check its exit and
accepting disposition, and read its ordered key pair back through
`rawTail_graft_acceptCoordinates_keys`, also at zero sizes.  The
commands cover the final-stage coordinates of `QCryptLean.QKD.BB84.TailOutput`.
-/

noncomputable section

namespace QCryptLeanTest.BB84.TailOutput

open _root_.LOCC
open QKD.BB84 _root_.LOCC.TwoParty QKD.BB84.Measurement

/-- The literal accepted point in the raw classical-tail graft. -/
def rawAcceptedPoint
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (e : (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit)
    (keys : Bits ℓ × Bits ℓ) :
    (QKD.BB84.rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).space :=
  (Boundary.graftSpaceEquiv
    (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC)
    (fun _ => FinalStage.boundary ℓ)).symm
      ⟨e, (FinalStage.outputEquiv ℓ).symm (Sum.inl keys)⟩

/-- rawAcceptedPoint is the literal inverse graft-space constructor required by the raw identity. -/
theorem rawAcceptedPoint_identity
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (e : (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit)
    (keys : Bits ℓ × Bits ℓ) :
    (Boundary.graftSpaceEquiv
      (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC)
      (fun _ => FinalStage.boundary ℓ)).symm
        ⟨e, (FinalStage.outputEquiv ℓ).symm (Sum.inl keys)⟩ =
      rawAcceptedPoint n m ℓ ℓEV peSel leakEC e keys := by
  rfl

/-- The graft exit read from the literal accepted point is the supplied predecision exit paired
with the accepting final-stage leaf. -/
theorem rawAcceptedPoint_exit_coordinates
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (e : (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit)
    (keys : Bits ℓ × Bits ℓ) :
    Boundary.graftExitEquiv
        (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC)
        (fun _ => FinalStage.boundary ℓ)
        (rawAcceptedPoint n m ℓ ℓEV peSel leakEC e keys).1 =
      ⟨e, ((FinalStage.outputEquiv ℓ).symm (Sum.inl keys)).1⟩ := by
  let B := QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC
  let C : B.Exit → Boundary TwoParty.Party := fun _ => FinalStage.boundary ℓ
  let G := Boundary.graftSpaceEquiv B C
  have h := G.apply_symm_apply
    ⟨e, (FinalStage.outputEquiv ℓ).symm (Sum.inl keys)⟩
  rw [Boundary.graftSpaceEquiv_apply] at h
  have h' := congrArg
    (fun w : Σ e, (C e).space =>
      (⟨w.1, w.2.1⟩ : Σ e, (C e).Exit)) h
  simpa [rawAcceptedPoint, G, B, C] using h'

/-- The raw classical-tail layout classifies the literal accepted point as accepting. -/
theorem rawAcceptedPoint_isAccept
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (e : (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit)
    (keys : Bits ℓ × Bits ℓ) :
    (QKD.BB84.rawClassicalTailOutputLayout
      n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout.disposition
        (rawAcceptedPoint n m ℓ ℓEV peSel leakEC e keys).1 = .accept ℓ := by
  change FinalStage.disposition ℓ
    ((Boundary.graftExitEquiv
      (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC)
      (fun _ => FinalStage.boundary ℓ)
      (rawAcceptedPoint n m ℓ ℓEV peSel leakEC e keys).1).2).1 = .accept ℓ
  rw [rawAcceptedPoint_exit_coordinates]
  rfl

/-- The raw identity consumes the literal point identity and its derived acceptance fact. -/
theorem rawPoint_consumer
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (e : (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit)
    (keys : Bits ℓ × Bits ℓ) :
    let point := rawAcceptedPoint n m ℓ ℓEV peSel leakEC e keys
    let L := (QKD.BB84.rawClassicalTailOutputLayout
      n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout
    ((L.acceptCoordinates
        (rawAcceptedPoint_isAccept n m ℓ ℓEV peSel leakEC e keys) point.2).1,
      (L.acceptCoordinates
        (rawAcceptedPoint_isAccept n m ℓ ℓEV peSel leakEC e keys) point.2).2.1) = keys := by
  -- The identity lemma at the accepted point of `(e, keys)`; its exit and multipartite system point
  -- are those of
  -- the goal.
  intro point
  refine rawTail_graft_acceptCoordinates_keys
    n m ℓ ℓEV peSel leakEC e keys _ _ ?_
      (rawAcceptedPoint_isAccept n m ℓ ℓEV peSel leakEC e keys)
  -- The literal point is the inverse graft of `⟨e, inl keys⟩` by definition.
  rfl

/-- Explicit semantic data for the zero-size predecision exit. -/
def zeroTailData :
    QKD.BB84.ClassicalTailData 0 0 0 0 (fun i => Fin.elim0 i) 0 where
  alicePE i := Fin.elim0 i
  bobPE i := Fin.elim0 i
  seedPair := (fun _ _ => 0, fun _ _ => 0)
  evTag := 0
  syndrome := 0

/-- A concrete zero-size predecision exit, obtained from the existing explicit exit equivalence. -/
def zeroPredecisionExit :
    (QKD.BB84.classicalPreDecisionBoundary
      0 0 0 0 (fun i => Fin.elim0 i) 0).Exit :=
  (QKD.BB84.classicalTailExitEquiv
    0 0 0 0 (fun i => Fin.elim0 i) 0).symm zeroTailData

/-- Zero key length and zero protocol sizes have a concrete accepted raw-tail point. -/
theorem zeroSizes_literalRawAcceptedPoint_isAccept :
    (QKD.BB84.rawClassicalTailOutputLayout
      0 0 0 0 (fun i => Fin.elim0 i) 0).toBoundaryKeyLayout.disposition
        (rawAcceptedPoint 0 0 0 0 (fun i => Fin.elim0 i) 0
          zeroPredecisionExit (0, 0)).1 =
      .accept 0 := by
  exact rawAcceptedPoint_isAccept 0 0 0 0 (fun i => Fin.elim0 i) 0
    zeroPredecisionExit (0, 0)

end QCryptLeanTest.BB84.TailOutput
