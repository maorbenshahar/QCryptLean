import QCryptLean.QKD.BB84.Reduction.RetainedExperiment
import QCryptLean.QKD.BB84.TailOutput
import QCryptLean.QKD.BB84.CompleteOutput

/-!
# Retained-output layout tests

These fixtures check the literal accepted and aborted outputs and their ordered key projections.
-/

open scoped Matrix BigOperators

noncomputable section

namespace QKD.BB84.Reduction.RetainedAnalysisLayoutProbe
open _root_.LOCC

open _root_.LOCC.TwoParty
open Measurement Sampling
open QKD.BB84

def zeroTailData : QKD.BB84.ClassicalTailData 0 0 1 0 (@packedPESel 0 0 0) 0 where
  alicePE i := Fin.elim0 i
  bobPE i := Fin.elim0 i
  seedPair := (fun _ _ => 0, fun _ _ => 0)
  evTag := 0
  syndrome := 0

def zeroAcceptedRawOutput (keys : Bits 1 × Bits 1) :
    RawClassicalTailOutput 0 0 1 0 (@packedPESel 0 0 0) 0 :=
  (Boundary.graftSpaceEquiv
    (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@packedPESel 0 0 0) 0)
    (fun _ => FinalStage.boundary 1)).symm
      ⟨(QKD.BB84.classicalTailExitEquiv 0 0 1 0 (@packedPESel 0 0 0) 0).symm zeroTailData,
        (FinalStage.outputEquiv 1).symm (Sum.inl keys)⟩

def zeroAcceptedRetainedOutput (keys : Bits 1 × Bits 1) :
    (retainedAnalysisBoundary 0 0 0 1 0 0).space :=
  (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0).symm
    (Equiv.refl (Fin 0), zeroAcceptedRawOutput keys)

theorem zeroAcceptedRawOutput_disposition (keys : Bits 1 × Bits 1) :
    (QKD.BB84.rawClassicalTailOutputLayout 0 0 1 0 (@packedPESel 0 0 0) 0).disposition
        (zeroAcceptedRawOutput keys).1 = .accept 1 := by
  let B := QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@packedPESel 0 0 0) 0
  let C : B.Exit → Boundary Party := fun _ => FinalStage.boundary 1
  let G := Boundary.graftSpaceEquiv B C
  let z := Boundary.graftExitEquiv B C (zeroAcceptedRawOutput keys).1
  let hSystem := Boundary.system_graftExitEquiv B C (zeroAcceptedRawOutput keys).1
  let qc := Equiv.cast (congrArg (fun R : MultipartiteSystem Party => R.total) hSystem)
    (zeroAcceptedRawOutput keys).2
  have hforward : G (zeroAcceptedRawOutput keys) =
      ⟨(QKD.BB84.classicalTailExitEquiv 0 0 1 0 (@packedPESel 0 0 0) 0).symm zeroTailData,
        (FinalStage.outputEquiv 1).symm (Sum.inl keys)⟩ := by
    exact G.apply_symm_apply _
  have hforward := (Boundary.graftSpaceEquiv_apply B C _).symm.trans hforward
  have hchild : (⟨z.2, qc⟩ : (FinalStage.boundary 1).space) =
      (FinalStage.outputEquiv 1).symm (Sum.inl keys) :=
    congrArg (fun w : Σ _ : B.Exit, (FinalStage.boundary 1).space => w.2) hforward
  have hflag : z.2.1 = 0 := by
    have h := congrArg (fun w : (FinalStage.boundary 1).space => w.1.1) hchild
    exact h
  change FinalStage.disposition 1 z.2.1 = .accept 1
  simp [FinalStage.disposition, hflag]

theorem zeroAcceptedRawOutput_keys (keys : Bits 1 × Bits 1) :
    let L := (QKD.BB84.rawClassicalTailOutputLayout
      0 0 1 0 (@packedPESel 0 0 0) 0).toBoundaryKeyLayout
    let q := zeroAcceptedRawOutput keys
    let h : L.disposition q.1 = .accept 1 :=
      zeroAcceptedRawOutput_disposition keys
    ((L.acceptCoordinates h q.2).1, (L.acceptCoordinates h q.2).2.1) = keys := by
  dsimp only
  exact rawTail_graft_acceptCoordinates_keys
    0 0 1 0 (@packedPESel 0 0 0) 0
    ((QKD.BB84.classicalTailExitEquiv 0 0 1 0 (@packedPESel 0 0 0) 0).symm zeroTailData)
    keys (zeroAcceptedRawOutput keys).1 (zeroAcceptedRawOutput keys).2 rfl
    (zeroAcceptedRawOutput_disposition keys)

theorem zeroAcceptedRetainedOutput_disposition (keys : Bits 1 × Bits 1) :
    (retainedAnalysisOutputLayout 0 0 0 1 0 0).disposition
        (zeroAcceptedRetainedOutput keys).1 = .accept 1 := by
  let B := retainedAnalysisPrefixBoundary 0
  let C : B.Exit → Boundary Party := fun _ =>
    QKD.BB84.rawClassicalTailBoundary 0 0 1 0 (@packedPESel 0 0 0) 0
  let G := Boundary.graftSpaceEquiv B C
  let z := Boundary.graftExitEquiv B C (zeroAcceptedRetainedOutput keys).1
  let hSystem := Boundary.system_graftExitEquiv B C (zeroAcceptedRetainedOutput keys).1
  let qc := Equiv.cast (congrArg (fun R : MultipartiteSystem Party => R.total) hSystem)
    (zeroAcceptedRetainedOutput keys).2
  have hforward : G (zeroAcceptedRetainedOutput keys) =
      ⟨(retainedAnalysisPrefixExitEquiv 0).symm (Equiv.refl (Fin 0)),
        zeroAcceptedRawOutput keys⟩ := by
    exact G.apply_symm_apply _
  have hforward := (Boundary.graftSpaceEquiv_apply B C _).symm.trans hforward
  have hchild :
      (⟨z.2, qc⟩ :
        (QKD.BB84.rawClassicalTailBoundary 0 0 1 0 (@packedPESel 0 0 0) 0).space) =
        zeroAcceptedRawOutput keys :=
    congrArg (fun w : Σ _ : B.Exit,
      (QKD.BB84.rawClassicalTailBoundary 0 0 1 0 (@packedPESel 0 0 0) 0).space => w.2)
      hforward
  change (QKD.BB84.rawClassicalTailOutputLayout
    0 0 1 0 (@packedPESel 0 0 0) 0).disposition z.2 = .accept 1
  exact (congrArg (fun w :
      (QKD.BB84.rawClassicalTailBoundary 0 0 1 0 (@packedPESel 0 0 0) 0).space =>
        (QKD.BB84.rawClassicalTailOutputLayout
          0 0 1 0 (@packedPESel 0 0 0) 0).disposition w.1) hchild).trans
    (zeroAcceptedRawOutput_disposition keys)

/-- The actual retained output layout reads Alice's key first and Bob's key second from a
literal accepting output. -/
theorem zeroAcceptedRetainedOutput_keys (keys : Bits 1 × Bits 1) :
    let L := (retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout
    let q := zeroAcceptedRetainedOutput keys
    let h : L.disposition q.1 = .accept 1 :=
      zeroAcceptedRetainedOutput_disposition keys
    ((L.acceptCoordinates h q.2).1, (L.acceptCoordinates h q.2).2.1) = keys := by
  let B := retainedAnalysisPrefixBoundary 0
  let R := QKD.BB84.rawClassicalTailBoundary 0 0 1 0 (@packedPESel 0 0 0) 0
  let C : B.Exit → Boundary Party := fun _ => R
  let G := Boundary.graftSpaceEquiv B C
  let q := zeroAcceptedRetainedOutput keys
  let qr := zeroAcceptedRawOutput keys
  let L := (retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout
  let LR := (QKD.BB84.rawClassicalTailOutputLayout
    0 0 1 0 (@packedPESel 0 0 0) 0).toBoundaryKeyLayout
  let h := zeroAcceptedRetainedOutput_disposition keys
  let hr := zeroAcceptedRawOutput_disposition keys
  have hforward : G q =
      ⟨(retainedAnalysisPrefixExitEquiv 0).symm (Equiv.refl (Fin 0)), qr⟩ := by
    exact G.apply_symm_apply _
  -- Key-coordinate transport through the outer graft is exactly the library's general fact about
  -- `OutputLayout.graftFixedParties` (which is literally how `retainedAnalysisOutputLayout` is
  -- built); using it directly avoids re-deriving the same graft induction through raw `cast`.
  have hp : q = G.symm ⟨(retainedAnalysisPrefixExitEquiv 0).symm (Equiv.refl (Fin 0)), qr⟩ :=
    (G.symm_apply_apply q).symm.trans (congrArg G.symm hforward)
  have hkeys := QKD.OutputLayout.graftFixedParties_coordinates_keys_heq
    B C (fun _ => QKD.BB84.rawClassicalTailOutputLayout 0 0 1 0 (@packedPESel 0 0 0) 0)
    Party.alice Party.bob (by decide) (fun _ => rfl) (fun _ => rfl)
    ((retainedAnalysisPrefixExitEquiv 0).symm (Equiv.refl (Fin 0))) qr q hp
  have hAliceMid : (L.coordinates q.1 q.2).1 ≍ (LR.coordinates qr.1 qr.2).1 := hkeys.1
  have hBobMid : (L.coordinates q.1 q.2).2.1 ≍ (LR.coordinates qr.1 qr.2).2.1 := hkeys.2
  have hRawKeys := zeroAcceptedRawOutput_keys keys
  have hrL : LR.disposition qr.1 = .accept 1 := by
    simpa [LR, qr] using hr
  have hL : L.disposition q.1 = .accept 1 := by
    simpa [L, q] using h
  have hRawAlice : (LR.coordinates qr.1 qr.2).1 ≍ keys.1 :=
    (LR.acceptCoordinates_fst_heq_coordinates_fst hrL qr.2).symm.trans
      (heq_of_eq (congrArg Prod.fst hRawKeys))
  have hRawBob : (LR.coordinates qr.1 qr.2).2.1 ≍ keys.2 :=
    (LR.acceptCoordinates_snd_fst_heq_coordinates_snd_fst hrL qr.2).symm.trans
      (heq_of_eq (congrArg (fun w => w.2) hRawKeys))
  -- Named intermediates so each `.trans` step is checked against a known type instead of being
  -- solved as one large nested unification problem inside the closing `exact`.
  have hAliceFull : (L.coordinates q.1 q.2).1 ≍ keys.1 := hAliceMid.trans hRawAlice
  have hBobFull : (L.coordinates q.1 q.2).2.1 ≍ keys.2 := hBobMid.trans hRawBob
  apply Prod.ext
  · exact eq_of_heq ((L.acceptCoordinates_fst_heq_coordinates_fst hL q.2).trans hAliceFull)
  · exact eq_of_heq ((L.acceptCoordinates_snd_fst_heq_coordinates_snd_fst hL q.2).trans hBobFull)

/-- The base residual at a literal accepted retained output is a singleton.  Nontrivial
coherence is therefore tested separately with an external reference register. -/
theorem zeroAcceptedRetainedOutput_residual_subsingleton
    (keys : Bits 1 × Bits 1)
    (u v : (retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout.Residual
      (zeroAcceptedRetainedOutput keys).1) : u = v := by
  change (Unit × Unit) × _ at u v
  apply Prod.ext
  · apply Prod.ext <;> exact Subsingleton.elim _ _
  · funext i
    rcases i with ⟨⟨p, hAlice⟩, hBob⟩
    cases p with
    | alice => exact (hAlice rfl).elim
    | bob =>
        exfalso
        apply hBob
        apply Subtype.ext
        rfl

/-- Literal zero-round abort output for the retained raw tail. -/
def zeroAbortRawOutput :
    RawClassicalTailOutput 0 0 1 0 (@packedPESel 0 0 0) 0 :=
  (Boundary.graftSpaceEquiv
    (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@packedPESel 0 0 0) 0)
    (fun _ => FinalStage.boundary 1)).symm
      ⟨(QKD.BB84.classicalTailExitEquiv 0 0 1 0 (@packedPESel 0 0 0) 0).symm zeroTailData,
        (FinalStage.outputEquiv 1).symm (Sum.inr ())⟩

/-- Literal retained output at the identity public permutation and aborting tail exit. -/
def zeroAbortRetainedOutput :
    (retainedAnalysisBoundary 0 0 0 1 0 0).space :=
  (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0).symm
    (Equiv.refl (Fin 0), zeroAbortRawOutput)

/-- The literal aborting retained output is classified as abort by the actual lifted layout. -/
theorem zeroAbortRetainedOutput_disposition :
    (retainedAnalysisOutputLayout 0 0 0 1 0 0).disposition
        zeroAbortRetainedOutput.1 = .abort := by
  let B0 := QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@packedPESel 0 0 0) 0
  let C0 : B0.Exit → Boundary Party := fun _ => FinalStage.boundary 1
  let G0 := Boundary.graftSpaceEquiv B0 C0
  let z0 := Boundary.graftExitEquiv B0 C0 zeroAbortRawOutput.1
  let hSystem0 := Boundary.system_graftExitEquiv B0 C0 zeroAbortRawOutput.1
  let qc0 := Equiv.cast (congrArg (fun R : MultipartiteSystem Party => R.total)
    hSystem0)
    zeroAbortRawOutput.2
  have hforward0 : G0 zeroAbortRawOutput =
      ⟨(QKD.BB84.classicalTailExitEquiv 0 0 1 0 (@packedPESel 0 0 0) 0).symm zeroTailData,
        (FinalStage.outputEquiv 1).symm (Sum.inr ())⟩ := by
    exact G0.apply_symm_apply _
  have hforward0 := (Boundary.graftSpaceEquiv_apply B0 C0 _).symm.trans hforward0
  have hchild0 : (⟨z0.2, qc0⟩ : (FinalStage.boundary 1).space) =
      (FinalStage.outputEquiv 1).symm (Sum.inr ()) :=
    congrArg (fun w : Σ _ : B0.Exit, (FinalStage.boundary 1).space => w.2) hforward0
  have hflag0 : z0.2.1 = 1 := by
    have hz := congrArg (fun w : (FinalStage.boundary 1).space => w.1.1) hchild0
    exact hz
  have hRawAbort :
      (QKD.BB84.rawClassicalTailOutputLayout
        0 0 1 0 (@packedPESel 0 0 0) 0).disposition zeroAbortRawOutput.1 =
        .abort := by
    change FinalStage.disposition 1 z0.2.1 = .abort
    simp [FinalStage.disposition, hflag0]
  let B := retainedAnalysisPrefixBoundary 0
  let C : B.Exit → Boundary Party := fun _ =>
    QKD.BB84.rawClassicalTailBoundary 0 0 1 0 (@packedPESel 0 0 0) 0
  let G := Boundary.graftSpaceEquiv B C
  let z := Boundary.graftExitEquiv B C zeroAbortRetainedOutput.1
  let hSystem := Boundary.system_graftExitEquiv B C zeroAbortRetainedOutput.1
  let qc := Equiv.cast (congrArg (fun R : MultipartiteSystem Party => R.total) hSystem)
    zeroAbortRetainedOutput.2
  have hforward : G zeroAbortRetainedOutput =
      ⟨(retainedAnalysisPrefixExitEquiv 0).symm (Equiv.refl (Fin 0)),
        zeroAbortRawOutput⟩ := by
    exact G.apply_symm_apply _
  have hforward := (Boundary.graftSpaceEquiv_apply B C _).symm.trans hforward
  have hchild :
      (⟨z.2, qc⟩ :
        (QKD.BB84.rawClassicalTailBoundary 0 0 1 0 (@packedPESel 0 0 0) 0).space) =
        zeroAbortRawOutput :=
    congrArg (fun w : Σ _ : B.Exit,
      (QKD.BB84.rawClassicalTailBoundary 0 0 1 0 (@packedPESel 0 0 0) 0).space => w.2)
      hforward
  change (QKD.BB84.rawClassicalTailOutputLayout
    0 0 1 0 (@packedPESel 0 0 0) 0).disposition z.2 = .abort
  exact (congrArg (fun w :
      (QKD.BB84.rawClassicalTailBoundary 0 0 1 0 (@packedPESel 0 0 0) 0).space =>
        (QKD.BB84.rawClassicalTailOutputLayout
          0 0 1 0 (@packedPESel 0 0 0) 0).disposition w.1) hchild).trans hRawAbort

end QKD.BB84.Reduction.RetainedAnalysisLayoutProbe
