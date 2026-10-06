import QCryptLean.QKD.BB84.Program

/-!
# The classical-tail output of the BB84 program

The classical tail `rawClassicalTailProgram` announces the pre-decision public cells and then the
final accept/abort flag. Its output boundary is `rawClassicalTailBoundary`. The complete output
space `RawClassicalTailOutput` pairs a public exit with the local registers at that exit: the
ordered accepted key pair after an accepting flag, and a key-free `Unit` payload after an aborting
one.

* `finalStageExitEquiv` reads a final-stage exit as its `Fin 2` flag, and `finalStageOutputEquiv`
  reads a final-stage output as `(Fin (2 ^ ℓ) × Fin (2 ^ ℓ)) ⊕ Unit`, Alice's key first.
* `rawClassicalTailExitDataEquiv` decodes a complete tail exit into the pre-decision data
  `ClassicalTailData` and the final flag; no public cell is discarded.
* `rawClassicalTail_graftSpaceEquiv_symm_inl_acceptCoordinates_keys`: at an accepting point, the
  tail's output layout reads exactly the ordered key pair of the final stage.

`finalStageExitEquiv` has the type of `QKD.BB84.FinalStage.exitEquiv`, and
`rawClassicalTailExitDataEquiv` that of `rawClassicalTailExitEquiv`
(`QCryptLean.QKD.BB84.Chronology`); their inverses select the unique leaf exit by
`finalStageLeafExit` rather than by `default`.  The complete program's output over this tail is
described in `QCryptLean.QKD.BB84.CompleteOutput`.

In Nahar et al., arXiv:2403.11851, source lines 394--400, the key registers of an aborted run hold
a special symbol; here an aborted run has no key register.
-/

noncomputable section

namespace QKD.BB84

open TypedLOCC QKD.BB84 TypedLOCC.TwoParty

/-- The complete output space of the raw classical tail. -/
abbrev RawClassicalTailOutput
    (n m ell ellEV : Nat) (peSel : Fin n -> Bool) (leakEC : Nat) :=
  (QKD.BB84.rawClassicalTailBoundary n m ell ellEV peSel leakEC).space

/-- The unique leaf exit selected by one final semantic flag. -/
def finalStageLeafExit (ell : Nat) (flag : Fin 2) :
    (FinalStage.flagBoundary ell flag).Exit := by
  unfold FinalStage.flagBoundary
  split <;> exact ()

/-- The final flag leaf has only one exit. -/
@[simp] theorem finalStageLeafExit_eq (ell : Nat) (flag : Fin 2)
    (e : (FinalStage.flagBoundary ell flag).Exit) :
    finalStageLeafExit ell flag = e := by
  by_cases hflag : flag = 0
  · subst flag
    exact Unit.ext _ _
  · have hflag_one : flag = 1 := Fin.eq_one_of_ne_zero flag hflag
    subst flag
    change (finalStageLeafExit ell 1 : Unit) = e
    exact Unit.ext _ _

/-- The direct final-stage public exit is its semantic `Fin 2` flag. -/
def finalStageExitEquiv (ell : Nat) :
    (FinalStage.boundary ell).Exit ≃ Fin 2 where
  toFun e := e.1
  invFun flag := ⟨flag, finalStageLeafExit ell flag⟩
  left_inv e := by
    rcases e with ⟨flag, leaf⟩
    have hleaf := finalStageLeafExit_eq ell flag leaf
    cases hleaf
    rfl
  right_inv _ := rfl

/-- Complete raw-tail exits are the decoded predecision data paired with the final semantic
flag.  No public cell is discarded. -/
noncomputable def rawClassicalTailExitDataEquiv
    (n m ell ellEV : Nat) (peSel : Fin n -> Bool) (leakEC : Nat) :
    (QKD.BB84.rawClassicalTailBoundary n m ell ellEV peSel leakEC).Exit ≃
      QKD.BB84.ClassicalTailData n m ell ellEV peSel leakEC × Fin 2 where
  toFun e :=
    let z := Boundary.graftExitEquiv
      (QKD.BB84.classicalPreDecisionBoundary n m ell ellEV peSel leakEC)
      (fun _ => FinalStage.boundary ell) e
    (QKD.BB84.classicalTailExitEquiv n m ell ellEV peSel leakEC z.1,
      finalStageExitEquiv ell z.2)
  invFun q :=
    (Boundary.graftExitEquiv
      (QKD.BB84.classicalPreDecisionBoundary n m ell ellEV peSel leakEC)
      (fun _ => FinalStage.boundary ell)).symm
        ⟨(QKD.BB84.classicalTailExitEquiv n m ell ellEV peSel leakEC).symm q.1,
          (finalStageExitEquiv ell).symm q.2⟩
  left_inv e := by
    simp only [Equiv.symm_apply_apply]
    exact Equiv.symm_apply_apply _ e
  right_inv q := by
    rcases q with ⟨data, flag⟩
    simp

/-- The direct final-stage heterogeneous output as the accepted-key-pair-or-abort payload. Both
directions use the literal Alice/Bob final multipartite systems. -/
def finalStageOutputEquiv (ell : Nat) :
    (FinalStage.boundary ell).space ≃
      (Fin (2 ^ ell) × Fin (2 ^ ell)) ⊕ Unit where
  toFun q := by
    rcases q with ⟨⟨flag, leaf⟩, registers⟩
    by_cases hflag : flag = 0
    · subst flag
      change Unit at leaf
      cases leaf
      exact Sum.inl (TwoParty.pairEquiv (Fin (2 ^ ell)) (Fin (2 ^ ell)) registers)
    · have hflag_one : flag = 1 := Fin.eq_one_of_ne_zero flag hflag
      subst flag
      change Unit at leaf
      cases leaf
      exact Sum.inr ()
  invFun q := by
    rcases q with keys | abort
    · exact ⟨⟨0, finalStageLeafExit ell 0⟩,
        (TwoParty.pairEquiv (Fin (2 ^ ell)) (Fin (2 ^ ell))).symm keys⟩
    · cases abort
      exact ⟨⟨1, finalStageLeafExit ell 1⟩, fun p => by cases p <;> exact ()⟩
  left_inv q := by
    rcases q with ⟨⟨flag, leaf⟩, registers⟩
    by_cases hflag : flag = 0
    · subst flag
      change Unit at leaf
      cases leaf
      have hzero : finalStageLeafExit ell 0 = () :=
        finalStageLeafExit_eq ell 0 ()
      rw [hzero]
      change (⟨⟨0, ()⟩,
        (TwoParty.pairEquiv (Fin (2 ^ ell)) (Fin (2 ^ ell))).symm
          (TwoParty.pairEquiv (Fin (2 ^ ell)) (Fin (2 ^ ell)) registers)⟩ :
            (FinalStage.boundary ell).space) = ⟨⟨0, ()⟩, registers⟩
      exact congrArg (fun q : (FinalStage.keySystem ell).total =>
        (⟨⟨0, ()⟩, q⟩ : (FinalStage.boundary ell).space))
        ((TwoParty.pairEquiv (Fin (2 ^ ell)) (Fin (2 ^ ell))).symm_apply_apply registers)
    · have hflag_one : flag = 1 := Fin.eq_one_of_ne_zero flag hflag
      subst flag
      change Unit at leaf
      cases leaf
      have hone : finalStageLeafExit ell 1 = () :=
        finalStageLeafExit_eq ell 1 ()
      rw [hone]
      change (⟨⟨1, ()⟩, (fun p => by cases p <;> exact ())⟩ :
        (FinalStage.boundary ell).space) = ⟨⟨1, ()⟩, registers⟩
      have hregisters : (fun p => by cases p <;> exact ()) = registers := by
        funext p
        cases p <;> exact Unit.ext _ _
      rw [hregisters]
  right_inv q := by
    rcases q with keys | abort
    · exact congrArg Sum.inl
        ((TwoParty.pairEquiv (Fin (2 ^ ell)) (Fin (2 ^ ell))).apply_symm_apply keys)
    · cases abort
      rfl

/-- Transporting a literal accepted final-stage point through the raw-tail graft preserves its
ordered Alice and Bob key coordinates. -/
theorem rawClassicalTail_graftSpaceEquiv_symm_inl_acceptCoordinates_keys
    (n m ℓ ℓEV : ℕ) (peSel : Fin n → Bool) (leakEC : ℕ)
    (e : (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC).Exit)
    (keys : Fin (2 ^ ℓ) × Fin (2 ^ ℓ))
    (g : (QKD.BB84.rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).Exit)
    (q : ((QKD.BB84.rawClassicalTailBoundary n m ℓ ℓEV peSel leakEC).system g).total)
    (hpoint :
      (Boundary.graftSpaceEquiv
          (QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC)
          (fun _ => FinalStage.boundary ℓ)).symm
          ⟨e, (finalStageOutputEquiv ℓ).symm (Sum.inl keys)⟩ =
        ⟨g, q⟩)
    (haccept :
      (QKD.BB84.rawClassicalTailOutputLayout
          n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout.disposition g =
        .accept ℓ) :
    let L := (QKD.BB84.rawClassicalTailOutputLayout
      n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout
    ((L.acceptCoordinates haccept q).1,
      (L.acceptCoordinates haccept q).2.1) = keys := by
  let B := QKD.BB84.classicalPreDecisionBoundary n m ℓ ℓEV peSel leakEC
  let C : B.Exit → Boundary TwoParty.Party := fun _ => FinalStage.boundary ℓ
  let G := Boundary.graftSpaceEquiv B C
  let z := Boundary.graftExitEquiv B C g
  let hSystem := Boundary.system_graftExitEquiv B C g
  let qc := Equiv.cast (congrArg (fun R : MultipartiteSystem TwoParty.Party => R.total) hSystem) q
  let L := (QKD.BB84.rawClassicalTailOutputLayout n m ℓ ℓEV peSel leakEC).toBoundaryKeyLayout
  have hforward : G ⟨g, q⟩ = ⟨e, (finalStageOutputEquiv ℓ).symm (Sum.inl keys)⟩ := by
    rw [← hpoint]
    exact G.apply_symm_apply _
  rw [Boundary.graftSpaceEquiv_apply] at hforward
  have hchild : (⟨z.2, qc⟩ : (FinalStage.boundary ℓ).space) =
      (finalStageOutputEquiv ℓ).symm (Sum.inl keys) :=
    congrArg (fun w : Σ _ : B.Exit, (FinalStage.boundary ℓ).space => w.2) hforward
  have castSplit_apply {R S : MultipartiteSystem TwoParty.Party} (h : R = S)
      (p : TwoParty.Party) {K A : Type} (E : S.reg p ≃ K × A) (r : R.total) :
      (cast (congrArg (fun D : MultipartiteSystem TwoParty.Party => D.reg p ≃ K × A) h.symm) E)
          (r p) =
        E ((Equiv.cast (congrArg (fun D : MultipartiteSystem TwoParty.Party => D.total) h) r) p)
          := by
    cases h
    rfl
  have graftKeys (D : Boundary TwoParty.Party)
      (v : (D.graft (fun _ => FinalStage.boundary ℓ)).Exit)
      (r : ((D.graft (fun _ => FinalStage.boundary ℓ)).system v).total) :
      let LD := QKD.OutputLayout.graftFixedParties .alice .bob (by decide)
        (fun _ : D.Exit => FinalStage.outputLayout ℓ) (fun _ => rfl) (fun _ => rfl)
      let w := Boundary.graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v
      let rc := Equiv.cast (congrArg (fun R : MultipartiteSystem TwoParty.Party => R.total)
        (Boundary.system_graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v)) r
      (LD.coordinates v r).1 = ((FinalStage.outputLayout ℓ).coordinates w.2 rc).1 ∧
        (LD.coordinates v r).2.1 = ((FinalStage.outputLayout ℓ).coordinates w.2 rc).2.1 := by
    constructor
    · exact congrArg Prod.fst
        (castSplit_apply (Boundary.system_graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v)
          .alice ((FinalStage.outputLayout ℓ).aliceSplit
            (Boundary.graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v).2) r)
    · exact congrArg Prod.fst
        (castSplit_apply (Boundary.system_graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v)
          .bob ((FinalStage.outputLayout ℓ).bobSplit
            (Boundary.graftExitEquiv D (fun _ => FinalStage.boundary ℓ) v).2) r)
  have hAlice : (L.coordinates g q).1 =
      ((FinalStage.outputLayout ℓ).coordinates z.2 qc).1 := by
    exact (graftKeys B g q).1
  have hBob : (L.coordinates g q).2.1 =
      ((FinalStage.outputLayout ℓ).coordinates z.2 qc).2.1 := by
    exact (graftKeys B g q).2
  have hAliceKeys : ((FinalStage.outputLayout ℓ).coordinates z.2 qc).1 ≍ keys.1 := by
    have h := congr_arg_heq
      (fun w : (FinalStage.boundary ℓ).space =>
        ((FinalStage.outputLayout ℓ).coordinates w.1 w.2).1) hchild
    exact h
  have hBobKeys : ((FinalStage.outputLayout ℓ).coordinates z.2 qc).2.1 ≍ keys.2 := by
    have h := congr_arg_heq
      (fun w : (FinalStage.boundary ℓ).space =>
        ((FinalStage.outputLayout ℓ).coordinates w.1 w.2).2.1) hchild
    exact h
  apply Prod.ext
  · exact eq_of_heq
      ((L.acceptCoordinates_fst_heq_coordinates_fst haccept q).trans
        ((heq_of_eq hAlice).trans hAliceKeys))
  · exact eq_of_heq
      ((L.acceptCoordinates_snd_fst_heq_coordinates_snd_fst haccept q).trans
        ((heq_of_eq hBob).trans hBobKeys))

end QKD.BB84
