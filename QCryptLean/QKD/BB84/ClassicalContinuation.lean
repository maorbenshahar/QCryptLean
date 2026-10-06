import QCryptLean.QKD.BB84.Program
import QCryptLean.LOCC.Typed.Program.TwoPartyClassicalReplacement
import QCryptLean.QKD.BB84.ClassicalStages
import QCryptLean.QKD.BB84.Measurement.ClassicalityReference
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction

/-!
# Classical continuation certificate for the complete measure-first BB84 program

This module connects the destructive measurement schedule to the actual late-public selection and
classical continuation.  Renner, arXiv:quant-ph/0512258v2, lines 673--736, and Pfister et al.,
arXiv:1506.07502v3, Sections IV--V motivate measurement before public sifting and classical
postprocessing.  The exact recursive certificate and coordinate identities here are properties of
the source-defined program.  They make no sampling-transfer or security claim.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84

open TypedLOCC
open QKD.BB84
open QKD.BB84.Reduction
open QKD.BB84.Engine

/-- Every raw action in the actual late-public selection and complete classical continuation
preserves honest-register diagonality before its continuation.

This is an implementation-specific all-step certificate for the post-measurement processing
motivated by Renner, quant-ph/0512258v2, lines 673--736, and Pfister et al., arXiv:1506.07502v3,
Sections IV--V.
-/
theorem classicalContinuation_isHonestClassical
    (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    (classicalContinuation
      N nK mZ mX ℓ ℓEV leakEC ec delta Q).IsHonestClassical := by
  unfold classicalContinuation
  exact Program.IsHonestClassical.graft
    (latePublicSelectionProgram_isHonestClassical N nK mZ mX)
    (completeContinuation_isHonestClassical
      N nK mZ mX ℓ ℓEV leakEC ec delta Q)

/-- The complete measure-first protocol maps every physical/reference operator to a CQ operator on
the full public output and honest registers.  The reference row and column coordinates remain
independent.  This follows by transporting the CQ records created by the destructive schedule to the
input multipartite system of the certified classical continuation and applying the generic program
CQ theorem; it assumes no positivity, normalization, IID structure, support condition, or positive
round count.

The construction follows the measurement-before-sifting organization discussed by Renner,
quant-ph/0512258v2, lines 673--736, and Pfister et al., arXiv:1506.07502v3, Sections IV--V.
-/
theorem protocol_real_isClassicalOnFirst
    (pA pB : PMF Measurement.Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    {E : Type} [Fintype E] [DecidableEq E]
    (rho : Op ((Measurement.weightedStreamSystem Unit N).total × E)) :
    IsClassicalOnFirst
      (Alpha := (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space)
      (Ref := E)
      (tensorIdLinear E
        (QKD.BB84.protocol
          pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real rho) := by
  unfold QKD.Protocol.real QKD.BB84.protocol
  rw [program_eq_schedule_graft_classicalContinuation]
  exact Program.IsHonestClassical.graft_leaf_denote_tensorId
    (Measurement.weightedMeasurementSchedule pA pB N)
    (classicalContinuation
      N nK mZ mX ℓ ℓEV leakEC ec delta Q)
    (classicalContinuation_isHonestClassical
      N nK mZ mX ℓ ℓEV leakEC ec delta Q)
    rho
    (Measurement.weightedMeasurementSchedule_isClassicalOnFirst pA pB N rho)

/-- Every actual output branch of the complete measure-first protocol is diagonal in Alice's and
Bob's final registers for every complex physical input operator.

This is the reference-free within-exit corollary of the full CQ theorem.  It assumes no positivity,
trace normalization, IID input, or PMF support.
-/
theorem protocol_real_honestRegistersDiagonal
    (pA pB : PMF Measurement.Basis) (N nK mZ mX ℓ ℓEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    ∀ rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total,
      (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).HonestRegistersDiagonal
        ((QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real rho) := by
  intro rho e q q' hdiff
  let rhoRef : Op ((Measurement.weightedStreamSystem Unit N).total × Unit) :=
    fun i j => rho i.1 j.1
  have hclass := protocol_real_isClassicalOnFirst
    pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q rhoRef
  have hne :
      (⟨e, q⟩ : (QKD.BB84.boundary
        N nK mZ mX ℓ ℓEV leakEC).space) ≠ ⟨e, q'⟩ := by
    intro h
    cases h
    exact hdiff.elim (fun ha => ha rfl) (fun hb => hb rfl)
  have hzero := hclass ⟨e, q⟩ ⟨e, q'⟩ () () hne
  exact hzero

/-- The complete output boundary has an inhabited output space, established from its explicit
public exits and terminal registers rather than a caller premise.

At the default raw control the construction exhibits one complete output: on the quota-feasible
branch the all-zero classical tail together with the abort leaf of the final decision, and on the
shortage branch the key-free abort leaf.  Neither branch is excluded and no feasibility assumption
is made. -/
theorem boundary_space_nonempty
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    Nonempty (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space := by
  let omega := Sampling.defaultRawControl N
  let outer : (Measurement.lateSelectionBoundary N nK mZ mX).Exit :=
    (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).symm omega
  have houter : QKD.BB84.lateSelectionExitEquiv N nK mZ mX outer = omega :=
    (QKD.BB84.lateSelectionExitEquiv N nK mZ mX).apply_symm_apply omega
  let qAbort : FinalStage.abortSystem.total :=
    (TwoParty.pairEquiv Unit Unit).symm ((), ())
  by_cases h : Sampling.HasQuotas nK mZ mX omega
  · let d : ClassicalTailData (nK + mZ + mX) (mZ + mX) ℓ ℓEV
        (@Sampling.packedPESel nK mZ mX) leakEC :=
      { alicePE := fun _ => 0
        bobPE := fun _ => 0
        seedPair := (fun _ _ => 0, fun _ _ => 0)
        evTag := 0
        syndrome := 0 }
    let preExit := (classicalTailExitEquiv
      (nK + mZ + mX) (mZ + mX) ℓ ℓEV
      (@Sampling.packedPESel nK mZ mX) leakEC).symm d
    let finalExit : (FinalStage.boundary ℓ).Exit := ⟨1, by
      exact (() : (Boundary.leaf FinalStage.abortSystem).Exit)⟩
    let finalSpace : (FinalStage.boundary ℓ).space := ⟨finalExit, by
      exact qAbort⟩
    let rawSpace :
        (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          (@Sampling.packedPESel nK mZ mX) leakEC).space :=
      (Boundary.graftSpaceEquiv _ _).symm ⟨preExit, finalSpace⟩
    have hquota : Sampling.HasQuotas nK mZ mX
        (QKD.BB84.lateSelectionExitEquiv N nK mZ mX outer) := by
      simpa [houter] using h
    have hC : QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC outer =
        QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ℓ ℓEV
          (@Sampling.packedPESel nK mZ mX) leakEC := by
      simp [QKD.BB84.completeContinuationBoundary, hquota]
    let innerSpace : (QKD.BB84.completeContinuationBoundary
        N nK mZ mX ℓ ℓEV leakEC outer).space :=
      cast (congrArg Boundary.space hC.symm) rawSpace
    let q : (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space :=
      (Boundary.graftSpaceEquiv _ _).symm ⟨outer, innerSpace⟩
    exact ⟨q⟩
  · have hquota : ¬Sampling.HasQuotas nK mZ mX
        (QKD.BB84.lateSelectionExitEquiv N nK mZ mX outer) := by
      simpa [houter] using h
    have hC : QKD.BB84.completeContinuationBoundary N nK mZ mX ℓ ℓEV leakEC outer =
        .leaf FinalStage.abortSystem := by
      simp [QKD.BB84.completeContinuationBoundary, hquota]
    let abortSpace : (Boundary.leaf FinalStage.abortSystem).space :=
      (Boundary.leafSpaceEquiv FinalStage.abortSystem).symm qAbort
    let innerSpace : (QKD.BB84.completeContinuationBoundary
        N nK mZ mX ℓ ℓEV leakEC outer).space :=
      cast (congrArg Boundary.space hC.symm) abortSpace
    let q : (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space :=
      (Boundary.graftSpaceEquiv _ _).symm ⟨outer, innerSpace⟩
    exact ⟨q⟩

/-- The complete output boundary declares an inhabited public exit.

This is the structural fact the coordinate-free security interface needs: it is derived from the
construction above, never assumed of an arbitrary boundary. -/
instance boundaryExitNonempty
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    Nonempty (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).Exit :=
  (boundary_space_nonempty N nK mZ mX ℓ ℓEV leakEC).elim fun q => ⟨q.1⟩

/-- The complete output boundary has a nonzero finite coordinate cardinality. -/
theorem boundary_card_ne_zero
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    Fintype.card
      (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space ≠ 0 :=
  Fintype.card_ne_zero

/-- Internal coordinate evidence for the explicit complete output boundary. -/
theorem boundaryCardNeZero
    (N nK mZ mX ℓ ℓEV leakEC : ℕ) :
    NeZero (Fintype.card
      (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space) :=
  ⟨boundary_card_ne_zero N nK mZ mX ℓ ℓEV leakEC⟩

attribute [local instance] Measurement.weightedStreamInputCardNeZero
attribute [local instance] boundaryCardNeZero

/-- Honest-register off-diagonal entries remain zero after adjoining an arbitrary finite
reference, while the reference row and column indices remain independent.

The physical program has no reference parameter.  This is the finite-coordinate `mapTensorId`
form of the common full CQ endpoint theorem, not a security or sampling theorem.
-/
theorem protocol_real_honestRegistersDiagonal_mapTensorId
    (pA pB : PMF Measurement.Basis) (N nK mZ mX ℓ ℓEV leakEC k : ℕ)
    [NeZero k]
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (W : Quantum.Operators.Op
      (Fintype.card (Measurement.weightedStreamSystem Unit N).total * k))
    (e : (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).Exit)
    (q q' : ((QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).system e).total)
    (s t : Fin k)
    (hdiff : q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob) :
    let eIn := Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total
    let eOut := Fintype.equivFin
      (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space
    Quantum.Channels.mapTensorId
        (coordinateLinear eIn eOut
          (QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real) W
        (finProdFinEquiv (eOut ⟨e, q⟩, s))
        (finProdFinEquiv (eOut ⟨e, q'⟩, t)) = 0 := by
  dsimp only
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  simp only [Equiv.symm_apply_apply]
  let rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total := fun i j =>
    W (finProdFinEquiv
        (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total i, s))
      (finProdFinEquiv
        (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total j, t))
  have hblock :
      (Matrix.of fun i j => W (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))) =
        Matrix.reindex
          (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total)
          (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total) rho := by
    ext i j
    exact congrArg₂ (fun a b => W (finProdFinEquiv (a, s)) (finProdFinEquiv (b, t)))
      ((Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total).apply_symm_apply i).symm
      ((Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total).apply_symm_apply j).symm
  rw [hblock]
  calc
    coordinateLinear
          (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total)
          (Fintype.equivFin
            (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space)
          (QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real
          (Matrix.reindex
            (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total)
            (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total) rho)
          (Fintype.equivFin
            (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space ⟨e, q⟩)
          (Fintype.equivFin
            (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space ⟨e, q'⟩) =
        (QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real rho
          ⟨e, q⟩ ⟨e, q'⟩ := by
      exact coordinateLinear_reindex_apply
          (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total)
          (Fintype.equivFin
            (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space)
          (QKD.BB84.protocol
            pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real rho ⟨e, q⟩ ⟨e, q'⟩
    _ = 0 := by
      let rhoRef : Op
          ((Measurement.weightedStreamSystem Unit N).total × Fin k) := fun i j =>
        W (finProdFinEquiv
            (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total i.1, i.2))
          (finProdFinEquiv
            (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total j.1, j.2))
      have hne :
          (⟨e, q⟩ : (QKD.BB84.boundary
            N nK mZ mX ℓ ℓEV leakEC).space) ≠ ⟨e, q'⟩ := by
        intro h
        cases h
        exact hdiff.elim (fun ha => ha rfl) (fun hb => hb rfl)
      have hzero := protocol_real_isClassicalOnFirst
        pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q rhoRef
        ⟨e, q⟩ ⟨e, q'⟩ s t hne
      exact hzero

/-- Entries between distinct complete public exits remain zero after adjoining an arbitrary finite
reference, again with independent reference row and column indices.

This is the finite-coordinate `mapTensorId` form of the common full CQ endpoint theorem for
distinct public exits; it makes no claim that the reference itself is classical.
-/
theorem protocol_real_exitBlockDiagonal_mapTensorId
    (pA pB : PMF Measurement.Basis) (N nK mZ mX ℓ ℓEV leakEC k : ℕ)
    [NeZero k]
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (W : Quantum.Operators.Op
      (Fintype.card (Measurement.weightedStreamSystem Unit N).total * k))
    (e f : (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).Exit)
    (q : ((QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).system e).total)
    (q' : ((QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).system f).total)
    (s t : Fin k) (hef : e ≠ f) :
    let eIn := Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total
    let eOut := Fintype.equivFin
      (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space
    Quantum.Channels.mapTensorId
        (coordinateLinear eIn eOut
          (QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real) W
        (finProdFinEquiv (eOut ⟨e, q⟩, s))
        (finProdFinEquiv (eOut ⟨f, q'⟩, t)) = 0 := by
  dsimp only
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  simp only [Equiv.symm_apply_apply]
  let rho : TypedLOCC.Op (Measurement.weightedStreamSystem Unit N).total := fun i j =>
    W (finProdFinEquiv
        (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total i, s))
      (finProdFinEquiv
        (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total j, t))
  have hblock :
      (Matrix.of fun i j => W (finProdFinEquiv (i, s)) (finProdFinEquiv (j, t))) =
        Matrix.reindex
          (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total)
          (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total) rho := by
    ext i j
    exact congrArg₂ (fun a b => W (finProdFinEquiv (a, s)) (finProdFinEquiv (b, t)))
      ((Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total).apply_symm_apply i).symm
      ((Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total).apply_symm_apply j).symm
  rw [hblock]
  calc
    coordinateLinear
          (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total)
          (Fintype.equivFin
            (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space)
          (QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real
          (Matrix.reindex
            (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total)
            (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total) rho)
          (Fintype.equivFin
            (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space ⟨e, q⟩)
          (Fintype.equivFin
            (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space ⟨f, q'⟩) =
        (QKD.BB84.protocol pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real rho
          ⟨e, q⟩ ⟨f, q'⟩ := by
      exact coordinateLinear_reindex_apply
          (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total)
          (Fintype.equivFin
            (QKD.BB84.boundary N nK mZ mX ℓ ℓEV leakEC).space)
          (QKD.BB84.protocol
            pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q).real rho ⟨e, q⟩ ⟨f, q'⟩
    _ = 0 := by
      let rhoRef : Op
          ((Measurement.weightedStreamSystem Unit N).total × Fin k) := fun i j =>
        W (finProdFinEquiv
            (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total i.1, i.2))
          (finProdFinEquiv
            (Fintype.equivFin (Measurement.weightedStreamSystem Unit N).total j.1, j.2))
      have hne :
          (⟨e, q⟩ : (QKD.BB84.boundary
            N nK mZ mX ℓ ℓEV leakEC).space) ≠ ⟨f, q'⟩ := by
        intro h
        exact hef (congrArg Sigma.fst h)
      have hzero := protocol_real_isClassicalOnFirst
        pA pB N nK mZ mX ℓ ℓEV leakEC ec delta Q rhoRef
        ⟨e, q⟩ ⟨f, q'⟩ s t hne
      exact hzero

end QKD.BB84
