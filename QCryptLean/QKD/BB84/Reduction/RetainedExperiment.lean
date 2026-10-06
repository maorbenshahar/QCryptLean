import QCryptLean.QKD.BB84.Reduction.Preprocessor
import QCryptLean.QKD.BB84.Reduction.SymmetrizationPrefix
import QCryptLean.InfoTheory.Postselection.PairedBlockedTransport
import QCryptLean.Quantum.Channels.CPTP.CKRBound.GeneralContractivity
import QCryptLean.Quantum.Channels.CPTP.Reindex
import QCryptLean.QKD.BB84.Program

/-!
# Direct retained-block analysis map

This module constructs the retained-`n` experiment without the outer basis-string and selection
weights used by the direct memory-free BB84 security route.  It samples and announces one inner
permutation, applies the actual local packed-basis operators, privately measures Alice and then
Bob, and runs the literal retained classical tail with its internal randomness.  The output
coordinate retains the permutation and the entire raw-tail output.

Christandl--König--Renner, arXiv:0809.3019, Theorem 1 and Lemma 1, and Renner,
arXiv:quant-ph/0512258v2, Section 6.5, motivate the retained-block security architecture.  The
typed program, coordinates, and boundary-derived ideal resource are implementation-specific
finite constructions.
-/

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Reduction
open TypedLOCC

open TypedLOCC.TwoParty
open QKD.BB84.Engine
open Measurement Sampling

/-- Public inner-permutation prefix, including Bob's literal singleton announcement. -/
def retainedAnalysisPrefixBoundary (n : ℕ) : Boundary Party :=
  .announce (Equiv.Perm (Fin n)) fun _ =>
    .announce Unit fun _ => .leaf (FinalStage.rawSystem n)

/-- Uniform inner permutation followed by actual private Alice-then-Bob measurement.

The prefix is the finite public symmetrization in Christandl--König--Renner,
arXiv:0809.3019, Theorem 1 and Lemma 1, implemented by the existing typed local actions. -/
noncomputable def retainedAnalysisPrefix
    (n : ℕ) (peSel xSel : Fin n → Bool) :
    Program (FinalStage.rawSystem n) (retainedAnalysisPrefixBoundary n) :=
  QKD.BB84.Reduction.permutationStage n peSel xSel fun _ =>
    QKD.BB84.Reduction.privateMeasurements n Program.done

/-- Prefix public exits are exactly the announced inner permutations; the intervening public
`Unit` and terminal `Unit` are retained by the inverse map. -/
def retainedAnalysisPrefixExitEquiv (n : ℕ) :
    (retainedAnalysisPrefixBoundary n).Exit ≃ Equiv.Perm (Fin n) where
  toFun e := e.1
  invFun pi := ⟨pi, ⟨(), ()⟩⟩
  left_inv e := by
    rcases e with ⟨pi, ⟨u, v⟩⟩
    cases u
    cases v
    rfl
  right_inv _ := rfl

/-- Full retained experiment boundary: public inner permutation followed by every actual
PE/fused/final tail exit. -/
def retainedAnalysisBoundary
    (nK mZ mX ell ellEV leakEC : ℕ) : Boundary Party :=
  (retainedAnalysisPrefixBoundary (nK + mZ + mX)).graft fun _ =>
    QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC

/-- The unweighted retained experiment.

Outer basis-string and selection probabilities are absent: they belong to the later physical
factorization.  Each inner permutation is weighted exactly once, and the literal measure-first
BB84 continuation retains its own hash and error-verification seed randomness.  The construction
is motivated by Renner, arXiv:quant-ph/0512258v2, Section 6.5. -/
noncomputable def retainedAnalysisProgram
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Program (FinalStage.rawSystem (nK + mZ + mX))
      (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC) :=
  (retainedAnalysisPrefix (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX)
      (@Sampling.packedXSel nK mZ mX)).graft fun e => by
    rcases e with ⟨pi, ⟨u, v⟩⟩
    cases u
    cases v
    exact QKD.BB84.rawClassicalTailProgram (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX)
      (@Sampling.packedXSel nK mZ mX) leakEC ec delta Q

/-- Actual ordered local-key layout lifted through the public inner-permutation prefix. -/
noncomputable def retainedAnalysisOutputLayout
    (nK mZ mX ell ellEV leakEC : ℕ) :
    QKD.OutputLayout (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC) :=
  QKD.OutputLayout.graftFixedParties .alice .bob (by decide)
    (fun _ => QKD.BB84.rawClassicalTailOutputLayout
      (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (fun _ => rfl) (fun _ => rfl)

/-- Explicit output decomposition into the public inner permutation and the complete raw-tail
output.  Bob's singleton cell is eliminated only through the explicit bijection
`retainedAnalysisPrefixExitEquiv`. -/
noncomputable def retainedAnalysisOutputDataEquiv
    (nK mZ mX ell ellEV leakEC : ℕ) :
    (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space ≃
      Equiv.Perm (Fin (nK + mZ + mX)) ×
        (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
          (@Sampling.packedPESel nK mZ mX) leakEC).space := by
  let G := Boundary.graftSpaceEquiv
    (retainedAnalysisPrefixBoundary (nK + mZ + mX))
    (fun _ => QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
  exact
    { toFun := fun q =>
        let z := G q
        (retainedAnalysisPrefixExitEquiv _ z.1, z.2)
      invFun := fun z =>
        G.symm ⟨(retainedAnalysisPrefixExitEquiv _).symm z.1, z.2⟩
      left_inv := by
        intro q
        dsimp only
        rw [(retainedAnalysisPrefixExitEquiv _).symm_apply_apply]
        exact G.symm_apply_apply q
      right_inv := by
        intro z
        rcases z with ⟨pi, q⟩
        dsimp only
        rw [G.apply_symm_apply, (retainedAnalysisPrefixExitEquiv _).apply_symm_apply] }

/-- The complete tail output over one announced inner permutation is a morphism of key layouts
from the retained-tail layout to the retained-analysis layout: the inclusion of that permutation's
continuation into the grafted output. -/
noncomputable def retainedAnalysisFibreHom
    (nK mZ mX ell ellEV leakEC : ℕ) (pi : Equiv.Perm (Fin (nK + mZ + mX))) :
    BoundaryKeyLayout.Hom
      (QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ell ellEV
        (@Sampling.packedPESel nK mZ mX) leakEC).toBoundaryKeyLayout
      (retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout :=
  QKD.OutputLayout.graftInclHom (retainedAnalysisPrefixBoundary (nK + mZ + mX))
    (fun _ => QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (fun _ => QKD.BB84.rawClassicalTailOutputLayout (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    .alice .bob (by decide) (fun _ => rfl) (fun _ => rfl)
    ((retainedAnalysisPrefixExitEquiv (nK + mZ + mX)).symm pi)

/-- The fibre morphism of an announced permutation reads the explicit output decomposition. -/
@[simp] theorem coe_retainedAnalysisFibreHom
    (nK mZ mX ell ellEV leakEC : ℕ) (pi : Equiv.Perm (Fin (nK + mZ + mX))) :
    ⇑(retainedAnalysisFibreHom nK mZ mX ell ellEV leakEC pi) =
      fun w => (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm (pi, w) :=
  rfl

/-- Numeral output dimension with the permutation and complete tail factors visible. -/
abbrev RetainedAnalysisOutputDim
    (nK mZ mX ell ellEV leakEC : ℕ) :=
  Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) *
    Fintype.card (QKD.BB84.rawClassicalTailBoundary
      (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).space

/-- Explicit numeral coordinates for the permutation-times-complete-tail output. -/
noncomputable def retainedAnalysisOutputEquiv
    (nK mZ mX ell ellEV leakEC : ℕ) :
    (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space ≃
      Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) :=
  (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).trans
    ((Equiv.prodCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans
      finProdFinEquiv)

/-- Alice/Bob-block coordinates of the actual retained input multipartite system. -/
def retainedAnalysisBlockInputEquiv (n : ℕ) :
    (FinalStage.rawSystem n).total ≃ Fin (2 ^ n * 2 ^ n) :=
  (TwoParty.pairEquiv (Fin (2 ^ n)) (Fin (2 ^ n))).trans finProdFinEquiv

/-- Selected bit strings embedded into the round-grouped `4^n` convention. -/
def retainedSelectedPairToRoundEquiv (n : ℕ) :
    ((Fin n → Bit) × (Fin n → Bit)) ≃ Fin (4 ^ n) :=
  (selectedPairNumeralEquiv n).trans
    (Equiv.roundGroupEquiv 2 2 n).symm

/-- Genuine round-grouped-to-Alice/Bob-block operator reindex.

This is the digit regrouping used by the CKR reduction, not a cast along equal cardinalities. -/
def retainedAnalysisRoundToBlock (n : ℕ) :
    Quantum.Operators.Op (4 ^ n) →ₗ[ℂ]
      Quantum.Operators.Op (2 ^ n * 2 ^ n) :=
  (Matrix.reindexLinearEquiv ℂ ℂ
    (Equiv.roundGroupEquiv 2 2 n)
    (Equiv.roundGroupEquiv 2 2 n)).toLinearMap

/-- Explicit zero-valued semantic transcript used to inhabit the raw-tail output space. -/
def retainedAnalysisDefaultTailData
    (nK mZ mX ell ellEV leakEC : ℕ) :
    QKD.BB84.ClassicalTailData (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC where
  alicePE := fun _ => 0
  bobPE := fun _ => 0
  seedPair := (fun _ _ => 0, fun _ _ => 0)
  evTag := 0
  syndrome := 0

/-- Explicit abort output used only to certify that the raw-tail output type is inhabited. -/
noncomputable def retainedAnalysisDefaultRawTailOutput
    (nK mZ mX ell ellEV leakEC : ℕ) :
    (QKD.BB84.rawClassicalTailBoundary (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).space :=
  let d := retainedAnalysisDefaultTailData nK mZ mX ell ellEV leakEC
  let preExit := (QKD.BB84.classicalTailExitEquiv
    (nK + mZ + mX) (mZ + mX) ell ellEV
    (@Sampling.packedPESel nK mZ mX) leakEC).symm d
  let qAbort : FinalStage.abortSystem.total :=
    (TwoParty.pairEquiv Unit Unit).symm ((), ())
  let finalExit : (FinalStage.boundary ell).Exit := ⟨1, by
    simpa [FinalStage.flagBoundary] using
      (() : (Boundary.leaf FinalStage.abortSystem).Exit)⟩
  let finalSpace : (FinalStage.boundary ell).space := ⟨finalExit, by
    simpa [finalExit, FinalStage.flagBoundary] using qAbort⟩
  (Boundary.graftSpaceEquiv _ _).symm ⟨preExit, finalSpace⟩

/-- The round-grouped input dimension is nonzero for every retained size. -/
def retainedAnalysisRoundDimNeZero (n : ℕ) : NeZero (4 ^ n) :=
  ⟨pow_ne_zero _ (by decide)⟩

/-- The Alice/Bob-block input dimension is nonzero for every retained size. -/
def retainedAnalysisBlockDimNeZero (n : ℕ) : NeZero (2 ^ n * 2 ^ n) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide))⟩

/-- The explicit permutation-times-tail output dimension is nonzero. -/
def retainedAnalysisOutputDimNeZero
    (nK mZ mX ell ellEV leakEC : ℕ) :
    NeZero (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) := by
  letI : Nonempty (Equiv.Perm (Fin (nK + mZ + mX))) :=
    ⟨Equiv.refl _⟩
  letI : Nonempty (QKD.BB84.rawClassicalTailBoundary
      (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC).space :=
    ⟨retainedAnalysisDefaultRawTailOutput nK mZ mX ell ellEV leakEC⟩
  exact ⟨Nat.mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero⟩

attribute [local instance] retainedAnalysisRoundDimNeZero
attribute [local instance] retainedAnalysisBlockDimNeZero
attribute [local instance] retainedAnalysisOutputDimNeZero

/-- Numeral real map of the unweighted retained experiment. -/
noncomputable def retainedAnalysisReal
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Quantum.Operators.Op (4 ^ (nK + mZ + mX)) →ₗ[ℂ]
      Quantum.Operators.Op
        (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) :=
  (coordinateLinear (retainedAnalysisBlockInputEquiv (nK + mZ + mX))
      (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)
      (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).denote).comp
    (retainedAnalysisRoundToBlock (nK + mZ + mX))

/-- Numeral full-complete-exit ideal-key resource of the retained experiment. -/
noncomputable def retainedAnalysisResource
    (nK mZ mX ell ellEV leakEC : ℕ) :
    Quantum.Operators.Op
        (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) →ₗ[ℂ]
      Quantum.Operators.Op
        (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) :=
  coordinateLinear
    (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)
    (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)
    (retainedAnalysisOutputLayout
      nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal

/-- Entry of the numeral retained resource at explicitly numbered output points. -/
theorem retainedAnalysisResource_entry
    (nK mZ mX ell ellEV leakEC : ℕ)
    (M : Quantum.Operators.Op (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC))
    (x y : (retainedAnalysisBoundary nK mZ mX ell ellEV leakEC).space) :
    retainedAnalysisResource nK mZ mX ell ellEV leakEC M
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC x)
        (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC y) =
      (retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout.ideal
        (M.submatrix (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)
          (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)) x y := by
  rw [retainedAnalysisResource, coordinateLinear_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

/-- Retained ideal map: the actual full-exit key resource after the retained real map. -/
noncomputable def retainedAnalysisIdeal
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Quantum.Operators.Op (4 ^ (nK + mZ + mX)) →ₗ[ℂ]
      Quantum.Operators.Op
        (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) :=
  (retainedAnalysisResource nK mZ mX ell ellEV leakEC).comp
    (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)

/-- Retained real-minus-ideal map. -/
noncomputable def retainedAnalysisDifference
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (delta Q : ℝ) :
    Quantum.Operators.Op (4 ^ (nK + mZ + mX)) →ₗ[ℂ]
      Quantum.Operators.Op
        (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) :=
  retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q -
    retainedAnalysisIdeal nK mZ mX ell ellEV leakEC ec delta Q

/-- The input reindex is literally the digit-wise round-to-party regrouping. -/
theorem retainedAnalysisRoundToBlock_apply (n : ℕ)
    (M : Quantum.Operators.Op (4 ^ n)) :
    retainedAnalysisRoundToBlock n M = Matrix.reindex
      (Equiv.roundGroupEquiv 2 2 n)
      (Equiv.roundGroupEquiv 2 2 n) M := by
  rfl

/-- The retained real map is CPTP.

This is the structural composition of program-denotation CPTP with equivalence reindexing; it is
not the physical `N`-round factorization or a CKR security estimate. -/
theorem retainedAnalysisReal_isCPTP
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    Quantum.Channels.IsCPTP
      ⇑(retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q) := by
  have hProgram :=
    (retainedAnalysisProgram nK mZ mX ell ellEV leakEC ec delta Q).coordinateDenote_isCPTP
      (retainedAnalysisBlockInputEquiv (nK + mZ + mX))
      (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)
  have hReindex := Quantum.Channels.reindexLinearEquiv_isCPTP
    (Equiv.roundGroupEquiv 2 2 (nK + mZ + mX))
  simpa [retainedAnalysisReal, Function.comp_def] using
    Quantum.Channels.cptp_comp _ _ hProgram hReindex

/-- The boundary-derived full-exit key resource is CPTP.

This is the finite key-replacement resource used by the CKR real/ideal interface, specialized to
the explicit retained output layout. -/
theorem retainedAnalysisResource_isCPTP
    (nK mZ mX ell ellEV leakEC : ℕ) :
    Quantum.Channels.IsCPTP
      ⇑(retainedAnalysisResource nK mZ mX ell ellEV leakEC) := by
  exact (retainedAnalysisOutputLayout nK mZ mX ell ellEV leakEC).toBoundaryKeyLayout
    |>.coordinateIdeal_isCPTP
      (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC)

/-- The retained ideal map is CPTP as resource after real. -/
theorem retainedAnalysisIdeal_isCPTP
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :
    Quantum.Channels.IsCPTP
      ⇑(retainedAnalysisIdeal nK mZ mX ell ellEV leakEC ec delta Q) := by
  simpa [retainedAnalysisIdeal, Function.comp_def] using
    Quantum.Channels.cptp_comp
      (⇑(retainedAnalysisResource nK mZ mX ell ellEV leakEC))
      (⇑(retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q))
      (retainedAnalysisResource_isCPTP nK mZ mX ell ellEV leakEC)
      (retainedAnalysisReal_isCPTP nK mZ mX ell ellEV leakEC ec delta Q)

/-- The difference of the retained real and ideal CP maps preserves conjugate transpose.

This is the Hermitian-preservation premise used by the CKR postselection reduction; it does not
assert permutation covariance or a norm bound. -/
theorem retainedAnalysisDifference_preserves_conjTranspose
    (nK mZ mX ell ellEV leakEC : ℕ)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ)
    (M : Quantum.Operators.Op (4 ^ (nK + mZ + mX))) :
    retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q
        M.conjTranspose =
      (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q M).conjTranspose := by
  exact Quantum.Channels.cp_linear_sub_preserves_conjTranspose _ _
    (retainedAnalysisReal_isCPTP
      nK mZ mX ell ellEV leakEC ec delta Q).2.1
    (retainedAnalysisIdeal_isCPTP
      nK mZ mX ell ellEV leakEC ec delta Q).2.1 M

end QKD.BB84.Reduction
