import QCryptLean.QKD.BB84.Reduction.Factorization.Reconstruction
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLeanTest.QKD.BB84.CompleteOutput.Fibres
import QCryptLeanTest.QKD.BB84.Reduction.RetainedCovariance.Resource
import QCryptLean.QKD.BB84.CompleteOutput

/-!
# Finite resource-composition fixtures for the reconstruction channel

Two literal parameter points, both with pure-`Z` basis laws, compare the complete-output key
resource after `reconstruction` with `reconstruction` after the blockwise retained resource,
without invoking the general intertwining theorem.

* success_compositions_nonzero_equalKey: with no rounds and a one-bit key, both compositions
  applied to an explicit matrix unit carrying unequal accepted keys have the nonzero equal-key
  replacement coefficient `1 / 2` at the literal equal-key output.
* shortage_compositions_literal_metadata: with one physical and one key round, both
  compositions preserve the unit weight of a failure-control retained diagonal at the literal
  metadata-bearing shortage output, whose announced bases are distinct.
* reconstruction_resource_composition_acceptance is their conjunction.
-/

open Quantum.Operators (Op)

open Quantum.Channels

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QCryptLeanTest.BB84.Reduction.Factorization.Resource

open _root_.LOCC
open QKD.BB84 QKD.BB84.Reduction
open QKD.BB84.Measurement QKD.BB84.Sampling
open QKD.BB84.FiniteKey
open QKD.BB84.Reduction.RetainedAnalysisLayoutProbe
open QKD.BB84.Reduction.RetainedCovarianceSupplement


/-! ### Target-independent coordinate, conjugation and ideal helpers

Every statement in this section is about generic finite coordinates, matrix conjugation or the
boundary-derived key ideal.  None mentions the reconstruction channel, the retained resource or
any BB84 object. -/

/-- Conjugating one diagonal matrix unit keeps exactly the corresponding Kraus column. -/
private theorem conj_single
    {A B : Type} [Fintype A] [DecidableEq A]
    (K : Matrix B A ℂ) (p : A) (y z : B) :
    Matrix.conjLinearMap K (Matrix.single p p 1) y z = K y p * star (K z p) := by
  rw [Matrix.conjLinearMap_apply_apply, Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single p]
    · rw [Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩, mul_one]
    · intro b _ hb
      rw [Matrix.single_apply, ite_eq_right (fun h => hb h.1.symm), mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q _ hq
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Matrix.single_apply, ite_eq_right (fun h => hq h.2.symm), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The uniform equal-key replacement weight of a diagonal matrix unit sharing the public exit
and residual coordinate of an equal-key evaluation point.  No positivity or support hypothesis is
used, and the input keys are unconstrained. -/
private theorem ideal_single_diag_equalKey
    {P : Type} [Fintype P] [DecidableEq P] {B : Boundary P}
    (L : BoundaryKeyLayout B) (e : B.Exit) (w w' : (B.system e).total)
    (hkey : (L.coordinates e w).1 = (L.coordinates e w).2.1)
    (hres : (L.coordinates e w').2.2 = (L.coordinates e w).2.2) :
    L.ideal (Matrix.single (⟨e, w'⟩ : B.space) ⟨e, w'⟩ 1) ⟨e, w⟩ ⟨e, w⟩ =
      (((Fintype.card ((L.disposition e).Key) : ℝ)⁻¹ : ℝ) : ℂ) := by
  classical
  rcases hc : L.coordinates e w with ⟨a, b, u⟩
  rcases hc' : L.coordinates e w' with ⟨a', b', u'⟩
  have hab : a = b := by
    simpa only [hc] using hkey
  have huu : u' = u := by
    simpa only [hc, hc'] using hres
  subst hab
  subst huu
  have hw : w = (L.coordinates e).symm (a, a, u') := by
    rw [← hc, Equiv.symm_apply_apply]
  have hw' : w' = (L.coordinates e).symm (a', b', u') := by
    rw [← hc', Equiv.symm_apply_apply]
  have hsum : (∑ oldA, ∑ oldB,
      Matrix.single (⟨e, (L.coordinates e).symm (a', b', u')⟩ : B.space)
        ⟨e, (L.coordinates e).symm (a', b', u')⟩ (1 : ℂ)
        (⟨e, (L.coordinates e).symm (oldA, oldB, u')⟩ : B.space)
        (⟨e, (L.coordinates e).symm (oldA, oldB, u')⟩ : B.space)) = 1 := by
    rw [Finset.sum_eq_single a']
    · rw [Finset.sum_eq_single b']
      · rw [Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩]
      · intro c _ hc2
        rw [Matrix.single_apply, ite_eq_right]
        rintro ⟨h1, -⟩
        have h2 : ((a', b', u') :
              (L.disposition e).Key × (L.disposition e).Key × L.Residual e) = (a', c, u') :=
          (L.coordinates e).symm.injective (eq_of_heq (Sigma.mk.inj_iff.mp h1).2)
        exact hc2 (congrArg (fun z => z.2.1) h2).symm
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro c _ hc2
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [Matrix.single_apply, ite_eq_right]
      rintro ⟨h1, -⟩
      have h2 : ((a', b', u') :
            (L.disposition e).Key × (L.disposition e).Key × L.Residual e) = (c, d, u') :=
        (L.coordinates e).symm.injective (eq_of_heq (Sigma.mk.inj_iff.mp h1).2)
      exact hc2 (congrArg (fun z => z.1) h2).symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hw, hw', L.ideal_coordinate_entry, ite_eq_left ⟨rfl, rfl, rfl⟩, hsum, mul_one]

/-- Conjugating by a Kraus matrix with a single nonzero entry in the evaluated row. -/
private theorem conj_row_single
    {A B : Type} [Fintype A] [DecidableEq A]
    (K : Matrix B A ℂ) (M : Op A) (y : B) (p : A) (c : ℂ)
    (hK : ∀ q, K y q = if q = p then c else 0) :
    Matrix.conjLinearMap K M y y = c * M p p * star c := by
  have hrow : K y = Pi.single p c := funext fun q => by rw [hK q, Pi.single_apply]
  exact Matrix.conjLinearMap_apply_of_row_eq_single K M hrow hrow

/-- The child exit of a grafted point is determined by its complete exit, for a constant graft. -/
private theorem graftConst_snd_fst
    {P : Type} [Fintype P] [DecidableEq P]
    (B : Boundary P) (D : Boundary P) (x : (B.graft (fun _ => D)).space) :
    (Boundary.graftSpaceEquiv B (fun _ => D) x).2.1 =
      (Boundary.graftExitEquiv B (fun _ => D) x.1).2 := by
  have hx : x = (Boundary.graftSpaceEquiv B (fun _ => D)).symm
      (Boundary.graftSpaceEquiv B (fun _ => D) x) :=
    (Equiv.symm_apply_apply _ _).symm
  conv_rhs => rw [hx]
  rw [Boundary.graftSpaceEquiv_symm_fst, Equiv.apply_symm_apply]

/-- Only two distinct laboratories exist, so a party away from both is impossible. -/
private theorem twoParty_eq_of_ne :
    ∀ p x y : TwoParty.Party, p ≠ x → x ≠ y → p = y := by decide

/-- In a two-party boundary layout no laboratory is a spectator. -/
private theorem spectatorParty_isEmpty
    {B : Boundary TwoParty.Party} (L : QKD.OutputLayout B) :
    IsEmpty L.SpectatorParty := by
  constructor
  rintro ⟨⟨p, hp⟩, hpb⟩
  exact hpb (Subtype.ext (twoParty_eq_of_ne p L.alice L.bob hp L.alice_ne_bob))

/-- A two-party layout with subsingleton local residual factors has a subsingleton complete
residual coordinate. -/
private theorem residual_subsingleton
    {B : Boundary TwoParty.Party} (L : QKD.OutputLayout B) (e : B.Exit)
    (hA : Subsingleton (L.AliceResidual e)) (hB : Subsingleton (L.BobResidual e)) :
    Subsingleton (L.Residual e) := by
  have := spectatorParty_isEmpty L
  have : Subsingleton (L.Spectators e) :=
    ⟨fun f g => funext fun i => isEmptyElim i⟩
  exact inferInstance

/-- The pure Z basis law used in both finite composition probes. -/
def pureZ : PMF Basis := PMF.pure Basis.z

/-- Explicit zero-round error-correction scheme. -/
def zeroEC : ECScheme 0 (@packedPESel 0 0 0) 0 where
  syndrome _ := 0
  decode x _ := x

/-- The unique retained subset in the zero-round successful ambient sector. -/
def emptySubset : Set.powersetCard (Fin 0) 0 := ⟨∅, by simp⟩

/-- The unique zero-round raw control. -/
def emptyRawControl : RawControl 0 := defaultRawControl 0

private theorem rawControl_zero_eq (omega : RawControl 0) : omega = emptyRawControl := by
  rcases omega with ⟨a, b, order⟩
  have ha : a = emptyRawControl.a := by
    funext i
    exact Fin.elim0 i
  have hb : b = emptyRawControl.b := by
    funext i
    exact Fin.elim0 i
  subst a
  subst b
  congr
  ext i
  exact Fin.elim0 i

private instance : Subsingleton (RawControl 0) :=
  ⟨fun omega omega' => (rawControl_zero_eq omega).trans (rawControl_zero_eq omega').symm⟩

private theorem emptySubset_eq (S : Set.powersetCard (Fin 0) 0) : S = emptySubset := by
  apply Subtype.ext
  ext i
  exact Fin.elim0 i

private instance : Unique (Set.powersetCard (Fin 0) 0) where
  default := emptySubset
  uniq := emptySubset_eq

private instance : Unique (ComparisonControl 0 0) where
  default := Sum.inl emptySubset
  uniq x := by
    rcases x with S | i
    · exact congrArg Sum.inl (emptySubset_eq S)
    · exact Fin.elim0 i

private theorem pmf_apply_eq_one_of_subsingleton
    {alpha : Type} [Subsingleton alpha]
    (p : PMF alpha) (x : alpha) : p x = 1 := by
  rw [PMF.apply_eq_one_iff]
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro
    exact Subsingleton.elim _ _
  · intro hy
    subst y
    obtain ⟨z, hz⟩ := p.support_nonempty
    simpa only [Subsingleton.elim z x] using hz

private instance (S : Set.powersetCard (Fin 0) 0)
    (pi : Equiv.Perm (Fin 0)) :
    Unique (SelectedControlSupport 0 0 0 0 pureZ pureZ S pi) where
  default := ⟨emptyRawControl, by
    rw [pmf_apply_eq_one_of_subsingleton]
    exact zero_lt_one⟩
  uniq omega := by
    apply Subtype.ext
    exact Subsingleton.elim _ _

private instance : Unique
    (Σ S : Set.powersetCard (Fin 0) 0,
      Σ pi : Equiv.Perm (Fin 0),
        SelectedControlSupport 0 0 0 0 pureZ pureZ S pi) where
  default := ⟨emptySubset, Equiv.refl _, default⟩
  uniq x := by
    rcases x with ⟨S, pi, omega⟩
    have hS : S = emptySubset := Subsingleton.elim _ _
    subst S
    have hpi : pi = Equiv.refl (Fin 0) := Subsingleton.elim _ _
    subst pi
    congr
    exact Subsingleton.elim _ _

private instance : Unique
    (ReconstructionKrausIndex 0 0 0 0 1 0 0 pureZ pureZ) where
  default := Sum.inl ⟨emptySubset, Equiv.refl _, default⟩
  uniq x := by
    rcases x with success | failure
    · rcases success with ⟨S, pi, omega⟩
      have hS : S = emptySubset := Subsingleton.elim _ _
      subst S
      have hpi : pi = Equiv.refl (Fin (0 + 0 + 0)) := by
        ext i
        exact Fin.elim0 i
      subst pi
      congr
      exact Subsingleton.elim _ _
    · rcases failure with ⟨j, rest⟩
      exact Fin.elim0 j

/-- The successful ambient typed input carrying unequal accepted keys. -/
def successInput :
    Op (ReconstructionInput 0 0 0 0 1 0 0) :=
  Matrix.single
    (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0 (zeroOneBitAcceptedPoint 0 1),
      Sum.inl emptySubset)
    (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0 (zeroOneBitAcceptedPoint 0 1),
      Sum.inl emptySubset) 1

/-- The literal complete successful output with equal replacement keys. -/
def successEqualOutput :
    (QKD.BB84.boundary 0 0 0 0 1 0 0).space :=
  successCompleteOutputEmbedding 0 0 0 0 1 0 0 emptyRawControl
    (by decide : HasQuotas 0 0 0 emptyRawControl)
    (QCryptLeanTest.BB84.CompleteOutput.Fibres.zeroAcceptedRawOutput (0, 0))

/-- The literal complete successful output before key replacement. -/
def successUnequalOutput :
    (QKD.BB84.boundary 0 0 0 0 1 0 0).space :=
  successCompleteOutputEmbedding 0 0 0 0 1 0 0 emptyRawControl
    (by decide : HasQuotas 0 0 0 emptyRawControl)
    (QCryptLeanTest.BB84.CompleteOutput.Fibres.zeroAcceptedRawOutput (0, 1))

private instance : Nonempty (ReconstructionInput 0 0 0 0 1 0 0) :=
  ⟨((retainedAnalysisOutputDataEquiv 0 0 0 1 0 0) (zeroOneBitAcceptedPoint 0 1),
    Sum.inl emptySubset)⟩

private instance : Nonempty (ReconstructionOutput 0 0 0 0 1 0 0) :=
  ⟨successUnequalOutput⟩

/-- The actual complete-output ideal resource at the successful fixture parameters. -/
noncomputable def successActualResource :
    Operation (QKD.BB84.boundary 0 0 0 0 1 0 0).space (QKD.BB84.boundary 0 0 0 0 1 0 0).space :=
  (QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.ideal

/-- The actual reconstruction channel at the successful fixture parameters. -/
noncomputable def successReconstruction :
    Operation (ReconstructionInput 0 0 0 0 1 0 0) (ReconstructionOutput 0 0 0 0 1 0 0) :=
  reconstruction 0 0 0 0 1 0 0 pureZ pureZ

/-- The retained key resource tensored with the complete comparison control at the successful
fixture parameters. -/
noncomputable def successRetainedControlResource :
    Operation (ReconstructionInput 0 0 0 0 1 0 0) (ReconstructionInput 0 0 0 0 1 0 0) :=
  mapTensorId (retainedAnalysisResource 0 0 0 1 0 0) (ComparisonControl 0 0)

/-! ### Branch and coordinate lemmas for the reconstruction Kraus family

These read one column of one explicit reconstruction Kraus matrix.  They are independent of the
resource, of the complete-output ideal and of any intertwining statement. -/

/-- The reconstruction input coordinate of one announced permutation, retained subset and
retained-tail point. -/
private def inputPoint (N nK mZ mX ell ellEV leakEC : ℕ)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (u : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    ReconstructionInput N nK mZ mX ell ellEV leakEC :=
  (retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
    ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm (pi, u)), Sum.inl S)

/-- One supported success Kraus matrix has a single nonzero entry in the column of its own
announced retained-tail input point. -/
private theorem succKraus_column
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (om : SelectedControlSupport N nK mZ mX pA pB S pi)
    (u : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (y : ReconstructionOutput N nK mZ mX ell ellEV leakEC) :
    reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi om y
        (inputPoint N nK mZ mX ell ellEV leakEC S pi u) =
      (if y = successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC om.1
            (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi om) u then
        Instrument.weightedChoiceScale (totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi)) om.1
      else 0) := by
  simp only [reconstructionSuccessKraus, inputPoint, Equiv.apply_symm_apply, true_and]

/-- One supported success Kraus matrix has a single nonzero entry in every fibre row. -/
private theorem succKraus_row
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (om : SelectedControlSupport N nK mZ mX pA pB S pi)
    (u : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC)
    (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
    reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi om
        (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC om.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi om) u) x =
      (if x = inputPoint N nK mZ mX ell ellEV leakEC S pi u then
        Instrument.weightedChoiceScale (totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi)) om.1
      else 0) := by
  simp only [reconstructionSuccessKraus, inputPoint]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h4 := (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC om.1
      (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi om)).injective h3
    have h5 : retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
        ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm x.1) = (pi, u) :=
      Prod.ext h2 h4.symm
    have h6 : x.1 = retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
        ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm (pi, u)) := by
      rw [← h5, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    exact Prod.ext h6 h1
  · intro hx
    subst hx
    refine ⟨rfl, ?_, ?_⟩
    · rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    · rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- A success Kraus matrix annihilates every shortage-control input column. -/
private theorem succKraus_shortage_column
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (om : SelectedControlSupport N nK mZ mX pA pB S pi)
    (y : ReconstructionOutput N nK mZ mX ell ellEV leakEC)
    (x : ReconstructionInput N nK mZ mX ell ellEV leakEC)
    (hx : ∀ T : Set.powersetCard (Fin N) (nK + mZ + mX), x.2 ≠ Sum.inl T) :
    reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi om y x = 0 := by
  simp only [reconstructionSuccessKraus]
  rw [ite_eq_right]
  rintro ⟨h1, -, -⟩
  exact hx S h1

/-- Entry of one supported shortage Kraus matrix. -/
private theorem failKraus_apply
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX))
    (t : RetainedAnalysisOutput nK mZ mX ell ellEV leakEC)
    (om : FailureControlSupport N nK mZ mX pA pB j)
    (y : ReconstructionOutput N nK mZ mX ell ellEV leakEC)
    (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
    reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j t om y x =
      (if shortageCompleteOutput N nK mZ mX ell ellEV leakEC om.1
            (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j om) = y ∧
            (t, Sum.inr j) = x then
        Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j) om.1
      else 0) := by
  unfold reconstructionShortageKraus
  refine (Matrix.smul_apply _ _ _ _).trans ?_
  simp only [Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- The reconstruction channel expanded into its explicit Kraus family. -/
private theorem postChannel_eq_krausSum
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :
    (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel =
      ∑ r : ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB,
        Matrix.conjLinearMap (reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r) := by
  -- The instrument has one outcome; its channel is the sum of the Kraus conjugations.
  rw [Instrument.channel_eq_sum, Fintype.sum_unique, Instrument.operation,
    Quantum.Channels.krausMap_eq_sum_conjLinearMap]
  rfl

/-! ### Literal data of the zero-round accepted success fixture -/

/-- The zero-round quota witness. -/
private theorem succHasQuotas : HasQuotas 0 0 0 emptyRawControl := by decide

/-- The two test spellings of the literal accepted raw-tail output agree. -/
private theorem zeroAcceptedRawOutput_spellings (keys : Measurement.Bits 1 × Measurement.Bits 1) :
    QCryptLeanTest.BB84.CompleteOutput.Fibres.zeroAcceptedRawOutput keys =
      RetainedAnalysisLayoutProbe.zeroAcceptedRawOutput keys := rfl

/-- The literal accepted raw-tail output of the fixture, typed at the packed selector. -/
private def succTail (keys : Measurement.Bits 1 × Measurement.Bits 1) :
    RawClassicalTailOutput (0 + 0 + 0) (0 + 0) 1 0 (@Sampling.packedPESel 0 0 0) 0 :=
  RetainedAnalysisLayoutProbe.zeroAcceptedRawOutput keys

/-- The zero-round complete-output embedding of the fixture. -/
private def succEmb :
    RawClassicalTailOutput (0 + 0 + 0) (0 + 0) 1 0 (@Sampling.packedPESel 0 0 0) 0 ↪
      (QKD.BB84.boundary 0 0 0 0 1 0 0).space :=
  successCompleteOutputEmbedding 0 0 0 0 1 0 0 emptyRawControl succHasQuotas

/-- The equal-key fixture output is the embedded literal `(0, 0)` raw tail. -/
private theorem successEqualOutput_eq : successEqualOutput = succEmb (succTail (0, 0)) := rfl

/-- The unequal-key fixture output is the embedded literal `(0, 1)` raw tail. -/
private theorem successUnequalOutput_eq :
    successUnequalOutput = succEmb (succTail (0, 1)) := rfl

/-- The literal accepted raw-tail outputs are accepting with one key bit. -/
private theorem succTail_disposition (keys : Measurement.Bits 1 × Measurement.Bits 1) :
    (QKD.BB84.rawClassicalTailOutputLayout (0 + 0 + 0) (0 + 0) 1 0
        (@Sampling.packedPESel 0 0 0) 0).toBoundaryKeyLayout.disposition
      (succTail keys).1 = .accept 1 :=
  zeroAcceptedRawOutput_disposition keys

/-- The literal accepted raw-tail outputs carry exactly the supplied ordered keys. -/
private theorem succTail_keys (keys : Measurement.Bits 1 × Measurement.Bits 1) :
    ((((QKD.BB84.rawClassicalTailOutputLayout (0 + 0 + 0) (0 + 0) 1 0
              (@Sampling.packedPESel 0 0 0) 0).toBoundaryKeyLayout.acceptCoordinates
            (succTail_disposition keys)) (succTail keys).2).1,
        (((QKD.BB84.rawClassicalTailOutputLayout (0 + 0 + 0) (0 + 0) 1 0
              (@Sampling.packedPESel 0 0 0) 0).toBoundaryKeyLayout.acceptCoordinates
            (succTail_disposition keys)) (succTail keys).2).2.1) = keys :=
  zeroAcceptedRawOutput_keys keys

/-- The literal accepted raw-tail exit is the grafted accepting final-stage exit. -/
private theorem succTail_exit_eq (keys : Measurement.Bits 1 × Measurement.Bits 1) :
    (succTail keys).1 =
      (Boundary.graftExitEquiv
        (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@packedPESel 0 0 0) 0)
        (fun _ => FinalStage.boundary 1)).symm
          ⟨(QKD.BB84.classicalTailExitEquiv 0 0 1 0 (@packedPESel 0 0 0) 0).symm
              RetainedAnalysisLayoutProbe.zeroTailData,
            ((FinalStage.outputEquiv 1).symm (Sum.inl keys)).1⟩ :=
  Boundary.graftSpaceEquiv_symm_fst
    (QKD.BB84.classicalPreDecisionBoundary 0 0 1 0 (@packedPESel 0 0 0) 0)
    (fun _ => FinalStage.boundary 1)
    ((QKD.BB84.classicalTailExitEquiv 0 0 1 0 (@packedPESel 0 0 0) 0).symm
      RetainedAnalysisLayoutProbe.zeroTailData)
    ((FinalStage.outputEquiv 1).symm (Sum.inl keys))

/-- The literal accepted raw-tail exit does not depend on the carried keys. -/
private theorem succTail_exit (keys keys' : Measurement.Bits 1 × Measurement.Bits 1) :
    (succTail keys).1 = (succTail keys').1 := by
  rw [succTail_exit_eq keys, succTail_exit_eq keys']
  rfl

/-- The complete exit of an embedded raw tail is the literal prefixed exit. -/
private theorem succEmb_exit
    (u : RawClassicalTailOutput (0 + 0 + 0) (0 + 0) 1 0 (@Sampling.packedPESel 0 0 0) 0) :
    (succEmb u).1 = successExitMap 0 0 0 0 1 0 0 emptyRawControl succHasQuotas u.1 :=
  successCompleteOutputEmbedding_exit 0 0 0 0 1 0 0 emptyRawControl succHasQuotas u

/-- Both embedded literal accepted raw tails share the complete public exit. -/
private theorem succEmb_exit_eq (keys keys' : Measurement.Bits 1 × Measurement.Bits 1) :
    (succEmb (succTail keys)).1 = (succEmb (succTail keys')).1 := by
  rw [succEmb_exit, succEmb_exit, succTail_exit keys keys']

/-- The embedded literal accepted raw tail is accepting with one key bit. -/
private theorem succEmb_disposition (keys : Measurement.Bits 1 × Measurement.Bits 1) :
    (QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.disposition
      (succEmb (succTail keys)).1 = .accept 1 := by
  change (QKD.BB84.outputLayout 0 0 0 0 1 0 0).disposition
    (succEmb (succTail keys)).1 = .accept 1
  rw [succEmb_exit, successExitMap_disposition]
  exact succTail_disposition keys

/-- The complete residual coordinate at the embedded literal accepted exit is a singleton. -/
private theorem succEmb_residual_subsingleton (keys : Measurement.Bits 1 × Measurement.Bits 1) :
    Subsingleton ((QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.Residual
      (succEmb (succTail keys)).1) := by
  rw [succEmb_exit (succTail keys),
    ← successExitMap_residual_type 0 0 0 0 1 0 0 emptyRawControl succHasQuotas
      (succTail keys).1]
  refine residual_subsingleton _ _ ?_ ?_
  · change Subsingleton Unit
    infer_instance
  · change Subsingleton Unit
    infer_instance

/-- The embedded literal `(0, 0)` accepted raw tail has equal Alice and Bob key coordinates. -/
private theorem succEmb_equalKeys :
    ((QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.coordinates
        (succEmb (succTail (0, 0))).1 (succEmb (succTail (0, 0))).2).1 =
      ((QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.coordinates
        (succEmb (succTail (0, 0))).1 (succEmb (succTail (0, 0))).2).2.1 := by
  have hd := succEmb_disposition (0, 0)
  have hpair := successCompleteOutputEmbedding_acceptedKeys 0 0 0 0 1 0 0
    emptyRawControl succHasQuotas (succTail (0, 0)) (succTail_disposition (0, 0))
  have hraw := succTail_keys (0, 0)
  have hA : (((QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.acceptCoordinates
      hd) (succEmb (succTail (0, 0))).2).1 = (0 : Measurement.Bits 1) :=
    (congrArg Prod.fst hpair).trans (congrArg Prod.fst hraw)
  have hB : (((QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.acceptCoordinates
      hd) (succEmb (succTail (0, 0))).2).2.1 = (0 : Measurement.Bits 1) :=
    (congrArg (fun z : Measurement.Bits 1 × Measurement.Bits 1 => z.2) hpair).trans
      (congrArg (fun z : Measurement.Bits 1 × Measurement.Bits 1 => z.2) hraw)
  refine eq_of_heq (((BoundaryKeyLayout.acceptCoordinates_fst_heq_coordinates_fst
    _ hd (succEmb (succTail (0, 0))).2).symm.trans
      (heq_of_eq (hA.trans hB.symm))).trans ?_)
  exact BoundaryKeyLayout.acceptCoordinates_snd_fst_heq_coordinates_snd_fst
    _ hd (succEmb (succTail (0, 0))).2

/-- The accepted key alphabet at the embedded literal exit has two elements. -/
private theorem succEmb_card_key (keys : Measurement.Bits 1 × Measurement.Bits 1) :
    Fintype.card
        (((QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.disposition
          (succEmb (succTail keys)).1).Key) = 2 := by
  rw [congrArg (fun d : BoundaryKeyLayout.Disposition => Fintype.card d.Key)
    (succEmb_disposition keys)]
  rfl

/-- The zero-round success amplitude is one:  the zero-round raw control is unique. -/
private theorem succScale_eq_one (f : Fin (0 + 0 + 0) ↪ Fin 0) (omega : RawControl 0) :
    Instrument.weightedChoiceScale (totalSelectedControlKernel 0 0 0 0 pureZ pureZ f) omega =
      1 := by
  unfold Instrument.weightedChoiceScale
  rw [pmf_apply_eq_one_of_subsingleton]
  simp

private instance : Subsingleton (Equiv.Perm (Fin (0 + 0 + 0))) :=
  ⟨fun _ _ => Equiv.ext fun i => Fin.elim0 i⟩

/-- The retained-tail component of the ambient unequal-key input point. -/
private def succSourceTail :
    RawClassicalTailOutput (0 + 0 + 0) (0 + 0) 1 0 (@Sampling.packedPESel 0 0 0) 0 :=
  ((retainedAnalysisOutputDataEquiv 0 0 0 1 0 0) (zeroOneBitAcceptedPoint 0 1)).2

/-- The ambient unequal-key input point is the identity-permutation point of its retained tail. -/
private theorem succSourceTail_point :
    (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0).symm
        (Equiv.refl (Fin (0 + 0 + 0)), succSourceTail) = zeroOneBitAcceptedPoint 0 1 := by
  rw [show ((Equiv.refl (Fin (0 + 0 + 0)) : Equiv.Perm (Fin (0 + 0 + 0))), succSourceTail) =
      (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0) (zeroOneBitAcceptedPoint 0 1) from
    Prod.ext (Subsingleton.elim _ _) rfl]
  exact (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0).symm_apply_apply _

/-- The retained tail exit read from a retained-analysis output point. -/
private theorem dataEquiv_tail_exit (x : (retainedAnalysisBoundary 0 0 0 1 0 0).space) :
    ((retainedAnalysisOutputDataEquiv 0 0 0 1 0 0) x).2.1 =
      (Boundary.graftExitEquiv (retainedAnalysisPrefixBoundary (0 + 0 + 0))
        (fun _ => QKD.BB84.rawClassicalTailBoundary (0 + 0 + 0) (0 + 0) 1 0
          (@Sampling.packedPESel 0 0 0) 0) x.1).2 :=
  graftConst_snd_fst _ _ x

/-- The retained tail of the ambient unequal-key point shares the fixture tail exit. -/
private theorem succSourceTail_exit : succSourceTail.1 = (succTail (0, 0)).1 := by
  have hbase : ((retainedAnalysisOutputDataEquiv 0 0 0 1 0 0)
      (zeroAcceptedRetainedOutput (0, 0))).2 = succTail (0, 0) := by
    change ((retainedAnalysisOutputDataEquiv 0 0 0 1 0 0)
      ((retainedAnalysisOutputDataEquiv 0 0 0 1 0 0).symm
        (Equiv.refl (Fin 0),
          RetainedAnalysisLayoutProbe.zeroAcceptedRawOutput (0, 0)))).2 = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [show succSourceTail.1 = ((retainedAnalysisOutputDataEquiv 0 0 0 1 0 0)
      (zeroOneBitAcceptedPoint 0 1)).2.1 from rfl,
    ← congrArg Sigma.fst hbase, dataEquiv_tail_exit, dataEquiv_tail_exit]
  rfl

/-- The ambient unequal-key matrix unit sits at the announced input point of its retained tail. -/
private theorem successInput_eq :
    successInput =
      Matrix.single (inputPoint 0 0 0 0 1 0 0 emptySubset (Equiv.refl _) succSourceTail)
        (inputPoint 0 0 0 0 1 0 0 emptySubset (Equiv.refl _) succSourceTail) 1 := by
  rw [show inputPoint 0 0 0 0 1 0 0 emptySubset (Equiv.refl _) succSourceTail =
      ((retainedAnalysisOutputDataEquiv 0 0 0 1 0 0) (zeroOneBitAcceptedPoint 0 1),
        Sum.inl emptySubset) from congrArg
        (fun q => ((retainedAnalysisOutputDataEquiv 0 0 0 1 0 0) q, Sum.inl emptySubset))
        succSourceTail_point]
  rfl

/-- The reconstruction embedding attached to the unique zero-round success branch. -/
private theorem succEmb_default :
    successCompleteOutputEmbedding 0 0 0 0 1 0 0
        (default : SelectedControlSupport 0 0 0 0 pureZ pureZ emptySubset
          (Equiv.refl (Fin (0 + 0 + 0)))).1
        (selectedControlSupport_hasQuotas 0 0 0 0 pureZ pureZ emptySubset
          (Equiv.refl (Fin (0 + 0 + 0))) default) = succEmb := rfl

/-- The zero-round reconstruction channel sends the ambient unequal-key matrix unit to the
literal complete output of its own retained tail. -/
private theorem succChannel_input :
    (reconstructionInstrument 0 0 0 0 1 0 0 pureZ pureZ).channel successInput =
      Matrix.single (succEmb succSourceTail) (succEmb succSourceTail) 1 := by
  rw [postChannel_eq_krausSum, LinearMap.sum_apply, Fintype.sum_unique]
  ext y z
  rw [show reconstructionKraus 0 0 0 0 1 0 0 pureZ pureZ default =
      reconstructionSuccessKraus 0 0 0 0 1 0 0 pureZ pureZ emptySubset
        (Equiv.refl (Fin (0 + 0 + 0))) default from rfl,
    successInput_eq, conj_single, succKraus_column, succKraus_column,
    succScale_eq_one, succEmb_default, Matrix.single_apply]
  by_cases hy : y = succEmb succSourceTail
  · by_cases hz : z = succEmb succSourceTail
    · simp [hy, hz]
    · simp [hy, hz, Ne.symm hz]
  · simp [hy, Ne.symm hy]

/-- Uniform equal-key weight of a same-exit diagonal matrix unit in the complete-output layout.
Only the shared public exit, the equal evaluated keys and a singleton residual are used. -/
private theorem succ_ideal_general
    (Ypt Xpt : (QKD.BB84.boundary 0 0 0 0 1 0 0).space)
    (hE : Xpt.1 = Ypt.1)
    (hkey : ((QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.coordinates
          Ypt.1 Ypt.2).1 =
      ((QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.coordinates
          Ypt.1 Ypt.2).2.1)
    (hsub : Subsingleton
      ((QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.Residual Ypt.1)) :
    (QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.ideal
        (Matrix.single Xpt Xpt 1) Ypt Ypt =
      (((Fintype.card
          (((QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.disposition
            Ypt.1).Key) : ℝ)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨gY, wY⟩ := Ypt
  obtain ⟨gX, wX⟩ := Xpt
  dsimp only at hE hkey hsub ⊢
  subst hE
  have := hsub
  exact ideal_single_diag_equalKey _ _ _ wX hkey (Subsingleton.elim _ _)

/-- The complete-output ideal weight of one same-exit diagonal matrix unit at the literal
equal-key fixture output. -/
private theorem succ_ideal_value :
    (QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.ideal
        (Matrix.single (succEmb succSourceTail) (succEmb succSourceTail) 1)
        (succEmb (succTail (0, 0))) (succEmb (succTail (0, 0))) = (2 : ℂ)⁻¹ := by
  have hE : (succEmb succSourceTail).1 = (succEmb (succTail (0, 0))).1 := by
    rw [succEmb_exit, succEmb_exit, succSourceTail_exit]
  rw [succ_ideal_general (succEmb (succTail (0, 0))) (succEmb succSourceTail) hE
      succEmb_equalKeys (succEmb_residual_subsingleton (0, 0)),
    succEmb_card_key (0, 0)]
  norm_num

/-- The literal `(0, 0)` accepted retained output is exactly the equal-key accepted point of the
zero-one-bit fixture. -/
private theorem zeroOneBitAcceptedPoint_zero :
    zeroOneBitAcceptedPoint 0 0 = zeroOneBitBaseOutput := by
  have hd := zeroOneBitBaseOutput_isAccept
  have hpair : ((((retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout.acceptCoordinates
          hd) zeroOneBitBaseOutput.2).1,
        (((retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout.acceptCoordinates
          hd) zeroOneBitBaseOutput.2).2.1) = ((0 : Measurement.Bits 1), (0 : Measurement.Bits 1)) :=
    zeroAcceptedRetainedOutput_keys (0, 0)
  have hkeyA : zeroOneBitLayoutKey 0 =
      ((retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout.coordinates
        zeroOneBitBaseOutput.1 zeroOneBitBaseOutput.2).1 := by
    refine eq_of_heq ((cast_heq zeroOneBitKeyType_eq.symm (0 : Measurement.Bits 1)).trans
      (((heq_of_eq (congrArg Prod.fst hpair)).symm).trans ?_))
    exact BoundaryKeyLayout.acceptCoordinates_fst_heq_coordinates_fst _ hd _
  have hkeyB : zeroOneBitLayoutKey 0 =
      ((retainedAnalysisOutputLayout 0 0 0 1 0 0).toBoundaryKeyLayout.coordinates
        zeroOneBitBaseOutput.1 zeroOneBitBaseOutput.2).2.1 := by
    refine eq_of_heq ((cast_heq zeroOneBitKeyType_eq.symm (0 : Measurement.Bits 1)).trans
      (((heq_of_eq (congrArg (fun z : Measurement.Bits 1 × Measurement.Bits 1 => z.2)
        hpair)).symm).trans ?_))
    exact BoundaryKeyLayout.acceptCoordinates_snd_fst_heq_coordinates_snd_fst _ hd _
  refine congrArg (Sigma.mk zeroOneBitBaseOutput.1) ?_
  exact (zeroOneBitLayout.coordinates zeroOneBitBaseOutput.1).symm_apply_eq.mpr
    (Prod.ext hkeyA (Prod.ext hkeyB rfl)).symm

/-- The retained resource block selected by the fixture comparison-control sector carries the
nonzero equal-key replacement weight. -/
private theorem succControlBlock :
    successRetainedControlResource successInput
      (inputPoint 0 0 0 0 1 0 0 emptySubset (Equiv.refl (Fin (0 + 0 + 0))) (succTail (0, 0)))
      (inputPoint 0 0 0 0 1 0 0 emptySubset (Equiv.refl (Fin (0 + 0 + 0))) (succTail (0, 0))) =
      (2 : ℂ)⁻¹ := by
  rw [successRetainedControlResource, mapTensorId_apply]
  have hblock : (fun i j => successInput (i, Sum.inl emptySubset) (j, Sum.inl emptySubset)) =
      zeroOneBitUnequalKeyPublicInput := by
    ext i j
    simp [successInput, zeroOneBitUnequalKeyPublicInput, zeroOneBitUnequalKeyInput,
      Matrix.reindex_apply, Matrix.single_apply, Equiv.eq_symm_apply]
  change retainedAnalysisResource 0 0 0 1 0 0
    (fun i j => successInput (i, Sum.inl emptySubset) (j, Sum.inl emptySubset)) _ _ = _
  rw [hblock]
  have hp : (Equiv.refl (Fin (0 + 0 + 0)), succTail (0, 0)) =
      retainedAnalysisOutputDataEquiv 0 0 0 1 0 0 (zeroOneBitAcceptedPoint 0 0) := by
    rw [zeroOneBitAcceptedPoint_zero]
    change _ = (retainedAnalysisOutputDataEquiv 0 0 0 1 0 0)
      ((retainedAnalysisOutputDataEquiv 0 0 0 1 0 0).symm _)
    rw [Equiv.apply_symm_apply]
    rfl
  change retainedAnalysisResource 0 0 0 1 0 0 zeroOneBitUnequalKeyPublicInput
    (Equiv.refl (Fin (0 + 0 + 0)), succTail (0, 0))
    (Equiv.refl (Fin (0 + 0 + 0)), succTail (0, 0)) = _
  rw [hp]
  exact retainedAnalysisResource_nonzero_accepted_sameExit

/-- Row evaluation of the zero-round reconstruction channel at the literal equal-key output. -/
private theorem succChannel_row (W : Op (ReconstructionInput 0 0 0 0 1 0 0)) :
    (reconstructionInstrument 0 0 0 0 1 0 0 pureZ pureZ).channel W
        (succEmb (succTail (0, 0))) (succEmb (succTail (0, 0))) =
      W (inputPoint 0 0 0 0 1 0 0 emptySubset (Equiv.refl (Fin (0 + 0 + 0))) (succTail (0, 0)))
        (inputPoint 0 0 0 0 1 0 0 emptySubset (Equiv.refl (Fin (0 + 0 + 0)))
          (succTail (0, 0))) := by
  have hK : ∀ q, reconstructionSuccessKraus 0 0 0 0 1 0 0 pureZ pureZ emptySubset
      (Equiv.refl (Fin (0 + 0 + 0))) default (succEmb (succTail (0, 0))) q =
      (if q = inputPoint 0 0 0 0 1 0 0 emptySubset (Equiv.refl (Fin (0 + 0 + 0)))
        (succTail (0, 0)) then (1 : ℂ) else 0) := by
    intro q
    rw [← succEmb_default, succKraus_row, succScale_eq_one]
  rw [postChannel_eq_krausSum, LinearMap.sum_apply, Fintype.sum_unique,
    show reconstructionKraus 0 0 0 0 1 0 0 pureZ pureZ default =
      reconstructionSuccessKraus 0 0 0 0 1 0 0 pureZ pureZ emptySubset
        (Equiv.refl (Fin (0 + 0 + 0))) default from rfl,
    conj_row_single _ W _ _ 1 hK]
  simp

/-- Both exact compositions have the nonzero equal-key replacement coefficient `1 / 2` on the
explicit ambient unequal-accepted-key matrix unit.  This is an acceptance target for the proved
resource identity; it neither imports nor invokes that identity. -/
theorem success_compositions_nonzero_equalKey :
    (successActualResource.comp successReconstruction)
        successInput successEqualOutput successEqualOutput = (2 : ℂ)⁻¹ ∧
      (successReconstruction.comp successRetainedControlResource)
        successInput successEqualOutput successEqualOutput = (2 : ℂ)⁻¹ := by
  constructor
  · change (QKD.BB84.outputLayout 0 0 0 0 1 0 0).toBoundaryKeyLayout.ideal
      ((reconstructionInstrument 0 0 0 0 1 0 0 pureZ pureZ).channel successInput)
      (succEmb (succTail (0, 0))) (succEmb (succTail (0, 0))) = _
    rw [succChannel_input, succ_ideal_value]
  · change (reconstructionInstrument 0 0 0 0 1 0 0 pureZ pureZ).channel
      (successRetainedControlResource successInput)
      (succEmb (succTail (0, 0))) (succEmb (succTail (0, 0))) = _
    rw [succChannel_row]
    exact succControlBlock

/-- Explicit one-round error-correction scheme for the shortage-sector fixture. -/
def oneRoundEC : ECScheme 1 (@packedPESel 1 0 0) 0 where
  syndrome _ := 0
  decode x _ := x

/-- The unique positive quota index in the one-retained-round shortage sector. -/
def failureIndex : Fin 1 := 0

/-- Literal one-round all-Z/all-X raw control used by the total failure kernel.  Its announced
Alice/Bob basis metadata is nontrivial and distinct. -/
def failureRawControl : RawControl 1 :=
  failureDefaultRawControl (N := 1) (nK := 1) (mZ := 0) (mX := 0) failureIndex

/-- The literal failure control exposes the distinct announced Z/X bases. -/
theorem failureRawControl_announcedBases :
    failureRawControl.a 0 = Basis.z ∧ failureRawControl.b 0 = Basis.x := by
  constructor <;> rfl

/-- The explicit shortage proof supplied by the total failure-kernel construction. -/
theorem failureRawControl_noQuotas : ¬ HasQuotas 1 0 0 failureRawControl := by
  exact not_hasQuotas_failureDefaultRawControl failureIndex

/-- An actual retained abort output used as the diagonal input of the failure-control fixture. -/
def failureRetainedOutput : (retainedAnalysisBoundary 1 0 0 0 0 0).space :=
  (retainedAnalysisOutputDataEquiv 1 0 0 0 0 0).symm
    (Equiv.refl (Fin 1), retainedAnalysisDefaultRawTailOutput 1 0 0 0 0 0)

/-- The actual typed failure-control diagonal retained coordinate. -/
def failureInput : Op (ReconstructionInput 1 1 0 0 0 0 0) :=
  Matrix.single
    ((retainedAnalysisOutputDataEquiv 1 0 0 0 0 0) failureRetainedOutput,
      Sum.inr failureIndex)
    ((retainedAnalysisOutputDataEquiv 1 0 0 0 0 0) failureRetainedOutput,
      Sum.inr failureIndex) 1

/-- Literal metadata-bearing complete shortage output selected by the failure fallback. -/
def failureShortageOutput :
    (QKD.BB84.boundary 1 1 0 0 0 0 0).space :=
  shortageCompleteOutput 1 1 0 0 0 0 0 failureRawControl failureRawControl_noQuotas

/-- The actual complete-output ideal resource at the shortage fixture parameters. -/
noncomputable def failureActualResource :
    Operation (QKD.BB84.boundary 1 1 0 0 0 0 0).space (QKD.BB84.boundary 1 1 0 0 0 0 0).space :=
  (QKD.BB84.outputLayout 1 1 0 0 0 0 0).toBoundaryKeyLayout.ideal

/-- The actual reconstruction channel at the shortage fixture parameters. -/
noncomputable def failureReconstruction :
    Operation (ReconstructionInput 1 1 0 0 0 0 0) (ReconstructionOutput 1 1 0 0 0 0 0) :=
  reconstruction 1 1 0 0 0 0 0 pureZ pureZ

/-- The retained key resource tensored with the complete comparison control at the shortage
fixture parameters. -/
noncomputable def failureRetainedControlResource :
    Operation (ReconstructionInput 1 1 0 0 0 0 0) (ReconstructionInput 1 1 0 0 0 0 0) :=
  mapTensorId (retainedAnalysisResource 1 0 0 0 0 0) (ComparisonControl 1 1)

/-! ### The one-round shortage fixture -/

/-- Under the pure-Z laws the quota-failure event has zero physical mass, so the total failure
kernel is exactly its explicit structurally valid fallback. -/
private theorem pureZ_failure_kernel :
    totalFailureControlKernel 1 1 0 0 pureZ pureZ failureIndex = PMF.pure failureRawControl := by
  unfold totalFailureControlKernel
  apply PMF.filterOrPure_eq_pure
  rintro ⟨omega, homega, hsupp⟩
  have hnz : rawControlLaw 1 pureZ pureZ omega ≠ 0 := (PMF.mem_support_iff _ _).mp hsupp
  have haz : omega.a 0 = Basis.z := by
    by_contra h
    apply hnz
    have hp : (∏ i : Fin 1, pureZ (omega.a i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 1))
        (show pureZ (omega.a 0) = 0 by simp [pureZ, PMF.pure_apply, h])
    rw [rawControlLaw_apply, hp]
    simp
  have hbz : omega.b 0 = Basis.z := by
    by_contra h
    apply hnz
    have hp : (∏ i : Fin 1, pureZ (omega.b i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 1))
        (show pureZ (omega.b 0) = 0 by simp [pureZ, PMF.pure_apply, h])
    rw [rawControlLaw_apply, hp]
    simp
  apply homega
  have hmem : (0 : Fin 1) ∈ Matched omega.a omega.b := by
    simp [Matched, haz, hbz]
  have hcard : 0 < (Matched omega.a omega.b).card := Finset.card_pos.mpr ⟨0, hmem⟩
  have h0 : (0 : Fin 1) ∈ matchedOrder omega := by
    rw [matchedOrder, List.mem_ofFn]
    exact ⟨⟨0, hcard⟩, Subsingleton.elim _ _⟩
  have hz0 : (0 : Fin 1) ∈ zOrder omega := by
    rw [zOrder, List.mem_filter]
    exact ⟨h0, by simp [haz]⟩
  refine ⟨?_, Nat.zero_le _⟩
  have hlen := List.length_pos_of_mem hz0
  omega

private instance : Unique (Fin (1 + 0 + 0)) := inferInstanceAs (Unique (Fin 1))

private instance : Unique (FailureControlSupport 1 1 0 0 pureZ pureZ failureIndex) where
  default := ⟨failureRawControl, by
    rw [pureZ_failure_kernel]
    simp [PMF.pure_apply]⟩
  uniq om := by
    apply Subtype.ext
    have h : 0 < PMF.pure failureRawControl om.1 := by
      rw [← pureZ_failure_kernel]
      exact om.2
    by_contra hne
    rw [PMF.pure_apply, ite_eq_right hne] at h
    exact absurd h (lt_irrefl 0)

/-- The one-round shortage amplitude is one. -/
private theorem failScale_eq_one :
    Instrument.weightedChoiceScale (totalFailureControlKernel 1 1 0 0 pureZ pureZ failureIndex)
      failureRawControl = 1 := by
  unfold Instrument.weightedChoiceScale
  rw [pureZ_failure_kernel]
  simp [PMF.pure_apply]

/-- A success Kraus conjugation annihilates every operator supported in shortage-control
sectors. -/
private theorem succBranch_zero_of_shortage_support
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (om : SelectedControlSupport N nK mZ mX pA pB S pi)
    (W : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC))
    (hW : ∀ p q, (∃ T : Set.powersetCard (Fin N) (nK + mZ + mX), p.2 = Sum.inl T) → W p q = 0)
    (y z : ReconstructionOutput N nK mZ mX ell ellEV leakEC) :
    Matrix.conjLinearMap
      (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi om) W y z = 0 := by
  rw [Matrix.conjLinearMap_apply_apply]
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : ∃ T : Set.powersetCard (Fin N) (nK + mZ + mX), p.2 = Sum.inl T
  · rw [hW p q hp, mul_zero, zero_mul]
  · rw [succKraus_shortage_column N nK mZ mX ell ellEV leakEC pA pB S pi om y p
      (fun T h => hp ⟨T, h⟩), zero_mul, zero_mul]

/-- Row evaluation of the shortage-sector reconstruction channel at the literal metadata-bearing
shortage output:  the retained coordinate is traced out in the failure-control sector. -/
private theorem failChannel_row (W : Op (ReconstructionInput 1 1 0 0 0 0 0))
    (hW : ∀ p q, (∃ T : Set.powersetCard (Fin 1) (1 + 0 + 0), p.2 = Sum.inl T) → W p q = 0) :
    (reconstructionInstrument 1 1 0 0 0 0 0 pureZ pureZ).channel W
        failureShortageOutput failureShortageOutput =
      ∑ t : RetainedAnalysisOutput 1 0 0 0 0 0,
        W (t, Sum.inr failureIndex) (t, Sum.inr failureIndex) := by
  have hzero : ∀ a : Σ S : Set.powersetCard (Fin 1) (1 + 0 + 0),
      Σ pi : Equiv.Perm (Fin (1 + 0 + 0)),
        SelectedControlSupport 1 1 0 0 pureZ pureZ S pi,
      Matrix.conjLinearMap (reconstructionKraus 1 1 0 0 0 0 0 pureZ pureZ (Sum.inl a)) W
        failureShortageOutput failureShortageOutput = 0 := by
    intro a
    obtain ⟨S, pi, om⟩ := a
    exact succBranch_zero_of_shortage_support 1 1 0 0 0 0 0 pureZ pureZ S pi om W hW _ _
  have hfail : ∀ (t : RetainedAnalysisOutput 1 0 0 0 0 0)
      (om : FailureControlSupport 1 1 0 0 pureZ pureZ failureIndex),
      Matrix.conjLinearMap (reconstructionShortageKraus 1 1 0 0 0 0 0 pureZ pureZ
        failureIndex t om) W failureShortageOutput failureShortageOutput =
        W (t, Sum.inr failureIndex) (t, Sum.inr failureIndex) := by
    intro t om
    have hom : om = default := Unique.uniq _ om
    subst hom
    have hK : ∀ q, reconstructionShortageKraus 1 1 0 0 0 0 0 pureZ pureZ failureIndex t
        (default : FailureControlSupport 1 1 0 0 pureZ pureZ failureIndex)
        failureShortageOutput q =
        (if q = ((t, Sum.inr failureIndex) : ReconstructionInput 1 1 0 0 0 0 0) then
          (1 : ℂ) else 0) := by
      intro q
      rw [failKraus_apply,
        show Instrument.weightedChoiceScale
            (totalFailureControlKernel 1 1 0 0 pureZ pureZ failureIndex)
            (default : FailureControlSupport 1 1 0 0 pureZ pureZ failureIndex).1 = 1 from
          failScale_eq_one]
      by_cases h : q = ((t, Sum.inr failureIndex) : ReconstructionInput 1 1 0 0 0 0 0)
      · exact (ite_eq_left ⟨rfl, h.symm⟩).trans (ite_eq_left h).symm
      · exact (ite_eq_right (fun hc => h hc.2.symm)).trans (ite_eq_right h).symm
    rw [conj_row_single _ W _ _ 1 hK]
    simp
  rw [postChannel_eq_krausSum, LinearMap.sum_apply, Matrix.sum_apply,
    Fintype.sum_sum_type, Finset.sum_eq_zero (fun a _ => hzero a), zero_add,
    Fintype.sum_sigma,
    Fintype.sum_eq_single failureIndex
      (fun j hj => absurd (Subsingleton.elim j failureIndex) hj),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_unique]
  exact hfail t default

/-- The complete-output ideal fixes every operator at the aborting shortage exit. -/
private theorem ideal_abort_apply
    {P : Type} [Fintype P] [DecidableEq P] {B : Boundary P}
    (L : BoundaryKeyLayout B) (M : Op B.space) (Ypt : B.space)
    (h : L.disposition Ypt.1 = .abort) :
    L.ideal M Ypt Ypt = M Ypt Ypt := by
  obtain ⟨e, w⟩ := Ypt
  exact L.ideal_coordinate_abort M e h w w

/-- The literal metadata-bearing shortage output aborts. -/
private theorem failureShortageOutput_abort :
    (QKD.BB84.outputLayout 1 1 0 0 0 0 0).toBoundaryKeyLayout.disposition
      failureShortageOutput.1 = .abort :=
  shortageCompleteOutput_disposition 1 1 0 0 0 0 0 failureRawControl failureRawControl_noQuotas

/-- The actual failure-control diagonal input coordinate. -/
private def failurePointQ : ReconstructionInput 1 1 0 0 0 0 0 :=
  ((retainedAnalysisOutputDataEquiv 1 0 0 0 0 0) failureRetainedOutput, Sum.inr failureIndex)

private theorem failureInput_eq :
    failureInput = Matrix.single failurePointQ failurePointQ 1 := rfl

/-- The failure-control diagonal input has no entry in any selected-control sector. -/
private theorem failureInput_sector (p q : ReconstructionInput 1 1 0 0 0 0 0)
    (hp : ∃ T : Set.powersetCard (Fin 1) (1 + 0 + 0), p.2 = Sum.inl T) :
    failureInput p q = 0 := by
  obtain ⟨T, hT⟩ := hp
  rw [failureInput_eq, Matrix.single_apply, ite_eq_right]
  rintro ⟨h1, -⟩
  rw [← h1] at hT
  simp only [failurePointQ, reduceCtorEq] at hT

/-- The traced failure-sector diagonal of the literal retained input has unit weight. -/
private theorem failureInput_diag_sum :
    (∑ t : RetainedAnalysisOutput 1 0 0 0 0 0,
      failureInput (t, Sum.inr failureIndex) (t, Sum.inr failureIndex)) = 1 := by
  rw [failureInput_eq,
    Fintype.sum_eq_single ((retainedAnalysisOutputDataEquiv 1 0 0 0 0 0) failureRetainedOutput)]
  · rw [Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩]
  · intro t ht
    rw [Matrix.single_apply, ite_eq_right]
    rintro ⟨h1, -⟩
    exact ht (congrArg Prod.fst h1).symm

/-- The control-lifted retained resource has no entry in any selected-control sector of the
fixture input. -/
private theorem failureControl_sector (p q : ReconstructionInput 1 1 0 0 0 0 0)
    (hp : ∃ T : Set.powersetCard (Fin 1) (1 + 0 + 0), p.2 = Sum.inl T) :
    (failureRetainedControlResource failureInput) p q = 0 := by
  rw [failureRetainedControlResource, mapTensorId_apply]
  have hblock : failureInput.submatrix (fun i => (i, p.2)) (fun j => (j, q.2)) = 0 := by
    ext i j
    exact failureInput_sector (i, p.2) (j, q.2) hp
  rw [hblock, map_zero]
  rfl

/-- The retained key resource preserves the traced failure-sector diagonal weight. -/
private theorem failureControl_diag_sum :
    (∑ t : RetainedAnalysisOutput 1 0 0 0 0 0,
      failureRetainedControlResource failureInput
        (t, Sum.inr failureIndex) (t, Sum.inr failureIndex)) = 1 := by
  change Matrix.trace (retainedAnalysisResource 1 0 0 0 0 0
    (fun i j => failureInput (i, Sum.inr failureIndex) (j, Sum.inr failureIndex))) = 1
  exact ((isChannel_retainedAnalysisResource 1 0 0 0 0 0).2
    (failureInput.submatrix (fun i => (i, Sum.inr failureIndex))
      (fun j => (j, Sum.inr failureIndex)))).trans failureInput_diag_sum

/-- Both exact compositions preserve unit weight from an actual failure-control retained diagonal
at the literal metadata-bearing shortage output.  This is independent of the general resource
intertwining theorem. -/
theorem shortage_compositions_literal_metadata :
    (failureActualResource.comp failureReconstruction)
        failureInput failureShortageOutput failureShortageOutput = 1 ∧
      (failureReconstruction.comp failureRetainedControlResource)
        failureInput failureShortageOutput failureShortageOutput = 1 := by
  constructor
  · change (QKD.BB84.outputLayout 1 1 0 0 0 0 0).toBoundaryKeyLayout.ideal
      ((reconstructionInstrument 1 1 0 0 0 0 0 pureZ pureZ).channel failureInput)
      failureShortageOutput failureShortageOutput = _
    rw [ideal_abort_apply _ _ _ failureShortageOutput_abort,
      failChannel_row failureInput failureInput_sector, failureInput_diag_sum]
  · change (reconstructionInstrument 1 1 0 0 0 0 0 pureZ pureZ).channel
      (failureRetainedControlResource failureInput) failureShortageOutput failureShortageOutput = _
    rw [failChannel_row _ failureControl_sector, failureControl_diag_sum]

/-- Aggregate acceptance target whose proof closure contains both concrete composition probes. -/
theorem reconstruction_resource_composition_acceptance :
    ((successActualResource.comp successReconstruction)
        successInput successEqualOutput successEqualOutput = (2 : ℂ)⁻¹ ∧
      (successReconstruction.comp successRetainedControlResource)
        successInput successEqualOutput successEqualOutput = (2 : ℂ)⁻¹) ∧
    ((failureActualResource.comp failureReconstruction)
        failureInput failureShortageOutput failureShortageOutput = 1 ∧
      (failureReconstruction.comp failureRetainedControlResource)
        failureInput failureShortageOutput failureShortageOutput = 1) := by
  exact ⟨success_compositions_nonzero_equalKey,
    shortage_compositions_literal_metadata⟩

end QCryptLeanTest.BB84.Reduction.Factorization.Resource
