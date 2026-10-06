import QCryptLean.QKD.BB84.CompleteOutput
import QCryptLean.QKD.BB84.Reduction.Preprocessor
import QCryptLean.QKD.BB84.Reduction.RetainedExperiment
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity
import QCryptLean.Quantum.Channels.CPTP.DiamondNormComp
import QCryptLean.QKD.BB84.Program

/-!
# The reconstruction channel of the retained-round factorization

When `nK + mZ + mX ≤ N`, the real map of the BB84 coordinates factors as
`reconstruction ∘ L ∘ comparisonPre` (`coordinates_real_eq_retainedFactorizedReal`).  The
comparison preprocessor `comparisonPre` outputs a selected-round input together with a complete
comparison control (`ComparisonControl`): a retained subset or a shortage label.  `L` applies the
retained-round experiment `retainedAnalysisReal` in every control block (`retainedControlLift`).
The reconstruction channel `reconstruction` of this module rebuilds the complete physical output
from the retained output and the control.

`reconstruction` is the coordinate channel of the one-outcome instrument
`reconstructionInstrument`, whose Kraus family `reconstructionKraus` has two kinds of branches.

* A **success branch** for a retained subset `S`, an announced permutation `pi` and a raw control
  `omega` in the positive support of the total selected-control kernel
  (`SelectedControlSupport`) carries a retained-tail output announced with `pi` in the control
  block of `S` to the successful complete output of `omega` with the same tail output
  (`successCompleteOutputEmbedding`).  Its amplitude is the square root of the kernel weight of
  `omega` (`reconstructionSuccessKraus_row`).
* A **shortage branch** for a quota index `j`, a retained coordinate `r` and a raw control `omega`
  in the positive support of the total failure-control kernel (`FailureControlSupport`) sends
  `(r, j)` to the metadata-bearing abort output `shortageCompleteOutput` of `omega`, with the
  same kind of amplitude (`reconstructionShortageKraus_eq_single`).  Summed over `r`, these
  branches trace out the retained output in the control block of `j`.

`reconstructionKraus_complete` derives completeness from the normalization of the two kernels.
The module then proves the laws of the control lift used by the reductions: CPTP, composition,
subtraction, preservation of conjugate transposes and the coefficient-one diamond-norm bound for a
Hermitian-preserving retained map.  `retainedFactorizedReal`, `retainedFactorizedIdeal` and
`retainedFactorizedDifference` are the three explicit composites.

The reconstruction is an analytical channel of the proof, a certified instrument on product
coordinates; it is not a step of the LOCC program `QKD.BB84.program`.
-/

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Reduction

open TypedLOCC QKD.BB84 QKD.BB84.Reduction
open QKD.BB84.Measurement QKD.BB84.Sampling
open QKD.BB84.Engine

attribute [local instance] retainedAnalysisRoundDimNeZero
attribute [local instance] retainedAnalysisOutputDimNeZero
attribute [local instance] QKD.BB84.boundaryCardNeZero

/-- Alice-then-Bob selected strings regrouped into genuine round coordinates. -/
def comparisonSelectedToRoundEquiv (n : ℕ) :
    Fin (2 ^ n * 2 ^ n) ≃ Fin (4 ^ n) :=
  (selectedPairNumeralEquiv n).symm.trans
    (retainedSelectedPairToRoundEquiv n)

/-- The preprocessor output regrouped as retained-round input and untouched control. -/
def comparisonPreToRetainedControlEquiv (N n : ℕ) :
    Fin ((2 ^ n * 2 ^ n) * Fintype.card (ComparisonControl N n)) ≃
      Fin (4 ^ n * Fintype.card (ComparisonControl N n)) :=
  (comparisonPreOutputEquiv N n).symm |>.trans
    ((Equiv.prodCongr (comparisonSelectedToRoundEquiv n) (Fintype.equivFin _)).trans
      finProdFinEquiv)

/-- The complete comparison-control dimension is nonzero for every `N,n`. -/
@[implicit_reducible] def comparisonControlCardNeZero (N n : ℕ) :
    NeZero (Fintype.card (ComparisonControl N n)) := by
  letI : Nonempty (ComparisonControl N n) := comparisonControlNonempty N n
  exact ⟨Fintype.card_ne_zero⟩

attribute [local instance] comparisonControlCardNeZero

/-- Apply the same retained map in every complete comparison-control block. -/
noncomputable def retainedControlLift
    (N n dOut : ℕ) [NeZero dOut]
    (Phi : Quantum.Operators.Op (4 ^ n) →ₗ[ℂ]
      Quantum.Operators.Op dOut) :
    Quantum.Operators.Op
        ((2 ^ n * 2 ^ n) * Fintype.card (ComparisonControl N n)) →ₗ[ℂ]
      Quantum.Operators.Op
        (dOut * Fintype.card (ComparisonControl N n)) :=
  (Quantum.Channels.mapTensorIdLinear
      (k := Fintype.card (ComparisonControl N n)) Phi).comp
    (Matrix.reindexLinearEquiv ℂ ℂ
      (comparisonPreToRetainedControlEquiv N n)
      (comparisonPreToRetainedControlEquiv N n)).toLinearMap

/-- Positive support of one total selected-control fibre. -/
abbrev SelectedControlSupport
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX))) :=
  {omega : RawControl N //
    0 < totalSelectedControlKernel N nK mZ mX pA pB
      (Math.FiniteEmbedding.joinSubsetPerm S pi) omega}

/-- Positive support of one total shortage-control fibre. -/
abbrev FailureControlSupport
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX)) :=
  {omega : RawControl N //
    0 < totalFailureControlKernel N nK mZ mX pA pB j omega}

/-- Positive selected-kernel support supplies the actual quota witness. -/
def selectedControlSupport_hasQuotas
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi) :
    HasQuotas nK mZ mX omega.1 := by
  have hselect := totalSelectedControlKernel_select
    N nK mZ mX pA pB (Math.FiniteEmbedding.joinSubsetPerm S pi)
      omega.1 omega.2
  apply (select_isSome_iff nK mZ mX omega.1).mp
  rw [hselect]
  rfl

/-- The supported selected embedding is the literal subset-permutation embedding. -/
theorem selectedControlSupport_selectedEmbedding
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi) :
    selectedEmbedding omega.1
        (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega) =
      Math.FiniteEmbedding.joinSubsetPerm S pi := by
  have hselect := totalSelectedControlKernel_select
    N nK mZ mX pA pB (Math.FiniteEmbedding.joinSubsetPerm S pi)
      omega.1 omega.2
  unfold select at hselect
  split at hselect
  · simpa only [Option.some.injEq] using hselect
  · simp at hselect

/-- Positive failure-kernel support supplies the actual shortage witness. -/
def failureControlSupport_not_hasQuotas
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX))
    (omega : FailureControlSupport N nK mZ mX pA pB j) :
    ¬ HasQuotas nK mZ mX omega.1 :=
  totalFailureControlKernel_not_hasQuotas
    N nK mZ mX pA pB j omega.1 omega.2

/-- Input type of the complete-control reconstruction instrument. -/
abbrev ReconstructionInput
    (N nK mZ mX ell ellEV leakEC : ℕ) :=
  Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) ×
    ComparisonControl N (nK + mZ + mX)

/-- Output type of the complete-control reconstruction instrument. -/
abbrev ReconstructionOutput
    (N nK mZ mX ell ellEV leakEC : ℕ) :=
  (QKD.BB84.boundary N nK mZ mX ell ellEV leakEC).space

/-- Hidden reconstruction Kraus index. -/
abbrev ReconstructionKrausIndex
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :=
  (Σ S : Set.powersetCard (Fin N) (nK + mZ + mX),
    Σ pi : Equiv.Perm (Fin (nK + mZ + mX)),
      SelectedControlSupport N nK mZ mX pA pB S pi) ⊕
  (Σ j : Fin (nK + mZ + mX),
    Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC) ×
      FailureControlSupport N nK mZ mX pA pB j)

/-- One supported success Kraus matrix, retaining the complete raw-tail coordinate coherently. -/
def reconstructionSuccessKraus
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi) :
    Matrix (ReconstructionOutput N nK mZ mX ell ellEV leakEC)
      (ReconstructionInput N nK mZ mX ell ellEV leakEC) ℂ :=
  fun y x =>
    let q := (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC).symm x.1
    let data := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC q
    if x.2 = Sum.inl S ∧ data.1 = pi ∧
        y = successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega) data.2 then
      Instrument.weightedChoiceScale
        (totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi)) omega.1
    else 0

/-- One supported shortage Kraus matrix, tracing the retained output and preserving metadata. -/
def reconstructionShortageKraus
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX))
    (r : Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC))
    (omega : FailureControlSupport N nK mZ mX pA pB j) :
    Matrix (ReconstructionOutput N nK mZ mX ell ellEV leakEC)
      (ReconstructionInput N nK mZ mX ell ellEV leakEC) ℂ :=
  Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j) omega.1 •
    Matrix.single
      (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega.1
        (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega))
      (r, Sum.inr j) 1

/-- Complete explicit reconstruction Kraus family. -/
def reconstructionKraus
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (r : ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB) :
    Matrix (ReconstructionOutput N nK mZ mX ell ellEV leakEC)
      (ReconstructionInput N nK mZ mX ell ellEV leakEC) ℂ :=
  match r with
  | Sum.inl ⟨S, pi, omega⟩ =>
      reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega
  | Sum.inr ⟨j, r, omega⟩ =>
      reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega

/-- A success Kraus matrix vanishes on every input column outside its own control block. -/
private theorem reconstructionSuccessKraus_apply_of_control_ne
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi)
    (y : ReconstructionOutput N nK mZ mX ell ellEV leakEC)
    (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) (hx : x.2 ≠ Sum.inl S) :
    reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega y x = 0 :=
  if_neg fun h => hx h.1

/-- The ambient reconstruction Kraus family resolves the identity on every control sector. -/
theorem reconstructionKraus_complete
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :
    ∑ r : ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB,
      (reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r)ᴴ *
        reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r = 1 := by
  classical
  have hprob {R : Type} [Fintype R] (p : PMF R) :
      ∑ a : {x : R // 0 < p x}, ((p a.1).toReal : ℂ) = 1 := by
    calc
      ∑ a : {x : R // 0 < p x}, ((p a.1).toReal : ℂ) =
          (∑ a : {x : R // 0 < p x}, ((p a.1).toReal : ℂ)) +
            ∑ a : {x : R // ¬ 0 < p x}, ((p a.1).toReal : ℂ) := by
        suffices (∑ a : {x : R // ¬ 0 < p x}, ((p a.1).toReal : ℂ)) = 0 by
          rw [this, add_zero]
        apply Finset.sum_eq_zero
        intro a _
        have ha : p a.1 = 0 := bot_unique (le_of_not_gt a.2)
        simp [ha]
      _ = ∑ a : R, ((p a).toReal : ℂ) :=
        Fintype.sum_subtype_add_sum_subtype (fun x : R => 0 < p x)
          (fun x => ((p x).toReal : ℂ))
      _ = 1 := TypedLOCC.Instrument.weightedChoiceProbability_sum p
  have hfailure_col_zero
      (l : Fin (nK + mZ + mX))
      (t : Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC))
      (omega : FailureControlSupport N nK mZ mX pA pB l)
      (y : ReconstructionOutput N nK mZ mX ell ellEV leakEC)
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC)
      (hcol : ((t, Sum.inr l) : ReconstructionInput
        N nK mZ mX ell ellEV leakEC) ≠ x) :
      reconstructionShortageKraus
          N nK mZ mX ell ellEV leakEC pA pB l t omega y x = 0 := by
    unfold reconstructionShortageKraus
    refine (Matrix.smul_apply _ _ _ _).trans ?_
    refine (congrArg (fun z : ℂ => (_ : ℂ) • z)
      (Matrix.single_apply_of_col_ne _ _ hcol (1 : ℂ))).trans ?_
    exact smul_zero _
  have hfailure_sum_zero_on_success
      (a : Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC))
      (S : Set.powersetCard (Fin N) (nK + mZ + mX))
      (x : ReconstructionInput N nK mZ mX ell ellEV leakEC) :
      (∑ l, ∑ t, ∑ omega, ∑ y,
        star (reconstructionShortageKraus
          N nK mZ mX ell ellEV leakEC pA pB l t omega y (a, Sum.inl S)) *
          reconstructionShortageKraus
            N nK mZ mX ell ellEV leakEC pA pB l t omega y x) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro omega _
    apply Finset.sum_eq_zero
    intro y _
    have hcol : ((t, Sum.inr l) : ReconstructionInput
        N nK mZ mX ell ellEV leakEC) ≠ (a, Sum.inl S) := by
      intro h
      cases congrArg Prod.snd h
    rw [hfailure_col_zero l t omega y (a, Sum.inl S) hcol]
    simp
  -- Expand the `(x, z)` entry into the success branches and the shortage branches.
  ext x z
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma, Fintype.sum_prod_type]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, reconstructionKraus]
  rcases x with ⟨r, c⟩
  rcases z with ⟨s, d⟩
  cases c with
  | inl S =>
    cases d with
    | inl T =>
      let E := retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
      let D := retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
      obtain ⟨u, rfl⟩ := E.surjective r
      obtain ⟨⟨pi, q⟩, rfl⟩ := D.symm.surjective u
      obtain ⟨v, rfl⟩ := E.surjective s
      obtain ⟨⟨pj, t⟩, rfl⟩ := D.symm.surjective v
      by_cases heq : S = T ∧ pi = pj ∧ q = t
      · rcases heq with ⟨rfl, rfl, rfl⟩
        rw [hfailure_sum_zero_on_success (E (D.symm (pi, q))) S
          (E (D.symm (pi, q)), Sum.inl S)]
        simp only [add_zero, Matrix.one_apply]
        rw [Fintype.sum_eq_single S]
        · rw [Fintype.sum_eq_single pi]
          · have hout (omega : SelectedControlSupport N nK mZ mX pA pB S pi) :
                ∑ y,
                    star (reconstructionSuccessKraus
                      N nK mZ mX ell ellEV leakEC pA pB S pi omega y
                        (E (D.symm (pi, q)), Sum.inl S)) *
                      reconstructionSuccessKraus
                        N nK mZ mX ell ellEV leakEC pA pB S pi omega y
                          (E (D.symm (pi, q)), Sum.inl S) =
                  ((totalSelectedControlKernel N nK mZ mX pA pB
                    (Math.FiniteEmbedding.joinSubsetPerm S pi) omega.1).toReal : ℂ) := by
              let y0 := successCompleteOutputEmbedding
                N nK mZ mX ell ellEV leakEC omega.1
                  (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega) q
              rw [Fintype.sum_eq_single y0]
              · simpa [reconstructionSuccessKraus, E, D, y0] using
                  Instrument.weightedChoiceScale_star_mul
                    (totalSelectedControlKernel N nK mZ mX pA pB
                      (Math.FiniteEmbedding.joinSubsetPerm S pi)) omega.1
              · intro y hy
                simp [reconstructionSuccessKraus, E, D, y0, hy]
            calc
              (∑ omega : SelectedControlSupport N nK mZ mX pA pB S pi,
                  ∑ y,
                    star (reconstructionSuccessKraus
                      N nK mZ mX ell ellEV leakEC pA pB S pi omega y
                        (E (D.symm (pi, q)), Sum.inl S)) *
                      reconstructionSuccessKraus
                        N nK mZ mX ell ellEV leakEC pA pB S pi omega y
                          (E (D.symm (pi, q)), Sum.inl S)) =
                    ∑ omega : SelectedControlSupport N nK mZ mX pA pB S pi,
                      ((totalSelectedControlKernel N nK mZ mX pA pB
                        (Math.FiniteEmbedding.joinSubsetPerm S pi)
                          omega.1).toReal : ℂ) := by
                    apply Finset.sum_congr rfl
                    intro omega _
                    exact hout omega
              _ = 1 := hprob (totalSelectedControlKernel N nK mZ mX pA pB
                (Math.FiniteEmbedding.joinSubsetPerm S pi))
          · intro pj hpj
            have hpij : pi ≠ pj := Ne.symm hpj
            simp [reconstructionSuccessKraus, E, D, hpij]
        · -- Kraus operators of another control block `T ≠ S` vanish on the column.
          intro T hTS
          refine Finset.sum_eq_zero fun pi' _ => Finset.sum_eq_zero fun omega _ =>
            Finset.sum_eq_zero fun y _ => ?_
          rw [reconstructionSuccessKraus_apply_of_control_ne N nK mZ mX ell ellEV leakEC pA pB
            T pi' omega y _ fun h => hTS (Sum.inl.inj h).symm, star_zero, zero_mul]
      · have hKzero (omega : SelectedControlSupport N nK mZ mX pA pB S pi) :
            reconstructionSuccessKraus
                N nK mZ mX ell ellEV leakEC pA pB S pi omega
                  (successCompleteOutputEmbedding
                    N nK mZ mX ell ellEV leakEC omega.1
                      (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega) q)
                  (E (D.symm (pj, t)), Sum.inl T) = 0 := by
          unfold reconstructionSuccessKraus
          simp only [E, D, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
          split
          · rename_i hcond
            exfalso
            rcases hcond with ⟨hTS, hpj, hout⟩
            apply heq
            refine ⟨(Sum.inl.inj hTS).symm, hpj.symm, ?_⟩
            exact (successCompleteOutputEmbedding
              N nK mZ mX ell ellEV leakEC omega.1
                (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega)).injective hout
          · rfl
        have hinput :
            ((E (D.symm (pi, q)), Sum.inl S) :
              ReconstructionInput N nK mZ mX ell ellEV leakEC) ≠
              ((E (D.symm (pj, t)), Sum.inl T) :
                ReconstructionInput N nK mZ mX ell ellEV leakEC) := by
          intro h
          apply heq
          have hcontrol := congrArg Prod.snd h
          have hcoordinate := congrArg Prod.fst h
          have hdata : (pi, q) = (pj, t) :=
            D.symm.injective (E.injective hcoordinate)
          exact ⟨Sum.inl.inj hcontrol, congrArg Prod.fst hdata,
            congrArg Prod.snd hdata⟩
        rw [hfailure_sum_zero_on_success (E (D.symm (pi, q))) S
          (E (D.symm (pj, t)), Sum.inl T)]
        simp only [add_zero, Matrix.one_apply, if_neg hinput]
        rw [Fintype.sum_eq_single S]
        · rw [Fintype.sum_eq_single pi]
          · apply Finset.sum_eq_zero
            intro omega _
            let y0 := successCompleteOutputEmbedding
              N nK mZ mX ell ellEV leakEC omega.1
                (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega) q
            rw [Fintype.sum_eq_single y0]
            · rw [hKzero omega]
              simp
            · intro y hy
              simp [reconstructionSuccessKraus, E, D, y0, hy]
          · intro pk hpk
            have hpik : pi ≠ pk := Ne.symm hpk
            simp [reconstructionSuccessKraus, E, D, hpik]
        · -- Kraus operators of another control block `U ≠ S` vanish on the column.
          intro U hUS
          refine Finset.sum_eq_zero fun pi' _ => Finset.sum_eq_zero fun omega _ =>
            Finset.sum_eq_zero fun y _ => ?_
          rw [reconstructionSuccessKraus_apply_of_control_ne N nK mZ mX ell ellEV leakEC pA pB
            U pi' omega y _ fun h => hUS (Sum.inl.inj h).symm, star_zero, zero_mul]
    | inr j =>
      rw [show (∑ U, ∑ pi, ∑ omega, ∑ y,
          star (reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (r, Sum.inl S)) *
            reconstructionSuccessKraus
              N nK mZ mX ell ellEV leakEC pA pB U pi omega y (s, Sum.inr j)) = 0 by
        apply Finset.sum_eq_zero
        intro U _
        apply Finset.sum_eq_zero
        intro pi _
        apply Finset.sum_eq_zero
        intro omega _
        apply Finset.sum_eq_zero
        intro y _
        have hz : reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (s, Sum.inr j) = 0 :=
          reconstructionSuccessKraus_apply_of_control_ne N nK mZ mX ell ellEV leakEC pA pB
            U pi omega y _ Sum.inr_ne_inl
        rw [hz, mul_zero]
      ]
      rw [show (∑ l, ∑ t, ∑ omega, ∑ y,
          star (reconstructionShortageKraus
            N nK mZ mX ell ellEV leakEC pA pB l t omega y (r, Sum.inl S)) *
            reconstructionShortageKraus
              N nK mZ mX ell ellEV leakEC pA pB l t omega y (s, Sum.inr j)) = 0 by
        apply Finset.sum_eq_zero
        intro l _
        apply Finset.sum_eq_zero
        intro t _
        apply Finset.sum_eq_zero
        intro omega _
        apply Finset.sum_eq_zero
        intro y _
        have hcol : ((t, Sum.inr l) : ReconstructionInput
            N nK mZ mX ell ellEV leakEC) ≠ (r, Sum.inl S) := by
          intro h
          cases congrArg Prod.snd h
        have hz : reconstructionShortageKraus
            N nK mZ mX ell ellEV leakEC pA pB l t omega y (r, Sum.inl S) = 0 := by
          unfold reconstructionShortageKraus
          refine (Matrix.smul_apply _ _ _ _).trans ?_
          refine (congrArg (fun z : ℂ => (_ : ℂ) • z)
            (Matrix.single_apply_of_col_ne _ _ hcol (1 : ℂ))).trans ?_
          exact smul_zero _
        rw [hz]
        simp
      ]
      simp
  | inr j =>
    cases d with
    | inl S =>
      rw [show (∑ U, ∑ pi, ∑ omega, ∑ y,
          star (reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (r, Sum.inr j)) *
            reconstructionSuccessKraus
              N nK mZ mX ell ellEV leakEC pA pB U pi omega y (s, Sum.inl S)) = 0 by
        apply Finset.sum_eq_zero
        intro U _
        apply Finset.sum_eq_zero
        intro pi _
        apply Finset.sum_eq_zero
        intro omega _
        apply Finset.sum_eq_zero
        intro y _
        have hz : reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (r, Sum.inr j) = 0 :=
          reconstructionSuccessKraus_apply_of_control_ne N nK mZ mX ell ellEV leakEC pA pB
            U pi omega y _ Sum.inr_ne_inl
        rw [hz]
        simp
      ]
      rw [show (∑ l, ∑ t, ∑ omega, ∑ y,
          star (reconstructionShortageKraus
            N nK mZ mX ell ellEV leakEC pA pB l t omega y (r, Sum.inr j)) *
            reconstructionShortageKraus
              N nK mZ mX ell ellEV leakEC pA pB l t omega y (s, Sum.inl S)) = 0 by
        apply Finset.sum_eq_zero
        intro l _
        apply Finset.sum_eq_zero
        intro t _
        apply Finset.sum_eq_zero
        intro omega _
        apply Finset.sum_eq_zero
        intro y _
        have hcol : ((t, Sum.inr l) : ReconstructionInput
            N nK mZ mX ell ellEV leakEC) ≠ (s, Sum.inl S) := by
          intro h
          cases congrArg Prod.snd h
        have hz : reconstructionShortageKraus
            N nK mZ mX ell ellEV leakEC pA pB l t omega y (s, Sum.inl S) = 0 := by
          unfold reconstructionShortageKraus
          refine (Matrix.smul_apply _ _ _ _).trans ?_
          refine (congrArg (fun z : ℂ => (_ : ℂ) • z)
            (Matrix.single_apply_of_col_ne _ _ hcol (1 : ℂ))).trans ?_
          exact smul_zero _
        rw [hz, mul_zero]
      ]
      simp
    | inr k =>
      rw [show (∑ U, ∑ pi, ∑ omega, ∑ y,
          star (reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (r, Sum.inr j)) *
            reconstructionSuccessKraus
              N nK mZ mX ell ellEV leakEC pA pB U pi omega y (s, Sum.inr k)) = 0 by
        apply Finset.sum_eq_zero
        intro U _
        apply Finset.sum_eq_zero
        intro pi _
        apply Finset.sum_eq_zero
        intro omega _
        apply Finset.sum_eq_zero
        intro y _
        have hz : reconstructionSuccessKraus
            N nK mZ mX ell ellEV leakEC pA pB U pi omega y (r, Sum.inr j) = 0 :=
          reconstructionSuccessKraus_apply_of_control_ne N nK mZ mX ell ellEV leakEC pA pB
            U pi omega y _ Sum.inr_ne_inl
        rw [hz]
        simp
      ]
      by_cases hinput :
          ((r, Sum.inr j) : ReconstructionInput
            N nK mZ mX ell ellEV leakEC) = (s, Sum.inr k)
      · have hrs : r = s := congrArg Prod.fst hinput
        have hjk : j = k := Sum.inr.inj (congrArg Prod.snd hinput)
        subst s
        subst k
        simp only [zero_add, Matrix.one_apply]
        rw [Fintype.sum_eq_single j]
        · rw [Fintype.sum_eq_single r]
          · have hout (omega : FailureControlSupport N nK mZ mX pA pB j) :
                ∑ y,
                    star (reconstructionShortageKraus
                      N nK mZ mX ell ellEV leakEC pA pB j r omega y
                        (r, Sum.inr j)) *
                      reconstructionShortageKraus
                        N nK mZ mX ell ellEV leakEC pA pB j r omega y
                          (r, Sum.inr j) =
                  ((totalFailureControlKernel N nK mZ mX pA pB j
                    omega.1).toReal : ℂ) := by
              let y0 := shortageCompleteOutput
                N nK mZ mX ell ellEV leakEC omega.1
                  (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega)
              rw [Fintype.sum_eq_single y0]
              · dsimp only [reconstructionShortageKraus]
                change star ((_ : ℂ) * _) * ((_ : ℂ) * _) = _
                refine (congrArg (fun z : ℂ => star ((_ : ℂ) * z) * ((_ : ℂ) * z))
                  (Matrix.single_apply_same y0 (r, (Sum.inr j : ComparisonControl N _))
                    (1 : ℂ))).trans ?_
                simpa only [mul_one] using
                  Instrument.weightedChoiceScale_star_mul
                    (totalFailureControlKernel N nK mZ mX pA pB j) omega.1
              · intro y hy
                have hrow : y0 ≠ y := Ne.symm hy
                have hz : reconstructionShortageKraus
                    N nK mZ mX ell ellEV leakEC pA pB j r omega y
                      (r, Sum.inr j) = 0 := by
                  unfold reconstructionShortageKraus
                  refine (Matrix.smul_apply _ _ _ _).trans ?_
                  rw [Matrix.single_apply_of_row_ne hrow]
                  exact smul_zero _
                rw [hz]
                simp
            calc
              (∑ omega : FailureControlSupport N nK mZ mX pA pB j,
                  ∑ y,
                    star (reconstructionShortageKraus
                      N nK mZ mX ell ellEV leakEC pA pB j r omega y
                        (r, Sum.inr j)) *
                      reconstructionShortageKraus
                        N nK mZ mX ell ellEV leakEC pA pB j r omega y
                          (r, Sum.inr j)) =
                    ∑ omega : FailureControlSupport N nK mZ mX pA pB j,
                      ((totalFailureControlKernel N nK mZ mX pA pB j
                        omega.1).toReal : ℂ) := by
                    apply Finset.sum_congr rfl
                    intro omega _
                    exact hout omega
              _ = 1 := hprob (totalFailureControlKernel N nK mZ mX pA pB j)
          · intro t htr
            apply Finset.sum_eq_zero
            intro omega _
            apply Finset.sum_eq_zero
            intro y _
            have hcol : ((t, Sum.inr j) : ReconstructionInput
                N nK mZ mX ell ellEV leakEC) ≠ (r, Sum.inr j) := by
              intro h
              exact htr (congrArg Prod.fst h)
            rw [hfailure_col_zero j t omega y (r, Sum.inr j) hcol]
            simp
        · intro l hlj
          apply Finset.sum_eq_zero
          intro t _
          apply Finset.sum_eq_zero
          intro omega _
          apply Finset.sum_eq_zero
          intro y _
          have hcol : ((t, Sum.inr l) : ReconstructionInput
              N nK mZ mX ell ellEV leakEC) ≠ (r, Sum.inr j) := by
            intro h
            exact hlj (Sum.inr.inj (congrArg Prod.snd h))
          rw [hfailure_col_zero l t omega y (r, Sum.inr j) hcol]
          simp
      · simp only [zero_add, Matrix.one_apply]
        refine Eq.trans ?_ (if_neg hinput).symm
        rw [Fintype.sum_eq_single j]
        · rw [Fintype.sum_eq_single r]
          · apply Finset.sum_eq_zero
            intro omega _
            let y0 := shortageCompleteOutput
              N nK mZ mX ell ellEV leakEC omega.1
                (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega)
            rw [Fintype.sum_eq_single y0]
            · rw [hfailure_col_zero j r omega y0 (s, Sum.inr k) hinput]
              simp
            · intro y hy
              have hrow : y0 ≠ y := Ne.symm hy
              have hz : reconstructionShortageKraus
                  N nK mZ mX ell ellEV leakEC pA pB j r omega y
                    (r, Sum.inr j) = 0 := by
                unfold reconstructionShortageKraus
                refine (Matrix.smul_apply _ _ _ _).trans ?_
                rw [Matrix.single_apply_of_row_ne hrow]
                exact smul_zero _
              rw [hz]
              simp
          · intro t htr
            apply Finset.sum_eq_zero
            intro omega _
            apply Finset.sum_eq_zero
            intro y _
            have hcol : ((t, Sum.inr j) : ReconstructionInput
                N nK mZ mX ell ellEV leakEC) ≠ (r, Sum.inr j) := by
              intro h
              exact htr (congrArg Prod.fst h)
            rw [hfailure_col_zero j t omega y (r, Sum.inr j) hcol]
            simp
        · intro l hlj
          apply Finset.sum_eq_zero
          intro t _
          apply Finset.sum_eq_zero
          intro omega _
          apply Finset.sum_eq_zero
          intro y _
          have hcol : ((t, Sum.inr l) : ReconstructionInput
              N nK mZ mX ell ellEV leakEC) ≠ (r, Sum.inr j) := by
            intro h
            exact hlj (Sum.inr.inj (congrArg Prod.snd h))
          rw [hfailure_col_zero l t omega y (r, Sum.inr j) hcol]
          simp

/-- Certified one-outcome reconstruction instrument on the complete ambient control. -/
def reconstructionInstrument
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :
    Instrument (ReconstructionInput N nK mZ mX ell ellEV leakEC)
      (ReconstructionOutput N nK mZ mX ell ellEV leakEC) Unit where
  krausIndex _ := ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB
  kraus _ r := reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r
  complete := by
    simpa only [Fintype.sum_unique] using
      reconstructionKraus_complete N nK mZ mX ell ellEV leakEC pA pB

/-! ### Rows of the reconstruction Kraus family -/

/-- The reconstruction input coordinate of one retained subset `S`, announced permutation `pi`
and retained-tail output `u`. -/
def reconstructionSuccessInput (N nK mZ mX ell ellEV leakEC : ℕ)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (u : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    ReconstructionInput N nK mZ mX ell ellEV leakEC :=
  (retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC
    ((retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC).symm (pi, u)), Sum.inl S)

/-- Along the successful output embedding of its control, a success Kraus matrix is the scaled
identity along the success input coordinates. -/
theorem reconstructionSuccessKraus_row
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi)
    (u : RawClassicalTailOutput (nK + mZ + mX) (mZ + mX) ell ellEV
      (@Sampling.packedPESel nK mZ mX) leakEC) :
    reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega
        (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega.1
          (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega) u) =
      Pi.single (reconstructionSuccessInput N nK mZ mX ell ellEV leakEC S pi u)
        (Instrument.weightedChoiceScale (totalSelectedControlKernel N nK mZ mX pA pB
          (Math.FiniteEmbedding.joinSubsetPerm S pi)) omega.1) := by
  funext x
  rw [Pi.single_apply]
  simp only [reconstructionSuccessKraus, reconstructionSuccessInput]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h4 := (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega.1
      (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega)).injective h3
    have h5 : retainedAnalysisOutputDataEquiv nK mZ mX ell ellEV leakEC
        ((retainedAnalysisOutputEquiv nK mZ mX ell ellEV leakEC).symm x.1) = (pi, u) :=
      Prod.ext h2 h4.symm
    refine Prod.ext ?_ h1
    rw [← h5, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  · rintro rfl
    refine ⟨rfl, ?_, ?_⟩ <;> rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- A success Kraus matrix vanishes on every output row outside the successful embedding of its
control. -/
theorem reconstructionSuccessKraus_row_eq_zero
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (omega : SelectedControlSupport N nK mZ mX pA pB S pi)
    {y : ReconstructionOutput N nK mZ mX ell ellEV leakEC}
    (hy : y ∉ Set.range (successCompleteOutputEmbedding N nK mZ mX ell ellEV leakEC omega.1
      (selectedControlSupport_hasQuotas N nK mZ mX pA pB S pi omega))) :
    reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB S pi omega y = 0 := by
  funext x
  simp only [reconstructionSuccessKraus]
  rw [if_neg]
  · rfl
  rintro ⟨-, -, h⟩
  exact hy ⟨_, h.symm⟩

/-- A shortage Kraus matrix is the scaled matrix unit from its retained input coordinate to the
metadata-bearing abort output of its control. -/
theorem reconstructionShortageKraus_eq_single
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX))
    (r : Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC))
    (omega : FailureControlSupport N nK mZ mX pA pB j) :
    reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega =
      Matrix.single
        (shortageCompleteOutput N nK mZ mX ell ellEV leakEC omega.1
          (failureControlSupport_not_hasQuotas N nK mZ mX pA pB j omega))
        (r, Sum.inr j)
        (Instrument.weightedChoiceScale (totalFailureControlKernel N nK mZ mX pA pB j)
          omega.1) := by
  unfold reconstructionShortageKraus
  refine (Matrix.smul_single _ _ _ _).trans ?_
  rw [smul_eq_mul, mul_one]

/-- The reconstruction channel is the sum of its supported success and shortage branches. -/
theorem reconstructionInstrument_channel_apply
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis)
    (rho : Op (ReconstructionInput N nK mZ mX ell ellEV leakEC)) :
    (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel rho =
      (∑ a : Σ S : Set.powersetCard (Fin N) (nK + mZ + mX),
          Σ pi : Equiv.Perm (Fin (nK + mZ + mX)),
            SelectedControlSupport N nK mZ mX pA pB S pi,
        matrixConjLinear (reconstructionSuccessKraus N nK mZ mX ell ellEV leakEC pA pB
          a.1 a.2.1 a.2.2) rho) +
      ∑ j : Fin (nK + mZ + mX), ∑ omega : FailureControlSupport N nK mZ mX pA pB j,
        ∑ r, matrixConjLinear
          (reconstructionShortageKraus N nK mZ mX ell ellEV leakEC pA pB j r omega) rho := by
  have h0 : (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel =
      ∑ r : ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB,
        matrixConjLinear (reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r) :=
    -- The instrument has the single outcome `()`, whose operation is the Kraus sum.
    Fintype.sum_unique fun o =>
      (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).operation o
  rw [h0, LinearMap.sum_apply,
    Fintype.sum_sum_type (fun r : ReconstructionKrausIndex N nK mZ mX ell ellEV leakEC pA pB =>
      matrixConjLinear (reconstructionKraus N nK mZ mX ell ellEV leakEC pA pB r) rho)]
  congr 1
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- Product coordinates for retained output and complete comparison control. -/
def reconstructionInputEquiv
    (N nK mZ mX ell ellEV leakEC : ℕ) :
    ReconstructionInput N nK mZ mX ell ellEV leakEC ≃
      Fin (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC *
        Fintype.card (ComparisonControl N (nK + mZ + mX))) :=
  (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)).trans finProdFinEquiv

/-- The reconstruction input coordinate dimension is nonzero. -/
@[implicit_reducible]
def reconstructionInputDimNeZero
    (N nK mZ mX ell ellEV leakEC : ℕ) :
    NeZero (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC *
      Fintype.card (ComparisonControl N (nK + mZ + mX))) :=
  ⟨Nat.mul_ne_zero
    (retainedAnalysisOutputDimNeZero nK mZ mX ell ellEV leakEC).out
    (comparisonControlCardNeZero N (nK + mZ + mX)).out⟩

attribute [local instance] reconstructionInputDimNeZero

/-- Coordinate channel of the complete-control reconstruction instrument. -/
noncomputable def reconstruction
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :
    Quantum.Operators.Op
        (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC *
          Fintype.card (ComparisonControl N (nK + mZ + mX))) →ₗ[ℂ]
      Quantum.Operators.Op
        (Fintype.card
          (QKD.BB84.boundary N nK mZ mX ell ellEV leakEC).space) :=
  coordinateLinear (reconstructionInputEquiv N nK mZ mX ell ellEV leakEC)
    (Fintype.equivFin _)
    (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB).channel

/-- The reconstruction channel is CPTP. -/
theorem reconstruction_isCPTP
    (N nK mZ mX ell ellEV leakEC : ℕ) (pA pB : PMF Basis) :
    Quantum.Channels.IsCPTP
      ⇑(reconstruction N nK mZ mX ell ellEV leakEC pA pB) := by
  exact (reconstructionInstrument N nK mZ mX ell ellEV leakEC pA pB)
    |>.coordinateChannel_isCPTP
      (reconstructionInputEquiv N nK mZ mX ell ellEV leakEC)
      (Fintype.equivFin _)

/-- The retained map tensored with complete control is CPTP whenever the retained map is. -/
theorem retainedControlLift_isCPTP
    (N n dOut : ℕ) [NeZero dOut]
    (Phi : Quantum.Operators.Op (4 ^ n) →ₗ[ℂ] Quantum.Operators.Op dOut)
    (hPhi : Quantum.Channels.IsCPTP ⇑Phi) :
    Quantum.Channels.IsCPTP ⇑(retainedControlLift N n dOut Phi) := by
  have hTensor := Quantum.Channels.mapTensorId_isCPTP
    (k := Fintype.card (ComparisonControl N n)) Phi hPhi
  have hReindex := Quantum.Channels.reindexLinearEquiv_isCPTP
    (comparisonPreToRetainedControlEquiv N n)
  simpa only [retainedControlLift, LinearMap.coe_comp, Function.comp_def,
    Quantum.Channels.mapTensorIdLinear] using
    Quantum.Channels.cptp_comp _ _ hTensor hReindex

/-- Control lifting respects composition on the retained factor. -/
theorem retainedControlLift_comp
    (N n dMid dOut : ℕ) [NeZero dMid] [NeZero dOut]
    (Phi : Quantum.Operators.Op (4 ^ n) →ₗ[ℂ] Quantum.Operators.Op dMid)
    (Psi : Quantum.Operators.Op dMid →ₗ[ℂ] Quantum.Operators.Op dOut) :
    (Quantum.Channels.mapTensorIdLinear
        (k := Fintype.card (ComparisonControl N n)) Psi).comp
        (retainedControlLift N n dMid Phi) =
      retainedControlLift N n dOut (Psi.comp Phi) := by
  apply LinearMap.ext
  intro rho
  simp only [retainedControlLift, LinearMap.comp_apply,
    Quantum.Channels.mapTensorIdLinear]
  exact Quantum.Channels.mapTensorId_comp Phi Psi _

/-- Control lifting respects subtraction on the retained factor. -/
theorem retainedControlLift_sub
    (N n dOut : ℕ) [NeZero dOut]
    (Phi Psi : Quantum.Operators.Op (4 ^ n) →ₗ[ℂ] Quantum.Operators.Op dOut) :
    retainedControlLift N n dOut (Phi - Psi) =
      retainedControlLift N n dOut Phi - retainedControlLift N n dOut Psi := by
  apply LinearMap.ext
  intro rho
  simp only [retainedControlLift, LinearMap.comp_apply, LinearMap.sub_apply,
    Quantum.Channels.mapTensorIdLinear]
  exact Quantum.Channels.mapTensorId_linearMap_sub Phi Psi _

/-- Private associativity reindex used to compare a complete-control register followed by a
reference register with their single combined reference register. -/
private def retainedFactorProdAssocFin (a c k : ℕ) :
    Fin (a * (c * k)) ≃ Fin ((a * c) * k) :=
  finProdFinEquiv.symm.trans
    ((Equiv.refl (Fin a)).prodCongr finProdFinEquiv.symm |>.trans
      (Equiv.prodAssoc (Fin a) (Fin c) (Fin k)).symm |>.trans
      (finProdFinEquiv.prodCongr (Equiv.refl (Fin k))) |>.trans
      finProdFinEquiv)

private theorem retainedFactorProdAssocFin_apply
    (a c k : ℕ) [NeZero c] [NeZero k] [NeZero (c * k)]
    (i : Fin a) (j : Fin c) (r : Fin k) :
    retainedFactorProdAssocFin a c k
        (finProdFinEquiv (i, finProdFinEquiv (j, r))) =
      finProdFinEquiv (finProdFinEquiv (i, j), r) := by
  simp only [retainedFactorProdAssocFin, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_apply, id_eq, finProdFinEquiv_symm_apply,
    Equiv.prodAssoc_symm_apply,
    Quantum.Channels.finProdFinEquiv_apply_divNat,
    Quantum.Channels.finProdFinEquiv_apply_modNat]

private theorem retainedFactorProdAssocFin_symm_apply
    (a c k : ℕ) [NeZero c] [NeZero k] [NeZero (a * c)] [NeZero (c * k)]
    (x : Fin ((a * c) * k)) :
    (retainedFactorProdAssocFin a c k).symm x =
      finProdFinEquiv
        (x.divNat.divNat, finProdFinEquiv (x.divNat.modNat, x.modNat)) := by
  simp only [retainedFactorProdAssocFin, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map_apply, id_eq, Equiv.prodAssoc_apply, finProdFinEquiv_symm_apply]

/-- Appending an external reference to a control-lifted map is a combined-reference application,
up to the explicit multiplication-associativity reindex. -/
private theorem retainedFactorMapTensorId_reassoc
    {a b c k : ℕ}
    [NeZero a] [NeZero b] [NeZero c] [NeZero k]
    [NeZero (a * c)] [NeZero (b * c)] [NeZero (c * k)]
    (Phi : Quantum.Operators.Op a →ₗ[ℂ] Quantum.Operators.Op b)
    (W : Quantum.Operators.Op ((a * c) * k)) :
    Quantum.Channels.mapTensorId (k := k)
        (Quantum.Channels.mapTensorIdLinear (k := c) Phi) W =
      (Quantum.Channels.mapTensorId (k := c * k) Phi
        (W.submatrix (retainedFactorProdAssocFin a c k)
          (retainedFactorProdAssocFin a c k))).submatrix
        (retainedFactorProdAssocFin b c k).symm
        (retainedFactorProdAssocFin b c k).symm := by
  classical
  ext p q
  simp only [Matrix.submatrix_apply]
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block]
  change (Quantum.Channels.mapTensorId (k := c) Phi _) _ _ = _
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block,
    Quantum.Channels.mapTensorId_apply_eq_apply_block]
  simp only [Matrix.of_apply, Matrix.submatrix_apply,
    retainedFactorProdAssocFin_symm_apply, finProdFinEquiv_symm_apply,
    Quantum.Channels.finProdFinEquiv_apply_divNat,
    Quantum.Channels.finProdFinEquiv_apply_modNat,
    retainedFactorProdAssocFin_apply]

/-- Tensoring a Hermitian-preserving map with the identity on a `c`-dimensional register does not
increase its diamond norm. -/
private theorem retainedFactor_mapTensorIdLinear_diamondNorm_le
    {a b c : ℕ} [NeZero a] [NeZero b] [NeZero c]
    (Phi : Quantum.Operators.Op a →ₗ[ℂ] Quantum.Operators.Op b)
    (hPhi : ∀ M : Quantum.Operators.Op a, Phi Mᴴ = (Phi M)ᴴ) :
    Quantum.Channels.diamondNorm
        (Quantum.Channels.mapTensorIdLinear (k := c) Phi) ≤
      Quantum.Channels.diamondNorm Phi := by
  letI : NeZero (a * c) :=
    ⟨Nat.mul_ne_zero (NeZero.out) (NeZero.out)⟩
  letI : NeZero (b * c) :=
    ⟨Nat.mul_ne_zero (NeZero.out) (NeZero.out)⟩
  refine Quantum.Channels.diamondNorm_le_of_forall _ _ fun W hW => ?_
  let k := a * c
  letI : NeZero k := inferInstance
  letI : NeZero (c * k) :=
    ⟨Nat.mul_ne_zero (NeZero.out) (NeZero.out)⟩
  rw [retainedFactorMapTensorId_reassoc Phi W]
  rw [Quantum.Metrics.traceNorm_submatrix_equiv]
  apply Quantum.Channels.traceNorm_mapTensorId_le_diamondNorm_of_hermitianPreserving
    Phi hPhi
  simpa only [Quantum.Metrics.traceNorm_submatrix_equiv] using hW

/-- The explicit reindex followed by a control tensor preserves conjugate transpose whenever the
retained map does. -/
theorem retainedControlLift_preserves_conjTranspose
    (N n dOut : ℕ) [NeZero dOut]
    (Phi : Quantum.Operators.Op (4 ^ n) →ₗ[ℂ] Quantum.Operators.Op dOut)
    (hPhi : ∀ M : Quantum.Operators.Op (4 ^ n), Phi Mᴴ = (Phi M)ᴴ)
    (M : Quantum.Operators.Op
      ((2 ^ n * 2 ^ n) * Fintype.card (ComparisonControl N n))) :
    retainedControlLift N n dOut Phi Mᴴ =
      (retainedControlLift N n dOut Phi M)ᴴ := by
  let R := Matrix.reindexLinearEquiv ℂ ℂ
    (comparisonPreToRetainedControlEquiv N n)
    (comparisonPreToRetainedControlEquiv N n)
  have hR := Quantum.Channels.reindexLinearEquiv_isCPTP
    (comparisonPreToRetainedControlEquiv N n)
  change Quantum.Channels.mapTensorId Phi (R Mᴴ) =
    (Quantum.Channels.mapTensorId Phi (R M))ᴴ
  rw [← Quantum.Channels.cptp_preserves_conjTranspose R hR M]
  exact Quantum.Channels.mapTensorId_preserves_conjTranspose_of_preserves_conj
    Phi hPhi (R M)

/-- The control lift of a Hermitian-preserving retained map has at most its diamond norm. -/
theorem retainedControlLift_diamondNorm_le
    (N n dOut : ℕ) [NeZero dOut]
    (Phi : Quantum.Operators.Op (4 ^ n) →ₗ[ℂ] Quantum.Operators.Op dOut)
    (hPhi : ∀ M : Quantum.Operators.Op (4 ^ n), Phi Mᴴ = (Phi M)ᴴ) :
    Quantum.Channels.diamondNorm (retainedControlLift N n dOut Phi) ≤
      Quantum.Channels.diamondNorm Phi := by
  let T := Quantum.Channels.mapTensorIdLinear
    (k := Fintype.card (ComparisonControl N n)) Phi
  let R := Matrix.reindexLinearEquiv ℂ ℂ
    (comparisonPreToRetainedControlEquiv N n)
    (comparisonPreToRetainedControlEquiv N n) |>.toLinearMap
  have hT : ∀ M, T Mᴴ = (T M)ᴴ :=
    Quantum.Channels.mapTensorId_preserves_conjTranspose_of_preserves_conj Phi hPhi
  have hR := Quantum.Channels.reindexLinearEquiv_isCPTP
    (comparisonPreToRetainedControlEquiv N n)
  calc
    Quantum.Channels.diamondNorm (retainedControlLift N n dOut Phi) ≤
        Quantum.Channels.diamondNorm T := by
      simpa only [retainedControlLift, T, R] using
        Quantum.Channels.diamondNorm_precomp_cptp_le T hT R hR
    _ ≤ Quantum.Channels.diamondNorm Phi :=
      retainedFactor_mapTensorIdLinear_diamondNorm_le Phi hPhi

/-- The composite of `comparisonPre`, the retained real experiment in every control block and the
reconstruction channel. -/
noncomputable def retainedFactorizedReal
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :=
  (reconstruction N nK mZ mX ell ellEV leakEC pA pB).comp
    ((retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
      (retainedAnalysisReal nK mZ mX ell ellEV leakEC ec delta Q)).comp
      (comparisonPre N nK mZ mX pA pB hN))

/-- The composite of `comparisonPre`, the retained ideal experiment in every control block and the
reconstruction channel. -/
noncomputable def retainedFactorizedIdeal
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :=
  (reconstruction N nK mZ mX ell ellEV leakEC pA pB).comp
    ((retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
      (retainedAnalysisIdeal nK mZ mX ell ellEV leakEC ec delta Q)).comp
      (comparisonPre N nK mZ mX pA pB hN))

/-- The composite of `comparisonPre`, the retained real-minus-ideal difference in every control
block and the reconstruction channel. -/
noncomputable def retainedFactorizedDifference
    (pA pB : PMF Basis) (N nK mZ mX ell ellEV leakEC : ℕ)
    (hN : nK + mZ + mX ≤ N)
    (ec : ECScheme (nK + mZ + mX)
      (@Sampling.packedPESel nK mZ mX) leakEC) (delta Q : ℝ) :=
  (reconstruction N nK mZ mX ell ellEV leakEC pA pB).comp
    ((retainedControlLift N (nK + mZ + mX)
      (RetainedAnalysisOutputDim nK mZ mX ell ellEV leakEC)
      (retainedAnalysisDifference nK mZ mX ell ellEV leakEC ec delta Q)).comp
      (comparisonPre N nK mZ mX pA pB hN))

end QKD.BB84.Reduction
