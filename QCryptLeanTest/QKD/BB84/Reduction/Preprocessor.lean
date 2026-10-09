import QCryptLean.QKD.BB84.Reduction.Preprocessor
import Mathlib.Util.AssertNoSorry

/-!
# Tests for the ambient comparison preprocessor

The independent fixtures inspect the empty failure sector, zero-probability branches, explicit
subset dependence, orthogonal ambient controls, and unequal finite-reference row and column
coordinates, proving the complete instrument, its channel formula, and its block formulas below.
-/

open Quantum.Operators (Op)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Reduction.PreprocessorAudit
open _root_.LOCC

open Measurement Sampling

/-- Degenerate all-Z basis law used to exercise a zero-probability X-quota success sector. -/
def pureZBasisLaw : PMF Basis := PMF.pure Basis.z

/-- At zero total quota the hidden failure summand has no inhabitants. -/
theorem zeroQuotaFailureIndex_elim (N : ℕ)
    (r : ComparisonPreKrausIndex N 0) :
    ∃ s : ComparisonPreSuccessIndex N 0, r = Sum.inl s := by
  cases r with
  | inl s => exact ⟨s, rfl⟩
  | inr q => exact Fin.elim0 q.1

/-- The shortage coefficient is zero when every quota is zero. -/
theorem zeroQuota_failureCoefficient_zero (N : ℕ) (pA pB : PMF Basis) :
    comparisonPreFailureCoefficient N 0 0 0 pA pB = 0 := by
  simp [comparisonPreFailureCoefficient, selectionFailureMass_zero_quotas]

/-- Under all-Z basis choices, requesting one X-test round has zero success mass. -/
theorem pureZ_oneX_successMass_zero :
    selectionSuccessMass 1 0 0 1 pureZBasisLaw pureZBasisLaw = 0 := by
  rw [selectionSuccessMass]
  apply Finset.sum_eq_zero
  intro omega _
  by_cases hq : HasQuotas 0 0 1 omega
  · simp only [hq, ite_true]
    have hxLength : 0 < (xOrder omega).length :=
      lt_of_lt_of_le Nat.zero_lt_one hq.2
    let i : Fin 1 := (xOrder omega).get ⟨0, hxLength⟩
    have hi : i ∈ xOrder omega := List.get_mem _ _
    rw [xOrder] at hi
    have hxi : omega.a i = Basis.x :=
      of_decide_eq_true (List.mem_filter.mp hi).2
    rw [rawControlLaw_apply]
    have hp : pureZBasisLaw (omega.a i) = 0 := by
      simp [pureZBasisLaw, hxi]
    have hprod : (∏ j : Fin 1, pureZBasisLaw (omega.a j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hp
    rw [hprod]
    simp
  · simp [hq]

/-- A zero-success event gives zero amplitude to every retained-subset success Kraus matrix. -/
theorem pureZ_oneX_successScale_zero :
    comparisonPreSuccessScale 1 0 0 1 pureZBasisLaw pureZBasisLaw = 0 := by
  simp [comparisonPreSuccessScale, Instrument.weightedChoiceScale,
    selectionStatusLaw_apply, selectionStatusWeight,
    pureZ_oneX_successMass_zero]

/-- A success Kraus matrix has no entry in a shortage control row. -/
theorem successKraus_shortageControl_zero
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (t : (selectedInputMarginalInstrument
      (increasingSubsetEmbedding S)).krausIndex ())
    (j : Fin (nK + mZ + mX))
    (x : Bits (nK + mZ + mX) × Bits (nK + mZ + mX))
    (a : ComparisonPreInput N) :
    comparisonPreSuccessKraus N nK mZ mX pA pB S t
        (x, Sum.inr j) a = 0 := by
  exact ite_eq_right Sum.inr_ne_inl

/-- A failure Kraus matrix has no entry in a retained-subset control row. -/
theorem failureKraus_successControl_zero
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX)) (a : ComparisonPreInput N)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (x : Bits (nK + mZ + mX) × Bits (nK + mZ + mX))
    (a' : ComparisonPreInput N) :
    comparisonPreFailureKraus N nK mZ mX pA pB j a
        (x, Sum.inl S) a' = 0 := by
  by_cases hj : j.val = 0
  · simp only [comparisonPreFailureKraus, hj, ite_eq_left]
    refine (Matrix.smul_apply _ _ _ _).trans ?_
    refine (congrArg (fun z : ℂ => (_ : ℂ) • z)
      (Matrix.single_apply_of_row_ne ?_ _ _ (1 : ℂ))).trans (smul_zero _)
    intro h
    exact Sum.inr_ne_inl (congrArg Prod.snd h)
  · simp [comparisonPreFailureKraus, hj]

/-- The literal success formula applies the selected marginal associated with its own subset,
not a fixed marginal independent of the control. -/
theorem successKraus_uses_selectedSubset
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (t : (selectedInputMarginalInstrument
      (increasingSubsetEmbedding S)).krausIndex ())
    (x : Bits (nK + mZ + mX) × Bits (nK + mZ + mX))
    (a : ComparisonPreInput N) :
    comparisonPreSuccessKraus N nK mZ mX pA pB S t
        (x, Sum.inl S) a =
      comparisonPreSuccessScale N nK mZ mX pA pB *
        (selectedInputMarginalInstrument
          (increasingSubsetEmbedding S)).kraus () t
            x a := by
  exact ite_eq_left rfl

/-- A reference-extended operator with an off-diagonal reference block. -/
def referenceCoherentOperator (N : ℕ) :
    Op (ComparisonPreInput N × Fin 2) :=
  fun q q' =>
    if q.2 = 0 ∧ q'.2 = 1 then
      if q.1 = q'.1 then (2 : ℂ) else (3 : ℂ)
    else 0

/-- The existing input-block helper retains the complete, generally off-diagonal physical-input
block at distinct reference row and column coordinates. -/
theorem referenceCoherentBlock_apply (N : ℕ)
    (a a' : ComparisonPreInput N) :
    selectedReferenceInputBlock (referenceCoherentOperator N)
        (0 : Fin 2) (1 : Fin 2) a a' =
      if a = a' then (2 : ℂ) else (3 : ℂ) := by
  simp [selectedReferenceInputBlock, referenceCoherentOperator]

end QKD.BB84.Reduction.PreprocessorAudit
