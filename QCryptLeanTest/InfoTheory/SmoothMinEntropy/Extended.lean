import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.FeasibleFloor

/-! # Zero-weight, support, and smoothing-boundary regressions -/
open Quantum.Operators Matrix InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder
noncomputable section
namespace QCryptLeanTest.SmoothMinEntropy

private def diagonalState (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    SubDensityOp (Fin 2) where
  toOp := Matrix.diagonal ![(a : ℂ), (b : ℂ)]
  posSemidef := Matrix.PosSemidef.diagonal (by
    intro i
    fin_cases i
    · change (0 : ℂ) ≤ (a : ℂ)
      exact_mod_cast ha
    · change (0 : ℂ) ≤ (b : ℂ)
      exact_mod_cast hb)
  trace_le_one := by simpa [Matrix.trace, Fin.sum_univ_two] using hab

private def oneOutcome {Q : Type*} [Fintype Q] (σ : SubDensityOp Q) : CQState Unit Q where
  stateMap _ := σ
  weight_le_one := by simpa only [Fintype.sum_unique, SubDensityOp.trace] using σ.trace_le_one

private lemma diagonalState_trace (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) : (diagonalState a b ha hb hab).trace = a + b := by
  simp [SubDensityOp.trace, diagonalState, Matrix.trace, Fin.sum_univ_two]

/-- Zero has infinite extended entropy even against the zero reference. -/
theorem zero_state_entropy :
    minEntropy (CQState.zero : CQState Unit (Fin 2)) SubDensityOp.zero = ⊤ ∧
      smoothMinEntropy 0 (CQState.zero : CQState Unit (Fin 2)) SubDensityOp.zero = ⊤ ∧
      smoothMinEntropyOpt 0 (CQState.zero : CQState Unit (Fin 2)) = ⊤ := by
  have h := smoothMinEntropy_eq_top_of_weight_le_eps_sq (by norm_num : (0 : ℝ) ≤ 0)
    (CQState.zero : CQState Unit (Fin 2)) SubDensityOp.zero
    (by simp [CQState.zero, SubDensityOp.zero, SubDensityOp.trace])
  refine ⟨minEntropy_zeroCQ _, h, top_unique ?_⟩
  rw [← h]
  exact smoothMinEntropy_le_smoothMinEntropyOpt _ _ _

/-- Every real floor is available at zero weight. -/
theorem zero_state_all_floors (k : ℝ) (σ : SubDensityOp (Fin 2)) :
    ENNReal.ofReal k ≤ smoothMinEntropy 0 (CQState.zero : CQState Unit (Fin 2)) σ := by
  rw [smoothMinEntropy_eq_top_of_weight_le_eps_sq (by norm_num) _ _
    (by simp [CQState.zero, SubDensityOp.zero, SubDensityOp.trace])]
  exact le_top

/-- The exact smoothing threshold includes its infinite-entropy endpoint. -/
theorem smoothMinEntropy_eq_top_at_weight_threshold :
    smoothMinEntropy (1 / 2)
      (oneOutcome (diagonalState (1 / 4) 0 (by norm_num) (by norm_num) (by norm_num)))
      (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)) = ⊤ := by
  apply smoothMinEntropy_eq_top_of_weight_le_eps_sq (by norm_num)
  norm_num [oneOutcome, diagonalState_trace]

/-- A reference cannot dominate positive mass in its kernel. -/
theorem singular_reference_infeasible :
    ¬ HasScale
      (oneOutcome (diagonalState (1 / 2) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num)))
      (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)) := by
  rintro ⟨t, ht⟩
  have h := ht.2 () (Pi.single (1 : Fin 2) 1)
  norm_num [quadraticForm, oneOutcome, diagonalState, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at h

/-- Infeasible singular references have zero positive-part entropy. -/
theorem singular_reference_entropy_zero :
    minEntropy
      (oneOutcome (diagonalState (1 / 2) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num)))
      (diagonalState 1 0 (by norm_num) (by norm_num) (by norm_num)) = 0 :=
  minEntropy_eq_zero_of_not_hasScale _ _ singular_reference_infeasible

end QCryptLeanTest.SmoothMinEntropy
