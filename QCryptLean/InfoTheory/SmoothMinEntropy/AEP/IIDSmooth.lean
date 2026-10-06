import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBits.ClassReduction

/-!
# IID smooth entropy lower bounds

The classical IID approximation gives an extended smooth entropy floor for a tensor power. Signed
entropy rates and finite-size penalties are combined in real arithmetic before applying
`ENNReal.ofReal`.
-/

open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- The bit-normalized i.i.d. AEP block floor bounds extended entropy for every positive radius. -/
theorem smoothMinEntropy_tensorPower_ge_classical_aep_floor
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (n_copies : ℕ) [NeZero n_copies]
    (ε : ℝ) (hε : 0 < ε) :
    ENNReal.ofReal ((n_copies : ℝ) *
      (((vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
        - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)) / Real.log 2)
        - δ_iidAEP_class ρ n_copies ε)) ≤
      smoothMinEntropy ε (CQState.tensorPower ρ n_copies)
        (SubDensityOp.tensorPower
          (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hρ_norm)) n_copies) := by
  exact (ofReal_le_iidAEPSmoothRate_iff
    ρ (ρ.quantumMarginalDensityOp hρ_norm) n_copies ε _).mp
      (iidAEPClassical_bit_normalized ρ hρ_norm n_copies ε hε)

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
