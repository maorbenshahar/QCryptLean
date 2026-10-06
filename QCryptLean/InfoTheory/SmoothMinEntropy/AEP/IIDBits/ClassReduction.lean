import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBits.Core

/-!
# Classical reduction of IID entropy rates

Classical and von Neumann entropy estimates reduce the IID spectral bound to a bit-valued floor
for the extended smooth entropy rate.
-/

open Quantum.Operators
open InfoTheory.SmoothMinEntropy
open InfoTheory.VonNeumannEntropy
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- Each CQ block is dominated by the quantum-marginal reference density operator
at scalar `λ = 1`: `(ρ.stateMap x).toOp ≼ 1 • (toSubDensityOp ρ_B).toOp`, since
the reference's operator is definitionally the quantum marginal operator. -/
lemma stateMap_opLe_one_smul_quantumMarginalDensityOp
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) (x : X) :
    opLe (ρ.stateMap x).toOp
      (((1 : ℝ) : ℂ) •
        (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hρ_norm)).toOp) := by
  have h := stateMap_opLe_quantumMarginalOp ρ x
  have heq :
      (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hρ_norm)).toOp =
        ρ.quantumMarginalOp := rfl
  rw [Complex.ofReal_one, one_smul, heq]
  exact h

/-- The quantum-marginal reference `ρ_B` is single-copy feasible at scalar `λ = 1`: every CQ block
`(ρ.stateMap x).toOp` is dominated in the operator (Löwner) order by
`1 • (DensityOp.toSubDensityOp ρ_B).toOp`. -/
theorem hasFeasibleLambda_quantumMarginalDensityOp
    {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    hasFeasibleLambda ρ
      (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hρ_norm)) :=
  ⟨1, zero_le_one,
    fun x => stateMap_opLe_one_smul_quantumMarginalDensityOp ρ hρ_norm x⟩

/-- `H(X|B) ≤ H_max(ρ_X)` in bits. The `σ = ρ_B` conditional von Neumann entropy
`(S(ρ_XB) − S(ρ_B)) / log 2` is bounded by the classical max-entropy
`H_max(ρ_X) = log₂(classicalRank ρ)`. Indeed `H(X|B) = H(X) − χ ≤ H(X) ≤ log(classicalRank)`,
where `χ ≥ 0` is the Holevo quantity (`holevoChi_nonneg`,
`InfoTheory/RelativeEntropy/HolevoBound/Concavity.lean`) and `H(X) ≤ log(rank)` is the classical
maximum-entropy bound. -/
theorem cqConditionalVonNeumann_le_classicalHmax
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    (vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
        - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)) / Real.log 2
      ≤ ρ.classicalHmax (ρ.classicalRank_filter_pos hρ_norm) := by
  -- Nat-level chain `H(X|B) ≤ H(X) ≤ log(classicalRank)` from the two named
  -- entropy leaves in `cqConditional_vonNeumann_le_log_classicalRank`, divided by `log 2 > 0`.
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcore := ρ.cqConditional_vonNeumann_le_log_classicalRank hρ_norm
  change _ ≤ Real.log (ρ.classicalRank : ℝ) / Real.log 2
  exact (div_le_div_iff_of_pos_right h2pos).mpr hcore

/-- **The tensor-power CQ state is `λ = 1` feasible against the tensor-power
marginal reference.** Each single-copy block is dominated by the quantum marginal
(`stateMap_opLe_quantumMarginalOp`), and finite tensor products preserve the
operator order with `c = 1` (`SubDensityOp.tensorFinProd_opLe_pow_const`), so the
tensor-power state is dominated blockwise by the tensor-power reference. -/
theorem iidAEP_tensorPower_isFeasible_one
    {X : Type*} [Fintype X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (n_copies : ℕ) :
    isFeasible
      (InfoTheory.SmoothMinEntropy.CQState.tensorPower ρ n_copies)
      (InfoTheory.SmoothMinEntropy.SubDensityOp.tensorPower
        (DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hρ_norm)) n_copies)
      1 := by
  classical
  refine ⟨zero_le_one, fun xs => ?_⟩
  set ρ_B : SubDensityOp n :=
    DensityOp.toSubDensityOp (ρ.quantumMarginalDensityOp hρ_norm) with hρB_def
  have hdom : ∀ j : Fin n_copies,
      opLe (ρ.stateMap (xs j)).toOp (((1 : ℝ) : ℂ) • ρ_B.toOp) := by
    intro j
    rw [hρB_def]
    exact stateMap_opLe_one_smul_quantumMarginalDensityOp ρ hρ_norm (xs j)
  have hkey := SubDensityOp.tensorFinProd_opLe_pow_const ρ_B n_copies
    (fun j => ρ.stateMap (xs j)) (c := (1 : ℝ)) zero_le_one hdom
  -- the RHS scalar `1 ^ n` collapses to `1`
  have hkey' :
      opLe (SubDensityOp.tensorFinProd n_copies (fun j => ρ.stateMap (xs j))).toOp
        (((1 : ℝ) : ℂ) •
          (SubDensityOp.tensorFinProd n_copies (fun _ => ρ_B)).toOp) := by
    simpa using hkey
  -- rewrite both sides into the tensor-power blocks
  rw [Complex.ofReal_one]
  intro v
  have hlhs :
      ((InfoTheory.SmoothMinEntropy.CQState.tensorPower ρ n_copies).stateMap xs).toOp
        = (SubDensityOp.tensorFinProd n_copies (fun j => ρ.stateMap (xs j))).toOp :=
    InfoTheory.SmoothMinEntropy.CQState.tensorPower_stateMap_toOp ρ n_copies xs
  have hrhs :
      ((InfoTheory.SmoothMinEntropy.SubDensityOp.tensorPower ρ_B n_copies).toOp)
        = (SubDensityOp.tensorFinProd n_copies (fun _ => ρ_B)).toOp := rfl
  rw [hlhs, hrhs, one_smul]
  have := hkey' v
  rwa [Complex.ofReal_one, one_smul] at this

/-- The classical i.i.d. AEP bounds the extended rate for every positive smoothing radius. -/
theorem iidAEPClassical_bit_normalized
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (n_copies : ℕ) [NeZero n_copies]
    (ε : ℝ) (hε : 0 < ε) :
    ENNReal.ofReal
      (((vonNeumannEntropy (ρ.toJointDensityOp hρ_norm)
        - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ_norm)) / Real.log 2)
        - δ_iidAEP_class ρ n_copies ε) ≤
      iidAEPSmoothRate ρ (ρ.quantumMarginalDensityOp hρ_norm) n_copies ε := by
  let ρ_B := ρ.quantumMarginalDensityOp hρ_norm
  have hAEP := iidAEPBitEntropyFloor_le_smoothRate_aep ρ hρ_norm ρ_B n_copies ε
    hε (hasFeasibleLambda_quantumMarginalDensityOp ρ hρ_norm)
  have h_rank : 1 ≤ ρ.classicalRank := ρ.classicalRank_filter_pos hρ_norm
  have h_tr_le : ρ.tracedSquareTimesInvFactor ρ_B ≤ 1 :=
    CQState.sum_trace_sq_mul_rpowNegOne_re_le_one ρ hρ_norm ρ_B rfl
  have h_tr_nn : 0 ≤ ρ.tracedSquareTimesInvFactor ρ_B :=
    CQState.sum_trace_sq_mul_rpowNegOne_re_nonneg ρ hρ_norm ρ_B rfl
  have h_squeeze := logb_rank_plus_two_le_two_mul_logb_rank_plus_four
    h_rank h_tr_nn h_tr_le
  have hδ : δ_iidAEP_general ρ ρ_B n_copies ε ≤ δ_iidAEP_class ρ n_copies ε := by
    have h := mul_le_mul_of_nonneg_right h_squeeze (Real.sqrt_nonneg
      ((Real.logb 2 ε⁻¹ + 1) / n_copies))
    simpa [δ_iidAEP_general, δ_iidAEP_class, CQState.classicalHmax, noiseFactor,
      add_mul, mul_comm, mul_left_comm, mul_assoc] using h
  refine (ENNReal.ofReal_le_ofReal ?_).trans hAEP
  unfold iidAEPBitEntropyFloor iidAEPBitEntropyContribution
  rw [InfoTheory.RelativeEntropy.relativeEntropyReal_self]
  simp only [sub_zero]
  exact sub_le_sub_left hδ _

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
