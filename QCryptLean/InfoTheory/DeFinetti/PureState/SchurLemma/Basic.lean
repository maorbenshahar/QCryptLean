import QCryptLean.InfoTheory.DeFinetti.PureState.CoherentState
import QCryptLean.Quantum.Operators.MatrixIntegral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Coherent State Integration — continuity, integrability, projector identities, overlaps

This module establishes basic analytic properties of the coherent-state density
operators needed for the Schur lemma proof: entry-wise continuity and
integrability over the Haar measure, interactions with the symmetric projector,
and inner-product overlap formulas.

## Main definitions
- (none)

## Main statements
- `coherentStateDensityOp_entry_continuous`: each matrix entry is continuous in g
- `coherentStateDensityOp_integrable`: Bochner integrability over Haar measure
- `integralTensorPower_deFinetti_haar_eq_coherent_integral`: Haar de Finetti
  tensor powers agree with the coherent-state integral
- `symProj_mul_coherentStateKet`: P_sym |v^g⟩ = |v^g⟩
- `coherentState_overlap_eq_entry_pow`: ⟨v_g|v_h⟩ = ((g†h)₀₀)ⁿ
- `coherent_integral_trace`: Tr(∫ ρ_g dg) = 1
- `coherent_integral_hermitian`: (∫ ρ_g dg)† = ∫ ρ_g dg
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Symmetry MeasureTheory
open Math.HaarMeasure
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.DeFinetti.PureState

/-- Each matrix entry of the coherent state density operator is continuous in g. -/
lemma coherentStateDensityOp_entry_continuous {d n : ℕ} [NeZero d] [NeZero n]
    (i j : Fin (d ^ n)) :
    Continuous (fun g : unitaryGroup (Fin d) ℂ =>
      (coherentStateDensityOp g n).toOp i j) := by
  have heq : ∀ g, (coherentStateDensityOp g n).toOp i j =
      (coherentStateKet g n).vec i * star ((coherentStateKet g n).vec j) := by
    intro g
    simp only [coherentStateDensityOp, DensityOp.fromPure, ket_mul_bra_apply, Ket.dag_vec,
      starRingEnd_apply]
  simp_rw [heq]
  apply Continuous.mul
  · simp only [coherentStateKet]
    apply continuous_finset_prod; intro k _
    exact ((continuous_apply 0).comp ((continuous_apply _).comp continuous_subtype_val))
  · apply Continuous.star; simp only [coherentStateKet]
    apply continuous_finset_prod; intro k _
    exact ((continuous_apply 0).comp ((continuous_apply _).comp continuous_subtype_val))

/-- Each entry g ↦ (coherentStateDensityOp g n).toOp i j is integrable over Haar probability
    measure. Follows from continuity + compactness of U(d). -/
lemma coherentStateDensityOp_entry_integrable {d n : ℕ} [NeZero d] [NeZero n]
    (i j : Fin (d ^ n)) :
    MeasureTheory.Integrable
      (fun g : unitaryGroup (Fin d) ℂ => (coherentStateDensityOp g n).toOp i j)
      (haarProbUnitary d) := by
  haveI : MeasureTheory.IsProbabilityMeasure (haarProbUnitary d) :=
    haarProbUnitary_isProbability d
  exact (coherentStateDensityOp_entry_continuous i j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The permutation representation acts trivially on coherent state kets.
    U_σ |v^g⟩ = |v^g⟩ because |v^g⟩ = (g|0⟩)^⊗n is a product of identical
    factors, which is invariant under permutation of tensor factors. -/
lemma coherentStateKet_perm_fixed {d n : ℕ} [NeZero d] [NeZero n]
    (g : unitaryGroup (Fin d) ℂ) (σ : Equiv.Perm (Fin n)) :
    Math.RepresentationTheory.permutationRepresentation d n σ *
      coherentStateKet g n = coherentStateKet g n := by
  -- Extract from the proof of coherentState_perm_invariant (the hUv sufficiency)
  set v := coherentStateKet g n
  set U := Math.RepresentationTheory.permutationRepresentation d n σ
  ext ⟨i, hi⟩
  simp only [instHMulOpKet, Matrix.mulVec, dotProduct]
  simp only [v, coherentStateKet, U,
    Math.RepresentationTheory.permutationRepresentation, Matrix.of_apply]
  set e := @finFunctionFinEquiv d n
  set f_i := e.symm ⟨i, hi⟩
  set x₀ := e (f_i ∘ ⇑σ) with hx₀_def
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rw [Finset.sum_eq_single x₀]
  · simp only [show e.symm x₀ = f_i ∘ ⇑σ from by simp [x₀],
      show (f_i ∘ ⇑σ) ∘ ⇑σ.symm = f_i from by ext k; simp,
      if_true, one_mul]
    conv_lhs =>
      arg 2; ext j
      rw [show (⟨↑(e (f_i ∘ ⇑σ)) / d ^ (n - 1 - ↑j) % d, _⟩ : Fin d) =
          finFunctionFinEquiv.symm (e (f_i ∘ ⇑σ)) (Fin.rev j) from
            bigEndian_digit_eq_finFunctionFinEquiv hd_pos _ j]
    conv_rhs =>
      arg 2; ext j
      rw [show (⟨i / d ^ (n - 1 - ↑j) % d, _⟩ : Fin d) =
          finFunctionFinEquiv.symm ⟨i, hi⟩ (Fin.rev j) from
            bigEndian_digit_eq_finFunctionFinEquiv hd_pos ⟨i, hi⟩ j]
    simp only [e, Equiv.symm_apply_apply,
      Function.comp_apply, f_i]
    trans ∏ m : Fin n,
      (g : Matrix (Fin d) (Fin d) ℂ) (finFunctionFinEquiv.symm ⟨i, hi⟩ m) 0
    · exact Finset.prod_equiv (Fin.revPerm.trans σ) (fun _ => by simp)
        (fun j _ => by simp [Fin.revPerm_apply, Equiv.trans_apply])
    · symm
      exact Finset.prod_equiv Fin.revPerm (fun _ => by simp)
        (fun j _ => by simp [Fin.revPerm_apply])
  · intro x _ hx
    simp only [ite_mul, one_mul, zero_mul]
    rw [if_neg]
    intro h; exact hx (show x = x₀ by
      have heq : e.symm x = f_i ∘ ⇑σ := by
        funext k
        have h1 := congr_fun h (σ k)
        simp only [Function.comp_apply, Equiv.symm_apply_apply] at h1
        exact h1.symm
      calc x = e (e.symm x) := (e.apply_symm_apply x).symm
        _ = e (f_i ∘ ⇑σ) := by rw [heq])
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The symmetric projector acts as identity on coherent state kets:
    P_sym |v^g⟩ = |v^g⟩. This follows from U_σ |v^g⟩ = |v^g⟩ for all σ
    and P_sym = (1/n!) Σ_σ U_σ. -/
lemma symProj_mul_coherentStateKet {d n : ℕ} [NeZero d] [NeZero n]
    (g : unitaryGroup (Fin d) ℂ) :
    symmetricProjector d n * coherentStateKet g n = coherentStateKet g n := by
  set v := coherentStateKet g n
  -- P = (1/n!) • Σ_σ U_σ, and U_σ v = v for all σ
  unfold symmetricProjector
  unfold Math.RepresentationTheory.symmetricProjectorRep
  -- Goal: ((1/n!) • Σ_σ U_σ) * v = v (as Kets)
  -- Reduce to vec equality
  have key : ((1 / (Nat.factorial n : ℂ)) •
    ∑ σ : Equiv.Perm (Fin n),
      Math.RepresentationTheory.permutationRepresentation d n σ).mulVec v.vec = v.vec := by
    rw [Matrix.smul_mulVec]
    rw [Matrix.sum_mulVec Finset.univ _ _]
    simp_rw [show ∀ σ,
      (Math.RepresentationTheory.permutationRepresentation d n σ).mulVec v.vec =
      v.vec from fun σ => congr_arg Ket.vec (coherentStateKet_perm_fixed g σ)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
    ext i
    simp [Pi.smul_apply, smul_eq_mul,
      Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne']
  exact Ket.ext (fun i => congr_fun key i)

/-- The symmetric projector acts as identity on coherent state density operators:
    P_sym * |v^g⟩⟨v^g| = |v^g⟩⟨v^g|.
    Follows from P_sym |v^g⟩ = |v^g⟩. -/
lemma symProj_mul_coherentDensityOp {d n : ℕ} [NeZero d] [NeZero n]
    (g : unitaryGroup (Fin d) ℂ) :
    symmetricProjector d n * (coherentStateDensityOp g n).toOp =
      (coherentStateDensityOp g n).toOp := by
  set v := coherentStateKet g n
  set P := symmetricProjector d n
  -- ρ = v * v.dag, so P * ρ = (P * v) * v.dag = v * v.dag = ρ
  change P * (v * v.dag) = v * v.dag
  rw [op_mul_ketbra P v v.dag, symProj_mul_coherentStateKet g]

/-- The coherent-state density operator `g ↦ |v^g⟩⟨v^g|` is Bochner-integrable
    with respect to the Haar probability measure on U(d). -/
lemma coherentStateDensityOp_integrable (d n : ℕ) [NeZero d] [NeZero n] :
    MeasureTheory.Integrable
      (fun g : unitaryGroup (Fin d) ℂ => (coherentStateDensityOp g n).toOp)
      (haarProbUnitary d) := by
  haveI : MeasureTheory.IsProbabilityMeasure (haarProbUnitary d) :=
    haarProbUnitary_isProbability d
  exact (continuous_matrix (fun i j =>
    coherentStateDensityOp_entry_continuous i j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The symmetric projector commutes with the coherent-state Haar integral on the left:
    P_sym * ∫ |v^g⟩⟨v^g| dg = ∫ |v^g⟩⟨v^g| dg.
    Follows by pulling the (continuous, linear) left-multiplication through
    the Bochner integral, then applying `symProj_mul_coherentDensityOp` pointwise. -/
lemma symProj_mul_coherent_integral (d n : ℕ) [NeZero d] [NeZero n] :
    symmetricProjector d n * ∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d) =
    ∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d) := by
  set P := symmetricProjector d n
  -- Left-multiplication by P as a continuous linear map (finite-dimensional)
  let mulP_CLM : Op (d ^ n) →L[ℝ] Op (d ^ n) :=
    (LinearMap.mulLeft ℝ P).toContinuousLinearMap
  have h_int := coherentStateDensityOp_integrable d n
  -- Pull P through the integral
  have h_pull : mulP_CLM (∫ g, (coherentStateDensityOp g n).toOp
      ∂(haarProbUnitary d)) =
    ∫ g, mulP_CLM ((coherentStateDensityOp g n).toOp)
      ∂(haarProbUnitary d) :=
    (mulP_CLM.integral_comp_comm h_int).symm
  -- mulP_CLM acts as left multiplication by P
  have h_eq : ∀ X : Op (d ^ n), mulP_CLM X = P * X := fun X => by
    simp [mulP_CLM, LinearMap.mulLeft_apply, LinearMap.coe_toContinuousLinearMap']
  rw [← h_eq, h_pull]
  congr 1; ext g
  rw [h_eq, symProj_mul_coherentDensityOp g]

/-- Each |v^g⟩⟨v^g| satisfies ρ_g * P_sym = ρ_g, since |v^g⟩ is in Sym^n.
    Right-multiplication analogue of `symProj_mul_coherentDensityOp`. -/
lemma coherentDensityOp_mul_symProj {d n : ℕ} [NeZero d] [NeZero n]
    (g : unitaryGroup (Fin d) ℂ) :
    (coherentStateDensityOp g n).toOp * symmetricProjector d n =
      (coherentStateDensityOp g n).toOp := by
  set v := coherentStateKet g n
  set P := symmetricProjector d n
  -- ρ = v * v†, so ρ * P = v * (v† * P) = v * v† = ρ (since P† = P and P v = v)
  change (v * v.dag) * P = v * v.dag
  rw [ketbra_mul_op v v.dag P]
  suffices h : v.dag * P = v.dag by rw [h]
  have hPH : P† = P := (symmetricProjector_is_projector d n).2
  have hPv : (P * v : Ket _) = v := symProj_mul_coherentStateKet g
  apply Bra.ext; intro j
  simp only [bra_mul_op_vec, Ket.dag_vec]
  -- Goal: ∑ x, (starRingEnd ℂ) (v.vec x) * P x j = (starRingEnd ℂ) (v.vec j)
  -- Since P is Hermitian: P x j = star (P j x) = (starRingEnd ℂ) (P j x)
  have hP_entry : ∀ i, P i j = (starRingEnd ℂ) (P j i) := fun i => by
    rw [show P i j = P† i j from congrFun (congrFun hPH.symm i) j,
        Matrix.conjTranspose_apply, starRingEnd_apply]
  simp_rw [hP_entry, ← map_mul (starRingEnd ℂ)]
  rw [← map_sum (starRingEnd ℂ)]
  congr 1
  -- Goal: ∑ x, v.vec x * P j x = v.vec j (= (P * v).vec j)
  simp_rw [mul_comm (v.vec _) (P j _)]
  -- Goal: ∑ x, P j x * v.vec x = v.vec j (= (P * v).vec j)
  exact congr_fun (congr_arg Ket.vec hPv) j

/-- The coherent-state Haar integral satisfies I * P_sym = I.
    Right-multiplication analogue of `symProj_mul_coherent_integral`. -/
lemma coherent_integral_mul_symProj (d n : ℕ) [NeZero d] [NeZero n] :
    (∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d)) *
      symmetricProjector d n =
    ∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d) := by
  set P := symmetricProjector d n
  -- Right-multiplication by P as a continuous linear map
  let mulP_CLM : Op (d ^ n) →L[ℝ] Op (d ^ n) :=
    (LinearMap.mulRight ℝ P).toContinuousLinearMap
  have h_int := coherentStateDensityOp_integrable d n
  -- Pull P through the integral
  have h_pull : mulP_CLM (∫ g, (coherentStateDensityOp g n).toOp
      ∂(haarProbUnitary d)) =
    ∫ g, mulP_CLM ((coherentStateDensityOp g n).toOp)
      ∂(haarProbUnitary d) :=
    (mulP_CLM.integral_comp_comm h_int).symm
  -- mulP_CLM acts as right multiplication by P
  have h_eq : ∀ X : Op (d ^ n), mulP_CLM X = X * P := fun X => by
    simp [mulP_CLM, LinearMap.mulRight_apply, LinearMap.coe_toContinuousLinearMap']
  rw [← h_eq, h_pull]
  congr 1; ext g
  rw [h_eq, coherentDensityOp_mul_symProj g]

/-- The trace of the coherent state integral equals 1, since each |v^g⟩ is
    normalized: Tr(∫ |v^g⟩⟨v^g| dg) = ∫ Tr(|v^g⟩⟨v^g|) dg = ∫ 1 dg = 1.

    **Reference**: Uses coherentStateKet_normalized and IsProbabilityMeasure. -/
lemma coherent_integral_trace (d n : ℕ) [NeZero d] [NeZero n] :
    (∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d)).trace = 1 := by
  have key : ∀ g : unitaryGroup (Fin d) ℂ, (coherentStateDensityOp g n).toOp.trace = 1 :=
    fun g => (coherentStateDensityOp g n).trace_one
  have trace_comm : (∫ g, (coherentStateDensityOp g n).toOp
      ∂(haarProbUnitary d)).trace =
      ∫ g, (coherentStateDensityOp g n).toOp.trace
      ∂(haarProbUnitary d) := by
    let trace_CLM : Op (d ^ n) →L[ℝ] ℂ :=
      (Matrix.traceLinearMap (Fin (d ^ n)) ℝ ℂ).toContinuousLinearMap
    haveI : MeasureTheory.IsProbabilityMeasure (haarProbUnitary d) :=
      haarProbUnitary_isProbability d
    have h_int : MeasureTheory.Integrable
        (fun g : unitaryGroup (Fin d) ℂ => (coherentStateDensityOp g n).toOp)
        (haarProbUnitary d) :=
      (continuous_matrix (fun i j =>
        coherentStateDensityOp_entry_continuous i j)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have h := (trace_CLM.integral_comp_comm h_int).symm
    have key_trace : ∀ M : Op (d ^ n), trace_CLM M = M.trace := fun M => by
      simp [trace_CLM, Matrix.traceLinearMap_apply]
    simp_rw [key_trace] at h
    exact h
  rw [trace_comm, show (∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp.trace
      ∂(haarProbUnitary d)) =
      ∫ _ : unitaryGroup (Fin d) ℂ, (1 : ℂ)
      ∂(haarProbUnitary d) from by congr 1; ext g; exact key g]
  have : MeasureTheory.IsProbabilityMeasure (haarProbUnitary d) :=
    haarProbUnitary_isProbability d
  rw [MeasureTheory.integral_const]
  simp

/-- The coherent-state Haar integral is Hermitian: `(∫ ρ_g dg)† = ∫ ρ_g dg`.
    Each `ρ_g = |v^g⟩⟨v^g|` is Hermitian, and `conjTranspose` commutes with
    Bochner integration as a continuous ℝ-linear map. -/
lemma coherent_integral_hermitian (d n : ℕ) [NeZero d] [NeZero n] :
    (∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d))† =
    ∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d) := by
  let ct_CLM : Op (d ^ n) →L[ℝ] Op (d ^ n) := {
    toLinearMap := {
      toFun := fun M => M†
      map_add' := fun M N => conjTranspose_add M N
      map_smul' := fun r M => by simp [conjTranspose_smul, star_trivial]
    }
    cont := continuous_star
  }
  have h_int := coherentStateDensityOp_integrable d n
  have h := (ct_CLM.integral_comp_comm h_int).symm
  simp only [show ∀ M : Op (d ^ n), ct_CLM M = M† from fun _ => rfl] at h
  rw [h]
  congr 1
  funext g
  exact (coherentStateDensityOp g n).toPosSemidefOp.toHermitianOp.isHermitian

/-!
## Haar de Finetti Integral Bridge

These lemmas connect the abstract tensor-power integral
`∫ σ^⊗n d(deFinetti_haarMeasure d)(σ)` with the concrete coherent-state
Haar integral used in the Schur-lemma proof.
-/

/-- Each entry of `σ ↦ σ.tensorPowGen n` varies continuously with `σ`. -/
lemma continuous_tensorPowGen_entry {d n : ℕ} [NeZero d]
    (i j : Fin (d ^ n)) :
    Continuous (fun σ : DensityOp d => (σ.tensorPowGen n).toOp i j) := by
  set e := @finFunctionFinEquiv d n
  set fi := e.symm i
  set fj := e.symm j
  have h_eq : ∀ σ : DensityOp d,
      (σ.tensorPowGen n).toOp i j =
        ∏ l : Fin n, σ.toOp (fi l) (fj l) := by
    intro σ
    have := tensorPowGen_toOp_eq_prod σ fi fj
    simp only [Equiv.apply_symm_apply, e, fi, fj] at this
    exact this
  simp_rw [h_eq]
  exact continuous_finset_prod Finset.univ (fun l _ =>
    (continuous_apply_apply (fi l) (fj l)).comp continuous_induced_dom)

/-- The entry `(i,j)` of `integralTensorPower n μ` is the integral of the
    corresponding tensor-power entries against `μ`. -/
lemma integralTensorPower_toOp_apply {d : ℕ} [NeZero d]
    (n : ℕ) [NeZero n] [NeZero (d ^ n)]
    (μ : InfoTheory.DeFinetti.DensityMeasure d)
    (i j : Fin (d ^ n)) :
    (InfoTheory.DeFinetti.integralTensorPower n μ).toOp i j =
      ∫ σ : DensityOp d, (σ.tensorPowGen n).toOp i j ∂μ.measure := by
  rfl

/-- The integral tensor power of the Haar de Finetti measure equals the
    coherent-state Haar integral. -/
lemma integralTensorPower_deFinetti_haar_eq_coherent_integral {d n : ℕ} [NeZero d] [NeZero n] :
    (InfoTheory.DeFinetti.integralTensorPower n
      (InfoTheory.DeFinetti.deFinetti_haarMeasure d)).toOp =
    ∫ g : unitaryGroup (Fin d) ℂ,
      (coherentStateDensityOp g n).toOp ∂(haarProbUnitary d) := by
  have h_tensor_eq : ∀ g : unitaryGroup (Fin d) ℂ,
      ((coherentSingleCopy g).tensorPowGen n).toOp = (coherentStateDensityOp g n).toOp :=
    fun g => (coherentState_is_tensorPow g).symm
  have h_measure_eq :
      (InfoTheory.DeFinetti.deFinetti_haarMeasure d).measure =
        Measure.map (fun g : unitaryGroup (Fin d) ℂ => coherentSingleCopy g)
          (haarProbUnitary d) := by
    rfl
  ext i j
  rw [integralTensorPower_toOp_apply]
  rw [h_measure_eq]
  have h_f_cont := continuous_tensorPowGen_entry (d := d) (n := n) i j
  rw [MeasureTheory.integral_map_of_stronglyMeasurable
    coherentSingleCopy_measurable h_f_cont.stronglyMeasurable]
  simp_rw [h_tensor_eq]
  symm
  haveI : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
  have h_M_cont : Continuous (fun g : unitaryGroup (Fin d) ℂ =>
      (coherentStateDensityOp g n).toOp) :=
    continuous_matrix (fun a b => coherentStateDensityOp_entry_continuous a b)
  have h_int : MeasureTheory.Integrable
      (fun g : unitaryGroup (Fin d) ℂ => (coherentStateDensityOp g n).toOp)
      (haarProbUnitary d) :=
    h_M_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact matrix_integral_entry (fun g : unitaryGroup (Fin d) ℂ =>
    (coherentStateDensityOp g n).toOp) h_int i j

/-- Inner product of coherent states factors as a power: ⟨v_g|v_h⟩ = (g†h)₀₀ⁿ.
    The coherent state |v_g^⊗n⟩ is a product state, so the inner product factors:
    ⟨v_g^⊗n|v_h^⊗n⟩ = ∏ⱼ ⟨g·e₀|h·e₀⟩ = (∑ₐ conj(g_{a,0}) h_{a,0})ⁿ = ((g†h)₀₀)ⁿ. -/
lemma coherentState_overlap_eq_entry_pow {d : ℕ} [NeZero d]
    (g h : unitaryGroup (Fin d) ℂ) (n : ℕ) [NeZero n] :
    (coherentStateKet g n).dag * coherentStateKet h n =
    (∑ a : Fin d, starRingEnd ℂ (g.val a 0) * h.val a 0) ^ (n : ℕ) := by
  -- Unfold to ∑_x conj(∏_j g_{d_j(x),0}) * ∏_j h_{d_j(x),0}
  simp only [bra_mul_ket_eq, coherentStateKet, Ket.dag]
  -- Distribute conj over product and combine
  simp_rw [map_prod, ← Finset.prod_mul_distrib]
  -- Reindex via finFunctionFinEquiv: Fin(d^n) → (Fin n → Fin d)
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  simp_rw [bigEndian_digit_eq_finFunctionFinEquiv hd_pos]
  -- Reindex: ∏_j f(j.rev) = ∏_j f(j)
  have hprod_rev : ∀ (x : Fin (d ^ n)),
      (∏ j : Fin n,
        starRingEnd ℂ ((g : Matrix (Fin d) (Fin d) ℂ) (finFunctionFinEquiv.symm x j.rev) 0) *
          (h : Matrix (Fin d) (Fin d) ℂ) (finFunctionFinEquiv.symm x j.rev) 0) =
      (∏ j : Fin n,
        starRingEnd ℂ ((g : Matrix (Fin d) (Fin d) ℂ) (finFunctionFinEquiv.symm x j) 0) *
          (h : Matrix (Fin d) (Fin d) ℂ) (finFunctionFinEquiv.symm x j) 0) := by
    intro x
    refine Finset.prod_equiv Fin.revPerm (by simp) (fun j _ => ?_)
    simp [Fin.revPerm_apply]
  simp_rw [hprod_rev]
  -- Reindex: ∑_{x:Fin(d^n)} F(equiv.symm x) = ∑_{f:Fin n→Fin d} F(f)
  set F := fun (ff : Fin n → Fin d) => ∏ j : Fin n,
        starRingEnd ℂ ((g : Matrix (Fin d) (Fin d) ℂ) (ff j) 0) *
          (h : Matrix (Fin d) (Fin d) ℂ) (ff j) 0
  change ∑ x, F (finFunctionFinEquiv.symm x) = _
  rw [Equiv.sum_comp finFunctionFinEquiv.symm F]
  -- Factor: ∑_f ∏_j h(f(j)) = (∑_a h(a))^n
  rw [← Fintype.prod_sum (f := fun (_ : Fin n) (a : Fin d) =>
      starRingEnd ℂ ((g : Matrix (Fin d) (Fin d) ℂ) a 0) *
        (h : Matrix (Fin d) (Fin d) ℂ) a 0)]
  rw [Finset.prod_const, Finset.card_fin]

/-- The shifted overlap: after Haar left-translation g → hg, the overlap becomes conj(g₀₀)ⁿ.
    Key identity: (hg)†h = g†(h†h) = g†, so ⟨v_{hg}|v_h⟩ = ((hg)†h)₀₀ⁿ = conj(g₀₀)ⁿ. -/
lemma overlap_hg_h_eq_conj_entry_pow {d : ℕ} [NeZero d]
    (g h : unitaryGroup (Fin d) ℂ) (n : ℕ) [NeZero n] :
    (coherentStateKet (h * g) n).dag * coherentStateKet h n =
    (starRingEnd ℂ (g.val 0 0)) ^ (n : ℕ) := by
  rw [coherentState_overlap_eq_entry_pow (h * g) h n]
  congr 1
  -- Need: ∑_a conj((hg)_{a,0}) * h_{a,0} = conj(g_{0,0})
  -- This is ((hg)†h)_{0,0} = (g†h†h)_{0,0} = (g†)_{0,0} = conj(g_{0,0})
  -- First show ∑_a conj((hg)_{a,0}) h_{a,0} = ((hg)†h)_{0,0}
  have key : ∑ a : Fin d, starRingEnd ℂ ((h * g).val a 0) * h.val a 0 =
      (((h * g).val)ᴴ * h.val) 0 0 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rfl
  rw [key]
  have hmul : (h * g).val = h.val * g.val := rfl
  rw [hmul, conjTranspose_mul, Matrix.mul_assoc]
  have hstar : h.valᴴ * h.val = 1 := by
    change star h.val * h.val = 1; exact h.2.1
  rw [hstar, Matrix.mul_one]
  simp [Matrix.conjTranspose_apply]

/-- normSq of the shifted overlap: |⟨v_{hg}|v_h⟩|² = |g₀₀|^{2n}. -/
lemma normSq_overlap_hg_h {d : ℕ} [NeZero d]
    (g h : unitaryGroup (Fin d) ℂ) (n : ℕ) [NeZero n] :
    Complex.normSq ((coherentStateKet (h * g) n).dag * coherentStateKet h n) =
    Complex.normSq (g.val 0 0) ^ n := by
  rw [overlap_hg_h_eq_conj_entry_pow g h n]
  rw [map_pow]
  congr 1
  exact Complex.normSq_conj _

end InfoTheory.DeFinetti.PureState
