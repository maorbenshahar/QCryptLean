import QCryptLean.InfoTheory.Postselection.SchurWeylKappa
import QCryptLean.Quantum.Operators.MatrixIntegral
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Group.Integral

/-!
# QKD postselection — Schur–Weyl twirl projection and permutation transport

The Haar-twirl channel is
`twirlMap dA dR n T := ∫ (1_{Aⁿ}⊗U^{⊗n}) T (1_{Aⁿ}⊗U^{⊗n})† dU`.
It underlies Nahar, Tupkary, Zhao, Lütkenhaus and Tan’s Lemma 10 construction
`Tₙ = twirlMap dA dR n Θₙ`. This module proves self-adjointness, idempotence and the
fixed-point/commutant characterization, together with the ricochet and trace identities that
transport the symmetric-group action across the unnormalized maximally entangled vector `|Θₙ⟩`,
where `Θₙ = |Θₙ⟩⟨Θₙ|`.

## Main definitions
- `InfoTheory.Postselection.twirlMap dA dR n T` : the Haar twirl channel by `1_{Aⁿ} ⊗ U^{⊗n}`.
- `InfoTheory.Postselection.thetaKet dA dR n hdim` : the maximally-entangled vector `|Θ⟩` underlying
  `maxEntangledProjectorPaired`, as a standalone `Fin (dA^n * dR^n) → ℂ`.

## Main statements
- `InfoTheory.Postselection.twirlKernel_continuous`,
`InfoTheory.Postselection.twirlIntegrand_integrable` :
  the kernel `U ↦ 1_{Aⁿ} ⊗ U^{⊗n}` is continuous and the twirl integrand is Haar-integrable.
- `InfoTheory.Postselection.twirlMap_maxEntangledProjectorPaired` : consistency,
  `maxEntangledUnitaryTwirl dA dR n hdim = twirlMap dA dR n (maxEntangledProjectorPaired ..)`.
- `InfoTheory.Postselection.twirlMap_selfAdjoint` : `Tr[(twirlMap A)ᴴ B] = Tr[Aᴴ (twirlMap
B)]`.
- `InfoTheory.Postselection.twirlMap_idempotent` : `twirlMap (twirlMap T) = twirlMap T`.
- `InfoTheory.Postselection.twirlMap_eq_iff_commute` : `twirlMap T = T ↔ ∀ U, Commute (K U)
T`.
- `InfoTheory.Postselection.ricochet_permutationRepresentation_thetaKet`:
  `(1_{Aⁿ} ⊗ U_σ^{dR}).mulVec Θ = (U_{σ⁻¹}^{dA} ⊗ 1_{Rⁿ}).mulVec Θ`.
- `InfoTheory.Postselection.thetaKet_tensor_one_bilinear`:
  `⟨Θ|(M⊗1)|Θ⟩ = Tr M`.
- `InfoTheory.Postselection.permRep_conjTranspose_mul_trace_eq_fixed_card`:
  `Tr[U_π† U_σ] = #{f : f∘(π⁻¹σ) = f}`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Math.RepresentationTheory
open Quantum.Symmetry InfoTheory.DeFinetti Quantum.Channels MeasureTheory Math.HaarMeasure
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.Postselection

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-! ## Continuity and integrability of the twirl kernel -/

/-- The Kraus map `U ↦ 1_{Aⁿ} ⊗ U^{⊗n}` of the Haar twirl is continuous in `U`. -/
theorem twirlKernel_continuous (dA dR n : ℕ) [NeZero dR] :
    Continuous (fun U : Matrix.unitaryGroup (Fin dR) ℂ =>
      Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) :=
  Op.continuous_tensor.comp
    (continuous_const.prodMk ((Op.continuous_tensorPow n).comp continuous_subtype_val))

/-- The twirl integrand `U ↦ K(U) T K(U)ᴴ` is continuous in `U`. -/
private lemma twirlIntegrand_continuous (dA dR n : ℕ) [NeZero dR]
    (T : Op (dA ^ n * dR ^ n)) :
    Continuous (fun U : Matrix.unitaryGroup (Fin dR) ℂ =>
      (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) * T *
        (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))ᴴ) := by
  have hK := twirlKernel_continuous dA dR n
  exact (hK.matrix_mul continuous_const).matrix_mul hK.matrix_conjTranspose

/-- The twirl integrand `U ↦ K(U) T K(U)ᴴ` is Bochner-integrable over the Haar
probability measure (continuity + compactness of `U(dR)`). -/
theorem twirlIntegrand_integrable (dA dR n : ℕ) [NeZero dR]
    (T : Op (dA ^ n * dR ^ n)) :
    MeasureTheory.Integrable (fun U : Matrix.unitaryGroup (Fin dR) ℂ =>
      (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) * T *
        (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))ᴴ) (haarProbUnitary dR) := by
  have : MeasureTheory.IsProbabilityMeasure (haarProbUnitary dR) :=
    haarProbUnitary_isProbability dR
  exact (twirlIntegrand_continuous dA dR n T).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **E1 def: the Haar twirl channel** `Tₙ = twirlMap dA dR n Θₙ` (Nahar et al. Lemma 10),
generalized to an arbitrary operator argument `T`:

`twirlMap dA dR n T = ∫ (1_{Aⁿ} ⊗ U^{⊗n}) T (1_{Aⁿ} ⊗ U^{⊗n})† dU`. -/
def twirlMap (dA dR n : ℕ) [NeZero dR] (T : Op (dA ^ n * dR ^ n)) :
    Op (dA ^ n * dR ^ n) :=
  ∫ U : Matrix.unitaryGroup (Fin dR) ℂ,
    (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) * T *
      (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))ᴴ
    ∂(haarProbUnitary dR)

/-- **Consistency**: `maxEntangledUnitaryTwirl` is `twirlMap` applied to the maximally
entangled projector `Θₙ`. -/
theorem twirlMap_maxEntangledProjectorPaired (dA dR n : ℕ) [NeZero dA] [NeZero dR] [NeZero n]
    (hdim : dA ≤ dR) :
    maxEntangledUnitaryTwirl dA dR n hdim
      = twirlMap dA dR n (maxEntangledProjectorPaired dA dR n hdim) := rfl

/-! ## Twirl kernel: homomorphism, unitarity, and self-adjoint inversion identity -/

/-- The Kraus map `K(U) := 1_{Aⁿ} ⊗ U^{⊗n}` is a monoid homomorphism from the unitary
group into the unitary operators on `Aⁿ ⊗ Rⁿ`: `K(V)K(U) = K(VU)`. -/
private lemma twirlKernel_mul (dA dR n : ℕ) [NeZero dR]
    (V U : Matrix.unitaryGroup (Fin dR) ℂ) :
    (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (V : Op dR) n)) *
      (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) =
    Op.tensor (1 : Op (dA ^ n))
      (Op.tensorPow ((V * U : Matrix.unitaryGroup (Fin dR) ℂ) : Op dR) n) := by
  rw [Op.tensor_mul, Matrix.one_mul, ← Op.mul_tensorPow]
  rfl

/-- The Kraus map `K(U)` is unitary. -/
private lemma twirlKernel_unitary (dA dR n : ℕ) [NeZero dR]
    (U : Matrix.unitaryGroup (Fin dR) ℂ) :
    (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) *
      (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))ᴴ = 1 ∧
    (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))ᴴ *
      (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) = 1 := by
  have hU1 : (U : Op dR) * (U : Op dR)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff).mp U.2
  have hU2 : (U : Op dR)ᴴ * (U : Op dR) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').mp U.2
  constructor
  · rw [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul, Matrix.one_mul,
      Op.tensorPow_mul_conjTranspose_self hU1, Op.tensor_one]
  · rw [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul, Matrix.one_mul,
      Op.conjTranspose_tensorPow_mul_self hU2, Op.tensor_one]

/-- **Range invariance of the twirl.** `twirlMap dA dR n T` is a fixed point of conjugation by
every Kraus operator `K(V) = 1_{Aⁿ} ⊗ V^{⊗n}`. Sandwiching the Haar average by `K(V)` and using
the Kraus homomorphism `K(V)K(U) = K(VU)` (`twirlKernel_mul`) reduces the resulting integral
to itself via the Haar left-invariance substitution `U ↦ VU`
(`MeasureTheory.integral_mul_left_eq_self`). The structural fact underlying both `E1b`
(idempotence) and the forward direction of `E1c` (fixed points are the commutant). -/
private lemma twirlMap_kernel_conj_eq_self (dA dR n : ℕ) [NeZero dR] (T : Op (dA ^ n * dR ^ n))
    (V : Matrix.unitaryGroup (Fin dR) ℂ) :
    (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (V : Op dR) n)) * twirlMap dA dR n T *
      (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (V : Op dR) n))ᴴ = twirlMap dA dR n T := by
  have : (haarProbUnitary dR).IsMulLeftInvariant := by
    unfold haarProbUnitary haarOnUnitary; infer_instance
  set K : Matrix.unitaryGroup (Fin dR) ℂ → Op (dA ^ n * dR ^ n) := fun U =>
    Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n) with hK
  set f : Matrix.unitaryGroup (Fin dR) ℂ → Op (dA ^ n * dR ^ n) := fun U => K U * T * (K U)ᴴ
    with hf
  have hfInt : MeasureTheory.Integrable f (haarProbUnitary dR) :=
    twirlIntegrand_integrable dA dR n T
  have htwirl : twirlMap dA dR n T = ∫ U, f U ∂(haarProbUnitary dR) := rfl
  set L : Op (dA ^ n * dR ^ n) →L[ℝ] Op (dA ^ n * dR ^ n) :=
    ((LinearMap.mulLeft ℝ (K V)).comp (LinearMap.mulRight ℝ ((K V)ᴴ))).toContinuousLinearMap
    with hL
  have hLeq : ∀ X : Op (dA ^ n * dR ^ n), L X = K V * X * (K V)ᴴ := fun X => by
    simp only [hL, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    rw [Matrix.mul_assoc]
  have hpull : L (∫ U, f U ∂(haarProbUnitary dR)) = ∫ U, L (f U) ∂(haarProbUnitary dR) :=
    (L.integral_comp_comm hfInt).symm
  have hstep : ∫ U, L (f U) ∂(haarProbUnitary dR) = ∫ U, f (V * U) ∂(haarProbUnitary dR) := by
    congr 1
    funext U
    rw [hLeq]
    change K V * (K U * T * (K U)ᴴ) * (K V)ᴴ = K (V * U) * T * (K (V * U))ᴴ
    rw [show K (V * U) = K V * K U from (twirlKernel_mul dA dR n V U).symm,
      Matrix.conjTranspose_mul]
    noncomm_ring
  have hshift : ∫ U, f (V * U) ∂(haarProbUnitary dR) = ∫ U, f U ∂(haarProbUnitary dR) :=
    MeasureTheory.integral_mul_left_eq_self f V
  calc K V * twirlMap dA dR n T * (K V)ᴴ
      = K V * (∫ U, f U ∂(haarProbUnitary dR)) * (K V)ᴴ := by rw [htwirl]
    _ = L (∫ U, f U ∂(haarProbUnitary dR)) := (hLeq _).symm
    _ = ∫ U, L (f U) ∂(haarProbUnitary dR) := hpull
    _ = ∫ U, f (V * U) ∂(haarProbUnitary dR) := hstep
    _ = ∫ U, f U ∂(haarProbUnitary dR) := hshift
    _ = twirlMap dA dR n T := htwirl.symm

/-- **E1b (idempotent).** `twirlMap dA dR n (twirlMap dA dR n T) = twirlMap dA dR n T`.
Immediate from range invariance (`twirlMap_kernel_conj_eq_self`): the outer twirl integrand
`K(V) · twirlMap T · K(V)ᴴ` is constant (`= twirlMap T`) in `V`, and the Haar measure has
total mass `1`. -/
theorem twirlMap_idempotent (dA dR n : ℕ) [NeZero dR] (T : Op (dA ^ n * dR ^ n)) :
    twirlMap dA dR n (twirlMap dA dR n T) = twirlMap dA dR n T := by
  have : MeasureTheory.IsProbabilityMeasure (haarProbUnitary dR) :=
    haarProbUnitary_isProbability dR
  have hOuter : twirlMap dA dR n (twirlMap dA dR n T) =
      ∫ V : Matrix.unitaryGroup (Fin dR) ℂ,
        (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (V : Op dR) n)) * (twirlMap dA dR n T) *
          (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (V : Op dR) n))ᴴ
        ∂(haarProbUnitary dR) := rfl
  rw [hOuter]
  simp_rw [twirlMap_kernel_conj_eq_self dA dR n T]
  simp

/-- **E1c (fixed-point/commutant).** `twirlMap dA dR n T = T` iff `T` commutes with every
Kraus operator `K(U) = 1_{Aⁿ} ⊗ U^{⊗n}`.

(⇒) `twirlMap_kernel_conj_eq_self` gives `K(V) T K(V)ᴴ = K(V) twirlMap T K(V)ᴴ = twirlMap T = T`
(the last step by hypothesis); unitarity of `K(V)` then yields `K(V) T = T K(V)`.
(⇐) If `T` commutes with every `K(U)`, the integrand collapses to the constant `T`
(unitarity of `K(U)`), and the Haar probability measure has total mass `1`. -/
theorem twirlMap_eq_iff_commute (dA dR n : ℕ) [NeZero dR] (T : Op (dA ^ n * dR ^ n)) :
    twirlMap dA dR n T = T ↔
      ∀ U : Matrix.unitaryGroup (Fin dR) ℂ,
        Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) T := by
  have : MeasureTheory.IsProbabilityMeasure (haarProbUnitary dR) :=
    haarProbUnitary_isProbability dR
  set K : Matrix.unitaryGroup (Fin dR) ℂ → Op (dA ^ n * dR ^ n) := fun U =>
    Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n) with hK
  set f : Matrix.unitaryGroup (Fin dR) ℂ → Op (dA ^ n * dR ^ n) := fun U => K U * T * (K U)ᴴ
    with hf
  have htwirl : twirlMap dA dR n T = ∫ U, f U ∂(haarProbUnitary dR) := rfl
  constructor
  · intro hFix V
    have hKey : K V * T * (K V)ᴴ = T := by
      rw [← hFix]
      exact twirlMap_kernel_conj_eq_self dA dR n T V
    have hcomm : K V * T = T * K V := by
      have hmul : K V * T * (K V)ᴴ * K V = T * K V := by rw [hKey]
      rw [Matrix.mul_assoc, (twirlKernel_unitary dA dR n V).2, Matrix.mul_one] at hmul
      exact hmul
    exact hcomm
  · intro hComm
    have hconst : ∀ U : Matrix.unitaryGroup (Fin dR) ℂ, f U = T := by
      intro U
      change K U * T * (K U)ᴴ = T
      rw [(hComm U).eq, Matrix.mul_assoc, (twirlKernel_unitary dA dR n U).1, Matrix.mul_one]
    rw [htwirl]
    simp_rw [hconst]
    simp

/-! ## Inversion-invariance of the Haar (probability) measure on `U(dR)`

Needed for `E1a` (self-adjointness of `twirlMap`): a compact group's Haar measure is
inversion-invariant, even when the group is non-abelian (`U(dR)` for `dR ≥ 2` is not). The
proof mirrors `haarOnUnitary_isMulRightInvariant`: the pushforward `μ.inv = map Inv.inv μ` is
left-invariant (using the *right*-invariance of `μ` and the identity
`(h·) ∘ inv = inv ∘ (· * h⁻¹)`), has the same total (finite) mass as `μ`, hence by uniqueness of
Haar measure on a compact group it equals `μ`. -/

/-- **The Haar measure on `U(dR)` is inversion-invariant** (any compact group is unimodular
and, moreover, its Haar measure is invariant under inversion). -/
private instance haarOnUnitary_isInvInvariant (d : ℕ) [NeZero d] :
    MeasureTheory.Measure.IsInvInvariant (haarOnUnitary d) := by
  set μ : MeasureTheory.Measure (Matrix.unitaryGroup (Fin d) ℂ) := haarOnUnitary d with hμdef
  have hμRI : μ.IsMulRightInvariant := haarOnUnitary_isMulRightInvariant d
  have hHaarμ : MeasureTheory.Measure.IsHaarMeasure μ := by
    rw [hμdef]; unfold haarOnUnitary; infer_instance
  have hInvMeas :
      Measurable (Inv.inv : Matrix.unitaryGroup (Fin d) ℂ → Matrix.unitaryGroup (Fin d) ℂ) := by
    fun_prop
  have hμFin : MeasureTheory.IsFiniteMeasure μ := ⟨haarOnUnitary_finite d⟩
  set ν : MeasureTheory.Measure (Matrix.unitaryGroup (Fin d) ℂ) := μ.inv with hνdef
  refine ⟨?_⟩
  change ν = μ
  have hνLI : ν.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    rw [hνdef, MeasureTheory.Measure.inv_def,
      MeasureTheory.Measure.map_map (by fun_prop) hInvMeas]
    have hcomm : (fun x : Matrix.unitaryGroup (Fin d) ℂ => h * x) ∘ (fun x => x⁻¹) =
        (fun x : Matrix.unitaryGroup (Fin d) ℂ => x⁻¹) ∘ (fun x => x * h⁻¹) := by
      funext x; simp [_root_.mul_inv_rev]
    rw [hcomm, ← MeasureTheory.Measure.map_map hInvMeas (by fun_prop),
      MeasureTheory.map_mul_right_eq_self μ h⁻¹]
  have hνFin : MeasureTheory.IsFiniteMeasure ν := by
    rw [hνdef, MeasureTheory.Measure.inv_def]; exact μ.isFiniteMeasure_map _
  have hνFinC : MeasureTheory.IsFiniteMeasureOnCompacts ν := inferInstance
  have hsmul : ν = MeasureTheory.Measure.haarScalarFactor ν μ • μ :=
    MeasureTheory.Measure.isMulInvariant_eq_smul_of_compactSpace ν μ
  have hmass : ν Set.univ = μ Set.univ := by
    rw [hνdef, MeasureTheory.Measure.inv_def,
      MeasureTheory.Measure.map_apply hInvMeas MeasurableSet.univ]
    simp
  have hfin : μ Set.univ ≠ ⊤ := ne_of_lt (haarOnUnitary_finite d)
  have hpos : μ Set.univ ≠ 0 :=
    ne_of_gt (pos_iff_ne_zero.mpr (@MeasureTheory.Measure.IsOpenPosMeasure.open_pos _ _ _ μ _
      Set.univ isOpen_univ Set.univ_nonempty))
  set c := MeasureTheory.Measure.haarScalarFactor ν μ with hc
  have hc1 : c = 1 := by
    have huniv := congrArg (fun m => m Set.univ) hsmul
    simp only [MeasureTheory.Measure.smul_apply] at huniv
    rw [hmass] at huniv
    have heq : (c : ENNReal) * μ Set.univ = 1 * μ Set.univ := by
      rw [one_mul]; exact huniv.symm
    have hcast : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hpos hfin).mp heq
    exact_mod_cast hcast
  rw [hsmul, hc1, one_smul]

/-- **The Haar probability measure on `U(dR)` is inversion-invariant**: a scalar multiple of
an inversion-invariant measure is inversion-invariant. -/
private instance haarProbUnitary_isInvInvariant (d : ℕ) [NeZero d] :
    MeasureTheory.Measure.IsInvInvariant (haarProbUnitary d) := by
  have hInv : MeasureTheory.Measure.IsInvInvariant (haarOnUnitary d) :=
    haarOnUnitary_isInvInvariant d
  refine ⟨?_⟩
  change ((haarOnUnitary d Set.univ)⁻¹ • haarOnUnitary d).inv =
    (haarOnUnitary d Set.univ)⁻¹ • haarOnUnitary d
  rw [MeasureTheory.Measure.inv_def,
    MeasureTheory.Measure.map_smul _ measurable_inv.aemeasurable,
    ← MeasureTheory.Measure.inv_def, MeasureTheory.Measure.inv_eq_self]

/-! ## E1a: `twirlMap` is self-adjoint for the Hilbert–Schmidt pairing -/

/-- Conjugate transpose commutes with the Bochner integral of a matrix-valued function
(`ctCLM : M ↦ Mᴴ` is a continuous `ℝ`-linear map on finite-dimensional matrices). -/
private lemma integral_conjTranspose_comm {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {N : ℕ} (F : α → Op N)
    (hF : MeasureTheory.Integrable F μ) :
    (∫ a, F a ∂μ)ᴴ = ∫ a, (F a)ᴴ ∂μ := by
  let ctCLM : Op N →L[ℝ] Op N := {
    toLinearMap := {
      toFun := fun M => Mᴴ
      map_add' := fun M1 M2 => Matrix.conjTranspose_add M1 M2
      map_smul' := fun r M => by simp [Matrix.conjTranspose_smul, star_trivial] }
    cont := continuous_star }
  exact (ctCLM.integral_comp_comm hF).symm

/-- The Kraus map inverts under conjugate transpose: `K(U)ᴴ = K(U⁻¹)`. -/
private lemma twirlKernel_conjTranspose (dA dR n : ℕ) [NeZero dR]
    (U : Matrix.unitaryGroup (Fin dR) ℂ) :
    (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))ᴴ =
      Op.tensor (1 : Op (dA ^ n))
        (Op.tensorPow ((U⁻¹ : Matrix.unitaryGroup (Fin dR) ℂ) : Op dR) n) := by
  have hUinv : ((U⁻¹ : Matrix.unitaryGroup (Fin dR) ℂ) : Op dR) = (U : Op dR)ᴴ := by
    rw [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose]
  rw [hUinv, Op.tensor_conjTranspose, conjTranspose_one, Op.conjTranspose_tensorPow]

/-- **E1a (self-adjoint).** `twirlMap` is self-adjoint with respect to the Hilbert–Schmidt
pairing `⟨X,Y⟩ = Tr(Xᴴ Y)`: `Tr[(twirlMap A)ᴴ B] = Tr[Aᴴ (twirlMap B)]`.

Uses `twirlKernel_conjTranspose` to show `(twirlMap A)ᴴ = twirlMap Aᴴ`, trace cyclicity to move
`K(U)` across the product, and the Haar **inversion**-invariance substitution `U ↦ U⁻¹`
(`MeasureTheory.integral_inv_eq_self`, via `haarProbUnitary_isInvInvariant`) to identify the
resulting integral with `twirlMap B`. -/
theorem twirlMap_selfAdjoint (dA dR n : ℕ) [NeZero dR] (A B : Op (dA ^ n * dR ^ n)) :
    ((twirlMap dA dR n A)ᴴ * B).trace = (Aᴴ * twirlMap dA dR n B).trace := by
  have : MeasureTheory.IsProbabilityMeasure (haarProbUnitary dR) :=
    haarProbUnitary_isProbability dR
  set K : Matrix.unitaryGroup (Fin dR) ℂ → Op (dA ^ n * dR ^ n) := fun U =>
    Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n) with hK
  have hKconj : ∀ U : Matrix.unitaryGroup (Fin dR) ℂ, (K U)ᴴ = K U⁻¹ :=
    fun U => twirlKernel_conjTranspose dA dR n U
  -- Step 1: `(twirlMap A)ᴴ = twirlMap Aᴴ`.
  have hHermStep : (twirlMap dA dR n A)ᴴ = twirlMap dA dR n Aᴴ := by
    have hconj := integral_conjTranspose_comm (fun U => K U * A * (K U)ᴴ)
      (twirlIntegrand_integrable dA dR n A)
    have hpt : ∀ U : Matrix.unitaryGroup (Fin dR) ℂ,
        (K U * A * (K U)ᴴ)ᴴ = K U * Aᴴ * (K U)ᴴ := by
      intro U
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      noncomm_ring
    unfold twirlMap
    rw [hconj]
    simp_rw [hpt]
    rfl
  rw [hHermStep]
  -- Step 2: pull the right-multiplication-by-`B` trace CLM through the integral.
  let trMulB : Op (dA ^ n * dR ^ n) →L[ℝ] ℂ :=
    (Matrix.traceLinearMap (Fin (dA ^ n * dR ^ n)) ℝ ℂ).toContinuousLinearMap.comp
      (LinearMap.mulRight ℝ B).toContinuousLinearMap
  have htrMulB : ∀ X : Op (dA ^ n * dR ^ n), trMulB X = (X * B).trace := fun X => by
    simp [trMulB, Matrix.traceLinearMap_apply]
  have hfIntAH : MeasureTheory.Integrable (fun U => K U * Aᴴ * (K U)ᴴ) (haarProbUnitary dR) :=
    twirlIntegrand_integrable dA dR n Aᴴ
  have step1 : (twirlMap dA dR n Aᴴ * B).trace =
      ∫ U, (K U * Aᴴ * (K U)ᴴ * B).trace ∂(haarProbUnitary dR) := by
    rw [← htrMulB]
    change trMulB (∫ U, K U * Aᴴ * (K U)ᴴ ∂(haarProbUnitary dR)) = _
    exact (trMulB.integral_comp_comm hfIntAH).symm
  -- Step 3: cyclicity — move `K(U)` from the left of the product to the right.
  have hcyc : ∀ U : Matrix.unitaryGroup (Fin dR) ℂ,
      (K U * Aᴴ * (K U)ᴴ * B).trace = (Aᴴ * ((K U)ᴴ * B * K U)).trace := by
    intro U
    have e1 : K U * Aᴴ * (K U)ᴴ * B = K U * (Aᴴ * (K U)ᴴ * B) := by noncomm_ring
    have e2 : (Aᴴ * (K U)ᴴ * B) * K U = Aᴴ * ((K U)ᴴ * B * K U) := by noncomm_ring
    rw [e1, Matrix.trace_mul_comm, e2]
  have step2 : ∫ U, (K U * Aᴴ * (K U)ᴴ * B).trace ∂(haarProbUnitary dR) =
      ∫ U, (Aᴴ * ((K U)ᴴ * B * K U)).trace ∂(haarProbUnitary dR) := by
    congr 1; funext U; exact hcyc U
  -- Step 4: the inversion substitution `U ↦ U⁻¹` identifies the remaining integral with
  -- `twirlMap dA dR n B`.
  have hgpt : ∀ U : Matrix.unitaryGroup (Fin dR) ℂ,
      (K U)ᴴ * B * K U = K U⁻¹ * B * (K U⁻¹)ᴴ := by
    intro U
    rw [hKconj U]
    congr 2
    rw [hKconj U⁻¹, inv_inv]
  have hgeq : (fun U : Matrix.unitaryGroup (Fin dR) ℂ => (K U)ᴴ * B * K U) =
      (fun U => (fun V => K V * B * (K V)ᴴ) U⁻¹) := funext hgpt
  have hgInt : MeasureTheory.Integrable
      (fun U : Matrix.unitaryGroup (Fin dR) ℂ => (K U)ᴴ * B * K U) (haarProbUnitary dR) := by
    rw [hgeq]
    exact (twirlIntegrand_integrable dA dR n B).comp_inv
  have hsubst : ∫ U, (K U)ᴴ * B * K U ∂(haarProbUnitary dR) = twirlMap dA dR n B := by
    rw [hgeq]
    unfold twirlMap
    exact MeasureTheory.integral_inv_eq_self
      (fun V : Matrix.unitaryGroup (Fin dR) ℂ => K V * B * (K V)ᴴ) (haarProbUnitary dR)
  -- Step 5: pull the left-multiplication-by-`Aᴴ` trace CLM through the integral.
  let trMulAH : Op (dA ^ n * dR ^ n) →L[ℝ] ℂ :=
    (Matrix.traceLinearMap (Fin (dA ^ n * dR ^ n)) ℝ ℂ).toContinuousLinearMap.comp
      (LinearMap.mulLeft ℝ Aᴴ).toContinuousLinearMap
  have htrMulAH : ∀ X : Op (dA ^ n * dR ^ n), trMulAH X = (Aᴴ * X).trace := fun X => by
    simp [trMulAH, Matrix.traceLinearMap_apply]
  have step3 : ∫ U, (Aᴴ * ((K U)ᴴ * B * K U)).trace ∂(haarProbUnitary dR) =
      (Aᴴ * twirlMap dA dR n B).trace := by
    rw [← hsubst, ← htrMulAH]
    change ∫ U, trMulAH ((K U)ᴴ * B * K U) ∂(haarProbUnitary dR) = _
    exact trMulAH.integral_comp_comm hgInt
  rw [step1, step2, step3]

/-! ## Step 7: ricochet and trace identities -/

/-- **Step-7, Identity 3 (turnkey trace identity).** `Tr[U_π† U_σ] = #{f : f∘(π⁻¹σ) = f}`:
`U_π† = U_{π⁻¹}` (`permutationRepresentation_inv`) and `U_{π⁻¹}U_σ = U_{π⁻¹σ}`
(`permutationRepresentation_mul`), so the trace is the fixed-tensor-word count
`permutationRepresentation_trace_eq_fixed_card` at `π⁻¹σ`. -/
theorem permRep_conjTranspose_mul_trace_eq_fixed_card (d n : ℕ) [NeZero d]
    (π σ : Equiv.Perm (Fin n)) :
    ((permutationRepresentation d n π)ᴴ * permutationRepresentation d n σ).trace =
      ((Finset.univ.filter (fun f : Fin n → Fin d => f ∘ ⇑(π⁻¹ * σ) = f)).card : ℂ) := by
  rw [← permutationRepresentation_inv, permutationRepresentation_mul,
    permutationRepresentation_trace_eq_fixed_card]

/-! ## `thetaKet`: the maximally entangled vector underlying `maxEntangledProjectorPaired` -/

/-- The digit-wise embedding `Fin (dA^n) → Fin (dR^n)` underlying `thetaKet`
(`maxEntangledProjectorPaired`'s local `emb`): decode into `n` base-`dA` digits, embed each via
`Fin.castLE hdim`, re-encode in base `dR`. -/
private def embDigit (dA dR n : ℕ) (hdim : dA ≤ dR) : Fin (dA ^ n) → Fin (dR ^ n) :=
  fun a => finFunctionFinEquiv (fun j => Fin.castLE hdim (finFunctionFinEquiv.symm a j))

/-- **`|Θ⟩` (step 7)**: the maximally entangled vector underlying `maxEntangledProjectorPaired`
(`SchurWeylTwirl.lean`) as a standalone `Fin (dA^n * dR^n) → ℂ`:
`⟨(a,r)|Θ⟩ = 1` iff `r = ι^{(n)}(a)` (the digit-wise embedding), else `0`. -/
def thetaKet (dA dR n : ℕ) (hdim : dA ≤ dR) : Fin (dA ^ n * dR ^ n) → ℂ :=
  fun i => if (finProdFinEquiv.symm i).2 =
      finFunctionFinEquiv (fun j =>
        Fin.castLE hdim (finFunctionFinEquiv.symm (finProdFinEquiv.symm i).1 j))
    then 1 else 0

/-- `thetaKet` unfolds through `embDigit`. -/
private lemma thetaKet_apply_eq_embDigit (dA dR n : ℕ) (hdim : dA ≤ dR)
    (i : Fin (dA ^ n * dR ^ n)) :
    thetaKet dA dR n hdim i =
      if (finProdFinEquiv.symm i).2 = embDigit dA dR n hdim (finProdFinEquiv.symm i).1
      then 1 else 0 := rfl

/-- `embDigit` is injective (composition of the injective digit-decoding equivalence,
the injective `Fin.castLE`, and the injective digit-encoding equivalence). -/
private lemma embDigit_injective (dA dR n : ℕ) (hdim : dA ≤ dR) :
    Function.Injective (embDigit dA dR n hdim) := by
  intro a b hab
  simp only [embDigit] at hab
  have heq := finFunctionFinEquiv.injective hab
  have hcastinj := Fin.castLE_injective hdim
  have hfun : finFunctionFinEquiv.symm a = finFunctionFinEquiv.symm b :=
    funext fun j => hcastinj (congr_fun heq j)
  exact finFunctionFinEquiv.symm.injective hfun

/-- **Entry formula (`1_{Aⁿ} ⊗ Y`-side).** `(1⊗Y).mulVec Θ` at `(a,r)` is the `(r, emb a)` entry
of `Y`: the `A`-slot delta collapses the outer sum to `a'=a`, and the `thetaKet` indicator
collapses the inner sum to `r' = emb a`. -/
private lemma tensorOneLeft_mulVec_thetaKet (dA dR n : ℕ) [NeZero dA] [NeZero dR]
    (hdim : dA ≤ dR) (Y : Op (dR ^ n)) (a : Fin (dA ^ n)) (r : Fin (dR ^ n)) :
    (Op.tensor (1 : Op (dA ^ n)) Y).mulVec (thetaKet dA dR n hdim) (finProdFinEquiv (a, r)) =
      Y r (embDigit dA dR n hdim a) := by
  simp only [Matrix.mulVec, dotProduct, Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    kroneckerMap_apply, Matrix.one_apply]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin (dA ^ n) × Fin (dR ^ n) => (if a = p.1 then (1 : ℂ) else 0) * Y r p.2 *
      thetaKet dA dR n hdim (finProdFinEquiv p))
    (by
      intro k
      have hk : finProdFinEquiv (k.divNat, k.modNat) = k := by
        rw [← finProdFinEquiv_symm_apply]; exact finProdFinEquiv.apply_symm_apply k
      simp [hk])]
  rw [Fintype.sum_prod_type]
  have inner : ∀ a' : Fin (dA ^ n),
      (∑ r' : Fin (dR ^ n), (if a = a' then (1 : ℂ) else 0) * Y r r' *
        thetaKet dA dR n hdim (finProdFinEquiv (a', r'))) =
      if a = a' then Y r (embDigit dA dR n hdim a') else 0 := by
    intro a'
    by_cases haa : a = a'
    · subst haa
      simp only [ite_true, one_mul]
      rw [Finset.sum_eq_single (embDigit dA dR n hdim a)]
      · rw [thetaKet_apply_eq_embDigit]
        simp
      · intro r' _ hr'
        rw [thetaKet_apply_eq_embDigit]
        simp only [Equiv.symm_apply_apply]
        rw [ite_eq_right hr']
        ring
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [haa]
  simp_rw [inner]
  rw [Finset.sum_ite_eq Finset.univ a (fun a' => Y r (embDigit dA dR n hdim a'))]
  simp [Finset.mem_univ]

/-- **Entry formula (`X ⊗ 1_{Rⁿ}`-side).** `(X⊗1).mulVec Θ` at `(a,r)` is
`Σ_{a'} X_{a,a'} · [r = emb a']`: the `R`-slot identity collapses the inner sum to `r'=r`. -/
private lemma tensorOneRight_mulVec_thetaKet (dA dR n : ℕ) [NeZero dA] [NeZero dR]
    (hdim : dA ≤ dR) (X : Op (dA ^ n)) (a : Fin (dA ^ n)) (r : Fin (dR ^ n)) :
    (Op.tensor X (1 : Op (dR ^ n))).mulVec (thetaKet dA dR n hdim) (finProdFinEquiv (a, r)) =
      ∑ a' : Fin (dA ^ n), X a a' * (if r = embDigit dA dR n hdim a' then (1 : ℂ) else 0) := by
  simp only [Matrix.mulVec, dotProduct, Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    kroneckerMap_apply, Matrix.one_apply]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin (dA ^ n) × Fin (dR ^ n) => X a p.1 * (if r = p.2 then (1 : ℂ) else 0) *
      thetaKet dA dR n hdim (finProdFinEquiv p))
    (by
      intro k
      have hk : finProdFinEquiv (k.divNat, k.modNat) = k := by
        rw [← finProdFinEquiv_symm_apply]; exact finProdFinEquiv.apply_symm_apply k
      simp [hk])]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a' _
  rw [Finset.sum_eq_single r]
  · rw [thetaKet_apply_eq_embDigit]
    simp
  · intro r' _ hr'
    rw [thetaKet_apply_eq_embDigit]
    simp only [Equiv.symm_apply_apply]
    rw [ite_eq_right (Ne.symm hr')]
    ring
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Step-7, ricochet identity.** Permuting the `Rⁿ` slots of `Θ` by `σ` equals permuting the
`Aⁿ` slots by `σ⁻¹`:

`(1_{Aⁿ} ⊗ U_σ^{dR}).mulVec Θ = (U_{σ⁻¹}^{dA} ⊗ 1_{Rⁿ}).mulVec Θ`.

The point `a0 := eA(eA.symm(a) ∘ σ.symm)` is the unique `A`-index making the `Aⁿ`-side
permutation entry `U_{σ⁻¹}^{dA}(a,a0) = 1` (a tautology after unwinding `(σ⁻¹).symm = σ`); at
every other index the entry is `0`, collapsing the `Aⁿ`-side sum
(`tensorOneRight_mulVec_thetaKet`) to the single value `[r = emb a0]`. The `Rⁿ`-side closed form
(`tensorOneLeft_mulVec_thetaKet`) `U_σ^{dR}(r, emb a) = [r = emb a0]` matches it exactly, since
`emb a0 = ι^{(n)}(eA.symm(a) ∘ σ.symm)` is precisely the digit-wise-embedded image of the
target tensor word `eR.symm(emb a) ∘ σ.symm`. -/
theorem ricochet_permutationRepresentation_thetaKet (dA dR n : ℕ) [NeZero dA] [NeZero dR]
    (hdim : dA ≤ dR) (σ : Equiv.Perm (Fin n)) :
    (Op.tensor (1 : Op (dA ^ n)) (permutationRepresentation dR n σ)).mulVec
        (thetaKet dA dR n hdim) =
      (Op.tensor (permutationRepresentation dA n σ⁻¹) (1 : Op (dR ^ n))).mulVec
        (thetaKet dA dR n hdim) := by
  funext i
  obtain ⟨⟨a, r⟩, rfl⟩ : ∃ p : Fin (dA ^ n) × Fin (dR ^ n), finProdFinEquiv p = i :=
    ⟨finProdFinEquiv.symm i, finProdFinEquiv.apply_symm_apply i⟩
  rw [tensorOneLeft_mulVec_thetaKet, tensorOneRight_mulVec_thetaKet]
  set a0 : Fin (dA ^ n) := finFunctionFinEquiv (finFunctionFinEquiv.symm a ∘ ⇑σ.symm) with ha0
  -- The `Aⁿ`-side entry is `1` at `a0` and `0` elsewhere.
  have hcondIff : ∀ a' : Fin (dA ^ n),
      (finFunctionFinEquiv.symm a = finFunctionFinEquiv.symm a' ∘ ⇑σ) ↔ a' = a0 := by
    intro a'
    constructor
    · intro h
      apply finFunctionFinEquiv.symm.injective
      rw [ha0, Equiv.symm_apply_apply]
      funext j
      have hj := congr_fun h (σ.symm j)
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at hj
      exact hj.symm
    · intro h
      subst h
      rw [ha0, Equiv.symm_apply_apply]
      funext j
      simp [Function.comp_apply]
  have hentry : ∀ a' : Fin (dA ^ n),
      permutationRepresentation dA n σ⁻¹ a a' = if a' = a0 then 1 else 0 := by
    intro a'
    unfold permutationRepresentation
    simp only [Matrix.of_apply, show (σ⁻¹).symm = σ from rfl]
    by_cases h : a' = a0
    · simp [h, (hcondIff a').mpr h]
    · rw [ite_eq_right h, ite_eq_right]
      intro hc; exact h ((hcondIff a').mp hc)
  simp_rw [hentry, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ a0]
  simp only [Finset.mem_univ, ite_true]
  -- The `Rⁿ`-side closed form matches the collapsed value.
  have hcondIff2 :
      (finFunctionFinEquiv.symm r =
          finFunctionFinEquiv.symm (embDigit dA dR n hdim a) ∘ ⇑σ.symm) ↔
        r = embDigit dA dR n hdim a0 := by
    unfold embDigit
    simp only [Equiv.symm_apply_apply]
    constructor
    · intro h
      apply finFunctionFinEquiv.symm.injective
      simp only [Equiv.symm_apply_apply]
      rw [ha0, Equiv.symm_apply_apply]
      funext j
      have hj := congr_fun h j
      simp only [Function.comp_apply] at hj
      exact hj
    · intro h
      subst h
      simp only [Equiv.symm_apply_apply, ha0]
      funext j
      rfl
  unfold permutationRepresentation
  simp only [Matrix.of_apply]
  by_cases h : r = embDigit dA dR n hdim a0
  · rw [ite_eq_left h, ite_eq_left ((hcondIff2).mpr h)]
  · rw [ite_eq_right h, ite_eq_right]
    intro hc; exact h ((hcondIff2).mp hc)

/-- **Step-7, Identity 2 (turnkey bilinear identity).** `⟨Θ|(M⊗1)|Θ⟩ = Tr M`: reindexing the
dot product over `Fin(dA^n) × Fin(dR^n)` pairs, the `Rⁿ`-slot identity in `M ⊗ 1` forces both
copies of `Θ`'s indicator onto the same `r = emb a'`, collapsing the double sum to the
diagonal `Σ_a M a a = Tr M` (`embDigit_injective` collapses `emb a = emb a'` to `a = a'`). -/
theorem thetaKet_tensor_one_bilinear (dA dR n : ℕ) [NeZero dA] [NeZero dR]
    (hdim : dA ≤ dR) (M : Op (dA ^ n)) :
    dotProduct (star (thetaKet dA dR n hdim))
        ((Op.tensor M (1 : Op (dR ^ n))).mulVec (thetaKet dA dR n hdim)) = M.trace := by
  simp only [dotProduct, Pi.star_apply]
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin (dA ^ n) × Fin (dR ^ n) => star (thetaKet dA dR n hdim (finProdFinEquiv p)) *
      (Op.tensor M (1 : Op (dR ^ n))).mulVec (thetaKet dA dR n hdim) (finProdFinEquiv p))
    (by
      intro k
      have hk : finProdFinEquiv (k.divNat, k.modNat) = k := by
        rw [← finProdFinEquiv_symm_apply]; exact finProdFinEquiv.apply_symm_apply k
      simp [hk])]
  rw [Fintype.sum_prod_type]
  simp_rw [tensorOneRight_mulVec_thetaKet]
  have hstar : ∀ a : Fin (dA ^ n), ∀ r : Fin (dR ^ n),
      star (thetaKet dA dR n hdim (finProdFinEquiv (a, r))) =
        (if r = embDigit dA dR n hdim a then (1 : ℂ) else 0) := by
    intro a r
    rw [thetaKet_apply_eq_embDigit]
    simp only [Equiv.symm_apply_apply]
    by_cases h : r = embDigit dA dR n hdim a
    · simp [h]
    · simp [h]
  simp_rw [hstar]
  have hinner : ∀ a : Fin (dA ^ n),
      (∑ r : Fin (dR ^ n), (if r = embDigit dA dR n hdim a then (1 : ℂ) else 0) *
        ∑ a' : Fin (dA ^ n), M a a' * (if r = embDigit dA dR n hdim a' then (1 : ℂ) else 0)) =
        M a a := by
    intro a
    rw [Finset.sum_eq_single (embDigit dA dR n hdim a)]
    · simp only [ite_true, one_mul]
      rw [Finset.sum_eq_single a]
      · simp
      · intro a' _ ha'
        have hne : embDigit dA dR n hdim a ≠ embDigit dA dR n hdim a' := fun hcontra =>
          ha' (embDigit_injective dA dR n hdim hcontra).symm
        rw [ite_eq_right hne, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro r' _ hr'
      rw [ite_eq_right hr', zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hinner]
  simp [Matrix.trace, Matrix.diag]

end InfoTheory.Postselection

end
