import QCryptLean.InfoTheory.Postselection.RawKeyMeasurementDischarge
import QCryptLean.InfoTheory.Postselection.MeasureThenHashFactorization
import QCryptLean.InfoTheory.Postselection.AcceptBranchBounds

/-!
# Measure-then-hash postselection

Extended mixture entropy floors and seed-visible leftover hashing bound the reference experiment.
The postselection lift turns that reference bound into coherent-attack security, including group-
symmetric reference constructions.
-/

open Quantum.Operators Quantum.Channels Quantum.Metrics Quantum.TensorProducts
open Quantum.Symmetry
open MeasureTheory
open InfoTheory.SmoothMinEntropy InfoTheory.DeFinetti InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.Postselection

variable {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero n]

/-! ## The group-symmetric measure-then-hash reference bound

The group-symmetric analogue of `postselection_referenceBound_of_measureThenHash`
(below) is derived here, upstream of the plain theorem, whose trivial-group
instance it is (see the docstring there). -/

/-- **Rank bound for the integral of canonical purifications** (the paper's
`eq:splittingoffV`, main.tex:1391–1395): the integral of the
canonical IID purifications against a `prodRep`-invariant measure has rank at most the
group-symmetric prefactor `g_{n,x}` with `x = ∑ i ∑ j (mA i)² (mB j)²`. Each integrand is
supported on the paired symmetric subspace (`purificationDensityOp_in_paired_symmetric_subspace`)
and, μ-a.e., on the paired group-twirl range (`groupPurification_prod`), so the integral is
supported by the product of the two commuting projectors, whose trace is `g_{n,x}`. -/
lemma rank_integral_purificationDensityOp_tensorPowGen_groupSymmetric_le
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {kA kB : ℕ} [NeZero (dA * dB)]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (mA : Fin kA → ℕ) (mB : Fin kB → ℕ)
    (hxA : (groupTwirlProjector πA).trace = ∑ i : Fin kA, (((mA i : ℕ) : ℂ) ^ 2))
    (hxB : (groupTwirlProjector πB).trace = ∑ j : Fin kB, (((mB j : ℕ) : ℂ) ^ 2))
    (μ : DensityMeasure (dA * dB))
    (hμinv : IsGroupInvariantMeasure (prodRep πA πB) μ) :
    Matrix.rank (∫ σ : DensityOp (dA * dB),
      (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) ≤
      deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n := by
  have hAB : NeZero (dA * dB) := ⟨mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  have hABn : NeZero ((dA * dB) ^ n) := ⟨pow_ne_zero n (NeZero.ne (dA * dB))⟩
  have hsq : NeZero (((dA * dB) ^ n) * ((dA * dB) ^ n)) := ⟨Nat.mul_ne_zero (NeZero.ne _)
    (NeZero.ne _)⟩
  have hπG : IsUnitaryRep (prodRep πA πB) := prodRep_isUnitaryRep πA hπA πB hπB
  have hint := InfoTheory.DeFinetti.integrable_purificationDensityOp_tensorPowGen
    (d := dA * dB) (n := n) μ
  -- Step 1: paired-symmetric support of the integral (each integrand is paired-symmetric)
  have hPsupp : symmetricProjectorPaired (dA * dB) n *
      (∫ σ : DensityOp (dA * dB),
        (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) *
      symmetricProjectorPaired (dA * dB) n =
      ∫ σ : DensityOp (dA * dB),
        (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure :=
    InfoTheory.DeFinetti.integral_purificationDensityOp_tensorPowGen_supported
      (d := dA * dB) (n := n) μ
  -- Step 2: group-twirl support, transported through the integral from the a.e. invariance
  have hRsupp : groupPairedTwirlProjector n (prodRep πA πB) *
      (∫ σ : DensityOp (dA * dB),
        (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) *
      groupPairedTwirlProjector n (prodRep πA πB) =
      ∫ σ : DensityOp (dA * dB),
        (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure := by
    let L := (LinearMap.mulRight ℂ (groupPairedTwirlProjector n (prodRep πA πB))).comp
      (LinearMap.mulLeft ℂ (groupPairedTwirlProjector n (prodRep πA πB)))
    calc _ = ∫ σ : DensityOp (dA * dB),
        groupPairedTwirlProjector n (prodRep πA πB) *
          (purificationDensityOp (σ.tensorPowGen n)).toOp *
          groupPairedTwirlProjector n (prodRep πA πB) ∂μ.measure :=
        (L.toContinuousLinearMap.integral_comp_comm hint).symm
      _ = _ := MeasureTheory.integral_congr_ae
        (hμinv.mono fun σ hσ =>
          purificationDensityOp_groupTwirlSupported (prodRep πA πB) hπG (σ.tensorPowGen n)
            ((isIIDGroupInvariant_tensorPowGen_iff (prodRep πA πB) hπG σ).2 hσ))
  -- Step 3: the product projection `Q = R * P` sandwiches the integral back to itself
  obtain ⟨hP_idem, hP_herm⟩ := Quantum.Channels.symmetricProjectorPaired_is_projector'
    (dA * dB) n
  obtain ⟨hPl, hPr⟩ := idempotent_sandwich_left_right (P := symmetricProjectorPaired (dA * dB) n)
    hP_idem hPsupp
  obtain ⟨hRl, hRr⟩ := idempotent_sandwich_left_right
    (P := groupPairedTwirlProjector n (prodRep πA πB))
    (groupPairedTwirlProjector_isProjection (prodRep πA πB) hπG) hRsupp
  have hQ : (groupPairedTwirlProjector n (prodRep πA πB) *
      symmetricProjectorPaired (dA * dB) n) *
      (∫ σ : DensityOp (dA * dB),
        (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) *
      (groupPairedTwirlProjector n (prodRep πA πB) *
        symmetricProjectorPaired (dA * dB) n) =
      ∫ σ : DensityOp (dA * dB),
        (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure := by
    calc (groupPairedTwirlProjector n (prodRep πA πB) * symmetricProjectorPaired (dA * dB) n) *
        (∫ σ : DensityOp (dA * dB),
          (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) *
        (groupPairedTwirlProjector n (prodRep πA πB) *
          symmetricProjectorPaired (dA * dB) n) =
        groupPairedTwirlProjector n (prodRep πA πB) * (symmetricProjectorPaired (dA * dB) n *
            (∫ σ : DensityOp (dA * dB),
              (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure)) *
          (groupPairedTwirlProjector n (prodRep πA πB) *
            symmetricProjectorPaired (dA * dB) n) := by
          rw [mul_assoc (groupPairedTwirlProjector n (prodRep πA πB))
            (symmetricProjectorPaired (dA * dB) n)
            (∫ σ : DensityOp (dA * dB),
              (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure)]
      _ = groupPairedTwirlProjector n (prodRep πA πB) *
          (∫ σ : DensityOp (dA * dB),
            (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) *
          (groupPairedTwirlProjector n (prodRep πA πB) *
            symmetricProjectorPaired (dA * dB) n) := by rw [hPl]
      _ = (groupPairedTwirlProjector n (prodRep πA πB) *
          (∫ σ : DensityOp (dA * dB),
            (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) *
          groupPairedTwirlProjector n (prodRep πA πB)) * symmetricProjectorPaired (dA * dB) n := by
          rw [← mul_assoc (groupPairedTwirlProjector n (prodRep πA πB) *
            (∫ σ : DensityOp (dA * dB),
              (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure))
            (groupPairedTwirlProjector n (prodRep πA πB))
            (symmetricProjectorPaired (dA * dB) n)]
      _ = (∫ σ : DensityOp (dA * dB),
          (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) *
          symmetricProjectorPaired (dA * dB) n := by rw [hRsupp]
      _ = ∫ σ : DensityOp (dA * dB),
          (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure := hPr
  -- Step 4: rank of the integral = rank of its `Q`-sandwich ≤ rank of `Q` = trace of `Q`
  -- trace of the one-round product twirl as a complex cast (cf. GroupSymmetricDeFinetti.lean)
  have hxc : (groupTwirlProjector (prodRep πA πB)).trace =
      (((∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2 : ℕ) : ℕ) : ℂ) := by
    rw [groupTwirlProjector_prod_trace_sumSq πA hπA πB hπB mA mB hxA hxB]
    push_cast
    rfl
  -- trace of the product projection `Q = R * P` is the group-symmetric prefactor
  have hQtrace : ((groupPairedTwirlProjector n (prodRep πA πB) *
      symmetricProjectorPaired (dA * dB) n)).trace =
      ((deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n : ℕ) : ℂ) :=
    groupPairedTwirlProjector_mul_symmetricProjectorPaired_trace (prodRep πA πB) hπG hxc
  -- Hermiticity of `Q = R * P` from Hermiticity and commutation of the two projectors
  have hQherm : ((groupPairedTwirlProjector n (prodRep πA πB) *
      symmetricProjectorPaired (dA * dB) n))ᴴ =
      groupPairedTwirlProjector n (prodRep πA πB) *
      symmetricProjectorPaired (dA * dB) n := by
    rw [Matrix.conjTranspose_mul,
      groupPairedTwirlProjector_isHermitian (prodRep πA πB) hπG, hP_herm,
      groupPairedTwirlProjector_commute_symmetricProjectorPaired (prodRep πA πB)]
  have hQidem : IsIdempotentElem (groupPairedTwirlProjector n (prodRep πA πB) *
      symmetricProjectorPaired (dA * dB) n) :=
    IsIdempotentElem.mul_of_commute
      (groupPairedTwirlProjector_commute_symmetricProjectorPaired (prodRep πA πB))
      (groupPairedTwirlProjector_isProjection (prodRep πA πB) hπG) hP_idem
  have hQrank : Matrix.rank (groupPairedTwirlProjector n (prodRep πA πB) *
      symmetricProjectorPaired (dA * dB) n) =
      deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n := by
    have h1 := Math.SpectralTheory.hermitian_idempotent_trace_re_eq_rank _ hQherm hQidem
    rw [hQtrace] at h1
    simp only [Complex.natCast_re] at h1
    exact_mod_cast h1.symm
  calc Matrix.rank (∫ σ : DensityOp (dA * dB),
      (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure)
      = Matrix.rank ((groupPairedTwirlProjector n (prodRep πA πB) *
          symmetricProjectorPaired (dA * dB) n) *
        (∫ σ : DensityOp (dA * dB),
          (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure) *
        (groupPairedTwirlProjector n (prodRep πA πB) *
          symmetricProjectorPaired (dA * dB) n)) := congrArg Matrix.rank hQ.symm
    _ ≤ Matrix.rank (groupPairedTwirlProjector n (prodRep πA πB) *
      symmetricProjectorPaired (dA * dB) n) := Matrix.rank_mul_le_right _ _
    _ = _ := hQrank

/-- **Pure extension of the integral of canonical purifications**: group-symmetric analogue of
`exists_isPure_partialTraceB_eq_integral_purificationDensityOp_tensorPowGen`
(DeFinetti/IntegralPurification.lean:86): a pure state on
`((A B)ⁿ ⊗ (A B)ⁿ) ⊗ V` with `dim V = g_{n,x}`, `x = ∑ i ∑ j (mA i)² (mB j)²`, whose
partial trace over `V` is the integral of the canonical IID purifications — via
`densityOp_purification_exists_of_rank_le` with the group-symmetric rank bound
`rank_integral_purificationDensityOp_tensorPowGen_groupSymmetric_le`
(the paper's `eq:splittingoffV`, main.tex:1391–1395). -/
lemma exists_isPure_partialTraceB_eq_integral_groupSymmetric
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {kA kB : ℕ}
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (mA : Fin kA → ℕ) (mB : Fin kB → ℕ)
    (hxA : (groupTwirlProjector πA).trace = ∑ i : Fin kA, (((mA i : ℕ) : ℂ) ^ 2))
    (hxB : (groupTwirlProjector πB).trace = ∑ j : Fin kB, (((mB j : ℕ) : ℂ) ^ 2))
    (μ : DensityMeasure (dA * dB))
    (hμinv : IsGroupInvariantMeasure (prodRep πA πB) μ) :
    ∃ ψ : DensityOp (((dA * dB) ^ n * (dA * dB) ^ n) *
        deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n),
      ψ.IsPure ∧ partialTraceB ψ.toOp =
        ∫ σ : DensityOp (dA * dB),
          (purificationDensityOp (σ.tensorPowGen n)).toOp ∂μ.measure := by
  have hAB : NeZero (dA * dB) := ⟨mul_ne_zero (NeZero.ne dA) (NeZero.ne dB)⟩
  have hABn : NeZero ((dA * dB) ^ n) := ⟨pow_ne_zero n (NeZero.ne (dA * dB))⟩
  have hsq : NeZero (((dA * dB) ^ n) * ((dA * dB) ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have gpos : NeZero (deFinettiPrefactor
      (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n) :=
    ⟨(deFinettiPrefactor_pos _ n).ne'⟩
  have := μ.isProbability
  let ρ := DensityOp.integral μ.measure
    (fun σ : DensityOp (dA * dB) => purificationDensityOp (σ.tensorPowGen n))
    (InfoTheory.DeFinetti.integrable_purificationDensityOp_tensorPowGen μ)
  exact densityOp_purification_exists_of_rank_le
    (r := deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n) ρ
      (rank_integral_purificationDensityOp_tensorPowGen_groupSymmetric_le πA hπA πB hπB mA mB
        hxA hxB μ hμinv)

/-- **Pure blocks extension for the measure-then-hash register**: group-symmetric analogue of
`MeasureThenHash.exists_isPure_extendedRawKeyCQ_partialTraceB_eq`
(MeasureThenHashFactorization.lean:102) with the generic prefactor replaced by
`g_x = deFinettiPrefactor (∑ i, ∑ j, (mA i)² (mB j)²) n` and the pure extension supplied
by `exists_isPure_partialTraceB_eq_integral_groupSymmetric`: a pure `τ` on
`((A B)ⁿ ⊗ (A B)ⁿ) ⊗ g_x` whose B-marginal is the de Finetti fixed-marginal mixture and
whose extended raw-key blocks all have B-marginal `M.mixCQ_En μ`. The proof follows the
generic one: `exists_isPure_partialTraceB_eq_integral_groupSymmetric` produces exactly the
integral marginal that `C.integral_rawKeyCQ_stateMap_toOp` needs. -/
lemma exists_isPure_extendedRawKeyCQ_partialTraceB_eq_groupSymmetric
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {kA kB : ℕ}
    (M : RawKeyMeasurement dA dB n) (l' : ℕ) (C : MeasureThenHash M l')
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (mA : Fin kA → ℕ) (mB : Fin kB → ℕ)
    (hxA : (groupTwirlProjector πA).trace = ∑ i : Fin kA, (((mA i : ℕ) : ℂ) ^ 2))
    (hxB : (groupTwirlProjector πB).trace = ∑ j : Fin kB, (((mB j : ℕ) : ℂ) ^ 2))
    (μ : DensityMeasure (dA * dB))
    (hμinv : IsGroupInvariantMeasure (prodRep πA πB) μ)
    [hgx : NeZero (deFinettiPrefactor
      (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n)] :
    ∃ τ : DensityOp ((dA * dB) ^ n *
        ((dA * dB) ^ n *
          deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n)),
      τ.IsPure ∧
      τ.partialTraceB = deFinettiMixtureFixedMarginal dA dB n μ ∧
      ∀ x : Fin M.toProtocol.rawKeyDim,
        partialTraceB ((C.extendedRawKeyCQ (deFinettiPrefactor
            (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n) τ).stateMap
          x).toOp = ((M.mixCQ_En μ (C.integrable μ)).stateMap x).toOp := by
  obtain ⟨ψ, hpure, hmarg⟩ := exists_isPure_partialTraceB_eq_integral_groupSymmetric (n := n)
    πA hπA πB hπB mA mB hxA hxB μ hμinv
  let g := deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n
  let τ := DensityOp.castDim (Nat.mul_assoc ((dA * dB) ^ n) ((dA * dB) ^ n) g) ψ
  have hop : τ.toOp = Op.castDim (Nat.mul_assoc ((dA * dB) ^ n) ((dA * dB) ^ n) g) ψ.toOp :=
    densityOp_castDim_toOp _ ψ
  refine ⟨τ, DensityOp.castDim_IsPure _ _ hpure, ?_, ?_⟩
  · apply DensityOp.ext
    change partialTraceB τ.toOp = _
    rw [hop]
    calc
      _ = partialTraceB (partialTraceB ψ.toOp) :=
        (partialTraceB_partialTraceB_eq_assoc ψ.toOp).symm
      _ = _ := by
        rw [hmarg]
        exact partialTraceB_integral_purificationDensityOp_tensorPowGen μ
  · intro x
    rw [C.extendedRawKeyCQ_partialTraceB, hop]
    rw [Op.castDim_cancel, hmarg]
    exact C.integral_rawKeyCQ_stateMap_toOp μ x

/-- Group-symmetric measure-then-hash postselection from extended IID entropy.
The reference bound admits zero accepted mass, an empty accepting set, and a zero hashing budget.
The invariant reference measure supplies the reduced purification dimension. -/
theorem postselection_referenceBound_of_measureThenHash_groupSymmetric
    {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A] [Fintype G_B]
    {kA kB : ℕ}
    (M : RawKeyMeasurement dA dB n) (σA : DensityOp dA)
    (εAT εPA εbar : ℝ) (l' : ℕ)
    (goodSet : Set (DensityOp (dA * dB)))
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA)
    (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (mA : Fin kA → ℕ) (mB : Fin kB → ℕ)
    (hxA : (groupTwirlProjector πA).trace = ∑ i : Fin kA, (((mA i : ℕ) : ℂ) ^ 2))
    (hxB : (groupTwirlProjector πB).trace = ∑ j : Fin kB, (((mB j : ℕ) : ℂ) ^ 2))
    (hcondS : SatisfiesAcceptTestBound (fixedMarginalSet σA)
      (goodSet ∩ fixedMarginalSet σA) M.pAcc εAT)
    (hcondLHL : ∀ σ ∈ goodSet ∩ fixedMarginalSet σA,
      hashingError M.toProtocol.l (smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE) ≤ εPA)
    (hεPA : 0 ≤ εPA) (hεbar : 0 ≤ εbar)
    (C : MeasureThenHash M l')
    (hl' : (l' : ℝ) ≤
      (M.toProtocol.l : ℝ) -
        2 * Real.logb 2
          (deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n))
    (hClosed : IsClosed goodSet)
    (μ : DensityMeasure (dA * dB)) (hμ : IsFixedMarginalMeasure σA μ)
    (hμinv : IsGroupInvariantMeasure (prodRep πA πB) μ) :
    SatisfiesReferenceBound M.toProtocol l' μ (coherentIIDSecrecy εAT εPA εbar) := by
  have := μ.isProbability
  have hacc : ∀ σ ∈ fixedMarginalSet σA \ goodSet, M.pAcc σ ≤ εAT := by
    intro σ hσ
    exact hcondS.2.2 σ ⟨hσ.1, fun hgood => hσ.2 hgood.1⟩
  let hproof : HasIIDSecurityProof M.toProtocol εAT εPA εbar :=
    { ι := DensityOp (dA * dB)
      Sσhat := fixedMarginalSet σA
      S := goodSet ∩ fixedMarginalSet σA
      pAcc := M.pAcc
      condTraceDist := fun _ => 0
      condDim := M.condDim
      condDim_neZero := M.condDim_neZero
      rawKeyCQ := M.rawKeyCQ
      ref := M.refCommon
      eq10 := hcondS
      eq11 := ⟨hεPA, hεbar, by
        intro σ hσ
        constructor
        · simp only [mul_zero]
          exact add_nonneg (hashingError_nonneg _ _)
            (mul_nonneg (by norm_num) hεbar)
        · exact add_le_add (hcondLHL σ hσ) le_rfl⟩ }
  have hbad := M.badBranchBlockOp_weight_le_of_pAcc_le μ (C.integrable μ)
    (fixedMarginalSet σA) hμ goodSet hClosed.measurableSet εAT hcondS.1.1 hacc
  have := M.toProtocol.keyDim_neZero
  have := M.toProtocol.annDim_neZero
  have hgx : NeZero (deFinettiPrefactor
      (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n) :=
    ⟨(deFinettiPrefactor_pos _ n).ne'⟩
  obtain ⟨τ, hτ_pure, hτ_marg, hτ_blocks⟩ :=
    exists_isPure_extendedRawKeyCQ_partialTraceB_eq_groupSymmetric M l' C
      πA hπA πB hπB mA mB hxA hxB μ hμinv
  obtain ⟨V, hV', hPA⟩ := C.exists_hashDifference_eq_conj_of_partialTraceB_eq
    (deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n)
    (deFinettiMixturePurification dA dB n μ) τ
    (purificationDensityOp_isPure (deFinettiMixtureFixedMarginal dA dB n μ)) hτ_pure
    (hτ_marg.trans (deFinettiMixturePurification_partialTraceB dA dB n μ).symm)
  exact postselection_protocol_referenceBound_of_iidSecurityProof M μ εAT εPA εbar l'
    (deFinettiPrefactor (∑ i : Fin kA, ∑ j : Fin kB, (mA i) ^ 2 * (mB j) ^ 2) n) hgx
    (C.integrable μ) (C.extendedRawKeyCQ _ τ) hτ_blocks hproof hl' rfl rfl HEq.rfl HEq.rfl
    goodSet (fixedMarginalSet σA) HEq.rfl hClosed
    (isClosed_eq partialTraceB_continuous_general continuous_const) hμ
    C.continuous_rawKeyCQ_stateMap_toOp hbad C.hash C.hash_isUniversal C.card_key V hV' hPA

/-- A measure-then-hash protocol satisfies the reference bound from extended IID entropy,
using one common positive-definite reference and the ordinary de Finetti dimension. -/
theorem postselection_referenceBound_of_measureThenHash
    (M : RawKeyMeasurement dA dB n) (σA : DensityOp dA)
    (εAT εPA εbar : ℝ) (l' : ℕ)
    (goodSet : Set (DensityOp (dA * dB)))
    (hcondS : SatisfiesAcceptTestBound (fixedMarginalSet σA)
      (goodSet ∩ fixedMarginalSet σA) M.pAcc εAT)
    (hcondLHL : ∀ σ ∈ goodSet ∩ fixedMarginalSet σA,
      hashingError M.toProtocol.l (smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE) ≤ εPA)
    (hεPA : 0 ≤ εPA) (hεbar : 0 ≤ εbar)
    (C : MeasureThenHash M l')
    (hl' : (l' : ℝ) ≤
      (M.toProtocol.l : ℝ) - 2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n))
    (hClosed : IsClosed goodSet)
    (μ : DensityMeasure (dA * dB)) (hμ : IsFixedMarginalMeasure σA μ) :
    SatisfiesReferenceBound M.toProtocol l' μ (coherentIIDSecrecy εAT εPA εbar) := by
  have hxA : (groupTwirlProjector (fun _ : Unit => (1 : Op dA))).trace =
      ∑ i : Fin 1, (((((fun _ : Fin 1 => dA) i : ℕ) : ℂ)) ^ 2) := by
    rw [groupTwirlProjector_unit_const_one_trace, Fin.sum_univ_one]
  have hxB : (groupTwirlProjector (fun _ : Unit => (1 : Op dB))).trace =
      ∑ j : Fin 1, (((((fun _ : Fin 1 => dB) j : ℕ) : ℂ)) ^ 2) := by
    rw [groupTwirlProjector_unit_const_one_trace, Fin.sum_univ_one]
  have hsum : (∑ i : Fin 1, ∑ j : Fin 1,
      ((fun _ : Fin 1 => dA) i) ^ 2 * ((fun _ : Fin 1 => dB) j) ^ 2) = dA ^ 2 * dB ^ 2 := by
    simp
  have hl'g : (l' : ℝ) ≤ (M.toProtocol.l : ℝ) - 2 * Real.logb 2
      (deFinettiPrefactor (∑ i : Fin 1, ∑ j : Fin 1,
        ((fun _ : Fin 1 => dA) i) ^ 2 * ((fun _ : Fin 1 => dB) j) ^ 2) n) := by
    rwa [hsum]
  have hμinv : IsGroupInvariantMeasure (prodRep (fun _ : Unit => (1 : Op dA))
      (fun _ : Unit => (1 : Op dB))) μ := by
    filter_upwards with σ
    intro g
    rw [prodRep_const_one g]
    simp
  exact postselection_referenceBound_of_measureThenHash_groupSymmetric M σA εAT εPA εbar l'
    goodSet (fun _ : Unit => (1 : Op dA)) isUnitaryRep_const_one
    (fun _ : Unit => (1 : Op dB)) isUnitaryRep_const_one
    (fun _ : Fin 1 => dA) (fun _ : Fin 1 => dB) hxA hxB hcondS hcondLHL hεPA hεbar C hl'g
    hClosed μ hμ hμinv

/-- Extended IID entropy gives coherent security for a permutation-invariant
measure-then-hash protocol with a full-rank fixed marginal. -/
theorem postselection_security_of_measureThenHash
    (M : RawKeyMeasurement dA dB n) (σA : DensityOp dA) (hσA : σA.toOp.PosDef)
    (εAT εPA εbar : ℝ) (l' : ℕ)
    (goodSet : Set (DensityOp (dA * dB)))
    (hcondS : SatisfiesAcceptTestBound (fixedMarginalSet σA)
      (goodSet ∩ fixedMarginalSet σA) M.pAcc εAT)
    (hcondLHL : ∀ σ ∈ goodSet ∩ fixedMarginalSet σA,
      hashingError M.toProtocol.l (smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE) ≤ εPA)
    (hεPA : 0 ≤ εPA) (hεbar : 0 ≤ εbar)
    (C : MeasureThenHash M l')
    (hl' : (l' : ℝ) ≤
      (M.toProtocol.l : ℝ) - 2 * Real.logb 2 (deFinettiPrefactor (dA ^ 2 * dB ^ 2) n))
    (hperm :
      haveI := M.toProtocol.keyDim_neZero
      haveI := M.toProtocol.annDim_neZero
      IsPermutationInvariantMap (M.toProtocol.roundDifferenceMap l'))
    (hClosed : IsClosed goodSet) :
    M.toProtocol.IsSecretAt l' σA
      ((deFinettiPrefactor (dA ^ 2 * dB ^ 2) n : ℝ) * coherentIIDSecrecy εAT εPA εbar) := by
  apply permInvariant_postselection_security_of_referenceBound M.toProtocol σA hσA
    (coherentIIDSecrecy εAT εPA εbar) l' _ hperm
  exact postselection_referenceBound_of_measureThenHash M σA εAT εPA εbar l'
    goodSet hcondS hcondLHL hεPA hεbar C hl' hClosed

end InfoTheory.Postselection
