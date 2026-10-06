import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.DirectSumEmbed
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.FubiniStudyTriangle
import QCryptLean.Quantum.Metrics.FidelityOrder
import QCryptLean.Quantum.Metrics.TraceNorm.SubNormalized
import QCryptLean.Quantum.Metrics.FidelityPurificationMax
import QCryptLean.Quantum.Metrics.PurificationUnitaryAction
import QCryptLean.Quantum.Metrics.TraceNorm.FidelitySymm
import QCryptLean.Quantum.Metrics.UhlmannWitness
import QCryptLean.Quantum.Metrics.FuchsVanDeGraafPure
import QCryptLean.Quantum.Metrics.PartialTraceContractive
import QCryptLean.InfoTheory.DistanceBounds.FuchsVanDeGraaf.Lower
import QCryptLean.Math.Analysis.Trig

/-!
# Purified Distance for Sub-Normalized Operators

The purified distance P(ρ, σ) = √(1 - F*(ρ,σ)²) between sub-normalized operators,
following Tomamichel 2016, §3.4.

## Main definitions
- `purifiedDistance`: P(ρ, σ) = √(1 - F*(ρ,σ)²) (Tomamichel §3.4)

## Main statements
- `purifiedDistance_nonneg`: P(ρ,σ) ≥ 0
- `purifiedDistance_symm`: P(ρ,σ) = P(σ,ρ)
- `purifiedDistance_self_zero`: P(ρ,ρ) = 0
- `purifiedDistance_le_one`: P(ρ,σ) ≤ 1
- `purifiedDistance_triangle`: triangle inequality P(ρ,τ) ≤ P(ρ,σ) + P(σ,τ),
  proved via the Bures-angle factorization.
- `SubDensityOp.trace_ge_of_purifiedDistance_of_normalized`: if `ρ.trace = 1`
  and `P(ρ, τ) ≤ ε`, then `1 - ε² ≤ τ.trace`.
- `purifiedDistance_eq_zero_iff`: P(ρ,σ) = 0 ↔ ρ = σ
- `traceDistanceGen_le_purifiedDistance`: D(ρ,σ) ≤ P(ρ,σ)
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Quantum.Metrics.KitaevWatrousPurification
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-!
## Purified Distance

Tomamichel 2016, §3.4:
  P(ρ, σ) := √(1 - F*(ρ,σ)²)

where F*(ρ,σ) is the generalized fidelity from §3.3.1.
-/

/-- Purified distance between two sub-normalized operators.

    Tomamichel 2016, §3.4:
      P(ρ, σ) := √(1 - F*(ρ,σ)²)

    This is well-defined because F*(ρ,σ) ∈ [0,1] (so 1 - F*(ρ,σ)² ≥ 0). -/
noncomputable def purifiedDistance {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) : ℝ :=
  Real.sqrt (1 - fidelityGen ρ σ ^ 2)

/-- The purified distance to zero is the square root of the state's trace. -/
@[simp] theorem purifiedDistance_zero_right {n : ℕ} [NeZero n] (ρ : SubDensityOp n) :
    purifiedDistance ρ 0 = Real.sqrt ρ.trace := by
  have hfid : Quantum.Metrics.fidelity ρ.toPosSemidefOp
      (0 : SubDensityOp n).toPosSemidefOp = 0 := by
    unfold Quantum.Metrics.fidelity Quantum.Metrics.sqrtPosSemidefOp
    simp [show (0 : SubDensityOp n).toPosSemidefOp.toOp = 0 from rfl]
  have htrace : (0 : SubDensityOp n).trace = 0 := by
    change (0 : Op n).trace.re = 0
    simp
  rw [purifiedDistance, fidelityGen, hfid, htrace, zero_add, sub_zero, mul_one,
    Real.sq_sqrt ρ.one_sub_trace_nonneg]
  congr 1
  ring

/-- Purified distance is nonneg. -/
theorem purifiedDistance_nonneg {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    0 ≤ purifiedDistance ρ σ :=
  Real.sqrt_nonneg _

/-- Squared purified distance: `P(ρ, σ)² = 1 - F*(ρ, σ)²`. -/
lemma purifiedDistance_sq {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    purifiedDistance ρ σ ^ 2 = 1 - fidelityGen ρ σ ^ 2 := by
  unfold purifiedDistance
  exact Real.sq_sqrt (by linarith [fidelityGen_sq_le_one ρ σ])

/-- For a normalized `ρ` (`ρ.trace = 1`), the generalized fidelity equals the
    Uhlmann fidelity: the sub-normalization correction `√((1-ρ.trace)(1-τ.trace))`
    vanishes. -/
lemma fidelityGen_eq_fidelity_of_trace_one {n : ℕ} [NeZero n]
    (ρ τ : SubDensityOp n) (hρ : ρ.trace = 1) :
    fidelityGen ρ τ = Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp := by
  unfold fidelityGen
  have hcorr : Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) = 0 := by rw [hρ]; simp
  rw [hcorr, add_zero]

/-- Purified distance is symmetric. -/
theorem purifiedDistance_symm {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    purifiedDistance ρ σ = purifiedDistance σ ρ := by
  unfold purifiedDistance
  rw [fidelityGen_symm]

/-- Purified distance vanishes on the diagonal: `P(ρ, ρ) = 0`. -/
theorem purifiedDistance_self_zero {n : ℕ} [NeZero n] (ρ : SubDensityOp n) :
    purifiedDistance ρ ρ = 0 := by
  unfold purifiedDistance fidelityGen
  rw [Quantum.Metrics.fidelity_self_posSemidefOp ρ.toPosSemidefOp]
  set t := ρ.trace
  have h_trace_eq : ((ρ.toPosSemidefOp.toOp).trace).re = t := rfl
  rw [h_trace_eq, Real.sqrt_mul_self ρ.one_sub_trace_nonneg]
  have h_sum : t + (1 - t) = 1 := by ring
  rw [h_sum]
  simp only [one_pow, sub_self, Real.sqrt_zero]

/-- Purified distance is at most 1. -/
theorem purifiedDistance_le_one {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    purifiedDistance ρ σ ≤ 1 := by
  calc purifiedDistance ρ σ
      = Real.sqrt (1 - fidelityGen ρ σ ^ 2) := rfl
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (fidelityGen ρ σ)])
    _ = 1 := Real.sqrt_one

/-- Purified distance is antitone in generalized fidelity. -/
lemma purifiedDistance_le_of_fidelityGen_ge
    {n m : ℕ} [NeZero n] [NeZero m]
    (ρ σ : SubDensityOp n) (τ υ : SubDensityOp m)
    (hfg : fidelityGen τ υ ≤ fidelityGen ρ σ) :
    purifiedDistance ρ σ ≤ purifiedDistance τ υ := by
  unfold purifiedDistance
  apply Real.sqrt_le_sqrt
  have hρσ_nonneg : 0 ≤ fidelityGen ρ σ := fidelityGen_nonneg ρ σ
  have hτυ_nonneg : 0 ≤ fidelityGen τ υ := fidelityGen_nonneg τ υ
  have hsq : fidelityGen τ υ ^ 2 ≤ fidelityGen ρ σ ^ 2 :=
    sq_le_sq' (by nlinarith) hfg
  nlinarith

/-- Norm symmetry of the bra-ket inner product. -/
lemma ket_inner_norm_comm {n : ℕ} (ψ φ : Ket n) :
    ‖(ψ.dag * φ : ℂ)‖ = ‖(φ.dag * ψ : ℂ)‖ := by
  change ‖Ket.inner ψ φ‖ = ‖Ket.inner φ ψ‖
  rw [Ket.inner_conj ψ φ, norm_star]

/-!
### Bures-angle factorization of the triangle inequality

We reduce `purifiedDistance_triangle` to a pure real-analysis fact about `sin`
applied to three angles `α, β, γ ∈ [0, π/2]` with `γ ≤ α + β`, combined with
the **Bures angle triangle inequality**
  `arccos (F*(ρ, τ)) ≤ arccos (F*(ρ, σ)) + arccos (F*(σ, τ))`
stated as `fidelityAngle_triangle`.

`fidelityAngle_triangle` is proved via the density-operator version
`fidelityAngle_triangle_densityOp` and the block-diagonal extension identity
`toDensityOpExtend_fidelity`.
-/

/-- **Bures angle triangle inequality for density operators** (Tomamichel 2016,
    Lemma 3.5, eq. 3.27, normalized version).

    The proof uses canonical purifications, Uhlmann witnesses, and the
    pure-state Fubini-Study triangle inequality. -/
theorem fidelityAngle_triangle_densityOp
    {d : ℕ} [NeZero d] (ρ σ τ : DensityOp d) :
    Real.arccos (Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp) ≤
      Real.arccos (Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp) +
        Real.arccos (Quantum.Metrics.fidelity σ.toPosSemidefOp τ.toPosSemidefOp) := by
  -- Canonical same-ancilla purifications of ρ, σ, τ.
  set ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
    (sameAncillaPurificationDensity_isPure ρ)
    with hψρ_def
  set ψσ := (sameAncillaPurificationDensity σ).pureKetOf
    (sameAncillaPurificationDensity_isPure σ)
    with hψσ_def
  set ψτ := (sameAncillaPurificationDensity τ).pureKetOf
    (sameAncillaPurificationDensity_isPure τ)
    with hψτ_def
  have hψρ_norm : ψρ.dag * ψρ = 1 :=
    (sameAncillaPurificationDensity ρ).pureKetOf_normalized
      (sameAncillaPurificationDensity_isPure ρ)
  have hψσ_norm : ψσ.dag * ψσ = 1 :=
    (sameAncillaPurificationDensity σ).pureKetOf_normalized
      (sameAncillaPurificationDensity_isPure σ)
  have hψτ_norm : ψτ.dag * ψτ = 1 :=
    (sameAncillaPurificationDensity τ).pureKetOf_normalized
      (sameAncillaPurificationDensity_isPure τ)
  -- Achievability witnesses on the pairs (ρ, σ) and (τ, σ).
  obtain ⟨U₁, hU₁⟩ :=
    sameAncillaPurificationDensity_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich
      ρ σ
  obtain ⟨U₂, hU₂⟩ :=
    sameAncillaPurificationDensity_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich
      τ σ
  -- The achievability RHS is exactly `fidelity` on the corresponding PSD pair.
  have hfidρσ :
      Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp =
        (ψσ.dag * (Op.tensor U₁.toOp (1 : Op d)) * ψρ).re := by
    -- `fidelity` reduces definitionally to the trace-of-cfcSqrt expression.
    show _ = _
    change (Matrix.trace (CFC.sqrt (CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp))).re = _
    exact hU₁.symm
  have hfidτσ :
      Quantum.Metrics.fidelity τ.toPosSemidefOp σ.toPosSemidefOp =
        (ψσ.dag * (Op.tensor U₂.toOp (1 : Op d)) * ψτ).re := by
    show _ = _
    change (Matrix.trace (CFC.sqrt (CFC.sqrt τ.toOp * σ.toOp * CFC.sqrt τ.toOp))).re = _
    exact hU₂.symm
  have hfidστ :
      Quantum.Metrics.fidelity σ.toPosSemidefOp τ.toPosSemidefOp =
        (ψσ.dag * (Op.tensor U₂.toOp (1 : Op d)) * ψτ).re := by
    rw [Quantum.Metrics.fidelity_comm]; exact hfidτσ
  -- Three normalized kets for Fubini–Study.
  set χρ : Ket (d * d) := (Op.tensor U₁.toOp (1 : Op d)) * ψρ with hχρ_def
  set χτ : Ket (d * d) := (Op.tensor U₂.toOp (1 : Op d)) * ψτ with hχτ_def
  have hχρ_norm : χρ.dag * χρ = 1 :=
    Quantum.Metrics.KitaevWatrousPurification.tensorUnitary_ket_normalized
      U₁ ψρ hψρ_norm
  have hχτ_norm : χτ.dag * χτ = 1 :=
    Quantum.Metrics.KitaevWatrousPurification.tensorUnitary_ket_normalized
      U₂ ψτ hψτ_norm
  -- Overlap identities using `operator_action_in_bra_ket`.
  have hoverlap_ρσ :
      (ψσ.dag * (Op.tensor U₁.toOp (1 : Op d)) * ψρ : ℂ) = (ψσ.dag * χρ : ℂ) :=
    operator_action_in_bra_ket (Op.tensor U₁.toOp (1 : Op d)) ψσ ψρ χρ rfl
  have hoverlap_τσ :
      (ψσ.dag * (Op.tensor U₂.toOp (1 : Op d)) * ψτ : ℂ) = (ψσ.dag * χτ : ℂ) :=
    operator_action_in_bra_ket (Op.tensor U₂.toOp (1 : Op d)) ψσ ψτ χτ rfl
  have hnorm_flip :
      ‖(ψσ.dag * χρ : ℂ)‖ = ‖(χρ.dag * ψσ : ℂ)‖ :=
    ket_inner_norm_comm ψσ χρ
  -- Per-pair bounds.
  -- (i) F(ρ, σ) ≤ ‖χρ.dag * ψσ‖.
  have hF_ρσ_le :
      Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp ≤
        ‖(χρ.dag * ψσ : ℂ)‖ := by
    rw [hfidρσ, hoverlap_ρσ, ← hnorm_flip]
    exact Complex.re_le_norm _
  -- (ii) F(σ, τ) ≤ ‖ψσ.dag * χτ‖.
  have hF_στ_le :
      Quantum.Metrics.fidelity σ.toPosSemidefOp τ.toPosSemidefOp ≤
        ‖(ψσ.dag * χτ : ℂ)‖ := by
    rw [hfidστ, ← hoverlap_τσ]
    exact Complex.re_le_norm _
  -- (iii) ‖χρ.dag * χτ‖ ≤ F(ρ, τ), by the canonical Uhlmann upper bound.
  -- Expand the LHS using the tensor-unitary overlap identity.
  have hexpand :
      (χρ.dag * χτ : ℂ) =
        (ψρ.dag *
          (Op.tensor (U₁.toOp.conjTranspose * U₂.toOp) (1 : Op d)) * ψτ : ℂ) :=
    Quantum.Metrics.KitaevWatrousPurification.tensor_unitary_overlap_expand
      U₁ U₂ ψρ ψτ
  -- Product of unitaries: V := U₁† * U₂ : UnitaryOp d.
  let V : UnitaryOp d := U₁† * U₂
  have hV_toOp : V.toOp = U₁.toOp.conjTranspose * U₂.toOp := rfl
  have hUmax :
      ‖(ψρ.dag * (Op.tensor V.toOp (1 : Op d)) * ψτ : ℂ)‖ ≤
        Quantum.Metrics.fidelity τ.toPosSemidefOp ρ.toPosSemidefOp :=
    Quantum.Metrics.fidelity_ge_canonical_overlap_norm τ ρ V
  have hF_ρτ_bound :
      ‖(χρ.dag * χτ : ℂ)‖ ≤
        Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp := by
    rw [hexpand, ← hV_toOp, Quantum.Metrics.fidelity_comm]
    exact hUmax
  -- Pure-state Fubini–Study triangle inequality on (χρ, ψσ, χτ).
  have hFS :=
    fubiniStudy_triangle_pure χρ ψσ χτ hχρ_norm hψσ_norm hχτ_norm
  -- Antitonicity of arccos on each leg transfers the pure-state triangle.
  have hleg_top :
      Real.arccos (Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp) ≤
        Real.arccos ‖(χρ.dag * χτ : ℂ)‖ :=
    Real.arccos_le_arccos hF_ρτ_bound
  have hleg_left :
      Real.arccos ‖(χρ.dag * ψσ : ℂ)‖ ≤
        Real.arccos (Quantum.Metrics.fidelity ρ.toPosSemidefOp σ.toPosSemidefOp) :=
    Real.arccos_le_arccos hF_ρσ_le
  have hleg_right :
      Real.arccos ‖(ψσ.dag * χτ : ℂ)‖ ≤
        Real.arccos (Quantum.Metrics.fidelity σ.toPosSemidefOp τ.toPosSemidefOp) :=
    Real.arccos_le_arccos hF_στ_le
  linarith [hFS, hleg_top, hleg_left, hleg_right]

/-- **Bures angle triangle inequality** (Tomamichel 2016, Lemma 3.5, eq. 3.27)
    for sub-normalized operators.

    The proof reduces to the density-operator version
    `fidelityAngle_triangle_densityOp` via the block-diagonal extension
    identity `toDensityOpExtend_fidelity`, which rewrites each
    `fidelityGen` on the sub-normalized originals as a standard Uhlmann
    fidelity on the extended density operators `ρ̃, σ̃, τ̃ : DensityOp (n+1)`. -/
theorem fidelityAngle_triangle {n : ℕ} [NeZero n] (ρ σ τ : SubDensityOp n) :
    Real.arccos (fidelityGen ρ τ) ≤
      Real.arccos (fidelityGen ρ σ) + Real.arccos (fidelityGen σ τ) := by
  rw [← toDensityOpExtend_fidelity ρ σ,
      ← toDensityOpExtend_fidelity σ τ,
      ← toDensityOpExtend_fidelity ρ τ]
  exact fidelityAngle_triangle_densityOp
    ρ.toDensityOpExtend σ.toDensityOpExtend τ.toDensityOpExtend

/-- Purified distance rewritten as `sin` of the Bures angle. -/
lemma purifiedDistance_eq_sin_arccos {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    purifiedDistance ρ σ = Real.sin (Real.arccos (fidelityGen ρ σ)) := by
  rw [Real.sin_arccos]
  rfl

/-- Triangle inequality for purified distance.

    P(ρ, τ) ≤ P(ρ, σ) + P(σ, τ) for all sub-normalized ρ, σ, τ.

    Proved via the Bures-angle factorization: each `purifiedDistance` equals
    `sin` of `arccos ∘ fidelityGen`, and the triangle inequality reduces to
    (a) the Bures angle triangle inequality `fidelityAngle_triangle`, combined
    with (b) the elementary real-analysis fact `Real.sin_le_sin_add_sin_of_le_add`. -/
theorem purifiedDistance_triangle {n : ℕ} [NeZero n] (ρ σ τ : SubDensityOp n) :
    purifiedDistance ρ τ ≤ purifiedDistance ρ σ + purifiedDistance σ τ := by
  set α := Real.arccos (fidelityGen ρ σ)
  set β := Real.arccos (fidelityGen σ τ)
  set γ := Real.arccos (fidelityGen ρ τ)
  have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 (fidelityGen_nonneg ρ σ)⟩
  have hβ_mem : β ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 (fidelityGen_nonneg σ τ)⟩
  have hγ_mem : γ ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 (fidelityGen_nonneg ρ τ)⟩
  have hangle : γ ≤ α + β := fidelityAngle_triangle ρ σ τ
  have hsin := Real.sin_le_sin_add_sin_of_le_add hα_mem hβ_mem hγ_mem hangle
  rw [purifiedDistance_eq_sin_arccos ρ τ,
      purifiedDistance_eq_sin_arccos ρ σ,
      purifiedDistance_eq_sin_arccos σ τ]
  exact hsin

/-!
## Purified Distance and Generalized Trace Distance

The purified distance bounds and is related to the generalized trace distance
via Tomamichel eq. 3.29 / Lemma 3.3.
-/

/-- A ket equal to the canonical same-ancilla purification reduces to the
original density operator after tracing out the ancilla. -/
lemma partialTraceB_fromPure_eq_sameAncillaPurificationKet
    {m : ℕ} [NeZero m] [NeZero (m * m)] (ρ' : DensityOp m)
    (ψ : Ket (m * m)) (hψ_norm : ψ.dag * ψ = 1)
    (hψ : ψ = sameAncillaPurificationKet ρ') :
    partialTraceB (DensityOp.fromPure ψ hψ_norm).toOp = ρ'.toOp := by
  rw [show (DensityOp.fromPure ψ hψ_norm).toOp = ψ * ψ.dag from rfl]
  rw [hψ, ← sameAncillaPurification_eq_ketbra_sameAncillaPurificationKet]
  have hρ'_psd : ρ'.toOp.PosSemidef :=
    Quantum.Operators.posSemidefOp_implies_mathlib ρ'.toPosSemidefOp
  exact partialTraceB_sameAncillaPurification ρ'.toOp hρ'_psd

/-- A ket equal to the Uhlmann witness purification `ketB` reduces to its
density operator after tracing out the ancilla. -/
lemma partialTraceB_fromPure_eq_ketB
    {m : ℕ} [NeZero m] [NeZero (m * m)] (σ' : DensityOp m) (U : UnitaryOp m)
    (ψ : Ket (m * m)) (hψ_norm : ψ.dag * ψ = 1)
    (hψ : ψ = Quantum.Metrics.UhlmannWitness.ketB σ' U) :
    partialTraceB (DensityOp.fromPure ψ hψ_norm).toOp = σ'.toOp := by
  rw [show (DensityOp.fromPure ψ hψ_norm).toOp = ψ * ψ.dag from rfl]
  rw [hψ]
  exact Quantum.Metrics.UhlmannWitness.ketB_partialTraceB σ' U

/-- **Mixed-state Fuchs–van de Graaf inequality** (Tomamichel 2016 eq. 3.29 /
    Nielsen–Chuang Thm 9.3.1): for normalized density operators `ρ', σ'`,

        D(ρ', σ') ≤ √(1 - F(ρ', σ')²).

    Proof: reduces to the pure-state FvdG inequality via Uhlmann achievability
    and the data-processing inequality for partial trace. -/
lemma traceDistance_le_sqrt_one_sub_fidelitySq_normalized
    {m : ℕ} [NeZero m] (ρ' σ' : DensityOp m) :
    Quantum.Metrics.traceDistance ρ'.toOp σ'.toOp
      ≤ Real.sqrt
          (1 - Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp ^ 2) := by
  let : NeZero (m * m) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne m)⟩
  -- Uhlmann achievability on the canonical purification kets of ρ' and σ'.
  obtain ⟨U, hU⟩ :=
    sameAncillaPurificationKet_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich
      ρ' σ'
  -- Canonical purification of ρ' and Uhlmann witness purification of σ'.
  set ψρ' := Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet ρ'
    with hψρ'_def
  set ψB := Quantum.Metrics.UhlmannWitness.ketB σ' U with hψB_def
  have hψρ'_norm : ψρ'.dag * ψρ' = 1 :=
    Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet_normalized ρ'
  have hψB_norm : ψB.dag * ψB = 1 :=
    Quantum.Metrics.UhlmannWitness.ketB_normalized σ' U
  set ρAB := DensityOp.fromPure ψρ' hψρ'_norm with hρAB_def
  set σAB := DensityOp.fromPure ψB hψB_norm with hσAB_def
  have hρAB_partial : partialTraceB ρAB.toOp = ρ'.toOp := by
    rw [hρAB_def]
    exact partialTraceB_fromPure_eq_sameAncillaPurificationKet
      ρ' ψρ' hψρ'_norm hψρ'_def
  have hσAB_partial : partialTraceB σAB.toOp = σ'.toOp := by
    rw [hσAB_def]
    exact partialTraceB_fromPure_eq_ketB σ' U ψB hψB_norm hψB_def
  -- Pure-state FvdG on the pair (ψρ', ψB).
  have hFvdG :
      Quantum.Metrics.traceDistance ρAB.toOp σAB.toOp ≤
        Real.sqrt (1 - Quantum.Metrics.fidelity
          ρAB.toPosSemidefOp σAB.toPosSemidefOp ^ 2) :=
    Quantum.Metrics.traceDistance_pure_le_sqrt_one_sub_fidelitySq
      ψρ' ψB hψρ'_norm hψB_norm
  -- DPI: `traceDistance ρ'.toOp σ'.toOp ≤ traceDistance ρAB.toOp σAB.toOp`.
  have hDPI :
      Quantum.Metrics.traceDistance ρ'.toOp σ'.toOp ≤
        Quantum.Metrics.traceDistance ρAB.toOp σAB.toOp := by
    have h :=
      Quantum.Metrics.traceDistance_contractive_under_partialTraceB
        ρAB.toOp σAB.toOp
    rw [hρAB_partial, hσAB_partial] at h
    exact h
  set z : ℂ := ψρ'.dag * ψB with hz_def
  -- Real part of `z` equals Uhlmann fidelity F(ρ', σ').
  have hz_re :
      z.re = Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp :=
    Quantum.Metrics.UhlmannWitness.ketB_re_overlap_of_witness ρ' σ' U hU
  -- Pure-state fidelity equals `‖z‖`.
  have hPureFid :
      Quantum.Metrics.fidelity ρAB.toPosSemidefOp σAB.toPosSemidefOp = ‖z‖ :=
    InfoTheory.SmoothMinEntropy.fidelity_pure_eq_abs_inner
      ψρ' ψB hψρ'_norm hψB_norm
  -- Bound: F(ρ', σ') ≤ ‖z‖.
  have hF_le_norm :
      Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp ≤ ‖z‖ := by
    rw [← hz_re]
    exact Complex.re_le_norm _
  -- Nonnegativity of F.
  have hF_nn :
      0 ≤ Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp :=
    Quantum.Metrics.fidelity_nonneg_posSemidefOp _ _
  -- Upper bound on F² by ‖z‖².
  have hF_sq_le :
      Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp ^ 2 ≤ ‖z‖ ^ 2 := by
    have := mul_self_le_mul_self hF_nn hF_le_norm
    simpa [pow_two] using this
  -- Pure-fidelity squared equals ‖z‖².
  have hPureFid_sq :
      Quantum.Metrics.fidelity ρAB.toPosSemidefOp σAB.toPosSemidefOp ^ 2 = ‖z‖ ^ 2 := by
    rw [hPureFid]
  -- √(1 - ‖z‖²) ≤ √(1 - F²).
  have h_sqrt_mono :
      Real.sqrt
        (1 - Quantum.Metrics.fidelity ρAB.toPosSemidefOp σAB.toPosSemidefOp ^ 2) ≤
      Real.sqrt
        (1 - Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp ^ 2) := by
    apply Real.sqrt_le_sqrt
    rw [hPureFid_sq]
    linarith
  -- Chain everything together.
  calc Quantum.Metrics.traceDistance ρ'.toOp σ'.toOp
      ≤ Quantum.Metrics.traceDistance ρAB.toOp σAB.toOp := hDPI
    _ ≤ Real.sqrt (1 - Quantum.Metrics.fidelity
          ρAB.toPosSemidefOp σAB.toPosSemidefOp ^ 2) := hFvdG
    _ ≤ Real.sqrt (1 - Quantum.Metrics.fidelity
          ρ'.toPosSemidefOp σ'.toPosSemidefOp ^ 2) := h_sqrt_mono

/-- Purified distance and generalized trace distance are related:
    D(ρ,σ) ≤ P(ρ,σ) (Tomamichel §3.4, Lemma 3.3 direction 1).

    Proof by block-diagonal reduction (Tomamichel 2016, Lemma 3.17):
    embed `ρ, σ` into normalized density operators `ρ̃, σ̃ : DensityOp (n+1)`
    via `SubDensityOp.toDensityOpExtend`.  Then

      D_gen(ρ, σ)  = D(ρ̃, σ̃)                    -- `toDensityOpExtend_traceDistance`
                   ≤ √(1 - F(ρ̃, σ̃)²)             -- mixed-state FvdG (helper)
                   = √(1 - F*(ρ, σ)²)             -- `toDensityOpExtend_fidelity`
                   = P(ρ, σ)                      -- definition of `purifiedDistance`. -/
theorem traceDistanceGen_le_purifiedDistance {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    Quantum.Metrics.traceDistanceGen ρ.toOp σ.toOp ≤ purifiedDistance ρ σ := by
  -- Block-diagonal extensions to normalized density operators on `Fin (n+1)`.
  set ρ' : DensityOp (n+1) := ρ.toDensityOpExtend with hρ'
  set σ' : DensityOp (n+1) := σ.toDensityOpExtend with hσ'
  -- Step 1: D_gen(ρ, σ) = D(ρ̃, σ̃).
  have h_D_eq : Quantum.Metrics.traceDistanceGen ρ.toOp σ.toOp
      = Quantum.Metrics.traceDistance ρ'.toOp σ'.toOp :=
    (toDensityOpExtend_traceDistance ρ σ).symm
  -- Step 2: F(ρ̃, σ̃) = fidelityGen ρ σ.
  have h_F_eq : Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp
      = fidelityGen ρ σ :=
    toDensityOpExtend_fidelity ρ σ
  -- Step 3: mixed-state Fuchs–van de Graaf applied to the extensions.
  have h_FvdG :
      Quantum.Metrics.traceDistance ρ'.toOp σ'.toOp
        ≤ Real.sqrt
            (1 - Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp ^ 2) :=
    traceDistance_le_sqrt_one_sub_fidelitySq_normalized ρ' σ'
  -- Chain the pieces; `purifiedDistance` unfolds to the final `√(1 - F*²)`.
  calc Quantum.Metrics.traceDistanceGen ρ.toOp σ.toOp
      = Quantum.Metrics.traceDistance ρ'.toOp σ'.toOp := h_D_eq
    _ ≤ Real.sqrt
          (1 - Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp ^ 2) :=
        h_FvdG
    _ = Real.sqrt (1 - fidelityGen ρ σ ^ 2) := by rw [h_F_eq]
    _ = purifiedDistance ρ σ := rfl

/-- The difference of two sub-normalized operators is Hermitian. -/
lemma subDensityOp_sub_isHermitian {n : ℕ} (ρ σ : SubDensityOp n) :
    (ρ.toOp - σ.toOp).IsHermitian :=
  ρ.isHermitian.sub σ.isHermitian

/-- Trace lower bound from purified distance, for normalized ρ.

    If `ρ.trace = 1` and `P(ρ, τ) ≤ ε` with `0 ≤ ε`, then
    `1 - ε² ≤ τ.trace`.

    Proof outline: From `P ≤ ε` (both in `[0,1]`), squaring and using
    `P² = 1 - F*²` gives `1 - ε² ≤ F*²`. Since `ρ.trace = 1`, the
    sub-normalization correction `√((1 - ρ.trace)(1 - τ.trace))` vanishes,
    so `F* = F` (the standard Uhlmann fidelity on `toPosSemidefOp`).
    By Cauchy–Schwarz (`fidelity_sq_le_trace_mul_trace`), `F² ≤ ρ.trace · τ.trace
    = τ.trace`. Chaining gives the claim. -/
theorem SubDensityOp.trace_ge_of_purifiedDistance_of_normalized {n : ℕ} [NeZero n]
    (ρ τ : SubDensityOp n) (hρ : ρ.trace = 1) {ε : ℝ} (_hε : 0 ≤ ε)
    (hP : purifiedDistance ρ τ ≤ ε) :
    1 - ε ^ 2 ≤ τ.trace := by
  -- Step 1: square the distance bound.
  have hP_nn : 0 ≤ purifiedDistance ρ τ := purifiedDistance_nonneg ρ τ
  have hP_sq_le : purifiedDistance ρ τ ^ 2 ≤ ε ^ 2 := by
    have := mul_self_le_mul_self hP_nn hP
    simpa [pow_two] using this
  -- Step 2: unpack purifiedDistance² = 1 - F*².
  have hP_sq_eq : purifiedDistance ρ τ ^ 2 = 1 - fidelityGen ρ τ ^ 2 :=
    purifiedDistance_sq ρ τ
  have h1_sub_le : 1 - ε ^ 2 ≤ fidelityGen ρ τ ^ 2 := by
    have := hP_sq_le
    rw [hP_sq_eq] at this
    linarith
  -- Step 3: fidelityGen = Uhlmann fidelity because ρ.trace = 1.
  have hFgen_eq :
      fidelityGen ρ τ =
        Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp :=
    fidelityGen_eq_fidelity_of_trace_one ρ τ hρ
  -- Step 4: Cauchy–Schwarz F² ≤ ρ.trace · τ.trace = τ.trace.
  have hF_sq_le : Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp ^ 2
      ≤ ρ.trace * τ.trace := fidelity_sq_le_trace_mul_trace ρ τ
  have hF_sq_le' : fidelityGen ρ τ ^ 2 ≤ τ.trace := by
    rw [hFgen_eq]
    calc Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp ^ 2
        ≤ ρ.trace * τ.trace := hF_sq_le
      _ = τ.trace := by rw [hρ, one_mul]
  linarith

/-- If one sub-density operator is dominated by another, then its trace is at
most the fidelity with the dominating operator. -/
theorem SubDensityOp.trace_le_fidelity_of_opLe
    {n : ℕ} [NeZero n] (ρ τ : SubDensityOp n)
    (hτ_le_ρ : opLe τ.toOp ρ.toOp) :
    τ.trace ≤ Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp := by
  have hFτρ :
      τ.trace ≤ Quantum.Metrics.fidelity τ.toPosSemidefOp ρ.toPosSemidefOp := by
    have hdom :
        opLe τ.toPosSemidefOp.toOp (((1 : ℝ) : ℂ) • ρ.toPosSemidefOp.toOp) := by
      simpa using hτ_le_ρ
    have h :=
      Quantum.Metrics.trace_div_sqrt_le_fidelity_of_opLe
        τ.toPosSemidefOp ρ.toPosSemidefOp (c := 1) (by norm_num) hdom
    simpa [SubDensityOp.trace] using h
  rw [Quantum.Metrics.fidelity_comm ρ.toPosSemidefOp τ.toPosSemidefOp]
  exact hFτρ

/-- Trace monotonicity for sub-density operators under the PSD order. -/
lemma SubDensityOp.trace_le_of_opLe
    {n : ℕ} (ρ τ : SubDensityOp n) (hτ_le_ρ : opLe τ.toOp ρ.toOp) :
    τ.trace ≤ ρ.trace := by
  have htrace :=
    Quantum.Operators.trace_mul_le_of_opLe
      (M := (1 : Op n)) Matrix.PosSemidef.one
      τ.isHermitian ρ.isHermitian hτ_le_ρ
  simpa [SubDensityOp.trace] using htrace

/-- The scalar inequality `1 - x² ≤ 2(1 - x)`, equivalently
`0 ≤ (1 - x)²`. -/
lemma one_sub_sq_le_two_mul_one_sub (x : ℝ) :
    1 - x ^ 2 ≤ 2 * (1 - x) := by
  nlinarith [sq_nonneg (1 - x)]

/-- If `τ ≤ ρ`, generalized fidelity is at least the complement of the trace gap. -/
lemma fidelityGen_ge_one_sub_trace_gap_of_opLe
    {n : ℕ} [NeZero n] (ρ τ : SubDensityOp n)
    (hτ_le_ρ : opLe τ.toOp ρ.toOp) :
    1 - (ρ.trace - τ.trace) ≤ fidelityGen ρ τ := by
  have htrace_le : τ.trace ≤ ρ.trace :=
    SubDensityOp.trace_le_of_opLe ρ τ hτ_le_ρ
  have hF_ge :
      τ.trace ≤ Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp :=
    SubDensityOp.trace_le_fidelity_of_opLe ρ τ hτ_le_ρ
  have hcorr_ge :
      1 - ρ.trace ≤ Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) := by
    have hρ_gap_nonneg : 0 ≤ 1 - ρ.trace := ρ.one_sub_trace_nonneg
    have hsq_le : (1 - ρ.trace) ^ 2 ≤ (1 - ρ.trace) * (1 - τ.trace) := by
      nlinarith
    calc
      1 - ρ.trace = Real.sqrt ((1 - ρ.trace) ^ 2) := by
        rw [Real.sqrt_sq hρ_gap_nonneg]
      _ ≤ Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) :=
        Real.sqrt_le_sqrt hsq_le
  unfold fidelityGen
  linarith

/-- **General purified-distance / trace-gap bound** (no operator domination).

From a fidelity lower bound `1 - (ρ.trace - τ.trace) ≤ fidelityGen ρ τ` and the
trace ordering `τ.trace ≤ ρ.trace`, the purified distance is bounded by the
square root of twice the trace gap.  This is the arithmetic core shared by the
`opLe` route and the weight-cap route (where `τ ⋠ ρ` fails but the fidelity
bound still holds). -/
theorem SubDensityOp.purifiedDistance_le_sqrt_two_mul_trace_gap_of_fidelityGen_ge
    {n : ℕ} [NeZero n] (ρ τ : SubDensityOp n)
    (htrace_le : τ.trace ≤ ρ.trace)
    (hfg_ge : 1 - (ρ.trace - τ.trace) ≤ fidelityGen ρ τ) :
    purifiedDistance ρ τ ≤ Real.sqrt (2 * (ρ.trace - τ.trace)) := by
  have hgap_nonneg : 0 ≤ ρ.trace - τ.trace := sub_nonneg.mpr htrace_le
  have hgap_le_one : ρ.trace - τ.trace ≤ 1 := by
    have hρ_le_one : ρ.trace ≤ 1 := ρ.trace_le_one
    have hτ_nonneg : 0 ≤ τ.trace := τ.trace_nonneg
    linarith
  have hbase_nonneg : 0 ≤ 1 - (ρ.trace - τ.trace) := by
    nlinarith
  have hsq_le :
      (1 - (ρ.trace - τ.trace)) ^ 2 ≤ fidelityGen ρ τ ^ 2 := by
    have hsq := mul_self_le_mul_self hbase_nonneg hfg_ge
    simpa [pow_two] using hsq
  unfold purifiedDistance
  apply Real.sqrt_le_sqrt
  calc
    1 - fidelityGen ρ τ ^ 2
        ≤ 1 - (1 - (ρ.trace - τ.trace)) ^ 2 := by
          nlinarith
    _ ≤ 2 * (ρ.trace - τ.trace) := by
          nlinarith [sq_nonneg (ρ.trace - τ.trace)]

/-- If `τ ≤ ρ`, then their purified distance is bounded by the square root of
twice the trace gap.  This is the sub-normalized analogue of the normalized
trace-deficit bound. -/
theorem SubDensityOp.purifiedDistance_le_sqrt_two_mul_trace_gap_of_opLe
    {n : ℕ} [NeZero n] (ρ τ : SubDensityOp n)
    (hτ_le_ρ : opLe τ.toOp ρ.toOp) :
    purifiedDistance ρ τ ≤ Real.sqrt (2 * (ρ.trace - τ.trace)) :=
  SubDensityOp.purifiedDistance_le_sqrt_two_mul_trace_gap_of_fidelityGen_ge ρ τ
    (SubDensityOp.trace_le_of_opLe ρ τ hτ_le_ρ)
    (fidelityGen_ge_one_sub_trace_gap_of_opLe ρ τ hτ_le_ρ)

/-- If `τ ≤ ρ` and the trace gap is externally bounded by `ε`, then their
purified distance is bounded by `√(2ε)`. -/
theorem SubDensityOp.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_opLe
    {n : ℕ} [NeZero n] (ρ τ : SubDensityOp n)
    {ε : ℝ} (_hε_nonneg : 0 ≤ ε)
    (hτ_le_ρ : opLe τ.toOp ρ.toOp)
    (htrace_gap : ρ.trace - τ.trace ≤ ε) :
    purifiedDistance ρ τ ≤ Real.sqrt (2 * ε) := by
  calc
    purifiedDistance ρ τ
        ≤ Real.sqrt (2 * (ρ.trace - τ.trace)) :=
          SubDensityOp.purifiedDistance_le_sqrt_two_mul_trace_gap_of_opLe
            ρ τ hτ_le_ρ
    _ ≤ Real.sqrt (2 * ε) := by
      apply Real.sqrt_le_sqrt
      nlinarith

/-- If a normalized sub-density operator `ρ` dominates `τ`, then their purified
distance is controlled by the missing trace mass of `τ`. -/
theorem SubDensityOp.purifiedDistance_le_sqrt_two_mul_one_sub_trace_of_opLe
    {n : ℕ} [NeZero n] (ρ τ : SubDensityOp n) (hρ : ρ.trace = 1)
    (hτ_le_ρ : opLe τ.toOp ρ.toOp) :
    purifiedDistance ρ τ ≤ Real.sqrt (2 * (1 - τ.trace)) := by
  have hFρτ :
      τ.trace ≤ Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp :=
    SubDensityOp.trace_le_fidelity_of_opLe ρ τ hτ_le_ρ
  have hFgen_eq :
      fidelityGen ρ τ =
        Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp :=
    fidelityGen_eq_fidelity_of_trace_one ρ τ hρ
  unfold purifiedDistance
  apply Real.sqrt_le_sqrt
  have hsq : τ.trace ^ 2 ≤ fidelityGen ρ τ ^ 2 := by
    rw [hFgen_eq]
    exact sq_le_sq'
      (by
        have hF_nn :=
          Quantum.Metrics.fidelity_nonneg_posSemidefOp
            ρ.toPosSemidefOp τ.toPosSemidefOp
        nlinarith [τ.trace_nonneg])
      hFρτ
  calc
    1 - fidelityGen ρ τ ^ 2 ≤ 1 - τ.trace ^ 2 := by nlinarith
    _ ≤ 2 * (1 - τ.trace) := one_sub_sq_le_two_mul_one_sub τ.trace

/-- If a normalized sub-density operator `ρ` dominates `τ` and the missing trace
mass of `τ` is at most `ε`, then `τ` is within radius `√(2ε)` of `ρ`. -/
theorem SubDensityOp.purifiedDistance_le_sqrt_two_mul_epsilon_of_opLe
    {n : ℕ} [NeZero n] (ρ τ : SubDensityOp n) (hρ : ρ.trace = 1)
    {ε : ℝ} (_hε_nonneg : 0 ≤ ε) (hτ_le_ρ : opLe τ.toOp ρ.toOp)
    (htrace_deficit : 1 - τ.trace ≤ ε) :
    purifiedDistance ρ τ ≤ Real.sqrt (2 * ε) := by
  calc
    purifiedDistance ρ τ
        ≤ Real.sqrt (2 * (1 - τ.trace)) :=
          SubDensityOp.purifiedDistance_le_sqrt_two_mul_one_sub_trace_of_opLe
            ρ τ hρ hτ_le_ρ
    _ ≤ Real.sqrt (2 * ε) := by
      apply Real.sqrt_le_sqrt
      nlinarith

/-- Purified distance separates points: `P(ρ, σ) = 0` iff `ρ = σ`. -/
theorem purifiedDistance_eq_zero_iff {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    purifiedDistance ρ σ = 0 ↔ ρ = σ := by
  refine ⟨fun hP => ?_, fun h => by rw [h]; exact purifiedDistance_self_zero σ⟩
  -- From `purifiedDistance ρ σ = 0` and the bound `D(ρ,σ) ≤ P(ρ,σ)`, deduce
  -- `traceDistanceGen ρ.toOp σ.toOp = 0`.
  have h_D_le : Quantum.Metrics.traceDistanceGen ρ.toOp σ.toOp ≤ 0 := by
    have := traceDistanceGen_le_purifiedDistance ρ σ
    linarith
  have h_D_nn : 0 ≤ Quantum.Metrics.traceDistanceGen ρ.toOp σ.toOp :=
    Quantum.Metrics.traceDistanceGen_nonneg ρ.toOp σ.toOp
  have h_D_eq : Quantum.Metrics.traceDistanceGen ρ.toOp σ.toOp = 0 :=
    le_antisymm h_D_le h_D_nn
  -- Unfold `traceDistanceGen` as a sum of two nonneg summands.
  unfold Quantum.Metrics.traceDistanceGen at h_D_eq
  have h_tn_nn : 0 ≤ Quantum.Metrics.traceNorm (ρ.toOp - σ.toOp) := by
    unfold Quantum.Metrics.traceNorm
    exact Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have h_s1_nn : 0 ≤ (1 / 2 : ℝ) * Quantum.Metrics.traceNorm (ρ.toOp - σ.toOp) :=
    mul_nonneg (by norm_num) h_tn_nn
  have h_s2_nn : 0 ≤ (1 / 2 : ℝ) * |((ρ.toOp.trace - σ.toOp.trace).re)| :=
    mul_nonneg (by norm_num) (abs_nonneg _)
  have h_s1_zero :
      (1 / 2 : ℝ) * Quantum.Metrics.traceNorm (ρ.toOp - σ.toOp) = 0 :=
    ((add_eq_zero_iff_of_nonneg h_s1_nn h_s2_nn).mp h_D_eq).1
  have h_tn_zero : Quantum.Metrics.traceNorm (ρ.toOp - σ.toOp) = 0 := by
    have : (1 / 2 : ℝ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h_s1_zero).resolve_left this
  -- Convert to Hermitian trace norm and apply faithfulness.
  have hHerm : (ρ.toOp - σ.toOp).IsHermitian := subDensityOp_sub_isHermitian ρ σ
  rw [Quantum.Metrics.traceNorm_hermitian_eq (ρ.toOp - σ.toOp) hHerm] at h_tn_zero
  have h_sub_zero : ρ.toOp - σ.toOp = 0 :=
    (Quantum.Metrics.traceNormHermitian_eq_zero_iff (ρ.toOp - σ.toOp) hHerm).mp h_tn_zero
  have h_toOp_eq : ρ.toOp = σ.toOp := sub_eq_zero.mp h_sub_zero
  exact SubDensityOp.ext h_toOp_eq

/-- **Lower Fuchs–van de Graaf inequality for sub-normalized states:**
`1 − F*(ρ, σ) ≤ Δ(ρ, σ)`, where `F*` is generalized fidelity and `Δ` is generalized
trace distance.

Lifts the normalized lower Fuchs–van de Graaf bound
(`Quantum.Metrics.one_sub_fidelity_le_traceDistance`) to the sub-normalized world along
the block-diagonal extension `ρ ↦ ρ ⊕ (1 − tr ρ)`, using the fidelity and trace-distance
bridges `toDensityOpExtend_fidelity` and `toDensityOpExtend_traceDistance`. -/
theorem one_sub_fidelityGen_le_traceDistanceGen
    {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    1 - fidelityGen ρ σ ≤ Quantum.Metrics.traceDistanceGen ρ.toOp σ.toOp := by
  have hbound :=
    Quantum.Metrics.one_sub_fidelity_le_traceDistance
      ρ.toDensityOpExtend σ.toDensityOpExtend
  rw [Quantum.Metrics.DensityOp.fidelity, Quantum.Metrics.DensityOp.traceDistance] at hbound
  rwa [toDensityOpExtend_fidelity ρ σ, toDensityOpExtend_traceDistance ρ σ] at hbound

/-- Arithmetic core: `P(ρ, σ) ≤ √(2 · (1 − F*(ρ, σ)))`.

From `P² = 1 − F*² = (1 − F*)(1 + F*) ≤ 2 (1 − F*)` since `0 ≤ F* ≤ 1`. -/
theorem purifiedDistance_le_sqrt_two_mul_one_sub_fidelityGen
    {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    purifiedDistance ρ σ ≤ Real.sqrt (2 * (1 - fidelityGen ρ σ)) := by
  unfold purifiedDistance
  apply Real.sqrt_le_sqrt
  have hF_nonneg : 0 ≤ fidelityGen ρ σ := fidelityGen_nonneg ρ σ
  have hF_le_one : fidelityGen ρ σ ≤ 1 := fidelityGen_le_one ρ σ
  nlinarith [sq_nonneg (fidelityGen ρ σ)]

/-- **Purified distance from generalized trace distance (Nahar et al. [46] Lemma 3.5 / B15).**

For two sub-normalized states the purified distance is controlled by the square root
of twice the generalized trace distance:
`P(ρ, σ) ≤ √(2 · Δ(ρ, σ))`, where `Δ = traceDistanceGen`.

This is the literature-faithful form used in Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024's
accept-split step (Eq. B15): once
the accept-conditioned residual `τ^(2)` has generalized trace distance `≤ εAT` to the
accept-conditioned `τ^(1)`, the purified distance is at most `√(2 εAT)`. It is the
Fuchs–van-de-Graaf direction `P ≤ √(2Δ)` complementing the proved `Δ ≤ P`
(`traceDistanceGen_le_purifiedDistance`), and reduces (via
`one_sub_fidelityGen_le_traceDistanceGen`) to the normalized lower Fuchs–van de Graaf
inequality `1 − F ≤ D`. -/
theorem purifiedDistance_le_sqrt_two_mul_traceDistanceGen
    {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) :
    purifiedDistance ρ σ ≤
      Real.sqrt (2 * Quantum.Metrics.traceDistanceGen ρ.toOp σ.toOp) := by
  calc
    purifiedDistance ρ σ
        ≤ Real.sqrt (2 * (1 - fidelityGen ρ σ)) :=
          purifiedDistance_le_sqrt_two_mul_one_sub_fidelityGen ρ σ
    _ ≤ Real.sqrt (2 * Quantum.Metrics.traceDistanceGen ρ.toOp σ.toOp) := by
          apply Real.sqrt_le_sqrt
          have := one_sub_fidelityGen_le_traceDistanceGen ρ σ
          linarith

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
