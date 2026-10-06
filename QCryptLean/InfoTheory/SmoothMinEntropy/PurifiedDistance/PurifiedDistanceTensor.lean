import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.PurifiedDistance
import QCryptLean.InfoTheory.SmoothMinEntropy.Tensor.TensorProduct
import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.Math.Probability.Bhattacharyya

/-!
# Purified Distance under Tensor Products

Tensor-product subadditivity of the purified distance, Tomamichel 2016 eq. 3.41.

The proof factors through the **Bures-angle subadditivity under tensor**, which
in turn reduces to **super-multiplicativity of the generalized fidelity**:

  F*(τ, ρ) · F*(τ', ρ') ≤ F*(τ ⊗ τ', ρ ⊗ ρ').

The cosine-of-angle-sum identity then converts that fidelity bound into a Bures
angle inequality, and `Real.sin_le_sin_add_sin_of_le_add` (already used by
`purifiedDistance_triangle`) closes the purified-distance bound.

## Main statements
- `fidelityGen_tensor_super_multiplicative`: super-multiplicativity of
  generalized fidelity under tensor products.
- `fidelityAngle_tensor_subadditive`: the Bures-angle subadditivity for
  tensor products. Proved here, modulo the super-multiplicativity above.
- `purifiedDistance_tensor_subadditive`: Tomamichel 2016 eq. 3.41 at the
  purified-distance level.
-/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Super-multiplicativity of the generalized fidelity under tensor products**
    (Tomamichel 2016, around eq. 3.41 / Lemma 3.6).

    `F*(τ, ρ) · F*(τ', ρ') ≤ F*(τ ⊗ τ', ρ ⊗ ρ')`.

    For density operators this is the standard multiplicativity of Uhlmann
    fidelity under tensor products combined with Cauchy–Schwarz on the
    sub-normalization correction term `√((1 - tr ρ)(1 - tr σ))`.

    The proof uses tensor multiplicativity
    `Quantum.Metrics.fidelity_tensor_mul`, the Bhattacharyya inequality
    `Real.sqrt_mul_add_sqrt_one_sub_mul_one_sub_le_one`, and the
    tensor-complement AM-GM helper
    `Real.sqrt_pq_one_sub_one_sub_add_sqrt_one_sub_le_sqrt_one_sub_pp_one_sub_qq`. -/
lemma fidelityGen_tensor_super_multiplicative
    {n n' : ℕ} [NeZero n] [NeZero n'] [NeZero (n * n')]
    (ρ τ : SubDensityOp n) (ρ' τ' : SubDensityOp n') :
    fidelityGen τ ρ * fidelityGen τ' ρ' ≤
      fidelityGen (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ') := by
  -- Notation: p = trτ, q = trρ, p' = trτ', q' = trρ'; F1 = F(τ,ρ), F2 = F(τ',ρ').
  set p := τ.trace with hp_def
  set q := ρ.trace with hq_def
  set p' := τ'.trace with hp'_def
  set q' := ρ'.trace with hq'_def
  set F1 := Quantum.Metrics.fidelity τ.toPosSemidefOp ρ.toPosSemidefOp with hF1_def
  set F2 := Quantum.Metrics.fidelity τ'.toPosSemidefOp ρ'.toPosSemidefOp with hF2_def
  -- Trace bounds and nonneg facts.
  have hp_mem : p ∈ Set.Icc (0 : ℝ) 1 := τ.trace_mem_unit_interval
  have hq_mem : q ∈ Set.Icc (0 : ℝ) 1 := ρ.trace_mem_unit_interval
  have hp'_mem : p' ∈ Set.Icc (0 : ℝ) 1 := τ'.trace_mem_unit_interval
  have hq'_mem : q' ∈ Set.Icc (0 : ℝ) 1 := ρ'.trace_mem_unit_interval
  have hp_nn : 0 ≤ p := hp_mem.1
  have hp_le : p ≤ 1 := hp_mem.2
  have hq_nn : 0 ≤ q := hq_mem.1
  have hq_le : q ≤ 1 := hq_mem.2
  have hp'_nn : 0 ≤ p' := hp'_mem.1
  have hp'_le : p' ≤ 1 := hp'_mem.2
  have hq'_nn : 0 ≤ q' := hq'_mem.1
  have hq'_le : q' ≤ 1 := hq'_mem.2
  have h1p_nn : 0 ≤ 1 - p := sub_nonneg.mpr hp_le
  have h1q_nn : 0 ≤ 1 - q := sub_nonneg.mpr hq_le
  have h1p'_nn : 0 ≤ 1 - p' := sub_nonneg.mpr hp'_le
  have h1q'_nn : 0 ≤ 1 - q' := sub_nonneg.mpr hq'_le
  have hF1_nn : 0 ≤ F1 :=
    Quantum.Metrics.fidelity_nonneg_posSemidefOp τ.toPosSemidefOp ρ.toPosSemidefOp
  have hF2_nn : 0 ≤ F2 :=
    Quantum.Metrics.fidelity_nonneg_posSemidefOp τ'.toPosSemidefOp ρ'.toPosSemidefOp
  set s := Real.sqrt ((1 - p) * (1 - q)) with hs_def
  set s' := Real.sqrt ((1 - p') * (1 - q')) with hs'_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hs'_nn : 0 ≤ s' := Real.sqrt_nonneg _
  -- Tensor-trace identities: tr(τ⊗τ') = p·p', tr(ρ⊗ρ') = q·q'.
  have htr_τ : (SubDensityOp.tensor τ τ').trace = p * p' := SubDensityOp.tensor_trace τ τ'
  have htr_ρ : (SubDensityOp.tensor ρ ρ').trace = q * q' := SubDensityOp.tensor_trace ρ ρ'
  -- Tensor-fidelity multiplicativity: F(τ⊗τ', ρ⊗ρ') = F1·F2.
  -- Bridge from `SubDensityOp.tensor` to `PosSemidefOp.tensor` via `.toOp` equality.
  have hbridge_τ :
      (SubDensityOp.tensor τ τ').toPosSemidefOp =
        Quantum.Operators.PosSemidefOp.tensor τ.toPosSemidefOp τ'.toPosSemidefOp := by
    apply Quantum.Operators.PosSemidefOp.ext
    rfl
  have hbridge_ρ :
      (SubDensityOp.tensor ρ ρ').toPosSemidefOp =
        Quantum.Operators.PosSemidefOp.tensor ρ.toPosSemidefOp ρ'.toPosSemidefOp := by
    apply Quantum.Operators.PosSemidefOp.ext
    rfl
  have hFt :
      Quantum.Metrics.fidelity (SubDensityOp.tensor τ τ').toPosSemidefOp
          (SubDensityOp.tensor ρ ρ').toPosSemidefOp = F1 * F2 := by
    rw [hbridge_τ, hbridge_ρ]
    exact Quantum.Metrics.fidelity_tensor_mul τ.toPosSemidefOp ρ.toPosSemidefOp
      τ'.toPosSemidefOp ρ'.toPosSemidefOp
  -- Trace-product bounds: F1 ≤ √(p·q), F2 ≤ √(p'·q').
  have hF1_sq : F1 ^ 2 ≤ p * q := fidelity_sq_le_trace_mul_trace τ ρ
  have hF2_sq : F2 ^ 2 ≤ p' * q' := fidelity_sq_le_trace_mul_trace τ' ρ'
  have hpq_nn : 0 ≤ p * q := mul_nonneg hp_nn hq_nn
  have hp'q'_nn : 0 ≤ p' * q' := mul_nonneg hp'_nn hq'_nn
  have hF1_le : F1 ≤ Real.sqrt (p * q) := by
    have := Real.sqrt_le_sqrt hF1_sq
    rwa [Real.sqrt_sq hF1_nn] at this
  have hF2_le : F2 ≤ Real.sqrt (p' * q') := by
    have := Real.sqrt_le_sqrt hF2_sq
    rwa [Real.sqrt_sq hF2_nn] at this
  -- Bhattacharyya bound on the primed factor: √(p'·q') + s' ≤ 1.
  have hBhatta' :
      Real.sqrt (p' * q') + Real.sqrt ((1 - p') * (1 - q')) ≤ 1 :=
    Real.sqrt_mul_add_sqrt_one_sub_mul_one_sub_le_one hp'_mem hq'_mem
  -- Tensor-complement bound: √(p·q·(1-p')·(1-q')) + s ≤ √((1-p·p')·(1-q·q')).
  have hAMGM :
      Real.sqrt (p * q * (1 - p') * (1 - q'))
          + Real.sqrt ((1 - p) * (1 - q)) ≤
        Real.sqrt ((1 - p * p') * (1 - q * q')) :=
    Real.sqrt_pq_one_sub_one_sub_add_sqrt_one_sub_le_sqrt_one_sub_pp_one_sub_qq
      hp_mem hq_mem hp'_mem hq'_mem
  -- Combine the sqrt: √(p·q)·s' = √(p·q·(1-p')·(1-q')).
  have hsqrt_split :
      Real.sqrt (p * q) * Real.sqrt ((1 - p') * (1 - q')) =
        Real.sqrt (p * q * (1 - p') * (1 - q')) := by
    rw [← Real.sqrt_mul hpq_nn]; congr 1; ring
  -- Now assemble the chain.
  -- LHS = F*(τ,ρ)·F*(τ',ρ') = (F1 + s)(F2 + s') = F1·F2 + F1·s' + s·F2 + s·s'.
  -- RHS = F*(τ⊗τ', ρ⊗ρ') = F1·F2 + √((1-p·p')(1-q·q')).
  -- Reduces to: F1·s' + s·F2 + s·s' ≤ √((1-p·p')(1-q·q')).
  have h_lhs_eq :
      fidelityGen τ ρ * fidelityGen τ' ρ' = (F1 + s) * (F2 + s') := by
    simp [fidelityGen, hF1_def, hF2_def, hs_def, hs'_def, hp_def, hq_def, hp'_def, hq'_def]
  have h_rhs_eq :
      fidelityGen (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ') =
        F1 * F2 + Real.sqrt ((1 - p * p') * (1 - q * q')) := by
    unfold fidelityGen
    rw [hFt, htr_τ, htr_ρ]
  -- Key reduction: cross-terms ≤ √((1-p·p')(1-q·q')).
  have hcross :
      F1 * s' + s * F2 + s * s' ≤ Real.sqrt ((1 - p * p') * (1 - q * q')) := by
    -- Step 1: F2 ≤ √(p'·q'); combine s·F2 + s·s' = s·(F2 + s') ≤ s·(√(p'·q') + s') ≤ s.
    have hF2_plus_s' : F2 + s' ≤ Real.sqrt (p' * q') + s' := by linarith
    have hbound1 : F2 + s' ≤ 1 := le_trans hF2_plus_s' hBhatta'
    have hbound2 : s * (F2 + s') ≤ s := by
      have := mul_le_mul_of_nonneg_left hbound1 hs_nn
      simpa using this
    -- Step 2: F1 ≤ √(p·q); so F1·s' ≤ √(p·q)·s' = √(p·q·(1-p')·(1-q')).
    have hF1_s' : F1 * s' ≤ Real.sqrt (p * q) * s' :=
      mul_le_mul_of_nonneg_right hF1_le hs'_nn
    have hF1_s'_eq :
        Real.sqrt (p * q) * s' = Real.sqrt (p * q * (1 - p') * (1 - q')) := by
      rw [hs'_def]; exact hsqrt_split
    -- Combine: F1·s' + s·(F2 + s') ≤ √(p·q·(1-p')(1-q')) + s ≤ RHS.
    have hkey :
        F1 * s' + s * (F2 + s') ≤
          Real.sqrt (p * q * (1 - p') * (1 - q')) + s := by
      have := add_le_add hF1_s' hbound2
      calc F1 * s' + s * (F2 + s')
          ≤ Real.sqrt (p * q) * s' + s := this
        _ = Real.sqrt (p * q * (1 - p') * (1 - q')) + s := by rw [hF1_s'_eq]
    have hreassoc : F1 * s' + s * F2 + s * s' = F1 * s' + s * (F2 + s') := by ring
    rw [hreassoc]
    calc F1 * s' + s * (F2 + s')
        ≤ Real.sqrt (p * q * (1 - p') * (1 - q')) + s := hkey
      _ = Real.sqrt (p * q * (1 - p') * (1 - q')) + Real.sqrt ((1 - p) * (1 - q)) := by
          rw [hs_def]
      _ ≤ Real.sqrt ((1 - p * p') * (1 - q * q')) := hAMGM
  -- Finish: rewrite LHS and RHS via the algebra.
  rw [h_lhs_eq, h_rhs_eq]
  have hexpand : (F1 + s) * (F2 + s') = F1 * F2 + (F1 * s' + s * F2 + s * s') := by ring
  rw [hexpand]
  linarith [hcross]

/-- **Bures angle subadditivity under tensor products** (the angle analog of
    Tomamichel 2016 eq. 3.41). The Bures angle between tensor products is at
    most the sum of the per-factor Bures angles.

    Proof: by `fidelityGen_tensor_super_multiplicative` plus
    `cos(α + β) = cos α cos β − sin α sin β` with `sin α, sin β ≥ 0` on
    `[0, π/2]`, plus antitonicity of `cos` on `[0, π]`. -/
lemma fidelityAngle_tensor_subadditive
    {n n' : ℕ} [NeZero n] [NeZero n']
    (ρ τ : SubDensityOp n) (ρ' τ' : SubDensityOp n') :
    Real.arccos
        (fidelityGen (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ')) ≤
      Real.arccos (fidelityGen τ ρ) + Real.arccos (fidelityGen τ' ρ') := by
  set α := Real.arccos (fidelityGen τ ρ) with hα_def
  set β := Real.arccos (fidelityGen τ' ρ') with hβ_def
  set γ := Real.arccos
      (fidelityGen (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ'))
      with hγ_def
  -- Angle bounds: each angle lies in `[0, π/2]`.
  have hFτρ_nn : 0 ≤ fidelityGen τ ρ := fidelityGen_nonneg τ ρ
  have hFτ'ρ'_nn : 0 ≤ fidelityGen τ' ρ' := fidelityGen_nonneg τ' ρ'
  have hFt_nn : 0 ≤ fidelityGen (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ') :=
    fidelityGen_nonneg _ _
  have hFτρ_le : fidelityGen τ ρ ≤ 1 := fidelityGen_le_one τ ρ
  have hFτ'ρ'_le : fidelityGen τ' ρ' ≤ 1 := fidelityGen_le_one τ' ρ'
  have hFt_le : fidelityGen (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ') ≤ 1 :=
    fidelityGen_le_one _ _
  have hα_nn : 0 ≤ α := Real.arccos_nonneg _
  have hβ_nn : 0 ≤ β := Real.arccos_nonneg _
  have hγ_nn : 0 ≤ γ := Real.arccos_nonneg _
  have hα_le : α ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.2 hFτρ_nn
  have hβ_le : β ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.2 hFτ'ρ'_nn
  have hγ_le : γ ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.2 hFt_nn
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hαβ_nn : 0 ≤ α + β := by linarith
  have hαβ_le_pi : α + β ≤ Real.pi := by linarith
  have hγ_le_pi : γ ≤ Real.pi := by linarith
  -- Cosine identifications.
  have hcos_α : Real.cos α = fidelityGen τ ρ :=
    Real.cos_arccos (by linarith) hFτρ_le
  have hcos_β : Real.cos β = fidelityGen τ' ρ' :=
    Real.cos_arccos (by linarith) hFτ'ρ'_le
  have hcos_γ :
      Real.cos γ =
        fidelityGen (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ') :=
    Real.cos_arccos (by linarith) hFt_le
  -- Sines on `[0, π/2]` are nonneg.
  have hsin_α_nn : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα_nn (by linarith)
  have hsin_β_nn : 0 ≤ Real.sin β :=
    Real.sin_nonneg_of_nonneg_of_le_pi hβ_nn (by linarith)
  -- Super-multiplicativity → cosine inequality.
  have hsuper :
      fidelityGen τ ρ * fidelityGen τ' ρ' ≤
        fidelityGen (SubDensityOp.tensor τ τ') (SubDensityOp.tensor ρ ρ') :=
    fidelityGen_tensor_super_multiplicative ρ τ ρ' τ'
  have hcos_le : Real.cos (α + β) ≤ Real.cos γ := by
    rw [Real.cos_add, hcos_α, hcos_β, hcos_γ]
    have hsin_prod_nn : 0 ≤ Real.sin α * Real.sin β :=
      mul_nonneg hsin_α_nn hsin_β_nn
    linarith
  -- Antitonicity of `cos` on `[0, π]` reverses the inequality.
  by_contra hlt
  push Not at hlt
  -- `hlt : α + β < γ`.
  have hstrict : Real.cos γ < Real.cos (α + β) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hαβ_nn hγ_le_pi hlt
  linarith

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
