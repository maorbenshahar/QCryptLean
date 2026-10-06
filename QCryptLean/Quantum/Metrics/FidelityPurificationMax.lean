import QCryptLean.Quantum.Metrics.SameAncillaPurification
import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.Quantum.Metrics.TraceNorm.FidelitySymm
import QCryptLean.Quantum.Metrics.TraceOpNormBound
import QCryptLean.Quantum.Operators.BraKet.Projector

/-!
# Uhlmann Upper Bound — purification overlap bounded by fidelity

This file states the **upper-bound direction** of Uhlmann's theorem
(Watrous Prop. 3.13 (i) / Nielsen–Chuang §9.2.3):

For any two density operators `ρ, τ : DensityOp d`, and any pair of
**normalized purifications** `ψρ, ψτ : Ket (d * d)` with

    `partialTraceB (ψρ * ψρ.dag) = ρ.toOp`
    `partialTraceB (ψτ * ψτ.dag) = τ.toOp`,

the bra–ket overlap is bounded by the Uhlmann fidelity:

    `‖⟨ψρ | ψτ⟩‖ ≤ F(ρ, τ)`.

The corresponding *achievability* direction (existence of some purification
pair saturating the bound) is available in the repository as
`sameAncillaPurificationDensity_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich`
(in `KitaevWatrousPurification.lean`).

## Main theorems

- `fidelity_ge_purification_overlap_norm`: Uhlmann upper bound for same-ancilla purifications —
  `‖⟨ψρ | ψτ⟩‖ ≤ F(ρ, τ)` for `ψρ ψτ : Ket (d * d)` purifying `ρ τ : DensityOp d`.
- `fidelity_ge_purification_overlap_re`: real-part corollary of the above.
- `fidelity_ge_canonical_overlap_norm`: canonical-ket form of the upper bound with an inserted
  system-side unitary — `‖ψτ.dag * (V ⊗ 1) * ψρ‖ ≤ F(ρ, τ)`.

## Supporting results

- `sameAncillaPurificationKet_ancilla_unitary_of_purifies` (in `SameAncillaPurification.lean`):
  purification uniqueness — any normalized purification on a same-size ancilla
  equals the canonical ket left-multiplied by an ancilla-side unitary.
- `sameAncillaPurificationKet_ancilla_unitary_overlap_le_fidelity`: the
  ancilla-side overlap bound — `‖ψρ_can.dag * (1 ⊗ V) * ψτ_can‖ ≤ F(ρ,τ)`.
- `fidelity_le_fidelity_partialTraceB` (in `FidelityPartialTraceMonotone.lean`):
  fidelity monotonicity under partial trace —
  `F(A, B) ≤ F(A.partialTraceB, B.partialTraceB)` for `A B : PosSemidefOp (dE * dR)`.

Only the upper-bound (`≤`) direction of Uhlmann's theorem is provided here; the full sup
characterization `F(ρ, τ) = ⨆_{purifications} ‖⟨ψρ | ψτ⟩‖` (Watrous Prop. 3.13 (ii)) is not
formalized in this file.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Quantum.Metrics

open Quantum.Metrics.KitaevWatrousPurification

/-- **Ancilla-side unitary overlap bound for canonical purifications**.

For any two density operators `ρ τ : DensityOp d` and any unitary
`V : UnitaryOp d`, the overlap between the canonical same-ancilla purifications
with an ancilla-side unitary `V` inserted satisfies:

    `‖(sameAncillaPurificationKet ρ).dag * (1 ⊗ V) * sameAncillaPurificationKet τ‖ ≤ F(ρ, τ)`.

The proof uses `⟨Ω|(A ⊗ B)|Ω⟩ = Tr(A · B^T)` to rewrite the overlap as
`Tr(√ρ · √τ · V^T)`, then applies `|Tr(W · X)| ≤ ‖X‖₁` with the unitary
`W = V^T` and identifies `‖√ρ · √τ‖₁ = F(ρ, τ)`. -/
theorem sameAncillaPurificationKet_ancilla_unitary_overlap_le_fidelity
    {d : ℕ} [NeZero d] (ρ τ : DensityOp d) (V : UnitaryOp d) :
    ‖((sameAncillaPurificationKet ρ).dag *
        Op.tensor (1 : Op d) V.toOp *
        sameAncillaPurificationKet τ : ℂ)‖
      ≤ Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp := by
  -- Ancilla-side ricochet: canonical-ket overlap equals `Tr(√ρ · √τ · Vᵀ)`.
  rw [Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet_ancilla_left_mul_eq_trace
      ρ τ V.toOp]
  -- Cyclicity of the trace: Tr(√ρ · √τ · Vᵀ) = Tr(Vᵀ · (√ρ · √τ)).
  have hcycle :
      (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp * V.toOp.transpose).trace =
        (V.toOp.transpose * (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp)).trace := by
    rw [Matrix.trace_mul_comm]
  rw [hcycle]
  -- Trace-opNorm-traceNorm bound: ‖Tr(Vᵀ · X)‖ ≤ ‖Vᵀ‖ · traceNorm X.
  have hbound :
      ‖(V.toOp.transpose * (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp)).trace‖ ≤
        ‖V.toOp.transpose‖ * traceNorm (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp) :=
    Quantum.Metrics.TraceOpNormBound.norm_trace_mul_le_opNorm_mul_traceNorm
      V.toOp.transpose (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp)
  -- The operator norm of the transposed unitary is `1`.
  have hV_norm : ‖V.toOp.transpose‖ = 1 :=
    Quantum.Metrics.TraceOpNormBound.unitaryOp_opNorm_eq_one (UnitaryOp.transpose V)
  rw [← fidelity_eq_traceNorm_cfcSqrt_mul ρ τ, hV_norm, one_mul] at hbound
  exact hbound

/-- Derive normalization from purification of a density operator.

If `ψ : Ket (d * d)` satisfies `partialTraceB (ψ * ψ.dag) = ρ.toOp` for a
density operator `ρ : DensityOp d`, then `ψ` is a unit vector. -/
private lemma ket_normalized_of_purifies_density
    {d : ℕ} (ρ : DensityOp d)
    (ψ : Ket (d * d))
    (hpuρ : partialTraceB (ψ * ψ.dag) = ρ.toOp) :
    ψ.dag * ψ = 1 := by
  have htrace : (ψ * ψ.dag).trace = 1 := by
    have h1 : (partialTraceB (ψ * ψ.dag)).trace = (ψ * ψ.dag).trace :=
      trace_partialTraceB (ψ * ψ.dag)
    rw [hpuρ] at h1
    rw [← h1]
    exact ρ.trace_one
  -- trace_ketbra_mul gives: (ψ * ψ.dag * 1).trace = ψ.dag * 1 * ψ
  have hstep : ((ψ * ψ.dag) * (1 : Op (d * d))).trace = ψ.dag * (1 : Op (d * d)) * ψ :=
    trace_ketbra_mul ψ (1 : Op (d * d))
  -- Simplify left: (ψ * ψ.dag * 1).trace = (ψ * ψ.dag).trace
  have hleft : ((ψ * ψ.dag) * (1 : Op (d * d))).trace = (ψ * ψ.dag).trace := by
    rw [Matrix.mul_one]
  -- Simplify right: ψ.dag * 1 * ψ = ψ.dag * ψ
  have hright : ψ.dag * (1 : Op (d * d)) * ψ = ψ.dag * ψ := by
    have hbra1 : ψ.dag * (1 : Op (d * d)) = ψ.dag := by
      ext j
      simp only [bra_mul_op_vec, Matrix.one_apply]
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ j]
      simp
    rw [hbra1]
  rw [hleft, hright] at hstep
  -- hstep : (ψ * ψ.dag).trace = ψ.dag * ψ
  rw [← hstep, htrace]

/-- **Uhlmann upper bound** (Watrous Prop. 3.13 (i); Nielsen–Chuang §9.2.3).

For any two density operators `ρ, τ : DensityOp d` and any two normalized
purifications `ψρ, ψτ : Ket (d * d)` (with `partialTraceB (ψ * ψ.dag)` equal to
the corresponding state on the first factor), the bra–ket overlap is bounded
by the Uhlmann fidelity:

    `‖⟨ψρ | ψτ⟩‖ ≤ F(ρ, τ)`.

The proof applies purification uniqueness
(`sameAncillaPurificationKet_ancilla_unitary_of_purifies`) to express each
purification as an ancilla-side unitary applied to the canonical ket, then uses
the ancilla-side overlap bound
(`sameAncillaPurificationKet_ancilla_unitary_overlap_le_fidelity`). -/
theorem fidelity_ge_purification_overlap_norm
    {d : ℕ} [NeZero d] (ρ τ : DensityOp d)
    (ψρ ψτ : Ket (d * d))
    (hpuρ : partialTraceB (ψρ * ψρ.dag) = ρ.toOp)
    (hpuτ : partialTraceB (ψτ * ψτ.dag) = τ.toOp) :
    ‖(ψρ.dag * ψτ : ℂ)‖
      ≤ Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp := by
  -- Derive normalization from the purification condition.
  have hψρ_norm : ψρ.dag * ψρ = 1 := ket_normalized_of_purifies_density ρ ψρ hpuρ
  have hψτ_norm : ψτ.dag * ψτ = 1 := ket_normalized_of_purifies_density τ ψτ hpuτ
  -- Apply purification uniqueness to each ket.
  obtain ⟨Uρ, hUρ⟩ :=
    sameAncillaPurificationKet_ancilla_unitary_of_purifies ρ ψρ hψρ_norm hpuρ
  obtain ⟨Uτ, hUτ⟩ :=
    sameAncillaPurificationKet_ancilla_unitary_of_purifies τ ψτ hψτ_norm hpuτ
  -- The composite ancilla unitary V = Uρ† · Uτ.
  let V : UnitaryOp d := UnitaryOp.mul Uρ.adj Uτ
  -- Rewrite the overlap using hUρ and hUτ.
  -- ψρ.dag * ψτ = ψρ_can.dag * (1 ⊗ Uρ†) * (1 ⊗ Uτ) * ψτ_can
  --             = ψρ_can.dag * (1 ⊗ Uρ†Uτ) * ψτ_can
  --             = ψρ_can.dag * (1 ⊗ V) * ψτ_can
  have hoverlap_eq :
      (ψρ.dag * ψτ : ℂ) =
        (sameAncillaPurificationKet ρ).dag *
          Op.tensor (1 : Op d) V.toOp *
          sameAncillaPurificationKet τ := by
    set ψρ_can := sameAncillaPurificationKet ρ
    set ψτ_can := sameAncillaPurificationKet τ
    set Aρ : Op (d * d) := Op.tensor (1 : Op d) Uρ.toOp
    set Aτ : Op (d * d) := Op.tensor (1 : Op d) Uτ.toOp
    -- Rewrite ψρ and ψτ in terms of canonical kets.
    rw [hUρ, hUτ]
    -- Apply dag_op_mul_ket to the bra factor.
    have hdag : (Aρ * ψρ_can).dag = ψρ_can.dag * Aρ† := dag_op_mul_ket Aρ ψρ_can
    -- Conjugate of the ancilla tensor: (1 ⊗ Uρ)† = 1 ⊗ Uρ†
    have hAdagρ : Aρ† = Op.tensor (1 : Op d) Uρ.toOp.conjTranspose := by
      simp [Aρ, Op.tensor_conjTranspose, conjTranspose_one]
    -- The two ancilla factors combine: (1 ⊗ Uρ†) * (1 ⊗ Uτ) = 1 ⊗ (Uρ† * Uτ) = 1 ⊗ V
    have hcombine : Op.tensor (1 : Op d) Uρ.toOp.conjTranspose * Aτ =
        Op.tensor (1 : Op d) V.toOp := by
      simp [Aτ, Op.tensor_mul, V, UnitaryOp.mul, UnitaryOp.adj]
    -- Now chain everything.
    -- Note: (Aρ * ψρ_can).dag : Bra (d*d), (Aτ * ψτ_can) : Ket (d*d), so product is ℂ.
    change ((Aρ * ψρ_can).dag * (Aτ * ψτ_can) : ℂ) =
        (ψρ_can.dag * Op.tensor (1 : Op d) V.toOp * ψτ_can : ℂ)
    calc ((Aρ * ψρ_can).dag * (Aτ * ψτ_can) : ℂ)
        = ((ψρ_can.dag * Aρ†) * (Aτ * ψτ_can) : ℂ) := by rw [hdag]
      _ = (ψρ_can.dag * (Aρ† * (Aτ * ψτ_can)) : ℂ) := by rw [braop_mul_ket]
      _ = (ψρ_can.dag * ((Aρ† * Aτ) * ψτ_can) : ℂ) := by rw [op_op_mul_ket_assoc]
      _ = (ψρ_can.dag * (Op.tensor (1 : Op d) Uρ.toOp.conjTranspose * Aτ) * ψτ_can : ℂ) := by
            rw [hAdagρ, ← braop_mul_ket]
      _ = (ψρ_can.dag * Op.tensor (1 : Op d) V.toOp * ψτ_can : ℂ) := by rw [hcombine]
  rw [hoverlap_eq]
  exact sameAncillaPurificationKet_ancilla_unitary_overlap_le_fidelity ρ τ V

/-- Real-part consequence of `fidelity_ge_purification_overlap_norm`, obtained
via `Complex.re_le_norm`: the real part of the overlap is bounded above by the
Uhlmann fidelity. -/
theorem fidelity_ge_purification_overlap_re
    {d : ℕ} [NeZero d] (ρ τ : DensityOp d)
    (ψρ ψτ : Ket (d * d))
    (hpuρ : partialTraceB (ψρ * ψρ.dag) = ρ.toOp)
    (hpuτ : partialTraceB (ψτ * ψτ.dag) = τ.toOp) :
    (ψρ.dag * ψτ : ℂ).re
      ≤ Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp :=
  (Complex.re_le_norm _).trans
    (fidelity_ge_purification_overlap_norm ρ τ ψρ ψτ hpuρ hpuτ)

-- The Uhlmann partial-trace monotonicity theorem
-- `fidelity_le_fidelity_partialTraceB` is proved in `FidelityPartialTraceMonotone.lean`.

/-- **Uhlmann upper bound, canonical-with-inserted-unitary form**
(Watrous Prop. 3.13 (i); Nielsen–Chuang §9.2.3).

For any two density operators `ρ, τ : DensityOp d` and any unitary
`V : UnitaryOp d`, the overlap between the canonical same-ancilla purifications
with a system-side unitary `V` inserted is bounded in norm by the Uhlmann
fidelity:

    `‖ψτ.dag * (V ⊗ 1) * ψρ‖ ≤ F(ρ, τ)`,

where
`ψρ := (sameAncillaPurificationDensity ρ).pureKetOf
  (sameAncillaPurificationDensity_isPure ρ)` and analogously for `ψτ`.

This is the trace-norm form of Uhlmann's upper bound: by a ricochet calculation
this is equivalent to `‖Tr(√τ · V · √ρ)‖ ≤ F(ρ, τ)`, a clean Hölder-on-Schatten
consequence of `F(ρ, τ) = ‖√ρ · √τ‖₁`. -/
theorem fidelity_ge_canonical_overlap_norm
    {d : ℕ} [NeZero d] (ρ τ : DensityOp d) (V : UnitaryOp d) :
    let ψρ := (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity ρ).pureKetOf
      (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity_isPure ρ)
    let ψτ := (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity τ).pureKetOf
      (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationDensity_isPure τ)
    ‖(ψτ.dag * (Op.tensor V.toOp (1 : Op d)) * ψρ : ℂ)‖
      ≤ Quantum.Metrics.fidelity ρ.toPosSemidefOp τ.toPosSemidefOp := by
  intro ψρ ψτ
  -- Phase transport: overlap norm is the same in canonical-ket form.
  have h_phase :
      ‖(ψτ.dag * Op.tensor V.toOp (1 : Op d) * ψρ : ℂ)‖ =
        ‖((sameAncillaPurificationKet τ).dag *
          Op.tensor V.toOp (1 : Op d) *
          sameAncillaPurificationKet ρ : ℂ)‖ :=
    sameAncillaPurificationDensity_pureKet_tensorUnitary_overlap_norm_eq_canonical ρ τ V.toOp
  rw [h_phase]
  -- Ricochet: canonical-ket overlap equals the trace expression.
  rw [Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet_left_mul_eq_trace
      ρ τ V.toOp]
  -- Cyclicity of the trace: Tr(√τ V √ρ) = Tr(V · √ρ · √τ).
  have hcycle :
      (CFC.sqrt τ.toOp * V.toOp * CFC.sqrt ρ.toOp).trace =
        (V.toOp * (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp)).trace := by
    calc (CFC.sqrt τ.toOp * V.toOp * CFC.sqrt ρ.toOp).trace
        = (CFC.sqrt ρ.toOp * (CFC.sqrt τ.toOp * V.toOp)).trace := by
            rw [Matrix.trace_mul_comm]
      _ = ((CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp) * V.toOp).trace := by
            simp [Matrix.mul_assoc]
      _ = (V.toOp * (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp)).trace := by
            rw [Matrix.trace_mul_comm]
  rw [hcycle]
  -- Trace-opNorm-traceNorm bound: ‖Tr(V · X)‖ ≤ ‖V‖ · traceNorm X.
  have hbound :
      ‖(V.toOp * (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp)).trace‖ ≤
        ‖V.toOp‖ * traceNorm (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp) :=
    Quantum.Metrics.TraceOpNormBound.norm_trace_mul_le_opNorm_mul_traceNorm
      V.toOp (CFC.sqrt ρ.toOp * CFC.sqrt τ.toOp)
  -- The operator norm of a unitary is `1`.
  have hV_norm : ‖V.toOp‖ = 1 :=
    Quantum.Metrics.TraceOpNormBound.unitaryOp_opNorm_eq_one V
  rw [← fidelity_eq_traceNorm_cfcSqrt_mul ρ τ, hV_norm, one_mul] at hbound
  exact hbound

end Quantum.Metrics

end -- noncomputable section
