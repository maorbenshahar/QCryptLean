import QCryptLean.Quantum.Metrics.SameAncillaPurification
import QCryptLean.Quantum.Metrics.PurificationUnitaryAction
import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity
import QCryptLean.Quantum.Operators.BraKet.Projector

/-!
# Same-Ancilla Uhlmann Witness Kets — `ketB`, PSD branches, overlap realization

Witness kets for the same-ancilla form of Uhlmann's theorem, both for
normalized density operators and for positive semidefinite operators.

Given two normalized density operators `ρ', σ' : DensityOp m` and a
`UnitaryOp m` witness `U`, we construct a second purification ket

    `ketB σ' U := ((√σ' · U) ⊗ 1) · |Ω⟩`

whose reduced state on the system factor is `σ'` but which, when paired
with the canonical purification ket `sameAncillaPurificationKet ρ'` of
`ρ'`, realizes the Uhlmann overlap `Tr(√ρ' · √σ' · U)`. Choosing `U` from
`sameAncillaPurificationKet_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich`
makes the real part of this overlap equal to `F(ρ', σ')`.

## Main definitions
- `ketB`: same-ancilla target purification for a density operator and unitary
  witness
- `ketBOfOp`: positive-semidefinite analogue of `ketB`

## Main statements
- `ketB_normalized` — `(ketB σ' U).dag * (ketB σ' U) = 1`.
- `ketB_partialTraceB` — `partialTraceB (ketB * ketB.dag) = σ'.toOp`.
- `ketBOfOp_partialTraceB` — the analogous reduced-state identity for
  positive semidefinite inputs
- `ketBOfOp_norm` — the PSD branch has squared norm `Tr σ`
- `sameAncillaPurificationKet_dag_mul_ketB_eq_trace`
    — `ψρ'.dag * ketB = (√ρ' · √σ' · U).trace`
- `sameAncillaPurificationKetOfOp_dag_mul_ketBOfOp_eq_trace`
    — the same trace identity for positive semidefinite inputs
- `ketB_re_overlap_of_witness` — for the canonical Uhlmann witness
  `U` chosen as in
  `sameAncillaPurificationKet_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich`,
  the real part of `ψρ'.dag * ketB` is the Uhlmann fidelity `F(ρ', σ')`
- `exists_ketBOfOp_unitary_overlap_re_eq_fidelity`: a unitary witness realizes
  PSD fidelity using `ketBOfOp`
- `exists_sameAncillaPurificationKetOfOp_overlap_re_eq_fidelity`: existential
  target-branch form of PSD same-ancilla achievability
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics.UhlmannWitness

open Quantum.Metrics.KitaevWatrousPurification

/-- The Strategy-A' purification ket of `σ'`, with the Uhlmann-witness
unitary `U` absorbed into the system-side square-root leg:

  `ketB σ' U = ((√σ' · U) ⊗ 1) * |Ω⟩`.

Its reduced state on the system factor is `σ'.toOp` (see
`ketB_partialTraceB`), and its outer product is therefore a purification
of `σ'` with the same ancilla as the canonical purification of `ρ'`. -/
noncomputable def ketB {m : ℕ} (σ' : DensityOp m) (U : UnitaryOp m) :
    Ket (m * m) :=
  (Op.tensor (CFC.sqrt σ'.toOp * U.toOp) (1 : Op m)) *
    InfoTheory.DeFinetti.maxEntangledKet m

/-- PSD version of `ketB`, with the unitary witness supplied explicitly.

This is the same-ancilla branch
`((√σ · U) ⊗ 1) |Ω⟩` for an arbitrary positive semidefinite operator `σ`. -/
noncomputable def ketBOfOp {m : ℕ} (σ : PosSemidefOp m) (U : UnitaryOp m) :
    Ket (m * m) :=
  (Op.tensor (CFC.sqrt σ.toOp * U.toOp) (1 : Op m)) *
    InfoTheory.DeFinetti.maxEntangledKet m

/-- Outer product expansion of `ketBOfOp`. -/
lemma ketBOfOp_outer {m : ℕ} (σ : PosSemidefOp m) (U : UnitaryOp m) :
    (ketBOfOp σ U) * (ketBOfOp σ U).dag =
      Op.tensor (CFC.sqrt σ.toOp * U.toOp) (1 : Op m) *
        InfoTheory.DeFinetti.maxEntangledOp m *
        (Op.tensor (CFC.sqrt σ.toOp * U.toOp) (1 : Op m))† := by
  set S : Op m := CFC.sqrt σ.toOp * U.toOp with hS
  set A : Op (m * m) := Op.tensor S (1 : Op m) with hA
  change (A * InfoTheory.DeFinetti.maxEntangledKet m) *
         (A * InfoTheory.DeFinetti.maxEntangledKet m).dag =
       A * InfoTheory.DeFinetti.maxEntangledOp m * A†
  calc (A * InfoTheory.DeFinetti.maxEntangledKet m) *
         (A * InfoTheory.DeFinetti.maxEntangledKet m).dag
      = (A * InfoTheory.DeFinetti.maxEntangledKet m) *
          ((InfoTheory.DeFinetti.maxEntangledKet m).dag * A†) := by
          rw [dag_op_mul_ket]
    _ = A * (InfoTheory.DeFinetti.maxEntangledKet m *
          (InfoTheory.DeFinetti.maxEntangledKet m).dag) * A† := by
          rw [op_mul_ketbra, ketbra_mul_op]
    _ = A * InfoTheory.DeFinetti.maxEntangledOp m * A† := by
          rw [InfoTheory.DeFinetti.maxEntangledOp_eq_ketbra]

/-- Multiplying a PSD square root on the right by a unitary preserves the
operator recovered by its right Gram product. -/
lemma cfc_sqrt_mul_unitary_mul_conjTranspose {m : ℕ}
    (σ : PosSemidefOp m) (U : UnitaryOp m) :
    (CFC.sqrt σ.toOp * U.toOp) * (CFC.sqrt σ.toOp * U.toOp)† = σ.toOp := by
  have hUright : U.toOp * U.toOp† = 1 := U.unitary_right
  have hsqrt_herm : (CFC.sqrt σ.toOp)† = CFC.sqrt σ.toOp :=
    Math.SpectralTheory.cfc_sqrt_conjTranspose_eq σ.toOp
  have hsqrt_sq : CFC.sqrt σ.toOp * CFC.sqrt σ.toOp = σ.toOp :=
    CFC.sqrt_mul_sqrt_self σ.toOp (ha := (posSemidefOp_implies_mathlib σ).nonneg)
  calc
    (CFC.sqrt σ.toOp * U.toOp) * (CFC.sqrt σ.toOp * U.toOp)†
        = (CFC.sqrt σ.toOp * U.toOp) * (U.toOp† * (CFC.sqrt σ.toOp)†) := by
            rw [conjTranspose_mul]
    _ = CFC.sqrt σ.toOp * (U.toOp * U.toOp†) * (CFC.sqrt σ.toOp)† := by
            simp only [Matrix.mul_assoc]
    _ = CFC.sqrt σ.toOp * 1 * (CFC.sqrt σ.toOp)† := by rw [hUright]
    _ = CFC.sqrt σ.toOp * CFC.sqrt σ.toOp := by
            rw [Matrix.mul_one, hsqrt_herm]
    _ = σ.toOp := hsqrt_sq

/-- The PSD `ketBOfOp` branch reduces to its input positive semidefinite
operator after tracing out the same-dimensional ancilla. -/
lemma ketBOfOp_partialTraceB {m : ℕ} (σ : PosSemidefOp m) (U : UnitaryOp m) :
    partialTraceB ((ketBOfOp σ U) * (ketBOfOp σ U).dag) = σ.toOp := by
  rw [ketBOfOp_outer]
  set S : Op m := CFC.sqrt σ.toOp * U.toOp with hS
  have hAdag : (Op.tensor S (1 : Op m))† = Op.tensor S† (1 : Op m) := by
    rw [Op.tensor_conjTranspose, conjTranspose_one]
  rw [hAdag]
  rw [Quantum.TensorProducts.partialTraceB_sandwich_tensor_one S S†
      (InfoTheory.DeFinetti.maxEntangledOp m)]
  rw [InfoTheory.DeFinetti.maxEntangledOp_partialTraceB, Matrix.mul_one]
  simpa [hS] using cfc_sqrt_mul_unitary_mul_conjTranspose σ U

/-- The squared norm of the PSD `ketBOfOp` branch is the trace of its input. -/
lemma ketBOfOp_norm {m : ℕ} (σ : PosSemidefOp m) (U : UnitaryOp m) :
    (ketBOfOp σ U).dag * ketBOfOp σ U = σ.toOp.trace := by
  have htrace := congrArg Matrix.trace (ketBOfOp_partialTraceB σ U)
  rw [trace_partialTraceB, ketbra_trace_eq_inner] at htrace
  exact htrace

/-- The right Gram product of two PSD square roots is the usual
sqrt-sandwich operator. -/
lemma cfc_sqrt_mul_cfc_sqrt_mul_conjTranspose {m : ℕ}
    (ρ σ : PosSemidefOp m) :
    (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp) *
        (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp)† =
      CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp := by
  have hρ_sqrt : (CFC.sqrt ρ.toOp)† = CFC.sqrt ρ.toOp :=
    Math.SpectralTheory.cfc_sqrt_conjTranspose_eq ρ.toOp
  have hσ_sqrt : (CFC.sqrt σ.toOp)† = CFC.sqrt σ.toOp :=
    Math.SpectralTheory.cfc_sqrt_conjTranspose_eq σ.toOp
  have hσ_mul : CFC.sqrt σ.toOp * CFC.sqrt σ.toOp = σ.toOp :=
    CFC.sqrt_mul_sqrt_self σ.toOp (ha := (posSemidefOp_implies_mathlib σ).nonneg)
  calc
    (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp) *
        (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp)†
        = (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp) *
            (CFC.sqrt σ.toOp * CFC.sqrt ρ.toOp) := by
            rw [conjTranspose_mul, hρ_sqrt, hσ_sqrt]
    _ = CFC.sqrt ρ.toOp * (CFC.sqrt σ.toOp * CFC.sqrt σ.toOp) *
            CFC.sqrt ρ.toOp := by
            simp only [Matrix.mul_assoc]
    _ = CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp := by
            rw [hσ_mul]

/-- Pairing the canonical PSD same-ancilla purification of `ρ` with
`ketBOfOp σ U` gives the corresponding square-root trace expression. -/
lemma sameAncillaPurificationKetOfOp_dag_mul_ketBOfOp_eq_trace
    {m : ℕ} (ρ σ : PosSemidefOp m) (U : UnitaryOp m) :
    (sameAncillaPurificationKetOfOp ρ.toOp).dag * (ketBOfOp σ U) =
      (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp * U.toOp).trace := by
  set R : Op m := CFC.sqrt ρ.toOp with hR
  set S : Op m := CFC.sqrt σ.toOp * U.toOp with hS
  set AR : Op (m * m) := Op.tensor R (1 : Op m) with hARdef
  set AS : Op (m * m) := Op.tensor S (1 : Op m) with hASdef
  set Ω  : Ket (m * m) := InfoTheory.DeFinetti.maxEntangledKet m with hΩ
  set Ωop : Op (m * m) := InfoTheory.DeFinetti.maxEntangledOp m with hΩop
  have hψρ : sameAncillaPurificationKetOfOp ρ.toOp = AR * Ω := rfl
  have hketB : ketBOfOp σ U = AS * Ω := rfl
  have hR_herm : R† = R :=
    Math.SpectralTheory.cfc_sqrt_conjTranspose_eq ρ.toOp
  have hAR_herm : AR† = AR := by
    rw [hARdef, Op.tensor_conjTranspose, hR_herm, conjTranspose_one]
  have hstep1 :
      (sameAncillaPurificationKetOfOp ρ.toOp).dag * (ketBOfOp σ U) =
        (((ketBOfOp σ U) * (sameAncillaPurificationKetOfOp ρ.toOp).dag) *
            (1 : Op (m * m))).trace := by
    have htrace := trace_cross_ketbra_mul
      (ψ := ketBOfOp σ U) (φ := sameAncillaPurificationKetOfOp ρ.toOp)
      (A := (1 : Op (m * m)))
    rw [bra_mul_one] at htrace
    exact htrace.symm
  have hcross :
      (ketBOfOp σ U) * (sameAncillaPurificationKetOfOp ρ.toOp).dag =
        AS * Ωop * AR† := by
    have hdagψρ : (sameAncillaPurificationKetOfOp ρ.toOp).dag = Ω.dag * AR† := by
      rw [hψρ, dag_op_mul_ket]
    rw [hketB, hdagψρ]
    calc (AS * Ω) * (Ω.dag * AR†)
        = AS * (Ω * Ω.dag) * AR† := by
            rw [op_mul_ketbra, ketbra_mul_op]
      _ = AS * Ωop * AR† := by rw [← InfoTheory.DeFinetti.maxEntangledOp_eq_ketbra]
  rw [hstep1, hcross, Matrix.mul_one, hAR_herm]
  have hcycle :
      (AS * Ωop * AR).trace = (Ωop * Op.tensor (R * S) (1 : Op m)).trace := by
    calc (AS * Ωop * AR).trace
        = (AR * (AS * Ωop)).trace := by rw [Matrix.trace_mul_comm]
      _ = (AR * AS * Ωop).trace := by rw [Matrix.mul_assoc]
      _ = (Op.tensor (R * S) (1 : Op m) * Ωop).trace := by
            rw [hARdef, hASdef, Op.tensor_mul, Matrix.mul_one]
      _ = (Ωop * Op.tensor (R * S) (1 : Op m)).trace := by
            rw [Matrix.trace_mul_comm]
  rw [hcycle, hΩop, InfoTheory.DeFinetti.trace_maxEntangled_mul_tensor_one]
  rw [hR, hS, ← Matrix.mul_assoc]

/-- Outer product expansion of `ketB`. -/
lemma ketB_outer {m : ℕ} (σ' : DensityOp m) (U : UnitaryOp m) :
    (ketB σ' U) * (ketB σ' U).dag =
      Op.tensor (CFC.sqrt σ'.toOp * U.toOp) (1 : Op m) *
        InfoTheory.DeFinetti.maxEntangledOp m *
        (Op.tensor (CFC.sqrt σ'.toOp * U.toOp) (1 : Op m))† := by
  simpa [ketB, ketBOfOp] using ketBOfOp_outer σ'.toPosSemidefOp U

/-- The Strategy-A' ket's reduced state on the system factor is `σ'.toOp`. -/
lemma ketB_partialTraceB {m : ℕ} (σ' : DensityOp m) (U : UnitaryOp m) :
    partialTraceB ((ketB σ' U) * (ketB σ' U).dag) = σ'.toOp := by
  simpa [ketB, ketBOfOp] using ketBOfOp_partialTraceB σ'.toPosSemidefOp U

/-- `ketB` is a unit vector. -/
lemma ketB_normalized {m : ℕ} [NeZero m] (σ' : DensityOp m) (U : UnitaryOp m) :
    (ketB σ' U).dag * (ketB σ' U) = 1 := by
  calc
    (ketB σ' U).dag * (ketB σ' U) = σ'.toOp.trace := by
      simpa [ketB, ketBOfOp] using ketBOfOp_norm σ'.toPosSemidefOp U
    _ = 1 := σ'.trace_one

/-- Overlap identity: pairing the canonical purification ket of `ρ'` with
`ketB σ' U` yields the scalar trace `Tr(√ρ' · √σ' · U)`. -/
lemma sameAncillaPurificationKet_dag_mul_ketB_eq_trace
    {m : ℕ} (ρ' σ' : DensityOp m) (U : UnitaryOp m) :
    (sameAncillaPurificationKet ρ').dag * (ketB σ' U) =
      (CFC.sqrt ρ'.toOp * CFC.sqrt σ'.toOp * U.toOp).trace := by
  simpa [sameAncillaPurificationKet, ketB, ketBOfOp] using
    sameAncillaPurificationKetOfOp_dag_mul_ketBOfOp_eq_trace
      ρ'.toPosSemidefOp σ'.toPosSemidefOp U

/-- The real part of `ψρ'.dag * ketB` is the Uhlmann fidelity, when `U`
is the Uhlmann witness of
`sameAncillaPurificationKet_exists_tensorUnitary_overlap_re_eq_trace_cfcSqrt_sandwich`
applied to the pair `(ρ', σ')`. -/
lemma ketB_re_overlap_of_witness
    {m : ℕ} [NeZero m] (ρ' σ' : DensityOp m) (U : UnitaryOp m)
    (hU : ((sameAncillaPurificationKet σ').dag *
              (Op.tensor U.toOp (1 : Op m)) *
              sameAncillaPurificationKet ρ').re =
          (Matrix.trace (CFC.sqrt
            (CFC.sqrt ρ'.toOp * σ'.toOp * CFC.sqrt ρ'.toOp))).re) :
    ((sameAncillaPurificationKet ρ').dag * (ketB σ' U) : ℂ).re =
      Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp := by
  have hwit :
      (CFC.sqrt σ'.toOp * U.toOp * CFC.sqrt ρ'.toOp).trace.re =
        (CFC.sqrt (CFC.sqrt ρ'.toOp * σ'.toOp * CFC.sqrt ρ'.toOp)).trace.re := by
    have hleft := sameAncillaPurificationKet_left_mul_eq_trace ρ' σ' U.toOp
    have hU' := hU
    rw [hleft] at hU'
    exact hU'
  have hoverlap := sameAncillaPurificationKet_dag_mul_ketB_eq_trace ρ' σ' U
  have hcycle :
      (CFC.sqrt ρ'.toOp * CFC.sqrt σ'.toOp * U.toOp).trace =
        (CFC.sqrt σ'.toOp * U.toOp * CFC.sqrt ρ'.toOp).trace := by
    rw [show CFC.sqrt ρ'.toOp * CFC.sqrt σ'.toOp * U.toOp =
          CFC.sqrt ρ'.toOp * (CFC.sqrt σ'.toOp * U.toOp) by
        rw [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
  rw [hoverlap, hcycle, hwit]
  change (CFC.sqrt (CFC.sqrt ρ'.toOp * σ'.toOp * CFC.sqrt ρ'.toOp)).trace.re =
    Quantum.Metrics.fidelity ρ'.toPosSemidefOp σ'.toPosSemidefOp
  rfl

/-- Canonical same-ancilla Uhlmann achievability for positive semidefinite
operators, with the target branch represented by `ketBOfOp`.

The supplied unitary is the finite-dimensional polar witness that aligns the
real overlap with `Quantum.Metrics.fidelity ρ σ`. -/
theorem exists_ketBOfOp_unitary_overlap_re_eq_fidelity
    {m : ℕ} [NeZero m] (ρ σ : PosSemidefOp m) :
    ∃ U : UnitaryOp m,
      partialTraceB ((ketBOfOp σ U) * (ketBOfOp σ U).dag) = σ.toOp ∧
      ((sameAncillaPurificationKetOfOp ρ.toOp).dag * (ketBOfOp σ U) : ℂ).re =
        Quantum.Metrics.fidelity ρ σ := by
  let X : Op m := CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp
  obtain ⟨U, hU⟩ :=
    Quantum.Metrics.PolarUnitary.exists_unitary_trace_mul_eq_trace_cfcSqrt_mul_conjTranspose X
  refine ⟨U, ketBOfOp_partialTraceB σ U, ?_⟩
  have hXX :
      X * X.conjTranspose =
        CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp := by
    simpa [X] using cfc_sqrt_mul_cfc_sqrt_mul_conjTranspose ρ σ
  have hpolar :
      (U.toOp * (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp)).trace =
        (CFC.sqrt (CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp)).trace := by
    have hU' := hU
    rw [hXX] at hU'
    simpa [X] using hU'
  have hoverlap := sameAncillaPurificationKetOfOp_dag_mul_ketBOfOp_eq_trace ρ σ U
  have hcycle :
      (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp * U.toOp).trace =
        (U.toOp * (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp)).trace := by
    rw [Matrix.trace_mul_comm]
  calc
    ((sameAncillaPurificationKetOfOp ρ.toOp).dag * (ketBOfOp σ U) : ℂ).re
        = (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp * U.toOp).trace.re := by
            exact congrArg Complex.re hoverlap
    _ = (U.toOp * (CFC.sqrt ρ.toOp * CFC.sqrt σ.toOp)).trace.re := by
            rw [hcycle]
    _ = (CFC.sqrt (CFC.sqrt ρ.toOp * σ.toOp * CFC.sqrt ρ.toOp)).trace.re := by
            rw [hpolar]
    _ = Quantum.Metrics.fidelity ρ σ := rfl

/-- Canonical same-ancilla Uhlmann achievability for positive semidefinite
operators, stated directly as an existential target live branch. -/
theorem exists_sameAncillaPurificationKetOfOp_overlap_re_eq_fidelity
    {m : ℕ} [NeZero m] (ρ σ : PosSemidefOp m) :
    ∃ φ : Ket (m * m),
      partialTraceB (φ * φ.dag) = σ.toOp ∧
      ((sameAncillaPurificationKetOfOp ρ.toOp).dag * φ : ℂ).re =
        Quantum.Metrics.fidelity ρ σ := by
  obtain ⟨U, hpur, hoverlap⟩ :=
    exists_ketBOfOp_unitary_overlap_re_eq_fidelity ρ σ
  exact ⟨ketBOfOp σ U, hpur, hoverlap⟩

end Quantum.Metrics.UhlmannWitness

end -- noncomputable section
