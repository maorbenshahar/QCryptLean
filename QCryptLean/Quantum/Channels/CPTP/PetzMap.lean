import QCryptLean.Quantum.Channels.CPTP.KrausAdjoint
import QCryptLean.Quantum.Operators.InverseSqrtSandwichIff

/-!
# The Petz transpose (recovery) map of a finite-dimensional channel

Let `Λ : L(ℂⁿ) → L(ℂᵐ)` be a channel with Kraus operators `Kₖ` and let `ρ` be a
reference operator on the **input** space with image `σ = Λ(ρ)`.  The *Petz transpose
map* (also called the transpose channel, or the Petz recovery map) is the map back
from the output space to the input space

`Λ̂(Y) = ρ^{1/2} · Λ*(σ^{-1/2} Y σ^{-1/2}) · ρ^{1/2}`,

where `Λ*` is the Hilbert–Schmidt adjoint (`Quantum.Channels.krausAdjoint`).  This is
verbatim eq. (8) of
[Hayden–Jozsa–Petz–Winter, arXiv:quant-ph/0304007v2](https://arxiv.org/pdf/quant-ph/0304007),
Section IV:

> on the support of `Tσ`, `T̂` can be given explicitly by the formula
> `T̂α = σ^{1/2} T*((Tσ)^{-1/2} α (Tσ)^{-1/2}) σ^{1/2}`,
> with the adjoint map `T*` of `T`: `T*(X) = ∑ᵢ Aᵢ* X Aᵢ`, if `T(α) = ∑ᵢ Aᵢ α Aᵢ*`.

(HJPW write `σ` for the reference on the input space; here that is `ρ`, and `σ` is its
image `Λ(ρ)`.)

## Support convention

HJPW give the formula *on the support of* `Λ(ρ)`.  This file formalizes the
**nonsingular** branch: `σ` is assumed positive definite, so `σ^{-1/2}` is the honest
inverse square root `Matrix.PosDef.inverseSqrt` and the map is defined on all of
`L(ℂᵐ)`.  For a singular `Λ(ρ)` the formula only defines a map on the support of
`Λ(ρ)`; extending it to the ambient output space is a genuine additional choice and
the extension is **not** trace preserving in general, so nothing here asserts it.

## Main definitions

* `Quantum.Channels.petzKraus` — the Kraus family `ρ^{1/2} Kₖᴴ σ^{-1/2}` of the Petz map.
* `Quantum.Channels.petzMap` — the Petz transpose map as a linear map `Op m →ₗ[ℂ] Op n`.

## Main statements

* `Quantum.Channels.petzMap_apply` — HJPW eq. (8) in the stated form.
* `Quantum.Channels.petzMap_posSemidef`, `Quantum.Channels.petzMap_isHermitian` —
  positivity, for an *arbitrary* reference (no relation between `ρ` and `σ`).
* `Quantum.Channels.petzMap_isCompletelyPositive` — genuine complete positivity, again
  for an arbitrary reference: the Kraus operators do not depend on the input.
* `Quantum.Channels.petzKraus_completeness`,
  `Quantum.Channels.petzMap_isTracePreserving`,
  `Quantum.Channels.petzMap_isCPTP` — under the marginal hypothesis `Λ(ρ) = σ` (and
  `ρ` positive semidefinite) the Petz map is a channel.  The marginal hypothesis is
  load-bearing: without it trace preservation fails
  (`Quantum.Channels.not_isTracePreserving_petzMap_zero_reference`).
* `Quantum.Channels.petzMap_reference` — `Λ̂(σ) = ρ` for a trace-preserving `Λ`, and
  `Quantum.Channels.petzMap_apply_krausMapFintype` — HJPW's `T̂ T ρ = ρ`.

## What is *not* claimed

The Petz map is not a right inverse of the channel: `Λ ∘ Λ̂ ≠ id` in general.  A
compiled counterexample for the partial-trace channel is
`Quantum.Channels.petzTranspose_not_marginal_exact` in `PetzMarginalTransport.lean`.
HJPW Theorem 3 is an equality condition
for the *relative entropy*; no fidelity-saturation statement is derived here.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Channels

variable {n m : ℕ} {κ : Type*} [Fintype κ]

/-! ## The Kraus family of the Petz map -/

/-- The Kraus family of the Petz transpose map: `ρ^{1/2} · Kₖᴴ · σ^{-1/2}`.

The operators depend only on the reference `ρ` and on `σ`, **not** on the input, which
is what makes `petzMap` a fixed-reference completely positive map. -/
def petzKraus (K : κ → Matrix (Fin m) (Fin n) ℂ) (ρ : Op n) {σ : Op m}
    (hσ : σ.PosDef) : κ → Matrix (Fin n) (Fin m) ℂ :=
  fun k => CFC.sqrt ρ * (K k)ᴴ * hσ.inverseSqrt

/-- The **Petz transpose map** `Λ̂` of the Kraus channel `Λ` of `K` with respect to the
reference `ρ` on the input space and the positive-definite `σ` on the output space.

See `petzMap_apply` for HJPW eq. (8). -/
def petzMap (K : κ → Matrix (Fin m) (Fin n) ℂ) (ρ : Op n) {σ : Op m}
    (hσ : σ.PosDef) : Op m →ₗ[ℂ] Op n :=
  krausMapFintype (petzKraus K ρ hσ)

omit [Fintype κ] in
lemma petzKraus_conjTranspose (K : κ → Matrix (Fin m) (Fin n) ℂ) (ρ : Op n) {σ : Op m}
    (hσ : σ.PosDef) (k : κ) :
    (petzKraus K ρ hσ k)ᴴ = hσ.inverseSqrt * K k * CFC.sqrt ρ := by
  rw [petzKraus, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hσ.inverseSqrt_isHermitian.eq,
    ((CFC.sqrt_nonneg ρ).posSemidef.isHermitian).eq, Matrix.mul_assoc]

/-- **HJPW eq. (8)**: `Λ̂(Y) = ρ^{1/2} · Λ*(σ^{-1/2} Y σ^{-1/2}) · ρ^{1/2}`. -/
theorem petzMap_apply (K : κ → Matrix (Fin m) (Fin n) ℂ) (ρ : Op n) {σ : Op m}
    (hσ : σ.PosDef) (Y : Op m) :
    petzMap K ρ hσ Y =
      CFC.sqrt ρ * krausAdjoint K (hσ.inverseSqrt * Y * hσ.inverseSqrt) * CFC.sqrt ρ := by
  change (∑ k, petzKraus K ρ hσ k * Y * (petzKraus K ρ hσ k)ᴴ) = _
  rw [krausAdjoint_apply, Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [petzKraus_conjTranspose, petzKraus]
  simp only [Matrix.mul_assoc]

/-! ## Positivity — no relation between `ρ` and `σ` is needed -/

/-- The Petz map preserves positive semidefiniteness, for an arbitrary reference. -/
lemma petzMap_posSemidef (K : κ → Matrix (Fin m) (Fin n) ℂ) (ρ : Op n) {σ : Op m}
    (hσ : σ.PosDef) {Y : Op m} (hY : Y.PosSemidef) : (petzMap K ρ hσ Y).PosSemidef :=
  krausMapFintype_posSemidef _ hY

/-- The Petz map preserves Hermiticity, for an arbitrary reference. -/
lemma petzMap_isHermitian (K : κ → Matrix (Fin m) (Fin n) ℂ) (ρ : Op n) {σ : Op m}
    (hσ : σ.PosDef) {Y : Op m} (hY : Y.IsHermitian) : (petzMap K ρ hσ Y).IsHermitian :=
  krausMapFintype_isHermitian _ hY

/-- **The Petz map is completely positive for an arbitrary reference.**

This is a genuine complete-positivity statement, not merely PSD preservation: the
`petzKraus` operators are independent of the input, so `petzMap` is a Kraus map and
`krausMapFintype_isCompletelyPositive` applies. -/
theorem petzMap_isCompletelyPositive [NeZero n] [NeZero m]
    (K : κ → Matrix (Fin m) (Fin n) ℂ) (ρ : Op n) {σ : Op m} (hσ : σ.PosDef) :
    IsCompletelyPositive ⇑(petzMap K ρ hσ) :=
  krausMapFintype_isCompletelyPositive _

/-! ## Trace preservation — the marginal hypothesis -/

/-- **Kraus completeness of the Petz family.**  The two hypotheses are exactly
`ρ ⪰ 0` (so that `ρ^{1/2} ρ^{1/2} = ρ`) and the marginal identity `Λ(ρ) = σ`. -/
theorem petzKraus_completeness {K : κ → Matrix (Fin m) (Fin n) ℂ} {ρ : Op n} {σ : Op m}
    (hσ : σ.PosDef) (hρ : ρ.PosSemidef) (hmarg : krausMapFintype K ρ = σ) :
    ∑ k, (petzKraus K ρ hσ k)ᴴ * petzKraus K ρ hσ k = 1 := by
  have hstep : ∀ k : κ, (petzKraus K ρ hσ k)ᴴ * petzKraus K ρ hσ k
      = hσ.inverseSqrt * (K k * ρ * (K k)ᴴ) * hσ.inverseSqrt := by
    intro k
    rw [petzKraus_conjTranspose, petzKraus]
    have hsq : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
    calc hσ.inverseSqrt * K k * CFC.sqrt ρ * (CFC.sqrt ρ * (K k)ᴴ * hσ.inverseSqrt)
        = hσ.inverseSqrt * K k * (CFC.sqrt ρ * CFC.sqrt ρ) * (K k)ᴴ * hσ.inverseSqrt := by
          simp only [Matrix.mul_assoc]
      _ = hσ.inverseSqrt * (K k * ρ * (K k)ᴴ) * hσ.inverseSqrt := by
          rw [hsq]; simp only [Matrix.mul_assoc]
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  have hsum : ∑ k : κ, hσ.inverseSqrt * (K k * ρ * (K k)ᴴ) * hσ.inverseSqrt
      = hσ.inverseSqrt * (∑ k : κ, K k * ρ * (K k)ᴴ) * hσ.inverseSqrt := by
    rw [Matrix.mul_sum, Finset.sum_mul]
  rw [hsum]
  change hσ.inverseSqrt * krausMapFintype K ρ * hσ.inverseSqrt = 1
  rw [hmarg, hσ.inverseSqrt_sandwich_eq_one]

/-- The Petz map is trace preserving under the marginal hypothesis. -/
theorem petzMap_isTracePreserving [NeZero n] [NeZero m]
    {K : κ → Matrix (Fin m) (Fin n) ℂ} {ρ : Op n} {σ : Op m}
    (hσ : σ.PosDef) (hρ : ρ.PosSemidef) (hmarg : krausMapFintype K ρ = σ) :
    IsTracePreserving ⇑(petzMap K ρ hσ) :=
  (krausMapFintype_isCPTP _ (petzKraus_completeness hσ hρ hmarg)).2.2

/-- **The Petz transpose map of a channel is a channel.** -/
theorem petzMap_isCPTP [NeZero n] [NeZero m]
    {K : κ → Matrix (Fin m) (Fin n) ℂ} {ρ : Op n} {σ : Op m}
    (hσ : σ.PosDef) (hρ : ρ.PosSemidef) (hmarg : krausMapFintype K ρ = σ) :
    IsCPTP ⇑(petzMap K ρ hσ) :=
  krausMapFintype_isCPTP _ (petzKraus_completeness hσ hρ hmarg)

/-! ## Reference recovery -/

/-- **Reference recovery.** For a trace-preserving `Λ` and a positive-semidefinite
reference `ρ`, the Petz map sends `σ` back to `ρ`:  `Λ̂(σ) = ρ`.

Note that no relation between `ρ` and `σ` is used: unitality of `Λ*` collapses the
whole `σ`-dependence.  Combined with `hmarg` this is HJPW's `T̂ T ρ = ρ`, see
`petzMap_apply_krausMapFintype`. -/
theorem petzMap_reference {K : κ → Matrix (Fin m) (Fin n) ℂ} {ρ : Op n} {σ : Op m}
    (hσ : σ.PosDef) (hρ : ρ.PosSemidef) (hK : ∑ k, (K k)ᴴ * K k = 1) :
    petzMap K ρ hσ σ = ρ := by
  rw [petzMap_apply, hσ.inverseSqrt_sandwich_eq_one, krausAdjoint_one_of_complete hK,
    Matrix.mul_one, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]

/-- **HJPW `T̂ T ρ = ρ`**: the Petz map recovers the reference from its own image. -/
theorem petzMap_apply_krausMapFintype {K : κ → Matrix (Fin m) (Fin n) ℂ} {ρ : Op n}
    {σ : Op m} (hσ : σ.PosDef) (hρ : ρ.PosSemidef) (hK : ∑ k, (K k)ᴴ * K k = 1)
    (hmarg : krausMapFintype K ρ = σ) :
    petzMap K ρ hσ (krausMapFintype K ρ) = ρ := by
  rw [hmarg, petzMap_reference hσ hρ hK]

/-! ## The marginal hypothesis is load-bearing -/

/-- **Trace preservation genuinely needs the marginal hypothesis.**

With a zero reference the Petz map is the zero map, which does not preserve the trace.
This is the honest control for `petzMap_isTracePreserving`: complete positivity
survives an arbitrary reference, trace preservation does not. -/
theorem not_isTracePreserving_petzMap_zero_reference :
    ¬ IsTracePreserving
      ⇑(petzMap (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (0 : Op 1)
        (Matrix.PosDef.one (n := Fin 1))) := by
  intro htp
  have hzero : petzMap (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (0 : Op 1)
      (Matrix.PosDef.one (n := Fin 1)) 1 = 0 := by
    rw [petzMap_apply, CFC.sqrt_zero, Matrix.zero_mul, Matrix.zero_mul]
  have h := htp 1
  rw [hzero, Matrix.trace_zero, Matrix.trace_one] at h
  simp at h

end Quantum.Channels

end -- noncomputable section
