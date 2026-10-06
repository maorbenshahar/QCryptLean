import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import QCryptLean.Quantum.Channels.CPTP.PartialTraceCPTP

/-!
# The Hilbert–Schmidt adjoint of a finite Kraus map

If a channel is given in Kraus form `Λ(A) = ∑ₖ Kₖ A Kₖᴴ` then its Hilbert–Schmidt
adjoint is `Λ*(M) = ∑ₖ Kₖᴴ M Kₖ`, characterized by the trace pairing
`Tr(Λ*(M) · A) = Tr(M · Λ(A))`.  This is the `T*` of
[Hayden–Jozsa–Petz–Winter, arXiv:quant-ph/0304007v2](https://arxiv.org/pdf/quant-ph/0304007),
Section IV, eq. (8), and is the ingredient the Petz transpose map is built from
(`Quantum.Channels.petzMap`).

The adjoint of a channel is completely positive and **unital** (rather than trace
preserving): `Λ*(1) = ∑ₖ Kₖᴴ Kₖ = 1` is exactly the Kraus completeness relation.

## Main definitions

* `Quantum.Channels.krausAdjoint` — `Λ*` as a linear map, namely the Kraus map of the
  adjoint family `k ↦ Kₖᴴ`.

## Main statements

* `Quantum.Channels.trace_krausAdjoint_mul` — the defining trace pairing.
* `Quantum.Channels.krausAdjoint_one` — unitality is the completeness relation.
* `Quantum.Channels.krausAdjoint_posSemidef`,
  `Quantum.Channels.krausAdjoint_isCompletelyPositive` — positivity of the adjoint.
* `Quantum.Channels.krausAdjoint_partialTraceBKraus` — **the adjoint of `partialTraceB`
  is `M ↦ M ⊗ 1_R`**, with the surviving factor on the *first* (untraced) register.
* `Quantum.Channels.trace_partialTraceB_mul` — the resulting partial-trace pairing
  `Tr(Tr_R(X) · M) = Tr(X · (M ⊗ 1_R))`.

None of the statements in this file needs `NeZero` except the Choi-matrix
formulation of complete positivity.  The underlying positivity laws for
`krausMapFintype` itself (`krausMapFintype_posSemidef`,
`krausMapFintype_isHermitian`) are in `FintypeKraus.lean`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

variable {n m : ℕ} {κ : Type*} [Fintype κ]

/-! ## The adjoint map -/

/-- The **Hilbert–Schmidt adjoint** of the Kraus map of `K`:
`Λ*(M) = ∑ₖ Kₖᴴ M Kₖ`.

It is the Kraus map of the adjoint family `k ↦ Kₖᴴ`, so every `krausMapFintype`
lemma applies to it; the separate name records its role as `T*` in
HJPW eq. (8). -/
def krausAdjoint (K : κ → Matrix (Fin m) (Fin n) ℂ) : Op m →ₗ[ℂ] Op n :=
  krausMapFintype fun k => (K k)ᴴ

@[simp] lemma krausAdjoint_apply (K : κ → Matrix (Fin m) (Fin n) ℂ) (M : Op m) :
    krausAdjoint K M = ∑ k, (K k)ᴴ * M * K k := by
  change (∑ k, (K k)ᴴ * M * ((K k)ᴴ)ᴴ) = _
  simp only [Matrix.conjTranspose_conjTranspose]

/-- **The defining adjoint property**: `Tr(Λ*(M) · A) = Tr(M · Λ(A))`. -/
lemma trace_krausAdjoint_mul (K : κ → Matrix (Fin m) (Fin n) ℂ) (M : Op m) (A : Op n) :
    (krausAdjoint K M * A).trace = (M * krausMapFintype K A).trace := by
  rw [krausAdjoint_apply, Finset.sum_mul, Matrix.trace_sum]
  change _ = (M * ∑ k, K k * A * (K k)ᴴ).trace
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := Matrix.trace_mul_comm ((K k)ᴴ) (M * (K k * A))
  simp only [Matrix.mul_assoc] at h ⊢
  exact h

/-- **Unitality of the adjoint is the Kraus completeness relation.** -/
lemma krausAdjoint_one (K : κ → Matrix (Fin m) (Fin n) ℂ) :
    krausAdjoint K (1 : Op m) = ∑ k, (K k)ᴴ * K k := by
  simp only [krausAdjoint_apply, Matrix.mul_one]

/-- The adjoint of a trace-preserving Kraus map is unital. -/
lemma krausAdjoint_one_of_complete {K : κ → Matrix (Fin m) (Fin n) ℂ}
    (hK : ∑ k, (K k)ᴴ * K k = 1) : krausAdjoint K (1 : Op m) = 1 := by
  rw [krausAdjoint_one, hK]

/-- The adjoint of a Kraus map preserves positive semidefiniteness. -/
lemma krausAdjoint_posSemidef (K : κ → Matrix (Fin m) (Fin n) ℂ)
    {M : Op m} (hM : M.PosSemidef) : (krausAdjoint K M).PosSemidef :=
  krausMapFintype_posSemidef _ hM

/-- The adjoint of a Kraus map preserves Hermiticity. -/
lemma krausAdjoint_isHermitian (K : κ → Matrix (Fin m) (Fin n) ℂ)
    {M : Op m} (hM : M.IsHermitian) : (krausAdjoint K M).IsHermitian :=
  krausMapFintype_isHermitian _ hM

/-- The adjoint of a Kraus map is completely positive. -/
theorem krausAdjoint_isCompletelyPositive [NeZero n] [NeZero m]
    (K : κ → Matrix (Fin m) (Fin n) ℂ) :
    IsCompletelyPositive ⇑(krausAdjoint K) :=
  krausMapFintype_isCompletelyPositive _

/-! ## The adjoint of `partialTraceB`

`partialTraceB` traces the **second** tensor factor, and its explicit Kraus operators
are `partialTraceBKraus n m k = 1_A ⊗ ⟨k|_B`.  Its adjoint is therefore
`M ↦ M ⊗ 1_B`, with `M` on the first factor. -/

/-- The Kraus map of `partialTraceBKraus` is `partialTraceB`.

This is the `krausMapFintype`-shaped, `NeZero`-free form of
`Quantum.Channels.partialTraceBKrausRep_applyOp_eq`. -/
lemma krausMapFintype_partialTraceBKraus (n m : ℕ) :
    ⇑(krausMapFintype (partialTraceBKraus n m)) = (partialTraceB : Op (n * m) → Op n) := by
  funext X
  ext i j
  change (∑ k, partialTraceBKraus n m k * X * (partialTraceBKraus n m k)ᴴ) i j = _
  simp only [partialTraceB, Matrix.of_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, partialTraceBKraus, Matrix.of_apply]
  simp [Finset.sum_ite_eq']

/-- **The Hilbert–Schmidt adjoint of `partialTraceB` is `M ↦ M ⊗ 1_R`.**

The surviving factor sits on the *first* (untraced) register, matching
`partialTraceB`, which traces the second one.  This is HJPW's `T*` for `T = Tr_R`. -/
theorem krausAdjoint_partialTraceBKraus (M : Op n) :
    krausAdjoint (partialTraceBKraus n m) M = Op.tensor M (1 : Op m) := by
  rw [krausAdjoint_apply]
  ext α β
  obtain ⟨⟨a, b⟩, rfl⟩ : ∃ p : Fin n × Fin m, α = finProdFinEquiv p :=
    ⟨_, (finProdFinEquiv.apply_symm_apply α).symm⟩
  obtain ⟨⟨c, d⟩, rfl⟩ : ∃ p : Fin n × Fin m, β = finProdFinEquiv p :=
    ⟨_, (finProdFinEquiv.apply_symm_apply β).symm⟩
  rw [Matrix.sum_apply, Op_tensor_apply_finProd]
  simp only [Equiv.symm_apply_apply, Matrix.one_apply]
  have hentry : ∀ k : Fin m,
      ((partialTraceBKraus n m k)ᴴ * M * partialTraceBKraus n m k)
          (finProdFinEquiv (a, b)) (finProdFinEquiv (c, d))
        = if b = k ∧ d = k then M a c else 0 := by
    intro k
    simp only [Matrix.mul_apply, partialTraceBKraus, Matrix.of_apply,
      Equiv.apply_eq_iff_eq, Prod.mk.injEq]
    simp only [ite_and, mul_ite, mul_one, mul_zero]
    by_cases hd : d = k <;> by_cases hb : b = k <;>
      simp [hd, hb, Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl (fun k _ => hentry k)]
  by_cases hbd : b = d
  · subst hbd
    simp only [and_self, ite_true]
    rw [Finset.sum_ite_eq Finset.univ b (fun _ => M a c)]
    simp
  · rw [ite_eq_right hbd, mul_zero]
    exact Finset.sum_eq_zero fun k _ => ite_eq_right fun ⟨h1, h2⟩ => hbd (h1.trans h2.symm)

/-- **Partial-trace trace pairing**: `Tr(Tr_R(X) · M) = Tr(X · (M ⊗ 1_R))`. -/
theorem trace_partialTraceB_mul (X : Op (n * m)) (M : Op n) :
    (partialTraceB X * M).trace = (X * Op.tensor M (1 : Op m)).trace := by
  have h := trace_krausAdjoint_mul (partialTraceBKraus n m) M X
  rw [krausAdjoint_partialTraceBKraus, krausMapFintype_partialTraceBKraus] at h
  rw [Matrix.trace_mul_comm (partialTraceB X) M, ← h, Matrix.trace_mul_comm]

end Quantum.Channels

end -- noncomputable section
