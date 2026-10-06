import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Partial Trace CPTP Maps — Kraus representation and section channels

The partial-trace-over-B channel `partialTraceB : Op (n*m) → Op n` is CPTP.
We build this by exhibiting an explicit Kraus representation: the `m`
operators `K_k = 1_n ⊗ ⟨k|_B`, reindexed via `finProdFinEquiv`.

## Main definitions
- `partialTraceBKraus`: Kraus operators for tracing out the right subsystem
- `partialTraceBKrausRep`: Kraus representation of `partialTraceB`

## Main statements
- `Quantum.Channels.isCPTP_partialTraceB`: `partialTraceB` is CPTP
- `Quantum.Channels.isCPTP_of_isCompletelyPositive_partialTraceB_section`:
  a completely positive section of `partialTraceB` is CPTP
-/

namespace Quantum.Channels

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

/-- Kraus operator `K_k = 1_A ⊗ ⟨k|_B` for the partial-trace-over-B channel,
    reindexed so that the domain is `Fin (n * m)` via `finProdFinEquiv`.

    Concretely `K k i α = 1` iff `α = finProdFinEquiv (i, k)`. -/
def partialTraceBKraus (n m : ℕ) : Fin m → Matrix (Fin n) (Fin (n * m)) ℂ :=
  fun k => Matrix.of fun i α => if α = finProdFinEquiv (i, k) then (1 : ℂ) else 0

/-- Entry of `(K_k)† * K_k` at `(α, β)`. -/
private lemma partialTraceBKraus_adj_mul_apply
    {n m : ℕ} (k : Fin m) (α β : Fin (n * m)) :
    ((partialTraceBKraus n m k)ᴴ * partialTraceBKraus n m k) α β =
      ∑ i : Fin n, (if α = finProdFinEquiv (i, k) ∧ β = finProdFinEquiv (i, k)
        then (1 : ℂ) else 0) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, partialTraceBKraus,
    Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : α = finProdFinEquiv (i, k)
  · by_cases h2 : β = finProdFinEquiv (i, k)
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

/-- Kraus completeness: `∑ k, (K_k)† K_k = 1`. -/
lemma partialTraceBKraus_completeness (n m : ℕ) [NeZero n] [NeZero m] :
    ∑ k, (partialTraceBKraus n m k)ᴴ * partialTraceBKraus n m k =
      (1 : Op (n * m)) := by
  ext α β
  rw [Matrix.sum_apply]
  simp_rw [partialTraceBKraus_adj_mul_apply]
  rw [Matrix.one_apply]
  by_cases hαβ : α = β
  · -- α = β: sum = 1
    subst hαβ
    rw [ite_eq_left rfl]
    -- Write α = finProdFinEquiv (a1, a2)
    obtain ⟨⟨a1, a2⟩, hα_eq⟩ : ∃ p : Fin n × Fin m, α = finProdFinEquiv p :=
      ⟨finProdFinEquiv.symm α, (finProdFinEquiv.apply_symm_apply α).symm⟩
    -- Collapse outer sum to k = a2
    rw [Finset.sum_eq_single a2
      (fun k _ hk => by
        apply Finset.sum_eq_zero
        intro i _
        apply ite_eq_right
        rintro ⟨hαi, _⟩
        apply hk
        have heq : finProdFinEquiv (a1, a2) = finProdFinEquiv (i, k) :=
          hα_eq.symm.trans hαi
        exact (congr_arg Prod.snd (finProdFinEquiv.injective heq)).symm)
      (fun h => absurd (Finset.mem_univ _) h)]
    -- Collapse inner sum to i = a1
    rw [Finset.sum_eq_single a1
      (fun i _ hi => by
        apply ite_eq_right
        rintro ⟨hαi, _⟩
        apply hi
        have heq : finProdFinEquiv (a1, a2) = finProdFinEquiv (i, a2) :=
          hα_eq.symm.trans hαi
        exact (congr_arg Prod.fst (finProdFinEquiv.injective heq)).symm)
      (fun h => absurd (Finset.mem_univ _) h)]
    -- now: if α = finProdFinEquiv (a1, a2) ∧ α = finProdFinEquiv (a1, a2) then 1 else 0
    rw [ite_eq_left ⟨hα_eq, hα_eq⟩]
  · rw [ite_eq_right hαβ]
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro i _
    apply ite_eq_right
    rintro ⟨h1, h2⟩
    exact hαβ (h1.trans h2.symm)

/-- The Kraus representation packaging of the partial-trace-over-B channel. -/
def partialTraceBKrausRep (n m : ℕ) [NeZero n] [NeZero m] :
    KrausRepresentation (n * m) n where
  numOps := m
  operators := partialTraceBKraus n m
  completeness := partialTraceBKraus_completeness n m

/-- Entry-level identity: `K_k * ρ * (K_k)†` at `(i, j)` equals
    `ρ (finProdFinEquiv (i,k)) (finProdFinEquiv (j,k))`. -/
private lemma partialTraceBKraus_sandwich_apply
    {n m : ℕ} (ρ : Op (n * m)) (k : Fin m) (i j : Fin n) :
    (partialTraceBKraus n m k * ρ * (partialTraceBKraus n m k)ᴴ) i j =
      ρ (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, partialTraceBKraus,
    Matrix.of_apply]
  -- Target: ∑ α, (∑ β, [β = fpfe(i,k)] * ρ β α) * star [α = fpfe(j,k)] = ρ fpfe(i,k) fpfe(j,k)
  -- Step 1: collapse inner β-sum to β = fpfe(i,k)
  have hinner : ∀ α : Fin (n * m),
      (∑ β, (if β = finProdFinEquiv (i, k) then (1 : ℂ) else 0) * ρ β α) =
      ρ (finProdFinEquiv (i, k)) α := by
    intro α
    rw [Finset.sum_eq_single (finProdFinEquiv (i, k))
      (fun β _ hβ => by rw [ite_eq_right hβ]; ring)
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [ite_eq_left rfl]; ring
  simp_rw [hinner]
  -- Step 2: collapse outer α-sum to α = fpfe(j,k)
  rw [Finset.sum_eq_single (finProdFinEquiv (j, k))
    (fun α _ hα => by
      have hne : ¬ (α = finProdFinEquiv (j, k)) := hα
      rw [ite_eq_right hne]; simp)
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [ite_eq_left rfl]; simp

/-- The Kraus action `KrausRepresentation.applyOp` agrees with `partialTraceB`. -/
lemma partialTraceBKrausRep_applyOp_eq (n m : ℕ) [NeZero n] [NeZero m] :
    (partialTraceBKrausRep n m).applyOp = (partialTraceB : Op (n * m) → Op n) := by
  funext ρ
  ext i j
  simp only [KrausRepresentation.applyOp, partialTraceBKrausRep, partialTraceB,
    Matrix.of_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact partialTraceBKraus_sandwich_apply ρ k i j

/-- **`partialTraceB` is CPTP.** This is the partial-trace-over-B channel
    packaged as a CPTP map. Used by the data-processing inequality for
    trace distance (`traceDistance_contractive_under_partialTraceB`). -/
theorem isCPTP_partialTraceB {n m : ℕ} [NeZero n] [NeZero m] :
    IsCPTP (partialTraceB : Op (n * m) → Op n) := by
  have h := (partialTraceBKrausRep n m).is_cptp
  rw [partialTraceBKrausRep_applyOp_eq n m] at h
  exact h

/-- A completely positive map that is a section of partial trace is trace
preserving, hence CPTP. -/
lemma isCPTP_of_isCompletelyPositive_partialTraceB_section
    {dE dR : ℕ} [NeZero dE] [NeZero (dE * dR)]
    (T : Op dE →ₗ[ℂ] Op (dE * dR))
    (hcp : IsCompletelyPositive ⇑T)
    (hsec : ∀ A : Op dE, partialTraceB (T A) = A) :
    IsCPTP ⇑T := by
  refine ⟨LinearMap.isLinear T, hcp, ?_⟩
  intro A
  exact Quantum.TensorProducts.trace_eq_of_partialTraceB_eq (T A) A (hsec A)

/-- A completely positive, trace-preserving map is CPTP.

This is the Variant-B counterpart to `isCPTP_of_isCompletelyPositive_partialTraceB_section`:
instead of deriving trace preservation from a global partial-trace section, we accept
`IsTracePreserving` directly as a hypothesis. -/
lemma isCPTP_of_isCompletelyPositive_isTracePreserving
    {dE dR : ℕ} [NeZero dE] [NeZero dR] [NeZero (dE * dR)]
    (T : Op dE →ₗ[ℂ] Op (dE * dR))
    (hcp : IsCompletelyPositive ⇑T)
    (htp : IsTracePreserving ⇑T) :
    IsCPTP ⇑T :=
  ⟨LinearMap.isLinear T, hcp, htp⟩

end -- noncomputable section

end Quantum.Channels
