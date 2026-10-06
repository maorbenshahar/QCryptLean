import QCryptLean.Quantum.Operators.Types
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin

/-!
# Cumulative spectral resolution from a sorted orthogonal idempotent family

This helper module isolates the purely algebraic / combinatorial content of
Renner's cumulative spectral resolution used in `IID.lean`.

Given a real eigenvalue tuple `lam : Fin d → ℝ` and an orthogonal family of
Hermitian idempotents `P : Fin d → Op d` with `M = ∑ z, lam z • P z`, we build:

* the cumulative projectors `cumProj P z = ∑_{z ≤ z'} P z'`,
* Renner's increments `betaIncr lam z = lam z - lam (z-1)` (with `lam (-1) = 0`),

and prove the seven cumulative-resolution conjuncts (nonnegativity of `β`
needs `lam` nondecreasing, achieved upstream by sorting the spectrum):

* `betaIncr_nonneg`               — `0 ≤ β z`            (needs `Monotone lam`),
* `cumProj`-definition            — `B z = ∑_{z ≤ z'} P z'`,
* `cumProj_idem`                  — `B z` idempotent,
* `cumProj_conjTranspose`         — `B z` Hermitian,
* `cumProj_nesting`               — `z ≤ z' → B z' B z = B z'`,
* `sum_beta_cumProj`              — `M = ∑ z, β z • B z` (Abel summation),
* `sum_filter_le_betaIncr`        — `lam z = ∑_{z' ≤ z} β z'` (telescoping).
-/

open Quantum.Operators Matrix

namespace InfoTheory.SmoothMinEntropy.IIDAEPCumulative

variable {d : ℕ}

/-- Real tuple shifted to `Fin (d+1)` by prepending `0`. -/
noncomputable def lamShift (lam : Fin d → ℝ) : Fin (d + 1) → ℝ := Fin.cases 0 lam

@[simp] lemma lamShift_zero (lam : Fin d → ℝ) : lamShift lam 0 = 0 := by
  simp [lamShift]

@[simp] lemma lamShift_succ (lam : Fin d → ℝ) (z : Fin d) :
    lamShift lam z.succ = lam z := by
  simp [lamShift]

/-- Renner's spectral increment `β z = lam z - lam (z-1)`, with the convention
`lam (-1) = 0` so that `β` of the minimal index is `lam` itself. -/
noncomputable def betaIncr (lam : Fin d → ℝ) (z : Fin d) : ℝ :=
  lamShift lam z.succ - lamShift lam z.castSucc

/-- Cumulative projector `B z = ∑_{z ≤ z'} P z'`. -/
noncomputable def cumProj (P : Fin d → Op d) (z : Fin d) : Op d :=
  ∑ z' ∈ Finset.univ.filter (fun z' => z ≤ z'), P z'

/-- For a nondecreasing nonnegative tuple, the increments are nonnegative. -/
lemma betaIncr_nonneg (lam : Fin d → ℝ) (hmono : Monotone lam)
    (hnonneg : ∀ z, 0 ≤ lam z) (z : Fin d) : 0 ≤ betaIncr lam z := by
  unfold betaIncr
  rw [lamShift_succ]
  have hle : lamShift lam z.castSucc ≤ lam z := by
    rcases Fin.eq_zero_or_eq_succ z.castSucc with h | ⟨w, hw⟩
    · rw [h, lamShift_zero]; exact hnonneg z
    · rw [hw, lamShift_succ]
      apply hmono
      have hval := congrArg Fin.val hw
      simp only [Fin.val_castSucc, Fin.val_succ] at hval
      rw [Fin.le_def]; omega
  linarith

/-- The shifted tuple read as a total `ℕ`-indexed function (extended by `0`). -/
noncomputable def lamNat (lam : Fin d → ℝ) (j : ℕ) : ℝ :=
  if h : j < d + 1 then lamShift lam ⟨j, h⟩ else 0

lemma lamNat_succ (lam : Fin d → ℝ) (z : Fin d) :
    lamNat lam (z.val + 1) = lam z := by
  unfold lamNat
  rw [dite_eq_left (by omega : z.val + 1 < d + 1)]
  have : (⟨z.val + 1, by omega⟩ : Fin (d + 1)) = z.succ := by apply Fin.ext; simp [Fin.val_succ]
  rw [this, lamShift_succ]

lemma lamNat_castSucc (lam : Fin d → ℝ) (z : Fin d) :
    lamNat lam z.val = lamShift lam z.castSucc := by
  unfold lamNat
  rw [dite_eq_left (by omega : z.val < d + 1)]
  have : (⟨z.val, by omega⟩ : Fin (d + 1)) = z.castSucc := by apply Fin.ext; simp [Fin.val_castSucc]
  rw [this]

lemma lamNat_zero (lam : Fin d → ℝ) : lamNat lam 0 = 0 := by
  unfold lamNat
  rw [dite_eq_left (by omega : (0 : ℕ) < d + 1)]
  have : (⟨0, by omega⟩ : Fin (d + 1)) = 0 := by apply Fin.ext; simp
  rw [this, lamShift_zero]

/-- Telescoping: `lam z = ∑_{z' ≤ z} β z'`. -/
lemma sum_filter_le_betaIncr (lam : Fin d → ℝ) (z : Fin d) :
    (Finset.univ.filter (fun z' => z' ≤ z)).sum (fun z' => betaIncr lam z') = lam z := by
  have hset : Finset.univ.filter (fun z' => z' ≤ z) = Finset.Iic z := by
    ext x; simp [Finset.mem_Iic]
  have hbeta : ∀ z' : Fin d, betaIncr lam z' = lamNat lam (z'.val + 1) - lamNat lam z'.val := by
    intro z'
    rw [lamNat_succ, lamNat_castSucc, betaIncr, lamShift_succ]
  rw [hset, Finset.sum_congr rfl (fun z' _ => hbeta z')]
  -- Reindex the `Finset.Iic z` sum (over `Fin d`) to a `Finset.range` sum.
  have reindex : (Finset.Iic z).sum (fun z' => lamNat lam (z'.val + 1) - lamNat lam z'.val)
      = ∑ j ∈ Finset.range (z.val + 1), (lamNat lam (j + 1) - lamNat lam j) := by
    apply Finset.sum_bij (fun (z' : Fin d) _ => z'.val)
    · intro a ha
      rw [Finset.mem_Iic] at ha
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le ha
    · intro a₁ _ a₂ _ h; exact Fin.ext h
    · intro b hb
      rw [Finset.mem_range] at hb
      exact ⟨⟨b, by omega⟩, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hb), rfl⟩
    · intro a _; rfl
  rw [reindex, Finset.sum_range_sub (lamNat lam) (z.val + 1), lamNat_succ, lamNat_zero, sub_zero]

/-- The cumulative projector is Hermitian when the increments are. -/
lemma cumProj_conjTranspose (P : Fin d → Op d)
    (herm : ∀ z, (P z)ᴴ = P z) (z : Fin d) :
    (cumProj P z)ᴴ = cumProj P z := by
  unfold cumProj
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => herm i)

/-- The cumulative projector is idempotent for an orthogonal idempotent family. -/
lemma cumProj_idem (P : Fin d → Op d)
    (idem : ∀ z, P z * P z = P z)
    (orth : ∀ z z', z ≠ z' → P z * P z' = 0) (z : Fin d) :
    cumProj P z * cumProj P z = cumProj P z := by
  unfold cumProj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem a ha
    (fun b _ hba => orth a b (Ne.symm hba))]
  exact idem a

/-- Nesting of cumulative projectors: `z ≤ z' → B z' B z = B z'`. -/
lemma cumProj_nesting (P : Fin d → Op d)
    (idem : ∀ z, P z * P z = P z)
    (orth : ∀ z z', z ≠ z' → P z * P z' = 0)
    {z z' : Fin d} (hzz : z ≤ z') :
    cumProj P z' * cumProj P z = cumProj P z' := by
  unfold cumProj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_filter] at ha
  have hmem : a ∈ Finset.univ.filter (fun b => z ≤ b) := by
    rw [Finset.mem_filter]; exact ⟨ha.1, le_trans hzz ha.2⟩
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem a hmem
    (fun b _ hba => orth a b (Ne.symm hba))]
  exact idem a

/-- Abel summation: `M = ∑ z, β z • B z`. -/
lemma sum_beta_cumProj (P : Fin d → Op d) (lam : Fin d → ℝ) (M : Op d)
    (hM : M = ∑ z, (lam z : ℂ) • P z) :
    M = ∑ z, (betaIncr lam z : ℂ) • cumProj P z := by
  have swap : ∑ z : Fin d, ∑ z' ∈ Finset.univ.filter (fun z' => z ≤ z'),
        ((betaIncr lam z : ℂ) • P z')
      = ∑ z' : Fin d, ∑ z ∈ Finset.univ.filter (fun z => z ≤ z'),
        ((betaIncr lam z : ℂ) • P z') := by
    apply Finset.sum_comm'
    intro z z'
    simp [Finset.mem_filter]
  have key : ∑ z, (betaIncr lam z : ℂ) • cumProj P z
      = ∑ z', (lam z' : ℂ) • P z' := by
    simp only [cumProj, Finset.smul_sum]
    rw [swap]
    apply Finset.sum_congr rfl
    intro z' _
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, sum_filter_le_betaIncr lam z']
  rw [hM]; exact key.symm

end InfoTheory.SmoothMinEntropy.IIDAEPCumulative
