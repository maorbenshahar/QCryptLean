import QCryptLean.InfoTheory.QuantumLHL.OffDiagonalLHL
import QCryptLean.Quantum.Operators.InverseSqrt

/-!
# General-reference (σ-weighted) leftover-hash trace-norm bound

Lean form of Regula–Tomamichel arXiv:2603.04493 Lemma 12 / Renner
quant-ph/0512258 §5.5–5.6: the seed-averaged trace-norm distance of a hashed cq
block operator from ideal, bounded via a **σ-weighted collision second moment**
against a fixed positive-definite reference `σ` (no `√dimE` max-mixed factor).

## Main declarations
- `weightedFrobeniusSq` : `‖σ^{-1/4} A σ^{-1/4}‖_F²`, the symmetric 4-2-4 weighted
  Hilbert–Schmidt square.
- `collisionQuantity` : `∑ x, weightedFrobeniusSq σ (V x)`.
- `traceNorm_le_sqrt_trace_mul_weightedFrobenius` : the σ-weighted Hölder step
  `‖A‖₁ ≤ √(Tr σ · weightedFrobeniusSq σ A)`, via the genuine 4-2-4 factorization
  `A = σ^{1/4}(σ^{-1/4} A σ^{-1/4})σ^{1/4}` (two Hilbert–Schmidt Cauchy–Schwarz steps).
- `QuantumHashFamily.IsUniversal2Star.seedAvg_traceNorm_offDiag_le_genRef` : the
  general-reference off-diagonal collision bound
  (`QuantumHashFamily.IsUniversal2Star.seedAvg_traceNorm_offDiag_le` with the
  dimension factor `n` replaced by `σ.trace.re` and the frobenius sum replaced by
  `collisionQuantity σ V`).
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.QuantumLHL

/-!
## σ-agnostic real-analysis helpers (re-stated from `OffDiagonalLHL.lean`, `private` there)
-/

/-- **Cauchy–Schwarz sqrt bound.** For nonnegative `a : ι → ℝ`,
`∑ i, √(a i) ≤ √(|ι| · ∑ i, a i)`. -/
private lemma sum_sqrt_le' {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, Real.sqrt (a i) ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, a i) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ))
    (fun i => Real.sqrt (a i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hcs
  rw [Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (ha i))] at hcs
  have hnn : 0 ≤ ∑ i, Real.sqrt (a i) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  calc ∑ i, Real.sqrt (a i)
      = Real.sqrt ((∑ i, Real.sqrt (a i)) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, a i) := Real.sqrt_le_sqrt hcs

/-- **Nested Cauchy–Schwarz sqrt bound** over a product index. -/
private lemma sum_sum_sqrt_le' {α β : Type*} [Fintype α] [Fintype β]
    (a : α → β → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    ∑ i, ∑ j, Real.sqrt (a i j)
      ≤ Real.sqrt (((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) * ∑ i, ∑ j, a i j) := by
  have h := sum_sqrt_le' (ι := α × β) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.card_prod] at h
  push_cast at h
  exact h

/-- Final algebraic cancellation: `(1/N)·√(nn·(N·Zc)·(N·(cc·Σ))) = √(nn·Zc·cc·Σ)`. -/
private lemma final_alg' (N Zc cc sV nn : ℝ) (hN : 0 < N) :
    (1 / N) * Real.sqrt (nn * (N * Zc) * (N * (cc * sV)))
      = Real.sqrt (nn * Zc * cc * sV) := by
  have hval : nn * (N * Zc) * (N * (cc * sV)) = N ^ 2 * (nn * Zc * cc * sV) := by ring
  rw [hval, Real.sqrt_mul (by positivity), Real.sqrt_sq hN.le]
  field_simp

/-!
## Definitions
-/

/-- **σ-weighted Hilbert–Schmidt square.** `= ‖σ^{-1/4} A σ^{-1/4}‖_F²`; the symmetric
4-2-4 form (NOT the one-sided `Tr[Aᴴ σ⁻¹ A]`). For `σ = 1` this is `(Aᴴ A).trace.re`. -/
noncomputable def weightedFrobeniusSq {n : ℕ} (σ A : Op n) : ℝ :=
  (((σ ^ (-1/4 : ℝ)) * A * (σ ^ (-1/4 : ℝ)))ᴴ *
    ((σ ^ (-1/4 : ℝ)) * A * (σ ^ (-1/4 : ℝ)))).trace.re

/-- **σ-weighted collision quantity** `∑ x, weightedFrobeniusSq σ (V x)`. -/
noncomputable def collisionQuantity {X : Type*} [Fintype X] {n : ℕ}
    (σ : Op n) (V : X → Op n) : ℝ := ∑ x : X, weightedFrobeniusSq σ (V x)

/-- At the reference `σ = 1` the weighted square is the plain Frobenius square. -/
@[simp] lemma weightedFrobeniusSq_one {n : ℕ} (A : Op n) :
    weightedFrobeniusSq 1 A = (Aᴴ * A).trace.re := by
  simp [weightedFrobeniusSq, CFC.one_rpow]

/-- `weightedFrobeniusSq σ A ≥ 0` (it is `(Cᴴ C).trace.re` for `C = σ^{-1/4} A σ^{-1/4}`). -/
lemma weightedFrobeniusSq_nonneg {n : ℕ} (σ A : Op n) : 0 ≤ weightedFrobeniusSq σ A := by
  rw [weightedFrobeniusSq, Quantum.Channels.trace_conjTranspose_mul_self_re]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

/-!
## the σ-weighted trace-norm Hölder step
-/

/-- **The σ-weighted Hölder step.** For positive-definite `σ` and arbitrary `A`,
`‖A‖₁ ≤ √(Tr σ · ‖σ^{-1/4} A σ^{-1/4}‖_F²)`. Proved via the genuine 4-2-4
factorization `A = σ^{1/4}·(σ^{-1/4} A σ^{-1/4})·σ^{1/4}` and two Hilbert–Schmidt
Cauchy–Schwarz applications (the polar-unitary cancels in the σ side because both
outer factors are `σ^{1/4}`). At `σ = 1` it is
`Quantum.Metrics.traceNorm_le_sqrt_dim_mul_frobenius`, by `weightedFrobeniusSq_one` and
`Tr 1 = n`. -/
theorem traceNorm_le_sqrt_trace_mul_weightedFrobenius {n : ℕ} [NeZero n]
    (σ : Op n) (hσ : σ.PosDef) (A : Op n) :
    Quantum.Metrics.traceNorm A ≤ Real.sqrt (σ.trace.re * weightedFrobeniusSq σ A) := by
  have hσ_nonneg : (0 : Op n) ≤ σ := Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef
  have hσtr_nonneg : 0 ≤ σ.trace.re := (Complex.nonneg_iff.mp hσ.posSemidef.trace_nonneg).1
  -- powers of σ
  set F : Op n := σ ^ (-1/4 : ℝ) with hF_def
  set G : Op n := σ ^ (1/4 : ℝ) with hG_def
  set Hh : Op n := σ ^ (1/2 : ℝ) with hHh_def
  have hF_psd : F.PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hG_psd : G.PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hHh_psd : Hh.PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hF_herm : Fᴴ = F := hF_psd.isHermitian.eq
  have hG_herm : Gᴴ = G := hG_psd.isHermitian.eq
  have hHh_herm : Hhᴴ = Hh := hHh_psd.isHermitian.eq
  -- the exponent laws `σ^a σ^b = σ^(a+b)`, `σ^0 = 1`, `σ^1 = σ` (`σ` is invertible)
  have hadd : ∀ a b : ℝ, σ ^ a * σ ^ b = σ ^ (a + b) := fun _ _ => (CFC.rpow_add hσ.isUnit).symm
  have hzero : σ ^ (0 : ℝ) = 1 := CFC.rpow_zero σ hσ_nonneg
  have hGF : G * F = 1 := by
    rw [hG_def, hF_def, hadd, show (1/4 + -1/4 : ℝ) = 0 by norm_num, hzero]
  have hFG : F * G = 1 := by
    rw [hF_def, hG_def, hadd, show (-1/4 + 1/4 : ℝ) = 0 by norm_num, hzero]
  have hGG : G * G = Hh := by
    rw [hG_def, hHh_def, hadd, show (1/4 + 1/4 : ℝ) = 1/2 by norm_num]
  have hHhHh : Hh * Hh = σ := by
    rw [hHh_def, hadd, show (1/2 + 1/2 : ℝ) = 1 by norm_num, CFC.rpow_one σ hσ_nonneg]
  -- the transformed operator B = σ^{-1/4} A σ^{-1/4}
  set B : Op n := F * A * F with hB_def
  have hWF : weightedFrobeniusSq σ A = (Bᴴ * B).trace.re := by
    rw [weightedFrobeniusSq, ← hF_def, ← hB_def]
  -- polar unitary for A: traceNorm A = (U · Aᴴ).trace.re
  obtain ⟨U, hU⟩ :=
    Quantum.Metrics.PolarUnitary.exists_unitary_trace_mul_eq_trace_cfcSqrt_mul_conjTranspose
      A.conjTranspose
  rw [show A.conjTranspose.conjTranspose = A from Matrix.conjTranspose_conjTranspose A] at hU
  have h_norm_eq : Quantum.Metrics.traceNorm A = (U.toOp * A.conjTranspose).trace.re := by
    rw [hU, ← Quantum.Metrics.traceNorm_eq_re_trace_cfcSqrt_conjTranspose_mul A]
  -- Aᴴ = G · Bᴴ · G
  have hBdag : Bᴴ = F * A.conjTranspose * F := by
    rw [hB_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF_herm, Matrix.mul_assoc]
  have hAdag : A.conjTranspose = G * Bᴴ * G := by
    rw [hBdag, show G * (F * A.conjTranspose * F) * G
          = (G * F) * A.conjTranspose * (F * G) from by
        simp only [Matrix.mul_assoc], hGF, hFG, Matrix.one_mul, Matrix.mul_one]
  -- P = G · U · G
  set P : Op n := G * U.toOp * G with hP_def
  -- trace rewriting: (U · Aᴴ).trace = (P · Bᴴ).trace
  have hTrace1 : (U.toOp * A.conjTranspose).trace = (P * Bᴴ).trace := by
    rw [hAdag, show U.toOp * (G * Bᴴ * G) = (U.toOp * G * Bᴴ) * G from by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm, hP_def]
    simp only [Matrix.mul_assoc]
  -- CS1: ‖(P Bᴴ).trace‖² ≤ (P Pᴴ).trace.re · (B Bᴴ).trace.re
  have hCS1 : ‖(P * Bᴴ).trace‖ ^ 2
      ≤ (P * Pᴴ).trace.re * (B * Bᴴ).trace.re := by
    have h := Quantum.Metrics.norm_trace_mul_sq_le_trace_mul_trace_conjTranspose P Bᴴ
    rwa [Matrix.conjTranspose_conjTranspose] at h
  -- (P Pᴴ).trace = (Hh U Hh Uᴴ).trace
  have hPP_eq : (P * Pᴴ).trace = (Hh * U.toOp * Hh * U.toOp.conjTranspose).trace := by
    have hPdag : Pᴴ = G * U.toOp.conjTranspose * G := by
      rw [hP_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG_herm, Matrix.mul_assoc]
    rw [hPdag, hP_def]
    rw [show G * U.toOp * G * (G * U.toOp.conjTranspose * G)
          = G * U.toOp * (G * G) * U.toOp.conjTranspose * G from by
        simp only [Matrix.mul_assoc], hGG]
    rw [Matrix.trace_mul_comm (G * U.toOp * Hh * U.toOp.conjTranspose) G,
      show G * (G * U.toOp * Hh * U.toOp.conjTranspose)
          = (G * G) * U.toOp * Hh * U.toOp.conjTranspose from by
        simp only [Matrix.mul_assoc], hGG]
  -- CS2: ‖(Hh U Hh Uᴴ).trace‖² ≤ σ.trace.re · σ.trace.re
  have hCS2 : ‖(Hh * U.toOp * Hh * U.toOp.conjTranspose).trace‖ ^ 2
      ≤ σ.trace.re * σ.trace.re := by
    have h := Quantum.Metrics.norm_trace_mul_sq_le_trace_mul_trace_conjTranspose
      Hh (U.toOp * Hh * U.toOp.conjTranspose)
    -- LHS trace pairing regroup
    rw [show Hh * (U.toOp * Hh * U.toOp.conjTranspose)
          = Hh * U.toOp * Hh * U.toOp.conjTranspose from by simp only [Matrix.mul_assoc]] at h
    -- Tr(Hh · Hhᴴ) = Tr σ
    have hA : (Hh * Hh.conjTranspose).trace.re = σ.trace.re := by
      rw [hHh_herm, hHhHh]
    -- Tr((U Hh Uᴴ)ᴴ (U Hh Uᴴ)) = Tr σ
    have hopeq : (U.toOp * Hh * U.toOp.conjTranspose)ᴴ * (U.toOp * Hh * U.toOp.conjTranspose)
        = U.toOp * σ * U.toOp.conjTranspose := by
      have e1 : (U.toOp * Hh * U.toOp.conjTranspose)ᴴ
          = U.toOp * Hh * U.toOp.conjTranspose := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, hHh_herm]
        simp only [Matrix.mul_assoc]
      rw [e1, show (U.toOp * Hh * U.toOp.conjTranspose) * (U.toOp * Hh * U.toOp.conjTranspose)
            = U.toOp * Hh * (U.toOp.conjTranspose * U.toOp) * Hh * U.toOp.conjTranspose from by
          simp only [Matrix.mul_assoc], U.unitary_left,
        show U.toOp * Hh * 1 * Hh * U.toOp.conjTranspose
            = U.toOp * (Hh * Hh) * U.toOp.conjTranspose from by
          simp only [Matrix.mul_assoc, Matrix.mul_one], hHhHh]
    have hB : ((U.toOp * Hh * U.toOp.conjTranspose).conjTranspose
        * (U.toOp * Hh * U.toOp.conjTranspose)).trace.re = σ.trace.re := by
      rw [hopeq, Matrix.trace_mul_comm, ← Matrix.mul_assoc, U.unitary_left, Matrix.one_mul]
    rw [hA, hB] at h
    exact h
  -- (P Pᴴ).trace.re ≤ σ.trace.re
  have hPP_le : (P * Pᴴ).trace.re ≤ σ.trace.re := by
    rw [hPP_eq]
    refine (Complex.re_le_norm _).trans ?_
    -- `‖·‖² ≤ (Tr σ)²` with `0 ≤ Tr σ` gives `‖·‖ ≤ Tr σ`.
    rw [← sq] at hCS2
    exact le_of_pow_le_pow_left₀ two_ne_zero hσtr_nonneg hCS2
  -- (B Bᴴ).trace.re = weightedFrobeniusSq σ A
  have hBB : (B * Bᴴ).trace.re = weightedFrobeniusSq σ A := by
    rw [hWF, Matrix.trace_mul_comm]
  -- assemble the squared bound
  have hre_sq : ((U.toOp * A.conjTranspose).trace.re) ^ 2
      ≤ ‖(U.toOp * A.conjTranspose).trace‖ ^ 2 := by
    have habs := Complex.abs_re_le_norm (U.toOp * A.conjTranspose).trace
    rw [show ((U.toOp * A.conjTranspose).trace.re) ^ 2
          = |((U.toOp * A.conjTranspose).trace.re)| ^ 2 from (sq_abs _).symm]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hfinal : Quantum.Metrics.traceNorm A ^ 2
      ≤ σ.trace.re * weightedFrobeniusSq σ A := by
    calc Quantum.Metrics.traceNorm A ^ 2
        = ((U.toOp * A.conjTranspose).trace.re) ^ 2 := by rw [h_norm_eq]
      _ ≤ ‖(U.toOp * A.conjTranspose).trace‖ ^ 2 := hre_sq
      _ = ‖(P * Bᴴ).trace‖ ^ 2 := by rw [hTrace1]
      _ ≤ (P * Pᴴ).trace.re * (B * Bᴴ).trace.re := hCS1
      _ ≤ σ.trace.re * weightedFrobeniusSq σ A := by
          rw [hBB]
          exact mul_le_mul_of_nonneg_right hPP_le (weightedFrobeniusSq_nonneg σ A)
  have htn_nonneg : 0 ≤ Quantum.Metrics.traceNorm A := by
    unfold Quantum.Metrics.traceNorm
    exact Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  calc Quantum.Metrics.traceNorm A
      = Real.sqrt (Quantum.Metrics.traceNorm A ^ 2) := (Real.sqrt_sq htn_nonneg).symm
    _ ≤ Real.sqrt (σ.trace.re * weightedFrobeniusSq σ A) := Real.sqrt_le_sqrt hfinal

/-!
## the general-reference off-diagonal bound
-/

/-- **Abstract seed-averaged σ-weighted trace-norm bound.** For an arbitrary bin
operator `W : S → Z → Op n`,
`∑ s, ∑ m, ‖W s m‖₁ ≤ √( Tr σ · (|S|·|Z|) · ∑ s, ∑ m, weightedFrobeniusSq σ (W s m) )`.
Combines the weighted Hölder bound per bin with a Cauchy–Schwarz over the `|S|·|Z|` bins. -/
private lemma seedAvg_traceNorm_le_of_weightedFrob {S Z : Type*} [Fintype S] [Fintype Z]
    {n : ℕ} [NeZero n] (σ : Op n) (hσ : σ.PosDef) (W : S → Z → Op n) :
    ∑ s : S, ∑ m : Z, Quantum.Metrics.traceNorm (W s m)
      ≤ Real.sqrt (σ.trace.re * ((Fintype.card S : ℝ) * (Fintype.card Z : ℝ))
          * ∑ s : S, ∑ m : Z, weightedFrobeniusSq σ (W s m)) := by
  have hσtr_nonneg : 0 ≤ σ.trace.re := (Complex.nonneg_iff.mp hσ.posSemidef.trace_nonneg).1
  have hwf_nonneg : ∀ s m, 0 ≤ weightedFrobeniusSq σ (W s m) :=
    fun s m => weightedFrobeniusSq_nonneg σ (W s m)
  have step1 : ∑ s : S, ∑ m : Z, Quantum.Metrics.traceNorm (W s m)
      ≤ Real.sqrt σ.trace.re *
          ∑ s : S, ∑ m : Z, Real.sqrt (weightedFrobeniusSq σ (W s m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [← Real.sqrt_mul hσtr_nonneg]
    exact traceNorm_le_sqrt_trace_mul_weightedFrobenius σ hσ (W s m)
  have step2 : ∑ s : S, ∑ m : Z, Real.sqrt (weightedFrobeniusSq σ (W s m))
      ≤ Real.sqrt (((Fintype.card S : ℝ) * (Fintype.card Z : ℝ))
          * ∑ s : S, ∑ m : Z, weightedFrobeniusSq σ (W s m)) :=
    sum_sum_sqrt_le' (fun s m => weightedFrobeniusSq σ (W s m)) hwf_nonneg
  calc ∑ s : S, ∑ m : Z, Quantum.Metrics.traceNorm (W s m)
      ≤ Real.sqrt σ.trace.re *
          ∑ s : S, ∑ m : Z, Real.sqrt (weightedFrobeniusSq σ (W s m)) := step1
    _ ≤ Real.sqrt σ.trace.re *
          Real.sqrt (((Fintype.card S : ℝ) * (Fintype.card Z : ℝ))
            * ∑ s : S, ∑ m : Z, weightedFrobeniusSq σ (W s m)) :=
        mul_le_mul_of_nonneg_left step2 (Real.sqrt_nonneg _)
    _ = Real.sqrt (σ.trace.re * ((Fintype.card S : ℝ) * (Fintype.card Z : ℝ))
          * ∑ s : S, ∑ m : Z, weightedFrobeniusSq σ (W s m)) := by
        rw [← Real.sqrt_mul hσtr_nonneg]; congr 1; ring

/-- **General-reference off-diagonal leftover-hash trace-norm bound**
(Regula–Tomamichel arXiv:2603.04493 Lemma 12 / Renner quant-ph/0512258 §5.5). This
is `QuantumHashFamily.IsUniversal2Star.seedAvg_traceNorm_offDiag_le` with the max-mixed
dimension factor `n` replaced by
`σ.trace.re` and `∑_x ‖V x‖²_F` replaced by `collisionQuantity σ V`. The PosDef
hypothesis `hσ` is load-bearing (`σ^{-1/4}` requires full support). -/
theorem QuantumHashFamily.IsUniversal2Star.seedAvg_traceNorm_offDiag_le_genRef
    {S X Z : Type*} [Fintype S] [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {n : ℕ} [NeZero n] {H : QuantumHashFamily S X Z} (h2 : H.IsUniversal2Star)
    (σ : Op n) (hσ : σ.PosDef) (V : X → Op n) :
    (1 / (Fintype.card S : ℝ)) * ∑ s : S, ∑ m : Z,
        Quantum.Metrics.traceNorm ((∑ x : X, if H.hash s x = m then V x else 0)
          - (1 / (Fintype.card Z : ℝ)) • (∑ x : X, V x))
      ≤ Real.sqrt (σ.trace.re * (Fintype.card Z : ℝ) * (1 - 1 / (Fintype.card Z : ℝ))
          * collisionQuantity σ V) := by
  have : Nonempty Z := H.outputNonempty
  have : Nonempty S := H.seedNonempty
  have hS_pos : 0 < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  set F : Op n := σ ^ (-1/4 : ℝ) with hF_def
  set Vt : X → Op n := fun x => F * V x * F with hVt_def
  set Wo : S → Z → Op n := fun s m =>
    (∑ x : X, if H.hash s x = m then V x else 0)
      - (1 / (Fintype.card Z : ℝ)) • (∑ x : X, V x) with hWo_def
  set Wt : S → Z → Op n := fun s m =>
    (∑ x : X, if H.hash s x = m then Vt x else 0)
      - (1 / (Fintype.card Z : ℝ)) • (∑ x : X, Vt x) with hWt_def
  -- Linearity: `F · (Wo s m) · F = Wt s m`.
  have hsum : ∀ (g : X → Op n), F * (∑ x : X, g x) * F = ∑ x : X, F * g x * F :=
    fun g => by rw [Finset.mul_sum, Finset.sum_mul]
  have hbin : ∀ s m, F * (Wo s m) * F = Wt s m := by
    intro s m
    simp only [hWo_def, hWt_def]
    rw [mul_sub, sub_mul]
    congr 1
    · rw [hsum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : H.hash s x = m
      · simp only [hx, ite_true, hVt_def]
      · simp only [hx, ite_false, Matrix.mul_zero, Matrix.zero_mul]
    · rw [mul_smul_comm, smul_mul_assoc, hsum]
  -- Each bin's σ-weighted frobenius = the transformed bin's plain frobenius.
  have hLHSeq : ∀ s m, weightedFrobeniusSq σ (Wo s m) = ((Wt s m)ᴴ * (Wt s m)).trace.re := by
    intro s m
    rw [weightedFrobeniusSq, ← hF_def, hbin s m]
  -- Transformed single-copy frobenius = σ-weighted frobenius of V.
  have hVtx : ∀ x, ((Vt x)ᴴ * (Vt x)).trace.re = weightedFrobeniusSq σ (V x) := by
    intro x
    simp only [weightedFrobeniusSq, ← hF_def, hVt_def]
  -- Centred second moment on the transformed family.
  have hsm := h2.centred_second_moment Vt
  have hSum : ∑ s : S, ∑ m : Z, weightedFrobeniusSq σ (Wo s m)
      = (Fintype.card S : ℝ)
          * ((1 - 1 / (Fintype.card Z : ℝ)) * collisionQuantity σ V) := by
    rw [Finset.sum_congr rfl (fun s _ =>
      Finset.sum_congr rfl (fun m _ => hLHSeq s m))]
    have h1 : (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ m : Z, ((Wt s m)ᴴ * (Wt s m)).trace.re
        = (1 - 1 / (Fintype.card Z : ℝ)) *
            ∑ x : X, ((Vt x)ᴴ * (Vt x)).trace.re := hsm
    rw [Finset.sum_congr rfl (fun x _ => hVtx x)] at h1
    have h2' : (Fintype.card S : ℝ) *
        ((1 / (Fintype.card S : ℝ))
          * ∑ s : S, ∑ m : Z, ((Wt s m)ᴴ * (Wt s m)).trace.re)
        = (Fintype.card S : ℝ) * ((1 - 1 / (Fintype.card Z : ℝ))
            * collisionQuantity σ V) := by rw [h1, collisionQuantity]
    rwa [← mul_assoc, mul_one_div, div_self hS_ne, one_mul] at h2'
  -- Apply the abstract σ-weighted bound.
  have habs := seedAvg_traceNorm_le_of_weightedFrob σ hσ Wo
  rw [hSum] at habs
  calc (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ m : Z, Quantum.Metrics.traceNorm (Wo s m)
      ≤ (1 / (Fintype.card S : ℝ)) *
          Real.sqrt (σ.trace.re * ((Fintype.card S : ℝ) * (Fintype.card Z : ℝ))
            * ((Fintype.card S : ℝ) * ((1 - 1 / (Fintype.card Z : ℝ))
              * collisionQuantity σ V))) := by
        exact mul_le_mul_of_nonneg_left habs (by positivity)
    _ = Real.sqrt (σ.trace.re * (Fintype.card Z : ℝ) * (1 - 1 / (Fintype.card Z : ℝ))
          * collisionQuantity σ V) :=
        final_alg' (Fintype.card S : ℝ) (Fintype.card Z : ℝ)
          (1 - 1 / (Fintype.card Z : ℝ)) (collisionQuantity σ V) σ.trace.re hS_pos

end InfoTheory.QuantumLHL

end -- noncomputable section
