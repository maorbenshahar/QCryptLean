import QCryptLean.Quantum.TensorProducts.Rpow
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CfcSpectral
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Operator/CFC support lemmas for the collision-MGF positivity chain

Operator-algebra and continuous-functional-calculus lemmas establishing strict
positivity of the single-copy tilted collision moment-generating function
(`iidAEPSingleCopyMGF_pos`).

Contents:

* `CfcSpectral.rpow_mul_specProj` — the CFC real power acts by the eigenvalue on an
  indicator spectral projector: `B ^ r * specProj B l = (l ^ r) • specProj B l`.
* `CfcSpectral.mul_eq_zero_of_mul_rpow_eq_zero` — right-kernel invariance of a
  CFC real power: `M * B ^ r = 0 → M * B = 0` (for PSD `B`).
* `Quantum.Operators.posSemidef_trace_re_pos_of_ne_zero` — a nonzero PSD operator has
  strictly positive real trace.
* `Matrix.IsHermitian.mul_eq_zero_of_mul_mul_eq_zero` — for Hermitian `R` and PSD `Q`,
  `R * Q * R = 0 → R * Q = 0` (two-sided to one-sided kernel).
* `InfoTheory.SmoothMinEntropy.trace_rpow_mul_rpow_pos_of_opLe` — under the
  Löwner support gate `A ≼ t·B`, the tilted collision trace `tr[A^{1+s} · B^{−s}]`
  is strictly positive for `s ≥ 0`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace CfcSpectral

/-- **Real power acts by the eigenvalue on a spectral projector.** For a PSD `B` and
an indicator spectral projector `specProj B l`, the CFC real power satisfies
`B ^ r · specProj B l = (l ^ r) • specProj B l`. Both sides are `cfc`-functions of
`B`; the indicator forces the argument to equal `l`, so the integrand `x ^ r` may be
replaced by `l ^ r`. -/
lemma rpow_mul_specProj {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (hB : 0 ≤ B) (r l : ℝ) :
    B ^ r * specProj B l = (l ^ r : ℝ) • specProj B l := by
  simp only [specProj]
  rw [CFC.rpow_eq_cfc_real hB,
    ← cfc_mul _ _ B (continuousOn_spectrum B _) (continuousOn_spectrum B _),
    ← cfc_const_mul (l ^ r : ℝ) _ B (continuousOn_spectrum B _)]
  apply cfc_congr
  intro x _
  by_cases hxl : x = l <;> simp [Set.indicator, hxl]

/-- **Right kernel invariance under a real power.** For a PSD operator `B`,
right-multiplication by the CFC power `B ^ r` annihilates exactly the operators
annihilated by right-multiplication by `B`: `M * B ^ r = 0 → M * B = 0`. The `r`-th
power preserves positive eigenvalues and fixes the zero eigenspace, so
`range (B ^ r) = range B`.

Proven through the indicator spectral resolution `B = Σ_l l • specProj B l`: for each
eigenvalue `l ≠ 0` (hence `l > 0` by PSD), `rpow_mul_specProj` gives
`M * B ^ r * specProj B l = l ^ r • (M * specProj B l)` with `l ^ r ≠ 0`, so
`M * specProj B l = 0`; the `l = 0` term vanishes by the scalar. -/
lemma mul_eq_zero_of_mul_rpow_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {M B : Matrix n n ℂ}
    (hB : B.PosSemidef) {r : ℝ} (_hr : r ≠ 0) (h : M * B ^ r = 0) :
    M * B = 0 := by
  classical
  have hBnn : (0 : Matrix n n ℂ) ≤ B := Matrix.nonneg_iff_posSemidef.mpr hB
  have hBsa : IsSelfAdjoint B := hB.isHermitian
  have hdecomp : B = ∑ l ∈ specFinset B, (l : ℂ) • specProj B l :=
    eq_sum_specProj B hBsa
  -- each projector with nonzero eigenvalue is annihilated on the right by `M`
  have hkey : ∀ l ∈ specFinset B, (l : ℂ) • (M * specProj B l) = 0 := by
    intro l hl
    by_cases hl0 : l = 0
    · simp [hl0]
    · have hlpos : 0 < l :=
        lt_of_le_of_ne (spectrum_nonneg_of_nonneg hBnn (mem_specFinset.mp hl))
          (Ne.symm hl0)
      have hlr : (l ^ r : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlpos r)
      have hmsp : M * specProj B l = 0 := by
        have h1 : M * (B ^ r * specProj B l) = 0 := by
          rw [← Matrix.mul_assoc, h, Matrix.zero_mul]
        rw [rpow_mul_specProj B hBnn r l, mul_smul_comm] at h1
        -- `h1 : (l ^ r : ℝ) • (M * specProj B l) = 0`, and `l ^ r ≠ 0`
        have h2 := congrArg (fun X => (l ^ r : ℝ)⁻¹ • X) h1
        simpa only [smul_zero, smul_smul, inv_mul_cancel₀ hlr, one_smul] using h2
      rw [hmsp, smul_zero]
  calc M * B
      = M * ∑ l ∈ specFinset B, (l : ℂ) • specProj B l := by rw [← hdecomp]
    _ = ∑ l ∈ specFinset B, (l : ℂ) • (M * specProj B l) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by rw [mul_smul_comm])
    _ = 0 := Finset.sum_eq_zero hkey

end CfcSpectral

namespace Quantum.Operators

/-- **Strict trace positivity for a nonzero PSD operator.** The real part of the
trace of a positive-semidefinite operator is nonnegative, and is strictly positive
unless the operator is `0`. -/
lemma posSemidef_trace_re_pos_of_ne_zero {n : ℕ}
    {A : Op n} (hA : A.PosSemidef) (hA0 : A ≠ 0) : 0 < A.trace.re := by
  rcases hA.trace_re_nonneg.lt_or_eq with h | h
  · exact h
  · exact absurd (hA.trace_eq_zero_iff.mp
      (Complex.ext h.symm (hA.trace_nonneg.2).symm)) hA0

end Quantum.Operators

namespace Matrix.IsHermitian

/-- **Two-sided to one-sided kernel for a PSD middle factor.** If a Hermitian `R`
and a positive-semidefinite `Q` satisfy `R * Q * R = 0`, then already `R * Q = 0`.
Writing `Q = S * S` with `S = √Q`, the operator `(R * S) * (R * S)ᴴ` vanishes,
forcing `R * S = 0` and hence `R * Q = 0`. -/
lemma mul_eq_zero_of_mul_mul_eq_zero {n : Type*} [Fintype n]
    {R Q : Matrix n n ℂ} (hR : R.IsHermitian) (hQ : Q.PosSemidef)
    (h : R * Q * R = 0) : R * Q = 0 := by
  classical
  set S : Matrix n n ℂ := CFC.sqrt Q with hSdef
  have hS : S.PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hSS : S * S = Q := CFC.sqrt_mul_sqrt_self Q hQ.nonneg
  -- `R Q R = (R S)(R S)ᴴ`, so `R S = 0`.
  have hCC : (R * S) * (R * S)ᴴ = 0 := by
    have hadj : (R * S)ᴴ = S * R := by
      rw [Matrix.conjTranspose_mul, hS.isHermitian, hR]
    rw [hadj]
    have hkey : (R * S) * (S * R) = R * Q * R := by
      rw [← hSS]; simp only [Matrix.mul_assoc]
    rw [hkey, h]
  have hRS0 : R * S = 0 := by
    have hiff := Matrix.conjTranspose_mul_self_eq_zero (A := (R * S)ᴴ)
    rw [Matrix.conjTranspose_conjTranspose] at hiff
    have hadj0 : (R * S)ᴴ = 0 := hiff.mp hCC
    have h := congrArg Matrix.conjTranspose hadj0
    rwa [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h
  -- Push `R S = 0` back to `R Q = 0`.
  have h : (R * S) * S = 0 := by rw [hRS0, Matrix.zero_mul]
  rwa [Matrix.mul_assoc, hSS] at h

end Matrix.IsHermitian

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators

/-- **Strict trace positivity of a tilted single block under the support gate.**
For PSD operators `A`, `B` with `A ≠ 0` and `A ≼ t·B` in the Löwner order
(`opLe`, the feasibility domination), and a nonnegative tilt `s ≥ 0`, the tilted
collision trace `tr[A^{1+s} · B^{−s}]` is strictly positive.

This is the operator-level support fact behind `iidAEPSingleCopyMGF_pos`.
The Löwner domination `A ≼ t·B` forces `supp A ⊆ supp B` (equivalently
`ker B ⊆ ker A`), so the CFC power `B^{−s}` — positive-definite on `range B` — does
not annihilate `range(A^{1+s}) = range A`. Writing
`tr[A^{1+s} B^{−s}] = tr[(B^{−s/2}) A^{1+s} (B^{−s/2})]` exhibits a PSD operator
whose trace would vanish only if `A^{(1+s)/2}·B^{−s/2} = 0`, i.e. `range B ⊆ ker A`;
combined with `range A ⊆ range B` this gives `range A ⊆ ker A`, forcing `A = 0`,
contradicting `A ≠ 0`. The negativity-of-trace branch is excluded because the
sandwich is PSD (`trace_mul_psd_nonneg`). -/
lemma trace_rpow_mul_rpow_pos_of_opLe {n : ℕ} [NeZero n]
    {A B : Quantum.Operators.Op n}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hA0 : A ≠ 0)
    {t : ℝ} (hle : Quantum.Operators.opLe A (Complex.ofReal t • B))
    {s : ℝ} (hs : 0 ≤ s) :
    0 < (A ^ (1 + s) * B ^ (-s)).trace.re := by
  classical
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · -- `s = 0`: the tilt is trivial, `A ^ 1 * B ^ 0 = A`, and a nonzero PSD
    -- operator has strictly positive trace.
    have hAB : A ^ (1 + s) * B ^ (-s) = A := by
      rw [← hs0]
      rw [show (1 : ℝ) + 0 = 1 by ring, show -(0 : ℝ) = 0 by ring,
        CFC.rpow_one A hA.nonneg, CFC.rpow_zero B hB.nonneg, mul_one]
    rw [hAB]
    exact posSemidef_trace_re_pos_of_ne_zero hA hA0
  · -- `0 < s`: the support gate kicks in.
    set P : Op n := A ^ (1 + s) with hPdef
    set Q : Op n := B ^ (-s) with hQdef
    have hP : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
    have hQ : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
    have hnn : 0 ≤ (P * Q).trace.re := trace_mul_psd_nonneg P Q hP hQ
    rcases hnn.lt_or_eq with hlt | heq
    · exact hlt
    -- Suppose the trace vanishes; derive `A = 0`, contradicting `hA0`.
    exfalso
    set R : Op n := CFC.sqrt P with hRdef
    have hR : R.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
    have hRH : R.IsHermitian := hR.isHermitian
    have hRR : R * R = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
    -- `M = R Q R` is PSD with vanishing trace, hence `0`.
    have hM_psd : (R * Q * R).PosSemidef := by
      have h := hQ.conjTranspose_mul_mul_same R
      rwa [hRH] at h
    have hcyc : (R * Q * R).trace = (P * Q).trace := by
      rw [Matrix.trace_mul_comm (R * Q) R, ← Matrix.mul_assoc, hRR]
    have htraceM : (R * Q * R).trace = 0 :=
      Complex.ext (by rw [hcyc]; exact heq.symm) (hM_psd.trace_nonneg.2).symm
    have hM0 : R * Q * R = 0 := hM_psd.trace_eq_zero_iff.mp htraceM
    -- `R Q R = 0` with `Q` PSD gives `R Q = 0`, then through the support `R B = 0`.
    have hRQ : R * Q = 0 := hRH.mul_eq_zero_of_mul_mul_eq_zero hQ hM0
    have hRBs : R * B ^ (-s) = 0 := by rw [hQdef] at hRQ; exact hRQ
    have hRB : R * B = 0 :=
      CfcSpectral.mul_eq_zero_of_mul_rpow_eq_zero hB (neg_ne_zero.mpr hs0.ne') hRBs
    have hBR : B * R = 0 := by
      have h := congrArg Matrix.conjTranspose hRB
      rwa [Matrix.conjTranspose_mul, hRH, hB.isHermitian,
        Matrix.conjTranspose_zero] at h
    -- The Löwner domination transfers the kernel: `A * R = 0`.
    have hAR : A * R = 0 := mul_eq_zero_of_opLe_smul hA hB.isHermitian hRH hle hBR
    -- Push to `A * P = 0`, then through the support to `A * A = 0`, hence `A = 0`.
    have hAP : A * P = 0 := by
      have h : (A * R) * R = 0 := by rw [hAR, Matrix.zero_mul]
      rwa [Matrix.mul_assoc, hRR] at h
    have hAPs : A * A ^ (1 + s) = 0 := by rw [hPdef] at hAP; exact hAP
    have hAA : A * A = 0 :=
      CfcSpectral.mul_eq_zero_of_mul_rpow_eq_zero hA (by intro hc; linarith) hAPs
    have hA_zero : A = 0 := by
      have hAH : Aᴴ * A = 0 := by rw [hA.isHermitian]; exact hAA
      exact Matrix.conjTranspose_mul_self_eq_zero.mp hAH
    exact hA0 hA_zero

end InfoTheory.SmoothMinEntropy

end
