import QCryptLean.Quantum.Operators.InverseSqrt
import QCryptLean.Quantum.Operators.ProjectorBlocks
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Math.Analysis.AMGM
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# PSD Domination by a Positive-Definite Reference

An operator-analysis helper used by the smooth quantum LHL development:

  For any positive-definite `σ` and any positive-semidefinite `A` on `Fin n`,
  there exists a real `t ≥ 0` such that `A ≼ t · σ` (in the `opLe` order).

This is the standard fact used to discharge feasibility of the min-entropy
SDP from `σ.toOp.PosDef`. The proof goes through the σ^{-1/2} sandwich:
`A_S := σ^{-1/2}·A·σ^{-1/2}` is PSD, hence `A_S ≼ tr(A_S).re · 1` (eigenvalues
of a PSD operator are bounded by its trace), and sandwiching back by σ^{1/2}
recovers `A ≼ tr(A_S).re · σ`.

## Main statement

* `Matrix.PosDef.exists_smul_opLe_of_posSemidef` — existence of a real witness
  `t ≥ 0` such that `A ≼ t · σ`, given `σ.PosDef` and `A.PosSemidef`.
* `Quantum.Operators.psd_le_one_of_trace_le_one` — a PSD operator with trace
  at most one is dominated by the identity.
* `Quantum.Operators.opLe_smul_one_of_psd_diag_add_offdiag` — the Weyl bound
  `λ_max(D + O) ≤ Tr D + λ_max(O)` for a PSD diagonal block and a scalar-capped
  off-diagonal part, and `Quantum.Operators.opLe_smul_one_of_compl_block_psd`, its form for
  the `{P, 1 - P}` blocks of a bulk-subtracted operator `A - z·B`.
* `Quantum.Operators.offdiag_opLe_eps_smul_diag_blocks` and
  `Quantum.Operators.offdiag_opLe_smul_one_of_diag_block_opNorms` — the block Young bound
  producing such an off-diagonal cap from the two diagonal-block operator norms, and
  `Quantum.Operators.offdiag_opLe_two_mul_sqrt_smul_one`, its optimal form: the cap is the
  geometric mean `2·√(μ_Q·μ_P)` of the two block norms.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Operators

/-- A PSD operator with trace at most one is dominated by the identity. -/
lemma psd_le_one_of_trace_le_one {d : ℕ} [NeZero d]
    (A : Op d) (hA : A.PosSemidef) (htr : A.trace.re ≤ 1) :
    (1 - A).PosSemidef := by
  have hAh := hA.isHermitian
  set U := (↑hAh.eigenvectorUnitary : Op d)
  set D := Matrix.diagonal
    ((Complex.ofReal ∘ hAh.eigenvalues : Fin d → ℂ))
  have heig_nn := hAh.posSemidef_iff_eigenvalues_nonneg.mp hA
  have htr_sum : ∑ i, hAh.eigenvalues i ≤ 1 := by
    have h1 : A.trace.re = ∑ i, hAh.eigenvalues i := by
      rw [hAh.trace_eq_sum_eigenvalues]
      simp [Complex.ofReal_re]
    linarith
  have heig_le1 : ∀ i, hAh.eigenvalues i ≤ 1 := by
    intro i
    linarith [Finset.single_le_sum
      (f := hAh.eigenvalues)
      (fun j _ => heig_nn j) (Finset.mem_univ i)]
  have hD_sub_psd : (1 - D).PosSemidef := by
    have hdiag : 1 - D = Matrix.diagonal
        (fun i => ((1 - hAh.eigenvalues i : ℝ) : ℂ)) := by
      ext i j
      simp [D, Matrix.diagonal, Matrix.one_apply]
      split <;> simp [*]
    rw [hdiag, Matrix.posSemidef_diagonal_iff]
    intro i
    rw [Complex.nonneg_iff]
    exact ⟨by simp; linarith [heig_le1 i], by simp⟩
  have hUU : U * Uᴴ = 1 := by
    exact_mod_cast hAh.eigenvectorUnitary.prop.2
  have hA_eq : A = U * D * Uᴴ := by
    have := hAh.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h1A_eq : 1 - A = U * (1 - D) * Uᴴ := by
    rw [hA_eq]
    conv_lhs => rw [← hUU]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  rw [h1A_eq]
  exact hD_sub_psd.mul_mul_conjTranspose_same U

/-- **A PSD operator is dominated in the `opLe` order by its trace times the identity.**

For positive-semidefinite `D`, every eigenvalue is at most the sum of eigenvalues
`= D.trace.re`, so `D ⪯ D.trace.re • 1`.  This is the operator-order (`opLe`) public
companion of the matrix-order `le_trace_re_smul_one_of_posSemidef`: the largest eigenvalue
of a PSD operator is bounded by its trace.

It is the load-bearing primitive of the Weyl trace-concentration bound
`opLe_smul_one_of_psd_diag_add_offdiag`: the kernel/diagonal block of a residual spike,
being PSD, contributes only its (scalar) trace mass to the spectral floor, never its full
operator norm. -/
lemma psd_opLe_trace_re_smul_one {d : ℕ} (D : Op d) (hD : D.PosSemidef) :
    opLe D (Complex.ofReal D.trace.re • (1 : Op d)) := by
  apply opLe_of_posSemidef_sub
  set c := D.trace.re with hc
  have hH := hD.isHermitian
  have hD_eig_nn : 0 ≤ hH.eigenvalues := hH.posSemidef_iff_eigenvalues_nonneg.mp hD
  have htr_eig_sum : (∑ i, hH.eigenvalues i : ℝ) = c := by
    have h := hH.trace_eq_sum_eigenvalues
    have : c = (∑ i, (hH.eigenvalues i : ℂ)).re := by simp [hc, h]
    rw [this, Complex.re_sum]; simp
  have hD_eig_le : ∀ i, hH.eigenvalues i ≤ c := fun i => by
    rw [← htr_eig_sum]
    exact Finset.single_le_sum (fun j _ => hD_eig_nn j) (Finset.mem_univ i)
  have h_spec : ∀ x ∈ spectrum ℝ D, 0 ≤ c - x := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i, rfl⟩; linarith [hD_eig_le i]
  have h_eq : cfc (fun x : ℝ => c - x) D = (Complex.ofReal c : ℂ) • (1 : Op d) - D := by
    have hfg : (fun x : ℝ => c - x) = fun x => (fun _ : ℝ => c) x - id x := by ext x; simp
    rw [hfg, cfc_sub (fun _ => c) id D, cfc_const c D, cfc_id ℝ D]
    congr 1; rw [Algebra.algebraMap_eq_smul_one]; rfl
  have h0 : (0 : Op d) ≤ cfc (fun x : ℝ => c - x) D := cfc_nonneg h_spec
  rw [h_eq] at h0; exact sub_nonneg.mp h0

/-- **Weyl trace-concentration upper bound: PSD diagonal block plus a Löwner-capped
off-diagonal Hermitian part.**

For a positive-semidefinite "diagonal" block `D` and an "off-diagonal" Hermitian part `O`
that is itself Löwner-bounded by a scalar `s` (`O ⪯ s • 1`), the sum is bounded by the
scalar floor `c • 1` as soon as the *trace* of `D` plus the off-diagonal cap `s` is at most
`c`:

  `D ⪰ 0`,  `O ⪯ s • 1`,  `D.trace.re + s ≤ c`  ⟹  `D + O ⪯ c • 1`.

This is the exact (no-approximation) spectral form of the Weyl additive eigenvalue bound
`λ_max(D + O) ≤ λ_max(D) + λ_max(O) ≤ D.trace.re + s`.  It is the reusable spectral
infrastructure behind the de Finetti residual *kernel + off-diagonal* concentration: the
PSD kernel block contributes only its trace mass `D.trace.re` (via `psd_opLe_trace_re_smul_one`),
while the off-diagonal leak contributes its scalar Löwner cap `s` — so a residual spike is
floored by its trace plus its (genuinely smaller) off-diagonal operator norm, *not* by the
worst-case operator norm of `D` itself.

A pure trace bound `D.trace.re ≤ c` on `D + O` is **unsound** when `O ≠ 0`: the off-diagonal
part can push `λ_max(D + O)` strictly above `D.trace.re` (e.g. `D = diag(1,0)`,
`O = [[0,½],[½,0]]` gives `λ_max(D + O) = (1+√2)/2 ≈ 1.207 > 1 = D.trace.re`).  The
off-diagonal Löwner cap `s` is therefore irreducible and load-bearing. -/
lemma opLe_smul_one_of_psd_diag_add_offdiag {d : ℕ} {D O : Op d} {s c : ℝ}
    (hD : D.PosSemidef)
    (hO : opLe O (Complex.ofReal s • (1 : Op d)))
    (hsum : D.trace.re + s ≤ c) :
    opLe (D + O) (Complex.ofReal c • (1 : Op d)) := by
  have hD' : opLe D (Complex.ofReal D.trace.re • (1 : Op d)) := psd_opLe_trace_re_smul_one D hD
  have hadd := opLe_add hD' hO
  have hcombine :
      (Complex.ofReal D.trace.re • (1 : Op d)) + (Complex.ofReal s • (1 : Op d))
        = Complex.ofReal (D.trace.re + s) • (1 : Op d) := by
    rw [← add_smul, ← Complex.ofReal_add]
  rw [hcombine] at hadd
  refine (fun v => le_trans (hadd v) ?_)
  rw [Quantum.Operators.quadraticForm_smul, Quantum.Operators.quadraticForm_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hqf_nn : 0 ≤ (quadraticForm (1 : Op d) v).re := by
    have h1 : (1 : Op d).PosSemidef := Matrix.PosSemidef.one
    exact (Complex.nonneg_iff.mp
      (by simp only [quadraticForm]; exact h1.dotProduct_mulVec_nonneg v)).1
  exact mul_le_mul_of_nonneg_right hsum hqf_nn

/-! ### Block Young / AM–GM off-diagonal Löwner bound

The operator-norm (largest-eigenvalue) companion of the trace-concentration bound above.
Where `opLe_smul_one_of_psd_diag_add_offdiag` floors the off-diagonal by its own scalar
Löwner cap `s`, the lemmas here *derive* such a cap from the two diagonal blocks via the
exact block Young inequality: for a PSD operator `A` and any two Hermitian operators `P`,
`Q` (typically complementary projectors), and any real `ε > 0`,

  `Q·A·P + P·A·Q  ⪯  ε·(Q·A·Q) + ε⁻¹·(P·A·P)`,

the Löwner shadow of the PSD witness `(√ε·Q − ε^{-1/2}·P)·A·(√ε·Q − ε^{-1/2}·P)ᴴ ⪰ 0`.
This is the *operator-norm* off-diagonal bound (no trace anywhere): the off-diagonal leak is
capped by the geometric mean of the two diagonal-block operator norms, never by their trace
mass.  It is the spectral form of the 2×2 Hermitian block bound
`‖[[X,Y],[Yᴴ,Z]]‖ ≤ max ‖X‖ ‖Z‖ + ‖Y‖` specialized to the off-diagonal contribution. -/

/-- **Block Young / AM–GM off-diagonal Löwner bound.**

For a positive-semidefinite `A` and Hermitian `P`, `Q`, and any real `ε > 0`, the Hermitian
off-diagonal `Q·A·P + P·A·Q` is Löwner-bounded by `ε·(Q·A·Q) + ε⁻¹·(P·A·P)`.  Proof: the
witness `B := √ε·Q − ε^{-1/2}·P` is Hermitian, so `B·A·Bᴴ = B·A·B ⪰ 0`; expanding gives
`ε·(QAQ) + ε⁻¹·(PAP) − (QAP + PAQ)` (the cross-coefficients `√ε·ε^{-1/2}` collapse to `1`),
which is therefore PSD. -/
lemma offdiag_opLe_eps_smul_diag_blocks {d : ℕ} {A P Q : Op d}
    (hA : A.PosSemidef) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    {ε : ℝ} (hε : 0 < ε) :
    opLe (Q * A * P + P * A * Q)
      ((Complex.ofReal ε) • (Q * A * Q) + (Complex.ofReal ε⁻¹) • (P * A * P)) := by
  apply opLe_of_posSemidef_sub
  set s : ℝ := Real.sqrt ε with hs
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hε
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs2 : s * s = ε := Real.mul_self_sqrt hε.le
  have hsi2 : s⁻¹ * s⁻¹ = ε⁻¹ := by rw [← mul_inv, hs2]
  have hsisi : s * s⁻¹ = 1 := mul_inv_cancel₀ hs_ne
  have hsis : s⁻¹ * s = 1 := inv_mul_cancel₀ hs_ne
  set B : Op d := ((s : ℂ) • Q - ((s⁻¹ : ℝ) : ℂ) • P) with hB
  have hBherm : Bᴴ = B := by
    rw [hB]; simp only [conjTranspose_sub, conjTranspose_smul, hP.eq, hQ.eq]
    simp [Complex.conj_ofReal]
  have hpsd : (B * A * Bᴴ).PosSemidef := hA.mul_mul_conjTranspose_same B
  rw [hBherm] at hpsd
  have hexpand : B * A * B
      = ((s * s : ℝ) : ℂ) • (Q * A * Q) + ((s⁻¹ * s⁻¹ : ℝ) : ℂ) • (P * A * P)
        - ((s * s⁻¹ : ℝ) : ℂ) • (Q * A * P) - ((s⁻¹ * s : ℝ) : ℂ) • (P * A * Q) := by
    rw [hB]
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    push_cast; ring_nf; abel
  rw [hexpand, hs2, hsi2, hsisi, hsis] at hpsd
  simp only [Complex.ofReal_one, one_smul] at hpsd
  convert hpsd using 1
  rw [sub_add_eq_sub_sub]

/-- A nonnegative real scaling of an operator-norm bound: if `X ⪯ μ·1` and `0 ≤ ε`, then
`ε·X ⪯ (ε·μ)·1`. -/
private lemma opLe_smul_smul_one_of_nonneg {d : ℕ} {X : Op d} {μ ε : ℝ}
    (hε : 0 ≤ ε) (h : opLe X (Complex.ofReal μ • (1 : Op d))) :
    opLe ((Complex.ofReal ε) • X) (Complex.ofReal (ε * μ) • (1 : Op d)) := by
  intro v
  have hX := h v
  rw [quadraticForm_smul] at hX
  rw [quadraticForm_smul, quadraticForm_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hX ⊢
  calc ε * (quadraticForm X v).re
      ≤ ε * (μ * (quadraticForm (1 : Op d) v).re) := mul_le_mul_of_nonneg_left hX hε
    _ = (ε * μ) * (quadraticForm (1 : Op d) v).re := by ring

/-- **Off-diagonal Löwner cap from the two diagonal-block operator norms.**

Combining the block Young inequality `offdiag_opLe_eps_smul_diag_blocks` with operator-norm
(largest-eigenvalue) bounds `Q·A·Q ⪯ μ_Q·1` and `P·A·P ⪯ μ_P·1` on the two diagonal blocks,
the off-diagonal `Q·A·P + P·A·Q` is Löwner-bounded by `s·1` as soon as the weighted sum of
the two block norms `ε·μ_Q + ε⁻¹·μ_P` is at most `s` for some `ε > 0` (optimally
`2·√(μ_Q·μ_P) ≤ s`):

  `A ⪰ 0`,  `Q·A·Q ⪯ μ_Q·1`,  `P·A·P ⪯ μ_P·1`,  `ε·μ_Q + ε⁻¹·μ_P ≤ s`  ⟹
    `Q·A·P + P·A·Q ⪯ s·1`.

This is the *operator-norm* off-diagonal estimate: unlike a trace bound on `P·A·P`, the
range-block contribution enters only through its largest eigenvalue `μ_P`, so a bulk-scale
trace does not inflate the off-diagonal cap.  It is the reusable spectral plumbing for the
de Finetti residual off-diagonal leak. -/
lemma offdiag_opLe_smul_one_of_diag_block_opNorms {d : ℕ} {A P Q : Op d}
    (hA : A.PosSemidef) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    {μQ μP s ε : ℝ} (hε : 0 < ε)
    (hQbound : opLe (Q * A * Q) (Complex.ofReal μQ • (1 : Op d)))
    (hPbound : opLe (P * A * P) (Complex.ofReal μP • (1 : Op d)))
    (harith : ε * μQ + ε⁻¹ * μP ≤ s) :
    opLe (Q * A * P + P * A * Q) (Complex.ofReal s • (1 : Op d)) := by
  have h1 := offdiag_opLe_eps_smul_diag_blocks hA hP hQ hε
  have hQ' := opLe_smul_smul_one_of_nonneg hε.le hQbound
  have hP' := opLe_smul_smul_one_of_nonneg (inv_nonneg.mpr hε.le) hPbound
  have hsum := opLe_add hQ' hP'
  have hcombine :
      (Complex.ofReal (ε * μQ) • (1 : Op d)) + (Complex.ofReal (ε⁻¹ * μP) • (1 : Op d))
        = Complex.ofReal (ε * μQ + ε⁻¹ * μP) • (1 : Op d) := by
    rw [← add_smul, ← Complex.ofReal_add]
  rw [hcombine] at hsum
  exact opLe_trans h1 (opLe_trans hsum (opLe_smul_one_mono (n := d) harith))

/-- **Optimal off-diagonal Löwner cap: the geometric mean of the two diagonal-block norms.**

For positive-semidefinite `A`, Hermitian `P`, `Q`, and diagonal-block bounds `Q·A·Q ⪯ μ_Q·1`
and `P·A·P ⪯ μ_P·1`, the off-diagonal is bounded by their geometric mean:

  `Q·A·P + P·A·Q ⪯ 2·√(μ_Q·μ_P)·1`.

This is `offdiag_opLe_smul_one_of_diag_block_opNorms` at the optimal weight
(`Real.isGLB_mul_add_inv_mul`); when one diagonal-block bound is `0` the cap `0` is only a limit
of weighted caps. No sign hypotheses are needed: on any nonzero vector the block bounds force
`μ_Q, μ_P ≥ 0`. -/
lemma offdiag_opLe_two_mul_sqrt_smul_one {d : ℕ} {A P Q : Op d}
    (hA : A.PosSemidef) (hP : P.IsHermitian) (hQ : Q.IsHermitian) {μQ μP : ℝ}
    (hQbound : opLe (Q * A * Q) (Complex.ofReal μQ • (1 : Op d)))
    (hPbound : opLe (P * A * P) (Complex.ofReal μP • (1 : Op d))) :
    opLe (Q * A * P + P * A * Q) (Complex.ofReal (2 * √(μQ * μP)) • (1 : Op d)) := by
  intro v
  have hsmul : ∀ c : ℝ, (quadraticForm (Complex.ofReal c • (1 : Op d)) v).re =
      c * (quadraticForm (1 : Op d) v).re := fun c => by
    rw [quadraticForm_smul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hr : 0 ≤ (quadraticForm (1 : Op d) v).re :=
    posSemidef_re_quadraticForm_nonneg Matrix.PosSemidef.one v
  have hweight : ∀ ε, 0 < ε → (quadraticForm (Q * A * P + P * A * Q) v).re ≤
      (ε * μQ + ε⁻¹ * μP) * (quadraticForm (1 : Op d) v).re := fun ε hε => by
    rw [← hsmul]
    exact offdiag_opLe_smul_one_of_diag_block_opNorms hA hP hQ hε hQbound hPbound le_rfl v
  rw [hsmul]
  rcases hr.eq_or_lt with hr0 | hrpos
  · have h := hweight 1 one_pos
    rw [← hr0, mul_zero] at h ⊢
    exact h
  -- On a nonzero vector a diagonal-block bound `B·A·B ⪯ μ·1` forces `μ ≥ 0`.
  have hblock : ∀ {B : Op d} {μ : ℝ}, B.IsHermitian →
      opLe (B * A * B) (Complex.ofReal μ • (1 : Op d)) → 0 ≤ μ := by
    intro B μ hB hbound
    have hpsd := hA.conjTranspose_mul_mul_same B
    rw [hB.eq] at hpsd
    have h := (posSemidef_re_quadraticForm_nonneg hpsd v).trans (hbound v)
    rw [hsmul] at h
    by_contra! hμ
    nlinarith
  have hlow : (quadraticForm (Q * A * P + P * A * Q) v).re / (quadraticForm (1 : Op d) v).re ≤
      2 * √(μQ * μP) := by
    refine (Real.isGLB_mul_add_inv_mul (hblock hQ hQbound) (hblock hP hPbound)).2 ?_
    rintro _ ⟨ε, hε, rfl⟩
    rw [div_le_iff₀ hrpos]
    exact hweight ε hε
  rwa [div_le_iff₀ hrpos] at hlow

/-! ### Scalar floor for a bulk-subtracted operator, read off its projector blocks -/

/-- **Löwner cap for a bulk-subtracted operator from its `{P, 1 − P}` blocks.**

Let `P` fix a reference `B` on both sides (`P·B = B·P = B`, the situation of a support
projector of `B`), and consider the indefinite residual `A − z·B`.  Splitting it into the
four `{P, 1 − P}` blocks (`sub_smul_eq_blocks`), the bulk `z·B` survives only on the
`P`-block, so the residual is

  `A − z·B = (1 − P)·A·(1 − P) + ((P·A·P − z·B) + ((1 − P)·A·P + P·A·(1 − P)))`.

Given that the complementary block is positive semidefinite, that the bulk-subtracted
`P`-block together with the off-diagonal pair is Löwner-capped by `s`, and that the
complementary block's trace mass plus `s` fits under `c`, the residual is capped by `c·1`.

This is `opLe_smul_one_of_psd_diag_add_offdiag` applied to that splitting, so it is the Weyl
bound `λ_max(D + O) ≤ Tr D + λ_max(O)` in block form: the complementary block contributes only
its trace, never its operator norm, and the cancellation between `A` and `z·B` is kept inside
the `P`-block rather than bounded away. -/
theorem opLe_smul_one_of_compl_block_psd {d : ℕ} {P A B : Op d} {z : ℂ} {s c : ℝ}
    (hPB : P * B = B) (hBP : B * P = B)
    (hCompl : ((1 - P) * A * (1 - P)).PosSemidef)
    (hRest : opLe ((P * A * P - z • B) + ((1 - P) * A * P + P * A * (1 - P)))
      (Complex.ofReal s • (1 : Op d)))
    (hsum : ((1 - P) * A * (1 - P)).trace.re + s ≤ c) :
    opLe (A - z • B) (Complex.ofReal c • (1 : Op d)) := by
  rw [sub_smul_eq_blocks hPB hBP A z]
  exact opLe_smul_one_of_psd_diag_add_offdiag hCompl hRest hsum

end Quantum.Operators

namespace Matrix.PosDef

/-- The quadratic form is linear in the operator under complex scalar multiplication:
`⟨v | (c • A) | v⟩ = c · ⟨v | A | v⟩`. -/
private lemma quadraticForm_smul {n : ℕ} (c : ℂ) (A : Op n) (v : Fin n → ℂ) :
    Quantum.Operators.quadraticForm (c • A) v = c * Quantum.Operators.quadraticForm A v := by
  change star v ⬝ᵥ (c • A).mulVec v = c * (star v ⬝ᵥ A.mulVec v)
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Bridge**: Mathlib's Löwner matrix order implies the `opLe` quadratic-form
ordering. No Hermitian hypothesis is needed. -/
private lemma opLe_of_matrix_le {n : ℕ} {A B : Op n} (h : A ≤ B) : opLe A B := by
  rw [Matrix.le_iff] at h
  intro v
  have hnn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 v
  -- hnn : 0 ≤ star v ⬝ᵥ (B - A) *ᵥ v
  rw [Complex.nonneg_iff] at hnn
  have hre := hnn.1
  -- hre : 0 ≤ (star v ⬝ᵥ (B - A) *ᵥ v).re
  change 0 ≤ (quadraticForm (B - A) v).re at hre
  rw [Quantum.Operators.quadraticForm_sub, Complex.sub_re, sub_nonneg] at hre
  exact hre

/-- **PSD operator bounded by its trace times identity** (matrix order version).

For PSD `P`, we have `P ≤ P.trace.re • 1` in the Löwner matrix order.

Proof: via CFC, with `f(x) = P.trace.re - x`. On the spectrum of `P`, each eigenvalue
is nonneg and at most the sum of eigenvalues (= `P.trace.re`), so `f(x) ≥ 0`.
Hence `cfc f P ≥ 0`, and this matches `P.trace.re • 1 - P` by CFC linearity. -/
private lemma le_trace_re_smul_one_of_posSemidef {d : ℕ}
    {P : Op d} (hP : P.PosSemidef) :
    P ≤ (Complex.ofReal P.trace.re : ℂ) • (1 : Op d) := by
  set c := P.trace.re with hc_def
  have hH := hP.isHermitian
  have hsa : IsSelfAdjoint P := hH.isSelfAdjoint
  have hP_eig_nn : 0 ≤ hH.eigenvalues :=
    hH.posSemidef_iff_eigenvalues_nonneg.mp hP
  -- Sum of eigenvalues = P.trace.re
  have htr_eig_sum : (∑ i, hH.eigenvalues i : ℝ) = c := by
    have h := hH.trace_eq_sum_eigenvalues
    -- h : P.trace = ∑ i, ↑(hH.eigenvalues i)
    have : c = (∑ i, (hH.eigenvalues i : ℂ)).re := by
      simp [hc_def, h]
    rw [this, Complex.re_sum]
    simp
  have hP_eig_le : ∀ i, hH.eigenvalues i ≤ c := fun i => by
    rw [← htr_eig_sum]
    exact Finset.single_le_sum (fun j _ => hP_eig_nn j) (Finset.mem_univ i)
  have h_spec : ∀ x ∈ spectrum ℝ P, 0 ≤ c - x := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i, rfl⟩; linarith [hP_eig_le i]
  -- cfc (c - ·) P = c • 1 - P
  have h_eq : cfc (fun x : ℝ => c - x) P
      = (Complex.ofReal c : ℂ) • (1 : Op d) - P := by
    have hfg : (fun x : ℝ => c - x) = fun x => (fun _ : ℝ => c) x - id x := by ext x; simp
    rw [hfg, cfc_sub (fun _ => c) id P, cfc_const c P, cfc_id ℝ P]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  have h0 : (0 : Op d) ≤ cfc (fun x : ℝ => c - x) P :=
    cfc_nonneg h_spec
  rw [h_eq] at h0
  exact sub_nonneg.mp h0

/-- **PSD ≼ scalar multiple of any positive-definite reference.**

For `σ : Op n` positive definite and `A : Op n` positive semidefinite, there
exists a real `t ≥ 0` with `opLe A (Complex.ofReal t • σ)`.

This packages two standard matrix-analysis facts into one named statement:
1. PSD operators are bounded by `(trace).re · I` (eigenvalues ≤ trace).
2. The σ^{-1/2}-sandwich is invertible: `opLe (S A S) (t • 1)` implies
   `opLe A (t • σ)` (sandwich back by σ^{1/2}).

A concrete witness is `t := (σ^{-1/2} · A · σ^{-1/2}).trace.re`. -/
lemma exists_smul_opLe_of_posSemidef {n : ℕ}
    {σ : Op n} (hσ : σ.PosDef)
    {A : Op n} (hA : A.PosSemidef) :
    ∃ t : ℝ, 0 ≤ t ∧ opLe A (Complex.ofReal t • σ) := by
  set S := hσ.inverseSqrt with hS_def
  have hS_herm : S.IsHermitian := hσ.inverseSqrt_isHermitian
  have hSσS : S * σ * S = 1 := hσ.inverseSqrt_sandwich_eq_one
  -- B is the σ-weighted A: B = S * A * S
  set B := S * A * S with hB_def
  -- Show B is PSD via the quadratic-form criterion
  have hB_herm : B.IsHermitian := by
    change Bᴴ = B
    rw [hB_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hS_herm.eq, hA.isHermitian.eq]
    simp [Matrix.mul_assoc]
  have hB_psd : B.PosSemidef := by
    refine Quantum.Operators.posSemidef_of_isHermitian_of_quadraticForm_re_nonneg
      hB_herm ?_
    intro w
    rw [hB_def,
        Quantum.Operators.quadraticForm_sandwich_self_of_isHermitian hS_herm A w]
    have hqf_A := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2 (S.mulVec w)
    rw [Complex.nonneg_iff] at hqf_A
    exact hqf_A.1
  -- Define t := B.trace.re
  set t : ℝ := B.trace.re with ht_def
  have ht_nn : 0 ≤ t := hB_psd.trace_re_nonneg
  refine ⟨t, ht_nn, ?_⟩
  -- opLe A (Complex.ofReal t • σ)
  intro v
  -- Define w := σ.mulVec (S.mulVec v) = (σ * S).mulVec v
  set w : Fin n → ℂ := σ.mulVec (S.mulVec v) with hw_def
  -- (a) S.mulVec w = v, using SσS = 1
  have hSw : S.mulVec w = v := by
    calc S.mulVec w
        = S.mulVec (σ.mulVec (S.mulVec v)) := by rw [hw_def]
      _ = (S * σ * S).mulVec v := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = (1 : Op n).mulVec v := by rw [hSσS]
      _ = v := Matrix.one_mulVec v
  -- (b) quadraticForm B w = quadraticForm A v
  have hBw_eq_Av : quadraticForm B w = quadraticForm A v := by
    rw [hB_def,
        Quantum.Operators.quadraticForm_sandwich_self_of_isHermitian hS_herm A w,
        hSw]
  -- (c) quadraticForm σ v = quadraticForm 1 w (equivalently, = w* w)
  have hσv_eq_1w : quadraticForm σ v = quadraticForm (1 : Op n) w := by
    calc quadraticForm σ v
        = quadraticForm σ (S.mulVec w) := by rw [hSw]
      _ = quadraticForm (S * σ * S) w := by
          rw [Quantum.Operators.quadraticForm_sandwich_self_of_isHermitian hS_herm σ w]
      _ = quadraticForm (1 : Op n) w := by rw [hSσS]
  -- Apply the PSD ≤ trace • 1 bound, then bridge to opLe
  have h_main : opLe B (Complex.ofReal t • (1 : Op n)) := by
    have h_mat_le :
        B ≤ (Complex.ofReal t : ℂ) • (1 : Op n) :=
      le_trace_re_smul_one_of_posSemidef hB_psd
    exact opLe_of_matrix_le h_mat_le
  -- Instantiate at w: (quadraticForm B w).re ≤ (quadraticForm (t • 1) w).re
  have h_w := h_main w
  -- Rewrite h_w's RHS: quadraticForm (t • 1) w = t * quadraticForm 1 w
  rw [quadraticForm_smul] at h_w
  -- Goal: (quadraticForm A v).re ≤ (quadraticForm (↑t • σ) v).re
  change (quadraticForm A v).re ≤ (quadraticForm ((Complex.ofReal t : ℂ) • σ) v).re
  rw [quadraticForm_smul, hσv_eq_1w, ← hBw_eq_Av]
  exact h_w

end Matrix.PosDef

end -- noncomputable section
