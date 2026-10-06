import QCryptLean.Quantum.Metrics.TraceNormHoelder

/-!
# Trace and trace-norm transport under partial-isometry conjugation

Generic (Matrix/Op-level, QKD-free) transport lemmas for conjugation `X ↦ V * X * Vᴴ`
by a rectangular matrix `V` that acts isometrically on the support of `X`, expressed by
the hypothesis `hV' : Vᴴ * V * X = X`.

## Main results

- `partialIsometry_extend_isometry` (L-extend): a rectangular partial isometry `V₀`
  (i.e. `V₀ᴴV₀` idempotent) into a target of dimension `≥` the source extends to a full
  isometry `V` (`Vᴴ * V = 1`) with `V * (V₀ᴴ * V₀) = V₀`.
- `trace_partialIsometry_conj`: `(V * X * Vᴴ).trace = X.trace` under `Vᴴ * V * X = X`.
- `traceNorm_partialIsometry_conj`: `traceNorm (V * X * Vᴴ) = traceNorm X` under
  `Vᴴ * V * X = X` and `X.IsHermitian`.
- `pow_mul_partialIsometry_conj`: `(V * X * Vᴴ) ^ k = V * X ^ k * Vᴴ` for `1 ≤ k`.
- `mul_self_conjTranspose_mul_of_hermitian`: right absorption `X * (Vᴴ * V) = X`.

The Hermitian transport `(V * X * Vᴴ).IsHermitian` of `X.IsHermitian` is exactly the
Mathlib lemma `Matrix.isHermitian_mul_mul_conjTranspose` instantiated at
`B := V`, `A := X`; cite it directly at call sites — it is deliberately NOT re-proved here.

## References

- Bhatia (1997) "Matrix Analysis", Section VII.3 (partial isometries).
- Watrous (2018) "Theory of Quantum Information", Section 1.1.2.
-/

open Quantum.Operators Matrix Quantum.Metrics
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics.TraceNormHoelder

open scoped Matrix.Norms.L2Operator

/-!
## The projector-completion core

For a Hermitian idempotent `R` on `Fin d`, the columns of the eigenvector unitary
with eigenvalue `0` assemble into an isometry `C` onto the kernel of `R`:
`Cᴴ * C = 1` and `C * Cᴴ = 1 - R`, with `(#columns : ℝ) = d - R.trace.re`.
-/

/-- Spectral complement factorization of a Hermitian idempotent: there is a
rectangular isometry `C` with `C * Cᴴ = 1 - R`, whose column count is
`d - tr R` (the co-rank of `R`). -/
private lemma projection_complement_isometry {d : ℕ}
    (R : Op d) (hR : R.IsHermitian) (hidem : R * R = R) :
    ∃ (k : ℕ) (C : Matrix (Fin d) (Fin k) ℂ),
      Cᴴ * C = 1 ∧ C * Cᴴ = 1 - R ∧ (k : ℝ) = d - R.trace.re := by
  classical
  -- Spectral data
  have h_spec := hR.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  set U : Op d := hR.eigenvectorUnitary.val with hU_def
  set μ : Fin d → ℝ := hR.eigenvalues with hμ_def
  set D : Op d := Matrix.diagonal (RCLike.ofReal ∘ μ) with hD_def
  have hU_l : Uᴴ * U = 1 := Unitary.coe_star_mul_self hR.eigenvectorUnitary
  have hU_r : U * Uᴴ = 1 := Unitary.coe_mul_star_self hR.eigenvectorUnitary
  have h_spec' : R = U * D * Uᴴ := h_spec
  -- Eigenvalues of a Hermitian idempotent are 0 or 1
  have hD_idem : D * D = D := by
    calc D * D
        = (Uᴴ * U) * D * ((Uᴴ * U) * D) * (Uᴴ * U) := by
          rw [hU_l]; simp only [Matrix.one_mul, Matrix.mul_one]
      _ = Uᴴ * (U * D * Uᴴ) * (U * D * Uᴴ) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * (R * R) * U := by rw [← h_spec']; simp only [Matrix.mul_assoc]
      _ = Uᴴ * (U * D * Uᴴ) * U := by rw [hidem, h_spec']
      _ = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = D := by rw [hU_l]; simp only [Matrix.one_mul, Matrix.mul_one]
  have hμ01 : ∀ i, μ i = 0 ∨ μ i = 1 := by
    intro i
    have h := Matrix.ext_iff.mpr hD_idem i i
    rw [hD_def, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_eq] at h
    simp only [Function.comp_apply] at h
    have h_real : μ i * μ i = μ i := by exact_mod_cast h
    have h_factor : μ i * (μ i - 1) = 0 := by nlinarith [h_real]
    rcases mul_eq_zero.mp h_factor with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by linarith)
  -- The zero-eigenvalue index set
  set s : Finset (Fin d) := Finset.univ.filter (fun i => μ i = 0) with hs_def
  set g : Fin s.card ≃o {x // x ∈ s} := s.orderIsoOfFin rfl with hg_def
  set C : Matrix (Fin d) (Fin s.card) ℂ :=
    Matrix.of (fun a j => U a ((g j : Fin d))) with hC_def
  have hg_mem : ∀ j, μ ((g j : Fin d)) = 0 := by
    intro j
    have hmem : (g j : Fin d) ∈ Finset.univ.filter (fun i => μ i = 0) := (g j).2
    exact (Finset.mem_filter.mp hmem).2
  -- Entry formula for U * diagonal v * Uᴴ
  have entry : ∀ (v : Fin d → ℂ) (a b : Fin d),
      (U * Matrix.diagonal v * Uᴴ) a b = ∑ i, U a i * v i * star (U b i) := by
    intro v a b
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  refine ⟨s.card, C, ?_, ?_, ?_⟩
  · -- Cᴴ * C = 1
    ext i j
    have h1 : (Cᴴ * C) i j = (Uᴴ * U) ((g i : Fin d)) ((g j : Fin d)) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hC_def]
    rw [h1, hU_l]
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.one_apply_ne, Matrix.one_apply_ne h]
      intro hc
      exact h (g.injective (Subtype.coe_injective hc))
  · -- C * Cᴴ = 1 - R
    have h_comp : (1 : Op d) - R
        = U * Matrix.diagonal (fun i => 1 - ((RCLike.ofReal ∘ μ) i : ℂ)) * Uᴴ := by
      calc (1 : Op d) - R
          = U * 1 * Uᴴ - U * D * Uᴴ := by rw [Matrix.mul_one, hU_r, ← h_spec']
        _ = U * (1 - D) * Uᴴ := by rw [← Matrix.sub_mul, ← Matrix.mul_sub]
        _ = U * Matrix.diagonal (fun i => 1 - ((RCLike.ofReal ∘ μ) i : ℂ)) * Uᴴ := by
            rw [hD_def, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    ext a b
    rw [h_comp, entry]
    have lhs_eq : (C * Cᴴ) a b
        = ∑ j : Fin s.card, U a ((g j : Fin d)) * star (U b ((g j : Fin d))) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hC_def]
    rw [lhs_eq]
    have lhs_eq2 : ∑ j : Fin s.card, U a ((g j : Fin d)) * star (U b ((g j : Fin d)))
        = ∑ i ∈ s, U a i * star (U b i) := by
      rw [← Finset.sum_coe_sort s (fun i => U a i * star (U b i))]
      exact Fintype.sum_equiv g.toEquiv _ _ (fun j => rfl)
    rw [lhs_eq2, hs_def, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hμ01 i with h | h
    · rw [if_pos h]
      simp [h]
    · rw [if_neg (by rw [h]; norm_num)]
      simp [h]
  · -- (s.card : ℝ) = d - R.trace.re
    have htrace : R.trace = ∑ i, ((μ i : ℝ) : ℂ) := by
      calc R.trace = (U * D * Uᴴ).trace := by rw [← h_spec']
        _ = (Uᴴ * U * D).trace := by rw [Matrix.trace_mul_cycle]
        _ = D.trace := by rw [hU_l, Matrix.one_mul]
        _ = ∑ i, ((μ i : ℝ) : ℂ) := by rw [hD_def, Matrix.trace_diagonal]; rfl
    have htr_re : R.trace.re = ∑ i, μ i := by
      rw [htrace, ← Complex.ofReal_sum, Complex.ofReal_re]
    have hsum : ∑ i, μ i
        = ((Finset.univ.filter (fun i => ¬ μ i = 0)).card : ℝ) := by
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases hμ01 i with h | h
      · simp [h]
      · rw [h]; norm_num
    have hcards : s.card + (Finset.univ.filter (fun i => ¬ μ i = 0)).card = d := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin d))) (p := fun i => μ i = 0)
      rw [Finset.card_univ, Fintype.card_fin] at h
      rw [hs_def]
      exact h
    have hcards' : (s.card : ℝ) + ((Finset.univ.filter (fun i => ¬ μ i = 0)).card : ℝ)
        = (d : ℝ) := by exact_mod_cast hcards
    rw [htr_re, hsum]
    linarith

/-- **L-extend**: a rectangular partial isometry `V₀ : Fin p × Fin q` (i.e. `V₀ᴴV₀`
idempotent) with `q ≤ p` extends to a full isometry `V` (`Vᴴ * V = 1`) agreeing with
`V₀` on the initial support: `V * (V₀ᴴ * V₀) = V₀`. -/
theorem partialIsometry_extend_isometry {p q : ℕ} [NeZero p] [NeZero q]
    (V₀ : Matrix (Fin p) (Fin q) ℂ)
    (hproj : (V₀ᴴ * V₀) * (V₀ᴴ * V₀) = V₀ᴴ * V₀)
    (hdim : q ≤ p) :
    ∃ V : Matrix (Fin p) (Fin q) ℂ, Vᴴ * V = 1 ∧ V * (V₀ᴴ * V₀) = V₀ := by
  classical
  set P : Op q := V₀ᴴ * V₀ with hP_def
  have hP_herm : P.IsHermitian := by
    rw [hP_def, Matrix.IsHermitian, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  -- V₀ absorbs its initial projection: V₀ * P = V₀
  have hV₀P : V₀ * P = V₀ := by
    have hexp : (V₀ * P - V₀)ᴴ * (V₀ * P - V₀) = P * P * P - P * P - P * P + P := by
      have hct : (V₀ * P - V₀)ᴴ = P * V₀ᴴ - V₀ᴴ := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hP_herm.eq]
      rw [hct, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
      have e1 : P * V₀ᴴ * (V₀ * P) = P * P * P := by
        rw [hP_def]; simp only [Matrix.mul_assoc]
      have e2 : P * V₀ᴴ * V₀ = P * P := by
        rw [hP_def]; simp only [Matrix.mul_assoc]
      have e3 : V₀ᴴ * (V₀ * P) = P * P := by
        rw [hP_def]; simp only [Matrix.mul_assoc]
      have e4 : V₀ᴴ * V₀ = P := hP_def.symm
      rw [e1, e2, e3, e4]
      abel
    have h0 : (V₀ * P - V₀)ᴴ * (V₀ * P - V₀) = 0 := by
      rw [hexp, hproj, hproj]
      abel
    have h1 := Matrix.conjTranspose_mul_self_eq_zero.mp h0
    exact sub_eq_zero.mp h1
  -- The final projection Q := V₀ * V₀ᴴ
  set Q : Op p := V₀ * V₀ᴴ with hQ_def
  have hQ_herm : Q.IsHermitian := by
    rw [hQ_def, Matrix.IsHermitian, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hQ_idem : Q * Q = Q := by
    calc Q * Q = V₀ * (V₀ᴴ * V₀) * V₀ᴴ := by
          rw [hQ_def]; simp only [Matrix.mul_assoc]
      _ = V₀ * V₀ᴴ := by rw [← hP_def, hV₀P]
      _ = Q := hQ_def.symm
  -- Complement isometries for P and Q
  obtain ⟨kP, C, hCC, hCCH, hkP⟩ := projection_complement_isometry P hP_herm hproj
  obtain ⟨kQ, DQ, hDD, hDDH, hkQ⟩ := projection_complement_isometry Q hQ_herm hQ_idem
  -- Rank bookkeeping: kP ≤ kQ from tr P = tr Q and q ≤ p
  have htr : P.trace = Q.trace := by
    rw [hP_def, hQ_def]; exact Matrix.trace_mul_comm V₀ᴴ V₀
  have hkPQ : kP ≤ kQ := by
    have h : (kP : ℝ) ≤ (kQ : ℝ) := by
      rw [hkP, hkQ, ← htr]
      have : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hdim
      linarith
    exact_mod_cast h
  -- The kernel-matching embedding
  set E : Matrix (Fin kQ) (Fin kP) ℂ :=
    Matrix.of (fun a b => if a = Fin.castLE hkPQ b then 1 else 0) with hE_def
  have hEE : Eᴴ * E = 1 := by
    ext i j
    have h1 : (Eᴴ * E) i j
        = ∑ a, (if a = Fin.castLE hkPQ i then (1 : ℂ) else 0)
            * (if a = Fin.castLE hkPQ j then (1 : ℂ) else 0) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hE_def, apply_ite (star : ℂ → ℂ)]
    rw [h1]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (Fin.castLE hkPQ i)
      (fun a => if a = Fin.castLE hkPQ j then (1 : ℂ) else 0)]
    simp [Matrix.one_apply, Fin.castLE_inj]
  -- The complement piece W
  set W : Matrix (Fin p) (Fin q) ℂ := DQ * E * Cᴴ with hW_def
  have hWW : Wᴴ * W = 1 - P := by
    calc Wᴴ * W = C * Eᴴ * (DQᴴ * DQ) * E * Cᴴ := by
          rw [hW_def]
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
      _ = C * (Eᴴ * E) * Cᴴ := by
          rw [hDD]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = C * Cᴴ := by rw [hEE, Matrix.mul_one]
      _ = 1 - P := hCCH
  have hQD : Q * DQ = 0 := by
    have h1 : (1 - Q) * DQ = DQ := by
      rw [← hDDH, Matrix.mul_assoc, hDD, Matrix.mul_one]
    rw [Matrix.sub_mul, Matrix.one_mul] at h1
    exact sub_eq_self.mp h1
  have hQW : Q * W = 0 := by
    rw [hW_def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQD, Matrix.zero_mul,
      Matrix.zero_mul]
  have hV₀HW : V₀ᴴ * W = 0 := by
    have hV₀Q : V₀ᴴ * Q = V₀ᴴ := by
      calc V₀ᴴ * Q = (V₀ᴴ * V₀) * V₀ᴴ := by
            rw [hQ_def]; simp only [Matrix.mul_assoc]
        _ = (V₀ * P)ᴴ := by
            rw [← hP_def, Matrix.conjTranspose_mul, hP_herm.eq]
        _ = V₀ᴴ := by rw [hV₀P]
    calc V₀ᴴ * W = (V₀ᴴ * Q) * W := by rw [hV₀Q]
      _ = V₀ᴴ * (Q * W) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hQW, Matrix.mul_zero]
  have hWV₀ : Wᴴ * V₀ = 0 := by
    have h := congrArg Matrix.conjTranspose hV₀HW
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h
    exact h
  have hWP : W * P = 0 := by
    have h0 : (W * P)ᴴ * (W * P) = 0 := by
      calc (W * P)ᴴ * (W * P)
          = P * (Wᴴ * W) * P := by
            rw [Matrix.conjTranspose_mul, hP_herm.eq]
            simp only [Matrix.mul_assoc]
        _ = P * (1 - P) * P := by rw [hWW]
        _ = (P - P * P) * P := by rw [Matrix.mul_sub, Matrix.mul_one]
        _ = 0 := by rw [hproj, sub_self, Matrix.zero_mul]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp h0
  -- Assemble V := V₀ + W
  refine ⟨V₀ + W, ?_, ?_⟩
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      hV₀HW, hWV₀, hWW, ← hP_def]
    abel
  · rw [Matrix.add_mul, hV₀P, hWP, add_zero]

/-!
## The hV′ transport lemmas
-/

/-- Right absorption: if `Vᴴ * V * X = X` and `X` is Hermitian, then also
`X * (Vᴴ * V) = X`. -/
lemma mul_self_conjTranspose_mul_of_hermitian {m n : ℕ}
    (V : Matrix (Fin m) (Fin n) ℂ) (X : Op n)
    (hV' : Vᴴ * V * X = X) (hX : X.IsHermitian) :
    X * (Vᴴ * V) = X := by
  have h := congrArg Matrix.conjTranspose hV'
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX.eq] at h
  exact h

/-- Trace transport under partial-isometry conjugation:
`tr (V * X * Vᴴ) = tr (Vᴴ * V * X) = tr X` by cyclicity and the hypothesis. -/
theorem trace_partialIsometry_conj {m n : ℕ}
    (V : Matrix (Fin m) (Fin n) ℂ) (X : Op n)
    (hV' : Vᴴ * V * X = X) :
    (V * X * Vᴴ).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, hV']

/-- Power identity under partial-isometry conjugation:
`(V * X * Vᴴ) ^ k = V * X ^ k * Vᴴ` for `k ≥ 1`, since each internal `Vᴴ * V`
is absorbed by `X` via `hV'`. -/
lemma pow_mul_partialIsometry_conj {m n : ℕ}
    (V : Matrix (Fin m) (Fin n) ℂ) (X : Op n)
    (hV' : Vᴴ * V * X = X) (k : ℕ) (hk : 1 ≤ k) :
    (V * X * Vᴴ) ^ k = V * (X ^ k) * Vᴴ := by
  induction k, hk using Nat.le_induction with
  | base => simp [pow_one]
  | succ k hk ih =>
    rw [pow_succ, ih, pow_succ]
    calc V * X ^ k * Vᴴ * (V * X * Vᴴ)
        = V * X ^ k * (Vᴴ * V * X) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * X ^ k * X * Vᴴ := by rw [hV']
      _ = V * (X ^ k * X) * Vᴴ := by simp only [Matrix.mul_assoc]

/-- If `P * B = B` for PSD `B`, then `P` also absorbs the square root:
`P * CFC.sqrt B = CFC.sqrt B`. (`(1-P) √B √B (1-P)ᴴ = (1-P) B (1-P)ᴴ = 0`.) -/
private lemma mul_sqrt_of_mul_self {n : ℕ}
    (P B : Op n) (hB : B.PosSemidef) (hPB : P * B = B) :
    P * CFC.sqrt B = CFC.sqrt B := by
  have hS_psd : (CFC.sqrt B).PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hSS : CFC.sqrt B * CFC.sqrt B = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have h0 : ((1 - P) * CFC.sqrt B) * ((1 - P) * CFC.sqrt B)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, hS_psd.isHermitian.eq]
    calc (1 - P) * CFC.sqrt B * (CFC.sqrt B * (1 - P)ᴴ)
        = ((1 - P) * (CFC.sqrt B * CFC.sqrt B)) * (1 - P)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = ((1 - P) * B) * (1 - P)ᴴ := by rw [hSS]
      _ = 0 := by
          rw [Matrix.sub_mul, Matrix.one_mul, hPB, sub_self, Matrix.zero_mul]
  have h1 := Matrix.self_mul_conjTranspose_eq_zero.mp h0
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
  exact h1.symm

/-- Square roots commute with conjugation by a partial isometry that is isometric on
the support of `B`: `√(V B Vᴴ) = V √B Vᴴ` under `Vᴴ * V * B = B`. -/
private lemma cfc_sqrt_partialIsometry_conj {m n : ℕ}
    (V : Matrix (Fin m) (Fin n) ℂ) (B : Op n)
    (hB : B.PosSemidef) (hVB : Vᴴ * V * B = B) :
    CFC.sqrt (V * B * Vᴴ) = V * CFC.sqrt B * Vᴴ := by
  have hPS : Vᴴ * V * CFC.sqrt B = CFC.sqrt B :=
    mul_sqrt_of_mul_self (Vᴴ * V) B hB hVB
  refine CFC.sqrt_unique ?_ ?_
  · calc (V * CFC.sqrt B * Vᴴ) * (V * CFC.sqrt B * Vᴴ)
        = V * (CFC.sqrt B * (Vᴴ * V * CFC.sqrt B)) * Vᴴ := by
          simp only [Matrix.mul_assoc]
      _ = V * (CFC.sqrt B * CFC.sqrt B) * Vᴴ := by rw [hPS]
      _ = V * B * Vᴴ := by rw [CFC.sqrt_mul_sqrt_self B hB.nonneg]
  · rw [Matrix.nonneg_iff_posSemidef]
    exact ((CFC.sqrt_nonneg B).posSemidef).mul_mul_conjTranspose_same V

/-- `traceNorm X = (tr √(Xᴴ X)).re` (local re-derivation of the standard formula). -/
private lemma traceNorm_eq_trace_sqrt_gram {d : ℕ} [NeZero d]
    (X : Op d) :
    traceNorm X = (Matrix.trace (CFC.sqrt (Xᴴ * X))).re := by
  have hP_psd : (CFC.sqrt (Xᴴ * X)).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have h1 : traceNorm (CFC.sqrt (Xᴴ * X)) = traceNorm X := by
    apply traceNorm_eq_of_conjTranspose_mul_self_eq
    rw [hP_psd.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self (Xᴴ * X) (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  rw [← h1, traceNorm_hermitian_eq _ hP_psd.isHermitian]
  exact Quantum.Metrics.traceNormHermitian_of_posSemidef
    _ hP_psd

/-- **Trace-norm transport under partial-isometry conjugation**:
`‖V X Vᴴ‖₁ = ‖X‖₁` whenever `V` is isometric on the support of the Hermitian `X`
(`Vᴴ * V * X = X`). Partial-isometry generalization of the
`traceNorm_isometry_mul_left`. -/
theorem traceNorm_partialIsometry_conj {m n : ℕ} [NeZero m] [NeZero n]
    (V : Matrix (Fin m) (Fin n) ℂ) (X : Op n)
    (hV' : Vᴴ * V * X = X) (hX : X.IsHermitian) :
    Quantum.Metrics.traceNorm (V * X * Vᴴ) = Quantum.Metrics.traceNorm X := by
  have hB : (Xᴴ * X).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  have hVB : Vᴴ * V * (Xᴴ * X) = Xᴴ * X := by
    calc Vᴴ * V * (Xᴴ * X) = (Vᴴ * V * Xᴴ) * X := by simp only [Matrix.mul_assoc]
      _ = (Vᴴ * V * X) * X := by rw [hX.eq]
      _ = X * X := by rw [hV']
      _ = Xᴴ * X := by rw [hX.eq]
  have hgram : (V * X * Vᴴ)ᴴ * (V * X * Vᴴ) = V * (Xᴴ * X) * Vᴴ := by
    have hct : (V * X * Vᴴ)ᴴ = V * Xᴴ * Vᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    calc (V * X * Vᴴ)ᴴ * (V * X * Vᴴ)
        = (V * Xᴴ * Vᴴ) * (V * X * Vᴴ) := by rw [hct]
      _ = V * (Xᴴ * (Vᴴ * V * X)) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * (Xᴴ * X) * Vᴴ := by rw [hV']
  rw [traceNorm_eq_trace_sqrt_gram (V * X * Vᴴ), traceNorm_eq_trace_sqrt_gram X,
    hgram, cfc_sqrt_partialIsometry_conj V (Xᴴ * X) hB hVB]
  congr 1
  calc (V * CFC.sqrt (Xᴴ * X) * Vᴴ).trace
      = (Vᴴ * V * CFC.sqrt (Xᴴ * X)).trace := by rw [Matrix.trace_mul_cycle]
    _ = (CFC.sqrt (Xᴴ * X)).trace := by
        rw [mul_sqrt_of_mul_self (Vᴴ * V) (Xᴴ * X) hB hVB]

end Quantum.Metrics.TraceNormHoelder

end
