import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.DataProcessing.ProjectiveDPI

/-!
# Naimark Dilation and Measurement Monotonicity — tensor-product projectors, isometry, DPI

Naimark's dilation theorem: every POVM can be realized as a projective measurement
on a larger Hilbert space. Combined with isometric invariance and the projective DPI,
this gives the data processing inequality for measurements.

## Main definitions
- `naimarkProjector`: projector `I_n ⊗ |y⟩⟨y|` in `(divNat, modNat)` coordinates
- `naimarkIsometry`: Naimark isometry in the same interleaved `(p, y)` ordering

## Main statements
- `naimark_dilation`: POVM → projective measurement via isometry
- `measurement_monotonicity_with_support`: measurement DPI under quantum support containment
- `measurement_monotonicity`: D_KL(measurement ‖ ρ,σ) ≤ D(ρ ‖ σ)
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy

/-- Projector onto the ancilla outcome `y` in `ℂⁿ ⊗ ℂᵐ ≅ ℂ^(n*m)`.

    In the `(p, y)` coordinates encoded by `Fin.divNat` and `Fin.modNat`, this is
    the tensor-product projector `I_n ⊗ |y⟩⟨y|`. The nonzero rows and columns are
    indexed by `p * m + y`, i.e. by the interleaved flattened tensor-product
    ordering. -/
def naimarkProjector (n m : ℕ) (y : Fin m) : Op (n * m) :=
  fun i j => if i.modNat = y ∧ j.modNat = y ∧ i.divNat = j.divNat
    then 1 else 0

private lemma ite_and_mul_ite_and_zero {c₁ c₂ : Prop}
    [Decidable c₁] [Decidable c₂] (h : ¬c₁ ∨ ¬c₂) :
    (if c₁ then (1 : ℂ) else 0) * (if c₂ then 1 else 0) = 0 := by
  rcases h with h | h <;> simp [h]

/-- Block projectors are idempotent: P_y² = P_y. -/
lemma naimarkProjector_idem (n m : ℕ) [NeZero m] (y : Fin m) :
    naimarkProjector n m y * naimarkProjector n m y =
      naimarkProjector n m y := by
  ext i j
  simp only [Matrix.mul_apply, naimarkProjector]
  by_cases h : i.modNat = y ∧ j.modNat = y ∧ i.divNat = j.divNat
  · rw [if_pos h]
    obtain ⟨hi, hj, hdiv⟩ := h
    rw [Finset.sum_eq_single (i.divNat.mkDivMod y)]
    · rw [if_pos ⟨hi, Fin.modNat_mkDivMod i.divNat y,
            (Fin.divNat_mkDivMod i.divNat y).symm⟩,
          if_pos ⟨Fin.modNat_mkDivMod i.divNat y, hj,
            by rw [Fin.divNat_mkDivMod, hdiv]⟩]
      simp
    · intro b _ hb
      apply ite_and_mul_ite_and_zero
      by_contra hc; push Not at hc
      obtain ⟨⟨_, hbm, hbd⟩, _⟩ := hc
      exact hb (by rw [← Fin.divNat_mkDivMod_modNat b, hbm, hbd])
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero; intro k _
    apply ite_and_mul_ite_and_zero
    by_contra hc; push Not at hc
    obtain ⟨⟨h1a, _, h1c⟩, ⟨_, h2b, h2c⟩⟩ := hc
    exact h ⟨h1a, h2b, h1c.trans h2c⟩

/-- Block projectors are Hermitian: P_y† = P_y.
    The condition (i.modNat = y ∧ j.modNat = y ∧ i.divNat = j.divNat) is symmetric
    in (i,j) and entries are real (0 or 1). -/
lemma naimarkProjector_herm (n m : ℕ) [NeZero m] (y : Fin m) :
    (naimarkProjector n m y).conjTranspose = naimarkProjector n m y := by
  ext i j
  simp only [conjTranspose_apply, naimarkProjector]
  split_ifs with h1 h2 h2
  · simp
  · exfalso; exact h2 ⟨h1.2.1, h1.1, h1.2.2.symm⟩
  · exfalso; exact h1 ⟨h2.2.1, h2.1, h2.2.2.symm⟩
  · simp

/-- Block projectors are mutually orthogonal: P_{y₁} P_{y₂} = 0 for y₁ ≠ y₂. -/
lemma naimarkProjector_ortho (n m : ℕ) [NeZero m]
    (y₁ y₂ : Fin m) (h : y₁ ≠ y₂) :
    naimarkProjector n m y₁ * naimarkProjector n m y₂ = 0 := by
  ext i j
  simp only [Matrix.mul_apply, naimarkProjector, Matrix.zero_apply]
  apply Finset.sum_eq_zero; intro k _
  by_cases h1 : i.modNat = y₁ ∧ k.modNat = y₁ ∧ i.divNat = k.divNat <;>
  by_cases h2 : k.modNat = y₂ ∧ j.modNat = y₂ ∧ k.divNat = j.divNat <;>
    simp_all

/-- Block projectors sum to identity: Σ_y P_y = I. -/
lemma naimarkProjector_complete (n m : ℕ) [NeZero m] :
    ∑ y : Fin m, naimarkProjector n m y = 1 := by
  ext i j
  simp only [Matrix.one_apply]
  rw [Matrix.sum_apply]
  simp only [naimarkProjector]
  by_cases hij : i = j
  · subst hij; simp only [ite_true]
    rw [Finset.sum_eq_single i.modNat]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp only [hij, ite_false]
    apply Finset.sum_eq_zero; intro y _
    split
    · next h =>
      exfalso; exact hij (by rw [← Fin.divNat_mkDivMod_modNat i,
        ← Fin.divNat_mkDivMod_modNat j, h.1, h.2.1, h.2.2])
    · rfl

/-- Naimark isometry in the interleaved `(p, y)` tensor-product ordering.

    For POVM `{M_y}` on `ℂⁿ`, this maps `ℂⁿ → ℂ^(n*m)` by
    `V|ψ⟩ = Σ_y (√M_y |ψ⟩) ⊗ |y⟩`.

    In the flattened basis, rows are indexed by `(i.divNat, i.modNat) = (p, y)`,
    so this is the standard tensor-product ordering in flattened coordinates.
    Uses `CFC.sqrt` for the matrix square root. -/
def naimarkIsometry {n m : ℕ}
    (M : InfoTheory.Measurement.POVM n m) :
    Matrix (Fin (n * m)) (Fin n) ℂ :=
  letI : PartialOrder (Matrix (Fin n) (Fin n) ℂ) := Matrix.instPartialOrder
  letI : StarOrderedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instNonnegSpectrumClass
  fun i j =>
    (CFC.sqrt (M.elements i.modNat)) i.divNat j

private lemma fpfe_divNat {n m : ℕ} (z : Fin n × Fin m) :
    (finProdFinEquiv z).divNat = z.1 := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv z)
  rw [Equiv.symm_apply_apply] at h
  exact (congr_arg Prod.fst h).symm

private lemma fpfe_modNat {n m : ℕ} (z : Fin n × Fin m) :
    (finProdFinEquiv z).modNat = z.2 := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv z)
  rw [Equiv.symm_apply_apply] at h
  exact (congr_arg Prod.snd h).symm

/-- Componentwise square root identity for POVM elements:
    ∑ p, (√M_y)ₚₐ* · (√M_y)ₚᵦ = (M_y)ₐᵦ. -/
private lemma povm_sqrt_inner_sum {n m : ℕ}
    (M : InfoTheory.Measurement.POVM n m) (y : Fin m) (a b : Fin n) :
    letI : PartialOrder (Op n) := Matrix.instPartialOrder
    letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
    letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
    ∑ p : Fin n, star (CFC.sqrt (M.elements y) p a) *
      CFC.sqrt (M.elements y) p b = (M.elements y) a b := by
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  have h1 : ∑ p : Fin n, star (CFC.sqrt (M.elements y) p a) *
      CFC.sqrt (M.elements y) p b =
      ((CFC.sqrt (M.elements y))ᴴ * CFC.sqrt (M.elements y)) a b := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h1, (CFC.sqrt_nonneg (a := M.elements y)).posSemidef.isHermitian,
    CFC.sqrt_mul_sqrt_self _
      (InfoTheory.Measurement.povm_element_is_mathlib_psd M y).nonneg]

/-- V†V = I for the Naimark isometry, using POVM completeness.

    (V†V)(a,b) = Σ_y (√M_y† · √M_y)(a,b) = Σ_y M_y(a,b) = I(a,b)

    This requires: √M_y is Hermitian and (√M_y)² = M_y. -/
lemma naimarkIsometry_isometry {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m) :
    (naimarkIsometry M).conjTranspose * (naimarkIsometry M) = 1 := by
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  ext a b
  simp only [naimarkIsometry, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.one_apply]
  -- Reindex: Fin(n*m) → Fin m × Fin n
  have hreindex : ∀ (f : Fin (n * m) → ℂ),
      ∑ x, f x = ∑ y : Fin m, ∑ p : Fin n,
        f (finProdFinEquiv (p, y)) := by
    intro f
    have h1 : ∑ x, f x = ∑ z : Fin n × Fin m, f (finProdFinEquiv z) :=
      (Fintype.sum_equiv finProdFinEquiv _ _ fun x => rfl).symm
    rw [h1, Fintype.sum_prod_type, Finset.sum_comm]
  rw [hreindex]
  simp_rw [fun p y => fpfe_divNat (n := n) (m := m) (p, y),
    fun p y => fpfe_modNat (n := n) (m := m) (p, y)]
  simp_rw [povm_sqrt_inner_sum M]
  -- ∑ y, M_y(a,b) = 1(a,b) by POVM completeness
  convert (show (∑ y : Fin m, M.elements y) a b =
    (if a = b then 1 else 0) from by rw [M.complete]; rfl) using 1
  rw [Matrix.sum_apply]

private lemma fin_eq_of_divNat_modNat {n m : ℕ} (i j : Fin (n * m))
    (h1 : i.divNat = j.divNat) (h2 : i.modNat = j.modNat) : i = j := by
  rw [← Fin.divNat_mkDivMod_modNat i, ← Fin.divNat_mkDivMod_modNat j, h1, h2]

/-- Block extraction: V† P_y V = M_y.
    This is the key identity for the Naimark trace proof. -/
private lemma naimark_block_extract {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m) (y : Fin m) :
    (naimarkIsometry M).conjTranspose * naimarkProjector n m y *
      naimarkIsometry M = M.elements y := by
  letI : PartialOrder (Op n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Op n) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Op n) := Matrix.instNonnegSpectrumClass
  ext a b
  simp only [naimarkIsometry, naimarkProjector,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  -- Inner sum collapses: P_y(x_1, x) is nonzero only when
  -- x_1.modNat = y, x.modNat = y, x_1.divNat = x.divNat (forcing x_1 = x)
  have hinner : ∀ x : Fin (n * m),
    (∑ x_1 : Fin (n * m),
      star (CFC.sqrt (M.elements x_1.modNat) x_1.divNat a) *
        if x_1.modNat = y ∧ x.modNat = y ∧ x_1.divNat = x.divNat
        then 1 else 0) =
    if x.modNat = y then
      star (CFC.sqrt (M.elements y) x.divNat a)
    else 0 := by
    intro x
    by_cases hx : x.modNat = y
    · simp only [hx, true_and, ite_true]
      rw [Finset.sum_eq_single x]
      · simp [hx]
      · intro x_1 _ hne
        by_cases h : x_1.modNat = y ∧ x_1.divNat = x.divNat
        · exfalso; apply hne
          exact fin_eq_of_divNat_modNat x_1 x h.2 (h.1.trans hx.symm)
        · simp [h]
      · simp
    · simp only [hx, false_and, and_false, ite_false, mul_zero,
        Finset.sum_const_zero]
  simp_rw [hinner]
  -- Merge: (if cond then a else 0) * b = if cond then a*b else 0
  have hsplit : ∀ x : Fin (n * m),
    (if x.modNat = y then
      star (CFC.sqrt (M.elements y) x.divNat a) else 0) *
    CFC.sqrt (M.elements x.modNat) x.divNat b =
    if x.modNat = y then
      star (CFC.sqrt (M.elements y) x.divNat a) *
      CFC.sqrt (M.elements y) x.divNat b
    else 0 := by
    intro x; by_cases hx : x.modNat = y <;> simp [hx]
  simp_rw [hsplit]
  -- Reindex via finProdFinEquiv and filter to single y
  rw [show ∑ x : Fin (n * m), _ = ∑ p : Fin n,
    star (CFC.sqrt (M.elements y) p a) *
    CFC.sqrt (M.elements y) p b from by
    trans (∑ z : Fin n × Fin m,
      if z.2 = y then
        star (CFC.sqrt (M.elements y) z.1 a) *
        CFC.sqrt (M.elements y) z.1 b
      else 0)
    · exact (Fintype.sum_equiv finProdFinEquiv _ _ fun z => by
        simp only [fpfe_divNat, fpfe_modNat]).symm
    · rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]]
  exact povm_sqrt_inner_sum M y a b

/-- The Naimark trace identity: Tr(P_y V ρ V†) = Tr(M_y ρ). -/
lemma naimarkIsometry_trace {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m)
    (ρ : DensityOp n) (y : Fin m) :
    ((naimarkProjector n m y *
      (naimarkIsometry M * ρ.toOp *
        (naimarkIsometry M).conjTranspose)).trace).re =
      M.prob ρ y := by
  -- Use trace cyclicity: Tr(P * V * ρ * Vᴴ) = Tr(Vᴴ * P * V * ρ)
  have hcycl : (naimarkProjector n m y *
      (naimarkIsometry M * ρ.toOp *
        (naimarkIsometry M).conjTranspose)).trace =
    ((naimarkIsometry M).conjTranspose * naimarkProjector n m y *
      naimarkIsometry M * ρ.toOp).trace := by
    have h1 : naimarkProjector n m y *
      (naimarkIsometry M * ρ.toOp * (naimarkIsometry M).conjTranspose) =
      (naimarkProjector n m y * naimarkIsometry M * ρ.toOp) *
        (naimarkIsometry M).conjTranspose := by
      simp [Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [hcycl, naimark_block_extract]
  rfl

/-- Naimark dilation theorem: every POVM can be realized as a projective
    measurement on a larger Hilbert space via an isometric embedding.

    For a POVM M with m outcomes on ℂⁿ, there exists:
    - An isometry V : ℂⁿ → ℂⁿᵐ (satisfying V†V = Iₙ)
    - Projectors P_y on ℂⁿᵐ (orthogonal, complete, idempotent)
    such that Tr(M_y ρ) = Tr(P_y V ρ V†) for all states ρ.

    **Proof**: Uses the explicit interleaved tensor-product projectors
    `I_n ⊗ |y⟩⟨y|` together with the matrix square root isometry. -/
lemma naimark_dilation {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m) :
    ∃ (V : Matrix (Fin (n * m)) (Fin n) ℂ) (P : Fin m → Op (n * m)),
      V.conjTranspose * V = 1 ∧
      (∀ y, P y * P y = P y) ∧
      (∀ y, (P y).conjTranspose = P y) ∧
      (∀ y₁ y₂, y₁ ≠ y₂ → P y₁ * P y₂ = 0) ∧
      (∑ y, P y = 1) ∧
      (∀ (ρ : DensityOp n) (y : Fin m),
        ((P y * (V * ρ.toOp * V.conjTranspose)).trace).re =
          M.prob ρ y) :=
  ⟨naimarkIsometry M, naimarkProjector n m,
   naimarkIsometry_isometry M,
   naimarkProjector_idem n m,
   naimarkProjector_herm n m,
   naimarkProjector_ortho n m,
   naimarkProjector_complete n m,
   naimarkIsometry_trace M⟩

/-- Support-conditioned measurement monotonicity in the real-valued finite case.

    Under the explicit support hypothesis
    `∀ j, eigenvaluesOf σ j = 0 → diagonalOfRhoInSigmaBasis ρ σ j = 0`,
    the real-valued measurement KL expression `measurementKLDivReal M ρ σ` is
    bounded by `relativeEntropyReal ρ σ`.

    This is the finite/support branch used later in the unconditional ENNReal
    theorem `measurement_monotonicity`; it is not itself the hypothesis-free
    CPTP monotonicity statement. -/
theorem measurement_monotonicity_with_support {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m) (ρ σ : DensityOp n)
    (h_support : ∀ j, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ j = 0 →
      diagonalOfRhoInSigmaBasis ρ σ j = 0) :
    measurementKLDivReal M ρ σ ≤ relativeEntropyReal ρ σ := by
  -- Step 1: Get Naimark dilation
  obtain ⟨V, P, hV, hP_proj, hP_herm, hP_ortho, hP_complete, hP_prob⟩ := naimark_dilation M
  -- Step 2: NeZero instance for extended space
  haveI : NeZero (n * m) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne m)⟩
  -- Step 3: Construct extended density operators
  let ρ' := DensityOp.isometryEmbed V hV ρ
  let σ' := DensityOp.isometryEmbed V hV σ
  -- Step 4: Support condition cascades through isometric embedding as kernel containment
  have h_ker := ker_sigma_sub_ker_rho_of_eigenvalue_support ρ σ h_support
  have h_ker' : ∀ v, σ'.toOp.mulVec v = 0 → ρ'.toOp.mulVec v = 0 := by
    exact kernel_containment_isometry_embed V hV ρ σ h_ker
  -- Step 5: measurementKLDiv equals projective KL on extended space
  have hρ'_toOp : ρ'.toOp = V * ρ.toOp * V.conjTranspose := rfl
  have hσ'_toOp : σ'.toOp = V * σ.toOp * V.conjTranspose := rfl
  have hρ_eq : ∀ y, ((P y * ρ'.toOp).trace).re = M.prob ρ y := by
    intro y; rw [hρ'_toOp]; exact hP_prob ρ y
  have hσ_eq : ∀ y, ((P y * σ'.toOp).trace).re = M.prob σ y := by
    intro y; rw [hσ'_toOp]; exact hP_prob σ y
  have h_kl_eq : measurementKLDivReal M ρ σ =
      ∑ y : Fin m,
        if ((P y * ρ'.toOp).trace).re = 0 then 0
        else ((P y * ρ'.toOp).trace).re *
          Real.log (((P y * ρ'.toOp).trace).re / ((P y * σ'.toOp).trace).re) := by
    unfold measurementKLDivReal
    apply Finset.sum_congr rfl; intro y _
    rw [hρ_eq y, hσ_eq y]
  -- Step 6: Chain the inequalities
  calc measurementKLDivReal M ρ σ
      = ∑ y : Fin m,
          if ((P y * ρ'.toOp).trace).re = 0 then 0
          else ((P y * ρ'.toOp).trace).re *
            Real.log (((P y * ρ'.toOp).trace).re / ((P y * σ'.toOp).trace).re) := h_kl_eq
    _ ≤ relativeEntropyReal ρ' σ' :=
        projective_measurement_dpi_of_ker_sub P hP_proj hP_herm hP_ortho hP_complete ρ' σ' h_ker'
    _ = relativeEntropyReal ρ σ :=
        relativeEntropyReal_isometry_invariance V hV ρ σ

/-- Quantum support transfers zero measurement probabilities.

    If Tr(M_y σ) = 0 (p_σ(y) = 0) and quantum support holds (ker σ ⊆ ker ρ),
    then Tr(M_y ρ) = 0 (p_ρ(y) = 0). -/
private lemma prob_zero_of_quantum_support_and_sigma_prob_zero {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m) (ρ σ : DensityOp n)
    (h_q_supp : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0)
    (y : Fin m) (hy_σ : M.prob σ y = 0) : M.prob ρ y = 0 := by
  obtain ⟨V, P, hV, hP_proj, hP_herm, hP_ortho, hP_complete, hP_prob⟩ := naimark_dilation M
  haveI : NeZero (n * m) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne m)⟩
  let ρ' := DensityOp.isometryEmbed V hV ρ
  let σ' := DensityOp.isometryEmbed V hV σ
  have h_ker := ker_sigma_sub_ker_rho_of_eigenvalue_support ρ σ h_q_supp
  have h_ker' : ∀ v, σ'.toOp.mulVec v = 0 → ρ'.toOp.mulVec v = 0 := by
    exact kernel_containment_isometry_embed V hV ρ σ h_ker
  have h_support' : ∀ j, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ' j = 0 →
      diagonalOfRhoInSigmaBasis ρ' σ' j = 0 :=
    eigenvalue_support_of_ker_sub ρ' σ' h_ker'
  obtain ⟨W, g, _hWU, hWU', h_trace_eq⟩ :=
    projector_adapted_onb_exists P hP_proj hP_herm hP_ortho hP_complete
  set dρ : Fin (n * m) → ℝ := fun j => ((W * ρ'.toOp * W.conjTranspose) j j).re
  set dσ : Fin (n * m) → ℝ := fun j => ((W * σ'.toOp * W.conjTranspose) j j).re
  have hW_inj : Function.Injective W.mulVec :=
    mulVec_injective_of_conjTranspose_mul_eq_one W hWU'
  have h_basis_supp : ∀ j, dσ j = 0 → dρ j = 0 := by
    intro j hj
    exact support_containment_any_basis W hW_inj ρ' σ' h_support' j (by
      simpa [dσ] using hj)
  have hρ'_toOp : ρ'.toOp = V * ρ.toOp * V.conjTranspose := rfl
  have hσ'_toOp : σ'.toOp = V * σ.toOp * V.conjTranspose := rfl
  have hρ_eq : ∀ y, ((P y * ρ'.toOp).trace).re = M.prob ρ y := by
    intro y
    rw [hρ'_toOp]
    exact hP_prob ρ y
  have hσ_eq : ∀ y, ((P y * σ'.toOp).trace).re = M.prob σ y := by
    intro y
    rw [hσ'_toOp]
    exact hP_prob σ y
  have h_meas_rho : ∀ y, ((P y * ρ'.toOp).trace).re =
      ∑ j ∈ Finset.univ.filter (fun j => g j = y), dρ j := by
    intro y
    have h1 := h_trace_eq ρ'.toOp y
    simp only [dρ]
    conv_lhs => rw [h1]
    simp [Complex.re_sum]
  have h_meas_sigma : ∀ y, ((P y * σ'.toOp).trace).re =
      ∑ j ∈ Finset.univ.filter (fun j => g j = y), dσ j := by
    intro y
    have h1 := h_trace_eq σ'.toOp y
    simp only [dσ]
    conv_lhs => rw [h1]
    simp [Complex.re_sum]
  have hσ_sum_zero : ∑ j ∈ Finset.univ.filter (fun j => g j = y), dσ j = 0 := by
    rw [← h_meas_sigma y, hσ_eq y, hy_σ]
  have hσ_diag_zero : ∀ j ∈ Finset.univ.filter (fun j => g j = y), dσ j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      psd_conj_diag_nonneg (posSemidefOp_implies_mathlib σ'.toPosSemidefOp) W j)).mp
      hσ_sum_zero
  have hρ_sum_zero : ∑ j ∈ Finset.univ.filter (fun j => g j = y), dρ j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact h_basis_supp j (hσ_diag_zero j hj)
  rw [← hρ_eq y, h_meas_rho y, hρ_sum_zero]

/-- **Data Processing Inequality for Measurements (ENNReal version)** — unconditional.

    For any POVM measurement M and density operators ρ, σ (no support hypothesis):
    D_KL(measurement(ρ) || measurement(σ)) ≤ D(ρ || σ)  (both ENNReal)

    When supp(ρ) ⊄ supp(σ), the RHS is +∞ and the inequality is trivial.
    When classical support fails (p_σ(y) = 0 but p_ρ(y) > 0), both sides are ⊤.
    When both support conditions hold, this reduces to measurement_monotonicity_with_support. -/
theorem measurement_monotonicity {n m : ℕ} [NeZero n] [NeZero m]
    (M : InfoTheory.Measurement.POVM n m) (ρ σ : DensityOp n) :
    measurementKLDiv M ρ σ ≤ relativeEntropy ρ σ := by
  -- Case split on classical support: ∀ y, p_σ(y) = 0 → p_ρ(y) = 0.
  by_cases h_cl_supp : ∀ y, M.prob σ y = 0 → M.prob ρ y = 0
  · -- Classical support holds: measurementKLDiv = ofReal (measurementKLDivReal ...).
    rw [measurementKLDiv_eq_ofReal_of_support M ρ σ h_cl_supp]
    -- Now case split on quantum support.
    by_cases h_supp : ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0
    · -- Quantum support holds: relativeEntropy = ofReal (relativeEntropyReal ...).
      rw [relativeEntropy_eq_ofReal_of_support ρ σ h_supp]
      apply ENNReal.ofReal_le_ofReal
      exact measurement_monotonicity_with_support M ρ σ h_supp
    · -- Quantum support fails: relativeEntropy = ⊤, inequality trivial.
      rw [relativeEntropy_eq_top ρ σ h_supp]
      exact le_top
  · -- Classical support fails: measurementKLDiv = ⊤.
    -- We show quantum support also fails, so relativeEntropy = ⊤ too.
    rw [measurementKLDiv_eq_top M ρ σ h_cl_supp]
    -- Show quantum support fails (so relativeEntropy = ⊤, giving ⊤ ≤ ⊤).
    have h_q_supp_fails : ¬ ∀ i, InfoTheory.VonNeumannEntropy.eigenvaluesOf σ i = 0 →
        diagonalOfRhoInSigmaBasis ρ σ i = 0 := by
      intro h_q_supp
      -- If quantum support holds, then classical support holds too. Contradiction.
      exact h_cl_supp (fun y hy_σ =>
        prob_zero_of_quantum_support_and_sigma_prob_zero M ρ σ h_q_supp y hy_σ)
    simp [relativeEntropy_eq_top ρ σ h_q_supp_fails]

end InfoTheory.RelativeEntropy

end
