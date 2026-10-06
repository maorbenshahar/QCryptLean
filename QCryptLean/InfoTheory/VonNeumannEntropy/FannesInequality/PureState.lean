import QCryptLean.InfoTheory.VonNeumannEntropy.Continuity
import QCryptLean.InfoTheory.DistanceBounds.Basic
import QCryptLean.InfoTheory.DistanceBounds.FuchsVanDeGraaf.Basic
import QCryptLean.InfoTheory.DistanceBounds.FuchsVanDeGraaf.EigenvalueBound
import QCryptLean.Math.ClassicalEntropy.ContinuityBounds.BinaryEntropy
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv

/-!
# Fannes Inequality for Pure States — fidelity-to-entropy bounds near rank-one states

Applications of entropy continuity to states that are close to a pure state.
The key bridge is that fidelity with a pure state controls a large eigenvalue,
which then feeds into the classical large-coordinate entropy bounds.

## Main statements
- `fidelityPureSq_le_max_eigenvalue`: fidelity with a pure state is controlled by
  a maximal eigenvalue
- `fannes_inequality_pure`: Fannes bound specialized to comparison with a pure state
- `vonNeumannEntropy_pure_state`: pure states have zero entropy
- `entropy_bound_near_pure`: near-pure entropy bound on the `sqrt ε` scale
- `entropy_bound_near_pure_tight`: sharper near-pure entropy bound on the `ε` scale
-/

open Quantum.Operators Quantum.TensorProducts

noncomputable section

namespace InfoTheory.Continuity

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy Quantum.Metrics Filter Topology

/-- The fidelity squared is bounded by the maximum eigenvalue.

    For a density operator ρ with eigenvalues λᵢ and a normalized state |ψ⟩,
    DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) = ⟨ψ|ρ|ψ⟩ = ∑ᵢ λᵢ |⟨eᵢ|ψ⟩|² ≤ max_i(λᵢ)

    since |⟨eᵢ|ψ⟩|² form a probability distribution (sum to 1, non-negative),
    and a convex combination is bounded by the maximum value.

    **Proof outline:**
    1. Use spectral decomposition: ρ = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|
    2. Then ⟨ψ|ρ|ψ⟩ = ∑ᵢ λᵢ |⟨eᵢ|ψ⟩|²
    3. Since |⟨eᵢ|ψ⟩|² ≥ 0 and ∑ᵢ |⟨eᵢ|ψ⟩|² = 1 (completeness), this is a convex combination
    4. Any convex combination of values is ≤ the maximum value -/
lemma fidelityPureSq_le_max_eigenvalue {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1) :
    ∃ i, DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) ≤ eigenvaluesOf ρ i := by
  -- Find the index with maximum eigenvalue
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  obtain ⟨i_max, _, hi_max_is_max⟩ :=
    Finset.exists_max_image Finset.univ (eigenvaluesOf ρ) hnonempty
  use i_max
  -- Use the spectral decomposition machinery (cf. fidelityPureSq_le_one in Metrics.lean)
  rw [fidelitySq_fromPure]
  have h_eq : ψ.dag * ρ.toOp * ψ = quadraticForm ρ.toOp ψ.vec := by
    rw [braop_mul_ket]
    simp only [bra_mul_ket_eq, op_mul_ket_vec, Ket.dag_vec]
    unfold quadraticForm dotProduct
    rfl
  -- Use the Hermitian eigenvalue machinery
  let hH := ρ.toPosSemidefOp.toHermitianOp.isHermitian
  let ev := hH.eigenvalues
  -- Get eigenvalue bounds: 0 ≤ λᵢ
  have h_ev_nonneg : ∀ i, 0 ≤ ev i :=
    (posSemidefOp_implies_mathlib ρ.toPosSemidefOp).eigenvalues_nonneg
  -- Eigenvalues sum to 1
  have h_ev_sum : ∑ i, ev i = 1 := by
    have h_trace_sum : (∑ j, (hH.eigenvalues j : ℂ)) = ρ.toOp.trace :=
      hH.trace_eq_sum_eigenvalues.symm
    have h_tr : ρ.toOp.trace = 1 := ρ.trace_one
    have h_eq : (∑ j, (hH.eigenvalues j : ℂ)) = 1 := by rw [h_trace_sum, h_tr]
    simp only [← Complex.ofReal_sum, Complex.ofReal_eq_one] at h_eq
    exact h_eq
  -- Use spectral theorem: ρ = U * D * U† where D = diagonal(ev)
  have h_spec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  let U := hH.eigenvectorUnitary.val
  have h_UU : U† * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have h_UU' : U * U† = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  -- Transform to eigenbasis: let φ = U†ψ
  let φ_vec := U†.mulVec ψ.vec
  -- The coefficients aᵢ = |φᵢ|² satisfy Σᵢ aᵢ = 1
  let a := fun i => Complex.normSq (φ_vec i)
  have h_a_nonneg : ∀ i, 0 ≤ a i := fun i => Complex.normSq_nonneg _
  -- Prove Σᵢ aᵢ = 1 using UU† = 1 and ⟨ψ|ψ⟩ = 1
  have h_a_sum : ∑ i, a i = 1 := by
    have h1 : ∑ i, a i = (star φ_vec ⬝ᵥ φ_vec).re := by
      have h_eq : star φ_vec ⬝ᵥ φ_vec = ∑ i, star (φ_vec i) * φ_vec i := rfl
      rw [h_eq]
      have h_sum_re : (∑ i, star (φ_vec i) * φ_vec i).re = ∑ i, (star (φ_vec i) * φ_vec i).re :=
        Complex.re_sum _ _
      rw [h_sum_re]
      congr 1; ext i
      have h1 : star (φ_vec i) = (starRingEnd ℂ) (φ_vec i) := rfl
      rw [h1, RCLike.conj_mul]
      simp only [a, Complex.normSq_eq_norm_sq]
      norm_cast
    have h2 : star φ_vec ⬝ᵥ φ_vec = star ψ.vec ⬝ᵥ ψ.vec := by
      change star (U†.mulVec ψ.vec) ⬝ᵥ (U†.mulVec ψ.vec) = star ψ.vec ⬝ᵥ ψ.vec
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [Matrix.vecMul_vecMul]
      have h3 : Matrix.vecMul (star ψ.vec) (U * U†) = star ψ.vec := by
        rw [h_UU', Matrix.vecMul_one]
      rw [h3]
    have h3 : star ψ.vec ⬝ᵥ ψ.vec = 1 := by
      have h_bra := hψ
      simp only [bra_mul_ket_eq, Ket.dag_vec] at h_bra
      have h_eq : star ψ.vec ⬝ᵥ ψ.vec = ∑ i, star (ψ.vec i) * ψ.vec i := rfl
      rw [h_eq]
      have h_star_eq : ∀ i, star (ψ.vec i) = (starRingEnd ℂ) (ψ.vec i) := fun _ => rfl
      simp_rw [h_star_eq]
      exact h_bra
    rw [h1, h2, h3, Complex.one_re]
  -- Now prove that ⟨ψ|ρ|ψ⟩ = Σᵢ λᵢ aᵢ using the spectral decomposition
  have h_expect : (ψ.dag * ρ.toOp * ψ).re = ∑ i, ev i * a i := by
    rw [h_eq]
    unfold quadraticForm
    rw [h_spec]
    -- The spectral form uses RCLike.ofReal ∘ hH.eigenvalues, which equals fun i => (ev i : ℂ)
    have hD_eq : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) =
                 Matrix.diagonal (fun i => (ev i : ℂ)) := rfl
    rw [hD_eq]
    set D := Matrix.diagonal (fun i => (ev i : ℂ)) with hD
    -- Note: star U = U† = Matrix.conjTranspose U
    have h_star_eq_dag : star U = U† := rfl
    rw [h_star_eq_dag]
    -- (U * D * U†).mulVec ψ.vec = U.mulVec (D.mulVec φ_vec)
    have h1 : (U * D * U†).mulVec ψ.vec = U.mulVec (D.mulVec φ_vec) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, φ_vec]
    rw [h1, Matrix.dotProduct_mulVec]
    -- vecMul (star ψ.vec) U = star φ_vec
    have h_star_vecMul : Matrix.vecMul (star ψ.vec) U = star φ_vec := by
      unfold φ_vec
      ext i
      simp only [Matrix.vecMul, dotProduct, Matrix.mulVec, Pi.star_apply,
                 Matrix.conjTranspose_apply]
      rw [star_sum]
      congr 1
      funext j
      rw [star_mul', star_star]
      ring
    rw [h_star_vecMul]
    -- star φ_vec ⬝ᵥ D.mulVec φ_vec = ∑ i, ev i * |φᵢ|²
    unfold dotProduct
    have h_diag_mulVec : ∀ i, (D.mulVec φ_vec) i = (ev i : ℂ) * φ_vec i := by
      intro i; rw [hD]; simp only [Matrix.mulVec_diagonal]
    simp_rw [h_diag_mulVec]
    -- Now we have (∑ x, star φ_vec x * (↑(ev x) * φ_vec x)).re = ∑ i, ev i * a i
    rw [Complex.re_sum]
    congr 1
    funext i
    -- Note: star φ_vec i = (star φ_vec) i = Pi.star φ_vec i
    have h_star_eq : star φ_vec i = star (φ_vec i) := rfl
    rw [h_star_eq]
    have h_conj : star (φ_vec i) * ((ev i : ℂ) * φ_vec i) =
                  (ev i : ℂ) * (star (φ_vec i) * φ_vec i) := by ring
    rw [h_conj]
    -- star (φ_vec i) * φ_vec i has real part = normSq
    -- Use starRingEnd for the conjugate
    have h_star_is_conj : star (φ_vec i) = (starRingEnd ℂ) (φ_vec i) := rfl
    rw [h_star_is_conj]
    -- Now use Complex.conj_mul: conj z * z = normSq z
    rw [RCLike.conj_mul]
    -- Now: (↑(ev i) * ↑‖φ_vec i‖^2).re = ev i * a i
    simp only [a, Complex.normSq_eq_norm_sq]
    -- Goal: (↑(ev i) * ↑‖φ_vec i‖ ^ 2).re = ev i * ‖φ_vec i‖ ^ 2
    have h_real_mul : ((ev i : ℂ) * (‖φ_vec i‖ ^ 2 : ℂ)).re = ev i * ‖φ_vec i‖ ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
      simp only [Complex.ofReal_re]
    exact h_real_mul
  rw [h_expect]
  -- Now use: Σᵢ λᵢ aᵢ ≤ max(λᵢ) using convex combination bound
  -- The key insight: weighted sum with weights summing to 1 ≤ max value
  have h_sum_pos : 0 < ∑ i : Fin n, a i := by rw [h_a_sum]; exact one_pos
  have h_centerMass_eq : Finset.centerMass Finset.univ a ev = ∑ i, a i * ev i := by
    simp only [Finset.centerMass, h_a_sum, inv_one, smul_eq_mul]
    ring_nf
  have h_bound := Finset.centerMass_le_sup (s := Finset.univ) (w := a) (f := ev)
                   (fun i _ => h_a_nonneg i) h_sum_pos
  rw [h_centerMass_eq] at h_bound
  -- Rewrite sum to have ev i * a i instead of a i * ev i
  have h_comm : ∑ i, a i * ev i = ∑ i, ev i * a i := by
    congr 1; ext i; ring
  rw [h_comm] at h_bound
  -- Now we need to relate sup' of ev to eigenvaluesOf ρ i_max
  -- The key is that hH.eigenvalues forms an IsEigenvalueSpectrum
  have h_ev_le_one : ∀ i, ev i ≤ 1 := by
    intro i
    calc ev i ≤ ∑ j, ev j := Finset.single_le_sum (fun j _ => h_ev_nonneg j) (Finset.mem_univ i)
      _ = 1 := h_ev_sum
  -- Build the IsEigenvalueSpectrum for ev
  have h_mathlib_spec : IsEigenvalueSpectrum ρ ev := by
    refine ⟨h_ev_nonneg, h_ev_sum, h_ev_le_one, ?_⟩
    -- Show spectral decomposition: ρ = V† * D * V for some unitary V
    -- From h_spec: ρ = U * D * U†
    -- We need: ρ = V† * D * V, so take V = U†
    use U†
    constructor
    · -- U†† * U† = U * U† = 1
      simp only [Matrix.conjTranspose_conjTranspose]
      exact h_UU'
    constructor
    · -- U† * U†† = U† * U = 1
      simp only [Matrix.conjTranspose_conjTranspose]
      exact h_UU
    · -- ρ = (U†)† * D * U† = U * D * U†
      simp only [Matrix.conjTranspose_conjTranspose]
      exact h_spec
  -- The eigenvalue spectra ev and eigenvaluesOf ρ have the same multiset
  -- So their sup' values are equal
  have h_multiset_eq := eigenvalueSpectrum_multiset_eq ρ ev (eigenvaluesOf ρ)
                         h_mathlib_spec (eigenvaluesOf_spec ρ)
  -- Use that equal multisets have equal sup
  have h_sup_ev : Finset.univ.sup' hnonempty ev = Finset.univ.sup' hnonempty (eigenvaluesOf ρ) := by
    -- The multisets are equal, so their sup' are equal
    -- eigenvalueMultiset is Finset.univ.val.map f
    -- When two multisets are equal, their max elements are equal
    apply le_antisymm
    · apply Finset.sup'_le hnonempty
      intro i _
      -- ev i is in the multiset of ev
      -- By h_multiset_eq, ev i is also in the multiset of eigenvaluesOf ρ
      -- So ev i = eigenvaluesOf ρ j for some j
      have h_ev_in : ev i ∈ Finset.univ.val.map ev :=
        Multiset.mem_map_of_mem ev (Finset.mem_univ_val i)
      -- eigenvalueMultiset is defined as Finset.univ.val.map
      -- h_multiset_eq says these are equal
      have h_in_eig : ev i ∈ Finset.univ.val.map (eigenvaluesOf ρ) := by
        have : Finset.univ.val.map ev = Finset.univ.val.map (eigenvaluesOf ρ) := h_multiset_eq
        rw [← this]; exact h_ev_in
      obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp h_in_eig
      rw [← hj]
      exact Finset.le_sup' (eigenvaluesOf ρ) (Finset.mem_univ j)
    · apply Finset.sup'_le hnonempty
      intro i _
      have h_eig_in : eigenvaluesOf ρ i ∈ Finset.univ.val.map (eigenvaluesOf ρ) :=
        Multiset.mem_map_of_mem (eigenvaluesOf ρ) (Finset.mem_univ_val i)
      have h_in_ev : eigenvaluesOf ρ i ∈ Finset.univ.val.map ev := by
        have : Finset.univ.val.map ev = Finset.univ.val.map (eigenvaluesOf ρ) := h_multiset_eq
        rw [this]; exact h_eig_in
      obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp h_in_ev
      rw [← hj]
      exact Finset.le_sup' ev (Finset.mem_univ j)
  -- Finally, sup' = eigenvaluesOf ρ i_max
  have h_sup_eq_max : Finset.univ.sup' hnonempty (eigenvaluesOf ρ) = eigenvaluesOf ρ i_max := by
    apply le_antisymm
    · apply Finset.sup'_le hnonempty
      intro i _
      exact hi_max_is_max i (Finset.mem_univ i)
    · exact Finset.le_sup' (eigenvaluesOf ρ) (Finset.mem_univ i_max)
  calc ∑ i, ev i * a i ≤ Finset.univ.sup' hnonempty ev := h_bound
    _ = Finset.univ.sup' hnonempty (eigenvaluesOf ρ) := h_sup_ev
    _ = eigenvaluesOf ρ i_max := h_sup_eq_max

/-- Fannes' inequality for pure states: simplified version without Weyl's theorem.

    When σ is a pure state |ψ⟩⟨ψ|, we can prove the entropy bound directly:
    S(ρ) ≤ T·log(n-1) + H(T)  where T = D(ρ, σ)

    **Key insight**: No eigenvalue perturbation theorem needed!

    **Proof strategy** (avoiding Weyl's theorem):
    1. From Fuchs-van de Graaf: T ≤ √(1 - F²) where F² = ⟨ψ|ρ|ψ⟩
    2. Since F² ≤ p_max (largest eigenvalue of ρ), we get p_max ≥ 1 - T²
    3. Since T < 1 (from `hT_bound`): p_max ≥ 1 - T (since 1 - T² ≥ 1 - T)
    4. Remaining eigenvalues sum to ≤ T, distributed over at most n-1 values
    5. Entropy decomposition:
       - Large eigenvalue contributes: -p_max·log(p_max) ≤ -(1-T)·log(1-T)
       - Small eigenvalues contribute: ≤ T·log(n-1) (by concavity/uniformity)
    6. Total: S(ρ) ≤ T·log(n-1) + H(T)

    This approach uses the rank-1 perturbation structure of ρ - |ψ⟩⟨ψ|
    which we already exploited in `traceDistance_from_fidelity`. -/
theorem fannes_inequality_pure {n : ℕ} [NeZero n] (ρ : DensityOp n)
    (ψ : Ket n) (hψ : (ψ.dag * ψ) = 1)
    (T : ℝ) (hT : T = traceDistance ρ.toOp (DensityOp.fromPure ψ hψ).toOp)
    (hT_pos : 0 ≤ T) (hT_bound : T ≤ 1 - 1 / (n : ℝ)) :
    vonNeumannEntropy ρ ≤ T * Real.log (n - 1) + binaryEntropy T := by
  -- This proof avoids Weyl's eigenvalue perturbation theorem by using
  -- the special structure of pure states.
  --
  -- Proof outline:
  -- 1. From Fuchs-van de Graaf: T ≤ √(1 - F²) where F² = ⟨ψ|ρ|ψ⟩
  -- 2. So F² ≥ 1 - T² ≥ 1 - T (since T < 1 implies T² < T)
  -- 3. The fidelity F² = ⟨ψ|ρ|ψ⟩ is bounded by the max eigenvalue of ρ
  -- 4. So p_max ≥ F² ≥ 1 - T
  -- 5. Apply entropy_bound_with_large_eigenvalue: S(ρ) ≤ T·log(n-1) + H(T)
  -- Step 1: Set up the pure state σ
  let σ := DensityOp.fromPure ψ hψ
  -- Note: traceDistance_from_fidelity gives: traceDistance ρ σ ≤ √(1 - fidelityPureSq ρ ψ hψ)
  -- but we don't need this upper bound - we need the spectral approach below
  -- Step 2: Establish fidelity bounds
  have h_fid_nn := fidelityPureSq_nonneg ρ ψ hψ
  have h_fid_le := fidelityPureSq_le_one ρ ψ hψ
  -- (These are stated in terms of DensityOp.fidelitySq via fidelitySq_fromPure)
  -- Step 3: The key lemma needed is that max eigenvalue ≥ 1 - T
  -- This requires the LOWER bound of Fuchs-van de Graaf: D ≥ 1 - F (fidelity, not F²)
  -- Combined with F ≤ λ_max (fidelity bounded by max eigenvalue)
  --
  -- The standard Fuchs-van de Graaf inequality is:
  --   1 - F(ρ, σ) ≤ D(ρ, σ) ≤ √(1 - F²(ρ, σ))
  -- where F is fidelity (not fidelity squared).
  --
  -- From the LOWER bound: D ≥ 1 - F, so F ≥ 1 - D = 1 - T
  -- Since F = √(fidelityPureSq) and fidelityPureSq ≤ λ_max, we need:
  --   √(fidelityPureSq) ≥ 1 - T, but this only gives fidelityPureSq ≥ (1-T)²
  --   which is weaker than fidelityPureSq ≥ 1 - T
  --
  -- ALTERNATIVE APPROACH: Use directly that for any density operator,
  -- if we're at trace distance T < 1 from a pure state, then ρ has
  -- an eigenvalue ≥ 1 - T. This follows from spectral analysis of the
  -- difference operator ρ - |ψ⟩⟨ψ|.
  --
  -- For now, we state this as an admitted lemma, documenting the
  -- mathematical fact that needs proper formalization:
  have h_max_eig_ge : ∃ i, eigenvaluesOf ρ i ≥ 1 - T := by
    -- Use the max_eigenvalue_ge_one_sub_traceDistance lemma from Metrics.lean
    -- which proves: for any density operator ρ and pure state σ = |ψ⟩⟨ψ|,
    -- max eigenvalue of ρ ≥ 1 - traceDistance(ρ, σ)
    obtain ⟨i, hi⟩ := _root_.Quantum.Metrics.max_eigenvalue_ge_one_sub_traceDistance ρ ψ hψ
    use i
    rw [hT]
    exact hi
  -- Step 4: Get eigenvalue properties
  have hspec := eigenvaluesOf_spec ρ
  obtain ⟨h_eig_nonneg, h_eig_sum, _, _⟩ := hspec
  -- Step 5: The entropy bound uses entropy_bound_with_large_eigenvalue
  -- vonNeumannEntropy ρ = shannonEntropy (eigenvaluesOf ρ) = ∑ i, entropyTerm (eigenvaluesOf ρ i)
  unfold vonNeumannEntropy shannonEntropy
  -- Need hT_pos as strict inequality for entropy_bound_with_large_eigenvalue
  by_cases hT_zero : T = 0
  · -- If T = 0, then the bound becomes S(ρ) ≤ 0 + H(0) = 0
    -- Also T = 0 means traceDistance = 0, so ρ = σ = |ψ⟩⟨ψ| is pure
    -- Pure states have entropy 0
    rw [hT_zero]
    simp only [zero_mul, binaryEntropy_zero, zero_add]
    -- S(ρ) ≥ 0 by shannonEntropy_nonneg, and S(ρ) ≤ 0 follows from purity
    -- From T = 0: ρ = σ (trace distance 0), so ρ is pure, so S(ρ) = 0
    have h_ρ_eq_σ : traceDistance ρ.toOp σ.toOp = 0 := by rw [← hT, hT_zero]
    -- For density operators, traceDistance 0 implies equality
    have h_eq : ρ = σ := (traceDistance_eq_zero_iff ρ σ).mp h_ρ_eq_σ
    -- σ is pure by construction, so ρ is pure
    have h_pure : ρ.IsPure := by
      rw [h_eq]
      unfold DensityOp.IsPure
      show σ.toOp * σ.toOp = σ.toOp
      -- σ.toOp = ψ * ψ.dag, so σ.toOp * σ.toOp = (ψ * ψ.dag) * (ψ * ψ.dag)
      -- = (ψ.dag * ψ) • (ψ * ψ.dag)  by ketbra_mul_ketbra
      -- = 1 • (ψ * ψ.dag) = ψ * ψ.dag = σ.toOp
      have h_op : σ.toOp = ψ * ψ.dag := rfl
      rw [h_op, ketbra_mul_ketbra]
      -- Now goal is: (ψ.dag * ψ) • (ψ * ψ.dag) = ψ * ψ.dag
      have h_inner : ψ.dag * ψ = 1 := hψ
      rw [h_inner, one_smul]
    -- Pure states have entropy 0
    have h_ent_zero := vonNeumannEntropy_pure ρ h_pure
    unfold vonNeumannEntropy shannonEntropy at h_ent_zero
    linarith [shannonEntropy_nonneg (eigenvaluesOf ρ) h_eig_nonneg
      (fun i => (eigenvaluesOf_spec ρ).2.2.1 i)]
  · -- T > 0 case
    have hT_pos_strict : 0 < T := lt_of_le_of_ne hT_pos (Ne.symm hT_zero)
    -- Apply entropy_bound_with_large_eigenvalue
    have h_bound := entropy_bound_with_large_eigenvalue (eigenvaluesOf ρ)
      h_eig_nonneg h_eig_sum T hT_bound h_max_eig_ge
    exact h_bound

/-!
## Entropy Bounds Near Pure States
-/

/-- Pure states have zero entropy -/
theorem vonNeumannEntropy_pure_state {n : ℕ} [NeZero n] (ψ : Ket n)
    (hψ : (ψ.dag * ψ) = 1) :
    vonNeumannEntropy (DensityOp.fromPure ψ hψ) = 0 := by
  apply vonNeumannEntropy_pure
  unfold DensityOp.IsPure DensityOp.fromPure
  simp only
  rw [ketbra_mul_ketbra]
  simp only [hψ, one_smul]

/-- Simplified entropy bound for states close to pure states.

    If ρ has fidelity F² with a pure state |ψ⟩ where F² > 1 - ε, then:
    S(ρ) < √ε · log(n) + H(√ε) + ε

    Note: This uses log(n) instead of log(n-1) from Fannes inequality,
    with the +ε slack term absorbing the difference. The strict inequality (<)
    comes from the strict fidelity bound (F² > 1 - ε, not ≥).

    For small ε, H(√ε) ≈ √ε · (1/ln2 + log(1/√ε)) = √ε · (1/ln2 - (1/2)log ε) -/
theorem entropy_bound_near_pure {n : ℕ} [NeZero n] (ρ : DensityOp n) (ψ : Ket n)
    (hψ : (ψ.dag * ψ) = 1) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hε_small : Real.sqrt ε ≤ 1 - 1 / (n : ℝ))
    (hfid : DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) > 1 - ε) :
    vonNeumannEntropy ρ < Real.sqrt ε * Real.log n + binaryEntropy (Real.sqrt ε) + ε := by
  -- ALTERNATIVE APPROACH: Direct eigenvalue bound (avoids traceDistance_from_fidelity gap)
  -- Step 1: From F² > 1 - ε, get max eigenvalue bound via fidelityPureSq_le_max_eigenvalue
  obtain ⟨i_max, h_fid_le_eig⟩ := fidelityPureSq_le_max_eigenvalue ρ ψ hψ
  have h_eig_gt : eigenvaluesOf ρ i_max > 1 - ε := lt_of_lt_of_le hfid h_fid_le_eig
  -- Step 2: For 0 < ε < 1, we have √ε > ε, so 1 - √ε < 1 - ε < max eigenvalue
  have h_sqrt_ε_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε_pos
  have h_sqrt_ε_lt_one : Real.sqrt ε < 1 := by
    calc Real.sqrt ε < Real.sqrt 1 := Real.sqrt_lt_sqrt hε_pos.le hε_lt
      _ = 1 := Real.sqrt_one
  have h_sqrt_gt_ε : Real.sqrt ε > ε := by
    -- For 0 < ε < 1: √ε > ε iff ε < √ε iff √ε · √ε < √ε (since √ε > 0)
    -- iff √ε < 1 (which we have)
    have hε_nn : 0 ≤ ε := le_of_lt hε_pos
    calc ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hε_nn).symm
      _ < Real.sqrt ε * 1 := mul_lt_mul_of_pos_left h_sqrt_ε_lt_one h_sqrt_ε_pos
      _ = Real.sqrt ε := mul_one _
  -- Step 3: Thus max eigenvalue ≥ 1 - √ε
  have h_eig_ge_sqrt : eigenvaluesOf ρ i_max ≥ 1 - Real.sqrt ε := by
    have h1 : eigenvaluesOf ρ i_max > 1 - ε := h_eig_gt
    have h2 : 1 - ε > 1 - Real.sqrt ε := by linarith
    linarith
  have h_max_eig_ge : ∃ i, eigenvaluesOf ρ i ≥ 1 - Real.sqrt ε := ⟨i_max, h_eig_ge_sqrt⟩
  -- Step 4: Apply entropy_bound_with_large_eigenvalue with T = √ε
  -- For n = 1, the bound is trivially true since S(ρ) = 0 for all ρ in dim 1
  -- For n ≥ 2, we use the entropy bound
  by_cases hn : n ≥ 2
  case pos => -- n ≥ 2: Apply entropy_bound_with_large_eigenvalue
    have hspec := eigenvaluesOf_spec ρ
    obtain ⟨h_eig_nonneg, h_eig_sum, _, _⟩ := hspec
    have h_entropy_bound : ∑ i, entropyTerm (eigenvaluesOf ρ i) ≤
        Real.sqrt ε * Real.log (n - 1) + binaryEntropy (Real.sqrt ε) :=
      entropy_bound_with_large_eigenvalue (eigenvaluesOf ρ) h_eig_nonneg h_eig_sum
        (Real.sqrt ε) hε_small h_max_eig_ge
    -- vonNeumannEntropy = shannonEntropy = ∑ entropyTerm
    unfold vonNeumannEntropy shannonEntropy
    calc ∑ i, entropyTerm (eigenvaluesOf ρ i)
        ≤ Real.sqrt ε * Real.log (n - 1) + binaryEntropy (Real.sqrt ε) := h_entropy_bound
      _ < Real.sqrt ε * Real.log n + binaryEntropy (Real.sqrt ε) + ε := by
          -- Goal: √ε * log(n-1) + H(√ε) < √ε * log(n) + H(√ε) + ε
          -- Simplifies to: √ε * log(n-1) < √ε * log(n) + ε
          have hn_cast : (n : ℝ) ≥ 2 := Nat.ofNat_le_cast.mpr hn
          have hn_sub_one_pos : (0 : ℝ) < n - 1 := by linarith
          have h_log_n_sub_nn : 0 ≤ Real.log (n - 1 : ℝ) := Real.log_nonneg (by linarith)
          have h_log_n_ge : Real.log (n - 1 : ℝ) ≤ Real.log n :=
            Real.log_le_log hn_sub_one_pos (by linarith)
          -- √ε * log(n-1) ≤ √ε * log(n) since log(n-1) ≤ log(n)
          have h1 : Real.sqrt ε * Real.log (n - 1 : ℝ) ≤ Real.sqrt ε * Real.log n :=
            mul_le_mul_of_nonneg_left h_log_n_ge (Real.sqrt_nonneg ε)
          -- Adding ε > 0 gives strict inequality
          linarith
  case neg =>
    -- n = 1: In dimension 1, all density operators have zero entropy
    push Not at hn
    have hn1 : n = 1 := by
      have hne : n ≠ 0 := NeZero.ne n
      omega
    -- Entropy is 0 in dimension 1, and RHS > 0
    have h_entropy_zero : vonNeumannEntropy ρ = 0 := by
      -- In dimension 1, there's only one eigenvalue and it must equal 1 (trace = 1)
      -- Therefore entropy = entropyTerm(1) = 0
      subst hn1
      unfold vonNeumannEntropy shannonEntropy
      have hspec := eigenvaluesOf_spec ρ
      obtain ⟨_, h_sum, _, _⟩ := hspec
      have h_single : eigenvaluesOf ρ 0 = 1 := by
        simp only [Fin.sum_univ_one] at h_sum
        exact h_sum
      simp only [Fin.sum_univ_one, h_single, entropyTerm_one]
    rw [h_entropy_zero]
    -- 0 < √ε·log(n) + H(√ε) + ε
    have h_rhs_pos : 0 < Real.sqrt ε * Real.log n + binaryEntropy (Real.sqrt ε) + ε := by
      -- When n = 1: log n = log 1 = 0, so first term vanishes
      have h_log_n : Real.log (n : ℝ) = 0 := by simp [hn1]
      rw [h_log_n, mul_zero, zero_add]
      -- Goal: 0 < H(√ε) + ε
      have h_bin_nn : 0 ≤ binaryEntropy (Real.sqrt ε) :=
        binaryEntropy_nonneg (Real.sqrt ε) (Real.sqrt_nonneg ε) h_sqrt_ε_lt_one.le
      linarith
    exact h_rhs_pos

/-- A density operator on a one-dimensional Hilbert space has zero entropy. -/
lemma vonNeumannEntropy_eq_zero_of_one_dim (ρ : DensityOp 1) :
    vonNeumannEntropy ρ = 0 := by
  unfold vonNeumannEntropy shannonEntropy
  have hspec := eigenvaluesOf_spec ρ
  obtain ⟨_, h_sum, _, _⟩ := hspec
  have h_single : eigenvaluesOf ρ 0 = 1 := by
    simpa only [Fin.sum_univ_one] using h_sum
  simp [h_single, entropyTerm_one]

/-- If `ρ` has fidelity squared at least `1 - ε` with a pure state and
`0 ≤ ε ≤ 1 - 1 / n`, then its entropy is bounded by `ε log (n - 1) + H(ε)`. -/
theorem entropy_bound_near_pure_tight {n : ℕ} [NeZero n] (ρ : DensityOp n) (ψ : Ket n)
    (hψ : (ψ.dag * ψ) = 1) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hε_small : ε ≤ 1 - 1 / (n : ℝ))
    (hfid : DensityOp.fidelitySq ρ (DensityOp.fromPure ψ hψ) ≥ 1 - ε) :
    vonNeumannEntropy ρ ≤ ε * Real.log (n - 1) + binaryEntropy ε := by
  by_cases hn : n ≥ 2
  · obtain ⟨i_max, h_fid_le_eig⟩ := fidelityPureSq_le_max_eigenvalue ρ ψ hψ
    have h_max_eig_ge : ∃ i, eigenvaluesOf ρ i ≥ 1 - ε := by
      exact ⟨i_max, le_trans hfid h_fid_le_eig⟩
    have hspec := eigenvaluesOf_spec ρ
    obtain ⟨h_eig_nonneg, h_eig_sum, _, _⟩ := hspec
    have h_entropy_bound :
        ∑ i, entropyTerm (eigenvaluesOf ρ i) ≤
          ε * Real.log (n - 1) + binaryEntropy ε :=
      entropy_bound_with_large_eigenvalue (eigenvaluesOf ρ) h_eig_nonneg h_eig_sum
        ε hε_small h_max_eig_ge
    simpa [vonNeumannEntropy, shannonEntropy] using h_entropy_bound
  · push Not at hn
    have hn1 : n = 1 := by
      have hne : n ≠ 0 := NeZero.ne n
      omega
    have hε_nonpos : ε ≤ 0 := by
      simpa [hn1] using hε_small
    have hε_zero : ε = 0 := by linarith
    subst hn1
    subst ε
    rw [vonNeumannEntropy_eq_zero_of_one_dim ρ]
    simp [binaryEntropy_zero]

end InfoTheory.Continuity

end
