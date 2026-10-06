import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.InfoTheory.DistanceBounds.Basic
import QCryptLean.Math.ClassicalEntropy.ContinuityBounds.Basic
import QCryptLean.Math.SpectralTheory.Weyl
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Topology.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Fannes Inequality — entropy continuity bound via trace distance

Continuity of von Neumann entropy: |S(ρ) - S(σ)| ≤ T · log(n-1) + H(T)
where T = D(ρ,σ) is the trace distance.

## Key lemmas
- `eigenvalue_perturbation`: ∑ᵢ |λᵢ(ρ) - λᵢ(σ)| ≤ 2·D(ρ,σ) via Weyl/Mirsky

## Main statements
- `fannes_inequality`: |S(ρ) - S(σ)| ≤ T · log(n-1) + H(T)  (for T ≤ 1 - 1/n)
- `audenaert_inequality`: full continuity bound covering both T ≤ 1 - 1/n and T > 1 - 1/n
-/

open Quantum.Operators Quantum.TensorProducts

noncomputable section

namespace InfoTheory.Continuity

open Math.ClassicalEntropy InfoTheory.VonNeumannEntropy Quantum.Metrics Filter Topology

/-!
## Fannes Inequality

Fannes' inequality is a fundamental continuity result for quantum entropy.
The proof strategy follows from the relationship between trace distance and
eigenvalue perturbations, combined with the continuity of the entropy function.

Key ingredients:
1. Trace distance bounds eigenvalue differences
2. Binary entropy captures the "mixing" contribution
3. The T·log(n-1) term accounts for the dimensional contribution
-/

/-!
## Eigenvalue Perturbation Bridge

Bridges `eigenvaluesOf` (our representation) to Mathlib's `IsHermitian.eigenvalues`,
then applies `Math.SpectralTheory.weyl_eigenvalue_sum_bound` (Mirsky's inequality) to
bound eigenvalue differences by trace distance.
-/

/-- Eigenvalue perturbation bound: ∑ᵢ |eigenvaluesOf(ρ)ᵢ - eigenvaluesOf(σ)ᵢ| ≤ 2·D(ρ,σ).

    Uses `Math.SpectralTheory.weyl_eigenvalue_sum_bound` for the Mirsky/Weyl inequality,
    then relates the trace norm to trace distance. The bridge between `eigenvaluesOf`
    and Mathlib's `IsHermitian.eigenvalues` is definitional since both use the same
    sorted eigenvalue representation.

    Reference: Horn & Johnson, "Matrix Analysis", Theorem 4.3.1 (Weyl). -/
lemma eigenvalue_perturbation {n : ℕ} [NeZero n] (ρ σ : DensityOp n) :
    ∑ i, |eigenvaluesOf ρ i - eigenvaluesOf σ i| ≤ 2 * traceDistance ρ.toOp σ.toOp := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  subst hk
  -- Hermitian properties
  let hρ := ρ.toPosSemidefOp.toHermitianOp.isHermitian
  let hσ := σ.toPosSemidefOp.toHermitianOp.isHermitian
  let h_diff := densityOp_sub_isHermitian ρ σ
  -- eigenvaluesOf is definitionally IsHermitian.eigenvalues
  have h_sum_eq : ∑ i, |eigenvaluesOf ρ i - eigenvaluesOf σ i| =
      ∑ i, |hρ.eigenvalues i - hσ.eigenvalues i| := by
    unfold eigenvaluesOf; rfl
  -- Mirsky/Weyl inequality from SpectralTheory
  have h_mirsky := Math.SpectralTheory.weyl_eigenvalue_sum_bound ρ.toOp σ.toOp hρ hσ h_diff
  -- Relate trace norm to trace distance
  have h_trace_norm : ∑ i, |h_diff.eigenvalues i| =
      Quantum.Metrics.traceNormHermitian (ρ.toOp - σ.toOp) h_diff := rfl
  have h_trace_dist : 2 * traceDistance ρ.toOp σ.toOp =
      Quantum.Metrics.traceNormHermitian (ρ.toOp - σ.toOp) h_diff := by
    rw [traceDistance_densityOp_eq_traceNormHermitian ρ σ]; ring
  calc ∑ i, |eigenvaluesOf ρ i - eigenvaluesOf σ i|
      = ∑ i, |hρ.eigenvalues i - hσ.eigenvalues i| := h_sum_eq
    _ ≤ ∑ i, |h_diff.eigenvalues i| := h_mirsky
    _ = Quantum.Metrics.traceNormHermitian (ρ.toOp - σ.toOp) h_diff := h_trace_norm
    _ = 2 * traceDistance ρ.toOp σ.toOp := h_trace_dist.symm

/-- Fannes' inequality: entropy continuity bound.

    For density operators ρ and σ in dimension d with trace distance T = D(ρ,σ):
    |S(ρ) - S(σ)| ≤ T · log(d - 1) + H(T)

    where H(T) = -T log T - (1-T) log(1-T) is binary entropy.

    This is the key inequality relating closeness of states to closeness of entropies.

    **Mathematical outline** (following Audenaert, J. Phys. A 40 (2007)):

    1. **Eigenvalue setup**:
       - Let λ = (λ₁,...,λₙ) be eigenvalues of ρ (sorted, summing to 1)
       - Let μ = (μ₁,...,μₙ) be eigenvalues of σ (sorted, summing to 1)
       - Trace distance: D(ρ,σ) = (1/2)∑ᵢ |λᵢ - μᵢ|

    2. **Splitting the spectrum**:
       - Let S = {i : λᵢ ≤ T} be the "small" eigenvalue indices
       - Let L = {i : λᵢ > T} be the "large" eigenvalue indices
       - Key observation: |S| ≤ (1-T)/T·|L| + 1 because ∑ᵢ λᵢ = 1

    3. **Entropy decomposition**:
       - S(ρ) = S_L + S_S where S_L = -∑_{i∈L} λᵢ log λᵢ
       - Small eigenvalues contribute: S_S ≤ T·log(n-1)
       - Use: -x log x ≤ x·log(n) for x ∈ [0, 1/n]

    4. **Lipschitz continuity on large eigenvalues**:
       - For λ > T, the function f(x) = -x log x has bounded derivative
       - |f'(x)| = |log x + 1| ≤ log(1/T) + 1 for x ≥ T
       - This gives: |S_L(ρ) - S_L(σ)| ≤ C·∑_{i∈L} |λᵢ - μᵢ|

    5. **Combining the bounds**:
       - |S(ρ) - S(σ)| ≤ |S_L(ρ) - S_L(σ)| + |S_S(ρ) - S_S(σ)|
       - Careful bookkeeping shows: ≤ T·log(n-1) + H(T)

    **Required infrastructure**:
    - Eigenvalue perturbation theory (relating D(ρ,σ) to eigenvalue differences)
    - Lipschitz bounds for -x log x
    - Combinatorial bounds on small eigenvalues
    - Properties of binary entropy -/
theorem fannes_inequality {n : ℕ} [NeZero n] (hn : n ≥ 2) (ρ σ : DensityOp n)
    (T : ℝ) (hT : T = traceDistance ρ.toOp σ.toOp) (hT_pos : 0 ≤ T) (hT_lt : T < 1)
    (hT_bound : T ≤ 1 - 1 / (n : ℝ)) :
    |vonNeumannEntropy ρ - vonNeumannEntropy σ| ≤
      T * Real.log (n - 1) + binaryEntropy T := by
  /-
  FANNES INEQUALITY PROOF

  The proof follows the standard approach using eigenvalue perturbation and
  entropy continuity bounds. The key steps are:

  1. Handle T = 0: trivial case where ρ = σ
  2. For T > 0, use WLOG S(ρ) ≥ S(σ) by symmetry of absolute value
  3. Show that each state's entropy can be related to a standard bound
  4. The key technical lemma: for probability distributions p, q with
     total variation ||p - q||₁ ≤ 2T, |H(p) - H(q)| ≤ T·log(n-1) + H(T)

  This is proved by:
  - If one distribution has a large component (≥ 1-T), use entropy_bound_with_large_eigenvalue
  - If both have all small components, they're both "spread out" and close to each other
  - The binary entropy H(T) accounts for the mixing between "concentrated" and "spread" mass

  Infrastructure used:
  - entropy_bound_with_large_eigenvalue: entropy bound when max eigenvalue ≥ 1-T
  - entropyTerm_lipschitz: Lipschitz bound for entropy term on [ε, 1]
  - eigenvalue_perturbation: ∑|λᵢ - μᵢ| ≤ 2T (from Weyl/Mirsky inequalities)
  -/

  -- The bound T*log(n-1) + H(T) is non-negative for T ∈ [0, 1)
  have h_bound_nonneg : 0 ≤ T * Real.log (n - 1) + binaryEntropy T := by
    apply add_nonneg
    · apply mul_nonneg hT_pos
      apply Real.log_nonneg
      have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith
    · exact binaryEntropy_nonneg T hT_pos (le_of_lt hT_lt)
  -- Handle T = 0 case: ρ = σ so the difference is 0
  by_cases hT_zero : T = 0
  · rw [hT_zero]
    simp only [zero_mul, binaryEntropy_zero, zero_add]
    have h_eq : ρ = σ := (traceDistance_eq_zero_iff ρ σ).mp (by rw [← hT, hT_zero])
    rw [h_eq]; simp
  -- Now T > 0
  have hT_pos' : 0 < T := lt_of_le_of_ne hT_pos (Ne.symm hT_zero)
  -- Get eigenvalue properties for ρ and σ
  have hρ_spec := eigenvaluesOf_spec ρ
  have hσ_spec := eigenvaluesOf_spec σ
  obtain ⟨hρ_nonneg, hρ_sum, _, _⟩ := hρ_spec
  obtain ⟨hσ_nonneg, hσ_sum, _, _⟩ := hσ_spec
  -- Bound using entropy_bound_with_large_eigenvalue
  -- Strategy: Check if each state has a large eigenvalue, and apply appropriate bounds
  -- Let B = T·log(n-1) + H(T) be our target bound
  let B := T * Real.log (n - 1) + binaryEntropy T
  -- Eigenvalue perturbation bound
  -- (eigenvalue_perturbation → weyl_eigenvalue_sum_bound)
  have h_pert : ∑ i, |eigenvaluesOf ρ i - eigenvaluesOf σ i| ≤ 2 * T := by
    rw [hT]; exact eigenvalue_perturbation ρ σ
  -- Check if ρ has a large eigenvalue
  by_cases hρ_large : ∃ i, eigenvaluesOf ρ i ≥ 1 - T
  · -- ρ has eigenvalue ≥ 1-T: apply entropy bound to ρ
    have hρ_bound : vonNeumannEntropy ρ ≤ B :=
      entropy_bound_with_large_eigenvalue (eigenvaluesOf ρ) hρ_nonneg hρ_sum T
        hT_bound hρ_large
    -- Similarly check σ
    by_cases hσ_large : ∃ i, eigenvaluesOf σ i ≥ 1 - T
    · -- Both have large eigenvalue: both bounded by B
      have hσ_bound : vonNeumannEntropy σ ≤ B :=
        entropy_bound_with_large_eigenvalue (eigenvaluesOf σ) hσ_nonneg hσ_sum T
          hT_bound hσ_large
      -- |S(ρ) - S(σ)| ≤ max(S(ρ), S(σ)) ≤ B (since both non-negative)
      have hS_ρ_nonneg : 0 ≤ vonNeumannEntropy ρ := vonNeumannEntropy_nonneg ρ
      have hS_σ_nonneg : 0 ≤ vonNeumannEntropy σ := vonNeumannEntropy_nonneg σ
      -- |a - b| ≤ max(a, b) when both are non-negative
      have h_abs_le_max : |vonNeumannEntropy ρ - vonNeumannEntropy σ| ≤
          max (vonNeumannEntropy ρ) (vonNeumannEntropy σ) := by
        by_cases h : vonNeumannEntropy ρ ≥ vonNeumannEntropy σ
        · rw [abs_of_nonneg (sub_nonneg.mpr h)]
          calc vonNeumannEntropy ρ - vonNeumannEntropy σ
              ≤ vonNeumannEntropy ρ := by linarith
            _ ≤ max (vonNeumannEntropy ρ) (vonNeumannEntropy σ) := le_max_left _ _
        · push Not at h
          rw [abs_of_neg (sub_neg.mpr h)]
          calc -(vonNeumannEntropy ρ - vonNeumannEntropy σ)
              = vonNeumannEntropy σ - vonNeumannEntropy ρ := by ring
            _ ≤ vonNeumannEntropy σ := by linarith
            _ ≤ max (vonNeumannEntropy ρ) (vonNeumannEntropy σ) := le_max_right _ _
      calc |vonNeumannEntropy ρ - vonNeumannEntropy σ|
          ≤ max (vonNeumannEntropy ρ) (vonNeumannEntropy σ) := h_abs_le_max
        _ ≤ max B B := max_le_max hρ_bound hσ_bound
        _ = B := max_self B
    · -- ρ has large eigenvalue, σ does not: use distribution_fannes_bound
      push Not at hσ_large
      unfold vonNeumannEntropy shannonEntropy
      exact distribution_fannes_bound (by omega) (eigenvaluesOf ρ) (eigenvaluesOf σ)
        hρ_nonneg hρ_sum hσ_nonneg hσ_sum T hT_bound h_pert
  · -- ρ has all eigenvalues < 1-T
    push Not at hρ_large
    by_cases hσ_large : ∃ i, eigenvaluesOf σ i ≥ 1 - T
    · -- σ has large eigenvalue, ρ does not: use distribution_fannes_bound
      unfold vonNeumannEntropy shannonEntropy
      exact distribution_fannes_bound (by omega) (eigenvaluesOf ρ) (eigenvaluesOf σ)
        hρ_nonneg hρ_sum hσ_nonneg hσ_sum T hT_bound h_pert
    · -- Neither has large eigenvalue: use distribution_fannes_bound
      push Not at hσ_large
      unfold vonNeumannEntropy shannonEntropy
      exact distribution_fannes_bound (by omega) (eigenvaluesOf ρ) (eigenvaluesOf σ)
        hρ_nonneg hρ_sum hσ_nonneg hσ_sum T hT_bound h_pert

/-- **Audenaert's inequality** (full continuity bound for von Neumann entropy).

For any two density operators ρ, σ on ℂⁿ with trace distance T = D(ρ,σ) ∈ [0,1]:
- If T ≤ 1 - 1/n:  |S(ρ) - S(σ)| ≤ T · log(n-1) + H(T)  (sharp, Audenaert 2007)
- If T > 1 - 1/n:  |S(ρ) - S(σ)| ≤ log(n)  (trivial entropy bound)

The first branch is `fannes_inequality`. The second branch (T > 1 - 1/n) uses the trivial
entropy bound log(n) (from `vonNeumannEntropy_le_log_dim`) rather than Audenaert's formula,
since the Audenaert bound is only tight when T is small relative to the dimension.

Reference: Audenaert, J. Phys. A 40 (2007), Theorem 1;
Wilde, Quantum Information Theory, Theorem 11.10.4. -/
theorem audenaert_inequality {n : ℕ} [NeZero n] (hn : n ≥ 2) (ρ σ : DensityOp n)
    (T : ℝ) (hT : T = traceDistance ρ.toOp σ.toOp) (hT_pos : 0 ≤ T) :
    |vonNeumannEntropy ρ - vonNeumannEntropy σ| ≤
      if T ≤ 1 - 1 / (n : ℝ)
      then T * Real.log (n - 1) + binaryEntropy T
      else Real.log n := by
  split_ifs with hcase
  · -- Branch: T ≤ 1 - 1/n. Apply fannes_inequality.
    -- Need T < 1: from T ≤ 1 - 1/n and n ≥ 2 we get 1/n ≥ 1/2 > 0, so T ≤ 1 - 1/n < 1.
    have hn_cast : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    have h_one_div_pos : 0 < 1 / (n : ℝ) := by positivity
    have hT_lt : T < 1 := by linarith
    exact fannes_inequality hn ρ σ T hT hT_pos hT_lt hcase
  · -- Branch: T > 1 - 1/n. Use the trivial bound |S(ρ) - S(σ)| ≤ log n.
    -- Both S(ρ) and S(σ) lie in [0, log n].
    have hρ_nonneg : 0 ≤ vonNeumannEntropy ρ := vonNeumannEntropy_nonneg ρ
    have hσ_nonneg : 0 ≤ vonNeumannEntropy σ := vonNeumannEntropy_nonneg σ
    have hρ_le : vonNeumannEntropy ρ ≤ Real.log n := vonNeumannEntropy_le_log_dim ρ
    have hσ_le : vonNeumannEntropy σ ≤ Real.log n := vonNeumannEntropy_le_log_dim σ
    -- |a - b| ≤ max(a, b) ≤ log n when both are non-negative
    rw [abs_le]
    constructor
    · linarith
    · linarith

end InfoTheory.Continuity

end
