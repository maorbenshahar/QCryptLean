import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDSingleCopyMoments
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.RtFunction
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQJointEntropyLowerBound
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.IsometricInvariance

/-!
# Single-copy `r_t` pre-log envelope for Renner's `thm:Hmincondrep` (bit track)

The single-copy `r_t` pre-log envelope for Renner's bound (main.tex:4818–4906):

  `m(s) ≤ rt(s, μ) − s·(ln 2)·H_bits + 1`,

with `m(s) = iidAEPSingleCopyMGF ρ σ s`, `μ = iidAEPSpectralRadius ρ σ`,
`H_bits = iidAEPBitEntropyContribution ρ hρ_norm σ`, together with the
quadratic-CGF bound `singleCopyMGF_logb_le` and the `N`-copy collision-trace tail
bound `iidAEPCollisionTrace_le_rtErrorBound` consumed by
`IIDChernoffTail.lean`.

## Main statements

- `singleCopy_perTriple_rt_bound` — the per-triple scalar `r_t` bound
  `(p/q)^s ≤ rt(s, q/p + p/q + 2) − s·ln(q/p) + 1`.
- `singleCopy_rt_envelope` — the single-copy `r_t` pre-log envelope.
- `singleCopyMGF_logb_le` — the single-copy quadratic cumulant-generating-function
  bound.
- `iidAEPCollisionTrace_le_rtErrorBound` — the `N`-copy collision-trace tail
  bound (main.tex:4962).

The spectral-data definitions and moment identities consumed here are defined in
`IIDSingleCopyMoments.lean`.
-/

open Quantum.Operators Matrix Quantum.TensorProducts
open InfoTheory.SmoothMinEntropy InfoTheory.VonNeumannEntropy
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The per-triple scalar `r_t` bound -/

/-- **Per-triple scalar `r_t` bound.** For a live triple with block eigenvalue
`p > 0` and reference eigenvalue `q > 0`, writing `z := q/p > 0` and
`Y := z + z⁻¹ + 2 ∈ [4,∞)`,

  `(p/q)^s ≤ rt(s, Y) − s·ln(q/p) + 1`,

for every tilt `s ≥ 0`. This is the per-letter input to the Jensen aggregation in
`singleCopy_rt_envelope`. -/
theorem singleCopy_perTriple_rt_bound
    {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s) :
    (p / q) ^ s
      ≤ InfoTheory.SmoothMinEntropy.rt s (q / p + p / q + 2) - s * Real.log (q / p) + 1 := by
  have hz : 0 < q / p := div_pos hq hp
  have hzinv : (q / p)⁻¹ = p / q := inv_div q p
  have key : (p / q) ^ s = ((q / p) ^ s)⁻¹ := by
    rw [← hzinv, Real.inv_rpow hz.le]
  have hpq_eq : (p / q) ^ s = InfoTheory.SmoothMinEntropy.rt (-s) (q / p) - s * Real.log (q / p) + 1
      := by
    rw [key]; unfold InfoTheory.SmoothMinEntropy.rt; rw [Real.rpow_neg hz.le]; ring
  have hineq1 : InfoTheory.SmoothMinEntropy.rt (-s) (q / p) ≤ InfoTheory.SmoothMinEntropy.rt |(-s)|
      (q / p + (q / p)⁻¹) :=
    rt_le_rt_abs_z_add_inv (-s) (q / p) hz
  have habs : |(-s)| = s := by rw [abs_neg, abs_of_nonneg hs]
  rw [habs, hzinv] at hineq1
  -- `z + z⁻¹ ≥ 1` for `z > 0`: one of `z`, `z⁻¹` is at least `1`, the other is positive.
  have hone : (1 : ℝ) ≤ q / p + p / q := by
    rcases le_total 1 (q / p) with h | h
    · exact h.trans (le_add_of_nonneg_right (div_pos hp hq).le)
    · have h' : 1 ≤ p / q := hzinv ▸ (one_le_inv₀ hz).mpr h
      exact h'.trans (le_add_of_nonneg_left hz.le)
  have hmono := rt_monotone_on_one_le s (Set.mem_Ici.mpr hone)
    (Set.mem_Ici.mpr (hone.trans (le_add_of_nonneg_right zero_le_two)))
    (le_add_of_nonneg_right zero_le_two)
  -- `(p/q)^s = rt(-s, z) − s·ln z + 1 ≤ rt(s, z + z⁻¹) − s·ln z + 1 ≤ rt(s, Y) − s·ln z + 1`.
  linarith only [hpq_eq, hineq1, hmono]

/-! ## Normalization, reweighting, and the mean argument -/

/-- **Rewriting a live summand of the spectral expansion.**
The summand `p^{1+s} q^{-s} overlap` equals `P·(p/q)^s`. The `p = 0` terms
vanish (`0^{1+s} = 0`); the `q = 0` terms vanish because `hfeas` forces the overlap
to `0` there (so no `0^{-s}` hazard); on live terms `p^{1+s} q^{-s} = p·p^s q^{-s}`
and `(p/q)^s = p^s q^{-s}`. -/
private lemma singleCopy_spectralTerm_eq_weighted_pq_pow
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    {s : ℝ} (hs : 0 ≤ s) (x : X) (a b : Fin n) :
    singleCopyBlockEigenvalue ρ x a ^ (1 + s)
        * singleCopyReferenceEigenvalue σ b ^ (-s)
        * singleCopyOverlap ρ σ x a b
      = singleCopyProbWeight ρ σ x a b
        * (singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b) ^ s := by
  classical
  have hp_nn : 0 ≤ singleCopyBlockEigenvalue ρ x a :=
    singleCopyBlockEigenvalue_nonneg ρ x a
  rcases eq_or_lt_of_le hp_nn with hp0 | hppos
  · -- `p = 0`
    rw [singleCopyProbWeight, ← hp0, Real.zero_rpow (by positivity)]
    ring
  · have hq_nn : 0 ≤ singleCopyReferenceEigenvalue σ b :=
      singleCopyReferenceEigenvalue_nonneg σ b
    rcases eq_or_lt_of_le hq_nn with hq0 | hqpos
    · -- `q = 0`: overlap vanishes by support containment
      have hP0 := singleCopy_probWeight_eq_zero_of_ref_zero ρ σ hfeas x a b hq0.symm
      have hov0 : singleCopyOverlap ρ σ x a b = 0 := by
        have hpv : singleCopyBlockEigenvalue ρ x a * singleCopyOverlap ρ σ x a b = 0 := hP0
        rcases mul_eq_zero.mp hpv with h | h
        · exact absurd h hppos.ne'
        · exact h
      rw [hP0, hov0]; ring
    · -- live term `p, q > 0`
      have hpq : (singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b) ^ s
          = singleCopyBlockEigenvalue ρ x a ^ s
              * singleCopyReferenceEigenvalue σ b ^ (-s) := by
        rw [Real.div_rpow hp_nn hqpos.le, Real.rpow_neg hqpos.le, div_eq_mul_inv]
      rw [singleCopyProbWeight, hpq, Real.rpow_add hppos, Real.rpow_one]
      ring

/-- **The single-copy MGF as a `P`-weighted `(p/q)^s` sum.**

  `m(s) = Σ_{x,a,b} P(x,a,b) · (p_{x,a} / q_b)^s`. -/
lemma singleCopyMGF_eq_weighted_pq_pow
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    {s : ℝ} (hs : 0 ≤ s) :
    iidAEPSingleCopyMGF ρ σ s
      = ∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
          singleCopyProbWeight ρ σ x a b
            * (singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b) ^ s := by
  classical
  rw [singleCopyMGF_spectral_expansion ρ σ hfeas hs]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => singleCopy_spectralTerm_eq_weighted_pq_pow ρ σ hfeas hs x a
        b)))

/-- **AM–GM lower bound for the per-triple Jensen argument.** For `p, q > 0`,
`q/p + p/q + 2 ≥ 4`. -/
private lemma singleCopy_meanArg_ge_four_of_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (4 : ℝ) ≤ q / p + p / q + 2 := by
  have hz : 0 < q / p := div_pos hq hp
  have hmul : (q / p) * (p / q) = 1 := by field_simp
  nlinarith [sq_nonneg (q / p - 1), hmul, hz, div_pos hp hq]

/-- **The mean Jensen argument is bounded by the spectral radius.** With per-triple
argument `Y(x,a,b) = q_b/p_{x,a} + p_{x,a}/q_b + 2`,

  `Σ_{x,a,b} P(x,a,b) · Y(x,a,b) ≤ μ = iidAEPSpectralRadius ρ σ`.

This is the monotonicity input that lets `singleCopy_rt_envelope` replace the
Jensen mean argument by `μ`. -/
lemma singleCopy_meanArg_le_spectralRadius
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ)) :
    ∑ x : X, ∑ a : Fin n, ∑ b : Fin n,
        singleCopyProbWeight ρ σ x a b
          * (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
              + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2)
      ≤ iidAEPSpectralRadius ρ σ := by
  classical
  have hdist : ∀ (x : X) (a b : Fin n),
      singleCopyProbWeight ρ σ x a b
          * (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
              + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2)
        = singleCopyProbWeight ρ σ x a b
              * (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a)
            + singleCopyProbWeight ρ σ x a b
              * (singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b)
            + 2 * singleCopyProbWeight ρ σ x a b := by
    intro x a b; ring
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => hdist x a b)))]
  simp only [Finset.sum_add_distrib]
  have h2P : ∑ x : X, ∑ a : Fin n, ∑ b : Fin n, 2 * singleCopyProbWeight ρ σ x a b
      = 2 * ∑ x : X, ∑ a : Fin n, ∑ b : Fin n, singleCopyProbWeight ρ σ x a b := by
    simp only [Finset.mul_sum]
  rw [h2P, sum_singleCopyProbWeight_eq_one ρ hρ_norm σ,
    singleCopyMGF_pOverq_moment ρ σ hfeas]
  have h8c := singleCopyMGF_qOverp_le_classicalRank ρ σ
  unfold iidAEPSpectralRadius
  linarith [h8c]

/-- **Positivity of block/reference eigenvalues at a live triple.** If the weight
`P(x,a,b) > 0` then both `p_{x,a} > 0` and `q_b > 0` (else `P = 0`). -/
private lemma singleCopy_pos_of_weight_pos
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (x : X) (a b : Fin n) (hW : 0 < singleCopyProbWeight ρ σ x a b) :
    0 < singleCopyBlockEigenvalue ρ x a ∧ 0 < singleCopyReferenceEigenvalue σ b := by
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le (singleCopyBlockEigenvalue_nonneg ρ x a) with hp0 | hppos
    · exfalso
      have : singleCopyProbWeight ρ σ x a b = 0 := by
        unfold singleCopyProbWeight; rw [← hp0]; ring
      linarith
    · exact hppos
  · rcases eq_or_lt_of_le (singleCopyReferenceEigenvalue_nonneg σ b) with hq0 | hqpos
    · exfalso
      have := singleCopy_probWeight_eq_zero_of_ref_zero ρ σ hfeas x a b hq0.symm
      linarith
    · exact hqpos

/-- **Per-triple `r_t` upper bound, weighted.** The per-letter scalar bound scaled
by the nonnegative weight `P`. Dead triples (`P = 0`) are trivial; live triples
have `p, q > 0`. -/
private lemma singleCopy_weighted_perTriple_rt_bound
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    {s : ℝ} (hs : 0 ≤ s) (x : X) (a b : Fin n) :
    singleCopyProbWeight ρ σ x a b
        * (singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b) ^ s
      ≤ singleCopyProbWeight ρ σ x a b
        * (InfoTheory.SmoothMinEntropy.rt s (singleCopyReferenceEigenvalue σ b /
            singleCopyBlockEigenvalue ρ x a
              + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2)
            - s * Real.log (singleCopyReferenceEigenvalue σ b
                / singleCopyBlockEigenvalue ρ x a)
            + 1) := by
  classical
  have hW_nn : 0 ≤ singleCopyProbWeight ρ σ x a b := singleCopyProbWeight_nonneg ρ σ x a b
  rcases eq_or_lt_of_le hW_nn with hW0 | hWpos
  · rw [← hW0]; simp
  · obtain ⟨hp_pos, hq_pos⟩ := singleCopy_pos_of_weight_pos ρ σ hfeas x a b hWpos
    exact mul_le_mul_of_nonneg_left
      (singleCopy_perTriple_rt_bound hp_pos hq_pos hs) hW_nn

/-- **Nested-sum Jensen for the concave `r_t`.** Over the triple index `(x,a,b)`,
flattened to the product `X × Fin n × Fin n`, Jensen's inequality
(`ConcaveOn.le_map_sum`) for a concave function with nonnegative weights summing to
`1` and points `max (G ·) 4 ∈ [4,∞)`:

  `Σ P · rt(s, max G 4) ≤ rt(s, Σ P · max G 4)`. -/
private lemma singleCopy_jensen_nested
    {X : Type*} [Fintype X] {n : ℕ}
    (P : X → Fin n → Fin n → ℝ) (G : X → Fin n → Fin n → ℝ)
    (hPnn : ∀ x a b, 0 ≤ P x a b)
    (hsum : ∑ x, ∑ a, ∑ b, P x a b = 1)
    {s : ℝ} (hconc : ConcaveOn ℝ (Set.Ici (4 : ℝ)) (InfoTheory.SmoothMinEntropy.rt s)) :
    (∑ x, ∑ a, ∑ b, P x a b * InfoTheory.SmoothMinEntropy.rt s (max (G x a b) 4))
      ≤ InfoTheory.SmoothMinEntropy.rt s (∑ x, ∑ a, ∑ b, P x a b * max (G x a b) 4) := by
  classical
  have hpe : ∀ (F : X → Fin n → Fin n → ℝ),
      (∑ i : X × Fin n × Fin n, F i.1 i.2.1 i.2.2) = ∑ x, ∑ a, ∑ b, F x a b := by
    intro F; simp [Fintype.sum_prod_type]
  have hmap := hconc.le_map_sum (t := (Finset.univ : Finset (X × Fin n × Fin n)))
    (w := fun i => P i.1 i.2.1 i.2.2)
    (p := fun i => max (G i.1 i.2.1 i.2.2) 4)
    (fun i _ => hPnn i.1 i.2.1 i.2.2)
    (by
      rw [show (∑ i : X × Fin n × Fin n, P i.1 i.2.1 i.2.2) = ∑ x, ∑ a, ∑ b, P x a b from
        hpe (fun x a b => P x a b)]
      exact hsum)
    (fun i _ => Set.mem_Ici.mpr (le_max_right _ _))
  simp only [smul_eq_mul] at hmap
  calc (∑ x, ∑ a, ∑ b, P x a b * InfoTheory.SmoothMinEntropy.rt s (max (G x a b) 4))
      = ∑ i : X × Fin n × Fin n,
          P i.1 i.2.1 i.2.2 * InfoTheory.SmoothMinEntropy.rt s (max (G i.1 i.2.1 i.2.2) 4) :=
        (hpe (fun x a b => P x a b * InfoTheory.SmoothMinEntropy.rt s (max (G x a b) 4))).symm
    _ ≤ InfoTheory.SmoothMinEntropy.rt s (∑ i : X × Fin n × Fin n,
          P i.1 i.2.1 i.2.2 * max (G i.1 i.2.1 i.2.2) 4) := by exact hmap
    _ = InfoTheory.SmoothMinEntropy.rt s (∑ x, ∑ a, ∑ b, P x a b * max (G x a b) 4) := by
        congr 1
        exact hpe (fun x a b => P x a b * max (G x a b) 4)

/-! ## The single-copy `r_t` pre-log envelope -/

/-- **Single-copy `r_t` pre-log envelope** (Renner, main.tex:4836–4906). The
operator inequality, before taking the logarithm,

  `m(s) ≤ rt s μ − s·ln2·H_bits + 1`,

with `m(s) = iidAEPSingleCopyMGF ρ σ s`, `μ = iidAEPSpectralRadius ρ σ`,
`H_bits = iidAEPBitEntropyContribution ρ hρ_norm σ`, and `rt = InfoTheory.SmoothMinEntropy.rt`.

`hfeas` (support gate `supp ρ_x ⊆ supp σ`) keeps the spectral expansion and the
tilted moments finite. `hrange` (`s·ln μ ≤ ln 2`) gives the admissibility
`s ≤ 1/2` on which `rt(s,·)` is concave on `[4,∞)`, which the Jensen step needs. -/
theorem singleCopy_rt_envelope
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    {s : ℝ} (hs : 0 ≤ s)
    (hrange : s * Real.log (iidAEPSpectralRadius ρ σ) ≤ Real.log 2) :
    iidAEPSingleCopyMGF ρ σ s
      ≤ InfoTheory.SmoothMinEntropy.rt s (iidAEPSpectralRadius ρ σ)
          - s * Real.log 2 * (iidAEPBitEntropyContribution ρ hρ_norm σ)
          + 1 := by
  classical
  have hexpand := singleCopyMGF_eq_weighted_pq_pow ρ σ hfeas hs
  have hentropy := singleCopyMGF_entropyMoment ρ hρ_norm σ hfeas
  have hmean := singleCopy_meanArg_le_spectralRadius ρ hρ_norm σ hfeas
  have hsum1 := sum_singleCopyProbWeight_eq_one ρ hρ_norm σ
  have hμ4 := four_le_iidAEPSpectralRadius ρ hρ_norm σ hfeas
  have hs_half := s_le_half_of_mul_log_spectralRadius_le_log_two ρ σ hμ4 hs hrange
  have hconcave : ConcaveOn ℝ (Set.Ici (4 : ℝ)) (InfoTheory.SmoothMinEntropy.rt s) :=
    rt_concave_on_four_le ⟨by linarith, hs_half⟩
  set μ := iidAEPSpectralRadius ρ σ with hμ_def
  set H := iidAEPBitEntropyContribution ρ hρ_norm σ with hH_def
  -- (1) reweighting: the `max(·,4)` clamp is invisible against the weight `P`
  have hmaxeq : ∀ (x : X) (a b : Fin n), singleCopyProbWeight ρ σ x a b ≠ 0 →
      max (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
          + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2) 4
        = singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
          + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2 := by
    intro x a b hne
    have hWpos : 0 < singleCopyProbWeight ρ σ x a b :=
      lt_of_le_of_ne (singleCopyProbWeight_nonneg ρ σ x a b) (Ne.symm hne)
    obtain ⟨hp, hq⟩ := singleCopy_pos_of_weight_pos ρ σ hfeas x a b hWpos
    exact max_eq_left (singleCopy_meanArg_ge_four_of_pos hp hq)
  have hWg : (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
        * max (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
            + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2) 4)
      = ∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
          * (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
              + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2) := by
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => ?_)))
    rcases eq_or_ne (singleCopyProbWeight ρ σ x a b) 0 with h0 | hne
    · rw [h0]; ring
    · rw [hmaxeq x a b hne]
  have hWrt : (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
        * InfoTheory.SmoothMinEntropy.rt s (singleCopyReferenceEigenvalue σ b /
            singleCopyBlockEigenvalue ρ x a
            + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2))
      = ∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
          * InfoTheory.SmoothMinEntropy.rt s (max (singleCopyReferenceEigenvalue σ b /
              singleCopyBlockEigenvalue ρ x a
              + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2) 4) := by
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => ?_)))
    rcases eq_or_ne (singleCopyProbWeight ρ σ x a b) 0 with h0 | hne
    · rw [h0]; ring
    · rw [hmaxeq x a b hne]
  -- (2) the clamped mean argument lies in `[4, μ]`
  have hmean_max : (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
        * max (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
            + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2) 4)
      ≤ μ := by rw [hWg]; exact hmean
  have hge4 : (4 : ℝ) ≤ ∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
        * max (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
            + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2) 4 := by
    have hstep : (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b * 4)
        ≤ ∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
            * max (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
                + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2) 4 := by
      refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun a _ =>
        Finset.sum_le_sum (fun b _ => ?_)))
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (singleCopyProbWeight_nonneg ρ σ x a b)
    have hval : (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b * 4) = 4 := by
      rw [show (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b * 4)
            = (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b) * 4 from by
          simp only [Finset.sum_mul], hsum1, one_mul]
    exact hval.symm.trans_le hstep
  -- (3) monotonicity of `rt s` on `[1, ∞)`
  have hmono : InfoTheory.SmoothMinEntropy.rt s (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
        * max (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
            + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2) 4)
      ≤ InfoTheory.SmoothMinEntropy.rt s μ :=
    rt_monotone_on_one_le s (Set.mem_Ici.mpr ((by norm_num : (1 : ℝ) ≤ 4).trans hge4))
      (Set.mem_Ici.mpr ((by norm_num : (1 : ℝ) ≤ 4).trans hμ4)) hmean_max
  -- (4) Jensen on the concave `rt s`
  have hjensen := singleCopy_jensen_nested (singleCopyProbWeight ρ σ)
    (fun x a b => singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
        + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2)
    (fun x a b => singleCopyProbWeight_nonneg ρ σ x a b) hsum1 hconcave
  -- linear-term bookkeeping: factor `s` out of the log moment
  have hsmul : (∑ x, ∑ a, ∑ b, s * (singleCopyProbWeight ρ σ x a b
        * Real.log (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a)))
      = s * ∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
          * Real.log (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a) := by
    simp only [Finset.mul_sum]
  -- decompose the per-triple bound into the three moment sums
  have hdecomp : (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
          * (InfoTheory.SmoothMinEntropy.rt s (singleCopyReferenceEigenvalue σ b /
              singleCopyBlockEigenvalue ρ x a
                + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2)
              - s * Real.log (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a)
              + 1))
      = (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
            * InfoTheory.SmoothMinEntropy.rt s (singleCopyReferenceEigenvalue σ b /
                singleCopyBlockEigenvalue ρ x a
                + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2))
          - s * (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
              * Real.log (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a))
          + (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b) := by
    have hterm : ∀ (x : X) (a b : Fin n),
        singleCopyProbWeight ρ σ x a b
            * (InfoTheory.SmoothMinEntropy.rt s (singleCopyReferenceEigenvalue σ b /
                singleCopyBlockEigenvalue ρ x a
                  + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2)
                - s * Real.log (singleCopyReferenceEigenvalue σ b
                    / singleCopyBlockEigenvalue ρ x a)
                + 1)
          = singleCopyProbWeight ρ σ x a b
                * InfoTheory.SmoothMinEntropy.rt s (singleCopyReferenceEigenvalue σ b /
                    singleCopyBlockEigenvalue ρ x a
                    + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2)
              - s * (singleCopyProbWeight ρ σ x a b
                  * Real.log (singleCopyReferenceEigenvalue σ b
                      / singleCopyBlockEigenvalue ρ x a))
              + singleCopyProbWeight ρ σ x a b := by
      intro x a b; ring
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => hterm x a b)))]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hsmul]
  -- assemble the chain
  calc iidAEPSingleCopyMGF ρ σ s
      = ∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
          * (singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b) ^ s := hexpand
    _ ≤ ∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
          * (InfoTheory.SmoothMinEntropy.rt s (singleCopyReferenceEigenvalue σ b /
              singleCopyBlockEigenvalue ρ x a
                + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2)
              - s * Real.log (singleCopyReferenceEigenvalue σ b
                  / singleCopyBlockEigenvalue ρ x a)
              + 1) := by
        refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum (fun b _ => ?_)))
        exact singleCopy_weighted_perTriple_rt_bound ρ σ hfeas hs x a b
    _ = (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
            * InfoTheory.SmoothMinEntropy.rt s (singleCopyReferenceEigenvalue σ b /
                singleCopyBlockEigenvalue ρ x a
                + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2))
          - s * (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
              * Real.log (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a))
          + (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b) := hdecomp
    _ = (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
            * InfoTheory.SmoothMinEntropy.rt s (max (singleCopyReferenceEigenvalue σ b /
                singleCopyBlockEigenvalue ρ x a
                + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2) 4))
          - s * (Real.log 2 * H) + 1 := by rw [hWrt, hentropy, hsum1]
    _ ≤ InfoTheory.SmoothMinEntropy.rt s (∑ x, ∑ a, ∑ b, singleCopyProbWeight ρ σ x a b
            * max (singleCopyReferenceEigenvalue σ b / singleCopyBlockEigenvalue ρ x a
                + singleCopyBlockEigenvalue ρ x a / singleCopyReferenceEigenvalue σ b + 2) 4)
          - s * (Real.log 2 * H) + 1 := by gcongr
    _ ≤ InfoTheory.SmoothMinEntropy.rt s μ - s * (Real.log 2 * H) + 1 := by gcongr
    _ = InfoTheory.SmoothMinEntropy.rt s μ - s * Real.log 2 * H + 1 := by ring

/-- **Single-copy quadratic cumulant-generating-function bound**
(Renner `lem:rtbound`, main.tex:10487, with the `r_t` definition `eq:rtdef` at
main.tex:4206). For a nonnegative tilt `s ≥ 0` **in
Renner's range** `s·ln μ ≤ ln 2` (`hrange`),

  `log₂ m(s) ≤ −s·H_bits + (1/ln2 − 1/2)·(s·ln μ)²`,

where `m(s) = iidAEPSingleCopyMGF ρ σ s = Σ_x tr[ρ_x^{1+s} σ^{−s}]`,
`H_bits = iidAEPBitEntropyContribution ρ hρ_norm σ` is the σ-relative
conditional von Neumann entropy in bits, and
`μ = iidAEPSpectralRadius ρ σ = classicalRank + Σ_x tr[ρ_x² σ^{−1}] + 2`
(natural log of `μ`, with `μ ≥ 2`). The linear term `−s·H_bits` is the first
cumulant `K'(0) = −H_bits·ln2` normalized to bits; the quadratic coefficient
`(1/ln2 − 1/2)` is the Taylor coefficient `½` plus the bit-conversion slack
`(1 − ln2)/ln2`.

The range hypothesis `hrange` is Renner's `lem:rtbound` gate `|s·log μ| ≤ 1`
(here `|s·ln μ| ≤ ln 2`, i.e. `|s·log₂ μ| ≤ 1`), the admissibility window in
which the `r_t` quadratic envelope `rt(s, μ) ≤ ½ (s·ln μ)²` is valid. Outside it
the tilted second cumulant exceeds `(ln μ)²` (it reaches `≈ 1.99·(ln μ)²` near
`s ≈ 1`), so the bound would fail; the gate is therefore load-bearing.

`hfeas` (single-copy support gate `supp ρ_x ⊆ supp σ`) keeps `σ^{−s}` and the
collision moments finite, and is also load-bearing. -/
theorem singleCopyMGF_logb_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    {s : ℝ} (hs : 0 ≤ s)
    (hrange : s * Real.log (iidAEPSpectralRadius ρ σ) ≤ Real.log 2) :
    Real.logb 2 (iidAEPSingleCopyMGF ρ σ s)
      ≤ -s * iidAEPBitEntropyContribution ρ hρ_norm σ
        + (1 / Real.log 2 - 1 / 2)
          * (s * Real.log (iidAEPSpectralRadius ρ σ)) ^ 2 := by
  classical
  set μ := iidAEPSpectralRadius ρ σ with hμ_def
  set m := iidAEPSingleCopyMGF ρ σ s with hm_def
  set H := iidAEPBitEntropyContribution ρ hρ_norm σ with hH_def
  -- positivity of `m` (needed to take `Real.log`)
  have hm_pos : 0 < m := iidAEPSingleCopyMGF_pos ρ hρ_norm σ hfeas hs
  -- `2 ≤ μ`, hence `1 < μ` and `log μ > 0`
  have hμ2 : (2 : ℝ) ≤ μ := hμ_def ▸ two_le_iidAEPSpectralRadius ρ σ
  have hμ1 : (1 : ℝ) < μ := by linarith
  have hL_pos : 0 < Real.log μ := Real.log_pos hμ1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2ne : Real.log 2 ≠ 0 := ne_of_gt hl2
  -- the deep operator envelope
  have henv := singleCopy_rt_envelope ρ hρ_norm σ hfeas hs hrange
  -- scalar endgame ----------------------------------------------------------
  -- (1) `log m ≤ m - 1`
  have hlog_le : Real.log m ≤ m - 1 := Real.log_le_sub_one_of_pos hm_pos
  -- (C) Renner's `r_t` quadratic envelope, in range
  have hrange' : s ≤ Real.log 2 / Real.log μ := (le_div_iff₀ hL_pos).mpr hrange
  have hlo : -(Real.log 2 / Real.log μ) ≤ s := by
    have hpos : 0 < Real.log 2 / Real.log μ := div_pos hl2 hL_pos
    linarith
  have hC := rt_le_quadratic_bound hμ1 hlo hrange'
  -- (5) numeric coefficient gate, in `(log 2)²` form, derived from
  -- `one_sub_log_two_div_log_two_pow_three_le_inv_log_two_sub_half`
  have hgate2 : (1 - Real.log 2) / (Real.log 2) ^ 2 ≤ 1 - Real.log 2 / 2 := by
    have h := one_sub_log_two_div_log_two_pow_three_le_inv_log_two_sub_half
    have e1 : (1 - Real.log 2) / (Real.log 2) ^ 2
        = Real.log 2 * ((1 - Real.log 2) / (Real.log 2) ^ 3) := by
      field_simp
    have e2 : 1 - Real.log 2 / 2 = Real.log 2 * (1 / Real.log 2 - 1 / 2) := by
      field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h (le_of_lt hl2)
  -- multiply the gate by the nonnegative square factor
  have hprod : (1 - Real.log 2) / (Real.log 2) ^ 2 * ((Real.log μ) ^ 2 * s ^ 2)
      ≤ (1 - Real.log 2 / 2) * ((Real.log μ) ^ 2 * s ^ 2) :=
    mul_le_mul_of_nonneg_right hgate2 (by positivity)
  -- assemble: rewrite the goal to a polynomial inequality and close it
  have hRHS : (-s * H + (1 / Real.log 2 - 1 / 2) * (s * Real.log μ) ^ 2) * Real.log 2
      = -s * Real.log 2 * H + (1 - Real.log 2 / 2) * (s * Real.log μ) ^ 2 := by
    field_simp
  rw [Real.logb, div_le_iff₀ hl2, hRHS]
  -- `log m ≤ m − 1 ≤ rt s μ − s·ln2·H ≤ c·(ln μ)²s² − s·ln2·H ≤ (1 − ln2/2)·(s·ln μ)² − s·ln2·H`,
  -- with `c = (1 − ln 2)/(ln 2)²` the `r_t` quadratic constant.
  calc Real.log m
      ≤ m - 1 := hlog_le
    _ ≤ InfoTheory.SmoothMinEntropy.rt s μ - s * Real.log 2 * H := sub_le_iff_le_add.mpr henv
    _ ≤ (1 - Real.log 2) / (Real.log 2) ^ 2 * ((Real.log μ) ^ 2 * s ^ 2)
          - s * Real.log 2 * H := by
        rw [← mul_assoc]; exact sub_le_sub_right hC _
    _ ≤ (1 - Real.log 2 / 2) * ((Real.log μ) ^ 2 * s ^ 2) - s * Real.log 2 * H :=
        sub_le_sub_right hprod _
    _ = -s * Real.log 2 * H + (1 - Real.log 2 / 2) * (s * Real.log μ) ^ 2 := by ring

/-- **Scalar gate inequality** behind the clamped-tilt endgame. With `v = s·a`
the tilt-magnitude and `w = d·b/a` the optimal magnitude (`a = log μ`,
`b = log 2`, `d = δ` the per-block bit penalty), the quadratic CGF bound's
excess over the relaxed-envelope exponent is `(1/b − 1/2)·v² − v·w/b + w²/2`. It
is `≤ 0` whenever `0 ≤ v ≤ w` (then it equals `(1/b − 1/2)(v − w)²`-type slack
that vanishes at `v = w`) **or** `v = b` with `w ∈ [b, 2 − b]` (the clamped
boundary case, where `2nf − 2nf² ≥ b − b²/2` holds for `nf = w/2 ∈ [b/2,
1−b/2]`). The two cases cover the clamped tilt `v = min(w, b)` under the
large-block regime `w ≤ 2 − b`. -/
private lemma collisionMGF_scalar_gate
    (b v w : ℝ) (hb0 : 0 < b)
    (hvmin : v = min w b) (hwub : w ≤ 2 - b) :
    (1 / b - 1 / 2) * v ^ 2 - v * w / b + w ^ 2 / 2 ≤ 0 := by
  have hbne : b ≠ 0 := ne_of_gt hb0
  rcases le_total w b with hwb | hbw
  · -- `v = w`: the excess is `(1/b − 1/2)w² − w²/b + w²/2 = 0`.
    have hv : v = w := by rw [hvmin, min_eq_left hwb]
    rw [hv]
    have : (1 / b - 1 / 2) * w ^ 2 - w * w / b + w ^ 2 / 2 = 0 := by
      field_simp; ring
    rw [this]
  · -- `v = b`: need `b − b²/2 − w + w²/2 ≤ 0`, i.e. `2w − w² ≥ 2b − b²`, which
    -- holds for `w ∈ [b, 2 − b]` since `w(2 − w)` is symmetric about `w = 1`.
    have hv : v = b := by rw [hvmin, min_eq_right hbw]
    rw [hv]
    have hkey : (1 / b - 1 / 2) * b ^ 2 - b * w / b + w ^ 2 / 2
        = b - b ^ 2 / 2 - w + w ^ 2 / 2 := by
      field_simp
    rw [hkey]
    -- `2w − w² − (2b − b²) = (w − b)(2 − w − b) ≥ 0` since `w ≥ b`, `w + b ≤ 2`.
    nlinarith [mul_nonneg (sub_nonneg.mpr hbw) (by linarith : (0:ℝ) ≤ 2 - w - b)]

/-! ## Entropy cancellation and scalar endgame -/

/-- **Operator-collision MGF tail bound** (Renner, main.tex:4962). At the pinned
optimal tilt `s = −W.rtTilt ≥ 0`, the `N`-copy collision trace obeys

  `iidAEPCollisionTrace ρ σ N (−W.rtTilt)
      ≤ weightCapScale W ^ (−W.rtTilt) · iidAEPRtErrorBound ρ σ N ε W`,

where `iidAEPRtErrorBound ρ σ N ε W = 2^{−N·δ²/(2·(log₂ μ)²)}` is Renner's
relaxed Gaussian tail target and `μ = iidAEPSpectralRadius ρ σ`.

Load-bearing hypotheses: `hfeas` (support gate `supp ρ_x ⊆ supp σ`) keeps `σ^{−s}`
and the collision moments finite; `hregime` (large-block regime
`2·noiseFactor ≤ 2 − ln 2`) places the clamped tilt in the range where the
quadratic envelope holds; `hcalib` calibrates the witness entropy threshold to
`N·(H_bits − δ)`, supplying the entropy cancellation; `hparams` pins the tilt to
the clamped optimum `min(δ·ln2/(ln μ)², ln2/ln μ)`. -/
theorem iidAEPCollisionTrace_le_rtErrorBound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    {n : ℕ} [NeZero n]
    (ρ : CQState X n) (hρ_norm : ∑ x : X, (ρ.stateMap x).trace = 1)
    (σ : DensityOp n)
    (n_copies : ℕ) [NeZero (n ^ n_copies)] (ε : ℝ)
    (W : IIDAEPSpectralWitness X n n_copies)
    (hfeas : hasFeasibleLambda ρ (DensityOp.toSubDensityOp σ))
    (hparams : iidAEPRtParameters ρ σ ε W)
    (hregime : iidAEPLargeBlockRegime n_copies ε)
    (hcalib : W.entropyThreshold =
      iidAEPBitBlockEntropyFloor ρ hρ_norm σ n_copies ε) :
    iidAEPCollisionTrace ρ σ n_copies (-W.rtTilt)
      ≤ weightCapScale W ^ (-W.rtTilt)
        * iidAEPRtErrorBound ρ σ n_copies ε W := by
  classical
  -- scalar sign facts for the clamped optimal tilt `s = −W.rtTilt`
  have htsf_nonneg : 0 ≤ ρ.tracedSquareTimesInvFactor σ :=
    tracedSquareTimesInvFactor_nonneg ρ σ
  have hμ2 : (2 : ℝ) ≤ iidAEPSpectralRadius ρ σ :=
    two_le_iidAEPSpectralRadius ρ σ
  have hLpos : 0 < Real.log (iidAEPSpectralRadius ρ σ) :=
    Real.log_pos (by linarith)
  have hLne : Real.log (iidAEPSpectralRadius ρ σ) ≠ 0 := ne_of_gt hLpos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2ne : Real.log 2 ≠ 0 := ne_of_gt hl2
  have hδnn : 0 ≤ δ_iidAEP_general ρ σ n_copies ε := by
    unfold δ_iidAEP_general
    have hlogb : 0 ≤ Real.logb 2
        ((ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2) := by
      have hcr : (0 : ℝ) ≤ (ρ.classicalRank : ℝ) := Nat.cast_nonneg _
      exact Real.logb_nonneg (by norm_num) (by linarith)
    have hnf : 0 ≤ noiseFactor n_copies ε := Real.sqrt_nonneg _
    positivity
  -- the clamped tilt magnitude `s = min(δ·ln2/(ln μ)², ln2/ln μ)`
  have ht : W.rtTilt = -(min (δ_iidAEP_general ρ σ n_copies ε * Real.log 2
            / Real.log (iidAEPSpectralRadius ρ σ) ^ 2)
        (Real.log 2 / Real.log (iidAEPSpectralRadius ρ σ))) := by
    rw [hparams.2]; rfl
  set a : ℝ := Real.log (iidAEPSpectralRadius ρ σ) with ha_def
  set d : ℝ := δ_iidAEP_general ρ σ n_copies ε with hd_def
  set s := -W.rtTilt with hsdef
  have hs_eq : s = min (d * Real.log 2 / a ^ 2) (Real.log 2 / a) := by
    rw [hsdef, ht, neg_neg]
  have hs_nonneg : 0 ≤ s := by
    rw [hs_eq]; exact le_min (by positivity) (by positivity)
  -- in-range gate `s·a ≤ ln 2`, always available from the clamp
  have hrange : s * a ≤ Real.log 2 := by
    rw [hs_eq]
    calc min (d * Real.log 2 / a ^ 2) (Real.log 2 / a) * a
        ≤ (Real.log 2 / a) * a := by
          apply mul_le_mul_of_nonneg_right (min_le_right _ _) hLpos.le
      _ = Real.log 2 := by field_simp
  -- factorization `M(s) = m(s)^N`
  rw [iidAEPCollisionTrace_eq_singleCopyMGF_pow ρ σ n_copies s]
  -- single-copy data, supplied with the in-range gate
  have hbound := singleCopyMGF_logb_le ρ hρ_norm σ hfeas hs_nonneg hrange
  have hm_nonneg := iidAEPSingleCopyMGF_nonneg ρ σ s
  set m := iidAEPSingleCopyMGF ρ σ s with hmdef
  set bnd := -s * iidAEPBitEntropyContribution ρ hρ_norm σ
      + (1 / Real.log 2 - 1 / 2)
        * (s * a) ^ 2 with hbnddef
  -- `m ≤ 2 ^ bnd` from the logb bound and `m ≥ 0`
  have hm_le : m ≤ (2 : ℝ) ^ bnd := by
    rcases eq_or_lt_of_le hm_nonneg with hm0 | hmpos
    · rw [← hm0]; positivity
    · calc m = (2 : ℝ) ^ Real.logb 2 m :=
            (Real.rpow_logb (by norm_num) (by norm_num) hmpos).symm
        _ ≤ (2 : ℝ) ^ bnd :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hbound
  -- RHS as a single power of two
  have hRHS : weightCapScale W ^ s * iidAEPRtErrorBound ρ σ n_copies ε W
      = (2 : ℝ) ^ (-W.entropyThreshold * s
          + -(n_copies : ℝ) * d ^ 2
            / (2 * Real.logb 2 (iidAEPSpectralRadius ρ σ) ^ 2)) := by
    simp only [weightCapScale, iidAEPRtErrorBound]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  -- entropy cancellation: `W.entropyThreshold = N·(H − δ)`
  have hcalib' : W.entropyThreshold
      = (n_copies : ℝ) * (iidAEPBitEntropyContribution ρ hρ_norm σ - d) := by
    rw [hcalib, hd_def]
    simp only [iidAEPBitBlockEntropyFloor, iidAEPBitEntropyFloor]
  -- scalar gate data: `v = s·a = min(w, ln2)`, `w = d·ln2/a = 2·noiseFactor`.
  -- The delta-design identity `d·ln2/ln μ = 2·noiseFactor` (proved inline:
  -- `d = 2·log₂μ·noiseFactor`, `log₂μ = ln μ/ln2`).
  have hw_eq : d * Real.log 2 / a = 2 * noiseFactor n_copies ε := by
    have hμ_eq : (ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2
        = iidAEPSpectralRadius ρ σ := rfl
    rw [hd_def]
    unfold δ_iidAEP_general
    rw [hμ_eq, Real.logb, ← ha_def]
    field_simp
  have hv_eq : s * a = min (d * Real.log 2 / a) (Real.log 2) := by
    have h1 : d * Real.log 2 / a ^ 2 * a = d * Real.log 2 / a := by
      rw [pow_two]; field_simp
    have h2 : Real.log 2 / a * a = Real.log 2 := by field_simp
    rw [hs_eq, min_mul_of_nonneg _ _ hLpos.le, h1, h2]
  have hwub : d * Real.log 2 / a ≤ 2 - Real.log 2 := by
    rw [hw_eq]
    have := hregime
    unfold iidAEPLargeBlockRegime at this
    linarith
  -- the clamped-tilt scalar endgame: `bnd · N ≤` the relaxed-envelope exponent
  have hle : bnd * (n_copies : ℝ)
      ≤ -W.entropyThreshold * s
        + -(n_copies : ℝ) * d ^ 2
          / (2 * Real.logb 2 (iidAEPSpectralRadius ρ σ) ^ 2) := by
    rw [hbnddef, hcalib']
    have hlogb : Real.logb 2 (iidAEPSpectralRadius ρ σ) = a / Real.log 2 := rfl
    rw [hlogb]
    -- divide out `N ≥ 0`; reduce to the scalar gate on `v = s·a`, `w = d·ln2/a`
    have hN_nonneg : (0 : ℝ) ≤ (n_copies : ℝ) := Nat.cast_nonneg _
    have hgate := collisionMGF_scalar_gate (Real.log 2) (s * a)
      (d * Real.log 2 / a) hl2 hv_eq hwub
    -- `(bnd) − (rhs/N)` is `−N · gate`-shaped; close by nlinarith with `a ≠ 0`
    have ha_sq_pos : 0 < a ^ 2 := by positivity
    have hexpand :
        (-s * iidAEPBitEntropyContribution ρ hρ_norm σ
            + (1 / Real.log 2 - 1 / 2) * (s * a) ^ 2) * (n_copies : ℝ)
          - (-((n_copies : ℝ)
              * (iidAEPBitEntropyContribution ρ hρ_norm σ - d)) * s
              + -(n_copies : ℝ) * d ^ 2 / (2 * (a / Real.log 2) ^ 2))
          = (n_copies : ℝ) *
              ((1 / Real.log 2 - 1 / 2) * (s * a) ^ 2
                - (s * a) * (d * Real.log 2 / a) / Real.log 2
                + (d * Real.log 2 / a) ^ 2 / 2) := by
      field_simp
      ring
    rw [← sub_nonpos, hexpand]
    exact mul_nonpos_of_nonneg_of_nonpos hN_nonneg hgate
  -- assemble
  calc m ^ n_copies
      ≤ ((2 : ℝ) ^ bnd) ^ n_copies :=
        pow_le_pow_left₀ hm_nonneg hm_le n_copies
    _ = (2 : ℝ) ^ (bnd * (n_copies : ℝ)) := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ bnd) n_copies,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ (2 : ℝ) ^ (-W.entropyThreshold * s
          + -(n_copies : ℝ) * d ^ 2
            / (2 * Real.logb 2 (iidAEPSpectralRadius ρ σ) ^ 2)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    _ = weightCapScale W ^ s * iidAEPRtErrorBound ρ σ n_copies ε W := hRHS.symm

end InfoTheory.SmoothMinEntropy
