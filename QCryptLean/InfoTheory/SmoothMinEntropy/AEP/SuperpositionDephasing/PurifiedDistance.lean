import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SuperpositionDephasing.Basic

/-!
# Dephased-mixture purified distance — weighted sqrt Cauchy–Schwarz correction and ε-ball assembly

The purified-distance geometric crux for the dephased mixture `dephasedMixtureCQ`:
if every per-component candidate lies within purified distance `ε` of its component,
then the assembled dephased mixture lies within purified distance `ε` of the original
mixture.  The core is a self-contained real Cauchy–Schwarz / AM–GM correction that
turns per-component generalized-fidelity lower bounds into a generalized-fidelity
lower bound for the weighted mixture.

**Textbook reference**: Renner, R. (2005). *Security of Quantum Key Distribution*.
PhD thesis, ETH Zürich. arXiv:quant-ph/0512258v2.

## Main statements
- `sum_weight_sqrt_mul_sq_le`, `two_mul_sum_weight_sqrt_mul_le`: weighted sqrt
  Cauchy–Schwarz and AM–GM (pure `ℝ`).
- `weighted_mixture_fidelityGen_ge`: the sub-normalization correction giving a
  generalized-fidelity lower bound for the weighted mixture (pure `ℝ`).
- `fidelity_smul_block_eq`: per-block fidelity scaling under a common scalar.
- `fidelityGen_ge_sqrt_one_sub_sq_of_purifiedDistance_le`: purified distance to
  generalized fidelity.
- `CQState.purifiedDistance_dephasedMixtureCQ_le`: the assembled dephased mixture is
  within purified distance `ε` of the original mixture.
-/

open Real Math.ClassicalEntropy
open Quantum.Operators
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open InfoTheory.SmoothMinEntropy

/-- Weighted Cauchy–Schwarz for square roots:
`(∑ wᵢ·√(uᵢvᵢ))² ≤ (∑ wᵢuᵢ)·(∑ wᵢvᵢ)`. -/
lemma sum_weight_sqrt_mul_sq_le
    (S : Finset ℕ) (w u v : ℕ → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hu : ∀ i ∈ S, 0 ≤ u i) (hv : ∀ i ∈ S, 0 ≤ v i) :
    (∑ i ∈ S, w i * Real.sqrt (u i * v i)) ^ 2 ≤
      (∑ i ∈ S, w i * u i) * (∑ i ∈ S, w i * v i) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun i => Real.sqrt (w i) * Real.sqrt (u i))
    (fun i => Real.sqrt (w i) * Real.sqrt (v i))
  simp only at key
  have h1 :
      (∑ i ∈ S, Real.sqrt (w i) * Real.sqrt (u i) * (Real.sqrt (w i) * Real.sqrt (v i)))
        = ∑ i ∈ S, w i * Real.sqrt (u i * v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [show Real.sqrt (w i) * Real.sqrt (u i) * (Real.sqrt (w i) * Real.sqrt (v i))
          = (Real.sqrt (w i)) ^ 2 * (Real.sqrt (u i) * Real.sqrt (v i)) by ring,
       Real.sq_sqrt (hw i hi), ← Real.sqrt_mul (hu i hi)]
  have h2 :
      (∑ i ∈ S, (Real.sqrt (w i) * Real.sqrt (u i)) ^ 2) = ∑ i ∈ S, w i * u i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hu i hi)]
  have h3 :
      (∑ i ∈ S, (Real.sqrt (w i) * Real.sqrt (v i)) ^ 2) = ∑ i ∈ S, w i * v i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hv i hi)]
  rw [h1, h2, h3] at key
  exact key

/-- Weighted termwise AM–GM summed: `2·∑ wᵢ√(uᵢvᵢ) ≤ ∑ wᵢuᵢ + ∑ wᵢvᵢ`. -/
lemma two_mul_sum_weight_sqrt_mul_le
    (S : Finset ℕ) (w u v : ℕ → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hu : ∀ i ∈ S, 0 ≤ u i) (hv : ∀ i ∈ S, 0 ≤ v i) :
    2 * (∑ i ∈ S, w i * Real.sqrt (u i * v i)) ≤
      (∑ i ∈ S, w i * u i) + (∑ i ∈ S, w i * v i) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [Real.sqrt_mul (hu i hi)]
  set su := Real.sqrt (u i) with hsudef
  set sv := Real.sqrt (v i) with hsvdef
  have hsu : su ^ 2 = u i := Real.sq_sqrt (hu i hi)
  have hsv : sv ^ 2 = v i := Real.sq_sqrt (hv i hi)
  have hexp : 2 * (w i * (su * sv)) = w i * (su ^ 2 + sv ^ 2) - w i * (su - sv) ^ 2 := by ring
  rw [hexp, hsu, hsv]
  nlinarith [mul_nonneg (hw i hi) (sq_nonneg (su - sv))]

/-- The sub-normalization correction.  Given per-component generalized-fidelity
lower bounds `c ≤ aₛ + √(uₛvₛ)` (with weights summing with a slack `w₀` to one),
the weighted mixture's generalized fidelity
`∑ wₛaₛ + √((w₀+∑wₛuₛ)(w₀+∑wₛvₛ))` is at least `c`. -/
lemma weighted_mixture_fidelityGen_ge
    (S : Finset ℕ) (w a u v : ℕ → ℝ) (c w0 : ℝ)
    (hw : ∀ s ∈ S, 0 ≤ w s)
    (_ha : ∀ s ∈ S, 0 ≤ a s)
    (hu : ∀ s ∈ S, 0 ≤ u s) (hv : ∀ s ∈ S, 0 ≤ v s)
    (hw0 : 0 ≤ w0) (hc1 : c ≤ 1)
    (hsum : w0 + ∑ s ∈ S, w s = 1)
    (hcomp : ∀ s ∈ S, c ≤ a s + Real.sqrt (u s * v s)) :
    c ≤ (∑ s ∈ S, w s * a s) +
        Real.sqrt ((w0 + ∑ s ∈ S, w s * u s) * (w0 + ∑ s ∈ S, w s * v s)) := by
  set Wu := ∑ s ∈ S, w s * u s with hWu
  set Wv := ∑ s ∈ S, w s * v s with hWv
  set Wsq := ∑ s ∈ S, w s * Real.sqrt (u s * v s) with hWsq
  -- basic nonnegativities
  have hWu_nn : 0 ≤ Wu := Finset.sum_nonneg fun s hs => mul_nonneg (hw s hs) (hu s hs)
  have hWv_nn : 0 ≤ Wv := Finset.sum_nonneg fun s hs => mul_nonneg (hw s hs) (hv s hs)
  have hWsq_nn : 0 ≤ Wsq :=
    Finset.sum_nonneg fun s hs => mul_nonneg (hw s hs) (Real.sqrt_nonneg _)
  have hP_nn : 0 ≤ w0 + Wu := add_nonneg hw0 hWu_nn
  have hQ_nn : 0 ≤ w0 + Wv := add_nonneg hw0 hWv_nn
  -- the two Cauchy–Schwarz / AM–GM facts
  have hCS : Wsq ^ 2 ≤ Wu * Wv := sum_weight_sqrt_mul_sq_le S w u v hw hu hv
  have hAMGM : 2 * Wsq ≤ Wu + Wv := two_mul_sum_weight_sqrt_mul_le S w u v hw hu hv
  -- step: w0 + Wsq ≤ √((w0+Wu)(w0+Wv))
  have hstep : w0 + Wsq ≤ Real.sqrt ((w0 + Wu) * (w0 + Wv)) := by
    apply Real.le_sqrt_of_sq_le
    -- `(w0 + Wsq)² = w0² + w0·(2 Wsq) + Wsq² ≤ w0² + w0·(Wu + Wv) + Wu·Wv`
    linarith only [hCS, mul_le_mul_of_nonneg_left hAMGM hw0]
  -- weighted lower bound on ∑ w a + (w0 + Wsq)
  have hsum_le : c ≤ (∑ s ∈ S, w s * a s) + (w0 + Wsq) := by
    have hpart : (∑ s ∈ S, w s * a s) + Wsq = ∑ s ∈ S, w s * (a s + Real.sqrt (u s * v s)) := by
      rw [hWsq, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs; ring
    have hge : ∑ s ∈ S, w s * c ≤ ∑ s ∈ S, w s * (a s + Real.sqrt (u s * v s)) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hcomp s hs) (hw s hs)
    have hwc : ∑ s ∈ S, w s * c = (∑ s ∈ S, w s) * c := by
      rw [Finset.sum_mul]
    have hsumw : ∑ s ∈ S, w s = 1 - w0 := by linarith only [hsum]
    have : (1 - w0) * c ≤ (∑ s ∈ S, w s * a s) + Wsq := by
      rw [← hsumw, ← hwc]; linarith only [hge, hpart]
    -- `c = (1 - w0)·c + w0·c` and `w0·c ≤ w0` since `c ≤ 1`
    linarith only [this, mul_le_mul_of_nonneg_left hc1 hw0]
  linarith only [hsum_le, hstep]

/-- Per-block fidelity scaling: if two PSD operators are common nonnegative real
multiples `c` of `A` and `B`, their fidelity is `c · F(A,B)`. -/
lemma fidelity_smul_block_eq {n : ℕ} [NeZero n] {c : ℝ} (hc : 0 ≤ c)
    (A B P Q : Quantum.Operators.PosSemidefOp n)
    (hP : P.toOp = (c : ℂ) • A.toOp) (hQ : Q.toOp = (c : ℂ) • B.toOp) :
    Quantum.Metrics.fidelity P Q = c * Quantum.Metrics.fidelity A B := by
  have h := Quantum.Metrics.fidelity_smul_smul (α := c) (β := c) hc hc A B
  rw [Real.sqrt_mul_self hc] at h
  rw [← h]
  unfold Quantum.Metrics.fidelity Quantum.Metrics.sqrtPosSemidefOp
  rw [hP, hQ]

/-- From a purified-distance bound `P(ρ,σ) ≤ ε` we recover the generalized-fidelity
lower bound `√(1-ε²) ≤ F*(ρ,σ)`. -/
lemma fidelityGen_ge_sqrt_one_sub_sq_of_purifiedDistance_le
    {n : ℕ} [NeZero n] (ρ σ : SubDensityOp n) {ε : ℝ} (hε : 0 ≤ ε)
    (hpd : purifiedDistance ρ σ ≤ ε) :
    Real.sqrt (1 - ε ^ 2) ≤ fidelityGen ρ σ := by
  have hpd_nn := purifiedDistance_nonneg ρ σ
  have hfg_nn := fidelityGen_nonneg ρ σ
  have hpd_sq := purifiedDistance_sq ρ σ
  have hsq_le : purifiedDistance ρ σ ^ 2 ≤ ε ^ 2 := by nlinarith
  have hfg_sq_ge : 1 - ε ^ 2 ≤ fidelityGen ρ σ ^ 2 := by rw [hpd_sq] at hsq_le; linarith
  calc Real.sqrt (1 - ε ^ 2) ≤ Real.sqrt (fidelityGen ρ σ ^ 2) :=
        Real.sqrt_le_sqrt hfg_sq_ge
    _ = fidelityGen ρ σ := Real.sqrt_sq hfg_nn

/-- Purified-distance geometric crux.  If every per-component candidate `comp' s`
is within purified distance `ε` of `comp s`, then the assembled dephased mixture is
within purified distance `ε` of the original mixture (over the product classical
register `X × S`). -/
lemma CQState.purifiedDistance_dephasedMixtureCQ_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]
    (S : Finset ℕ) (hS : S.Nonempty)
    (comp comp' : ℕ → CQState X n) (weight : ℕ → ℝ)
    (hwn : ∀ s ∈ S, 0 ≤ weight s) (hwl : ∀ s ∈ S, weight s ≤ 1)
    (hws : ∑ s ∈ S, weight s ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hdist : ∀ s ∈ S, CQState.purifiedDistance (comp s) (comp' s) ≤ ε) :
    letI : Nonempty {s // s ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
    CQState.purifiedDistance
        (dephasedMixtureCQ S comp weight hwn hwl hws)
        (dephasedMixtureCQ S comp' weight hwn hwl hws) ≤ ε := by
  classical
  haveI : Nonempty {s // s ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  haveI : Nonempty (X × {s // s ∈ S}) :=
    ⟨(Classical.arbitrary X, ⟨hS.choose, hS.choose_spec⟩)⟩
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card X) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  haveI : NeZero (Fintype.card (X × {s // s ∈ S})) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (n * Fintype.card (X × {s // s ∈ S})) :=
    ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  set mix := dephasedMixtureCQ S comp weight hwn hwl hws with hmix
  set mix' := dephasedMixtureCQ S comp' weight hwn hwl hws with hmix'
  set mixJD := mix.toJointDensity with hmixJD
  set mixJD' := mix'.toJointDensity with hmixJD'
  -- abbreviations for the per-component data
  set a : ℕ → ℝ := fun s => Quantum.Metrics.fidelity
    (comp s).toJointDensity.toPosSemidefOp (comp' s).toJointDensity.toPosSemidefOp with ha
  set u : ℕ → ℝ := fun s => 1 - (comp s).toJointDensity.trace with hu
  set v : ℕ → ℝ := fun s => 1 - (comp' s).toJointDensity.trace with hv
  set w0 : ℝ := 1 - ∑ s ∈ S, weight s with hw0def
  have hw0_nn : 0 ≤ w0 := sub_nonneg.mpr hws
  -- F-sum: fidelity of the mixture joint densities decomposes over s
  have hFsum :
      Quantum.Metrics.fidelity mixJD.toPosSemidefOp mixJD'.toPosSemidefOp
        = ∑ s ∈ S, weight s * a s := by
    rw [hmixJD, hmixJD', CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity,
      Fintype.sum_prod_type_right]
    rw [← Finset.sum_attach S (fun s => weight s * a s)]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [ha]
    simp only
    rw [CQState.fidelity_toJointDensity_eq_sum_stateMap_fidelity, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine fidelity_smul_block_eq (hwn s.1 s.2) _ _ _ _ ?_ ?_
    · rfl
    · rfl
  -- trace identities in the (w0 + ∑ w·u) form
  have htrmix : 1 - mixJD.trace = w0 + ∑ s ∈ S, weight s * u s := by
    rw [hmixJD, hmix, dephasedMixtureCQ_toJointDensity_trace S comp weight hwn hwl hws,
      hw0def, hu]
    have : ∑ s ∈ S, weight s * (1 - (comp s).toJointDensity.trace)
        = (∑ s ∈ S, weight s) - ∑ s ∈ S, weight s * (comp s).toJointDensity.trace := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun s _ => by ring)
    simp only at this ⊢
    rw [this]; ring
  have htrmix' : 1 - mixJD'.trace = w0 + ∑ s ∈ S, weight s * v s := by
    rw [hmixJD', hmix', dephasedMixtureCQ_toJointDensity_trace S comp' weight hwn hwl hws,
      hw0def, hv]
    have : ∑ s ∈ S, weight s * (1 - (comp' s).toJointDensity.trace)
        = (∑ s ∈ S, weight s) - ∑ s ∈ S, weight s * (comp' s).toJointDensity.trace := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun s _ => by ring)
    simp only at this ⊢
    rw [this]; ring
  -- the correction lemma supplies the generalized-fidelity lower bound
  have hcorr := weighted_mixture_fidelityGen_ge S weight a u v (Real.sqrt (1 - ε ^ 2)) w0
    hwn
    (fun s _ => Quantum.Metrics.fidelity_nonneg_posSemidefOp _ _)
    (fun s _ => sub_nonneg.mpr (comp s).toJointDensity.trace_le_one)
    (fun s _ => sub_nonneg.mpr (comp' s).toJointDensity.trace_le_one)
    hw0_nn
    (by
      have h := Real.sqrt_le_sqrt (sub_le_self (1 : ℝ) (sq_nonneg ε))
      rwa [Real.sqrt_one] at h)
    (by rw [hw0def]; ring)
    (fun s hs => by
      have hpd := hdist s hs
      unfold CQState.purifiedDistance at hpd
      have h := fidelityGen_ge_sqrt_one_sub_sq_of_purifiedDistance_le
        (comp s).toJointDensity (comp' s).toJointDensity hε hpd
      unfold fidelityGen at h
      rw [ha, hu, hv]; simpa using h)
  -- assemble: √(1-ε²) ≤ fidelityGen mixJD mixJD'
  have hfg_eq : fidelityGen mixJD mixJD'
      = (∑ s ∈ S, weight s * a s)
        + Real.sqrt ((w0 + ∑ s ∈ S, weight s * u s) * (w0 + ∑ s ∈ S, weight s * v s)) := by
    unfold fidelityGen
    rw [hFsum, htrmix, htrmix']
  have hfg_ge : Real.sqrt (1 - ε ^ 2) ≤ fidelityGen mixJD mixJD' := by
    rw [hfg_eq]; exact hcorr
  -- conclude the purified-distance bound
  -- square `√(1-ε²) ≤ F*` (trivial when `1 - ε² < 0`)
  have hfgsq : 1 - ε ^ 2 ≤ fidelityGen mixJD mixJD' ^ 2 := by
    rcases le_total 0 (1 - ε ^ 2) with h | h
    · calc 1 - ε ^ 2 = Real.sqrt (1 - ε ^ 2) ^ 2 := (Real.sq_sqrt h).symm
        _ ≤ fidelityGen mixJD mixJD' ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hfg_ge 2
    · exact h.trans (sq_nonneg _)
  unfold CQState.purifiedDistance InfoTheory.SmoothMinEntropy.purifiedDistance
  calc Real.sqrt (1 - fidelityGen mixJD mixJD' ^ 2)
      ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt (by linarith only [hfgsq])
    _ = ε := Real.sqrt_sq hε

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
