import QCryptLean.InfoTheory.DeFinetti.Theorem.TensorPowerPushforward
import QCryptLean.InfoTheory.VonNeumannEntropy.Continuity

/-!
# Quantum de Finetti Theorem — CKMR main theorem, BB84 specialization, entropy bound

The main quantum de Finetti theorem (CKMR 2007, Theorem II.7) and applications.
Starting from a permutation-invariant state ρ on (ℂᵈ)^⊗n, shows existence of a
measure μ over pure states such that k-copy marginals approximate ∫ |ψ⟩⟨ψ|^⊗k dμ(ψ)
with trace distance bound 2kd²/n.

## Main statements
- `quantum_deFinetti`: Main theorem with 2kd²/n bound
- `quantum_deFinetti_bb84`: BB84 specialization (d=4, bound 32k/n)
- `deFinetti_entropy_bound`: Entropy continuity via de Finetti approximation
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Symmetry MeasureTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.DeFinetti

/-- CKMR Theorem II.7 Steps 2+3: From purification to de Finetti bound.

    Given a purification Ψ with Tr_B(Ψ) = ρ, produce ONE measure μ such that
    for ALL k ≤ n, the k-copy reduced state of ρ is within 2k·d²/n of
    the de Finetti mixture ∫ σ^⊗k dμ(σ).

    **Reference**: CKMR 2007, Theorem II.7 proof (definetti.tex lines 624-628). -/
private lemma deFinetti_purified_bound {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n))
    (Ψ : DensityOp (d ^ n * d ^ n))
    (_hsym : symmetricProjectorPaired d n * Ψ.toOp *
      symmetricProjectorPaired d n = Ψ.toOp)
    (_hlink : partialTraceB Ψ.toOp = ρ.toOp) :
    ∃ μ : DensityMeasure d,
      ∀ (k : ℕ) [NeZero k] [NeZero (d ^ k)] (hk : k ≤ n),
        traceDistance (partialTraceToFirstK k hk ρ).toOp (integralTensorPower k μ).toOp ≤
          2 * k * ((d * d : ℕ) : ℝ) / n := by
  -- Combine deFinetti_paired with partial trace contraction.
  -- By CKMR Theorem II.7 proof (definetti.tex lines 624-628):
  -- Step 1: Get NeZero instances, apply deFinetti_paired to get ν
  --   on (d*d)-dim space with bound D(Ψ'_k, ∫τ^⊗k dν) ≤ 2k(d²)/n for all k.
  --   Now uses reindexInterleave (not castDim) for correct interleaving.
  -- Step 2: Push forward ν through Tr_B to get μ on d-dim space.
  -- Step 3: For each k, the key chain is:
  --   D(ρ_k, ∫σ^⊗k dμ) = D(Tr_B(Ψ'_k), Tr_B(∫τ^⊗k dν)) ≤ D(Ψ'_k, ∫τ^⊗k dν)
  --   The first equality needs two sub-facts:
  --   (a) ρ_k = Tr_B(Ψ'_k): partial traces commute
  --       (partialTraces_commute_interleave).
  --   (b) ∫σ^⊗k dμ = Tr_B(∫τ^⊗k dν): since μ = pushforward of ν through Tr_B,
  --       for each τ in the support, (Tr_B τ)^⊗k = Tr_B^{⊗k}(τ^⊗k) (partial trace
  --       distributes over tensor products), then integrate both sides.
  --   The inequality is partialTraceB_contracts_traceDistance (CPTP contraction).
  have : NeZero (d * d) := ⟨Nat.mul_pos (NeZero.pos d) (NeZero.pos d) |>.ne'⟩
  have : NeZero ((d * d) ^ n) := ⟨pow_ne_zero n (NeZero.ne (d * d))⟩
  obtain ⟨ν, hν⟩ := deFinetti_paired Ψ _hsym
  let μ : DensityMeasure d := partialTraceBDensityMeasure ν
  refine ⟨μ, fun k _ _ hk => ?_⟩
  -- For each k, need D(ρ_k, ∫σ^⊗k dμ) ≤ 2k·d²/n.
  -- From hν: D(partialTraceToFirstK k hk (reindexInterleave Ψ), integralTensorPower k ν) ≤ 2k·d²/n.
  -- Chain of equalities/inequalities:
  --   (a) ρ_k = Tr_B(Ψ'_k) by partialTraces_commute_interleave (partial traces commute).
  --       Here Ψ' = reindexInterleave Ψ, and Tr_B takes d²-dim states to d-dim states.
  --   (b) ∫σ^⊗k dμ = Tr_B^{⊗k}(∫τ^⊗k dν) because μ is the pushforward of ν under Tr_B.
  --       This requires: Tr_B distributes over tensor powers and commutes with integration.
  --       Formally: integralTensorPower k μ = partialTraceB_tensorPower(integralTensorPower k ν).
  --   (c) D(Tr_B(X), Tr_B(Y)) ≤ D(X, Y) by CPTP contraction.
  -- Combining: D(ρ_k, ∫σ^⊗k dμ) = D(Tr_B(Ψ'_k), Tr_B(∫τ^⊗k dν))
  --            ≤ D(Ψ'_k, ∫τ^⊗k dν) ≤ 2k·d²/n.
  -- Steps (a) and (b) are the main work; (c) is already proved.
  -- Key: (d*d)^k = d^k * d^k, so we can apply partialTraceB to factor out the "B" copies.
  have : NeZero (d ^ k) := ⟨pow_ne_zero k (NeZero.ne d)⟩
  have : NeZero ((d * d) ^ k) := ⟨pow_ne_zero k (NeZero.ne (d * d))⟩
  have : NeZero (d ^ k * d ^ k) :=
    ⟨Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne (d ^ k)))
      (Nat.pos_of_ne_zero (NeZero.ne (d ^ k))) |>.ne'⟩
  -- Deinterleave: (d*d)^k → d^k * d^k via interleavingEquiv (correct index separation)
  -- Unlike castDim, this correctly separates A-parts from B-parts at each tensor position.
  let deintK := densityOp_reindex (interleavingEquiv d k).symm
  -- (a) Partial traces commute: ρ_k = Tr_B(deintK(Ψ'_k))
  -- Both sides compute ∑_{a_{k+1}..aₙ, b₁..bₙ} Ψ[(a,b), (a',b')] with a₁..aₖ free.
  -- LHS: first traces B (d^n*d^n → d^n), then copies k+1..n.
  -- RHS: first interleaves, traces copies k+1..n, deinterleaves, then traces B-factor.
  have ha : partialTraceToFirstK k hk ρ =
      DensityOp.partialTraceB (deintK
        (partialTraceToFirstK k hk (reindexInterleave Ψ))) := by
    have hlink_do : DensityOp.partialTraceB Ψ = ρ := by
      apply DensityOp.ext
      simp only [DensityOp.partialTraceB, PosSemidefOp.partialTraceB]
      exact _hlink
    rw [← hlink_do]
    exact partialTraces_commute_interleave Ψ k hk
  -- (b) μ-mixture = Tr_B(deintK(ν-mixture)): pushforward distributes over tensor powers.
  -- Key pointwise fact: (Tr_B τ)^⊗k = Tr_B(deintK(τ^⊗k)).
  -- Entry (i,j): LHS = ∏_l (∑_b τ_{(i_l,b),(j_l,b)}) by tensorPowGen_toOp_eq_prod.
  -- RHS = ∑_{b₁..bₖ} ∏_l τ_{(i_l,b_l),(j_l,b_l)} by deinterleave + tensorPowGen_toOp_eq_prod.
  -- These are equal by Finset.prod_sum (product of sums = sum of products over all choices).
  have hb : integralTensorPower k μ =
      DensityOp.partialTraceB (deintK (integralTensorPower k ν)) := by
    change integralTensorPower k (partialTraceBDensityMeasure ν) =
      DensityOp.partialTraceB
        (densityOp_reindex (interleavingEquiv d k).symm (integralTensorPower k ν))
    exact integralTensorPower_partialTraceBDensityMeasure (d := d) (k := k) ν
  -- (c) CPTP contraction: D(Tr_B(X), Tr_B(Y)) ≤ D(X, Y), and reindex preserves D exactly.
  rw [ha, hb]
  have h_contract : traceDistance
      (DensityOp.partialTraceB (deintK
        (partialTraceToFirstK k hk (reindexInterleave Ψ)))).toOp
      (DensityOp.partialTraceB (deintK
        (integralTensorPower k ν))).toOp ≤
    traceDistance (partialTraceToFirstK k hk (reindexInterleave Ψ)).toOp
      (integralTensorPower k ν).toOp := by
    calc traceDistance _ _ ≤ traceDistance
          (deintK (partialTraceToFirstK k hk (reindexInterleave Ψ))).toOp
          (deintK (integralTensorPower k ν)).toOp :=
        InfoTheory.DistanceBounds.TraceNormContraction.partialTraceB_contracts_traceDistance _ _
      _ = traceDistance (partialTraceToFirstK k hk (reindexInterleave Ψ)).toOp
            (integralTensorPower k ν).toOp :=
        reindex_preserves_traceDistance _ _ _
  linarith [h_contract, hν k hk]

/-- Core de Finetti bound: one measure approximates all k-copy reduced states.

    Proof follows CKMR 2007 Theorem II.7:
    1. Symmetric purification (Lemma II.5): construct Ψ in paired symmetric subspace
    2+3. Pure-state de Finetti + CPTP contraction for all k simultaneously -/
private lemma deFinetti_core {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) (hinv : IsPermutationInvariant ρ) :
    ∃ μ : DensityMeasure d,
      ∀ (k : ℕ) [NeZero k] [NeZero (d ^ k)] (hk : k ≤ n),
        traceDistance (partialTraceToFirstK k hk ρ).toOp (integralTensorPower k μ).toOp ≤
          2 * k * (d : ℝ) ^ 2 / n := by
  obtain ⟨Ψ, _hΨ_inv, hΨ_sym, hΨ_link⟩ := symmetric_purification ρ hinv
  obtain ⟨μ, hμ⟩ := deFinetti_purified_bound ρ Ψ hΨ_sym hΨ_link
  refine ⟨μ, fun k _ _ hk => ?_⟩
  have heq : (2 : ℝ) * k * ((d * d : ℕ) : ℝ) / (n : ℝ) = 2 * k * (d : ℝ) ^ 2 / (n : ℝ) := by
    push_cast; ring
  linarith [hμ k hk]

/-- **Quantum de Finetti Theorem** (CKMR 2007, Theorem II.7).

    For any permutation-invariant state ρ on (ℂᵈ)^⊗n, there exists ONE
    probability measure μ over d-dimensional density operators such that
    for ALL k ≤ n:
      D(Tr_{k+1,...,n}[ρ], ∫ σ^⊗k dμ(σ)) ≤ 2kd²/n

    The ∀ k quantifier is essential: the same measure simultaneously
    approximates all k-copy reduced states. This prevents trivial witnesses
    (e.g., Dirac measure) which work for k=1 but fail for k≥2.

    **Reference**: Christandl-König-Mitchison-Renner (2007)
    "One-and-a-Half Quantum de Finetti Theorems", Theorem II.7. -/
theorem quantum_deFinetti {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) (_hinv : IsPermutationInvariant ρ) :
    ∃ μ : DensityMeasure d,
      ∀ (k : ℕ) [NeZero k] [NeZero (d ^ k)] (hk : k ≤ n),
        traceDistance (partialTraceToFirstK k hk ρ).toOp (integralTensorPower k μ).toOp ≤
          2 * k * (d : ℝ) ^ 2 / n := by
  exact deFinetti_core ρ _hinv

/-- **Quantum de Finetti for BB84** (d=4 for qubit pairs).

    For BB84, the local dimension is 4 (two qubits per round).
    For all k ≤ n copies: D(ρ_k, ∫ σ^⊗k dμ) ≤ 32k/n.

    **Reference**: CKMR (2007), Theorem II.7 with d=4. -/
theorem quantum_deFinetti_bb84 {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (ρ : DensityOp (4 ^ n)) (hinv : IsPermutationInvariant ρ) :
    ∃ μ : DensityMeasure 4,
      ∀ (k : ℕ) [NeZero k] [NeZero (4 ^ k)] (hk : k ≤ n),
        traceDistance (partialTraceToFirstK k hk ρ).toOp (integralTensorPower k μ).toOp ≤
          32 * k / n := by
  obtain ⟨μ, hμ⟩ := quantum_deFinetti ρ hinv
  refine ⟨μ, fun k _ _ hk => ?_⟩
  calc traceDistance (partialTraceToFirstK k hk ρ).toOp (integralTensorPower k μ).toOp
      ≤ 2 * k * (4 : ℝ) ^ 2 / n := hμ k hk
    _ = 32 * k / n := by ring

/-!
## De Finetti and Entropy

The de Finetti approximation implies entropy bounds: if ρ is close to
∫ σ^⊗n dμ(σ), then S(ρ) is close to the average n·S(σ).
-/

/-- De Finetti implies entropy is close to i.i.d. entropy.

    If D(ρ, ∫σ^⊗n dμ) ≤ ε, then by Fannes inequality:
      |S(ρ) - S(∫σ^⊗n dμ)| ≤ ε·log(d^n) + H(ε)

    For the de Finetti bound ε = d²/n, this gives:
      |S(ρ) - S(∫σ^⊗n dμ)| ≤ (d²/n)·(n·log(d)) + H(d²/n)
                           = d²·log(d) + H(d²/n)

    The H(d²/n) term vanishes as n → ∞, so the bound is O(d²·log(d)).

    **Depends on**: `fannes_inequality` (proved in Continuity.lean) + monotonicity of
    `f(t) = t·log(d^n - 1) + H(t)` on `[0, 1 - 1/d^n]`. -/
theorem deFinetti_entropy_bound {d n : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n))
    (μ : DensityMeasure d) (ε : ℝ) (_hε_nn : 0 ≤ ε) (_hε_lt : ε < 1)
    (_hε_fan : ε ≤ 1 - 1 / (d ^ n : ℝ)) (_hd : 2 ≤ d ^ n)
    (_hμ : traceDistance ρ.toOp (integralTensorPower n μ).toOp ≤ ε) :
    |InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ -
     InfoTheory.VonNeumannEntropy.vonNeumannEntropy (integralTensorPower n μ)| ≤
    ε * Real.log (d ^ n) + Math.ClassicalEntropy.binaryEntropy ε := by
  -- Step 1: Apply fannes_inequality from Continuity.lean with T = traceDistance ρ σ.
  set σ := integralTensorPower n μ with hσ_def
  set T := traceDistance ρ.toOp σ.toOp with hT_def
  have hT_pos : 0 ≤ T := traceDistance_nonneg ρ.toOp σ.toOp
  have hT_le : T ≤ ε := _hμ
  have hT_lt : T < 1 := lt_of_le_of_lt hT_le _hε_lt
  have hT_bound : T ≤ 1 - 1 / ((d ^ n : ℕ) : ℝ) := by
    calc T ≤ ε := hT_le
      _ ≤ 1 - 1 / (↑d ^ n) := _hε_fan
      _ = 1 - 1 / ((d ^ n : ℕ) : ℝ) := by push_cast; ring
  have hfannes := InfoTheory.Continuity.fannes_inequality _hd ρ σ T rfl hT_pos hT_lt hT_bound
  -- Step 2: Chain Fannes bound (T * log(d^n - 1) + H(T)) to target (ε * log(d^n) + H(ε)).
  -- Monotonicity of f(t) = t·log(d^n - 1) + H(t) on [0, 1 - 1/d^n]:
  --   f'(t) = log(d^n - 1) + log((1-t)/t) ≥ 0 when t ≤ (d^n - 1)/d^n.
  -- Then f(T) ≤ f(ε) ≤ ε·log(d^n) + H(ε) since log(d^n - 1) ≤ log(d^n).
  have hcast : (↑(d ^ n) : ℝ) = (↑d : ℝ) ^ n := by push_cast; ring
  calc
    |InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ -
      InfoTheory.VonNeumannEntropy.vonNeumannEntropy σ|
      ≤ T * Real.log (↑(d ^ n) - 1) + Math.ClassicalEntropy.binaryEntropy T := hfannes
    _ ≤ ε * Real.log (↑d ^ n) + Math.ClassicalEntropy.binaryEntropy ε := by
        rw [← hcast]
        -- Use qaryEntropy monotonicity: qaryEntropy D is increasing on [0, 1-1/D]
        set D := d ^ n with hD_def
        have hD_ge : 2 ≤ D := _hd
        have hD1 : 1 ≤ D := Nat.one_le_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hD_ge)
        -- Step 1: Monotonicity gives f(T) ≤ f(ε) where f(t) = t*log(D-1) + H(t)
        suffices h_mono : T * Real.log (↑D - 1) + Math.ClassicalEntropy.binaryEntropy T ≤
            ε * Real.log (↑D - 1) + Math.ClassicalEntropy.binaryEntropy ε by
          have h_log : Real.log (↑D - 1) ≤ Real.log ↑D := by
            apply Real.log_le_log
            · exact_mod_cast show 0 < D - 1 by omega
            · linarith
          linarith [mul_le_mul_of_nonneg_left h_log _hε_nn]
        -- Step 2: Convert to qaryEntropy and apply StrictMonoOn
        have h_eq : ∀ t : ℝ, t * Real.log (↑D - 1) + Math.ClassicalEntropy.binaryEntropy t =
            Real.qaryEntropy D t := by
          intro t
          unfold Real.qaryEntropy
          rw [Math.ClassicalEntropy.binaryEntropy_eq_binEntropy]
          norm_cast
        rw [h_eq, h_eq]
        have hT_mem : T ∈ Set.Icc 0 (1 - 1 / (↑D : ℝ)) := ⟨hT_pos, hT_bound⟩
        have hε_mem : ε ∈ Set.Icc 0 (1 - 1 / (↑D : ℝ)) := by
          refine ⟨_hε_nn, ?_⟩
          have h := _hε_fan
          simp only [hD_def]
          rwa [show (1 : ℝ) - 1 / ↑(d ^ n) = 1 - 1 / ↑d ^ n by push_cast; ring]
        by_cases heq : T = ε
        · rw [heq]
        · exact le_of_lt (Real.qaryEntropy_strictMonoOn hD_ge hT_mem hε_mem
            (lt_of_le_of_ne hT_le heq))

open scoped TensorProduct Kronecker

end InfoTheory.DeFinetti

end
