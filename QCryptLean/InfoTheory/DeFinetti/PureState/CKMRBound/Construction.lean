import QCryptLean.InfoTheory.DeFinetti.PureState.SchurLemma.Main
import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# CKMR Construction — de Finetti measure, post-measurement states, permutation invariance

This module constructs the de Finetti measure and post-measurement states from the
coherent-state POVM (CKMR 2007). Given a symmetric state Ψ in (ℂᵈ)^⊗n, we define:
- The POVM weight w(g) and prove it integrates to 1
- The de Finetti measure μ as the pushforward of w(g)·Haar through g ↦ |g₀⟩⟨g₀|
- The conditional post-measurement state ξ^g_k on systems 1,...,k

We also prove permutation invariance of the bipartite reindexing (used in the
trace distance bound), the bridge between integralTensorPower and the POVM form,
and the Bochner integral PSD preservation lemma.

## Main definitions
- `postMeasurementWeight`: POVM outcome weight w(g) = dim(Sym^n) · Tr(ρ_g · Ψ)
- `coherentState_deFinettiMeasure`: The de Finetti measure from the coherent-state POVM
- `postMeasurementState_k`: Conditional k-copy state after POVM outcome g

## Main statements
- `integralTensorPower_coherentState_eq`: ∫ σ^⊗k dμ = ∫ w(g)|v^g_k⟩⟨v^g_k| dg
- `bochner_integral_posSemidef`: Bochner integral of PSD functions is PSD
- `symmetric_containment_bipartite`: Tr_B[Ψ_bip] = Tr_B[(I ⊗ P_sym) · Ψ_bip]

## References
- Christandl, König, Mitchison, Renner (2007) "One-and-a-Half Quantum de Finetti
  Theorems", Comm. Math. Phys. 273(2), 473-498
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Symmetry MeasureTheory
open Math.HaarMeasure Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.DeFinetti.PureState

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-!
## Section 4: Post-Measurement State and De Finetti Measure

After measuring systems k+1,...,n with the coherent POVM, we obtain
a conditional state on systems 1,...,k. The mixture over measurement
outcomes reproduces the reduced state ρ_k.

The de Finetti measure is constructed from the Ψ-weighted Haar measure
pushed forward through the pure-state map g ↦ |g₀⟩⟨g₀|. This is
the SAME measure for all k, which is the key structural property.
-/

/-- The POVM outcome weight: w(g) = dim(Sym^n) · Tr(|v^g_n⟩⟨v^g_n| · Ψ).
    This is the probability density for outcome g when measuring with
    the coherent-state POVM. Satisfies ∫ w(g) dg = 1 by `schur_integral_trace`. -/
noncomputable def postMeasurementWeight {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (g : unitaryGroup (Fin d) ℂ) : ℝ :=
  (Nat.choose (n + d - 1) (d - 1) : ℝ) *
    ((coherentStateDensityOp g n).toOp * Ψ.toOp).trace.re

-- Helper lemmas for the coherentState_deFinettiMeasure construction

/-- The post-measurement weight w(g) is nonneg: it is dim(Sym^n) * Tr(PSD * PSD).re ≥ 0. -/
lemma postMeasurementWeight_nonneg {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n)) (g : unitaryGroup (Fin d) ℂ) :
    0 ≤ postMeasurementWeight Ψ g := by
  simp only [postMeasurementWeight]
  apply mul_nonneg
  · positivity
  · exact Quantum.Operators.trace_mul_psd_nonneg _ _
      (posSemidefOp_implies_mathlib (coherentStateDensityOp g n).toPosSemidefOp)
      (posSemidefOp_implies_mathlib Ψ.toPosSemidefOp)

/-- The post-measurement weight is integrable over Haar measure. -/
lemma postMeasurementWeight_integrable {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n)) :
    MeasureTheory.Integrable (postMeasurementWeight Ψ)
      (haarProbUnitary d) := by
  unfold postMeasurementWeight
  apply Integrable.const_mul
  apply ContinuousLinearMap.integrable_comp Complex.reCLM
  simp only [Matrix.trace, Matrix.diag]
  apply integrable_finsetSum
  intro i _
  simp only [Matrix.mul_apply]
  apply integrable_finsetSum
  intro j _
  exact (coherentStateDensityOp_entry_integrable i j).mul_const _

/-- The de Finetti measure constructed from the coherent-state POVM.

    The measure `μ` on `DensityOp d` is the pushforward of the weighted Haar measure
    `w(g) dg`, where `w(g) = postMeasurementWeight Ψ g`, along the pure-state map
    `g ↦ coherentSingleCopy g = |g₀⟩⟨g₀|`.

    This measure depends on `Ψ`, but not on the later choice of `k` in the CKMR
    approximation.

    **Reference**: CKMR definetti.tex line 371: `dm(g) := tr(E^g_n |Ψ⟩⟨Ψ|) dg`. -/
noncomputable def coherentState_deFinettiMeasure (d : ℕ) [NeZero d]
    {n : ℕ} [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (_hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp) :
    InfoTheory.DeFinetti.DensityMeasure d :=
  -- Construction: take Haar measure on U(d), weight by w(g) = postMeasurementWeight Ψ g,
  -- then push forward through g ↦ coherentSingleCopy g (= |g₀⟩⟨g₀|).
  -- The weighted measure dm(g) = w(g) · d(haar)(g) is a probability measure
  -- by schur_integral_trace. Its pushforward through g ↦ |g₀⟩⟨g₀| gives
  -- a probability measure on DensityOp d.
  let weightedHaar : Measure (unitaryGroup (Fin d) ℂ) :=
    (haarProbUnitary d).withDensity
      (fun g => ENNReal.ofReal (postMeasurementWeight Ψ g))
  { measure := Measure.map (fun g => coherentSingleCopy g) weightedHaar
    isProbability := by
      have hprob : IsProbabilityMeasure weightedHaar := by
        constructor
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        rw [← ofReal_integral_eq_lintegral_ofReal
          (postMeasurementWeight_integrable Ψ)
          (ae_of_all _ (postMeasurementWeight_nonneg Ψ))]
        have : ∫ g, postMeasurementWeight Ψ g ∂(haarProbUnitary d) = 1 :=
          schur_integral_trace d n Ψ _hsym
        rw [this]; simp
      infer_instance }

/-- The single-copy coherent state `|g₀⟩⟨g₀|` is a pure density operator
    for every `g ∈ U(d)`. Direct corollary of `DensityOp.fromPure_isPure`. -/
lemma coherentSingleCopy_isPure {d : ℕ} [NeZero d]
    (g : unitaryGroup (Fin d) ℂ) : (coherentSingleCopy g).IsPure := by
  unfold coherentSingleCopy
  exact DensityOp.fromPure_isPure _ _

/-- The CKMR de Finetti measure built from the coherent-state POVM is a
    pure-state (product-state) measure: it is concentrated on rank-1
    projectors `|g₀⟩⟨g₀|`.

    Proof: `coherentState_deFinettiMeasure` is by construction the
    pushforward `Measure.map coherentSingleCopy (w · haar)`, and every
    state in the image of `coherentSingleCopy` is pure
    (`coherentSingleCopy_isPure`). Hence the predicate
    `IsProductStateMeasure` holds for the constructed measure.

    This is the canonical witness used by `pure_state_deFinetti_symmetric`
    and (via `reindexInterleave`) `deFinetti_paired`; downstream
    code that needs the pure-state-support condition of CKMR Cor II.3
    can derive it from this lemma without modifying the existential
    conclusions of those theorems. -/
lemma coherentState_deFinettiMeasure_isProductStateMeasure
    (d : ℕ) [NeZero d] {n : ℕ} [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp) :
    (coherentState_deFinettiMeasure d Ψ hsym).IsProductStateMeasure := by
  -- Reduce to a.e. predicate on the pushforward source.
  -- The underlying measure unfolds to `Measure.map coherentSingleCopy (weightedHaar)`.
  change ∀ᵐ σ ∂(MeasureTheory.Measure.map (fun g => coherentSingleCopy g)
    ((haarProbUnitary d).withDensity
      (fun g => ENNReal.ofReal (postMeasurementWeight Ψ g)))), σ.IsPure
  -- Measurability of `{σ | σ.IsPure}`: same Borel-closed argument as for
  -- `deFinetti_haarMeasure_isProductStateMeasure`.
  have h_toOp : Continuous (fun σ : DensityOp d => σ.toOp) := continuous_induced_dom
  have h_meas : MeasurableSet (Set.ofPred (fun σ : DensityOp d => σ.IsPure)) := by
    have hset : Set.ofPred (fun σ : DensityOp d => σ.IsPure)
        = Set.ofPred (fun σ : DensityOp d => σ.toOp * σ.toOp = σ.toOp) := rfl
    rw [hset]
    exact (isClosed_eq (h_toOp.mul h_toOp) h_toOp).measurableSet
  refine (MeasureTheory.ae_map_iff coherentSingleCopy_measurable.aemeasurable
    h_meas).mpr ?_
  exact MeasureTheory.ae_of_all _ (fun g => coherentSingleCopy_isPure g)

/-- The post-measurement `k`-copy state: the conditional state on systems
    1,...,k after POVM outcome g, normalized so that
    ρ_k = ∫ w(g) · ξ^g_k dg.

    Formally, ξ^g_k := dim(Sym^{n-k}) · (I_k ⊗ ⟨v^g_{n-k}|) Ψ (I_k ⊗ |v^g_{n-k}⟩) / w(g),
    where the partial inner product acts on systems k+1,...,n and w(g)
    is `postMeasurementWeight`. The dim(Sym^{n-k}) factor converts between
    the (n-k)-POVM weight and the n-POVM weight used in `postMeasurementWeight`.

    This is defined as an `Op`; its positivity and normalization are handled
    separately in later arguments.

    **Reference**: CKMR definetti.tex lines 370-380. -/
noncomputable def postMeasurementState_k {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n)) (k : ℕ) [NeZero k] (hk : k ≤ n)
    (g : unitaryGroup (Fin d) ℂ) : Op (d ^ k) :=
  -- Cast Ψ to bipartite space: d^n = d^k * d^(n-k)
  let Ψ_bipartite : Op (d ^ k * d ^ (n - k)) :=
    (DensityOp.castDim (InfoTheory.DeFinetti.pow_eq_mul_pow_sub hk) Ψ).toOp
  -- Coherent state vector on the last (n-k) systems.
  -- When n = k, d^(n-k) = d^0 = 1, and the vector is just [1].
  let v : Fin (d ^ (n - k)) → ℂ := fun c =>
    if _hnk : n - k = 0 then 1
    else
      -- Big-endian digit extraction matching coherentStateKet convention
      ∏ j : Fin (n - k), (g : Matrix (Fin d) (Fin d) ℂ)
        ⟨(c.val / d ^ (n - k - 1 - j.val)) % d,
          Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))⟩ 0
  -- Partial inner product: (I_{d^k} ⊗ ⟨v|) Ψ (I_{d^k} ⊗ |v⟩)
  -- Entry (a, b) = ∑_{c, c'} v̄_c · Ψ_{(a,c),(b,c')} · v_{c'}
  let unnormalized : Op (d ^ k) := Matrix.of fun a b =>
    ∑ c : Fin (d ^ (n - k)), ∑ c' : Fin (d ^ (n - k)),
      starRingEnd ℂ (v c) *
        Ψ_bipartite (finProdFinEquiv (a, c)) (finProdFinEquiv (b, c')) *
        v c'
  -- Scale by dim(Sym^{n-k}) and normalize by w(g) = postMeasurementWeight Ψ g.
  -- This ensures w(g) · ξ^g_k = dim(Sym^{n-k}) · unnormalized, which integrates
  -- to ρ_k by Schur's lemma on the (n-k) system:
  --   ∫ dim(Sym^{n-k}) · (I_k ⊗ ⟨v^g_{n-k}|)Ψ(I_k ⊗ |v^g_{n-k}⟩) dg
  --     = Tr_B[(I_k ⊗ P_sym^{n-k})Ψ(I_k ⊗ P_sym^{n-k})] = Tr_B[Ψ] = ρ_k
  let w := postMeasurementWeight Ψ g
  let dim_sym_nk : ℝ := (Nat.choose (n - k + d - 1) (d - 1) : ℝ)
  if w = 0 then 0 else ((dim_sym_nk / w : ℝ) : ℂ) • unnormalized

/-- Scalar cancellation: w • ((c/w : ℂ) • M) = (c : ℂ) • M when w ≠ 0.
    Used to simplify w(g) • ξ^g_k = dim_{n-k} • unnormalized(g). -/
lemma smul_complex_ofReal_div_cancel {N : ℕ} (w c : ℝ) (hw : w ≠ 0)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    w • ((↑(c / w) : ℂ) • M) = (↑c : ℂ) • M := by
  rw [Complex.ofReal_div, ← smul_assoc]
  congr 1
  rw [Complex.real_smul, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hw)]

/-- Entry-level form of permutation invariance: for symmetric Ψ,
    Ψ(e(f ∘ π), j) = Ψ(e(f), j) where e = finFunctionFinEquiv d n.
    Follows from `symmetric_perm_invariant`: U_π * Ψ = Ψ. -/
lemma symmetric_perm_invariant_entry {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (π : Equiv.Perm (Fin n)) (f : Fin n → Fin d) (j : Fin (d ^ n)) :
    Ψ.toOp ((@finFunctionFinEquiv d n) (f ∘ π)) j =
    Ψ.toOp ((@finFunctionFinEquiv d n) f) j := by
  have hinv := symmetric_perm_invariant Ψ hsym π
  -- (U_π * Ψ)(i, j) = Ψ(i, j)
  set e := @finFunctionFinEquiv d n with he_def
  set i := e f with hi_def
  have h_entry : (permutationRepresentation d n π * Ψ.toOp) i j = Ψ.toOp i j :=
    congr_fun (congr_fun hinv i) j
  -- (U_π * Ψ)(i, j) = ∑_k U_π(i,k) * Ψ(k,j) = Ψ(e(f ∘ π), j)
  -- because U_π(i,k) = 1 iff e.symm(i) = e.symm(k) ∘ π.symm, i.e., k = e(f ∘ π)
  rw [mul_apply] at h_entry
  -- The sum has exactly one nonzero term, at k = e(f ∘ π)
  have h_collapse : ∑ k, permutationRepresentation d n π i k * Ψ.toOp k j =
      Ψ.toOp (e (f ∘ π)) j := by
    rw [Finset.sum_eq_single_of_mem (e (f ∘ π)) (Finset.mem_univ _)]
    · -- This term has indicator = 1
      simp only [permutationRepresentation, Matrix.of_apply, hi_def, he_def]
      rw [ite_eq_left]
      · ring
      · ext l; simp [Function.comp_apply, Equiv.symm_apply_apply]
    · -- All other terms have indicator = 0
      intro k _ hk
      simp only [permutationRepresentation, Matrix.of_apply, hi_def, he_def]
      rw [ite_eq_right, zero_mul]
      intro heq
      apply hk
      -- From heq: f = e.symm k ∘ π.symm, so f ∘ π = e.symm k, so k = e(f ∘ π)
      have h1 : f = e.symm k ∘ π.symm := by
        rwa [Equiv.symm_apply_apply] at heq
      have h2 : e.symm k = f ∘ π := by
        ext l; have := congr_fun h1 (π l)
        simp only [Function.comp_apply, Equiv.symm_apply_apply] at this
        simp only [Function.comp_apply]; omega
      rw [← h2, Equiv.apply_symm_apply]
  rw [h_collapse] at h_entry
  -- h_entry : Ψ.toOp (e (f ∘ π)) j = Ψ.toOp i j, and i = e f
  rw [hi_def] at h_entry; exact h_entry

/-- Bipartite permutation invariance: for Ψ in Sym^n and σ ∈ S_{n-k}, the bipartite
    reindexing Ψ_bip satisfies Ψ_bip((a, σ·c), j) = Ψ_bip((a, c), j).

    This is the bipartite-space form of `symmetric_perm_invariant_entry`. The permutation
    σ acts on the B-index (last n-k systems) via the finFunctionFinEquiv encoding, while the
    A-index (first k systems) is unchanged.

    **Proof**: Embed σ ∈ S_{n-k} into S_n by fixing the first k positions. Then
    `symmetric_perm_invariant_entry` gives invariance in d^n space, and
    `castDim_toOp_cast` + `cast_finProdFinEquiv_finFunctionFinEquiv` translate
    to the bipartite space. -/
lemma bipartite_perm_invariant {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (hk : k ≤ n) [NeZero (n - k)]
    (σ : Equiv.Perm (Fin (n - k)))
    (a : Fin (d ^ k)) (c : Fin (d ^ (n - k))) (j : Fin (d ^ k * d ^ (n - k))) :
    let Ψ_bip := (DensityOp.castDim (InfoTheory.DeFinetti.pow_eq_mul_pow_sub hk) Ψ).toOp
    let e_nk := @finFunctionFinEquiv d (n - k)
    let σ_action : Fin (d ^ (n - k)) → Fin (d ^ (n - k)) :=
      fun c => e_nk (e_nk.symm c ∘ σ)
    Ψ_bip (finProdFinEquiv (a, σ_action c)) j = Ψ_bip (finProdFinEquiv (a, c)) j := by
  intro Ψ_bip e_nk σ_action
  simp only [Ψ_bip, castDim_toOp_cast]
  -- Define the embedded permutation ι : S_{n-k} ↪ S_n (fixes first k positions)
  let embed : Fin (n - k) ≃ { m : Fin n // (m : ℕ) < n - k } :=
    ⟨fun m => ⟨⟨m.val, by omega⟩, m.isLt⟩,
     fun ⟨m, hm⟩ => ⟨m.val, hm⟩,
     fun m => by ext; simp,
     fun ⟨⟨_, _⟩, _⟩ => by simp⟩
  let ι := σ.extendDomain embed
  -- Set up digit functions
  set f_a := (@finFunctionFinEquiv d k).symm a with hf_a_def
  set f_c := (@finFunctionFinEquiv d (n - k)).symm c with hf_c_def
  have ha : a = finFunctionFinEquiv f_a := (Equiv.apply_symm_apply _ a).symm
  have hc : c = finFunctionFinEquiv f_c := (Equiv.apply_symm_apply _ c).symm
  have hσc : σ_action c = finFunctionFinEquiv (f_c ∘ σ) := by
    change e_nk (e_nk.symm c ∘ ⇑σ) = finFunctionFinEquiv (f_c ∘ σ)
    rfl
  -- The concatenated digit function g : Fin n → Fin d
  set g : Fin n → Fin d := fun m =>
    if hm : (m : ℕ) < n - k then f_c ⟨m.val, hm⟩ else f_a ⟨m.val - (n - k), by omega⟩
  -- Key: cast(fPE(a, c)) = e_n g (by digit_of_cast_finProdFinEquiv)
  have heq_c : Fin.cast (pow_eq_mul_pow_sub hk).symm (finProdFinEquiv (a, c)) =
      (@finFunctionFinEquiv d n) g := by
    have hfun : (@finFunctionFinEquiv d n).symm
        (Fin.cast (pow_eq_mul_pow_sub hk).symm (finProdFinEquiv (a, c))) = g := by
      funext m; rw [ha, hc]; exact digit_of_cast_finProdFinEquiv hk f_a f_c m
    rw [← hfun, Equiv.apply_symm_apply]
  -- Key: cast(fPE(a, σ_action c)) = e_n (g ∘ ι) (digits permuted by ι)
  have heq_σ : Fin.cast (pow_eq_mul_pow_sub hk).symm (finProdFinEquiv (a, σ_action c)) =
      (@finFunctionFinEquiv d n) (g ∘ ι) := by
    have hfun : (@finFunctionFinEquiv d n).symm
        (Fin.cast (pow_eq_mul_pow_sub hk).symm (finProdFinEquiv (a, σ_action c))) = g ∘ ι := by
      funext m
      -- LHS by digit_of_cast_finProdFinEquiv
      have hlhs : (@finFunctionFinEquiv d n).symm
          (Fin.cast (pow_eq_mul_pow_sub hk).symm (finProdFinEquiv (a, σ_action c))) m =
          if hm : (m : ℕ) < n - k then (f_c ∘ σ) ⟨m.val, hm⟩
          else f_a ⟨m.val - (n - k), by omega⟩ := by
        rw [ha, hσc]; exact digit_of_cast_finProdFinEquiv hk f_a (f_c ∘ σ) m
      rw [hlhs]
      -- RHS: (g ∘ ι) m — split on whether m < n-k
      change _ = g (ι m)
      by_cases hm : (m : ℕ) < n - k
      · rw [dite_eq_left hm]
        -- ι m = ⟨(σ ⟨m, hm⟩).val, ...⟩ when m < n-k
        have h_ι : ι m = ⟨(σ ⟨m.val, hm⟩).val, by omega⟩ := by
          change σ.extendDomain embed m = _
          rw [Equiv.Perm.extendDomain_apply_subtype σ embed hm]
          simp [embed]
        change (f_c ∘ σ) ⟨m.val, hm⟩ = g (ι m)
        simp only [Function.comp_apply]
        rw [h_ι]; show f_c (σ ⟨↑m, hm⟩) = g ⟨(σ ⟨↑m, hm⟩).val, _⟩
        simp only [g, dite_eq_left (σ ⟨m.val, hm⟩).isLt]
      · rw [dite_eq_right hm]
        -- ι m = m when m ≥ n-k
        have h_ι : ι m = m := Equiv.Perm.extendDomain_apply_not_subtype σ embed hm
        change f_a ⟨↑m - (n - k), _⟩ = g (ι m)
        rw [h_ι]; simp only [g, dite_eq_right hm]
    rw [← hfun, Equiv.apply_symm_apply]
  -- Apply symmetric_perm_invariant_entry
  rw [heq_σ, heq_c]
  exact symmetric_perm_invariant_entry Ψ hsym ι g (Fin.cast _ j)

/-- Symmetric containment: for Ψ in Sym^n, the bipartite reindexed form satisfies
    Tr_B[Ψ_bip] = Tr_B[(I ⊗ P_sym^{n-k}) · Ψ_bip].

    Equivalently: the partial trace is unchanged by inserting the symmetric projector
    on the B-index.

    **Proof**: Expand P_sym^{n-k} = (1/(n-k)!) Σ_σ U_σ. For each σ, the inner sum
    collapses to a single term (by the permutation representation definition), and by
    `bipartite_perm_invariant`, each term equals the original. Averaging gives the result.

    **Reference**: CKMR definetti.tex lines 345-365. -/
lemma symmetric_containment_bipartite {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (hk : k ≤ n) [NeZero (n - k)] :
    let Ψ_bip := (DensityOp.castDim (InfoTheory.DeFinetti.pow_eq_mul_pow_sub hk) Ψ).toOp
    ∀ a b : Fin (d ^ k),
      ∑ c : Fin (d ^ (n - k)),
        Ψ_bip (finProdFinEquiv (a, c)) (finProdFinEquiv (b, c)) =
      ∑ c : Fin (d ^ (n - k)), ∑ c' : Fin (d ^ (n - k)),
        symmetricProjector d (n - k) c c' *
        Ψ_bip (finProdFinEquiv (a, c')) (finProdFinEquiv (b, c)) := by
  intro Ψ_bip a b
  congr 1; funext c; symm
  -- Goal: ∑ c', P_sym(c,c') * Ψ_bip(fPE(a,c'), fPE(b,c)) = Ψ_bip(fPE(a,c), fPE(b,c))
  -- Key invariance from bipartite_perm_invariant
  set e := @finFunctionFinEquiv d (n - k) with he_def
  have hinv : ∀ σ : Equiv.Perm (Fin (n - k)),
      Ψ_bip (finProdFinEquiv (a, e (e.symm c ∘ ⇑σ))) (finProdFinEquiv (b, c)) =
      Ψ_bip (finProdFinEquiv (a, c)) (finProdFinEquiv (b, c)) :=
    fun σ => bipartite_perm_invariant Ψ hsym k hk σ a c (finProdFinEquiv (b, c))
  -- Expand P_sym = (1/(n-k)!) ∑_σ U_σ
  simp only [symmetricProjector, symmetricProjectorRep, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, permutationRepresentation, Matrix.of_apply]
  -- Goal: ∑_x (1/N! * (∑_σ indicator)) * Ψ_bip = Ψ_bip(...)
  -- Rearrange: pull 1/N! out, distribute inner sum, swap sum order
  simp_rw [mul_assoc]             -- (1/N! * sum) * Ψ → 1/N! * (sum * Ψ)
  rw [← Finset.mul_sum]           -- ∑_x 1/N! * f(x) → 1/N! * ∑_x f(x)
  simp_rw [Finset.sum_mul]        -- (∑_σ indicator) * Ψ → ∑_σ indicator * Ψ
  rw [Finset.sum_comm]            -- ∑_x ∑_σ → ∑_σ ∑_x
  -- Goal: 1/N! * ∑_σ ∑_c' indicator(c,c',σ) * Ψ_bip(fPE(a,c'), fPE(b,c)) = Ψ_bip(...)
  -- For each σ, collapse the inner sum over c'
  -- The indicator selects exactly c' = e(e.symm c ∘ σ)
  have h_collapse : ∀ σ : Equiv.Perm (Fin (n - k)),
      ∑ c' : Fin (d ^ (n - k)),
        (if (@finFunctionFinEquiv d (n - k)).symm c =
            (@finFunctionFinEquiv d (n - k)).symm c' ∘ ⇑(Equiv.symm σ) then (1 : ℂ) else 0) *
        Ψ_bip (finProdFinEquiv (a, c')) (finProdFinEquiv (b, c)) =
      Ψ_bip (finProdFinEquiv (a, c)) (finProdFinEquiv (b, c)) := by
    intro σ
    rw [Finset.sum_eq_single_of_mem (e (e.symm c ∘ ⇑σ)) (Finset.mem_univ _)]
    · -- The selected term: condition holds, gives 1 * Ψ(fPE(a, σ_action c), fPE(b, c))
      rw [ite_eq_left, one_mul]
      · exact hinv σ
      · -- e.symm c = e.symm(e(e.symm c ∘ σ)) ∘ σ⁻¹ = (e.symm c ∘ σ) ∘ σ⁻¹ = e.symm c
        simp only [← he_def] at *
        ext l; simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    · -- All other terms: condition fails, gives 0 * Ψ(...) = 0
      intro c' _ hne
      rw [ite_eq_right, zero_mul]
      intro heq; apply hne
      -- From heq: e.symm c = e.symm c' ∘ σ⁻¹, derive c' = e(e.symm c ∘ σ)
      simp only [← he_def] at heq
      have h1 : e.symm c' = e.symm c ∘ ⇑σ := by
        funext l; have := congr_fun heq (σ l)
        simp only [Function.comp_apply, Equiv.symm_apply_apply] at this ⊢
        exact this.symm
      exact (Equiv.apply_symm_apply e c').symm ▸ congr_arg e h1
  simp_rw [h_collapse]
  -- Goal: 1/N! * ∑_σ Ψ_bip(fPE(a,c), fPE(b,c)) = Ψ_bip(fPE(a,c), fPE(b,c))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, one_div_mul_cancel, one_mul]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/-- The real part of the trace of the coherent-state approximation integral equals 1.
    This follows from Tr(∫ w(g) • M_k(g) dg) = ∫ w(g) · Tr(M_k(g)) dg = ∫ w(g) dg = 1,
    using that Tr(coherentStateDensityOp g k) = 1 and `schur_integral_trace`. -/
lemma approx_integral_trace_re {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (_hk : k ≤ n) :
    (∫ g : unitaryGroup (Fin d) ℂ,
      postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
      ∂(haarProbUnitary d)).trace.re = 1 := by
  -- Strategy: Tr(∫ w(g)•M(g) dg) = ∫ Tr(w(g)•M(g)) dg = ∫ w(g)•1 dg = ∫ ↑w(g) dg
  -- then .re = ∫ w(g) dg = 1 by schur_integral_trace.
  have : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
  -- Step 0: Integrability
  have h_w_cont : Continuous (postMeasurementWeight Ψ) := by
    unfold postMeasurementWeight
    apply continuous_const.mul
    exact Complex.continuous_re.comp ((continuous_matrix
      (fun a b => coherentStateDensityOp_entry_continuous a b)
      |>.matrix_mul continuous_const).matrix_trace)
  have h_M_cont : Continuous (fun g : unitaryGroup (Fin d) ℂ =>
      (coherentStateDensityOp g k).toOp) :=
    continuous_matrix (fun a b => coherentStateDensityOp_entry_continuous a b)
  have h_int : Integrable (fun g : unitaryGroup (Fin d) ℂ =>
      postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp)
      (haarProbUnitary d) :=
    (h_w_cont.smul h_M_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- Step 1: Interchange trace and Bochner integral via trace CLM
  let trCLM : Op (d ^ k) →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M.trace
      map_add' := fun _ _ => Matrix.trace_add _ _
      map_smul' := fun _ _ => Matrix.trace_smul _ _ }
  rw [show (∫ g, postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
        ∂(haarProbUnitary d)).trace =
      ∫ g, (postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp).trace
        ∂(haarProbUnitary d) from (trCLM.integral_comp_comm h_int).symm]
  -- Step 2: trace(w g • M g) = w g • trace(M g) = w g • 1
  simp_rw [Matrix.trace_smul, show ∀ g : unitaryGroup (Fin d) ℂ,
    (coherentStateDensityOp g k).toOp.trace = 1 from
    fun g => (coherentStateDensityOp g k).trace_one]
  -- Goal: (∫ g, w g • (1 : ℂ) ∂haar).re = 1
  -- Step 3: Factor out constant 1 from integral, then take .re
  rw [integral_smul_const]
  -- Goal: ((∫ g, w g ∂haar) • (1 : ℂ)).re = 1
  rw [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]
  -- Goal: ∫ g, w g ∂haar = 1
  exact schur_integral_trace d n Ψ hsym

/-- The tensor-power integral of the CKMR de Finetti measure equals the
    corresponding POVM-weighted coherent-state Haar integral. -/
lemma integralTensorPower_coherentState_eq {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (_hk : k ≤ n) :
    (InfoTheory.DeFinetti.integralTensorPower k
      (coherentState_deFinettiMeasure d Ψ hsym)).toOp =
    ∫ g : unitaryGroup (Fin d) ℂ,
      postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
      ∂(haarProbUnitary d) := by
  -- Strategy: entrywise, chain integral_map + integral_withDensity + coherentState_is_tensorPow.
  set μ := coherentState_deFinettiMeasure d Ψ hsym
  -- The key identity: (coherentSingleCopy g).tensorPowGen k = coherentStateDensityOp g k
  have h_tensor_eq : ∀ g : unitaryGroup (Fin d) ℂ,
      ((coherentSingleCopy g).tensorPowGen k).toOp = (coherentStateDensityOp g k).toOp :=
    fun g => (coherentState_is_tensorPow g).symm
  -- Abbreviations
  set haar := haarProbUnitary d
  set w := postMeasurementWeight Ψ
  set wE := fun g : unitaryGroup (Fin d) ℂ => ENNReal.ofReal (w g)
  set weightedHaar := haar.withDensity wE
  -- The LHS measure is the pushforward of weightedHaar through coherentSingleCopy
  have h_measure_eq : μ.measure = Measure.map (fun g => coherentSingleCopy g) weightedHaar := by
    rfl
  -- Compare entrywise
  ext i j
  rw [integralTensorPower_toOp_apply]
  rw [h_measure_eq]
  -- LHS = ∫ σ, (σ.tensorPowGen k).toOp i j ∂(Measure.map coherentSingleCopy weightedHaar)
  -- Step 1: Change of variables via integral_map
  have h_f_cont := continuous_tensorPowGen_entry (d := d) (n := k) i j
  rw [MeasureTheory.integral_map_of_stronglyMeasurable
    coherentSingleCopy_measurable h_f_cont.stronglyMeasurable]
  -- Step 2: Unfold withDensity
  have h_w_aemeas : AEMeasurable wE haar := by
    apply AEMeasurable.ennreal_ofReal
    exact (postMeasurementWeight_integrable Ψ).aestronglyMeasurable.aemeasurable
  rw [integral_withDensity_eq_integral_toReal_smul₀ h_w_aemeas
    (ae_of_all _ (fun g => ENNReal.ofReal_lt_top))]
  -- Step 3: Simplify (ENNReal.ofReal (w g)).toReal = w g
  have h_toReal : ∀ g, (wE g).toReal = w g :=
    fun g => ENNReal.toReal_ofReal (postMeasurementWeight_nonneg Ψ g)
  simp_rw [h_toReal]
  -- Step 4: Apply coherentState_is_tensorPow
  simp_rw [h_tensor_eq]
  -- Step 5: Pull entry selection inside Bochner integral on RHS
  symm
  have : IsProbabilityMeasure haar := haarProbUnitary_isProbability d
  have h_M_cont : Continuous (fun g : unitaryGroup (Fin d) ℂ =>
      (coherentStateDensityOp g k).toOp) :=
    continuous_matrix (fun a b => coherentStateDensityOp_entry_continuous a b)
  have h_w_cont : Continuous w := by
    simp only [w]
    unfold postMeasurementWeight
    apply continuous_const.mul
    exact Complex.continuous_re.comp ((continuous_matrix
      (fun a b => coherentStateDensityOp_entry_continuous a b)
      |>.matrix_mul continuous_const).matrix_trace)
  have h_int : MeasureTheory.Integrable
      (fun g : unitaryGroup (Fin d) ℂ =>
        w g • (coherentStateDensityOp g k).toOp) haar :=
    (h_w_cont.smul h_M_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [matrix_integral_entry
    (fun g : unitaryGroup (Fin d) ℂ => w g • (coherentStateDensityOp g k).toOp)
    h_int i j]
  simp_rw [Matrix.smul_apply]

/-- The Bochner integral of PSD-valued functions is PSD.

    Proof: decompose `PosSemidef` into `IsHermitian` + non-negative quadratic form.
    Both are preserved by the Bochner integral via CLM interchange. -/
lemma bochner_integral_posSemidef {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {N : ℕ}
    (F : α → Matrix (Fin N) (Fin N) ℂ)
    (h_int : MeasureTheory.Integrable F μ)
    (h_psd : ∀ g, (F g).PosSemidef) :
    (∫ g, F g ∂μ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · -- IsHermitian: conjTranspose commutes with Bochner integral
    ext i j
    simp only [Matrix.conjTranspose_apply]
    rw [matrix_integral_entry F h_int j i, matrix_integral_entry F h_int i j]
    -- star (∫ F g j i) = ∫ conj(F g j i) = ∫ F g i j
    have h_star_int : star (∫ g, F g j i ∂μ) = ∫ g, starRingEnd ℂ (F g j i) ∂μ :=
      integral_conj.symm
    rw [h_star_int]
    congr 1; ext g
    have herm := (h_psd g).isHermitian
    simp only [Matrix.IsHermitian] at herm
    exact congr_fun (congr_fun herm i) j
  · -- ∀ x, 0 ≤ star x ⬝ᵥ (∫ F) *ᵥ x
    intro x
    -- The quadratic form is a CLM from matrices to ℂ
    let Q : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
      { toFun := fun M => star x ⬝ᵥ M *ᵥ x
        map_add' := fun A B => by simp [Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun r A => by
          change star x ⬝ᵥ (r • A).mulVec x = r • (star x ⬝ᵥ A.mulVec x)
          rw [Matrix.smul_mulVec, dotProduct_smul] }
    rw [show star x ⬝ᵥ (∫ g, F g ∂μ) *ᵥ x = ∫ g, (star x ⬝ᵥ (F g) *ᵥ x) ∂μ from
        (Q.integral_comp_comm h_int).symm]
    exact integral_nonneg_of_ae
      (ae_of_all _ (fun g => (Matrix.posSemidef_iff_dotProduct_mulVec.mp (h_psd g)).2 x))

end InfoTheory.DeFinetti.PureState
