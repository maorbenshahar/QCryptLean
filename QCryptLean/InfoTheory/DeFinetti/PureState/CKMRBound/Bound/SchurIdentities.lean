import QCryptLean.InfoTheory.DeFinetti.PureState.CKMRBound.Construction

/-!
# CKMR Schur Identities — ket embedding, unnormalized operator, Schur lemma applications

This module defines the partial ket embedding and unnormalized post-measurement operator
used in the CKMR trace distance bound, and establishes three Schur lemma identities
that relate Haar integrals of these operators to reduced states and coherent-state mixtures.

## Main definitions
- `ckmrKetEmbed`: Partial ket embedding V = (I_k ⊗ |v^g_{n-k}⟩)
- `ckmrUnnorm`: Unnormalized post-measurement operator V† · Ψ_bip · V

## Main statements
- `ckmrUnnorm_posSemidef`: the unnormalized operator V† · Ψ_bip · V is PSD
- `ckmr_schur_identity_1`: ∫ dim_{n-k} · unnorm(g) dg = ρ_k
- `coherent_mul_unnorm_as_partialTrace`: P_g^k · unnorm(g) = Tr_{n-k}(P_g^n_bip · Ψ_bip)
- `ckmr_schur_core_identity`: ∫ dim_n · P_g · unnorm(g) dg = ρ_k
- `ckmr_schur_identity_2`: ∫ dim_{n-k} · P_g · unnorm(g) dg = f · ρ_k
- `ckmr_schur_identity_2'`: ∫ dim_{n-k} · unnorm(g) · P_g dg = f · ρ_k
- `ckmr_schur_identity_3`: ∫ dim_{n-k} · P_g · unnorm(g) · P_g dg = f · σ_k

## References
- Christandl, König, Mitchison, Renner (2007) "One-and-a-Half Quantum de Finetti
  Theorems", Comm. Math. Phys. 273(2), 473-498 (Corollary II.2 / Theorem II.4)
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Symmetry MeasureTheory
open Math.HaarMeasure Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

noncomputable section

namespace InfoTheory.DeFinetti.PureState

private local instance {n : ℕ} : ContinuousENorm (Op n) := SeminormedAddGroup.toContinuousENorm

/-- The partial ket embedding V = (I_k ⊗ |v^g_{n-k}⟩) as a rectangular matrix.

    Maps d^k-vectors to d^(k*(n-k))-vectors by tensoring with the coherent state
    vector: (V · x)_{(a,c)} = δ_{a,a'} · v_c · x_{a'} = x_a · v_c.

    Used to express the unnormalized post-measurement operator as V† · Ψ_bip · V. -/
noncomputable def ckmrKetEmbed {d n : ℕ} [NeZero d] [NeZero n]
    (k : ℕ) [NeZero k] (_hk : k ≤ n)
    (g : unitaryGroup (Fin d) ℂ) : Matrix (Fin (d ^ k * d ^ (n - k))) (Fin (d ^ k)) ℂ :=
  let v : Fin (d ^ (n - k)) → ℂ := fun c =>
    if _hnk : n - k = 0 then 1
    else
      ∏ j : Fin (n - k), (g : Matrix (Fin d) (Fin d) ℂ)
        ⟨(c.val / d ^ (n - k - 1 - j.val)) % d,
          Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))⟩ 0
  Matrix.of fun i a' =>
    if (finProdFinEquiv.symm i).1 = a' then v (finProdFinEquiv.symm i).2 else 0

/-- The unnormalized post-measurement operator: V† · Ψ_bip · V where
    V = ckmrKetEmbed = (I_k ⊗ |v^g_{n-k}⟩).

    Equivalently, (I_k ⊗ ⟨v^g_{n-k}|) Ψ (I_k ⊗ |v^g_{n-k}⟩), the partial inner
    product of Ψ with the coherent state on the last (n-k) systems.

    PSD as V† · PSD · V by `conjTranspose_mul_mul_same`. -/
noncomputable def ckmrUnnorm {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n)) (k : ℕ) [NeZero k] (hk : k ≤ n)
    (g : unitaryGroup (Fin d) ℂ) : Op (d ^ k) :=
  let Ψ_bip : Op (d ^ k * d ^ (n - k)) :=
    (DensityOp.castDim (InfoTheory.DeFinetti.pow_eq_mul_pow_sub hk) Ψ).toOp
  let V := ckmrKetEmbed k hk g
  Vᴴ * Ψ_bip * V

/-- The unnormalized operator is PSD: it equals V† · Ψ_bip · V where Ψ_bip is PSD
    (a reindexing of the density operator Ψ). -/
lemma ckmrUnnorm_posSemidef {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (k : ℕ) [NeZero k] (hk : k ≤ n)
    (g : unitaryGroup (Fin d) ℂ) : (ckmrUnnorm Ψ k hk g).PosSemidef := by
  unfold ckmrUnnorm
  have h_psd : ((DensityOp.castDim
      (InfoTheory.DeFinetti.pow_eq_mul_pow_sub hk) Ψ).toOp).PosSemidef := by
    simp only [DensityOp.castDim]
    exact posSemidefOp_implies_mathlib (show DensityOp (d ^ k * d ^ (n - k)) from
      InfoTheory.DeFinetti.pow_eq_mul_pow_sub hk ▸ Ψ).toPosSemidefOp
  exact h_psd.conjTranspose_mul_mul_same _

/-- The coherent state vector on (n-k) systems, extracted from ckmrKetEmbed. -/
private noncomputable def ckmrVec {d : ℕ} [NeZero d]
    {n : ℕ} (k : ℕ) (_hk : k ≤ n) (g : unitaryGroup (Fin d) ℂ) :
    Fin (d ^ (n - k)) → ℂ :=
  fun c =>
    if _hnk : n - k = 0 then 1
    else ∏ j : Fin (n - k), (g : Matrix (Fin d) (Fin d) ℂ)
        ⟨(c.val / d ^ (n - k - 1 - j.val)) % d,
          Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))⟩ 0

/-- V entry simplification: V(fPE(a,c), x) = δ_{a,x} · v(c). -/
private lemma ckmrKetEmbed_entry' {d n : ℕ} [NeZero d] [NeZero n]
    (k : ℕ) [NeZero k] (hk : k ≤ n) (g : unitaryGroup (Fin d) ℂ)
    (a : Fin (d ^ k)) (c : Fin (d ^ (n - k))) (x : Fin (d ^ k)) :
    ckmrKetEmbed k hk g (finProdFinEquiv (a, c)) x =
    if a = x then ckmrVec k hk g c else 0 := by
  simp only [ckmrKetEmbed, ckmrVec, Matrix.of_apply]
  rw [finProdFinEquiv.symm_apply_apply]

/-- Delta collapse against column `b` of V: only the rows `(b, c)` contribute, with weight
`v(c)`. -/
private lemma sum_mul_ckmrKetEmbed {d n : ℕ} [NeZero d] [NeZero n]
    (k : ℕ) [NeZero k] (hk : k ≤ n) (g : unitaryGroup (Fin d) ℂ)
    (f : Fin (d ^ k * d ^ (n - k)) → ℂ) (b : Fin (d ^ k)) :
    ∑ j, f j * ckmrKetEmbed k hk g j b =
      ∑ c, f (finProdFinEquiv (b, c)) * ckmrVec k hk g c := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Fintype.sum_eq_single b]
  · simp only [ckmrKetEmbed_entry', if_pos]
  · intro x hx
    simp only [ckmrKetEmbed_entry', if_neg hx, mul_zero, Finset.sum_const_zero]

/-- Delta collapse against column `a` of V†: only the rows `(a, c)` contribute, with weight
`v̄(c)`. -/
private lemma sum_star_ckmrKetEmbed_mul {d n : ℕ} [NeZero d] [NeZero n]
    (k : ℕ) [NeZero k] (hk : k ≤ n) (g : unitaryGroup (Fin d) ℂ)
    (f : Fin (d ^ k * d ^ (n - k)) → ℂ) (a : Fin (d ^ k)) :
    ∑ i, star (ckmrKetEmbed k hk g i a) * f i =
      ∑ c, star (ckmrVec k hk g c) * f (finProdFinEquiv (a, c)) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Fintype.sum_eq_single a]
  · simp only [ckmrKetEmbed_entry', if_pos]
  · intro x hx
    simp only [ckmrKetEmbed_entry', if_neg hx, star_zero, zero_mul, Finset.sum_const_zero]

/-- Entries of the unnormalized operator:
`unnorm(g)(a, b) = ∑_{c'} ∑_c v̄(c) · Ψ_bip((a,c),(b,c')) · v(c')`. -/
private lemma ckmrUnnorm_apply {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n)) (k : ℕ) [NeZero k] (hk : k ≤ n)
    (g : unitaryGroup (Fin d) ℂ) (a b : Fin (d ^ k)) :
    ckmrUnnorm Ψ k hk g a b =
      ∑ c', ∑ c, star (ckmrVec k hk g c) *
        (DensityOp.castDim (InfoTheory.DeFinetti.pow_eq_mul_pow_sub hk) Ψ).toOp
          (finProdFinEquiv (a, c)) (finProdFinEquiv (b, c')) * ckmrVec k hk g c' := by
  simp only [ckmrUnnorm, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [sum_mul_ckmrKetEmbed]
  simp only [sum_star_ckmrKetEmbed_mul, Finset.sum_mul]

/-- For `n - k ≠ 0`, the vector `v` of V is the coherent-state ket on the last `n - k`
systems. -/
private lemma ckmrVec_eq_coherentStateKet {d n : ℕ} [NeZero d]
    (k : ℕ) (hk : k ≤ n) [NeZero (n - k)] (g : unitaryGroup (Fin d) ℂ)
    (c : Fin (d ^ (n - k))) :
    ckmrVec k hk g c = (coherentStateKet g (n - k)).vec c :=
  dif_neg (NeZero.ne (n - k))

/-- Schur Identity 1: ∫ dim_{n-k} · unnorm(g) dg = ρ_k.
    Follows from `schur_lemma_symmetric` on (n-k) systems + `symmetric_containment_bipartite`. -/
lemma ckmr_schur_identity_1 {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (_hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (_hk : k ≤ n) :
    ∫ g : unitaryGroup (Fin d) ℂ,
      (↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) • ckmrUnnorm Ψ k _hk g
      ∂(haarProbUnitary d) =
    (InfoTheory.DeFinetti.partialTraceToFirstK k _hk Ψ).toOp := by
  by_cases hnk : n = k
  · subst hnk
    haveI : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
    -- When n = k nothing is traced out: the second register is trivial and `v = 1`
    have hdim : d ^ (n - n) = 1 := by rw [Nat.sub_self, pow_zero]
    haveI : Unique (Fin (d ^ (n - n))) := hdim ▸ Fin.instUnique
    -- so for every `g` the integrand is already the reduced state
    have hconst : ∀ g : unitaryGroup (Fin d) ℂ,
        (↑(Nat.choose (n - n + d - 1) (d - 1)) : ℝ) • ckmrUnnorm Ψ n _hk g =
          (InfoTheory.DeFinetti.partialTraceToFirstK n _hk Ψ).toOp := by
      intro g
      simp only [Nat.sub_self, zero_add, Nat.choose_self, Nat.cast_one, one_smul]
      ext a b
      rw [ckmrUnnorm_apply]
      simp only [ckmrVec, dif_pos (Nat.sub_self n), star_one, one_mul, mul_one,
        Fintype.sum_unique, InfoTheory.DeFinetti.partialTraceToFirstK, DensityOp.partialTraceB,
        PosSemidefOp.partialTraceB, partialTraceB, Matrix.of_apply, densityOp_castDim_toOp]
    rw [integral_congr_ae (ae_of_all _ hconst), integral_const, probReal_univ, one_smul]
  · haveI : NeZero (n - k) := ⟨by omega⟩
    haveI : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
    set h_eq := InfoTheory.DeFinetti.pow_eq_mul_pow_sub _hk
    set Ψ_bip := (DensityOp.castDim h_eq Ψ).toOp with hΨ_bip
    -- Define CLM: M(A)(a,b) = ∑_c ∑_c' A(c',c) * Ψ_bip(fPE(a,c), fPE(b,c'))
    let M : Op (d ^ (n - k)) →L[ℝ] Op (d ^ k) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun A => Matrix.of fun a b =>
            ∑ c : Fin (d ^ (n - k)), ∑ c' : Fin (d ^ (n - k)),
              A c' c * Ψ_bip (finProdFinEquiv (a, c)) (finProdFinEquiv (b, c'))
          map_add' := fun A B => by
            ext a b; simp only [Matrix.of_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
          map_smul' := fun r A => by
            ext a b
            simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply, smul_mul_assoc,
              Finset.smul_sum] }
    have hM : ∀ A a b, M A a b = ∑ c : Fin (d ^ (n - k)), ∑ c' : Fin (d ^ (n - k)),
        A c' c * Ψ_bip (finProdFinEquiv (a, c)) (finProdFinEquiv (b, c')) :=
      fun _ _ _ => rfl
    -- Step 1: unnorm(g) = M((coherentStateDensityOp g (n-k)).toOp), entrywise:
    -- both sides are `∑_{c,c'} v̄(c) v(c') Ψ_bip((a,c),(b,c'))`
    have h_unnorm_M : ∀ g : unitaryGroup (Fin d) ℂ,
        ckmrUnnorm Ψ k _hk g = M ((coherentStateDensityOp g (n - k)).toOp) := by
      intro g; ext a b
      rw [ckmrUnnorm_apply, ← hΨ_bip, hM, Finset.sum_comm]
      refine Fintype.sum_congr _ _ fun c => Fintype.sum_congr _ _ fun c' => ?_
      simp only [coherentStateDensityOp, DensityOp.fromPure, ket_mul_bra_apply, Ket.dag_vec,
        starRingEnd_apply, ckmrVec_eq_coherentStateKet]
      exact (mul_rotate _ _ _).symm
    -- Step 2: Rewrite integrand and use CLM commutativity
    simp_rw [h_unnorm_M]
    have h_integrand : ∀ g,
        (↑((n - k + d - 1).choose (d - 1)) : ℝ) • M ((coherentStateDensityOp g (n - k)).toOp) =
        M ((↑((n - k + d - 1).choose (d - 1)) : ℝ) • (coherentStateDensityOp g (n - k)).toOp) :=
      fun g => (M.map_smul _ _).symm
    simp_rw [h_integrand]
    -- Integrability
    have h_Pg_cont : Continuous (fun g : unitaryGroup (Fin d) ℂ =>
        (coherentStateDensityOp g (n - k)).toOp) :=
      continuous_matrix (fun a b => coherentStateDensityOp_entry_continuous a b)
    have h_int : Integrable (fun g : unitaryGroup (Fin d) ℂ =>
        (↑((n - k + d - 1).choose (d - 1)) : ℝ) • (coherentStateDensityOp g (n - k)).toOp)
        (haarProbUnitary d) :=
      (continuous_const.smul h_Pg_cont).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    -- Interchange integral and CLM
    refine (M.integral_comp_comm h_int).trans ?_
    -- Apply Schur lemma: ∫ dim_{n-k} • Pg^{n-k} dg = symProj_{n-k}
    change M (∫ g, (↑((n - k + d - 1).choose (d - 1)) : ℝ) •
      (coherentStateDensityOp g (n - k)).toOp ∂haarProbUnitary d) = _
    rw [schur_lemma_symmetric d (n - k)]
    -- Step 3: M(symProj_{n-k}) = partialTraceB(Ψ_bip)
    -- M(symProj)(a,b) = ∑_c ∑_c' symProj(c',c) * Ψ_bip(fPE(a,c), fPE(b,c'))
    -- = ∑_c ∑_c' symProj(c,c') * Ψ_bip(fPE(a,c'), fPE(b,c))  [swap c↔c']
    -- = ∑_c Ψ_bip(fPE(a,c), fPE(b,c))  [by symmetric_containment_bipartite]
    -- = partialTraceB(Ψ_bip)(a,b)
    ext a b
    -- Swap summation order c ↔ c'
    rw [hM, Finset.sum_comm]
    -- Now: ∑_c' ∑_c symProj(c',c) * Ψ_bip(fPE(a,c), fPE(b,c'))
    -- = ∑_c ∑_c' symProj(c,c') * Ψ_bip(fPE(a,c'), fPE(b,c))  [rename]
    -- Apply symmetric_containment_bipartite
    have h_scb := symmetric_containment_bipartite Ψ _hsym k _hk
    -- h_scb: ∑_c Ψ_bip(fPE(a,c), fPE(b,c)) = ∑_c ∑_c' symProj(c,c') * Ψ_bip(fPE(a,c'), fPE(b,c))
    rw [← h_scb a b]
    -- Now goal: ∑_c Ψ_bip(fPE(a,c), fPE(b,c)) = (partialTraceToFirstK k _hk Ψ).toOp a b
    -- This is the definition of partialTraceToFirstK / partialTraceB
    simp only [InfoTheory.DeFinetti.partialTraceToFirstK, DensityOp.partialTraceB]
    rfl

/-- Symmetric projector times symmetric state equals the state. -/
lemma symProj_mul_symState {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp) :
    symmetricProjector d n * Ψ.toOp = Ψ.toOp := by
  have hP_idem := (symmetricProjector_is_projector d n).1
  calc symmetricProjector d n * Ψ.toOp
      = symmetricProjector d n *
        (symmetricProjector d n * Ψ.toOp * symmetricProjector d n) := by rw [hsym]
    _ = symmetricProjector d n * symmetricProjector d n *
        (Ψ.toOp * symmetricProjector d n) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = symmetricProjector d n * (Ψ.toOp * symmetricProjector d n) := by
        rw [hP_idem]
    _ = symmetricProjector d n * Ψ.toOp * symmetricProjector d n := by
        rw [Matrix.mul_assoc]
    _ = Ψ.toOp := hsym

/-- Operator casting preserves ℝ-scalar multiplication. -/
private lemma Op_castDim_smul_real {n m : ℕ} (h : n = m) (r : ℝ) (A : Op n) :
    Op.castDim h (r • A) = r • Op.castDim h A := by
  subst h; rfl

/-- Tensor factorization of bipartite coherent state entries.
    Pg_n_bip(fPE(a,c), fPE(x,c')) = Pg_k(a,x) · v(c) · star(v(c')).

    Uses `tensorPowGen_toOp_eq_prod` and `digit_of_cast_finProdFinEquiv`
    to split the n-product into k and (n-k) parts. -/
private lemma castDim_coherent_bipartite_entry {d n : ℕ} [NeZero d] [NeZero n]
    (k : ℕ) [NeZero k] (hk : k ≤ n) (g : unitaryGroup (Fin d) ℂ)
    (a x : Fin (d ^ k)) (c c' : Fin (d ^ (n - k))) :
    (DensityOp.castDim (InfoTheory.DeFinetti.pow_eq_mul_pow_sub hk)
      (coherentStateDensityOp g n)).toOp
      (finProdFinEquiv (a, c)) (finProdFinEquiv (x, c')) =
    (coherentStateDensityOp g k).toOp a x *
      (ckmrVec k hk g c * star (ckmrVec k hk g c')) := by
  -- Unfold to pure state entry formula: ψ(i) * star(ψ(j))
  rw [castDim_toOp_cast]
  simp only [coherentStateDensityOp, DensityOp.fromPure, ket_mul_bra_apply,
    Ket.dag_vec, starRingEnd_apply]
  -- Goal: ket_n(cast(fPE(a,c))) * star(ket_n(cast(fPE(x,c')))) =
  --   (ket_k(a) * star(ket_k(x))) * (v(c) * star(v(c')))
  -- Suffices to show ket factorization: ket_n(cast(fPE(a,c))) = ket_k(a) * v(c)
  simp only [coherentStateKet, ckmrVec]
  -- Now products of g entries. Use ket factorization.
  set hd := Nat.pos_of_ne_zero (NeZero.ne d)
  -- Ket factorization: ∏ j, g⟨digit_j(fPE(a,c))⟩ 0 = (∏_k) * (if … else ∏_{n-k})
  suffices h_ket : ∀ (a' : Fin (d ^ k)) (c₀ : Fin (d ^ (n - k))),
      (∏ j : Fin n, (g : Matrix (Fin d) (Fin d) ℂ)
        ⟨(Fin.cast (pow_eq_mul_pow_sub hk).symm (finProdFinEquiv (a', c₀))).val /
          d ^ (n - 1 - j.val) % d, Nat.mod_lt _ hd⟩ 0) =
      (∏ j : Fin k, (g : Matrix (Fin d) (Fin d) ℂ)
        ⟨a'.val / d ^ (k - 1 - j.val) % d, Nat.mod_lt _ hd⟩ 0) *
      (if _hnk : n - k = 0 then 1 else
        ∏ j : Fin (n - k), (g : Matrix (Fin d) (Fin d) ℂ)
          ⟨c₀.val / d ^ (n - k - 1 - j.val) % d, Nat.mod_lt _ hd⟩ 0) by
    rw [h_ket a c, h_ket x c', StarMul.star_mul]; ring
  intro a' c₀
  -- Setup
  have hkp : k + (n - k) = n := Nat.add_sub_cancel' hk
  have hdpow : (0 : ℕ) < d ^ (n - k) :=
    Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne d))
  -- Value of the bipartite index
  have hVval : (Fin.cast (pow_eq_mul_pow_sub hk).symm
      (finProdFinEquiv (a', c₀))).val = c₀.val + d ^ (n - k) * a'.val := by
    simp [finProdFinEquiv_apply_val]
  -- Division identity
  have hVdiv : (Fin.cast (pow_eq_mul_pow_sub hk).symm
      (finProdFinEquiv (a', c₀))).val / d ^ (n - k) = a'.val := by
    rw [hVval, Nat.add_mul_div_left _ _ hdpow, Nat.div_eq_of_lt c₀.isLt, zero_add]
  -- High digit: for j < k, digit(n-1-j) = a' digit(k-1-j)
  have high : ∀ j : ℕ, j < k →
      (Fin.cast (pow_eq_mul_pow_sub hk).symm (finProdFinEquiv (a', c₀))).val /
        d ^ (n - 1 - j) % d = a'.val / d ^ (k - 1 - j) % d := by
    intro j hj
    rw [show n - 1 - j = (n - k) + (k - 1 - j) from by omega,
      pow_add, ← Nat.div_div_eq_div_mul, hVdiv]
  -- Low digit: for i < n-k, digit(n-k-1-i) = c₀ digit(n-k-1-i)
  have low : ∀ i : ℕ, i < n - k →
      (Fin.cast (pow_eq_mul_pow_sub hk).symm (finProdFinEquiv (a', c₀))).val /
        d ^ (n - k - 1 - i) % d = c₀.val / d ^ (n - k - 1 - i) % d := by
    intro i hi
    conv_lhs =>
      rw [hVval, show d ^ (n - k) * a'.val =
        d ^ (n - k - 1 - i) * (d ^ (i + 1) * a'.val) from by
        conv_lhs => rw [show n - k = (n - k - 1 - i) + (i + 1) from by omega]
        rw [pow_add, mul_assoc]]
    rw [Nat.add_mul_div_left _ _
        (show (0 : ℕ) < d ^ (n - k - 1 - i) from by positivity),
      show d ^ (i + 1) * a'.val = d * (d ^ i * a'.val) from by
        rw [pow_succ, mul_comm (d ^ i) d, mul_assoc],
      Nat.add_mul_mod_self_left]
  -- Reindex product from Fin n to Fin (k + (n-k)) and split
  have prod_split := (Fintype.prod_equiv (finCongr hkp)
    (fun j : Fin (k + (n - k)) =>
      (g : Matrix (Fin d) (Fin d) ℂ)
        ⟨(Fin.cast (pow_eq_mul_pow_sub hk).symm
            (finProdFinEquiv (a', c₀))).val /
          d ^ (n - 1 - j.val) % d, Nat.mod_lt _ hd⟩ 0)
    (fun j : Fin n =>
      (g : Matrix (Fin d) (Fin d) ℂ)
        ⟨(Fin.cast (pow_eq_mul_pow_sub hk).symm
            (finProdFinEquiv (a', c₀))).val /
          d ^ (n - 1 - j.val) % d, Nat.mod_lt _ hd⟩ 0)
    (fun _ => rfl)).symm
  rw [prod_split, Fin.prod_univ_add]
  congr 1
  · -- First factor: Fin k → a' digits
    apply Finset.prod_congr rfl; intro ⟨m, hm⟩ _
    exact congrFun (congrArg (↑g) (Fin.ext (high m hm))) 0
  · -- Second factor: Fin (n-k) → c₀ digits or 1
    by_cases hnk : n - k = 0
    · rw [dif_pos hnk]
      exact Finset.prod_eq_one (fun i _ => absurd i.isLt (by omega))
    · rw [dif_neg hnk]
      apply Finset.prod_congr rfl; intro ⟨m, hm⟩ _
      have h_exp : n - 1 - (k + m) = n - k - 1 - m := by omega
      simp only [Fin.val_natAdd, h_exp]
      exact congrFun (congrArg (↑g) (Fin.ext (low m hm))) 0

/-- Tensor factorization: P_g^k · unnorm(g) = Tr_{n-k}(P_g^n_bip · Ψ_bip).

    The coherent state |v^g_n⟩ on n systems factors as |v^g_k⟩ ⊗ |v^g_{n-k}⟩.
    Therefore P_g^n reindexed to the bipartite system d^k ⊗ d^{n-k} equals
    P_g^k ⊗ P_g^{n-k}. Taking Tr_{n-k}((P_g^k ⊗ P_g^{n-k}) · Ψ_bip) gives
    P_g^k · (I_k ⊗ ⟨v^g|) Ψ_bip (I_k ⊗ |v^g⟩) = P_g^k · unnorm(g). -/
lemma coherent_mul_unnorm_as_partialTrace {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n)) (k : ℕ) [NeZero k] (hk : k ≤ n)
    (g : unitaryGroup (Fin d) ℂ) :
    (coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k hk g =
    partialTraceB
      ((DensityOp.castDim (InfoTheory.DeFinetti.pow_eq_mul_pow_sub hk)
          (coherentStateDensityOp g n)).toOp *
       (DensityOp.castDim (InfoTheory.DeFinetti.pow_eq_mul_pow_sub hk) Ψ).toOp) := by
  ext a b
  -- LHS: `∑ₓ P_k(a,x) · unnorm(x,b)`, with `unnorm` expanded to its double sum over `c', c`;
  -- RHS: `∑_{c₀} ∑_j P_n((a,c₀), j) · Ψ_bip(j, (b,c₀))`
  simp only [Matrix.mul_apply, ckmrUnnorm_apply, Finset.mul_sum, partialTraceB, Matrix.of_apply]
  -- split `j = (x, c')` and factor `P_n((a,c₀),(x,c')) = P_k(a,x) · v(c₀) · v̄(c')`
  simp only [← (finProdFinEquiv (m := d ^ k) (n := d ^ (n - k))).sum_comp,
    Fintype.sum_prod_type, castDim_coherent_bipartite_entry k hk g]
  -- bring `x` outermost on the right; the summands then agree termwise
  conv_rhs => rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun x => Fintype.sum_congr _ _ fun c' =>
    Fintype.sum_congr _ _ fun c => ?_
  ring

/-- Core Schur identity: ∫ dim_n · P_g · unnorm(g) dg = ρ_k.

    **Proof sketch** (3 steps):
    1. By `coherent_mul_unnorm_as_partialTrace`:
       P_g^k · unnorm(g) = Tr_{n-k}(P_g^n_bip · Ψ_bip).
    2. Interchange integral and Tr_{n-k} (both are continuous linear maps),
       then use `schur_lemma_symmetric`: ∫ dim_n · P_g^n dg = P_sym^n.
    3. P_sym · Ψ = Ψ (from symmetry hypothesis), so
       Tr_{n-k}(P_sym_bip · Ψ_bip) = Tr_{n-k}(Ψ_bip) = ρ_k. -/
lemma ckmr_schur_core_identity {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (_hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (_hk : k ≤ n) :
    ∫ g : unitaryGroup (Fin d) ℂ,
      (↑(Nat.choose (n + d - 1) (d - 1)) : ℝ) •
        ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g)
      ∂(haarProbUnitary d) =
    (InfoTheory.DeFinetti.partialTraceToFirstK k _hk Ψ).toOp := by
  -- Step 1: Rewrite integrand using tensor factorization
  simp_rw [coherent_mul_unnorm_as_partialTrace Ψ k _hk]
  -- Steps 2-5: interchange integral and Tr_B, apply Schur, use symmetry
  -- Key facts
  have hPΨ := symProj_mul_symState Ψ _hsym
  have hSchur := schur_lemma_symmetric d n
  haveI : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
  set h_eq := InfoTheory.DeFinetti.pow_eq_mul_pow_sub _hk
  -- Rewrite product using castDim_mul (combine the two castDim'd operators)
  simp_rw [densityOp_castDim_toOp]
  simp_rw [Op.castDim_mul h_eq]
  -- Define CLM: M(A) = partialTraceB(Op.castDim h_eq (A * Ψ.toOp))
  -- This maps Op (d^n) →L[ℝ] Op (d^k)
  let M : Op (d ^ n) →L[ℝ] Op (d ^ k) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun A => partialTraceB (Op.castDim h_eq (A * Ψ.toOp))
        map_add' := fun A B => by
          rw [add_mul, Op.castDim_add h_eq]
          exact partialTraceB_add _ _
        map_smul' := fun r A => by
          simp only [RingHom.id_apply, smul_mul_assoc]
          rw [Op_castDim_smul_real h_eq]
          exact partialTraceB_real_smul r _ }
  -- Rewrite integrand as M(c • Pg.toOp) using linearity
  have h_integrand : ∀ g : unitaryGroup (Fin d) ℂ,
      (↑((n + d - 1).choose (d - 1)) : ℝ) •
        partialTraceB (Op.castDim h_eq ((coherentStateDensityOp g n).toOp * Ψ.toOp)) =
      M ((↑((n + d - 1).choose (d - 1)) : ℝ) • (coherentStateDensityOp g n).toOp) := by
    intro g; symm
    exact M.map_smul _ _
  simp_rw [h_integrand]
  -- Integrability of c • Pg
  have h_Pg_cont : Continuous (fun g : unitaryGroup (Fin d) ℂ =>
      (coherentStateDensityOp g n).toOp) :=
    continuous_matrix (fun a b => coherentStateDensityOp_entry_continuous a b)
  have h_int : Integrable (fun g : unitaryGroup (Fin d) ℂ =>
      (↑((n + d - 1).choose (d - 1)) : ℝ) • (coherentStateDensityOp g n).toOp)
      (haarProbUnitary d) :=
    (continuous_const.smul h_Pg_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- Apply CLM.integral_comp_comm: ∫ M(f(g)) dg = M(∫ f(g) dg)
  refine (M.integral_comp_comm h_int).trans ?_
  -- Apply Schur: ∫ c • Pg dg = Psym
  change M (∫ g, (↑((n + d - 1).choose (d - 1)) : ℝ) • (coherentStateDensityOp g n).toOp
      ∂haarProbUnitary d) = _
  rw [hSchur]
  -- M(Psym) = TrB(castDim(Psym * Ψ)) = TrB(castDim(Ψ))
  change partialTraceB (Op.castDim h_eq (symmetricProjector d n * Ψ.toOp)) = _
  rw [hPΨ]
  -- TrB(castDim(Ψ.toOp)) = ρ_k.toOp  (by definition of partialTraceToFirstK)
  show partialTraceB (Op.castDim h_eq Ψ.toOp) =
    (InfoTheory.DeFinetti.partialTraceToFirstK k _hk Ψ).toOp
  -- partialTraceToFirstK unfolds to DensityOp.partialTraceB (DensityOp.castDim h Ψ)
  -- and (DensityOp.partialTraceB X).toOp = partialTraceB X.toOp
  -- and (DensityOp.castDim h Ψ).toOp = Op.castDim h Ψ.toOp
  rw [← densityOp_castDim_toOp h_eq Ψ]
  rfl

/-- Schur Identity 2: ∫ dim_{n-k} · P_g · unnorm(g) dg = f · ρ_k.
    Follows from `ckmr_schur_core_identity` by rescaling:
    dim_{n-k} = (dim_{n-k}/dim_n) · dim_n. -/
lemma ckmr_schur_identity_2 {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (_hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (_hk : k ≤ n) :
    ∫ g : unitaryGroup (Fin d) ℂ,
      (↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) •
        ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g)
      ∂(haarProbUnitary d) =
    ((↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) /
      ↑(Nat.choose (n + d - 1) (d - 1))) •
    (InfoTheory.DeFinetti.partialTraceToFirstK k _hk Ψ).toOp := by
  have h_core := ckmr_schur_core_identity Ψ _hsym k
  rw [← h_core]
  -- Goal: ∫ dim_{n-k} • f dg = (dim_{n-k}/dim_n) • ∫ dim_n • f dg
  -- Pull constants out of both integrals
  rw [MeasureTheory.integral_smul, MeasureTheory.integral_smul, smul_smul]
  -- Goal: dim_{n-k} • ∫ f = (dim_{n-k}/dim_n * dim_n) • ∫ f
  congr 1
  have h_pos : (0 : ℝ) < ↑((n + d - 1).choose (d - 1)) := by
    exact_mod_cast Nat.choose_pos (by omega)
  field_simp

/-- Bochner integral commutes with matrix conjTranspose (entry-wise). -/
lemma integral_conjTranspose {m : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {F : α → Matrix (Fin m) (Fin m) ℂ}
    (hF : MeasureTheory.Integrable F μ) :
    ∫ g, (F g)ᴴ ∂μ = (∫ g, F g ∂μ)ᴴ := by
  ext i j
  simp only [Matrix.conjTranspose_apply]
  let L : ∀ (a b : Fin m), Matrix (Fin m) (Fin m) ℂ →L[ℝ] ℂ := fun a b =>
    LinearMap.toContinuousLinearMap
      ({ toFun := fun (M : Matrix (Fin m) (Fin m) ℂ) => M a b
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ℂ)
  have rhs_eq : (∫ g, F g ∂μ) j i = ∫ g, F g j i ∂μ :=
    ((L j i).integral_comp_comm hF).symm
  have hFct : MeasureTheory.Integrable (fun g => (F g)ᴴ) μ := by
    let ct : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
      LinearMap.toContinuousLinearMap
        ({ toFun := fun M => Mᴴ
           map_add' := fun _ _ => conjTranspose_add _ _
           map_smul' := fun _ _ => by
             simp only [Matrix.conjTranspose_smul, RingHom.id_apply,
               star_trivial] } : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ]
                Matrix (Fin m) (Fin m) ℂ)
    exact ct.integrable_comp hF
  have lhs_eq : (∫ g, (F g)ᴴ ∂μ) i j =
      ∫ g, (F g)ᴴ i j ∂μ :=
    ((L i j).integral_comp_comm hFct).symm
  rw [lhs_eq, rhs_eq]
  simp only [Matrix.conjTranspose_apply]
  change ∫ g, starRingEnd ℂ (F g j i) ∂μ =
    starRingEnd ℂ (∫ g, F g j i ∂μ)
  exact integral_conj

/-- Schur Identity 2': ∫ dim_{n-k} · unnorm(g) · P_g dg = f · ρ_k.
    Adjoint of identity 2: follows from Hermitianness of A, P, and ρ. -/
lemma ckmr_schur_identity_2' {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (_hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (_hk : k ≤ n) :
    ∫ g : unitaryGroup (Fin d) ℂ,
      (↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) •
        (ckmrUnnorm Ψ k _hk g * (coherentStateDensityOp g k).toOp)
      ∂(haarProbUnitary d) =
    ((↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) /
      ↑(Nat.choose (n + d - 1) (d - 1))) •
    (InfoTheory.DeFinetti.partialTraceToFirstK k _hk Ψ).toOp := by
  -- Pointwise: A * P = (P * A)^†
  have h_pw : ∀ g : unitaryGroup (Fin d) ℂ,
      ckmrUnnorm Ψ k _hk g * (coherentStateDensityOp g k).toOp =
      ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g)ᴴ := by
    intro g
    rw [Matrix.conjTranspose_mul,
        (ckmrUnnorm_posSemidef Ψ k _hk g).isHermitian.eq,
        (posSemidefOp_implies_mathlib (coherentStateDensityOp g k).toPosSemidefOp).isHermitian.eq]
  -- Rewrite integrand: c • (A * P) = c • (P * A)^† = (c • (P * A))^†
  have h_pw2 : ∀ g : unitaryGroup (Fin d) ℂ,
      (↑((n - k + d - 1).choose (d - 1)) : ℝ) •
        (ckmrUnnorm Ψ k _hk g * (coherentStateDensityOp g k).toOp) =
      ((↑((n - k + d - 1).choose (d - 1)) : ℝ) •
        ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g))ᴴ := by
    intro g
    rw [h_pw g, Matrix.conjTranspose_smul, star_natCast]
  simp_rw [h_pw2]
  -- Prove integrability and continuity of the integrand
  haveI : IsProbabilityMeasure (haarProbUnitary d) := haarProbUnitary_isProbability d
  have h_P_cont : Continuous (fun g : unitaryGroup (Fin d) ℂ =>
      (coherentStateDensityOp g k).toOp) :=
    continuous_matrix (fun a b => coherentStateDensityOp_entry_continuous a b)
  have h_V_entry : ∀ (i : Fin (d ^ k * d ^ (n - k))) (a' : Fin (d ^ k)),
      Continuous (fun g : unitaryGroup (Fin d) ℂ =>
        ckmrKetEmbed k _hk g i a') := by
    intro i a'; simp only [ckmrKetEmbed, Matrix.of_apply]
    split_ifs
    · exact continuous_const
    · apply continuous_finsetProd; intro j _; exact continuous_subtype_val.matrix_elem _ _
    · exact continuous_const
  have h_A_cont : Continuous (fun g : unitaryGroup (Fin d) ℂ => ckmrUnnorm Ψ k _hk g) := by
    apply continuous_matrix; intro a b
    simp only [ckmrUnnorm, Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply continuous_finsetSum; intro j _
    apply Continuous.mul
    · apply continuous_finsetSum; intro i _; exact (h_V_entry i a).star.mul continuous_const
    · exact h_V_entry j b
  have h_int : Integrable (fun g => (↑((n - k + d - 1).choose (d - 1)) : ℝ) •
      ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g)) (haarProbUnitary d) :=
    (continuous_const.smul (h_P_cont.mul h_A_cont)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_conjTranspose h_int, ckmr_schur_identity_2 Ψ _hsym k _hk]
  -- RHS: (f • ρ_k)^† = f • ρ_k (since ρ_k is Hermitian and f is real)
  rw [Matrix.conjTranspose_smul, star_trivial]
  congr 1
  exact (posSemidefOp_implies_mathlib
    (InfoTheory.DeFinetti.partialTraceToFirstK k _hk Ψ).toPosSemidefOp).isHermitian.eq

/-- Rank-1 sandwich: |ψ⟩⟨ψ| · A · |ψ⟩⟨ψ| = Tr(|ψ⟩⟨ψ| · A) • |ψ⟩⟨ψ|.
    Entry-wise: (PAP)(i,j) = Tr(PA) · P(i,j). -/
private lemma fromPure_sandwich {m : ℕ} (ψ : Ket m) (hψ : ψ.dag * ψ = 1) (A : Op m) :
    (DensityOp.fromPure ψ hψ).toOp * A * (DensityOp.fromPure ψ hψ).toOp =
    ((DensityOp.fromPure ψ hψ).toOp * A).trace • (DensityOp.fromPure ψ hψ).toOp := by
  have h_toOp : (DensityOp.fromPure ψ hψ).toOp = ψ * ψ.dag := rfl
  rw [h_toOp]
  ext i j
  simp only [ket_mul_bra_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.trace,
    Matrix.diag, smul_eq_mul, Ket.dag_vec]
  rw [Finset.sum_mul]
  congr 1; ext x
  rw [Finset.sum_mul, Finset.sum_mul]
  congr 1; ext x₁
  ring

/-- Trace of the partial trace equals the total trace (for the bipartite cast). -/
private lemma trace_partialTraceB_eq {n m : ℕ} (A : Op (n * m)) :
    (partialTraceB A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTraceB, Matrix.of_apply]
  -- Goal: ∑ x, ∑ k, A(fPE(x,k))(fPE(x,k)) = ∑ i, A i i
  rw [show (∑ x : Fin n, ∑ k : Fin m,
      A (finProdFinEquiv (x, k)) (finProdFinEquiv (x, k))) =
    ∑ i : Fin (n * m), A i i from by
    conv_rhs =>
      arg 2; ext i
      rw [show i = finProdFinEquiv (finProdFinEquiv.symm i) from
        (finProdFinEquiv.apply_symm_apply i).symm]
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    simp [Equiv.symm_apply_apply]]

/-- Trace of castDim equals trace of original. -/
private lemma trace_castDim {n m : ℕ} (h : n = m) (A : Op n) :
    (Op.castDim h A).trace = A.trace := by
  subst h; rfl

/-- Trace of (Pg_k * unnorm) equals trace of (Pg_n * Ψ).
    Follows from coherent_mul_unnorm_as_partialTrace + trace preservation. -/
private lemma trace_coherent_unnorm_eq {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n)) (k : ℕ) [NeZero k] (hk : k ≤ n)
    (g : unitaryGroup (Fin d) ℂ) :
    ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k hk g).trace =
    ((coherentStateDensityOp g n).toOp * Ψ.toOp).trace := by
  rw [coherent_mul_unnorm_as_partialTrace Ψ k hk g]
  rw [trace_partialTraceB_eq]
  simp only [densityOp_castDim_toOp]
  rw [Op.castDim_mul, trace_castDim]

/-- The trace of Pg * Ψ is real (both Hermitian PSD). -/
private lemma trace_coherent_mul_real {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n)) (g : unitaryGroup (Fin d) ℂ) :
    ((coherentStateDensityOp g n).toOp * Ψ.toOp).trace =
    ↑((coherentStateDensityOp g n).toOp * Ψ.toOp).trace.re := by
  -- Tr(P*Ψ) is real because star(Tr(P*Ψ)) = Tr((P*Ψ)†) = Tr(Ψ†*P†) = Tr(Ψ*P) = Tr(P*Ψ)
  have hP := (posSemidefOp_implies_mathlib (coherentStateDensityOp g n).toPosSemidefOp).isHermitian
  have hΨ := (posSemidefOp_implies_mathlib Ψ.toPosSemidefOp).isHermitian
  have h_conj : star ((coherentStateDensityOp g n).toOp * Ψ.toOp).trace =
      ((coherentStateDensityOp g n).toOp * Ψ.toOp).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hΨ.eq, hP.eq,
      Matrix.trace_mul_comm]
  exact (Complex.conj_eq_iff_re.mp h_conj).symm

/-- Schur Identity 3: ∫ dim_{n-k} · P_g · unnorm(g) · P_g dg = f · σ_k.
    Follows from weight factorization: P_g · unnorm · P_g = ⟨v|unnorm|v⟩ · P_g. -/
lemma ckmr_schur_identity_3 {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n))
    (_hsym : symmetricProjector d n * Ψ.toOp * symmetricProjector d n = Ψ.toOp)
    (k : ℕ) [NeZero k] (_hk : k ≤ n) :
    ∫ g : unitaryGroup (Fin d) ℂ,
      (↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) •
        ((coherentStateDensityOp g k).toOp * ckmrUnnorm Ψ k _hk g *
         (coherentStateDensityOp g k).toOp)
      ∂(haarProbUnitary d) =
    ((↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) /
      ↑(Nat.choose (n + d - 1) (d - 1))) •
    ∫ g : unitaryGroup (Fin d) ℂ,
      postMeasurementWeight Ψ g • (coherentStateDensityOp g k).toOp
      ∂(haarProbUnitary d) := by
  -- Step 1: Pointwise rewrite of integrand using rank-1 sandwich + trace connection
  have h_pw : ∀ u : unitaryGroup (Fin d) ℂ,
      (↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) •
        ((coherentStateDensityOp u k).toOp * ckmrUnnorm Ψ k _hk u *
         (coherentStateDensityOp u k).toOp) =
      ((↑(Nat.choose (n - k + d - 1) (d - 1)) : ℝ) /
        ↑(Nat.choose (n + d - 1) (d - 1))) •
      (postMeasurementWeight Ψ u • (coherentStateDensityOp u k).toOp) := by
    intro u
    -- Rank-1 sandwich: Pg * A * Pg = Tr(Pg * A) • Pg
    rw [show (coherentStateDensityOp u k).toOp =
      (DensityOp.fromPure (coherentStateKet u k) (coherentStateKet_normalized u k)).toOp from rfl]
    rw [fromPure_sandwich (coherentStateKet u k) (coherentStateKet_normalized u k)
        (ckmrUnnorm Ψ k _hk u)]
    rw [show (DensityOp.fromPure (coherentStateKet u k) (coherentStateKet_normalized u k)).toOp =
      (coherentStateDensityOp u k).toOp from rfl]
    rw [trace_coherent_unnorm_eq Ψ k _hk u]
    -- Trace is real
    rw [trace_coherent_mul_real Ψ u]
    -- Connect to postMeasurementWeight and simplify scalars
    simp only [postMeasurementWeight]
    -- Convert ↑(trace.re) • Pg (ℂ smul) to trace.re • Pg (ℝ smul)
    rw [Complex.coe_smul]
    -- Now both sides use ℝ • Op
    rw [smul_smul, smul_smul]
    congr 1
    have h_dim_pos : (0 : ℝ) < ↑((n + d - 1).choose (d - 1)) := by
      exact_mod_cast Nat.choose_pos (by omega)
    field_simp
  simp_rw [h_pw]
  rw [MeasureTheory.integral_smul]

end InfoTheory.DeFinetti.PureState
