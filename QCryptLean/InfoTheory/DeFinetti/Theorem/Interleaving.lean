import QCryptLean.InfoTheory.DeFinetti.Purification
import QCryptLean.InfoTheory.DeFinetti.PureState.CKMRBound.Bound.Main

/-!
# Interleaving Equivalence — index combinatorics, conjugation, partial trace commutativity

The interleaving equivalence W : Fin(d^n × d^n) ≃ Fin((d·d)^n) maps concatenated
tensor indices (a₁,...,aₙ, b₁,...,bₙ) to interleaved paired indices
((a₁,b₁),...,(aₙ,bₙ)). This file proves:

1. W conjugates the paired permutation action to the standard one
2. W conjugates the paired symmetric projector to the standard one
3. Partial traces commute with interleaving
4. Various supporting combinatorial lemmas (mixed-radix digits, tensor power factorization)

These are the combinatorial ingredients for the quantum de Finetti theorem
(CKMR 2007, Theorem II.7), proved in the companion `Main.lean` file.

## Main definitions
- `interleavingEquiv`: the interleaving bijection W
- `reindexInterleave`: reindex a DensityOp via W

## Main statements
- `interleavingEquiv_conjugates_perm`: W conjugates paired permutations to standard ones
- `interleavingEquiv_conjugates_projector`: W conjugates paired symmetric projector
- `deFinetti_paired`: de Finetti bound for paired symmetric states
- `partialTraceB_tensorPow_eq`: partial trace distributes through tensor powers
- `partialTraces_commute_interleave`: partial traces commute with interleaving
- `reindex_preserves_traceDistance`: reindexing preserves trace distance
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Symmetry MeasureTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.DeFinetti
/-!
### Interleaving and paired-symmetry lemmas

This namespace collects the index combinatorics and reindexing facts used to
move between paired tensor products and a single tensor power of local dimension `d * d`.
-/

/-- The interleaving equivalence between concatenated and interleaved tensor indices.

    Maps (a₁,...,aₙ, b₁,...,bₙ) ∈ Fin(d^n × d^n) to ((a₁,b₁),...,(aₙ,bₙ)) ∈ Fin((d·d)^n).

    Concretely: given flat index i ∈ Fin(d^n * d^n) decomposed as (a, b) via finProdFinEquiv,
    decompose a and b into digit tuples (a₁,...,aₙ) and (b₁,...,bₙ) via finFunctionFinEquiv,
    pair them as (finProdFinEquiv(aⱼ, bⱼ))ⱼ, and recompose via finFunctionFinEquiv for d*d.

    This is the isomorphism W from the CKMR proof (Theorem II.7) that conjugates
    the paired permutation action to the standard tensor permutation action. -/
noncomputable def interleavingEquiv (d n : ℕ) :
    Fin (d ^ n * d ^ n) ≃ Fin ((d * d) ^ n) where
  toFun := fun i =>
    let ab := finProdFinEquiv.symm i
    let ta := finFunctionFinEquiv.symm ab.1
    let tb := finFunctionFinEquiv.symm ab.2
    finFunctionFinEquiv (fun j => finProdFinEquiv (ta j, tb j))
  invFun := fun i =>
    let t := finFunctionFinEquiv.symm i
    let pairs := fun j => finProdFinEquiv.symm (t j)
    finProdFinEquiv (finFunctionFinEquiv (fun j => (pairs j).1),
                     finFunctionFinEquiv (fun j => (pairs j).2))
  left_inv := fun i => by
    dsimp only []
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Prod.mk.eta]
  right_inv := fun i => by
    dsimp only []
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Prod.mk.eta]

/-- Reindex a DensityOp from the concatenated encoding (d^n * d^n) to the interleaved
    encoding ((d*d)^n) via the interleaving equivalence.

    It applies the interleaving permutation to both row and column indices, which is
    equivalent to the unitary conjugation Ψ' = W * Ψ * W† where W is the interleaving
    permutation matrix. -/
noncomputable def reindexInterleave {d n : ℕ}
    (Ψ : DensityOp (d ^ n * d ^ n)) : DensityOp ((d * d) ^ n) :=
  densityOp_reindex (interleavingEquiv d n) Ψ

private lemma finProdFinEquiv_divNat {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).divNat = a := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv (a, b))
  rw [Equiv.symm_apply_apply] at h
  exact (congr_arg Prod.fst h).symm

private lemma finProdFinEquiv_modNat {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).modNat = b := by
  have h := finProdFinEquiv_symm_apply (finProdFinEquiv (a, b))
  rw [Equiv.symm_apply_apply] at h
  exact (congr_arg Prod.snd h).symm

lemma interleavingEquiv_digit_fst {d n : ℕ} [NeZero d]
    (a : Fin ((d * d) ^ n)) (k : Fin n) :
    (@finFunctionFinEquiv d n).symm
        ((interleavingEquiv d n).symm a).divNat k =
      (finProdFinEquiv.symm
        ((@finFunctionFinEquiv (d * d) n).symm a k)).1 := by
  simp only [interleavingEquiv]
  dsimp
  rw [finProdFinEquiv_divNat, Equiv.symm_apply_apply]

lemma interleavingEquiv_digit_snd {d n : ℕ} [NeZero d]
    (a : Fin ((d * d) ^ n)) (k : Fin n) :
    (@finFunctionFinEquiv d n).symm
        ((interleavingEquiv d n).symm a).modNat k =
      (finProdFinEquiv.symm
        ((@finFunctionFinEquiv (d * d) n).symm a k)).2 := by
  simp only [interleavingEquiv]
  dsimp
  rw [finProdFinEquiv_modNat, Equiv.symm_apply_apply]

private lemma interleavingEquiv_perm_condition_iff {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n)) (i j : Fin ((d * d) ^ n)) :
    let tie_d := @finFunctionFinEquiv d n
    let tie_dd := @finFunctionFinEquiv (d * d) n
    (tie_dd.symm i = tie_dd.symm j ∘ ⇑(Equiv.symm σ)) ↔
      (tie_d.symm ((interleavingEquiv d n).symm i).divNat =
        tie_d.symm ((interleavingEquiv d n).symm j).divNat
          ∘ ⇑(Equiv.symm σ) ∧
       tie_d.symm ((interleavingEquiv d n).symm i).modNat =
        tie_d.symm ((interleavingEquiv d n).symm j).modNat
          ∘ ⇑(Equiv.symm σ)) := by
  dsimp
  constructor
  · intro h
    refine ⟨funext fun k => ?_, funext fun k => ?_⟩
    · rw [interleavingEquiv_digit_fst, Function.comp_apply, interleavingEquiv_digit_fst]
      exact congr_arg (fun x => (finProdFinEquiv.symm x).1) (congr_fun h k)
    · rw [interleavingEquiv_digit_snd, Function.comp_apply, interleavingEquiv_digit_snd]
      exact congr_arg (fun x => (finProdFinEquiv.symm x).2) (congr_fun h k)
  · intro ⟨h1, h2⟩
    funext k
    have hk1 := congr_fun h1 k
    have hk2 := congr_fun h2 k
    rw [interleavingEquiv_digit_fst, Function.comp_apply, interleavingEquiv_digit_fst] at hk1
    rw [interleavingEquiv_digit_snd, Function.comp_apply, interleavingEquiv_digit_snd] at hk2
    exact (Equiv.injective finProdFinEquiv.symm) (Prod.ext hk1 hk2)

/-- The interleaving equivalence conjugates the paired permutation action to the
    standard tensor permutation action:
      reindex(W)(U_σ ⊗ U_σ) = permutationRepresentation (d*d) n σ

    This is because W maps the simultaneous permutation of (a₁,...,aₙ) and (b₁,...,bₙ)
    to the permutation of paired indices ((a₁,b₁),...,(aₙ,bₙ)), which is exactly
    the standard permutation representation on (ℂ^{d²})^⊗n. -/
lemma interleavingEquiv_conjugates_perm {d n : ℕ} [NeZero d]
    (σ : Equiv.Perm (Fin n)) :
    let e := interleavingEquiv d n
    Matrix.reindex e e (Op.tensor
      (Math.RepresentationTheory.permutationRepresentation d n σ)
      (Math.RepresentationTheory.permutationRepresentation d n σ)) =
    Math.RepresentationTheory.permutationRepresentation (d * d) n σ := by
  intro e
  ext i j
  simp only [Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Math.RepresentationTheory.permutationRepresentation, Matrix.of_apply]
  have cond_iff :
      (@finFunctionFinEquiv (d * d) n).symm i =
          (@finFunctionFinEquiv (d * d) n).symm j
            ∘ ⇑(Equiv.symm σ) ↔
        ((@finFunctionFinEquiv d n).symm
            (finProdFinEquiv.symm (e.symm i)).1 =
          (@finFunctionFinEquiv d n).symm
            (finProdFinEquiv.symm (e.symm j)).1 ∘ ⇑(Equiv.symm σ) ∧
         (@finFunctionFinEquiv d n).symm
            (finProdFinEquiv.symm (e.symm i)).2 =
         (@finFunctionFinEquiv d n).symm
            (finProdFinEquiv.symm (e.symm j)).2 ∘ ⇑(Equiv.symm σ)) := by
    simpa [e] using interleavingEquiv_perm_condition_iff (d := d) σ i j
  split_ifs with h1 h2 h3 h3 h3 h3 <;>
    simp_all [mul_one, mul_zero]

/-- The interleaving conjugates the paired symmetric projector to the standard one:
      reindex(W)(P_paired) = P_standard

    Follows from interleavingEquiv_conjugates_perm by averaging over σ. -/
lemma interleavingEquiv_conjugates_projector {d n : ℕ} [NeZero d] [NeZero n] :
    Matrix.reindex (interleavingEquiv d n) (interleavingEquiv d n)
      (symmetricProjectorPaired d n) = symmetricProjector (d * d) n := by
  unfold symmetricProjectorPaired
  simp only [symmetricProjector, Math.RepresentationTheory.symmetricProjectorRep]
  set e := interleavingEquiv d n
  have h_smul : ∀ (c : ℂ) (M : Op (d ^ n * d ^ n)),
      Matrix.reindex e e (c • M) = c • Matrix.reindex e e M := by
    intro c M; ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  have h_sum : ∀ (f : Equiv.Perm (Fin n) → Op (d ^ n * d ^ n)),
      Matrix.reindex e e (∑ σ : Equiv.Perm (Fin n), f σ) =
        ∑ σ : Equiv.Perm (Fin n), Matrix.reindex e e (f σ) := by
    intro f; ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [h_smul, h_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact interleavingEquiv_conjugates_perm σ

/-- The trace of the paired symmetric projector equals the symmetric-subspace
    dimension for local dimension `d * d`. -/
lemma symmetricProjectorPaired_trace {d n : ℕ} [NeZero d] [NeZero n] :
    (symmetricProjectorPaired d n).trace =
      (Nat.choose (n + (d * d - 1)) (d * d - 1) : ℂ) := by
  have h_trace_eq : (symmetricProjectorPaired d n).trace =
      (Matrix.reindex (interleavingEquiv d n) (interleavingEquiv d n)
        (symmetricProjectorPaired d n)).trace := by
    have := Matrix.trace_map
      (Matrix.reindexAlgEquiv ℂ ℂ (interleavingEquiv d n))
      (symmetricProjectorPaired d n)
    simp only [Matrix.reindexAlgEquiv_apply] at this
    exact this.symm
  rw [h_trace_eq, interleavingEquiv_conjugates_projector, symmetricProjector_trace]
  have hd : 1 ≤ d * d := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (NeZero.pos d) (NeZero.pos d))
  simp [Nat.add_sub_assoc hd]

/-- The partial trace of the paired symmetric projector is the weighted
    permutation average induced by tracing out the second copy. -/
lemma partialTraceB_symmetricProjectorPaired_eq_weighted_sum {d n : ℕ}
    [NeZero d] [NeZero n] :
    partialTraceB (symmetricProjectorPaired d n) =
      (1 / (Nat.factorial n : ℂ)) •
        ∑ σ : Equiv.Perm (Fin n),
          (Math.RepresentationTheory.permutationRepresentation d n σ).trace •
            Math.RepresentationTheory.permutationRepresentation d n σ := by
  unfold symmetricProjectorPaired
  rw [partialTraceB_smul, partialTraceB_finset_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simpa using partialTraceB_tensor_op
    (Math.RepresentationTheory.permutationRepresentation d n σ)
    (Math.RepresentationTheory.permutationRepresentation d n σ)

/-- **De Finetti for paired symmetric states.**

    If Ψ is a density operator supported in the paired symmetric subspace of
    `(ℂᵈ)^⊗n ⊗ (ℂᵈ)^⊗n`, then there exists ONE measure ν over
    `(d*d)`-dimensional density operators such that for every `k`
    with `1 ≤ k ≤ n`, the `k`-copy reduced state is within `2k(d*d)/n`
    of the de Finetti mixture `∫ σ^⊗k dν(σ)`.

    The ∀ k quantifier is essential: it prevents the Dirac-measure trick
    (which works for `k = 1` but fails for `k ≥ 2` since
    `ρ_k ≠ ρ₁^⊗k` in general).

    The hypothesis is paired-symmetric support of an arbitrary density operator,
    not a pure state. -/
lemma deFinetti_paired {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n * d ^ n))
    (_hsym : symmetricProjectorPaired d n * Ψ.toOp *
      symmetricProjectorPaired d n = Ψ.toOp) :
    ∃ ν : DensityMeasure (d * d),
      ∀ (k : ℕ) [NeZero k] (hk : k ≤ n),
        traceDistance
          (partialTraceToFirstK k hk (reindexInterleave Ψ)).toOp
          (integralTensorPower k ν).toOp ≤
            2 * k * ((d * d : ℕ) : ℝ) / n := by
  let Ψ' := reindexInterleave Ψ
  have hsym' : symmetricProjector (d * d) n * Ψ'.toOp *
      symmetricProjector (d * d) n = Ψ'.toOp := by
    set e := interleavingEquiv d n
    have hsym_reindexed := congrArg (Matrix.reindexAlgEquiv ℂ ℂ e) _hsym
    simp only [Matrix.reindexAlgEquiv_apply, map_mul] at hsym_reindexed
    rw [interleavingEquiv_conjugates_projector] at hsym_reindexed
    simpa [Ψ', reindexInterleave, densityOp_reindex] using hsym_reindexed
  obtain ⟨ν, hν⟩ := InfoTheory.DeFinetti.PureState.pure_state_deFinetti_symmetric (d * d) n Ψ' hsym'
  refine ⟨ν, fun k _ hk => ?_⟩
  have h :
      traceDistance
          (partialTraceToFirstK k hk (reindexInterleave Ψ)).toOp
          (integralTensorPower k ν).toOp ≤
        2 * ↑(d * d) * ↑k / ↑n := by
    simpa [Ψ'] using hν k hk
  calc traceDistance _ _ ≤ 2 * ↑(d * d) * ↑k / ↑n := h
    _ = 2 * ↑k * ↑(d * d) / ↑n := by ring

-- Trace norm contraction lemmas are in InfoTheory.DistanceBounds.TraceNormContraction.lean

/-- Reindexing by an equivalence preserves trace distance. This holds because
    permutation similarity preserves eigenvalues, hence the trace norm. -/
lemma reindex_preserves_traceDistance {m n : ℕ} [NeZero m]
    (e : Fin m ≃ Fin n) (A B : DensityOp m) :
    let _ : NeZero n := ⟨by
      intro hn
      have hcard : m = n := by simpa using Fintype.card_congr e
      exact NeZero.ne m (hcard.trans hn)⟩
    traceDistance (densityOp_reindex e A).toOp (densityOp_reindex e B).toOp =
    traceDistance A.toOp B.toOp := by
  letI : NeZero n := ⟨by
    intro hn
    have hcard : m = n := by simpa using Fintype.card_congr e
    exact NeZero.ne m (hcard.trans hn)⟩
  dsimp
  -- Since Fin m ≃ Fin n, m = n
  have hmn : m = n := Fin.equiv_iff_eq.mp ⟨e⟩
  subst hmn
  -- Now e : Fin m ≃ Fin m, all in dimension m
  -- Both sides reduce via bridge lemma to traceNormHermitian
  rw [traceDistance_densityOp_eq_traceNormHermitian (densityOp_reindex e A) (densityOp_reindex e B),
      traceDistance_densityOp_eq_traceNormHermitian A B]
  congr 1
  -- Need: traceNormHermitian of reindexed difference = traceNormHermitian of original
  -- Key: reindexed difference = Matrix.reindex e e (original difference)
  have h_sub : (densityOp_reindex e A).toOp - (densityOp_reindex e B).toOp =
      Matrix.reindex e e (A.toOp - B.toOp) := by
    ext i j
    simp only [densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.sub_apply]
  -- Eigenvalues are preserved because charpoly is preserved
  unfold traceNormHermitian
  set hH1 := densityOp_sub_isHermitian (densityOp_reindex e A) (densityOp_reindex e B)
  set hH2 := densityOp_sub_isHermitian A B
  -- Show eigenvalues match via charpoly equality
  have h_eig : hH1.eigenvalues = hH2.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    calc ((densityOp_reindex e A).toOp - (densityOp_reindex e B).toOp).charpoly
        = (Matrix.reindex e e (A.toOp - B.toOp)).charpoly := by rw [h_sub]
      _ = (A.toOp - B.toOp).charpoly := Matrix.charpoly_reindex e _
  simp_rw [h_eig]

/-- The interleaving equivalence maps concatenated encoded pairs to interleaved
    encoded pairs: ie(fpfe(fpfe(α), fpfe(γ))) = fpfe_{d²}(fun l => fpfe(α l, γ l)). -/
private lemma interleavingEquiv_finFunctionFinEquiv_pair {d k : ℕ} [NeZero d]
    (α γ : Fin k → Fin d) :
    interleavingEquiv d k
      (finProdFinEquiv
        (@finFunctionFinEquiv d k α,
         @finFunctionFinEquiv d k γ)) =
    @finFunctionFinEquiv (d * d) k
      (fun l => finProdFinEquiv (α l, γ l)) := by
  unfold interleavingEquiv
  dsimp only [Equiv.coe_fn_mk]
  congr 1; funext l
  simp [Equiv.symm_apply_apply]

/-- Partial trace distributes through tensor powers with correct interleaving:
    (Tr_B τ)^⊗k = Tr_B(deinterleave(τ^⊗k)).
    Entry-wise: ∏_l (∑_c τ_{(a_l,c),(b_l,c)}) = ∑_{c₁..cₖ} ∏_l τ_{(a_l,c_l),(b_l,c_l)}
    by Fintype.prod_sum (product of sums = sum of products over all choices). -/
lemma partialTraceB_tensorPow_eq {d k : ℕ} [NeZero d]
    (τ : DensityOp (d * d)) :
    τ.partialTraceB.tensorPowGen k =
    (densityOp_reindex (interleavingEquiv d k).symm
      (τ.tensorPowGen k)).partialTraceB := by
  haveI : NeZero (d * d) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d)⟩
  haveI : NeZero (d ^ k) := ⟨pow_ne_zero _ (NeZero.ne d)⟩
  haveI : NeZero ((d * d) ^ k) := ⟨pow_ne_zero _ (NeZero.ne (d * d))⟩
  apply DensityOp.ext; ext i j
  -- Setup: decode i,j as digit tuples α,β
  set tie_d := @finFunctionFinEquiv d k
  set α := tie_d.symm i
  set β := tie_d.symm j
  have hi : tie_d α = i := tie_d.apply_symm_apply i
  have hj : tie_d β = j := tie_d.apply_symm_apply j
  -- Both sides equal ∑ γ, ∏ l, τ(fpfe(α l, γ l), fpfe(β l, γ l))
  -- LHS: by tensorPowGen_toOp_eq_prod + partialTraceB defn + Fintype.prod_sum
  have h_lhs : (τ.partialTraceB.tensorPowGen k).toOp i j =
      ∑ γ : Fin k → Fin d, ∏ l : Fin k,
        τ.toOp (finProdFinEquiv (α l, γ l))
          (finProdFinEquiv (β l, γ l)) := by
    rw [← hi, ← hj, tensorPowGen_toOp_eq_prod]
    exact Fintype.prod_sum
      (fun l c => τ.toOp (finProdFinEquiv (α l, c))
        (finProdFinEquiv (β l, c)))
  -- RHS: unfold partialTraceB + reindex, reindex sum, index identity
  have h_rhs :
      (densityOp_reindex (interleavingEquiv d k).symm
        (τ.tensorPowGen k)).partialTraceB.toOp i j =
      ∑ γ : Fin k → Fin d, ∏ l : Fin k,
        τ.toOp (finProdFinEquiv (α l, γ l))
          (finProdFinEquiv (β l, γ l)) := by
    -- Unfold partialTraceB + reindex
    simp only [DensityOp.partialTraceB, PosSemidefOp.partialTraceB,
        partialTraceB, Matrix.of, densityOp_reindex,
        Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm]
    -- Remove Equiv.refl wrapper
    change ∑ c', (τ.tensorPowGen k).toOp
        ((interleavingEquiv d k) (finProdFinEquiv (i, c')))
        ((interleavingEquiv d k) (finProdFinEquiv (j, c')))
      = _
    rw [← hi, ← hj]
    -- Reindex sum from Fin(d^k) to (Fin k → Fin d) and rewrite summands
    exact Fintype.sum_equiv tie_d.symm _ _ (fun c' => by
      conv_lhs =>
        rw [show c' = tie_d (tie_d.symm c') from
            (tie_d.apply_symm_apply c').symm]
      rw [interleavingEquiv_finFunctionFinEquiv_pair α (tie_d.symm c'),
          interleavingEquiv_finFunctionFinEquiv_pair β (tie_d.symm c'),
          tensorPowGen_toOp_eq_prod])
  rw [h_lhs, h_rhs]

/-- For `j < m`, the j-th base-d digit of `A + d^m * B` equals that of `A`. -/
private lemma mixed_radix_digit_low (A B d m j : ℕ) (hj : j < m)
    (hd : 0 < d) :
    (A + d ^ m * B) / d ^ j % d = A / d ^ j % d := by
  have hdj : 0 < d ^ j := Nat.pos_of_ne_zero (pow_ne_zero j (by omega))
  rw [show d ^ m = d ^ j * d ^ (m - j) from by rw [← pow_add]; congr 1; omega,
      show A + d ^ j * d ^ (m - j) * B = A + d ^ j * (d ^ (m - j) * B) from by ring,
      Nat.add_mul_div_left _ _ hdj]
  -- Goal: (A / d^j + d^(m-j) * B) % d = A / d^j % d
  -- d | d^(m-j) since m-j ≥ 1, so d^(m-j)*B = d * (d^(m-j)/d * B)
  obtain ⟨q, hq⟩ := dvd_pow_self d (show m - j ≠ 0 by omega)
  rw [hq, show d * q * B = d * (q * B) from by ring, Nat.add_mul_mod_self_left]

/-- For `A < d^m`, the (m+j)-th base-d digit of `A + d^m * B` equals the j-th digit of `B`. -/
private lemma mixed_radix_digit_high (A B d m j : ℕ) (hA : A < d ^ m) (hd : 0 < d) :
    (A + d ^ m * B) / d ^ (m + j) % d = B / d ^ j % d := by
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  have hdm : 0 < d ^ m := Nat.pos_of_ne_zero (pow_ne_zero m (by omega))
  rw [Nat.add_mul_div_left _ _ hdm, Nat.div_eq_of_lt hA, Nat.zero_add]

/-- Interleaving commutes with index concatenation: interleaving the concatenation
    of (a,c) and (b,e) equals the concatenation of interleaving (a,b) and (c,e).
    At the digit level, this is the identity
    (a₁γ₁)(a₂γ₂)…(aₙγₙ) = (a₁γ₁)…(aₖγₖ)(aₖ₊₁γₖ₊₁)…(aₙγₙ)
    when the left side interleaves two n-digit concatenated sequences and
    the right side concatenates two separately interleaved subsequences. -/
private lemma interleavingEquiv_comm_concat {d n k : ℕ} [NeZero d]
    (hk : k ≤ n)
    (a b : Fin (d ^ k)) (c e : Fin (d ^ (n - k))) :
    (interleavingEquiv d n)
      (finProdFinEquiv (Fin.cast (pow_eq_mul_pow_sub hk).symm (finProdFinEquiv (a, c)),
                         Fin.cast (pow_eq_mul_pow_sub hk).symm (finProdFinEquiv (b, e)))) =
    Fin.cast (pow_eq_mul_pow_sub (d := d * d) hk).symm
      (finProdFinEquiv ((interleavingEquiv d k) (finProdFinEquiv (a, b)),
                         (interleavingEquiv d (n - k)) (finProdFinEquiv (c, e)))) := by
  -- Convert a, b, c, e to digit functions
  -- Both sides are Fin((d*d)^n) values. Prove val-equality.
  apply Fin.ext
  simp only [Fin.val_cast]
  -- Unfold all interleavingEquiv (both outer and inner) to their definitions
  simp only [interleavingEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  -- Now both sides: tie_{d²} applied to pointwise fpfe of digit decompositions
  -- Expand to value sums
  simp only [finFunctionFinEquiv_apply_val, finProdFinEquiv_apply_val,
    finFunctionFinEquiv_symm_apply_val, Fin.val_cast]
  -- Goal is a purely arithmetic identity about mixed-radix digits.
  -- Split ∑_{Fin n} into ∑_{Fin(n-k)} + ∑_{Fin k} via Fin.sum_univ_add.
  have hn : (n - k) + k = n := Nat.sub_add_cancel hk
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have he_bound : ↑e < d ^ (n - k) := e.isLt
  have hc_bound : ↑c < d ^ (n - k) := c.isLt
  -- Reindex LHS sum from Fin n to Fin((n-k)+k)
  conv_lhs => rw [← Equiv.sum_comp (finCongr hn)]
  simp only [finCongr_apply, Fin.val_cast]
  -- Split into low and high index sums
  rw [Fin.sum_univ_add]
  congr 1
  · -- Low part: indices 0..n-k-1, castAdd preserves val
    apply Finset.sum_congr rfl; intro x _
    simp only [Fin.val_castAdd]
    -- Apply mixed_radix_digit_low to simplify both digit extractions
    rw [mixed_radix_digit_low ↑e ↑b d (n - k) ↑x x.isLt hd,
        mixed_radix_digit_low ↑c ↑a d (n - k) ↑x x.isLt hd]
  · -- High part: indices n-k..n-1, natAdd shifts by (n-k)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    simp only [Fin.val_natAdd]
    rw [mixed_radix_digit_high ↑e ↑b d (n - k) ↑x he_bound hd,
        mixed_radix_digit_high ↑c ↑a d (n - k) ↑x hc_bound hd,
        pow_add]
    ring

/-- Partial traces commute with interleaving: tracing B then copies k+1..n equals
    interleaving, tracing copies k+1..n, deinterleaving, then tracing B.

    Both paths compute ∑_{a_{k+1}..aₙ, b₁..bₙ} Ψ[(a,b),(a',b')] with a₁..aₖ free.
    The proof is by ext to matrix entries and a change of summation variables:
    the bijection maps (c : Fin(d^(n-k)), b : Fin(d^n)) on the LHS to
    (e : Fin(d^k), c' : Fin((d*d)^(n-k))) on the RHS, where b splits as (b₁,b₂)
    with e = b₁ and c' encodes the interleaving of (c, b₂). -/
lemma partialTraces_commute_interleave {d n : ℕ} [NeZero d] [NeZero n]
    (Ψ : DensityOp (d ^ n * d ^ n))
    (k : ℕ) [NeZero k]
    (hk : k ≤ n) :
    partialTraceToFirstK k hk Ψ.partialTraceB =
      (densityOp_reindex (interleavingEquiv d k).symm
        (partialTraceToFirstK k hk (reindexInterleave Ψ))).partialTraceB := by
  haveI : NeZero (d * d) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d)⟩
  haveI : NeZero (d ^ n) := ⟨pow_ne_zero _ (NeZero.ne d)⟩
  haveI : NeZero ((d * d) ^ n) := ⟨pow_ne_zero _ (NeZero.ne (d * d))⟩
  haveI : NeZero (d ^ k) := ⟨pow_ne_zero _ (NeZero.ne d)⟩
  haveI : NeZero ((d * d) ^ k) := ⟨pow_ne_zero _ (NeZero.ne (d * d))⟩
  -- Both sides compute the same sum over entries of Ψ.toOp.
  -- The proof goes through digit decomposition and a change of summation variables.
  haveI : NeZero (d ^ (n - k)) := ⟨pow_ne_zero _ (NeZero.ne d)⟩
  haveI : NeZero ((d * d) ^ (n - k)) := ⟨pow_ne_zero _ (NeZero.ne (d * d))⟩
  haveI : NeZero (d ^ (n - k) * d ^ (n - k)) :=
    ⟨Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne (d ^ (n - k))))
      (Nat.pos_of_ne_zero (NeZero.ne (d ^ (n - k)))) |>.ne'⟩
  apply DensityOp.ext; ext i j
  -- Unfold both sides to sums over Ψ.toOp entries
  unfold partialTraceToFirstK
  simp only [DensityOp.partialTraceB, PosSemidefOp.partialTraceB,
    partialTraceB, Matrix.of_apply]
  -- Apply `castDim_toOp_cast` to unfold `castDim` on the left-hand side.
  -- LHS = ∑_c ∑_b Ψ(fpfe(cast(fpfe(i,c)), b), fpfe(cast(fpfe(j,c)), b))
  -- RHS = ∑_e (reindex(ptB(castDim(reindexInterleave Ψ)))).toOp (fpfe(i,e)) (fpfe(j,e))
  -- which unfolds to:
  -- ∑_e ∑_{c'} Ψ(ie_n.symm(cast(fpfe(ie_k(fpfe(i,e)), c'))),
  --               ie_n.symm(cast(fpfe(ie_k(fpfe(j,e)), c'))))
  -- Both sides are sums over Ψ.toOp entries. Prove by showing each entry matches
  -- after reindexing the summation variables.
  -- Helper: entries of reindexInterleave
  have ri_entry : ∀ (p q : Fin ((d * d) ^ n)),
      (reindexInterleave Ψ).toOp p q =
      Ψ.toOp ((interleavingEquiv d n).symm p) ((interleavingEquiv d n).symm q) := by
    intro p q
    simp [reindexInterleave, densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply]
  -- Unfold all castDim to Fin.cast, all densityOp_reindex to Equiv.symm,
  -- all reindexInterleave to ie_n.symm
  simp_rw [castDim_toOp_cast, ri_entry]
  simp only [densityOp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Matrix.of_apply]
  -- Both sides sum Ψ entries with different index parameterization.
  -- The proof constructs a bijection and uses a key index identity.
  have hpms : d ^ n = d ^ k * d ^ (n - k) := pow_eq_mul_pow_sub hk
  have hpmsd : (d * d) ^ n = (d * d) ^ k * (d * d) ^ (n - k) := pow_eq_mul_pow_sub hk
  -- Key identity: interleaving commutes with index concatenation
  have key : ∀ (a b : Fin (d ^ k)) (c e : Fin (d ^ (n - k))),
      (interleavingEquiv d n)
        (finProdFinEquiv (Fin.cast hpms.symm (finProdFinEquiv (a, c)),
                           Fin.cast hpms.symm (finProdFinEquiv (b, e)))) =
      Fin.cast hpmsd.symm
        (finProdFinEquiv ((interleavingEquiv d k) (finProdFinEquiv (a, b)),
                           (interleavingEquiv d (n - k)) (finProdFinEquiv (c, e)))) :=
    fun a b c e => interleavingEquiv_comm_concat hk a b c e
  -- Bijection: (x : Fin(d^(n-k)), k₁ : Fin(d^n)) ↔ (bh : Fin(d^k), x₁ : Fin((d*d)^(n-k)))
  -- via splitting k₁ = (bh, bl) and x₁ = ie_{n-k}(x, bl)
  let bij : Fin (d ^ (n - k)) × Fin (d ^ n) ≃
      Fin (d ^ k) × Fin ((d * d) ^ (n - k)) :=
  { toFun := fun p =>
      let q := finProdFinEquiv.symm (Fin.cast hpms p.2)
      (q.1, (interleavingEquiv d (n - k)) (finProdFinEquiv (p.1, q.2)))
    invFun := fun p =>
      let q := finProdFinEquiv.symm ((interleavingEquiv d (n - k)).symm p.2)
      (q.1, Fin.cast hpms.symm (finProdFinEquiv (p.1, q.2)))
    left_inv := by
      intro ⟨x, k₁⟩
      refine Prod.ext ?_ ?_
      · -- fst: x
        change (finProdFinEquiv.symm ((interleavingEquiv d (n - k)).symm
          ((interleavingEquiv d (n - k))
            (finProdFinEquiv (x, (finProdFinEquiv.symm (Fin.cast hpms k₁)).2))))).1 = x
        simp [Equiv.symm_apply_apply]
      · -- snd: k₁
        change Fin.cast hpms.symm (finProdFinEquiv
          ((finProdFinEquiv.symm (Fin.cast hpms k₁)).1,
           (finProdFinEquiv.symm ((interleavingEquiv d (n - k)).symm
             ((interleavingEquiv d (n - k))
               (finProdFinEquiv (x, (finProdFinEquiv.symm (Fin.cast hpms k₁)).2))))).2)) = k₁
        simp only [Equiv.symm_apply_apply]
        apply Fin.ext
        simp only [finProdFinEquiv_apply_val, finProdFinEquiv_symm_apply,
          Fin.val_cast, Fin.coe_modNat, Fin.coe_divNat]
        exact Nat.mod_add_div k₁.val _
    right_inv := by
      intro ⟨bh, x₁⟩
      simp only [Fin.cast_cast, Fin.cast_refl, id_eq, Equiv.symm_apply_apply,
        Equiv.apply_symm_apply, Prod.mk.eta] }
  -- Combine nested sums into single sums over product types
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  apply Fintype.sum_equiv bij
  intro ⟨x, k₁⟩
  -- Compute bij(x, k₁) explicitly before rewriting k₁
  set bh := (finProdFinEquiv.symm (Fin.cast hpms k₁)).1
  set bl := (finProdFinEquiv.symm (Fin.cast hpms k₁)).2
  -- bij(x, k₁) = (bh, ie(fpfe(x, bl)))
  have hb : bij (x, k₁) = (bh, (interleavingEquiv d (n - k)) (finProdFinEquiv (x, bl))) := rfl
  rw [hb]
  -- Recover k₁ from bh, bl for the LHS
  have hk₁ : k₁ = Fin.cast hpms.symm (finProdFinEquiv (bh, bl)) := by
    apply Fin.ext
    simp only [bh, bl, Fin.val_cast, finProdFinEquiv_apply_val, finProdFinEquiv_symm_apply,
      Fin.coe_modNat, Fin.coe_divNat]
    exact (Nat.mod_add_div k₁.val _).symm
  rw [hk₁]
  -- Use key identity: from ie_n(X) = Y, deduce X = ie_n.symm(Y)
  have aux : ∀ (a : Fin (d ^ k)),
      finProdFinEquiv (Fin.cast hpms.symm (finProdFinEquiv (a, x)),
        Fin.cast hpms.symm (finProdFinEquiv (bh, bl))) =
      (interleavingEquiv d n).symm (Fin.cast hpmsd.symm
        (finProdFinEquiv ((interleavingEquiv d k) (finProdFinEquiv (a, bh)),
          (interleavingEquiv d (n - k)) (finProdFinEquiv (x, bl))))) := by
    intro a
    have h := key a bh x bl
    exact ((interleavingEquiv d n).symm_apply_eq.mpr h.symm).symm
  congr 1
  · exact aux i
  · exact aux j

end InfoTheory.DeFinetti

end
