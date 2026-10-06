import QCryptLean.InfoTheory.Postselection.PairedBlockedTransport
import QCryptLean.Quantum.TensorProducts.ReferenceTransport

/-!
# Local operators under paired-to-blocked regrouping

The marginal transport identity determines the corresponding transport of local
Alice operators by the nondegeneracy of the trace pairing.
-/

open Equiv

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Matrix InfoTheory.DeFinetti
open Math.RepresentationTheory
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

/-- Tensoring with the identity is adjoint to partial trace for the trace pairing. -/
private lemma trace_tensor_one_mul {a b : ℕ} (A : Op a) (X : Op (a * b)) :
    (Op.tensor A (1 : Op b) * X).trace = (A * partialTraceB X).trace := by
  have h := partialTraceB_sandwich_tensor_one A (1 : Op a) X
  simp only [Op.tensor_one, mul_one] at h
  rw [← trace_partialTraceB, h]

/-- Transporting one factor of a trace pairing backwards is equivalent to
transporting the other factor forwards. -/
private lemma trace_reindex_mul {a b : ℕ} (e : Fin a ≃ Fin b) (A : Op a) (B : Op b) :
    (Matrix.reindex e e A * B).trace = (A * Matrix.reindex e.symm e.symm B).trace := by
  rw [← Matrix.trace_reindex_self e, Matrix.reindex_mul, Matrix.reindex_reindex_symm]

/-- An Alice operator on the blocked register acts on Alice in the first paired
copy and as the identity on both remaining registers. -/
lemma pairedToBlockedEquiv_tensor_one (dA dB n : ℕ)
    [NeZero dA] [NeZero dB] [NeZero n] (A : Op (dA ^ n)) :
    Matrix.reindex (pairedToBlockedEquiv dA dB n) (pairedToBlockedEquiv dA dB n)
      (Op.tensor (Matrix.reindex (roundGroupEquiv dA dB n).symm
        (roundGroupEquiv dA dB n).symm (Op.tensor A (1 : Op (dB ^ n))))
        (1 : Op ((dA * dB) ^ n))) =
      Op.tensor A (1 : Op ((dA * dB ^ 2) ^ n)) := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [trace_reindex_mul, trace_tensor_one_mul, trace_reindex_mul, Equiv.symm_symm,
    trace_tensor_one_mul, trace_tensor_one_mul]
  congr 1
  have h := pairedToBlockedEquiv_partialTraceB_eq_roundGroup dA dB n
    (Matrix.reindex (pairedToBlockedEquiv dA dB n).symm
      (pairedToBlockedEquiv dA dB n).symm X)
  rw [Matrix.reindex_reindex_symm] at h
  rw [h]

/-- Conjugation by a unitary on the traced register preserves the partial trace. -/
lemma partialTraceB_one_tensor_unitary_conj {a b : ℕ}
    (V : Op b) (hV : Vᴴ * V = 1) (M : Op (a * b)) :
    partialTraceB (Op.tensor (1 : Op a) V * M * Op.tensor (1 : Op a) Vᴴ) = partialTraceB M := by
  exact partialTraceB_one_tensor_sandwich_of_mul_eq_one V Vᴴ hV M

/-- `partialTraceB` of a sandwich by `A ⊗ V` and `A' ⊗ Vᴴ` with `V` unitary (`Vᴴ * V = 1`):
    the unitary conjugation of the traced register cancels, leaving
    `A * partialTraceB M * A'`. -/
lemma partialTraceB_sandwich_tensor_unitary {a b : ℕ}
    (A A' : Op a) (V : Op b) (hV : Vᴴ * V = 1) (M : Op (a * b)) :
    partialTraceB (Op.tensor A V * M * Op.tensor A' Vᴴ) = A * partialTraceB M * A' := by
  have hA : Op.tensor A V = Op.tensor A (1 : Op b) * Op.tensor (1 : Op a) V := by
    rw [Op.tensor_mul, Matrix.mul_one, Matrix.one_mul]
  have hA' : Op.tensor A' Vᴴ = Op.tensor (1 : Op a) Vᴴ * Op.tensor A' (1 : Op b) := by
    rw [Op.tensor_mul, Matrix.one_mul, Matrix.mul_one]
  have hmid := partialTraceB_one_tensor_unitary_conj V hV M
  calc partialTraceB (Op.tensor A V * M * Op.tensor A' Vᴴ)
      = partialTraceB (Op.tensor A (1 : Op b) *
          (Op.tensor (1 : Op a) V * M * Op.tensor (1 : Op a) Vᴴ) *
          Op.tensor A' (1 : Op b)) := by
        rw [hA, hA']
        simp only [mul_assoc]
    _ = A * partialTraceB (Op.tensor (1 : Op a) V * M * Op.tensor (1 : Op a) Vᴴ) * A' := by
        rw [partialTraceB_sandwich_tensor_one]
    _ = A * partialTraceB M * A' := by rw [hmid]

/-- A reference-side tensor power commutes with simultaneous round symmetrization. -/
lemma tensor_one_tensorPow_commute_symmetricProjectorPairedGen
    {a b n : ℕ} [NeZero a] [NeZero b] [NeZero n] (U : Op b) :
    Commute (Op.tensor (1 : Op (a ^ n)) (Op.tensorPow U n))
      (symmetricProjectorPairedGen a b n) := by
  unfold Commute SemiconjBy symmetricProjectorPairedGen
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [Op.tensor_mul, Op.tensor_mul, one_mul, mul_one,
    (Op.commute_tensorPow_permutationRepresentation U σ).eq]

/-- Every simultaneous round permutation fixes the paired symmetric subspace
pointwise. -/
lemma pairedPermutation_mul_symmetricProjectorPairedGen
    {dA dR n : ℕ} [NeZero dA] [NeZero dR] [NeZero n] (σ : Equiv.Perm (Fin n)) :
    Op.tensor (permutationRepresentation dA n σ) (permutationRepresentation dR n σ) *
      symmetricProjectorPairedGen dA dR n = symmetricProjectorPairedGen dA dR n := by
  apply (Matrix.reindexAlgEquiv ℂ ℂ (interleavingEquivGen dA dR n)).injective
  simp only [map_mul, Matrix.coe_reindexAlgEquiv,
    interleavingEquivGen_conjugates_perm, interleavingEquivGen_conjugates_projector]
  exact permRep_mul_symmetricProjector σ

/-- The marginal of a Hermitian operator supported on the paired symmetric
subspace commutes with each round permutation. -/
lemma partialTraceB_symmetric_supported_commute
    {dA dR n : ℕ} [NeZero dA] [NeZero dR] [NeZero n]
    (X : Op (dA ^ n * dR ^ n)) (hX : X.IsHermitian)
    (hsupp : symmetricProjectorPairedGen dA dR n * X = X)
    (σ : Equiv.Perm (Fin n)) :
    permutationRepresentation dA n σ * partialTraceB X =
      partialTraceB X * permutationRepresentation dA n σ := by
  let U := permutationRepresentation dA n σ
  let V := permutationRepresentation dR n σ
  have hTX : Op.tensor U V * X = X := by
    rw [← hsupp, ← mul_assoc, pairedPermutation_mul_symmetricProjectorPairedGen]
  have hXT : X * (Op.tensor U V)ᴴ = X := by
    have h := congrArg Matrix.conjTranspose hTX
    simpa only [Matrix.conjTranspose_mul, hX.eq] using h
  have hconj : Op.tensor U V * X * Op.tensor Uᴴ Vᴴ = X := by
    rw [← Op.tensor_conjTranspose, hTX, hXT]
  have h := partialTraceB_sandwich_tensor_unitary U Uᴴ V
    (permutationRepresentation_unitary dR n σ).1 X
  rw [hconj] at h
  have heq := congrArg (fun A => A * U) h
  have hU : Uᴴ * U = 1 := (permutationRepresentation_unitary dA n σ).1
  simpa only [mul_assoc, hU, mul_one] using heq.symm

/-- Left multiplication by a paired permutation permutes the two row words together. -/
lemma pairedPermutation_mul_apply {a b n : ℕ} [NeZero a] [NeZero b]
    (σ : Equiv.Perm (Fin n)) (M : Op (a ^ n * b ^ n))
    (i j : Fin (a ^ n * b ^ n)) :
    (Op.tensor (permutationRepresentation a n σ) (permutationRepresentation b n σ) * M) i j =
      M (finProdFinEquiv
        (finFunctionFinEquiv (finFunctionFinEquiv.symm (finProdFinEquiv.symm i).1 ∘ σ),
         finFunctionFinEquiv (finFunctionFinEquiv.symm (finProdFinEquiv.symm i).2 ∘ σ))) j := by
  classical
  have hshift {d : ℕ} (u v : Fin (d ^ n)) :
      (finFunctionFinEquiv.symm u = finFunctionFinEquiv.symm v ∘ σ.symm) ↔
        v = finFunctionFinEquiv (finFunctionFinEquiv.symm u ∘ σ) := by
    rw [eq_comp_perm_symm_iff_comp_perm_eq, ← Equiv.apply_eq_iff_eq finFunctionFinEquiv,
      Equiv.apply_symm_apply]
    exact eq_comm
  rw [Matrix.mul_apply, ← Equiv.sum_comp finProdFinEquiv]
  simp only [Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Equiv.symm_apply_apply, permutationRepresentation,
    Matrix.of_apply, hshift, Fintype.sum_prod_type]
  simp [ite_mul]

/-- A diagonal operator commutes with paired permutations when its entries are invariant. -/
lemma pairedPermutation_commute_diagonal {a b n : ℕ} [NeZero a] [NeZero b]
    (σ : Equiv.Perm (Fin n)) (f : Fin (a ^ n * b ^ n) → ℂ)
    (hf : ∀ i, f (finProdFinEquiv
        (finFunctionFinEquiv (finFunctionFinEquiv.symm (finProdFinEquiv.symm i).1 ∘ σ),
         finFunctionFinEquiv (finFunctionFinEquiv.symm (finProdFinEquiv.symm i).2 ∘ σ))) = f i) :
    Commute (Op.tensor (permutationRepresentation a n σ) (permutationRepresentation b n σ))
      (Matrix.diagonal f) := by
  classical
  ext i j
  have hU := pairedPermutation_mul_apply σ (1 : Op (a ^ n * b ^ n)) i j
  rw [mul_one, Matrix.one_apply] at hU
  rw [pairedPermutation_mul_apply, Matrix.diagonal_mul, hU, Matrix.diagonal_apply, hf]
  split <;> simp

/-- Regrouping a tensor family of bipartite operators gives the tensor product
of the two component tensor families. -/
lemma tensorFamily_tensor_interleaving {dA dB n : ℕ} [NeZero dA] [NeZero dB]
    (X : Fin n → Op dA) (Y : Fin n → Op dB) :
    Matrix.reindex (interleavingEquivGen dA dB n).symm (interleavingEquivGen dA dB n).symm
        (tensorFamily fun k => Op.tensor (X k) (Y k))
      = Op.tensor (tensorFamily X) (tensorFamily Y) := by
  -- Entry projections of `finProdFinEquiv.symm` are the `divNat`/`modNat` digits
  have hFst : ∀ {m n : ℕ} (x : Fin (m * n)), (finProdFinEquiv.symm x).1 = x.divNat :=
    fun x => congrArg Prod.fst (finProdFinEquiv_symm_apply x)
  have hMod : ∀ {m n : ℕ} (x : Fin (m * n)), (finProdFinEquiv.symm x).2 = x.modNat :=
    fun x => congrArg Prod.snd (finProdFinEquiv_symm_apply x)
  -- Digit bridge: site `k` of the interleaved index splits into the two blocked digits
  have hF : ∀ (i : Fin (dA ^ n * dB ^ n)) (k : Fin n),
      (finFunctionFinEquiv.symm (interleavingEquivGen dA dB n i) k).divNat
        = (@finFunctionFinEquiv dA n).symm i.divNat k := by
    intro i k
    have h := interleavingEquivGen_digit_fst (dA := dA) (dR := dB) (n := n)
      (interleavingEquivGen dA dB n i) k
    rw [Equiv.symm_apply_apply, finProdFinEquiv_symm_apply] at h
    exact h.symm
  have hS : ∀ (i : Fin (dA ^ n * dB ^ n)) (k : Fin n),
      (finFunctionFinEquiv.symm (interleavingEquivGen dA dB n i) k).modNat
        = (@finFunctionFinEquiv dB n).symm i.modNat k := by
    intro i k
    have h := interleavingEquivGen_digit_snd (dA := dA) (dR := dB) (n := n)
      (interleavingEquivGen dA dB n i) k
    rw [Equiv.symm_apply_apply, finProdFinEquiv_symm_apply] at h
    exact h.symm
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, hFst, hMod,
    tensorFamily_apply, Op_tensor_apply_finProd, hF, hS, Finset.prod_mul_distrib]

/-- Numeric reindexing commutes with tensor families. -/
lemma reindex_finCongr_tensorFamily {a b n : ℕ} (h : a = b) (X : Fin n → Op a) :
    Matrix.reindex (finCongr (congrArg (· ^ n) h)) (finCongr (congrArg (· ^ n) h))
      (tensorFamily X) = tensorFamily fun k => Matrix.reindex (finCongr h) (finCongr h) (X k) := by
  subst h
  rfl

/-- Numeric reassociation of three tensor factors preserves their order. -/
lemma reindex_tensor_assoc {a b c : ℕ} (X : Op a) (Y : Op b) (Z : Op c) :
    Matrix.reindex (finCongr (Nat.mul_assoc a b c)) (finCongr (Nat.mul_assoc a b c))
      (Op.tensor (Op.tensor X Y) Z) = Op.tensor X (Op.tensor Y Z) := by
  rw [← Op.tensor_assoc, ← Op.castDim_eq_reindex_finCongr]
  exact Op.castDim_cancel _ _ _

/-- Reassociation with a prescribed reference dimension preserves the tensor factors. -/
lemma reindex_tensor_assoc_cast {a b c r : ℕ} (h : b * c = r)
    (X : Op a) (Y : Op b) (Z : Op c) :
    Matrix.reindex (finCongr ((Nat.mul_assoc a b c).trans (congrArg (a * ·) h)))
      (finCongr ((Nat.mul_assoc a b c).trans (congrArg (a * ·) h)))
      (Op.tensor (Op.tensor X Y) Z) =
        Op.tensor X (Matrix.reindex (finCongr h) (finCongr h) (Op.tensor Y Z)) := by
  subst h
  exact reindex_tensor_assoc X Y Z

/-- Regrouping paired tensor families separates Alice from Bob and the reference. -/
lemma pairedToBlockedEquiv_tensorFamily {a b n : ℕ} [NeZero a] [NeZero b]
    (A : Fin n → Op a) (B : Fin n → Op b) (C : Fin n → Op (a * b)) :
    Matrix.reindex (pairedToBlockedEquiv a b n) (pairedToBlockedEquiv a b n)
      (Op.tensor (tensorFamily fun k => Op.tensor (A k) (B k)) (tensorFamily C)) =
      Op.tensor (tensorFamily A) (tensorFamily fun k =>
        Matrix.reindex (finCongr (show b * (a * b) = a * b ^ 2 by ring))
          (finCongr (show b * (a * b) = a * b ^ 2 by ring)) (Op.tensor (B k) (C k))) := by
  have : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have : NeZero (a * b ^ 2) := ⟨mul_ne_zero (NeZero.ne a) (pow_ne_zero 2 (NeZero.ne b))⟩
  rw [pairedToBlockedEquiv, Matrix.reindex_trans_apply, Matrix.reindex_trans_apply,
    ← tensorFamily_tensor_interleaving, Matrix.reindex_reindex_symm,
    reindex_finCongr_tensorFamily (show (a * b) * (a * b) = a * (a * b ^ 2) by ring)]
  have h (k : Fin n) := reindex_tensor_assoc_cast
    (show b * (a * b) = a * b ^ 2 by ring) (A k) (B k) (C k)
  simp_rw [h]
  exact tensorFamily_tensor_interleaving _ _

/-- Tensor powers of the entangled operator regroup into the entangled operator. -/
lemma maxEntangledOp_tensorPow_interleaving {d n : ℕ} [NeZero d] :
    Matrix.reindex (interleavingEquivGen d d n).symm (interleavingEquivGen d d n).symm
      (Op.tensorPow (maxEntangledOp d) n) = maxEntangledOp (d ^ n) := by
  have hfst (i : Fin (d ^ n * d ^ n)) (k : Fin n) :
      (finProdFinEquiv.symm (finFunctionFinEquiv.symm (interleavingEquivGen d d n i) k)).1 =
        finFunctionFinEquiv.symm (finProdFinEquiv.symm i).1 k := by
    have h := (interleavingEquivGen_digit_fst (interleavingEquivGen d d n i) k).symm
    simp only [Equiv.symm_apply_apply] at h
    exact h
  have hsnd (i : Fin (d ^ n * d ^ n)) (k : Fin n) :
      (finProdFinEquiv.symm (finFunctionFinEquiv.symm (interleavingEquivGen d d n i) k)).2 =
        finFunctionFinEquiv.symm (finProdFinEquiv.symm i).2 k := by
    have h := (interleavingEquivGen_digit_snd (interleavingEquivGen d d n i) k).symm
    simp only [Equiv.symm_apply_apply] at h
    exact h
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Op.tensorPow_eq_tensorFamily, tensorFamily_apply, maxEntangledOp, Matrix.of_apply,
    hfst, hsnd, Fintype.prod_ite_zero, forall_and, ← funext_iff,
    finFunctionFinEquiv.symm.injective.eq_iff, Finset.prod_const_one]

/-- Reassociation turns two successive partial traces into one partial trace. -/
lemma partialTraceB_reindex_assoc_cast {a b c r : ℕ} (h : b * c = r)
    (M : Op ((a * b) * c)) :
    partialTraceB (Matrix.reindex
      (finCongr ((Nat.mul_assoc a b c).trans (congrArg (a * ·) h)))
      (finCongr ((Nat.mul_assoc a b c).trans (congrArg (a * ·) h))) M) =
      partialTraceB (partialTraceB M) := by
  subst h
  rw [← Op.castDim_eq_reindex_finCongr]
  exact (partialTraceB_partialTraceB_eq_assoc M).symm

/-- The one-round entangled seed, with Alice separated and identity Alice marginal. -/
def blockedEntangledSeedRound (a b : ℕ) : Op (a * (a * b ^ 2)) :=
  Matrix.reindex (finCongr (show (a * b) * (a * b) = a * (a * b ^ 2) by ring))
    (finCongr (show (a * b) * (a * b) = a * (a * b ^ 2) by ring))
    ((b : ℂ)⁻¹ • maxEntangledOp (a * b))

/-- The one-round blocked entangled seed is positive semidefinite. -/
lemma blockedEntangledSeedRound_posSemidef (a b : ℕ) :
    (blockedEntangledSeedRound a b).PosSemidef :=
  ((maxEntangledOp_posSemidef _).smul (by positivity)).submatrix _

/-- The one-round blocked entangled seed has identity Alice marginal. -/
lemma blockedEntangledSeedRound_partialTraceB (a b : ℕ) [NeZero b] :
    partialTraceB (blockedEntangledSeedRound a b) = 1 := by
  rw [blockedEntangledSeedRound, partialTraceB_reindex_assoc_cast
    (show b * (a * b) = a * b ^ 2 by ring), partialTraceB_smul,
    maxEntangledOp_partialTraceB, partialTraceB_smul, partialTraceB_one]
  simp [smul_smul, NeZero.ne b]

/-- The paired entangled seed scaled to have identity Alice marginal. -/
def blockedEntangledSeed (a b n : ℕ) : Op (a ^ n * (a * b ^ 2) ^ n) :=
  (b : ℂ)⁻¹ ^ n • Matrix.reindex (pairedToBlockedEquiv a b n) (pairedToBlockedEquiv a b n)
    (maxEntangledOp ((a * b) ^ n))

/-- The blocked entangled seed is positive semidefinite. -/
lemma blockedEntangledSeed_posSemidef (a b n : ℕ) : (blockedEntangledSeed a b n).PosSemidef := by
  exact ((maxEntangledOp_posSemidef _).submatrix _).smul (by positivity)

/-- The blocked entangled seed has identity Alice marginal. -/
lemma blockedEntangledSeed_partialTraceB (a b n : ℕ) [NeZero a] [NeZero b] [NeZero n] :
    partialTraceB (blockedEntangledSeed a b n) = 1 := by
  rw [blockedEntangledSeed, partialTraceB_smul,
    pairedToBlockedEquiv_partialTraceB_eq_roundGroup, maxEntangledOp_partialTraceB]
  simp [partialTraceB_one, NeZero.ne b]

/-- The blocked entangled seed is supported on the paired symmetric subspace. -/
lemma symmetricProjectorPairedGen_mul_blockedEntangledSeed (a b n : ℕ)
    [NeZero a] [NeZero b] [NeZero n] :
    symmetricProjectorPairedGen a (a * b ^ 2) n * blockedEntangledSeed a b n =
      blockedEntangledSeed a b n := by
  have : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  rw [blockedEntangledSeed, mul_smul_comm,
    ← pairedToBlockedEquiv_conjugates_projector, ← Matrix.reindex_mul,
    symmetricProjectorPaired_mul_eq_of_perm_left_invariant _
      (fun σ => maxEntangledOp_left_perm_invariant σ)]

/-- The blocked entangled seed is the regrouped tensor power of its one-round seed. -/
lemma blockedEntangledSeed_eq_tensorPow (a b n : ℕ) [NeZero a] [NeZero b] :
    blockedEntangledSeed a b n =
      Matrix.reindex (interleavingEquivGen a (a * b ^ 2) n).symm
        (interleavingEquivGen a (a * b ^ 2) n).symm
        (Op.tensorPow (blockedEntangledSeedRound a b) n) := by
  have : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  rw [blockedEntangledSeedRound, blockedEntangledSeed, ← maxEntangledOp_tensorPow_interleaving,
    pairedToBlockedEquiv, Matrix.reindex_trans_apply, Matrix.reindex_trans_apply,
    Matrix.reindex_reindex_symm, Op.reindex_finCongr_tensorPow
      (show (a * b) * (a * b) = a * (a * b ^ 2) by ring),
    Matrix.reindex_smul, Op.smul_tensorPow, Matrix.reindex_smul]

/-- Tensor powers commute with changing from Alice-reference to paired registers. -/
lemma pairedToBlockedEquiv_tensorPow_cast {a b n : ℕ} (T : Op (a * (a * b ^ 2))) :
    Matrix.reindex (pairedToBlockedEquiv a b n).symm (pairedToBlockedEquiv a b n).symm
      (Matrix.reindex (interleavingEquivGen a (a * b ^ 2) n).symm
        (interleavingEquivGen a (a * b ^ 2) n).symm (Op.tensorPow T n)) =
      Matrix.reindex (interleavingEquivGen (a * b) (a * b) n).symm
        (interleavingEquivGen (a * b) (a * b) n).symm
        (Op.tensorPow (Matrix.reindex
          (finCongr (show a * (a * b ^ 2) = (a * b) * (a * b) by ring))
          (finCongr (show a * (a * b ^ 2) = (a * b) * (a * b) by ring)) T) n) := by
  have hflip {X Y Z : Type} (e : X ≃ Y) (f : Y ≃ Z) :
      (e.trans f).symm = f.symm.trans e.symm := rfl
  simp only [pairedToBlockedEquiv, hflip,
    Matrix.reindex_trans_apply, Equiv.symm_symm, Matrix.reindex_reindex_symm]
  rw [show (finCongr (congrArg (· ^ n) (show (a * b) * (a * b) = a * (a * b ^ 2) by ring))).symm =
    finCongr (congrArg (· ^ n) (show a * (a * b ^ 2) = (a * b) * (a * b) by ring)) from rfl,
    Op.reindex_finCongr_tensorPow]

end InfoTheory.Postselection
