import QCryptLean.Quantum.Channels.CPTP.CKRBound.Contractivity
import QCryptLean.Quantum.Metrics.TraceNormHoelder

/-!
# Rectangular tensor isometries `id ⊗ V` — trace-norm transport and channel conjugacy

This file collects branch-agnostic operator-algebra lemmas for the rectangular
Kronecker tensor `id_c ⊗ V`, where `V : Matrix (Fin m) (Fin n) ℂ` is a
(rectangular) partial isometry on an ancilla register. They are used to transport
isometric-conjugation relations through identity-tensored maps and to certify
trace-norm invariance under such conjugation.

## Main definitions
- `idTensorRectMatrix`: block representation of the rectangular tensor `id_c ⊗ V`.

## Main statements
- `idTensorRect_eq_of`: the `Matrix.of` block form equals the reindexed Kronecker
  tensor `id_c ⊗ V`.
- `Quantum.Metrics.TraceNormHoelder.idTensorRect_isometry`: `id_c ⊗ V` is an isometry when `V` is.
- `Quantum.Channels.traceNorm_idTensorRect_isometry_mul_left`: trace-norm invariance under
  conjugation by `id ⊗ V`.
- `traceNorm_sub_idTensorRect_conj_eq`: trace-norm invariance for differences
  transported by the same rectangular tensor isometry.
- `matrix_mul_sub_mul_conjTranspose`: conjugation distributes over a difference.
- `mapIdTensor_conj_of_conj`: an isometric conjugacy of two maps lifts through
  `mapIdTensor` to a conjugacy of the identity-tensored maps.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker

noncomputable section

namespace Quantum.Channels

/-- The `Matrix.of` block form used in isometric-conjugacy hypotheses is the
rectangular Kronecker tensor `id ⊗ V`. -/
lemma idTensorRect_eq_of {c m n : ℕ}
    (V : Matrix (Fin m) (Fin n) ℂ) :
    (Matrix.of fun p q =>
      let ⟨a, e⟩ := finProdFinEquiv.symm p
      let ⟨b, f⟩ := finProdFinEquiv.symm q
      if a = b then V e f else 0) =
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      ((1 : Op c) ⊗ₖ V) :
        Matrix (Fin (c * m)) (Fin (c * n)) ℂ) := by
  ext p q
  simp [Matrix.reindex, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Trace norm is invariant under conjugation by the rectangular tensor `id ⊗ V`
when `V` is an isometry. -/
theorem traceNorm_idTensorRect_isometry_mul_left {c m n : ℕ} [NeZero c]
    [NeZero m] [NeZero n]
    (V : Matrix (Fin m) (Fin n) ℂ)
    (A : Op (c * n))
    (hV : V.conjTranspose * V = (1 : Op n)) :
    let W : Matrix (Fin (c * m)) (Fin (c * n)) ℂ :=
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((1 : Op c) ⊗ₖ V)
    Quantum.Metrics.traceNorm (W * A * W.conjTranspose) =
      Quantum.Metrics.traceNorm A := by
  dsimp
  exact Quantum.Metrics.TraceNormHoelder.traceNorm_isometry_mul_left
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      ((1 : Op c) ⊗ₖ V)) A
    (Quantum.Metrics.TraceNormHoelder.idTensorRect_isometry V hV)

/-- The rectangular tensor `id_c ⊗ V`, represented as a block matrix indexed by
`Fin (c * m)` and `Fin (c * n)` via the product-index equivalence. -/
noncomputable def idTensorRectMatrix (c m n : ℕ)
    (V : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin (c * m)) (Fin (c * n)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    ((1 : Op c) ⊗ₖ V)

/-- Conjugating two matrices by the same rectangular tensor isometry preserves
the trace norm of their difference. -/
lemma traceNorm_sub_idTensorRect_conj_eq {c m n : ℕ} [NeZero c] [NeZero m]
    [NeZero n]
    (V : Matrix (Fin m) (Fin n) ℂ)
    (A B : Op (c * m))
    (A' B' : Op (c * n))
    (hV : V.conjTranspose * V = (1 : Op n))
    (hA : A = idTensorRectMatrix c m n V * A' *
      (idTensorRectMatrix c m n V).conjTranspose)
    (hB : B = idTensorRectMatrix c m n V * B' *
      (idTensorRectMatrix c m n V).conjTranspose) :
    Quantum.Metrics.traceNorm (A - B) =
      Quantum.Metrics.traceNorm (A' - B') := by
  let W := idTensorRectMatrix c m n V
  have hDiff : A - B = W * (A' - B') * W.conjTranspose := by
    simp only [W]
    rw [hA, hB]
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hDiff]
  simpa [W, idTensorRectMatrix] using
    Quantum.Channels.traceNorm_idTensorRect_isometry_mul_left (c := c) (m := m) (n := n)
      V (A' - B') hV

/-- Conjugation by a fixed matrix distributes over a difference. -/
lemma matrix_mul_sub_mul_conjTranspose {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℂ) (A B : Op n) :
    W * (A - B) * W.conjTranspose =
      W * A * W.conjTranspose - W * B * W.conjTranspose := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

private lemma fintype_sum_four_rotate {α β γ δ M : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M]
    (f : α → β → γ → δ → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d) =
      ∑ c : γ, ∑ d : δ, ∑ a : α, ∑ b : β, f a b c d := by
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext b
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext b
    arg 2
    ext c
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext c
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext c
    arg 2
    ext d
    rw [Finset.sum_comm]

/-- Isometric conjugacy of two maps lifts through `mapIdTensor` to a conjugacy of
the identity-tensored maps.

If `Φ A = W * Ψ A * Wᴴ` for all `A`, then `mapIdTensor Φ X = (id ⊗ W) * mapIdTensor Ψ X * (id ⊗ W)ᴴ`
for all `X`, where `id ⊗ W` is the rectangular block tensor on the `Fin k`
factor. -/
lemma mapIdTensor_conj_of_conj
    {n m m' k : ℕ} [NeZero n] [NeZero m] [NeZero m'] [NeZero k]
    (Φ : Op n →ₗ[ℂ] Op m) (Ψ : Op n →ₗ[ℂ] Op m')
    (W : Matrix (Fin m) (Fin m') ℂ)
    (hΦ : ∀ A : Op n, Φ A = W * Ψ A * Wᴴ)
    (X : Op (k * n)) :
    let idTensorW : Matrix (Fin (k * m)) (Fin (k * m')) ℂ :=
      Matrix.of fun p q =>
        let ⟨s, a⟩ := finProdFinEquiv.symm p
        let ⟨t, b⟩ := finProdFinEquiv.symm q
        if s = t then W a b else 0
    mapIdTensor Φ X = idTensorW * mapIdTensor Ψ X * idTensorWᴴ := by
  intro idTensorW
  -- In product coordinates `id ⊗ W` is block diagonal with diagonal blocks `W`, so it acts on a
  -- row (left factor) or column (right factor) inside one `Fin k` block only.
  have hW (s t : Fin k) (a : Fin m) (b : Fin m') :
      idTensorW (finProdFinEquiv (s, a)) (finProdFinEquiv (t, b)) = if s = t then W a b else 0 := by
    simp only [idTensorW, Matrix.of_apply, Equiv.toFun_as_coe, Equiv.symm_apply_apply]
  have hrow (s : Fin k) (a : Fin m) (f : Fin (k * m') → ℂ) :
      ∑ p, idTensorW (finProdFinEquiv (s, a)) p * f p =
        ∑ a', W a a' * f (finProdFinEquiv (s, a')) := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type,
      Fintype.sum_eq_single s fun s' hs' => Finset.sum_eq_zero fun a' _ => by
        rw [hW, if_neg (Ne.symm hs'), zero_mul]]
    exact Finset.sum_congr rfl fun a' _ => by rw [hW, if_pos rfl]
  have hcol (t : Fin k) (b : Fin m) (f : Fin (k * m') → ℂ) :
      ∑ q, f q * star (idTensorW (finProdFinEquiv (t, b)) q) =
        ∑ b', f (finProdFinEquiv (t, b')) * star (W b b') := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type,
      Fintype.sum_eq_single t fun t' ht' => Finset.sum_eq_zero fun b' _ => by
        rw [hW, if_neg (Ne.symm ht'), star_zero, mul_zero]]
    exact Finset.sum_congr rfl fun b' _ => by rw [hW, if_pos rfl]
  ext p q
  obtain ⟨⟨s, a⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨t, b⟩, rfl⟩ := finProdFinEquiv.surjective q
  -- The `(s, a), (t, b)` entry of the conjugation is `W` applied to the `(s, t)` block.
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply]
  rw [hcol]
  simp only [hrow]
  -- Both sides are now the same fourfold sum over the block indices `i j` and the `W`-indices.
  simp only [mapIdTensor, Matrix.of_apply, Equiv.toFun_as_coe, Equiv.symm_apply_apply, hΦ,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [fintype_sum_four_rotate]
  refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A pointwise rectangular output conjugation lifts to an untouched reference. -/
lemma mapTensorId_conj_of_conj {a b c r : ℕ}
    [NeZero a] [NeZero b] [NeZero c] [NeZero r]
    (F : Op a →ₗ[ℂ] Op c) (G : Op a →ₗ[ℂ] Op b)
    (E : Matrix (Fin c) (Fin b) ℂ)
    (h : ∀ A, F A = E * G A * Eᴴ) (A : Op (a * r)) :
    mapTensorId F A = tensorRect E (1 : Op r) * mapTensorId G A *
      (tensorRect E (1 : Op r))ᴴ := by
  ext p q
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [tensorRect_one_sandwich_block, mapTensorId_apply_eq_apply_block]
  simp only [Equiv.symm_apply_apply]
  rw [h]
  simp only [mapTensorId_apply_eq_apply_block, Equiv.symm_apply_apply]
  rfl

end Quantum.Channels

end -- noncomputable section
