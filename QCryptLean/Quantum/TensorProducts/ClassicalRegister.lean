import QCryptLean.Quantum.TensorProducts.Rectangular

/-!
# Classical label registers

Appending and prepending a fixed basis label are isometries. Their matrix products place and
extract blocks, and canonical reassociation makes each write local to one tensor factor.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

/-- **Appending a classical label** `d` to a register of size `N`: the isometry `|j⟩ ↦ |j⟩|d⟩`,
with the label in the low product digit. -/
def appendIndexKraus (N : ℕ) {D : ℕ} (d : Fin D) : Matrix (Fin (N * D)) (Fin N) ℂ :=
  Matrix.of fun i j => if i = finProdFinEquiv (j, d) then 1 else 0

/-- **Prepending a classical label** `d` to a register of size `N`: the isometry `|j⟩ ↦ |d⟩|j⟩`,
with the label in the high product digit. -/
def prependIndexKraus (N : ℕ) {D : ℕ} (d : Fin D) : Matrix (Fin (D * N)) (Fin N) ℂ :=
  Matrix.of fun i j => if i = finProdFinEquiv (d, j) then 1 else 0

@[simp] theorem appendIndexKraus_apply (N : ℕ) {D : ℕ} (d : Fin D)
    (i : Fin (N * D)) (j : Fin N) :
    appendIndexKraus N d i j = if i = finProdFinEquiv (j, d) then 1 else 0 := rfl

@[simp] theorem prependIndexKraus_apply (N : ℕ) {D : ℕ} (d : Fin D)
    (i : Fin (D * N)) (j : Fin N) :
    prependIndexKraus N d i j = if i = finProdFinEquiv (d, j) then 1 else 0 := rfl

/-- The appended label as a condition on index numerals: the label is the remainder. -/
theorem appendIndexKraus_val (N : ℕ) {D : ℕ} (d : Fin D) (i : Fin (N * D)) (j : Fin N) :
    appendIndexKraus N d i j = if (i : ℕ) = (d : ℕ) + D * (j : ℕ) then 1 else 0 := by
  rw [appendIndexKraus_apply]
  exact if_congr (by rw [Fin.ext_iff, finProdFinEquiv_val]) rfl rfl

/-- The prepended label as a condition on index numerals: the label is the quotient. -/
theorem prependIndexKraus_val (N : ℕ) {D : ℕ} (d : Fin D) (i : Fin (D * N)) (j : Fin N) :
    prependIndexKraus N d i j = if (i : ℕ) = (j : ℕ) + N * (d : ℕ) then 1 else 0 := by
  rw [prependIndexKraus_apply]
  exact if_congr (by rw [Fin.ext_iff, finProdFinEquiv_val]) rfl rfl

/-- The label writers as sums of matrix units, one per basis vector of the written register. -/
theorem appendIndexKraus_eq_sum_single (N : ℕ) {D : ℕ} (d : Fin D) :
    appendIndexKraus N d = ∑ j : Fin N, Matrix.single (finProdFinEquiv (j, d)) j (1 : ℂ) := by
  ext i j
  rw [appendIndexKraus_apply, Matrix.sum_apply, Finset.sum_eq_single j]
  · rw [Matrix.single_apply]
    exact if_congr (by simp [eq_comm]) rfl rfl
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem prependIndexKraus_eq_sum_single (N : ℕ) {D : ℕ} (d : Fin D) :
    prependIndexKraus N d = ∑ j : Fin N, Matrix.single (finProdFinEquiv (d, j)) j (1 : ℂ) := by
  ext i j
  rw [prependIndexKraus_apply, Matrix.sum_apply, Finset.sum_eq_single j]
  · rw [Matrix.single_apply]
    exact if_congr (by simp [eq_comm]) rfl rfl
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-! ## 2. Isometry, orthogonality and the label block -/

private theorem appendIndexKraus_gram {D N : ℕ} (d d' : Fin D) :
    (appendIndexKraus N d)ᴴ * appendIndexKraus N d' =
      if d = d' then (1 : Matrix (Fin N) (Fin N) ℂ) else 0 := by
  ext j j'
  rw [Matrix.mul_apply, Finset.sum_eq_single (finProdFinEquiv (j, d))]
  · rw [Matrix.conjTranspose_apply, appendIndexKraus_apply, if_pos rfl, star_one, one_mul,
      appendIndexKraus_apply,
      if_congr (show (finProdFinEquiv (j, d) = finProdFinEquiv (j', d')) ↔ (j = j' ∧ d = d') by
        rw [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]) rfl rfl]
    by_cases h : d = d'
    · subst h
      simp [Matrix.one_apply]
    · simp [h]
  · intro i _ hi
    rw [Matrix.conjTranspose_apply, appendIndexKraus_apply, if_neg hi, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem prependIndexKraus_gram {D N : ℕ} (d d' : Fin D) :
    (prependIndexKraus N d)ᴴ * prependIndexKraus N d' =
      if d = d' then (1 : Matrix (Fin N) (Fin N) ℂ) else 0 := by
  ext j j'
  rw [Matrix.mul_apply, Finset.sum_eq_single (finProdFinEquiv (d, j))]
  · rw [Matrix.conjTranspose_apply, prependIndexKraus_apply, if_pos rfl, star_one, one_mul,
      prependIndexKraus_apply,
      if_congr (show (finProdFinEquiv (d, j) = finProdFinEquiv (d', j')) ↔ (j = j' ∧ d = d') by
        rw [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]; tauto) rfl rfl]
    by_cases h : d = d'
    · subst h
      simp [Matrix.one_apply]
    · simp [h]
  · intro i _ hi
    rw [Matrix.conjTranspose_apply, prependIndexKraus_apply, if_neg hi, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Writing a label is an isometry**: it adjoins a register without disturbing the state. This
is what keeps a branch of a protocol from silently losing weight. -/
theorem appendIndexKraus_conjTranspose_mul_self (N : ℕ) {D : ℕ} (d : Fin D) :
    (appendIndexKraus N d)ᴴ * appendIndexKraus N d = 1 := by
  rw [appendIndexKraus_gram, if_pos rfl]

theorem prependIndexKraus_conjTranspose_mul_self (N : ℕ) {D : ℕ} (d : Fin D) :
    (prependIndexKraus N d)ᴴ * prependIndexKraus N d = 1 := by
  rw [prependIndexKraus_gram, if_pos rfl]

/-- **Distinct labels have orthogonal images.** With the isometry law this says the label writers
are an orthonormal family of embeddings, one per classical value. -/
theorem appendIndexKraus_conjTranspose_mul_of_ne (N : ℕ) {D : ℕ} {d d' : Fin D} (h : d ≠ d') :
    (appendIndexKraus N d)ᴴ * appendIndexKraus N d' = 0 := by
  rw [appendIndexKraus_gram, if_neg h]

theorem prependIndexKraus_conjTranspose_mul_of_ne (N : ℕ) {D : ℕ} {d d' : Fin D} (h : d ≠ d') :
    (prependIndexKraus N d)ᴴ * prependIndexKraus N d' = 0 := by
  rw [prependIndexKraus_gram, if_neg h]

private theorem sum_single_mul_conjTranspose {P N : ℕ} (f : Fin N → Fin P) :
    (∑ j : Fin N, Matrix.single (f j) j (1 : ℂ)) *
        (∑ j : Fin N, Matrix.single (f j) j (1 : ℂ))ᴴ =
      ∑ j : Fin N, Matrix.single (f j) (f j) (1 : ℂ) := by
  rw [Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_single, star_one]
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_sum, Finset.sum_eq_single j]
  · rw [Matrix.single_mul_single_same, one_mul]
  · intro j' _ hj'
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hj')]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **The image of one label is a block of the composite register.** The reverse product is the
projector onto that block, so writing a label is not a co-isometry unless that block exhausts the
composite register. -/
theorem appendIndexKraus_mul_conjTranspose (N : ℕ) {D : ℕ} (d : Fin D) :
    appendIndexKraus N d * (appendIndexKraus N d)ᴴ =
      ∑ j : Fin N, Matrix.single (finProdFinEquiv (j, d)) (finProdFinEquiv (j, d)) (1 : ℂ) := by
  rw [appendIndexKraus_eq_sum_single]
  exact sum_single_mul_conjTranspose fun j => finProdFinEquiv (j, d)

theorem prependIndexKraus_mul_conjTranspose (N : ℕ) {D : ℕ} (d : Fin D) :
    prependIndexKraus N d * (prependIndexKraus N d)ᴴ =
      ∑ j : Fin N, Matrix.single (finProdFinEquiv (d, j)) (finProdFinEquiv (d, j)) (1 : ℂ) := by
  rw [prependIndexKraus_eq_sum_single]
  exact sum_single_mul_conjTranspose fun j => finProdFinEquiv (d, j)

/-! ## 3. Block placement and block extraction -/

/-- **Block placement.** Conjugating `M` by the label writers at labels `d` and `d'` places `M` in
the `(d, d')` block of the composite register: the result is the rectangular Kronecker product of
`M` with the matrix unit `|d⟩⟨d'|` on the label register. -/
theorem appendIndexKraus_mul_mul_conjTranspose {N N' D D' : ℕ} (d : Fin D) (d' : Fin D')
    (M : Matrix (Fin N) (Fin N') ℂ) :
    appendIndexKraus N d * M * (appendIndexKraus N' d')ᴴ =
      tensorRect M (Matrix.single d d' (1 : ℂ)) := by
  rw [tensorRect_single_right_eq_sum, appendIndexKraus_eq_sum_single,
    appendIndexKraus_eq_sum_single, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_single, star_one]
  rw [Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.single_mul_mul_single]
  simp only [one_mul, mul_one]

/-- Block placement for a prepended label: `M` lands in the `(d, d')` block with the label as the
high digit. -/
theorem prependIndexKraus_mul_mul_conjTranspose {N N' D D' : ℕ} (d : Fin D) (d' : Fin D')
    (M : Matrix (Fin N) (Fin N') ℂ) :
    prependIndexKraus N d * M * (prependIndexKraus N' d')ᴴ =
      tensorRect (Matrix.single d d' (1 : ℂ)) M := by
  rw [tensorRect_single_left_eq_sum, prependIndexKraus_eq_sum_single,
    prependIndexKraus_eq_sum_single, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_single, star_one]
  rw [Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.single_mul_mul_single]
  simp only [one_mul, mul_one]

/-- **Mixed block placement.** Appending the row label and prepending the column label places
`M i j` at the interior-major row `finProdFinEquiv (i, d)` and label-major column
`finProdFinEquiv (d', j)`. -/
theorem appendIndexKraus_mul_mul_prependIndexKraus_conjTranspose
    {N N' D D' : ℕ} (d : Fin D) (d' : Fin D')
    (M : Matrix (Fin N) (Fin N') ℂ) :
    appendIndexKraus N d * M * (prependIndexKraus N' d')ᴴ =
      ∑ i : Fin N, ∑ j : Fin N',
        Matrix.single (finProdFinEquiv (i, d)) (finProdFinEquiv (d', j)) (M i j) := by
  rw [prependIndexKraus_eq_sum_single, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_single, star_one]
  rw [appendIndexKraus_eq_sum_single, Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.single_mul_mul_single]
  simp only [one_mul, mul_one]

/-- **Mirror mixed block placement.** Prepending the row label and appending the column label
places `M i j` at the label-major row `finProdFinEquiv (d, i)` and interior-major column
`finProdFinEquiv (j, d')`. It is the digit-swapped companion of
`appendIndexKraus_mul_mul_prependIndexKraus_conjTranspose`. -/
theorem prependIndexKraus_mul_mul_appendIndexKraus_conjTranspose
    {N N' D D' : ℕ} (d : Fin D) (d' : Fin D')
    (M : Matrix (Fin N) (Fin N') ℂ) :
    prependIndexKraus N d * M * (appendIndexKraus N' d')ᴴ =
      ∑ i : Fin N, ∑ j : Fin N',
        Matrix.single (finProdFinEquiv (d, i)) (finProdFinEquiv (j, d')) (M i j) := by
  rw [appendIndexKraus_eq_sum_single, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_single, star_one]
  rw [prependIndexKraus_eq_sum_single, Matrix.sum_mul, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.single_mul_mul_single]
  simp only [one_mul, mul_one]

/-- **What appending a label does to a state**: `ρ ↦ ρ ⊗ |d⟩⟨d|`. The diagonal case of
`appendIndexKraus_mul_mul_conjTranspose`, in the square `Op.tensor` form. -/
theorem appendIndexKraus_conj {N D : ℕ} (d : Fin D) (M : Op N) :
    appendIndexKraus N d * M * (appendIndexKraus N d)ᴴ =
      Op.tensor M (Matrix.single d d (1 : ℂ)) :=
  (appendIndexKraus_mul_mul_conjTranspose d d M).trans (tensorRect_square _ _)

/-- Prepending a label: `ρ ↦ |d⟩⟨d| ⊗ ρ`. -/
theorem prependIndexKraus_conj {N D : ℕ} (d : Fin D) (M : Op N) :
    prependIndexKraus N d * M * (prependIndexKraus N d)ᴴ =
      Op.tensor (Matrix.single d d (1 : ℂ)) M :=
  (prependIndexKraus_mul_mul_conjTranspose d d M).trans (tensorRect_square _ _)

/-- **A family of blocks, placed.** Summing the placement of `C d` at label `d` over all labels
gives the block-diagonal operator in tensor form. -/
theorem sum_appendIndexKraus_conj {N D : ℕ} (C : Fin D → Op N) :
    (∑ d : Fin D, appendIndexKraus N d * C d * (appendIndexKraus N d)ᴴ) =
      ∑ d : Fin D, Op.tensor (C d) (Matrix.single d d (1 : ℂ)) :=
  Finset.sum_congr rfl fun d _ => appendIndexKraus_conj d (C d)

theorem sum_prependIndexKraus_conj {N D : ℕ} (C : Fin D → Op N) :
    (∑ d : Fin D, prependIndexKraus N d * C d * (prependIndexKraus N d)ᴴ) =
      ∑ d : Fin D, Op.tensor (Matrix.single d d (1 : ℂ)) (C d) :=
  Finset.sum_congr rfl fun d _ => prependIndexKraus_conj d (C d)

/-- **A labelled family is block diagonal.** Writing label `d` on the block `C d` and summing
over the labels gives `Matrix.blockDiagonal C`, read in the numeral coordinate. The reindex is
not removable: `Matrix.blockDiagonal` is indexed by the pair `(interior, label)` and the label
register by its numeral. -/
theorem sum_appendIndexKraus_conj_eq_reindex_blockDiagonal {N D : ℕ} (C : Fin D → Op N) :
    (∑ d : Fin D, appendIndexKraus N d * C d * (appendIndexKraus N d)ᴴ) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.blockDiagonal C) :=
  (sum_appendIndexKraus_conj C).trans
    (Quantum.TensorProducts.sum_tensor_single_eq_reindex_blockDiagonal C)

/-- The mirror of `sum_appendIndexKraus_conj_eq_reindex_blockDiagonal` for the high-digit writer.
`Matrix.blockDiagonal` always puts the label second, so the two index factors are exchanged
before the numeral coordinate is taken. -/
theorem sum_prependIndexKraus_conj_eq_reindex_blockDiagonal {N D : ℕ} (C : Fin D → Op N) :
    (∑ d : Fin D, prependIndexKraus N d * C d * (prependIndexKraus N d)ᴴ) =
      Matrix.reindex ((Equiv.prodComm (Fin N) (Fin D)).trans finProdFinEquiv)
        ((Equiv.prodComm (Fin N) (Fin D)).trans finProdFinEquiv) (Matrix.blockDiagonal C) :=
  (sum_prependIndexKraus_conj C).trans
    (Quantum.TensorProducts.sum_single_tensor_eq_reindex_blockDiagonal C)

/-- **Block extraction.** The sandwich read in the other direction reads off the `(d, d')` block
of a matrix on the composite register. -/
theorem conjTranspose_appendIndexKraus_mul_mul {N N' D D' : ℕ} (d : Fin D) (d' : Fin D')
    (M : Matrix (Fin (N * D)) (Fin (N' * D')) ℂ) :
    (appendIndexKraus N d)ᴴ * M * appendIndexKraus N' d' =
      Matrix.of fun i j => M (finProdFinEquiv (i, d)) (finProdFinEquiv (j, d')) := by
  ext i j
  rw [Matrix.of_apply, Matrix.mul_apply, Finset.sum_eq_single (finProdFinEquiv (j, d'))]
  · rw [appendIndexKraus_apply, if_pos rfl, mul_one, Matrix.mul_apply,
      Finset.sum_eq_single (finProdFinEquiv (i, d))]
    · rw [Matrix.conjTranspose_apply, appendIndexKraus_apply, if_pos rfl, star_one, one_mul]
    · intro p _ hp
      rw [Matrix.conjTranspose_apply, appendIndexKraus_apply, if_neg hp, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q _ hq
    rw [appendIndexKraus_apply, if_neg hq, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem conjTranspose_prependIndexKraus_mul_mul {N N' D D' : ℕ} (d : Fin D) (d' : Fin D')
    (M : Matrix (Fin (D * N)) (Fin (D' * N')) ℂ) :
    (prependIndexKraus N d)ᴴ * M * prependIndexKraus N' d' =
      Matrix.of fun i j => M (finProdFinEquiv (d, i)) (finProdFinEquiv (d', j)) := by
  ext i j
  rw [Matrix.of_apply, Matrix.mul_apply, Finset.sum_eq_single (finProdFinEquiv (d', j))]
  · rw [prependIndexKraus_apply, if_pos rfl, mul_one, Matrix.mul_apply,
      Finset.sum_eq_single (finProdFinEquiv (d, i))]
    · rw [Matrix.conjTranspose_apply, prependIndexKraus_apply, if_pos rfl, star_one, one_mul]
    · intro p _ hp
      rw [Matrix.conjTranspose_apply, prependIndexKraus_apply, if_neg hp, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q _ hq
    rw [prependIndexKraus_apply, if_neg hq, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## 4. Locality across a two-factor cut

Appending a label to a *joint* register touches only one of the two factors, once the composite
register is regrouped by the canonical value-preserving cast. Which factor is determined by the
digit the label occupies: a low digit is charged to the second factor, a high digit to the first.
-/

/-- **Appending a label to a joint register is a second-factor operation.** Regrouped as
`sA | (sB · D)`, appending the label to the whole `sA · sB` register acts on the second block
alone and leaves the first untouched. -/
theorem castRect_mul_appendIndexKraus (sA sB : ℕ) {D : ℕ} (d : Fin D) :
    castRect (sA * sB * D) (sA * (sB * D)) * appendIndexKraus (sA * sB) d =
      tensorRect (1 : Matrix (Fin sA) (Fin sA) ℂ) (appendIndexKraus sB d) := by
  ext i j
  rw [castRect_mul (Nat.mul_assoc sA sB D)]
  simp only [Matrix.submatrix_apply, id_eq, appendIndexKraus_apply, tensorRect_apply,
    Matrix.one_apply]
  have hpos : 0 < sA * (sB * D) := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hQpos : 0 < sB * D := by
    rcases Nat.eq_zero_or_pos (sB * D) with h | h
    · rw [h, Nat.mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h
  have hsB : 0 < sB := Nat.pos_of_ne_zero fun h => by simp [h] at hQpos
  have hcomm : sB * D = D * sB := Nat.mul_comm sB D
  have hjm : (j : ℕ) % sB < sB := Nat.mod_lt _ hsB
  have hsmall : (d : ℕ) + D * ((j : ℕ) % sB) < sB * D := by
    have hstep : D * ((j : ℕ) % sB) + D ≤ D * sB := by
      calc D * ((j : ℕ) % sB) + D = D * ((j : ℕ) % sB + 1) := by ring
        _ ≤ D * sB := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hjm)
    have hd := d.isLt
    omega
  have hrewrite : (d : ℕ) + D * (j : ℕ) =
      (sB * D) * ((j : ℕ) / sB) + ((d : ℕ) + D * ((j : ℕ) % sB)) := by
    conv_lhs => rw [← Nat.div_add_mod (j : ℕ) sB]
    ring
  have key : ((Fin.cast (Nat.mul_assoc sA sB D).symm i) = finProdFinEquiv (j, d)) ↔
      ((finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 ∧
        ((finProdFinEquiv.symm i).2 : Fin (sB * D))
          = finProdFinEquiv (((finProdFinEquiv.symm j).2 : Fin sB), d)) := by
    simp only [Fin.ext_iff, Fin.val_cast, finProdFinEquiv_val,
      finProdFinEquiv_symm_fst_val, finProdFinEquiv_symm_snd_val]
    rw [hrewrite]
    rw [Nat.div_mod_unique hQpos]
    simp only [hsmall, and_true, Nat.add_comm, eq_comm]
  by_cases hcond : (Fin.cast (Nat.mul_assoc sA sB D).symm i) = finProdFinEquiv (j, d)
  · rw [if_pos hcond]
    obtain ⟨h1, h2⟩ := key.mp hcond
    rw [if_pos h1, if_pos h2, one_mul]
  · rw [if_neg hcond]
    rcases not_and_or.mp (fun h => hcond (key.mpr h)) with h | h
    · rw [if_neg h, zero_mul]
    · rw [if_neg h, mul_zero]

/-- **Prepending a label to a joint register is a first-factor operation.** Regrouped as
`(D · sA) | sB`, prepending the label to the whole `sA · sB` register acts on the first block
alone. This is the mirror of `castRect_mul_appendIndexKraus`. -/
theorem castRect_mul_prependIndexKraus (sA sB : ℕ) {D : ℕ} (d : Fin D) :
    castRect (D * (sA * sB)) (D * sA * sB) * prependIndexKraus (sA * sB) d =
      tensorRect (prependIndexKraus sA d) (1 : Matrix (Fin sB) (Fin sB) ℂ) := by
  ext i j
  rw [castRect_mul (Nat.mul_assoc D sA sB).symm]
  simp only [Matrix.submatrix_apply, id_eq, prependIndexKraus_apply, tensorRect_apply,
    Matrix.one_apply]
  have hpos : 0 < D * sA * sB := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hsB : 0 < sB := by
    rcases Nat.eq_zero_or_pos sB with h | h
    · rw [h, Nat.mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h
  have hjm : (j : ℕ) % sB < sB := Nat.mod_lt _ hsB
  have hrewrite : (j : ℕ) + sA * sB * (d : ℕ) =
      sB * ((j : ℕ) / sB + sA * (d : ℕ)) + (j : ℕ) % sB := by
    conv_lhs => rw [← Nat.div_add_mod (j : ℕ) sB]
    ring
  have key : ((Fin.cast (Nat.mul_assoc D sA sB) i) = finProdFinEquiv (d, j)) ↔
      (((finProdFinEquiv.symm i).1 : Fin (D * sA))
          = finProdFinEquiv (d, ((finProdFinEquiv.symm j).1 : Fin sA)) ∧
        (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2) := by
    simp only [Fin.ext_iff, Fin.val_cast, finProdFinEquiv_val,
      finProdFinEquiv_symm_fst_val, finProdFinEquiv_symm_snd_val]
    rw [hrewrite]
    rw [Nat.div_mod_unique hsB]
    simp only [hjm, and_true, Nat.add_comm, eq_comm]
  by_cases hcond : (Fin.cast (Nat.mul_assoc D sA sB) i) = finProdFinEquiv (d, j)
  · rw [if_pos hcond]
    obtain ⟨h1, h2⟩ := key.mp hcond
    rw [if_pos h1, if_pos h2, mul_one]
  · rw [if_neg hcond]
    rcases not_and_or.mp (fun h => hcond (key.mpr h)) with h | h
    · rw [if_neg h, zero_mul]
    · rw [if_neg h, mul_zero]

/-- Appending two labels successively appends their ordered pair after canonical reassociation. -/
theorem appendIndexKraus_comp (N D c : ℕ) (x : Fin c) (t : Fin D) :
    castRect ((N * D) * c) (N * (D * c)) * appendIndexKraus (N * D) x *
        appendIndexKraus N t = appendIndexKraus N (finProdFinEquiv (t, x)) := by
  rw [Matrix.mul_assoc, castRect_mul (Nat.mul_assoc N D c)]
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, Matrix.mul_apply, appendIndexKraus_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (finProdFinEquiv (j, t))]
  simp only [Finset.mem_univ, if_true]
  refine if_congr ?_ rfl rfl
  simp only [Fin.ext_iff, Fin.val_cast, finProdFinEquiv_val]
  rw [show (x : ℕ) + c * ((t : ℕ) + D * (j : ℕ)) =
      (x : ℕ) + c * (t : ℕ) + D * c * (j : ℕ) by ring]

/-- Appending the unique label is the value-preserving cast to a dimension multiplied by one. -/
theorem appendIndexKraus_one (sB : ℕ) (t : Fin 1) :
    appendIndexKraus sB t = castRect sB (sB * 1) := by
  have ht : (t : ℕ) = 0 := Nat.lt_one_iff.mp t.isLt
  ext i j
  rw [appendIndexKraus_val, castRect_apply, ht, Nat.zero_add, Nat.one_mul]

theorem tensorRect_appendIndexKraus_isometry {rA rB sA sB D : ℕ} (t : Fin D)
    (A : Matrix (Fin sA) (Fin rA) ℂ) (B : Matrix (Fin sB) (Fin rB) ℂ) :
    (tensorRect A (appendIndexKraus sB t * B))ᴴ * tensorRect A (appendIndexKraus sB t * B)
      = (tensorRect A B)ᴴ * tensorRect A B := by
  rw [tensorRect_conjTranspose, tensorRect_mul, tensorRect_conjTranspose, tensorRect_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (appendIndexKraus sB t)ᴴ,
    appendIndexKraus_conjTranspose_mul_self, Matrix.one_mul]

end Quantum.TensorProducts
