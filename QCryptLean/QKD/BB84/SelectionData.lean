import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Lean.Elab.Tactic.Omega
import QCryptLean.QKD.BB84.Constants

/-!
# BB84 round selection

Key-round counts, the permutation placing key rounds before test rounds, and the sizes of the
two test subsamples. The general split accepts an arbitrary test count `m`; the canonical split
(`m = (n + 1) / 2`) is its special case. Neither split adds a correctness assumption on a
selector.
-/

noncomputable section

namespace QKD.BB84.Engine

/-- Number of key rounds after reserving `m` test rounds, using truncated natural subtraction. -/
def bb84KeyRoundCount (n m : ℕ) : ℕ := n - m

/-- **The announced PE-outcome register at a general test-set size `m`**: one `signalDim`-ary
digit per parameter-estimation round, over the split-point-parametrised round partition
`bb84KeyRoundCount n m = n − m`.

This is Nahar et al.'s `\Cat^m` (arXiv:2403.11851, `main.tex:909`); for `m ≤ n` it is
literally `signalDim ^ m`. -/
def bb84PEAnnounceLabelDim (n m : ℕ) : ℕ :=
  signalDim ^ (n - bb84KeyRoundCount n m)


/-- The key-round count never exceeds the block length. -/
lemma bb84KeyRoundCount_le (n m : ℕ) : bb84KeyRoundCount n m ≤ n :=
  Nat.sub_le _ _

/-- **The number of reserved test rounds is `min n m`.**

The split reserves `n - bb84KeyRoundCount n m` rounds for parameter estimation. Because the key
count is the truncated difference `n - m`, that number is `min n m`: it is `m` exactly when
`m ≤ n`, and it saturates at `n` when `m > n`. Every general-`m` construction that loops over the
reserved rounds runs this many times, and no construction is entitled to rewrite the length to
`m` without the hypothesis `m ≤ n`. -/
lemma bb84KeyRoundCount_testCount (n m : ℕ) :
    n - bb84KeyRoundCount n m = min n m := by
  simp only [bb84KeyRoundCount]
  omega

/-- `m + n_K = n` for `m ≤ n` (the PE/key split is well-formed). -/
lemma bb84KeyRoundCount_add (n m : ℕ) (hm : m ≤ n) :
    m + bb84KeyRoundCount n m = n :=
  Nat.add_sub_cancel' hm

/-- At least one key round remains when fewer than `n` rounds are tested. -/
lemma bb84KeyRoundCount_pos {n m : ℕ} (hmn : m < n) : 0 < bb84KeyRoundCount n m := by
  simp only [bb84KeyRoundCount]
  omega

/-- Nonzero key-round count when fewer than `n` rounds are tested. -/
lemma bb84KeyRoundCount_neZero {n m : ℕ} (hmn : m < n) :
    NeZero (bb84KeyRoundCount n m) :=
  ⟨by have := bb84KeyRoundCount_pos hmn; omega⟩

/-- The typeclass form of `bb84KeyRoundCount_neZero`. -/
instance bb84KeyRoundCount_neZero_of_fact (n m : ℕ) [h : Fact (m < n)] :
    NeZero (bb84KeyRoundCount n m) :=
  bb84KeyRoundCount_neZero h.out

/-- Number of key rounds in the canonical split, which tests `(n + 1) / 2` rounds — the
`bb84KeyRoundCount` special case at `m = (n + 1) / 2`. -/
def bb84KeyRoundCountCanonical (n : ℕ) : ℕ := bb84KeyRoundCount n ((n + 1) / 2)

/-- The key-round count never exceeds the block length. -/
lemma bb84KeyRoundCountCanonical_le (n : ℕ) : bb84KeyRoundCountCanonical n ≤ n :=
  Nat.sub_le _ _

/-- `n_K = ⌊n/2⌋`. -/
lemma bb84KeyRoundCountCanonical_eq_div_two (n : ℕ) : bb84KeyRoundCountCanonical n = n / 2 := by
  rw [bb84KeyRoundCountCanonical, bb84KeyRoundCount]; omega

/-! ## Key-first ordering -/

/-- The permutation placing key rounds (`peSel = false`) before test rounds. -/
def bb84PeSelSort {n : ℕ} (peSel : Fin n → Bool) : Equiv.Perm (Fin n) := Tuple.sort peSel

/-- After sorting, `peSel ∘ bb84PeSelSort peSel` is monotone (key rounds first). -/
lemma bb84PeSelSort_monotone {n : ℕ} (peSel : Fin n → Bool) :
    Monotone (peSel ∘ ⇑(bb84PeSelSort peSel)) :=
  Tuple.monotone_sort peSel

/-- The number of key rounds (`peSel = false`) is preserved by the sort. -/
lemma bb84PeSelSort_keyCount {n : ℕ} (peSel : Fin n → Bool) :
    Fintype.card { i // (peSel ∘ ⇑(bb84PeSelSort peSel)) i = false } =
      Fintype.card { i // peSel i = false } :=
  Fintype.card_congr (Equiv.subtypeEquiv (Tuple.sort peSel) (fun i => by simp [bb84PeSelSort]))

/-- **Threshold characterization of the sort.**  After sorting, round `j` is a key round
(`peSel = false`) exactly when `j` lies in the prefix `[0, #key)`. -/
lemma bb84PeSelSort_isKey_iff {n : ℕ} (peSel : Fin n → Bool) (j : Fin n) :
    peSel (bb84PeSelSort peSel j) = false ↔
      (j : ℕ) < Fintype.card { i // peSel i = false } := by
  have hbf : ∀ b : Bool, (b ≤ false) ↔ (b = false) := fun b => by cases b <;> simp
  have h := Tuple.lt_card_le_iff_apply_le_of_monotone (f := peSel ∘ ⇑(bb84PeSelSort peSel))
    (a := false) (j := j) (bb84PeSelSort_monotone peSel)
  rw [← Fintype.card_subtype] at h
  have hcard : Fintype.card { i // (peSel ∘ ⇑(bb84PeSelSort peSel)) i ≤ false } =
      Fintype.card { i // peSel i = false } := by
    rw [← bb84PeSelSort_keyCount peSel]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => hbf _))
  rw [hcard, hbf] at h
  exact h.symm

/-! ## Sorted test-round indices, at a general test-set size `m` -/

/-- `n_K + (n − n_K) = n` at a general test-set size `m` (the key-rounds-first split is
well-formed). -/
lemma bb84KeyRoundCount_add' (n m : ℕ) :
    bb84KeyRoundCount n m + (n - bb84KeyRoundCount n m) = n :=
  Nat.add_sub_cancel' (bb84KeyRoundCount_le n m)

/-- The `j`-th **sorted PE round** index at a general test-set size `m`: the round occupying the
`j`-th position of the PE-rounds suffix `[n_K, n)`. -/
def bb84PERoundIdx {n m : ℕ} (peSel : Fin n → Bool)
    (j : Fin (n - bb84KeyRoundCount n m)) : Fin n :=
  bb84PeSelSort peSel
    (Fin.cast (bb84KeyRoundCount_add' n m) (Fin.natAdd (bb84KeyRoundCount n m) j))

/-! ## Sorted test-round indices, at the canonical test-set size -/

/-- `n_K + (n − n_K) = n` at the canonical test-set size (the key-rounds-first split is
well-formed) — the `bb84KeyRoundCount_add'` special case at `m = (n + 1) / 2`. -/
lemma bb84KeyRoundCountCanonical_add (n : ℕ) :
    bb84KeyRoundCountCanonical n + (n - bb84KeyRoundCountCanonical n) = n :=
  bb84KeyRoundCount_add' n ((n + 1) / 2)

/-- The `j`-th **sorted PE round** index at the canonical test-set size — the `bb84PERoundIdx`
special case at `m = (n + 1) / 2`. -/
def bb84PERoundIdxCanonical {n : ℕ} (peSel : Fin n → Bool)
    (j : Fin (n - bb84KeyRoundCountCanonical n)) : Fin n :=
  bb84PERoundIdx (m := (n + 1) / 2) peSel j

/-! ## Test subsample sizes -/

/-- Z-test subsample size. -/
def bb84SiftedZTestSampleSize {n : ℕ} (peSel xSel : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => peSel i = true ∧ xSel i = false)).card

/-- X-test subsample size. -/
def bb84SiftedXTestSampleSize {n : ℕ} (peSel xSel : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => peSel i = true ∧ xSel i = true)).card

/-! ## The round-outcome partition equivalence, at a general test-set size `m`

Moved here from `QKD.BB84.Engine.EntropyFloor.SiftedRoundFactorizationReferee`: this is pure
round-selection combinatorics built only on the definitions above, consumed by both the Model and
the Engine layers, so it belongs with `bb84KeyRoundCount`/`bb84PERoundIdx` rather than inside one
Engine analysis file. -/

/-- The `i`-th **sorted key round** index at a general test-set size `m` (mirror of
`bb84PERoundIdx`). -/
def bb84KeyRoundIdx {n m : ℕ} (peSel : Fin n → Bool)
    (i : Fin (bb84KeyRoundCount n m)) : Fin n :=
  bb84PeSelSort peSel
    (Fin.cast (bb84KeyRoundCount_add' n m) (Fin.castAdd (n - bb84KeyRoundCount n m) i))

/-- The count hypothesis at a general test-set size `m`: there are exactly
`n_K = bb84KeyRoundCount n m = n − m` key rounds. -/
abbrev bb84KeyCount (n m : ℕ) (peSel : Fin n → Bool) : Prop :=
  Fintype.card { i // peSel i = false } = bb84KeyRoundCount n m

/-- A sorted key round is a key round (`peSel = false`). -/
lemma bb84KeyRoundIdx_isKey {n m : ℕ} (peSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (i : Fin (bb84KeyRoundCount n m)) :
    peSel (bb84KeyRoundIdx peSel i) = false := by
  rw [bb84KeyRoundIdx, bb84PeSelSort_isKey_iff, hcount]
  exact i.isLt

/-- A sorted PE round is a PE round (`peSel = true`). -/
lemma bb84PERoundIdx_isPE {n m : ℕ} (peSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (j : Fin (n - bb84KeyRoundCount n m)) :
    peSel (bb84PERoundIdx peSel j) = true := by
  have h : ¬ (peSel (bb84PERoundIdx peSel j) = false) := by
    rw [bb84PERoundIdx, bb84PeSelSort_isKey_iff, hcount, not_lt]
    exact Nat.le_add_right _ _
  simpa using h

/-- The combined sorted-round bijection at a general test-set size `m`:
`Fin n_K ⊕ Fin (n − n_K) ≃ Fin n`. -/
def bb84RoundEquiv {n m : ℕ} (peSel : Fin n → Bool) :
    Fin (bb84KeyRoundCount n m) ⊕ Fin (n - bb84KeyRoundCount n m) ≃ Fin n :=
  finSumFinEquiv.trans ((finCongr (bb84KeyRoundCount_add' n m)).trans (bb84PeSelSort peSel))

@[simp] lemma bb84RoundEquiv_inl {n m : ℕ} (peSel : Fin n → Bool)
    (i : Fin (bb84KeyRoundCount n m)) :
    bb84RoundEquiv (m := m) peSel (Sum.inl i) = bb84KeyRoundIdx peSel i := by
  simp only [bb84RoundEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply]
  rfl

@[simp] lemma bb84RoundEquiv_inr {n m : ℕ} (peSel : Fin n → Bool)
    (j : Fin (n - bb84KeyRoundCount n m)) :
    bb84RoundEquiv (m := m) peSel (Sum.inr j) = bb84PERoundIdx peSel j := by
  simp only [bb84RoundEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply]
  rfl

/-- The **partition equivalence** of the round-outcome register at a general test-set size `m`. -/
def bb84PartEquiv {n m : ℕ} (peSel : Fin n → Bool) :
    (Fin n → Fin signalDim) ≃
      (Fin (bb84KeyRoundCount n m) → Fin signalDim) ×
        (Fin (n - bb84KeyRoundCount n m) → Fin signalDim) :=
  (Equiv.arrowCongr (bb84RoundEquiv (m := m) peSel) (Equiv.refl (Fin signalDim))).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] lemma bb84PartEquiv_apply_fst {n m : ℕ} (peSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) (i : Fin (bb84KeyRoundCount n m)) :
    (bb84PartEquiv (m := m) peSel ω).1 i = ω (bb84KeyRoundIdx peSel i) := by
  simp only [bb84PartEquiv, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl,
    Function.comp_apply, id_eq, Equiv.symm_symm, bb84RoundEquiv_inl]

@[simp] lemma bb84PartEquiv_apply_snd {n m : ℕ} (peSel : Fin n → Bool)
    (ω : Fin n → Fin signalDim) (j : Fin (n - bb84KeyRoundCount n m)) :
    (bb84PartEquiv (m := m) peSel ω).2 j = ω (bb84PERoundIdx peSel j) := by
  simp only [bb84PartEquiv, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_snd,
    Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl,
    Function.comp_apply, id_eq, Equiv.symm_symm, bb84RoundEquiv_inr]

@[simp] lemma bb84PartEquiv_symm_apply_keyIdx {n m : ℕ} (peSel : Fin n → Bool)
    (k : Fin (bb84KeyRoundCount n m) → Fin signalDim)
    (q : Fin (n - bb84KeyRoundCount n m) → Fin signalDim)
    (i : Fin (bb84KeyRoundCount n m)) :
    (bb84PartEquiv (m := m) peSel).symm (k, q) (bb84KeyRoundIdx peSel i) = k i := by
  simp only [bb84PartEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_apply,
    Equiv.coe_refl, Function.comp_apply, id_eq]
  rw [show bb84KeyRoundIdx peSel i = bb84RoundEquiv (m := m) peSel (Sum.inl i) from
        (bb84RoundEquiv_inl peSel i).symm, Equiv.symm_apply_apply,
    Equiv.sumArrowEquivProdArrow_symm_apply_inl]

@[simp] lemma bb84PartEquiv_symm_apply_peIdx {n m : ℕ} (peSel : Fin n → Bool)
    (k : Fin (bb84KeyRoundCount n m) → Fin signalDim)
    (q : Fin (n - bb84KeyRoundCount n m) → Fin signalDim)
    (j : Fin (n - bb84KeyRoundCount n m)) :
    (bb84PartEquiv (m := m) peSel).symm (k, q) (bb84PERoundIdx peSel j) = q j := by
  simp only [bb84PartEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_apply,
    Equiv.coe_refl, Function.comp_apply, id_eq]
  rw [show bb84PERoundIdx peSel j = bb84RoundEquiv (m := m) peSel (Sum.inr j) from
        (bb84RoundEquiv_inr peSel j).symm, Equiv.symm_apply_apply,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]

/-- Every PE round (`peSel a = true`) is a sorted PE round. -/
lemma bb84_peRound_eq_peIdx {n m : ℕ} (peSel : Fin n → Bool) (hcount : bb84KeyCount n m peSel)
    (a : Fin n) (ha : peSel a = true) :
    ∃ j, a = bb84PERoundIdx (m := m) peSel j := by
  rcases hsum : (bb84RoundEquiv (m := m) peSel).symm a with i | j
  · exfalso
    have : a = bb84KeyRoundIdx peSel i := by
      rw [← bb84RoundEquiv_inl peSel i, ← hsum, Equiv.apply_symm_apply]
    rw [this, bb84KeyRoundIdx_isKey peSel hcount i] at ha
    exact Bool.noConfusion ha
  · exact ⟨j, by rw [← bb84RoundEquiv_inr peSel j, ← hsum, Equiv.apply_symm_apply]⟩

end QKD.BB84.Engine
