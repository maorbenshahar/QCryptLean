import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Mixed-radix finite indices

Digit decompositions for `finPiFinEquiv` and the effect of updating the lowest radix.
-/

open scoped BigOperators

variable {k : ℕ}

/-- Factor `0` is the low digit of `finPiFinEquiv`: the index of a digit tuple is its digit `0` plus
`m 0` times the index of the remaining digits. -/
theorem finPiFinEquiv_succ_val {m : Fin (k + 1) → ℕ} (f : ∀ j, Fin (m j)) :
    (finPiFinEquiv f : ℕ) =
      (f 0 : ℕ) + m 0 * (finPiFinEquiv (n := fun j : Fin k => m j.succ) fun j => f j.succ : ℕ) := by
  rw [finPiFinEquiv_apply, finPiFinEquiv_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero]
  simp only [Fintype.prod_empty, Nat.mul_one]
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  change (f i.succ : ℕ) *
      (∏ j : Fin (i.val + 1), m (Fin.castLE (Fin.is_lt (Fin.succ i)).le j)) = _
  rw [Fin.prod_univ_succ]
  have h0 : (Fin.castLE (Fin.is_lt (Fin.succ i)).le (0 : Fin ((i : ℕ) + 1))) = 0 := Fin.ext rfl
  have hrest : ∀ j : Fin (i : ℕ),
      m (Fin.castLE (Fin.is_lt (Fin.succ i)).le (Fin.succ j)) =
        m (Fin.succ (Fin.castLE (Fin.is_lt i).le j)) := fun j => congrArg m (Fin.ext rfl)
  rw [h0, Finset.prod_congr rfl fun j _ => hrest j]
  ring

/-- The last factor is the high digit of `finPiFinEquiv`: the index of a digit tuple is the index
of its first `k` digits plus `∏ j < k, m j` times its last digit. -/
theorem finPiFinEquiv_castSucc_val {m : Fin (k + 1) → ℕ} (f : ∀ j, Fin (m j)) :
    (finPiFinEquiv f : ℕ) =
      (finPiFinEquiv (n := fun j : Fin k => m j.castSucc) fun j => f j.castSucc : ℕ) +
        (∏ j : Fin k, m j.castSucc) * (f (Fin.last k) : ℕ) := by
  rw [finPiFinEquiv_apply, finPiFinEquiv_apply, Fin.sum_univ_castSucc]
  exact congrArg₂ (· + ·) rfl (Nat.mul_comm _ _)

/-- Splitting off the low digit `0`: in `Fin ((∏ j : Fin k, m j.succ) * m 0)` the index of a digit
tuple is the pair of the index of its remaining digits and its digit `0`. -/
theorem finProdFinEquiv_symm_cast_finPiFinEquiv_succ {m : Fin (k + 1) → ℕ}
    (f : ∀ j, Fin (m j)) (h : ∏ j, m j = (∏ j : Fin k, m j.succ) * m 0) :
    finProdFinEquiv.symm (Fin.cast h (finPiFinEquiv f)) =
      (finPiFinEquiv (n := fun j : Fin k => m j.succ) (fun j => f j.succ), f 0) := by
  rw [Equiv.symm_apply_eq, Fin.ext_iff, Fin.val_cast, finProdFinEquiv_apply_val,
    finPiFinEquiv_succ_val]

/-- Splitting off the high digit, the last one: in
`Fin (m (Fin.last k) * ∏ j : Fin k, m j.castSucc)` the index of a digit tuple is the pair of its
last digit and the index of its first `k` digits. -/
theorem finProdFinEquiv_symm_cast_finPiFinEquiv_castSucc {m : Fin (k + 1) → ℕ}
    (f : ∀ j, Fin (m j)) (h : ∏ j, m j = m (Fin.last k) * ∏ j : Fin k, m j.castSucc) :
    finProdFinEquiv.symm (Fin.cast h (finPiFinEquiv f)) =
      (f (Fin.last k),
        finPiFinEquiv (n := fun j : Fin k => m j.castSucc) fun j => f j.castSucc) := by
  rw [Equiv.symm_apply_eq, Fin.ext_iff, Fin.val_cast, finProdFinEquiv_apply_val,
    finPiFinEquiv_castSucc_val]

/-- With a common digit range, `finPiFinEquiv` is `finFunctionFinEquiv` up to the cast
`∏ j, a = a ^ k`. -/
theorem cast_finPiFinEquiv_const {a : ℕ} (f : Fin k → Fin a) :
    Fin.cast (Fin.prod_const k a) (finPiFinEquiv f) = finFunctionFinEquiv f := by
  ext
  simp [finPiFinEquiv_apply]

variable [NeZero k]

/-- Multiplying the value at index zero by `D` multiplies the product by `D`. -/
theorem prod_update_zero_mul (n : Fin k → ℕ) (D : ℕ) :
    ∏ j, Function.update n 0 (n 0 * D) j = (∏ j, n j) * D := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  rw [Fin.prod_univ_succ (f := fun j => Function.update n 0 (n 0 * D) j),
    Fin.prod_univ_succ (f := fun j => n j), Function.update_self,
    Finset.prod_congr rfl
      (fun j (_ : j ∈ Finset.univ) => Function.update_of_ne (Fin.succ_ne_zero j) _ _)]
  ring

/-- Updating the lowest radix by a factor `c` sends the encoded index `J` to `x + c * J`
exactly when the lowest digit changes by the same formula and all other digits stay fixed. -/
theorem finPiFinEquiv_update_zero_mul_iff (n : Fin k → ℕ) (D c x : ℕ) (hx : x < c)
    (I : Fin (∏ j, Function.update n 0 (n 0 * (D * c)) j))
    (J : Fin (∏ j, Function.update n 0 (n 0 * D) j)) :
    ((I : ℕ) = x + c * (J : ℕ))
      ↔ ((finPiFinEquiv.symm I 0 : ℕ) = x + c * (finPiFinEquiv.symm J 0 : ℕ)
          ∧ ∀ j : Fin k, j ≠ 0 →
              (finPiFinEquiv.symm I j : ℕ) = (finPiFinEquiv.symm J j : ℕ)) := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  set gI : ∀ j : Fin k', Fin (n j.succ) := fun j =>
    Fin.cast (Function.update_of_ne (Fin.succ_ne_zero j) _ _)
      (finPiFinEquiv.symm I j.succ) with hgI
  set gJ : ∀ j : Fin k', Fin (n j.succ) := fun j =>
    Fin.cast (Function.update_of_ne (Fin.succ_ne_zero j) _ _)
      (finPiFinEquiv.symm J j.succ) with hgJ
  have hI : (I : ℕ) = (finPiFinEquiv.symm I 0 : ℕ)
      + (n 0 * (D * c)) * (finPiFinEquiv gI : ℕ) := by
    conv_lhs =>
      rw [← Equiv.apply_symm_apply (finPiFinEquiv (n := Function.update n 0 (n 0 * (D * c)))) I]
    rw [finPiFinEquiv_succ_val]
    refine congrArg₂ _ rfl (congrArg₂ _ (by simp) ?_)
    rw [finPiFinEquiv_apply, finPiFinEquiv_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine congrArg₂ _ ?_ ?_
    · simp only [hgI, Fin.val_cast]
    · exact Finset.prod_congr rfl fun j _ =>
        Function.update_of_ne (Fin.succ_ne_zero _) _ _
  have hJ : (J : ℕ) = (finPiFinEquiv.symm J 0 : ℕ)
      + (n 0 * D) * (finPiFinEquiv gJ : ℕ) := by
    conv_lhs => rw [← Equiv.apply_symm_apply (finPiFinEquiv (n := Function.update n 0 (n 0 * D))) J]
    rw [finPiFinEquiv_succ_val]
    refine congrArg₂ _ rfl (congrArg₂ _ (by simp) ?_)
    rw [finPiFinEquiv_apply, finPiFinEquiv_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine congrArg₂ _ ?_ ?_
    · simp only [hgJ, Fin.val_cast]
    · exact Finset.prod_congr rfl fun j _ => Function.update_of_ne (Fin.succ_ne_zero _) _ _
  have ha0 : (finPiFinEquiv.symm I 0 : ℕ) < n 0 * (D * c) :=
    lt_of_lt_of_eq (finPiFinEquiv.symm I 0).isLt (Function.update_self _ _ _)
  have hb0 : (finPiFinEquiv.symm J 0 : ℕ) < n 0 * D :=
    lt_of_lt_of_eq (finPiFinEquiv.symm J 0).isLt (Function.update_self _ _ _)
  have hQpos : 0 < n 0 * (D * c) := Nat.lt_of_le_of_lt (Nat.zero_le _) ha0
  have hbound : x + c * (finPiFinEquiv.symm J 0 : ℕ) < n 0 * (D * c) := by
    calc x + c * (finPiFinEquiv.symm J 0 : ℕ) < c + c * (finPiFinEquiv.symm J 0 : ℕ) := by omega
      _ = c * ((finPiFinEquiv.symm J 0 : ℕ) + 1) := by ring
      _ ≤ c * (n 0 * D) := Nat.mul_le_mul_left _ hb0
      _ = n 0 * (D * c) := by ring
  have key : ∀ u v : ℕ, u < n 0 * (D * c) →
      ((u + (n 0 * (D * c)) * v) / (n 0 * (D * c)) = v
        ∧ (u + (n 0 * (D * c)) * v) % (n 0 * (D * c)) = u) := by
    intro u v hu
    exact (Nat.div_mod_unique hQpos).2 ⟨rfl, hu⟩
  have htail : ((finPiFinEquiv gI : ℕ) = (finPiFinEquiv gJ : ℕ))
      ↔ ∀ j : Fin (k' + 1), j ≠ 0 →
          (finPiFinEquiv.symm I j : ℕ) = (finPiFinEquiv.symm J j : ℕ) := by
    constructor
    · intro hT j hj
      have hgg : gI = gJ := finPiFinEquiv.injective (Fin.ext hT)
      obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hj
      have := congrFun hgg j'
      simpa [hgI, hgJ] using congrArg (Fin.val) this
    · intro hd
      have hgg : gI = gJ := by
        funext j
        exact Fin.ext (by simpa [hgI, hgJ] using hd j.succ (Fin.succ_ne_zero j))
      rw [hgg]
  rw [hI, hJ]
  constructor
  · intro heq
    have heq' : (finPiFinEquiv.symm I 0 : ℕ) + (n 0 * (D * c)) * (finPiFinEquiv gI : ℕ)
        = (x + c * (finPiFinEquiv.symm J 0 : ℕ))
          + (n 0 * (D * c)) * (finPiFinEquiv gJ : ℕ) := by
      rw [heq]; ring
    obtain ⟨hdI, hmI⟩ := key _ (finPiFinEquiv gI : ℕ) ha0
    obtain ⟨hdJ, hmJ⟩ := key _ (finPiFinEquiv gJ : ℕ) hbound
    refine ⟨?_, htail.mp ?_⟩
    · rw [← hmI, ← hmJ, heq']
    · rw [← hdI, ← hdJ, heq']
  · rintro ⟨h0, hrest⟩
    rw [h0, ← htail.mpr hrest]
    ring

