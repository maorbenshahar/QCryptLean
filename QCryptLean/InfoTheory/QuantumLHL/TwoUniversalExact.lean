import QCryptLean.InfoTheory.QuantumLHL.ScalarTwoUniversalL2

/-!
# Exact (2*-universal) hash families and the centred second-moment identity

This module introduces the **exact-collision** (`2*`-universal) predicate for a
`QuantumHashFamily`, strengthening the `≤`-form `isUniversal`
(Tomamichel 2016, §7.3, eq. 7.31) to a Nat *equality*:
```
  |{s : H.hash s x = H.hash s x'}| · |Z| = |S|   (for x ≠ x').
```

The exactness is what makes the **centred second-moment (decoupling) identity**
true for *arbitrary* complex matrix-valued `V` (no positivity / Hermitian
assumption): the centred off-diagonal collision coefficient
`(1/|S|)·|{s : H.hash s x = H.hash s x'}| − 1/|Z|` is forced to be *exactly* `0`,
cancelling the arbitrary-sign Hilbert–Schmidt cross terms `⟨V x, V x'⟩` without
any sign argument.

## Main declarations
- `QuantumHashFamily.IsUniversal2Star` — the Nat-equality predicate.
- `QuantumHashFamily.IsUniversal2Star.isUniversal` — exact ⇒ `≤` (2-universal).
- `QuantumHashFamily.IsUniversal2Star.centred_second_moment` — the centred
  second-moment identity for arbitrary `V : X → Op n`.
-/

open Quantum.Operators Matrix

noncomputable section

namespace InfoTheory.QuantumLHL

/-- **Exact (`2*`-universal) collision predicate.** For any two distinct inputs
`x ≠ x'`, the number of seeds on which they collide, times `|Z|`, equals `|S|`
(equality, not merely `≤`). This holds for affine/linear universal families and
is what forces the centred off-diagonal coefficient to vanish exactly. -/
def QuantumHashFamily.IsUniversal2Star {S X Z : Type*} [Fintype S] [Fintype Z]
    [DecidableEq Z] (H : QuantumHashFamily S X Z) : Prop :=
  ∀ x x' : X, x ≠ x' →
    (Finset.univ.filter (fun s => H.hash s x = H.hash s x')).card * Fintype.card Z
      = Fintype.card S

/-- **Exact ⇒ 2-universal.** Dividing the Nat equality by `|Z| > 0` gives the
`≤`-form collision bound `isUniversal` (Tomamichel eq. 7.31). -/
lemma QuantumHashFamily.IsUniversal2Star.isUniversal {S X Z : Type*} [Fintype S]
    [Fintype Z] [DecidableEq Z] {H : QuantumHashFamily S X Z}
    (h : H.IsUniversal2Star) : H.isUniversal := by
  have : Nonempty Z := H.outputNonempty
  intro x x' hxx'
  have hZ_pos : 0 < (Fintype.card Z : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
  have hcard := h x x' hxx'
  have hR : ((Finset.univ.filter (fun s => H.hash s x = H.hash s x')).card : ℝ)
      * (Fintype.card Z : ℝ) = (Fintype.card S : ℝ) := by
    exact_mod_cast hcard
  rw [le_div_iff₀ hZ_pos]
  exact le_of_eq hR

/-- **Hilbert–Schmidt bilinear expansion.** For real coefficients `a : X → ℝ`
and matrices `V : X → Op n`,
```
  ‖∑ x, a x • V x‖_F²
    = ∑ x, ∑ x', (a x · a x') · ((V x)ᴴ * V x').trace.re.
```
Pure trace algebra (no positivity). -/
private lemma hs_bilin_expand {X : Type*} [Fintype X] {n : ℕ}
    (a : X → ℝ) (V : X → Op n) :
    (((∑ x : X, (a x : ℂ) • V x)ᴴ) * (∑ x : X, (a x : ℂ) • V x)).trace.re
      = ∑ x : X, ∑ x' : X, a x * a x' * (((V x)ᴴ) * (V x')).trace.re := by
  rw [Matrix.conjTranspose_sum]
  rw [Finset.sum_mul_sum]
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, smul_eq_mul]
  have hstar : star (a x : ℂ) = (a x : ℂ) := Complex.conj_ofReal (a x)
  rw [hstar, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

/-- **Centred second-moment (decoupling) identity.** For an exact
(`2*`-universal) family `H` and *arbitrary* complex matrix-valued `V : X → Op n`
(no PSD/Hermitian assumption), with `c := 1/|Z|` and `Vtot := ∑ x, V x`,
```
  (1/|S|) · ∑ s, ∑ m, ‖(∑_{x : H.hash s x = m} V x) − c • Vtot‖_F²
    = (1 − c) · ∑ x, ‖V x‖_F².
```
The exactness hypothesis forces the centred off-diagonal collision coefficient
to be exactly `0`, cancelling the arbitrary-sign HS cross terms without any
positivity argument. -/
lemma QuantumHashFamily.IsUniversal2Star.centred_second_moment {S X Z : Type*}
    [Fintype S] [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {n : ℕ}
    {H : QuantumHashFamily S X Z} (h2 : H.IsUniversal2Star) (V : X → Op n) :
    (1 / (Fintype.card S : ℝ)) * ∑ s : S, ∑ m : Z,
        (let W := (∑ x : X, if H.hash s x = m then V x else 0)
            - (1 / (Fintype.card Z : ℝ)) • (∑ x : X, V x);
          (Wᴴ * W).trace.re)
      = (1 - 1 / (Fintype.card Z : ℝ)) *
          ∑ x : X, (((V x)ᴴ) * (V x)).trace.re := by
  have : Nonempty Z := H.outputNonempty
  have : Nonempty S := H.seedNonempty
  simp only []
  set c : ℝ := 1 / (Fintype.card Z : ℝ) with hc_def
  have hS_pos : 0 < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  set K : X → X → ℝ := fun x x' => (((V x)ᴴ) * (V x')).trace.re with hK_def
  set e : S → X → Z → ℝ := fun s x m => (if H.hash s x = m then (1:ℝ) else 0) - c
    with he_def
  -- Step 1&2: rewrite each inner Frobenius square as an HS bilinear collision sum.
  have hInner : ∀ (s : S) (m : Z),
      (((∑ x : X, if H.hash s x = m then V x else 0) - c • (∑ x : X, V x))ᴴ *
        ((∑ x : X, if H.hash s x = m then V x else 0) - c • (∑ x : X, V x))).trace.re
      = ∑ x : X, ∑ x' : X, e s x m * e s x' m * K x x' := by
    intro s m
    have hWrw : (∑ x : X, if H.hash s x = m then V x else 0) - c • (∑ x : X, V x)
        = ∑ x : X, ((e s x m : ℝ) : ℂ) • V x := by
      have hpt : ∀ x : X, ((e s x m : ℝ) : ℂ) • V x
          = (if H.hash s x = m then V x else 0) - (c : ℂ) • V x := by
        intro x
        simp only [he_def]
        by_cases hx : H.hash s x = m
        · simp [hx, sub_smul]
        · simp [hx]
      rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib,
        ← Finset.smul_sum, Complex.coe_smul]
    rw [hWrw, hs_bilin_expand]
  -- Coefficient identity via the centred Gram identity (B1c).
  have hP : ∀ x x' : X, (∑ s : S, ∑ m : Z, e s x m * e s x' m)
      = ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
          - (Fintype.card S : ℝ) * c := by
    intro x x'
    simp only [he_def]
    exact (collision_count_sub_eq_double_sum_centred H x x').symm
  -- Reorder the fourfold sum (move `(x, x')` outermost) and factor `K` out.
  have hswap : ∀ F : S → Z → X → X → ℝ,
      (∑ s : S, ∑ m : Z, ∑ x : X, ∑ x' : X, F s m x x')
        = ∑ x : X, ∑ x' : X, ∑ s : S, ∑ m : Z, F s m x x' := by
    intro F
    have step1 : (∑ s : S, ∑ m : Z, ∑ x : X, ∑ x' : X, F s m x x')
        = ∑ s : S, ∑ x : X, ∑ m : Z, ∑ x' : X, F s m x x' :=
      Finset.sum_congr rfl fun s _ => Finset.sum_comm
    have step2 : (∑ s : S, ∑ x : X, ∑ m : Z, ∑ x' : X, F s m x x')
        = ∑ x : X, ∑ s : S, ∑ m : Z, ∑ x' : X, F s m x x' :=
      Finset.sum_comm
    have step3 : (∑ x : X, ∑ s : S, ∑ m : Z, ∑ x' : X, F s m x x')
        = ∑ x : X, ∑ s : S, ∑ x' : X, ∑ m : Z, F s m x x' :=
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun s _ => Finset.sum_comm
    have step4 : (∑ x : X, ∑ s : S, ∑ x' : X, ∑ m : Z, F s m x x')
        = ∑ x : X, ∑ x' : X, ∑ s : S, ∑ m : Z, F s m x x' :=
      Finset.sum_congr rfl fun x _ => Finset.sum_comm
    rw [step1, step2, step3, step4]
  have hReorder :
      (∑ s : S, ∑ m : Z, ∑ x : X, ∑ x' : X, e s x m * e s x' m * K x x')
      = ∑ x : X, ∑ x' : X, (∑ s : S, ∑ m : Z, e s x m * e s x' m) * K x x' := by
    rw [hswap (fun s m x x' => e s x m * e s x' m * K x x')]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
  -- Diagonal/off-diagonal split of the centred collision coefficient.
  have hsplit : ∀ x x' : X,
      (1 / (Fintype.card S : ℝ)) *
        ((((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
            - (Fintype.card S : ℝ) * c) * K x x')
        = (if x = x' then (1 - c) * K x x else 0) := by
    intro x x'
    by_cases hxx' : x = x'
    · subst hxx'
      have hfilter :
          (Finset.univ.filter (fun s : S => H.hash s x = H.hash s x))
            = (Finset.univ : Finset S) :=
        Finset.filter_true_of_mem (fun _ _ => rfl)
      rw [hfilter, Finset.card_univ, ite_eq_left rfl]
      rw [show (1 / (Fintype.card S : ℝ)) *
              (((Fintype.card S : ℝ) - (Fintype.card S : ℝ) * c) * K x x)
            = ((1 / (Fintype.card S : ℝ)) * (Fintype.card S : ℝ)) * (1 - c) * K x x from by
        ring]
      rw [one_div_mul_cancel hS_ne, one_mul]
    · rw [ite_eq_right hxx']
      have hex := h2 x x' hxx'
      have hcardR :
          ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
            * (Fintype.card Z : ℝ) = (Fintype.card S : ℝ) := by exact_mod_cast hex
      have hZ_pos : 0 < (Fintype.card Z : ℝ) := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
      have hcard_eq :
          ((Finset.univ.filter (fun s : S => H.hash s x = H.hash s x')).card : ℝ)
            = (Fintype.card S : ℝ) * c := by
        rw [hc_def]
        field_simp
        linarith [hcardR]
      rw [hcard_eq]; ring
  -- Assemble.
  rw [Finset.sum_congr rfl (fun s _ =>
        Finset.sum_congr rfl (fun m _ => hInner s m))]
  rw [hReorder]
  rw [Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun x' _ => by rw [hP x x']))]
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => by rw [Finset.mul_sum])]
  rw [Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun x' _ => hsplit x x'))]
  -- Collapse the diagonal.
  have hdiag : ∀ x : X, (∑ x' : X, if x = x' then (1 - c) * K x x else 0)
      = (1 - c) * K x x := fun x => by simp
  rw [Finset.sum_congr rfl (fun x _ => hdiag x), ← Finset.mul_sum]

end InfoTheory.QuantumLHL

end -- noncomputable section
