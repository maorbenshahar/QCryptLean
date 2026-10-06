import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.Quantum.Operators.InverseSqrt
import QCryptLean.Quantum.Operators.HermitianTraceSq

/-!
# Single-σ analogues of the 2-universality collision bound

This helper module isolates the "single-σ⁻¹" combinatorial sub-steps for
the trace form `(S · A · B · S).trace.re` (in contrast to the double-σ form
`((S·A·S)·(S·B·S)).trace.re` used by `LambdaBoundTwoUniversal.lean`).

## Main statements (this file)

- `tr_S_avg_sq_S_le_avg_tr_S_sq_S`: real-valued Jensen for the PSD bilinear
  form `(X, Y) ↦ Tr(S·X·Y·S).re`.

- `sum_tr_SMzsqS_le_seed_avg_collision_sum_single`: single-σ analogue of
  `sum_tr_SMzS_sq_le_seed_avg_collision_sum`, combining per-z Jensen with the
  per-seed collision expansion.

- `sum_tr_SDsqS_eq_sum_tr_SMzsqS_sub_uniform`: D² expansion identity converting
  the per-block "difference square" sum into the per-block "M-square" sum minus
  a uniform-marginal correction.

- `per_seed_collision_identity_single`: abstract per-seed collision identity
  (bilinearity + indicator collapse).

- `sum_pair_tr_S_RR_S_eq_marginal_sq`: bilinearity equality
  `∑_{x,x'} Tr(S·R_x·R_{x'}·S).re = Tr(S·(∑_x R_x)²·S).re`.

- `sum_offdiag_tr_S_rhoxrhoxp_S_le_sq_marginal_single`: auxiliary bilinearity
  bound `∑_{x≠x'} (S·ρ_x·ρ_{x'}·S).trace.re ≤ (S·ρ_A·ρ_A·S).trace.re`.

## References

Tomamichel 2016, Prop 7.1, eq. 7.38–7.40 (single-σ form).
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- Restated for local use to avoid an import cycle with the double-σ
helper module. The proof is the same as `Finset.sum_sum_eq_diag_add_offdiag`
in `LambdaBoundTwoUniversal.lean`; this is a verbatim re-statement, not a
re-derivation. -/
private lemma diag_offdiag_split
    {α β : Type*} [AddCommMonoid β] [DecidableEq α] [Fintype α] (f : α → α → β) :
    (∑ x : α, ∑ x' : α, f x x') =
      (∑ x : α, f x x) +
        (∑ x : α, ∑ x' : α, (if x ≠ x' then f x x' else 0)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdiag : f x x = ∑ x' : α, if x = x' then f x x' else 0 := by
    rw [Finset.sum_ite_eq Finset.univ x (fun x' => f x x'),
      if_pos (Finset.mem_univ x)]
  rw [hdiag, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x' _ => ?_
  by_cases h : x = x' <;> simp [h]

/-- Bilinearity expansion of an `S`-sandwiched product of two sums:
`S · (∑ x, f x) · (∑ y, g y) · S = ∑ x, ∑ y, S · f x · g y · S`. -/
private lemma sandwich_sum_mul_sum
    {n : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (S : Op n) (f : X → Op n) (g : Y → Op n) :
    S * (∑ x : X, f x) * (∑ y : Y, g y) * S =
      ∑ x : X, ∑ y : Y, S * f x * g y * S := by
  have hProd :
      (∑ x : X, f x) * (∑ y : Y, g y) =
        ∑ x : X, ∑ y : Y, f x * g y :=
    Finset.sum_mul_sum (s := (Finset.univ : Finset X))
      (t := (Finset.univ : Finset Y)) (f := f) (g := g)
  calc S * (∑ x : X, f x) * (∑ y : Y, g y) * S
      = S * ((∑ x : X, f x) * (∑ y : Y, g y)) * S := by
            rw [Matrix.mul_assoc S (∑ x : X, f x) (∑ y : Y, g y)]
    _ = S * (∑ x : X, ∑ y : Y, f x * g y) * S := by rw [hProd]
    _ = (∑ x : X, S * ∑ y : Y, f x * g y) * S := by
          rw [Matrix.mul_sum (s := (Finset.univ : Finset X))]
    _ = ∑ x : X, S * (∑ y : Y, f x * g y) * S := by
          rw [Finset.sum_mul (s := (Finset.univ : Finset X))]
    _ = ∑ x : X, (∑ y : Y, S * (f x * g y)) * S := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Matrix.mul_sum (s := (Finset.univ : Finset Y))]
    _ = ∑ x : X, ∑ y : Y, S * (f x * g y) * S := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul (s := (Finset.univ : Finset Y))]
    _ = ∑ x : X, ∑ y : Y, S * f x * g y * S := by
          refine Finset.sum_congr rfl fun x _ => ?_
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Matrix.mul_assoc S (f x) (g y)]

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy

/-- Collapse of the double-condition indicator sum over `Z`:
`∑ z, [z1=z ∧ z2=z] · f = [z1=z2] · f`. (Local copy of the private helper from
`LambdaBoundTwoUniversal.lean`; the proof is generic in the value type.) -/
private lemma sum_z_collapse_double_iff
    {Z : Type*} [Fintype Z] [DecidableEq Z] {α : Type*} [AddCommMonoid α]
    (z1 z2 : Z) (f : α) :
    ∑ z : Z, (if z1 = z ∧ z2 = z then f else 0) =
      (if z1 = z2 then f else 0) := by
  by_cases h : z1 = z2
  · subst h
    rw [if_pos rfl]
    have : (∑ z : Z, (if z1 = z ∧ z1 = z then f else 0)) =
        ∑ z : Z, if z1 = z then f else 0 := by
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : z1 = z <;> simp [hz]
    rw [this, Finset.sum_ite_eq Finset.univ z1 (fun _ => f),
      if_pos (Finset.mem_univ z1)]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro z _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (h1.trans h2.symm)

/-- **Real-valued Jensen for the single-σ trace pairing.**

For Hermitian `S` (later `S = σ⁻¹/²`) and any family `A : T → Op n` over a
nonempty Fintype `T`,

  `(1/|T|)² · Tr(S · (∑_t A_t) · (∑_t A_t) · S).re
       ≤ (1/|T|) · ∑_t Tr(S · A_t · A_t · S).re`.

This is the discrete Cauchy–Schwarz inequality for the PSD real bilinear form
`⟨X, Y⟩ := Tr(S·X·Y·S).re` (which is PSD because the diagonal `⟨X,X⟩` equals
`Tr((S X)(S X)†).re ≥ 0`). -/
lemma tr_S_avg_sq_S_le_avg_tr_S_sq_S
    {T : Type*} [Fintype T] {n : ℕ}
    {S : Op n} (hS : S.IsHermitian) (A : T → Op n) (hA : ∀ t, (A t).IsHermitian) :
    (S * ((1 / (Fintype.card T : ℝ)) • ∑ t, A t) *
        ((1 / (Fintype.card T : ℝ)) • ∑ t, A t) * S).trace.re ≤
      (1 / (Fintype.card T : ℝ)) *
        ∑ t, (S * A t * A t * S).trace.re := by
  by_cases hT : Nonempty T
  · haveI := hT
    exact Quantum.Operators.tr_smul_avg_right_mul_sq_re_le_avg_tr_right_mul_sq_re A S hA hS
  · rw [not_nonempty_iff] at hT
    haveI : IsEmpty T := hT
    simp

/-- **Per-seed collision identity (single-σ form, abstract).**

For any operator `T : Op n`, family `R : X → Op n`, and hash function
`h : X → Z`,
  `∑_z (T · (∑_{x : h x = z} R x) · (∑_{x : h x = z} R x) · T).trace.re
     = ∑_{x,x'} [h x = h x'] · (T · R x · R x' · T).trace.re`.

Pure algebraic identity (bilinearity + indicator collapse), no PSD/Hermitian
structure required. -/
lemma per_seed_collision_identity_single
    {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq Z] {n : ℕ}
    (T : Op n) (R : X → Op n) (h : X → Z) :
    (∑ z : Z, (T *
        (∑ x : X, if h x = z then R x else 0) *
        (∑ x : X, if h x = z then R x else 0) * T).trace.re) =
      ∑ x : X, ∑ x' : X,
        (if h x = h x' then (T * R x * R x' * T).trace.re else 0) := by
  have hExpand : ∀ z : Z,
      (T * (∑ x : X, if h x = z then R x else 0) *
        (∑ x' : X, if h x' = z then R x' else 0) * T).trace.re =
        ∑ x : X, ∑ x' : X,
          (if h x = z ∧ h x' = z then (T * R x * R x' * T).trace.re else 0) := by
    intro z
    rw [sandwich_sum_mul_sum T
        (fun x => if h x = z then R x else 0)
        (fun x' => if h x' = z then R x' else 0)]
    rw [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    by_cases hx : h x = z <;> by_cases hx' : h x' = z <;> simp [hx, hx']
  simp_rw [hExpand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  exact sum_z_collapse_double_iff _ _ _

/-- **Bilinearity: pair sum equals sandwich of marginal squared.**

For any `S : Op n` and family `R : X → Op n`,
  `∑_{x,x'} (S · R x · R x' · S).trace.re
     = (S · (∑_x R x) · (∑_x R x) · S).trace.re`. -/
lemma sum_pair_tr_S_RR_S_eq_marginal_sq
    {X : Type*} [Fintype X] {n : ℕ} (S : Op n) (R : X → Op n) :
    (∑ x : X, ∑ x' : X, (S * R x * R x' * S).trace.re) =
      (S * (∑ x : X, R x) * (∑ x : X, R x) * S).trace.re := by
  rw [sandwich_sum_mul_sum S R R, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.trace_sum, Complex.re_sum]

/-- **Jensen + per-seed collision expansion (single-σ form).**

Single-σ analogue of `sum_tr_SMzS_sq_le_seed_avg_collision_sum`. The trace
form here is `(S · M_z · M_z · S).trace.re` (with `M_z` unsandwiched), instead
of `((S·M_z·S)·(S·M_z·S)).trace.re`.

Proof structure: expand `M_z = (1/|S|) ∑_s E_{s,z}` where
`E_{s,z} := ∑_{x : H.hash s x = z} (ρ.stateMap x).toOp`, apply per-z Jensen
via `tr_S_avg_sq_S_le_avg_tr_S_sq_S` to the family `(E_{s,z})_s`, then
collapse the per-seed sum via `per_seed_collision_identity_single`. -/
lemma sum_tr_SMzsqS_le_seed_avg_collision_sum_single
    {S X Z : Type*} [Fintype S] [Fintype X]
    [Fintype Z] [DecidableEq Z] {n : ℕ}
    (H : QuantumHashFamily S X Z)
    (ρ : CQState X n) {σ : Op n} (hσ : σ.PosDef) :
    (∑ z : Z,
        (hσ.inverseSqrt * extractorWeightedOp H ρ z *
          extractorWeightedOp H ρ z * hσ.inverseSqrt).trace.re) ≤
      (1 / (Fintype.card S : ℝ)) *
        ∑ s : S, ∑ x : X, ∑ x' : X,
          (if H.hash s x = H.hash s x' then
            (hσ.inverseSqrt * (ρ.stateMap x).toOp *
              (ρ.stateMap x').toOp * hσ.inverseSqrt).trace.re
           else 0) := by
  by_cases hS : Nonempty S
  · haveI := hS
    -- Abbreviations.
    set T : Op n := hσ.inverseSqrt with hT_def
    set R : X → Op n := fun x => (ρ.stateMap x).toOp with hR_def
    let E : S → Z → Op n := fun s z =>
      ∑ x : X, if H.hash s x = z then R x else 0
    have hT_herm : T.IsHermitian := hσ.inverseSqrt_isHermitian
    have hρ_herm : ∀ x : X, (R x).IsHermitian := fun x =>
      (Quantum.Operators.posSemidefOp_implies_mathlib
        (ρ.stateMap x).toPosSemidefOp).isHermitian
    -- Hermiticity of `E s z`.
    have hE_herm : ∀ s z, (E s z).IsHermitian := by
      intros s z
      change (∑ x : X, if H.hash s x = z then R x else 0).IsHermitian
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : H.hash s x = z <;> simp [hx, (hρ_herm x).eq]
    -- Sandwich linearity (definitional): M_z = (1/|S|) • ∑ s, E s z.
    have hSand : ∀ z : Z,
        extractorWeightedOp H ρ z = (1 / (Fintype.card S : ℝ)) • ∑ s, E s z := by
      intro z; rfl
    -- Rewrite LHS using hSand.
    have hLHS_rewrite :
        (∑ z : Z,
            (T * extractorWeightedOp H ρ z *
              extractorWeightedOp H ρ z * T).trace.re) =
        ∑ z : Z,
            (T * ((1 / (Fintype.card S : ℝ)) • ∑ s, E s z) *
              ((1 / (Fintype.card S : ℝ)) • ∑ s, E s z) * T).trace.re := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [hSand z]
    rw [hLHS_rewrite]
    -- Per-z Jensen via `tr_S_avg_sq_S_le_avg_tr_S_sq_S`.
    have hPerZ : ∀ z : Z,
        (T * ((1 / (Fintype.card S : ℝ)) • ∑ s, E s z) *
            ((1 / (Fintype.card S : ℝ)) • ∑ s, E s z) * T).trace.re ≤
          (1 / (Fintype.card S : ℝ)) * ∑ s, (T * E s z * E s z * T).trace.re :=
      fun z =>
        tr_S_avg_sq_S_le_avg_tr_S_sq_S hT_herm (E · z) (fun s => hE_herm s z)
    have hSumZ :
        ∑ z : Z, (T * ((1 / (Fintype.card S : ℝ)) • ∑ s, E s z) *
              ((1 / (Fintype.card S : ℝ)) • ∑ s, E s z) * T).trace.re ≤
          ∑ z : Z, (1 / (Fintype.card S : ℝ)) *
            ∑ s, (T * E s z * E s z * T).trace.re :=
      Finset.sum_le_sum fun z _ => hPerZ z
    refine hSumZ.trans ?_
    -- Reorganize: ∑_z (1/|S|) * ∑_s = (1/|S|) * ∑_s ∑_z.
    rw [← Finset.mul_sum, Finset.sum_comm]
    -- Pull out the (1/|S|) factor and bound per-s using the per-seed identity.
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine Finset.sum_le_sum fun s _ => ?_
    exact le_of_eq (per_seed_collision_identity_single T R (H.hash s))
  · -- Empty seed: extractorWeightedOp = 0 for all z, RHS sum is 0.
    rw [not_nonempty_iff] at hS
    haveI : IsEmpty S := hS
    have hMz : ∀ z : Z, extractorWeightedOp H ρ z = 0 := by
      intro z
      unfold extractorWeightedOp
      have : (∑ s : S, ∑ x : X,
          if H.hash s x = z then (ρ.stateMap x).toOp else 0) = 0 := by
        rw [Finset.univ_eq_empty (α := S)]
        simp
      rw [this, smul_zero]
    simp [hMz]

/-- **D² expansion identity (single-σ form).**
For an `S`, `R : Op n`, a family of operators `M : Z → Op n`
summing to `R` (`∑_z M z = R`), and `c := 1/|Z|`, we have:

  `∑_z (S · (M_z - c·R) · (M_z - c·R) · S).trace.re
     = (∑_z (S · M_z · M_z · S).trace.re) - c · (S · R · R · S).trace.re`.

This is the algebraic core of the δ step: it converts the per-block "difference
square" sum into the per-block "M-square" sum minus a uniform-marginal correction.
The proof is purely algebraic (expansion of `(M - cR)²`, trace/`.re` linearity,
and using `∑_z M_z = R` to evaluate the cross- and `N²`-terms). -/
lemma sum_tr_SDsqS_eq_sum_tr_SMzsqS_sub_uniform
    {Z : Type*} [Fintype Z] {n : ℕ}
    (S R : Op n) (M : Z → Op n) (hSumM : ∑ z, M z = R) :
    (∑ z : Z, (S *
        (M z - (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • R) *
        (M z - (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) • R) * S).trace.re) =
      (∑ z : Z, (S * M z * M z * S).trace.re) -
        ((1 : ℝ) / (Fintype.card Z : ℝ)) * (S * R * R * S).trace.re := by
  by_cases hcard : Fintype.card Z = 0
  · -- Empty case: all sums over Z vanish, and `R = 0` (forced by `hSumM`).
    haveI hZemp : IsEmpty Z := Fintype.card_eq_zero_iff.mp hcard
    have hR : R = 0 := by
      simpa [Finset.sum_of_isEmpty] using hSumM.symm
    subst hR
    simp
  haveI hZne : Nonempty Z := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
  set c : ℝ := 1 / (Fintype.card Z : ℝ) with hc_def
  set cC : ℂ := (c : ℂ) with hcC_def
  -- Per-z trace identity.
  have hTraceLinear : ∀ z : Z,
      (S * (M z - cC • R) * (M z - cC • R) * S).trace.re =
        (S * M z * M z * S).trace.re
          - c * (S * M z * R * S).trace.re
          - c * (S * R * M z * S).trace.re
          + (c * c) * (S * R * R * S).trace.re := by
    intro z
    have h_inner :
        (M z - cC • R) * (M z - cC • R) =
          M z * M z - cC • (M z * R) - cC • (R * M z) + (cC * cC) • (R * R) := by
      have e1 : (M z - cC • R) * (M z - cC • R)
              = M z * M z - M z * (cC • R) - (cC • R) * M z
                + (cC • R) * (cC • R) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]; abel
      rw [e1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    have h_S_S :
        S * ((M z - cC • R) * (M z - cC • R)) * S =
          S * (M z * M z) * S
            - cC • (S * (M z * R) * S)
            - cC • (S * (R * M z) * S)
            + (cC * cC) • (S * (R * R) * S) := by
      rw [h_inner]
      rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_sub]
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.sub_mul]
      rw [Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.smul_mul]
    have h_LHS_assoc :
        S * (M z - cC • R) * (M z - cC • R) * S =
          S * ((M z - cC • R) * (M z - cC • R)) * S := by
      rw [Matrix.mul_assoc S (M z - cC • R) (M z - cC • R)]
    rw [h_LHS_assoc, h_S_S]
    rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
    rw [Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul]
    rw [Complex.add_re, Complex.sub_re, Complex.sub_re]
    have h_cC_re : ∀ w : ℂ, (cC • w).re = c * w.re := by
      intro w
      have hw : cC • w = (c : ℂ) * w := by rw [hcC_def]; rfl
      rw [hw, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h_cCcC_re : ∀ w : ℂ, ((cC * cC) • w).re = (c * c) * w.re := by
      intro w
      have hcc : (cC * cC : ℂ) = ((c * c : ℝ) : ℂ) := by
        rw [hcC_def]; push_cast; ring
      have hw : (cC * cC) • w = ((c * c : ℝ) : ℂ) * w := by rw [hcc]; rfl
      rw [hw, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [h_cC_re, h_cC_re, h_cCcC_re]
    have hA : S * (M z * M z) * S = S * M z * M z * S := by
      rw [← Matrix.mul_assoc S (M z) (M z)]
    have hB : S * (M z * R) * S = S * M z * R * S := by
      rw [← Matrix.mul_assoc S (M z) R]
    have hC : S * (R * M z) * S = S * R * M z * S := by
      rw [← Matrix.mul_assoc S R (M z)]
    have hD : S * (R * R) * S = S * R * R * S := by
      rw [← Matrix.mul_assoc S R R]
    rw [hA, hB, hC, hD]
  -- Bridge the goal's scalar form to `cC`.
  have hCast : (((1 : ℝ) / (Fintype.card Z : ℝ)) : ℂ) = cC := by
    rw [hcC_def, hc_def]; push_cast; ring
  simp_rw [hCast, hTraceLinear]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  -- Cross terms: ∑_z (S * M z * R * S).trace.re = (S * R * R * S).trace.re via ∑ M = R.
  have hCross1 : ∑ z : Z, (S * M z * R * S).trace.re = (S * R * R * S).trace.re := by
    have hsum : (∑ z : Z, S * M z * R * S) = S * R * R * S := by
      calc (∑ z : Z, S * M z * R * S)
          = (∑ z : Z, S * M z) * R * S := by rw [Finset.sum_mul, Finset.sum_mul]
        _ = S * (∑ z : Z, M z) * R * S := by rw [← Matrix.mul_sum]
        _ = S * R * R * S := by rw [hSumM]
    rw [← hsum, Matrix.trace_sum, Complex.re_sum]
  have hCross2 : ∑ z : Z, (S * R * M z * S).trace.re = (S * R * R * S).trace.re := by
    have hsum : (∑ z : Z, S * R * M z * S) = S * R * R * S := by
      calc (∑ z : Z, S * R * M z * S)
          = (∑ z : Z, S * R * M z) * S := by rw [Finset.sum_mul]
        _ = S * R * (∑ z : Z, M z) * S := by
                rw [show (∑ z : Z, S * R * M z) = S * R * (∑ z : Z, M z) from by
                  rw [Matrix.mul_sum]]
        _ = S * R * R * S := by rw [hSumM]
    rw [← hsum, Matrix.trace_sum, Complex.re_sum]
  have hConst : (∑ _z : Z, (S * R * R * S).trace.re) =
      (Fintype.card Z : ℝ) * (S * R * R * S).trace.re := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hCross1, hCross2, hConst]
  have hc_card : c * (Fintype.card Z : ℝ) = 1 := by
    rw [hc_def]; field_simp
  have hcc_card : (c * c) * (Fintype.card Z : ℝ) = c := by
    rw [show (c * c) * (Fintype.card Z : ℝ) = c * (c * (Fintype.card Z : ℝ)) from by ring]
    rw [hc_card, mul_one]
  have h_simp : c * c * ((Fintype.card Z : ℝ) * (S * R * R * S).trace.re) =
      c * (S * R * R * S).trace.re := by
    rw [show c * c * ((Fintype.card Z : ℝ) * (S * R * R * S).trace.re) =
        (c * c * (Fintype.card Z : ℝ)) * (S * R * R * S).trace.re from by ring]
    rw [hcc_card]
  linarith [h_simp]

/-- **Off-diagonal pair sum bounded by marginal square (single-σ form).**

Single-σ analogue of `sum_offdiag_tr_prod_sandwich_le_sq_marginal`. The full
pair sum `∑_{x,x'} (S · ρ_x · ρ_{x'} · S).trace.re` equals
`(S · ρ_A · ρ_A · S).trace.re` by bilinearity (with
`ρ_A := ρ.quantumMarginalOp = ∑_x (ρ.stateMap x).toOp`). The diagonal
contributions are non-negative (each is `(S · ρ_x · ρ_x · S).trace.re ≥ 0` by
`Quantum.Operators.tr_S_ASqS_re_nonneg` from
`Quantum/Operators/HermitianTraceSq.lean`), so dropping them yields the
off-diagonal bound. -/
lemma sum_offdiag_tr_S_rhoxrhoxp_S_le_sq_marginal_single
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (ρ : CQState X n) {σ : Op n} (hσ : σ.PosDef) :
    (∑ x : X, ∑ x' : X,
        (if x ≠ x' then
          (hσ.inverseSqrt * (ρ.stateMap x).toOp *
            (ρ.stateMap x').toOp * hσ.inverseSqrt).trace.re
         else 0)) ≤
      (hσ.inverseSqrt * ρ.quantumMarginalOp *
          ρ.quantumMarginalOp * hσ.inverseSqrt).trace.re := by
  set S : Op n := hσ.inverseSqrt with hS_def
  have hS_herm : S.IsHermitian := hσ.inverseSqrt_isHermitian
  have hρ_herm : ∀ x : X, ((ρ.stateMap x).toOp).IsHermitian := fun x =>
    (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp).isHermitian
  -- Bilinearity: ∑_{x,x'} Tr(S·ρ_x·ρ_{x'}·S).re = Tr(S·ρ_A·ρ_A·S).re
  have hFull :
      (∑ x : X, ∑ x' : X,
          (S * (ρ.stateMap x).toOp * (ρ.stateMap x').toOp * S).trace.re) =
        (S * ρ.quantumMarginalOp * ρ.quantumMarginalOp * S).trace.re :=
    sum_pair_tr_S_RR_S_eq_marginal_sq S (fun x => (ρ.stateMap x).toOp)
  -- Diagonal non-negativity.
  have hDiag_nonneg : ∀ x : X,
      0 ≤ (S * (ρ.stateMap x).toOp * (ρ.stateMap x).toOp * S).trace.re := fun x =>
    tr_S_ASqS_re_nonneg hS_herm (hρ_herm x)
  have hDiagSum_nonneg :
      0 ≤ ∑ x : X, (S * (ρ.stateMap x).toOp * (ρ.stateMap x).toOp * S).trace.re :=
    Finset.sum_nonneg fun x _ => hDiag_nonneg x
  -- Diag/off-diag split.
  have hSplit :
      (∑ x : X, ∑ x' : X,
          (S * (ρ.stateMap x).toOp * (ρ.stateMap x').toOp * S).trace.re) =
        (∑ x : X, (S * (ρ.stateMap x).toOp * (ρ.stateMap x).toOp * S).trace.re) +
        (∑ x : X, ∑ x' : X,
          (if x ≠ x' then
            (S * (ρ.stateMap x).toOp * (ρ.stateMap x').toOp * S).trace.re
           else 0)) :=
    diag_offdiag_split
      (fun x x' => (S * (ρ.stateMap x).toOp * (ρ.stateMap x').toOp * S).trace.re)
  linarith [hFull, hSplit, hDiagSum_nonneg]

end InfoTheory.QuantumLHL

end -- noncomputable section
