import QCryptLean.Quantum.Symmetry.SymmetricSubspace

/-!
# Symmetric tensor powers of a projected subspace

The symmetric tensor power of an orthogonal projection of rank `r` has trace
`Nat.choose (n + r - 1) (r - 1)`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Math.RepresentationTheory
open scoped BigOperators

noncomputable section

namespace Quantum.Symmetry

/-- Tensor powers commute with the symmetric projector. -/
lemma tensorPow_commute_symmetricProjector {d n : ℕ} [NeZero d] [NeZero n] (A : Op d) :
    Commute (Op.tensorPow A n) (symmetricProjector d n) := by
  unfold symmetricProjector symmetricProjectorRep
  exact (Commute.sum_right Finset.univ _ _
    (fun σ _ => Op.commute_tensorPow_permutationRepresentation A σ)).smul_right _

/-- A simultaneous change of basis on all factors preserves the trace against the
symmetric projector. -/
lemma trace_tensorPow_conj_mul_symmetricProjector {d n : ℕ} [NeZero d] [NeZero n]
    (U A : Op d) (hU : Uᴴ * U = 1) :
    (Op.tensorPow (U * A * Uᴴ) n * symmetricProjector d n).trace =
      (Op.tensorPow A n * symmetricProjector d n).trace := by
  rw [Op.mul_tensorPow, Op.mul_tensorPow]
  rw [mul_assoc (Op.tensorPow U n * Op.tensorPow A n),
    (tensorPow_commute_symmetricProjector (n := n) Uᴴ).eq,
    ← mul_assoc, Matrix.trace_mul_cycle,
    ← mul_assoc, ← Op.mul_tensorPow Uᴴ U, hU, Op.one_tensorPow, one_mul]

/-- An orthogonal projection is unitarily conjugate to the diagonal indicator of a
finite set of basis vectors. -/
lemma exists_unitary_diagonal_indicator_of_projection {d : ℕ} (P : Op d)
    (hP : P.IsHermitian) (hPP : P * P = P) :
    ∃ (U : Matrix.unitaryGroup (Fin d) ℂ) (s : Finset (Fin d)),
      P = (U : Op d) * Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) *
        (U : Op d)ᴴ := by
  let U := hP.eigenvectorUnitary
  let D : Op d := Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)
  have hspec : P = (U : Op d) * D * (U : Op d)ᴴ := by
    exact hP.spectral_theorem
  have hU : (U : Op d)ᴴ * (U : Op d) = 1 := Unitary.coe_star_mul_self U
  have hU' : (U : Op d) * (U : Op d)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hD : (U : Op d)ᴴ * P * (U : Op d) = D := by
    rw [hspec]
    simp only [mul_assoc, hU, mul_one]
    rw [← mul_assoc, hU, one_mul]
  have hDD : D * D = D := by
    rw [← hD]
    calc (U : Op d)ᴴ * P * (U : Op d) * ((U : Op d)ᴴ * P * (U : Op d))
        = (U : Op d)ᴴ * (P * ((U : Op d) * (U : Op d)ᴴ) * P) * (U : Op d) := by
            simp only [mul_assoc]
      _ = (U : Op d)ᴴ * P * (U : Op d) := by
        rw [hU', mul_one, hPP]
  have hentry : ∀ i, (hP.eigenvalues i : ℂ) = 0 ∨ (hP.eigenvalues i : ℂ) = 1 := by
    intro i
    have hi := congr_fun₂ hDD i i
    simp only [D, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Function.comp_apply, RCLike.ofReal_eq_complex_ofReal] at hi
    have hz : (hP.eigenvalues i : ℂ) * ((hP.eigenvalues i : ℂ) - 1) = 0 := by
      rw [mul_sub, mul_one, hi, sub_self]
    exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
  refine ⟨U, Finset.univ.filter (fun i => (hP.eigenvalues i : ℂ) = 1), ?_⟩
  refine hspec.trans ?_
  congr 2
  apply congrArg Matrix.diagonal
  funext i
  simp only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hentry i with hi | hi <;> simp [hi]

/-- Fixed words whose letters belong to `s` are fixed words over the subtype `s`. -/
lemma card_fixed_words_in_finset {d n : ℕ} (s : Finset (Fin d)) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      (∀ k, f k ∈ s) ∧ f ∘ σ = f)).card =
    (Finset.univ.filter (fun f : Fin n → s => f ∘ σ = f)).card := by
  classical
  symm
  refine Finset.card_bij (fun f _ => fun k => (f k).val) ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    exact ⟨fun k => (f k).property, congrArg (fun f => fun k => (f k).val) hf⟩
  · intro f _ g _ h
    funext k
    exact Subtype.ext (congrFun h k)
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    refine ⟨fun k => ⟨f k, hf.1 k⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    funext k
    exact Subtype.ext (congrFun hf.2 k)

/-- Contracting diagonal indicator matrices along a permutation counts the fixed words
over their supporting set of coordinates. -/
lemma diagonal_indicator_cycle_contraction {d n : ℕ} (s : Finset (Fin d))
    (σ : Equiv.Perm (Fin n)) :
    (∑ f : Fin n → Fin d, ∏ k,
      Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) (f k) (f (σ k))) =
      ((Finset.univ.filter (fun f : Fin n → s => f ∘ σ = f)).card : ℂ) := by
  classical
  have hentry : ∀ i j : Fin d,
      Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) i j =
        if i ∈ s ∧ j = i then 1 else 0 := by
    intro i j
    by_cases h : i = j
    · subst j; simp
    · simp [Matrix.diagonal_apply_ne _ h, Ne.symm h]
  simp_rw [hentry, Fintype.prod_boole]
  have hcond : ∀ f : Fin n → Fin d,
      (∀ k, f k ∈ s ∧ f (σ k) = f k) ↔ (∀ k, f k ∈ s) ∧ f ∘ σ = f := by
    intro f
    simp only [forall_and, funext_iff, Function.comp_apply]
  simp_rw [hcond]
  rw [Finset.sum_boole, card_fixed_words_in_finset]

/-- The symmetric tensor power of the coordinate projection onto a nonempty set `s`
has the stars-and-bars dimension for an alphabet of size `s.card`. -/
lemma trace_tensorPow_diagonal_indicator_mul_symmetricProjector {d n : ℕ}
    [NeZero d] [NeZero n] (s : Finset (Fin d)) (hs : s.Nonempty) :
    (Op.tensorPow (Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)) n *
      symmetricProjector d n).trace =
        (Nat.choose (n + s.card - 1) (s.card - 1) : ℂ) := by
  classical
  have : NeZero (Fintype.card s) := ⟨by simpa using hs.card_pos.ne'⟩
  rw [symmetricProjector, Op.trace_tensorPow_mul_symmetricProjectorRep]
  simp_rw [diagonal_indicator_cycle_contraction s]
  have hinv :
      (∑ σ : Equiv.Perm (Fin n),
        ((Finset.univ.filter (fun f : Fin n → s => f ∘ σ.symm = f)).card : ℂ)) =
      ∑ σ : Equiv.Perm (Fin n),
        ((Finset.univ.filter (fun f : Fin n → s => f ∘ σ = f)).card : ℂ) :=
    Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)
  rw [hinv, ← Nat.cast_sum, sum_card_fixedBy_perm_fun_eq_of_fintype,
    Nat.cast_mul, Fintype.card_coe]
  rw [one_div, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]

/-- The symmetric tensor power of a nonzero orthogonal projection of trace `r` has
trace `Nat.choose (n + r - 1) (r - 1)`. -/
lemma trace_tensorPow_projection_mul_symmetricProjector {d n r : ℕ}
    [NeZero d] [NeZero n] [NeZero r] (P : Op d)
    (hP : P.IsHermitian) (hPP : P * P = P) (htr : P.trace = (r : ℂ)) :
    (Op.tensorPow P n * symmetricProjector d n).trace =
      (Nat.choose (n + r - 1) (r - 1) : ℂ) := by
  obtain ⟨U, s, hdiag⟩ := exists_unitary_diagonal_indicator_of_projection P hP hPP
  have hU : (U : Op d)ᴴ * (U : Op d) = 1 := Unitary.coe_star_mul_self U
  have hs : s.card = r := by
    rw [hdiag, Matrix.trace_mul_cycle, hU, one_mul, Matrix.trace_diagonal,
      Finset.sum_boole] at htr
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
      (Nat.cast_inj.mp htr : (Finset.univ.filter (fun x => x ∈ s)).card = r)
  have hsne : s.Nonempty := Finset.card_pos.mp (hs ▸ NeZero.pos r)
  rw [hdiag, trace_tensorPow_conj_mul_symmetricProjector _ _ hU,
    trace_tensorPow_diagonal_indicator_mul_symmetricProjector s hsne, hs]

end Quantum.Symmetry
