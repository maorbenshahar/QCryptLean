import QCryptLean.LOCC.Local

/-!
# Classical local instruments

Three `LOCC.LocalInstrument`s for classical post-processing of a party's register:
read a function of the register while retaining it, read a uniformly seeded function, or compute
a function while discarding the input. A program's announced node publishes the instrument's
outcome; a private node sums over it without extending the transcript. Public visibility is a
property of that use, not of an instrument alone. These are local operations in the LOCC formalism
of Chitambar, Leung, Mančinska, Ozols and Winter, *Everything you always wanted to know about
LOCC (but were afraid to ask)*, Comm. Math. Phys. **328** (2014) 303-326, arXiv:1210.4583,
Section II, and nothing below mentions a particular protocol.

Each instrument is an explicit `def` with a proved `complete` field, so summing its branches
preserves trace (see `LOCC.LocalInstrument`).

## Main definitions

* `LOCC.outcomeDigit`: the numeral coordinate `Fintype.equivFin` assigns to an outcome of
  `Fin N`, as a self-equivalence of `Fin N`. Announcing an outcome writes this digit.
* `LOCC.registerBit`: the `i`-th bit of a `2 ^ n`-dimensional register. Which register it
  is applied to is what makes a step one party's rather than the other's.
* `LOCC.pinnedReadout`: read `v x` and keep the register.
* `LOCC.seededReadout`: draw a seed uniformly and read the pair `(r, w r x)`.
* `LOCC.hashForget`: compute `f x` with Kraus operators `|f x⟩⟨x|` indexed by `x`.

## Main statements

The column laws give each branch's action on a computational basis vector. For `pinnedReadout`
and `hashForget`, one outcome has a nonzero column; for `seededReadout`, one outcome per seed
does, with squared amplitude `1 / Nr`. Together with
`Quantum.Operators.krausConj_single_of_col`, these laws evaluate the branches on basis projectors;
linearity then evaluates classical mixtures.

## Scope limit

Every branch below is diagonal in the computational basis, or a matrix unit; the column laws
therefore evaluate the instruments on *basis projectors* and extend by linearity to the diagonal
span, that is, to classical mixtures. A coherent input needs off-diagonal matrix-unit values,
and an input entangled with a reference system needs the corresponding equality after tensoring
with an identity. Neither is asserted here.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace LOCC
open Quantum

/-! ## 1. Register and alphabet coordinates -/

/-- The numeral coordinate assigned to a `Fin N` outcome by `Fintype.equivFin`. -/
def outcomeDigit (N : ℕ) : Fin N ≃ Fin N :=
  (Fintype.equivFin (Fin N)).trans (finCongr (Fintype.card_fin N))

/-- The coordinate change preserves the natural-number value assigned by `Fintype.equivFin`. -/
theorem outcomeDigit_val (N : ℕ) (o : Fin N) :
    ((Fintype.equivFin (Fin N) o : Fin (Fintype.card (Fin N))) : ℕ) = (outcomeDigit N o : ℕ) := rfl

/-- The `i`-th bit of a party's own `2 ^ n`-dimensional register. Both parties read their own
register with this function; which register it is applied to is what makes a step Alice's or
Bob's. -/
def registerBit (n : ℕ) (i : Fin n) (x : Fin (2 ^ n)) : Fin 2 := finFunctionFinEquiv.symm x i

/-! ## 2. The three instruments -/

/-- A diagonal `0/1` indicator is an orthogonal projector. -/
theorem diagonal_indicator_conj_self {d : ℕ} (P : Fin d → Prop) [DecidablePred P] :
    (Matrix.diagonal fun x : Fin d => if P x then (1 : ℂ) else 0)ᴴ *
        (Matrix.diagonal fun x : Fin d => if P x then (1 : ℂ) else 0) =
      Matrix.diagonal fun x : Fin d => if P x then (1 : ℂ) else 0 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases h : P x <;> simp [h]

/-- On an already-dephased register, read `v x` and keep the register. The branch at outcome `o`
is the diagonal indicator of `v ⁻¹' {outcomeDigit N o}`. The family is complete and each branch
is a projector. When used in an announced node, the written transcript digit is `v x`. -/
def pinnedReadout {d N : ℕ} (v : Fin d → Fin N) : LocalInstrument d d (Fin N) where
  kraus o := Matrix.diagonal fun x => if v x = outcomeDigit N o then (1 : ℂ) else 0
  complete := by
    simp_rw [diagonal_indicator_conj_self]
    ext i j
    rw [Matrix.sum_apply]
    by_cases hij : i = j
    · subst hij
      have hpt : ∀ o : Fin N, (if v i = outcomeDigit N o then (1 : ℂ) else 0) =
          if o = (outcomeDigit N).symm (v i) then (1 : ℂ) else 0 := by
        intro o
        refine if_congr ?_ rfl rfl
        constructor
        · intro h; rw [h]; simp
        · intro h; subst h; simp
      simp only [Matrix.diagonal_apply_eq, hpt, Matrix.one_apply_eq]
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- A uniformly seeded classical readout. The party draws a seed `r` uniformly and reads the pair
`(r, w r x)`. An announced node publishes that pair. Each compatible branch has amplitude
`√(1/Nr)` and weight `1/Nr`; summing over outcomes includes every seed.

Completeness is genuinely two-step: for each fixed seed the sets `{x | w r x = ν}` are the fibres of
a function, hence a partition, so the `ν`-sum is the identity; the `r`-sum then contributes `Nr`
copies of the weight `1/Nr`. -/
def seededReadout {d Nr Nv : ℕ} [NeZero Nr] (w : Fin Nr → Fin d → Fin Nv) :
    LocalInstrument d d (Fin (Nr * Nv)) where
  kraus o :=
    ((Real.sqrt ((Nr : ℝ))⁻¹ : ℝ) : ℂ) •
      Matrix.diagonal fun x =>
        if w (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).1 x =
            (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).2 then (1 : ℂ) else 0
  complete := by
    have hscale : (((Real.sqrt ((Nr : ℝ))⁻¹ : ℝ) : ℂ)) * (((Real.sqrt ((Nr : ℝ))⁻¹ : ℝ) : ℂ)) =
        ((Nr : ℂ))⁻¹ := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      simp
    have hstar : star (((Real.sqrt ((Nr : ℝ))⁻¹ : ℝ) : ℂ)) = (((Real.sqrt ((Nr : ℝ))⁻¹ : ℝ) : ℂ)) :=
      Complex.conj_ofReal _
    have hsq : ∀ o : Fin (Nr * Nv),
        (((Real.sqrt ((Nr : ℝ))⁻¹ : ℝ) : ℂ) •
            Matrix.diagonal fun x : Fin d =>
              if w (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).1 x =
                  (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).2 then (1 : ℂ) else 0)ᴴ *
          (((Real.sqrt ((Nr : ℝ))⁻¹ : ℝ) : ℂ) •
            Matrix.diagonal fun x : Fin d =>
              if w (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).1 x =
                  (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).2 then (1 : ℂ) else 0) =
        ((Nr : ℂ))⁻¹ • Matrix.diagonal fun x : Fin d =>
          if w (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).1 x =
              (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).2 then (1 : ℂ) else 0 := by
      intro o
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        diagonal_indicator_conj_self, hstar, hscale]
    simp_rw [hsq]
    have hNr : ((Nr : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Nr)
    ext i j
    rw [Matrix.sum_apply]
    by_cases hij : i = j
    · subst hij
      have hreindex : (∑ o : Fin (Nr * Nv), (((Nr : ℂ))⁻¹ • Matrix.diagonal
            fun x : Fin d => if w (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).1 x =
              (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).2 then (1 : ℂ) else 0) i i) =
          ∑ rv : Fin Nr × Fin Nv, ((Nr : ℂ))⁻¹ * (if w rv.1 i = rv.2 then (1 : ℂ) else 0) := by
        rw [← Equiv.sum_comp ((outcomeDigit (Nr * Nv)).trans finProdFinEquiv.symm)
          fun rv : Fin Nr × Fin Nv =>
            ((Nr : ℂ))⁻¹ * (if w rv.1 i = rv.2 then (1 : ℂ) else 0)]
        refine Finset.sum_congr rfl fun o _ => ?_
        simp [Matrix.diagonal_apply_eq]
      rw [hreindex, Fintype.sum_prod_type]
      have hinner : ∀ r : Fin Nr,
          (∑ ν : Fin Nv, ((Nr : ℂ))⁻¹ * (if w r i = ν then (1 : ℂ) else 0)) = ((Nr : ℂ))⁻¹ := by
        intro r
        rw [← Finset.mul_sum]
        simp
      simp_rw [hinner]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_inv_cancel₀ hNr, Matrix.one_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- **Hash-and-forget.** The private, dimension-changing step `|f x⟩⟨x|`: the party computes `f`
of its own register and keeps only the result. Completeness holds for **any** `f` — the family is
`∑ₓ |x⟩⟨f x| |f x⟩⟨x| = ∑ₓ |x⟩⟨x| = 1` — which is why nothing here constrains the hash. What makes
this step private rather than announced is semantic and not arithmetic: an announced step with the
same instrument writes the raw input string into the transcript. -/
def hashForget {p q : ℕ} (f : Fin p → Fin q) : LocalInstrument p q (Fin p) where
  kraus x := Matrix.single (f x) x (1 : ℂ)
  complete := by
    have hx : ∀ x : Fin p, (Matrix.single (f x) x (1 : ℂ))ᴴ * Matrix.single (f x) x (1 : ℂ) =
        Matrix.single x x (1 : ℂ) := by
      intro x
      rw [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
      simp
    simp_rw [hx]
    ext i j
    simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
    simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ## 3. The columns of the three instruments

Each instrument is "one column per basis vector": on a computational basis input exactly one
outcome branch survives, and its Kraus operator sends that basis vector to a multiple of another.
These six lemmas evaluate the retained, discarded, and uniformly seeded readouts. -/

theorem pinnedReadout_kraus_col {d N : ℕ} (v : Fin d → Fin N) (a i : Fin d) :
    (pinnedReadout v).kraus ((outcomeDigit N).symm (v a)) i a = if i = a then (1 : ℂ) else 0 := by
  by_cases h : i = a
  · subst h
    simp [pinnedReadout]
  · simp [pinnedReadout, h]

theorem pinnedReadout_kraus_col_zero {d N : ℕ} (v : Fin d → Fin N) (a : Fin d) (o : Fin N)
    (ho : o ≠ (outcomeDigit N).symm (v a)) (i : Fin d) : (pinnedReadout v).kraus o i a = 0 := by
  by_cases h : i = a
  · subst h
    have hv : ¬ (v i = outcomeDigit N o) := fun hc => ho (by rw [hc, Equiv.symm_apply_apply])
    simp [pinnedReadout, hv]
  · simp [pinnedReadout, h]

theorem hashForget_kraus_col {p q : ℕ} (f : Fin p → Fin q) (a : Fin p) (i : Fin q) :
    (hashForget f).kraus a i a = if i = f a then (1 : ℂ) else 0 := by
  simp [hashForget, Matrix.single_apply, eq_comm]

theorem hashForget_kraus_col_zero {p q : ℕ} (f : Fin p → Fin q) (a o : Fin p) (ho : o ≠ a)
    (i : Fin q) : (hashForget f).kraus o i a = 0 := by
  simp [hashForget, ho]

theorem seededReadout_kraus_col {d Nr Nv : ℕ} [NeZero Nr] (w : Fin Nr → Fin d → Fin Nv)
    (a : Fin d) (r : Fin Nr) (i : Fin d) :
    (seededReadout w).kraus
        ((outcomeDigit (Nr * Nv)).symm (finProdFinEquiv (r, w r a))) i a =
      if i = a then ((Real.sqrt ((Nr : ℝ))⁻¹ : ℝ) : ℂ) else 0 := by
  by_cases h : i = a
  · subst h
    simp only [seededReadout, Matrix.smul_apply, Matrix.diagonal_apply, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, smul_eq_mul]
    simp
  · simp only [seededReadout, Matrix.smul_apply, Matrix.diagonal_apply, if_neg h, smul_eq_mul,
      mul_zero]

theorem seededReadout_kraus_col_zero {d Nr Nv : ℕ} [NeZero Nr] (w : Fin Nr → Fin d → Fin Nv)
    (a : Fin d) (o : Fin (Nr * Nv))
    (ho : ∀ r : Fin Nr, o ≠ (outcomeDigit (Nr * Nv)).symm (finProdFinEquiv (r, w r a)))
    (i : Fin d) : (seededReadout w).kraus o i a = 0 := by
  by_cases h : i = a
  · subst h
    have hne : ¬ (w (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).1 i =
        (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).2) := by
      intro hc
      refine ho (finProdFinEquiv.symm (outcomeDigit (Nr * Nv) o)).1 ?_
      rw [hc, Prod.mk.eta, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    simp only [seededReadout, Matrix.smul_apply, Matrix.diagonal_apply, if_neg hne, smul_eq_mul]
    simp
  · simp only [seededReadout, Matrix.smul_apply, Matrix.diagonal_apply, if_neg h, smul_eq_mul,
      mul_zero]

end LOCC

end
