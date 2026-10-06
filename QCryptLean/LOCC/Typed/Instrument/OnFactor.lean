import QCryptLean.LOCC.Typed.Channel

/-!
# Reindexing an instrument onto one tensor factor

This module constructs `Instrument.onFactor eIn eOut I`. The supplied equivalences identify the
larger input and output with the acted-on register paired with one unchanged spectator type. Each
Kraus matrix is the corresponding matrix of `I` tensored with the identity and reindexed by those
equivalences; the hidden Kraus fibre is unchanged.

This is the finite `K ⊗ 1` local-instrument construction of
Chitambar--Leung--Mančinska--Ozols--Winter, arXiv:1210.4583, Section 2.  The present helper is
generic finite-dimensional bookkeeping: it makes no BB84, schedule, memory, or security claim.
Unlike `Instrument.liftAt`, the explicit equivalences permit an empty spectator type.
-/

open scoped Matrix BigOperators Kronecker
open Matrix

namespace TypedLOCC.Instrument

variable {A B A' B' S Outcome : Type}

/-- Reindex `K ⊗ 1` from explicit product coordinates to the supplied outer register types. -/
def onFactorKraus [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    [Fintype S] [DecidableEq S] [Fintype Outcome]
    (eIn : A' ≃ A × S) (eOut : B' ≃ B × S)
    (I : Instrument A B Outcome) (y : Outcome) (t : I.krausIndex y) :
    Matrix B' A' ℂ :=
  ((I.kraus y t) ⊗ₖ (1 : Matrix S S ℂ)).submatrix eOut eIn

/-- Entrywise support of the reindexed `K ⊗ 1` Kraus matrix.

The acted-on matrix entry is retained exactly when the input and output spectator coordinates
agree.  This is the coordinate form of the local tensor-factor action in arXiv:1210.4583,
Section 2. -/
@[simp] theorem onFactorKraus_apply [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    [Fintype S] [DecidableEq S] [Fintype Outcome]
    (eIn : A' ≃ A × S) (eOut : B' ≃ B × S)
    (I : Instrument A B Outcome) (y : Outcome) (t : I.krausIndex y)
    (b : B') (a : A') :
    onFactorKraus eIn eOut I y t b a =
      if (eOut b).2 = (eIn a).2 then
        I.kraus y t (eOut b).1 (eIn a).1
      else 0 := by
  simp [onFactorKraus, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- The complete Kraus family of `I` remains complete after tensoring with the spectator identity
and reindexing both register types.

This is the trace-preserving certificate for the finite local `K ⊗ 1` construction in
arXiv:1210.4583, Section 2.  It includes the empty-spectator case and takes no proof-valued
normalization input beyond the certificate already carried by `I`. -/
theorem onFactorKraus_complete [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    [Fintype S] [DecidableEq S] [Fintype Outcome]
    (eIn : A' ≃ A × S) (eOut : B' ≃ B × S)
    (I : Instrument A B Outcome) :
    ∑ y : Outcome, ∑ t : I.krausIndex y,
        (onFactorKraus eIn eOut I y t)ᴴ * onFactorKraus eIn eOut I y t =
      1 := by
  have hGram (y : Outcome) (t : I.krausIndex y) :
      (onFactorKraus eIn eOut I y t)ᴴ * onFactorKraus eIn eOut I y t =
        ((((I.kraus y t)ᴴ * I.kraus y t) ⊗ₖ (1 : Matrix S S ℂ)).submatrix
          eIn eIn) := by
    rw [onFactorKraus, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  simp only [hGram]
  ext a a'
  simp only [Matrix.sum_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, ← Finset.sum_mul]
  have hc := congrFun (congrFun I.complete (eIn a).1) (eIn a').1
  simp only [Matrix.sum_apply] at hc
  rw [hc]
  by_cases haa : a = a'
  · subst a'
    simp
  · have hne : eIn a ≠ eIn a' := fun h => haa (eIn.injective h)
    by_cases h1 : (eIn a).1 = (eIn a').1
    · have h2 : (eIn a).2 ≠ (eIn a').2 := fun h2 =>
        hne (Prod.ext_iff.mpr ⟨h1, h2⟩)
      rw [ite_eq_right h2, ite_eq_right haa, mul_zero]
    · rw [ite_eq_right haa, Matrix.one_apply_ne h1]
      simp

/-- Run `I` on the first factor selected by `eIn` and `eOut`, leaving `S` unchanged.

The observed outcome and dependent hidden Kraus fibre are definitionally those of `I`. -/
def onFactor [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    [Fintype S] [DecidableEq S] [Fintype Outcome]
    (eIn : A' ≃ A × S) (eOut : B' ≃ B × S)
    (I : Instrument A B Outcome) : Instrument A' B' Outcome where
  krausIndex := I.krausIndex
  kraus y t := onFactorKraus eIn eOut I y t
  complete := onFactorKraus_complete eIn eOut I

/-- The hidden Kraus fibre of `onFactor` is definitionally the original fibre. -/
@[simp] theorem onFactor_krausIndex [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    [Fintype S] [DecidableEq S] [Fintype Outcome]
    (eIn : A' ≃ A × S) (eOut : B' ≃ B × S)
    (I : Instrument A B Outcome) (y : Outcome) :
    (onFactor eIn eOut I).krausIndex y = I.krausIndex y := by
  rfl

/-- The certified factor instrument exposes the explicit reindexed tensor-product Kraus matrix. -/
@[simp] theorem onFactor_kraus [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    [Fintype S] [DecidableEq S] [Fintype Outcome]
    (eIn : A' ≃ A × S) (eOut : B' ≃ B × S)
    (I : Instrument A B Outcome) (y : Outcome) (t : I.krausIndex y) :
    (onFactor eIn eOut I).kraus y t = onFactorKraus eIn eOut I y t := by
  rfl

/-- Exact operation of `I` on one explicitly selected tensor factor.

The spectator row and column coordinates are independently selected by `b` and `b'`.  The theorem
holds for every operator `rho`, with no positivity, self-adjointness, trace, or equality assumption
on those two spectator coordinates.  It is the arbitrary-operator coordinate form of the local
`K ⊗ 1` action in arXiv:1210.4583, Section 2. -/
theorem onFactor_operation_apply [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
    [Fintype S] [DecidableEq S] [Fintype Outcome]
    (eIn : A' ≃ A × S) (eOut : B' ≃ B × S)
    (I : Instrument A B Outcome) (y : Outcome) (rho : Op A')
    (b b' : B') :
    ((onFactor eIn eOut I).operation y rho) b b' =
      (I.operation y
        (rho.submatrix
          (fun a => eIn.symm (a, (eOut b).2))
          (fun a => eIn.symm (a, (eOut b').2))))
        (eOut b).1 (eOut b').1 := by
  have hsum (f : A' → ℂ) :
      (∑ x, f x) = ∑ p : A × S, f (eIn.symm p) := by
    exact (Equiv.sum_comp eIn.symm f).symm
  simp only [Instrument.operation, onFactor, matrixConjLinear,
    LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.sum_apply, Matrix.mul_apply, onFactorKraus_apply, ite_mul,
    zero_mul, Matrix.conjTranspose_apply, RCLike.star_def]
  simp_rw [hsum]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp [apply_ite]
  rfl

end TypedLOCC.Instrument
