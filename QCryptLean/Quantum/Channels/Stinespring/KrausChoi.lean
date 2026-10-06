import QCryptLean.Quantum.Channels.Stinespring.PartialTrace

/-!
# Stacked Kraus Choi Vectors — row-Gram identities for marginal channels

This file contains the Choi-vector matrix associated to a Kraus representation
and the row-Gram identities that identify it with the Choi matrix of the Bob
marginal channel.

## Main definitions
- `stackedKrausChoiVec`: Choi-vector matrix stacking a Kraus representation.

## Main statements
- `stackedKrausChoiVec_gram_eq_choi_marginal`: the stacked Kraus row Gram is the marginal Choi
matrix.
- `stackedKrausChoiVec_gram_eq_of_partialTraceB_krausMapFintype_eq`: equal partial-trace marginals
give equal stacked row Grams.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- **Stacked-Kraus matrix in Choi-Jamiolkowski vec form.**

Given a Kraus representation `kr : KrausRepresentation B (B*E)`, the natural
Choi-Jamiolkowski vec lift is the rectangular matrix
`W_kr : Matrix (Fin (B*B)) (Fin (E*kr.numOps)) ℂ` with entries
`W_kr ((α, β), (e, i)) = K_i ((β, e), α)`, obtained by reshaping the Kraus
column (input index) onto the row and packing the Kraus index together with
the environment slice onto the column.

This is the standard Choi-Jamiolkowski vec construction; see Watrous (2018)
*Theory of Quantum Information*, §2.2. -/
noncomputable def stackedKrausChoiVec
    {B E : ℕ} (kr : KrausRepresentation B (B * E)) :
    Matrix (Fin (B * B)) (Fin (E * kr.numOps)) ℂ :=
  Matrix.of fun ab ei =>
    let p := finProdFinEquiv.symm ab
    let q := finProdFinEquiv.symm ei
    kr.operators q.2 (finProdFinEquiv (p.2, q.1)) p.1

/-- The row-Gram product of the stacked Kraus-Choi matrix is the Choi matrix of
the Bob marginal channel. -/
theorem stackedKrausChoiVec_gram_eq_choi_marginal
    {B E : ℕ} [NeZero B] [NeZero E]
    (kr : KrausRepresentation B (B * E)) :
    (stackedKrausChoiVec kr) * (stackedKrausChoiVec kr)ᴴ =
      ChoiMatrix B B (fun A => partialTraceB (krausMapFintype kr.operators A)) := by
  ext ab ab'
  set p := finProdFinEquiv.symm ab with hp
  set p' := finProdFinEquiv.symm ab' with hp'
  have h_single_eq :
      Matrix.single p.1 p'.1 (1 : ℂ) =
        Matrix.of fun r c => if r = p.1 ∧ c = p'.1 then (1 : ℂ) else 0 := by
    ext r c
    simp [Matrix.single_apply, eq_comm]
  have key :
      ((stackedKrausChoiVec kr) * (stackedKrausChoiVec kr)ᴴ) ab ab' =
        partialTraceB (krausMapFintype kr.operators
            (Matrix.single p.1 p'.1 (1 : ℂ))) p.2 p'.2 := by
    rw [Matrix.mul_apply]
    rw [← finProdFinEquiv.sum_comp
        (fun ei => (stackedKrausChoiVec kr) ab ei *
          (stackedKrausChoiVec kr)ᴴ ei ab')]
    rw [Fintype.sum_prod_type]
    simp only [stackedKrausChoiVec, Matrix.of_apply, Matrix.conjTranspose_apply,
      Equiv.symm_apply_apply, ← hp, ← hp']
    simp only [partialTraceB, Matrix.of_apply, krausMapFintype, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_eq_single p'.1, Matrix.mul_apply,
      Finset.sum_eq_single p.1]
    · simp [Matrix.single_apply_same, Matrix.conjTranspose_apply]
    · intro u _ hu
      simp [Matrix.single_apply_of_row_ne hu.symm p'.1 p'.1 (1 : ℂ)]
    · intro hcontra; exact (hcontra (Finset.mem_univ _)).elim
    · intro v _ hv
      rw [Matrix.mul_apply]
      have hzero : ∀ u, kr.operators k (finProdFinEquiv (p.2, t)) u *
          Matrix.single p.1 p'.1 (1 : ℂ) u v = 0 := by
        intro u
        rw [Matrix.single_apply_of_col_ne p.1 u hv.symm (1 : ℂ)]
        ring
      simp [hzero]
    · intro hcontra; exact (hcontra (Finset.mem_univ _)).elim
  rw [key]
  simp only [ChoiMatrix, Matrix.of_apply]
  change partialTraceB ((krausMapFintype kr.operators) (Matrix.single p.1 p'.1 (1 : ℂ))) p.2 p'.2 =
    partialTraceB ((krausMapFintype kr.operators)
      (Matrix.of fun r c => if r = p.1 ∧ c = p'.1 then (1 : ℂ) else 0)) p.2 p'.2
  rw [← h_single_eq]

/-- The stacked Kraus-Choi matrix has rank equal to the Choi rank of the Bob
marginal channel. -/
theorem stackedKrausChoiVec_rank_eq_choi_marginal_rank
    {B E : ℕ} [NeZero B] [NeZero E]
    (kr : KrausRepresentation B (B * E)) :
    Matrix.rank (stackedKrausChoiVec kr) =
      Matrix.rank (ChoiMatrix B B (fun A => partialTraceB (krausMapFintype kr.operators A))) := by
  have h := congrArg Matrix.rank (stackedKrausChoiVec_gram_eq_choi_marginal kr)
  simpa [Matrix.rank_self_mul_conjTranspose] using h

/-- **Choi-Jamiolkowski Gram equality for stacked Kraus matrices.**

The row-Gram product `W_kr * W_krᴴ` of the stacked-Kraus matrix
`stackedKrausChoiVec kr` (see definition above) equals the Choi matrix of the
partial-trace-B marginal channel `A ↦ partialTraceB (krausMapFintype kr.operators A)`.

Consequently, given two Kraus representations `kr, kr'` with equal
partial-trace-B marginal channels, their stacked-Kraus matrices share the same
row-Gram product:
`W_kr * W_krᴴ = W_kr' * W_kr'ᴴ`.

This is the Choi-Jamiolkowski lift of marginal equality.

References:
- Choi (1975), "Completely positive linear maps on complex matrices".
- Jamiolkowski (1972), "Linear transformations which preserve trace and positive
  semidefiniteness of operators".
- Watrous (2018), *Theory of Quantum Information*, §2.2. -/
theorem stackedKrausChoiVec_gram_eq_of_partialTraceB_krausMapFintype_eq
    {B E E' : ℕ} [NeZero B] [NeZero E] [NeZero E']
    (kr : KrausRepresentation B (B * E))
    (kr' : KrausRepresentation B (B * E'))
    (h : ∀ A : Op B,
      partialTraceB (krausMapFintype kr.operators A) =
        partialTraceB (krausMapFintype kr'.operators A)) :
    (stackedKrausChoiVec kr) * (stackedKrausChoiVec kr)ᴴ =
      (stackedKrausChoiVec kr') * (stackedKrausChoiVec kr')ᴴ := by
  rw [stackedKrausChoiVec_gram_eq_choi_marginal kr,
    stackedKrausChoiVec_gram_eq_choi_marginal kr']
  have hfun :
      (fun A : Op B => partialTraceB (krausMapFintype kr.operators A)) =
        (fun A : Op B => partialTraceB (krausMapFintype kr'.operators A)) := by
    funext A
    exact h A
  rw [hfun]

end Quantum.Channels

end -- noncomputable section
