import QCryptLean.Quantum.Channels.CPTP.Basic

/-!
# Minimal Stinespring Dilation — structure, Choi-rank bound, and reindexing

A Stinespring dilation `Φ(A) = Tr_E(V A V†)` is *minimal* when the environment dimension
equals the Choi rank of `Φ`.  This file bundles the data of a minimal dilation as a
`structure`, provides the trivial Choi-rank bound `≤ n * m`, and proves the
basis-reindexing lemmas used throughout the uniqueness and transport proofs.

## Main definitions
- `MinimalStinespringDilation`: bundles the isometry, the recovery predicate, and minimality.
- `outputEnvEquiv`: reindexes the output coordinate of a flattened output-environment basis.

## Main statements
- `choiMatrix_rank_le_nm`: the Choi rank is at most `n * m` (trivial matrix-size bound).
- `MinimalStinespringDilation.reindex`: transports a minimal dilation across finite input
  and output basis equivalences.

## References
- Stinespring (1955) "Positive functions on C*-algebras"
- Paulsen (2002) "Completely Bounded Maps and Operator Algebras" Chapter 4
- Watrous (2018) "Theory of Quantum Information", §2.2, Theorem 2.22
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-!
## Minimal Stinespring Dilation structure
-/

/-- A minimal Stinespring dilation of a CP linear map `Φ : Op n →ₗ[ℂ] Op m` with
    environment dimension `envDim`.

    The dilation witnesses:
    - `isometry`: the Stinespring isometry `V : Matrix (Fin (m * envDim)) (Fin n) ℂ`
        satisfying `V†V = I_n`.
    - `recovers`: `Φ A = partialTraceB (V * A * V†)` for every `A : Op n`.
    - `env_minimal`: `envDim ≤ envDim'` for any other isometric dilation `V'` of `Φ`
        into environment dimension `envDim'`.

    The environment dimension of a minimal dilation equals `Matrix.rank (ChoiMatrix n m Φ)`;
    this equality is stated separately in `minimal_stinespring_exists`. -/
structure MinimalStinespringDilation
    {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) (envDim : ℕ) [NeZero envDim] [NeZero (m * envDim)] where
  /-- The Stinespring isometry V : ℂⁿ → ℂᵐ ⊗ ℂ^envDim. -/
  isometry : Matrix (Fin (m * envDim)) (Fin n) ℂ
  /-- V is a partial isometry from ℂⁿ: V†V = I. -/
  isometry_adj_mul : isometry† * isometry = 1
  /-- Conjugating by V and tracing out the environment recovers Φ. -/
  recovers : DilationRecovers (⇑Φ) isometry
  /-- Minimality: no dilation of Φ has a smaller environment. -/
  env_minimal : ∀ (envDim' : ℕ) [NeZero envDim'] [NeZero (m * envDim')]
    (V' : Matrix (Fin (m * envDim')) (Fin n) ℂ),
    V'† * V' = 1 →
    DilationRecovers (⇑Φ) V' →
    envDim ≤ envDim'

/-!
## Choi rank and its trivial upper bound
-/

/-- The Choi rank of a CP linear map is at most `n * m`.

    The Choi matrix `ChoiMatrix n m Φ` is an `(n * m) × (n * m)` matrix, so
    its rank is at most `n * m` by the trivial row-rank bound `Matrix.rank_le_height`. -/
theorem choiMatrix_rank_le_nm {n m : ℕ} [NeZero n] [NeZero m]
    (Φ : Op n →ₗ[ℂ] Op m) :
    Matrix.rank (ChoiMatrix n m ⇑Φ) ≤ n * m :=
  Matrix.rank_le_height (ChoiMatrix n m ⇑Φ)

end Quantum.Channels

/-!
## Submatrix conjugation algebra and reindexing of minimal Stinespring dilations

The following helpers package the matrix-algebraic identities needed to transport
a minimal Stinespring dilation through a pair of index `Equiv`s on the source and
output factors. -/
namespace Quantum.Channels

open Quantum.TensorProducts

/-- Reindex a flattened output-environment basis by changing only the output
coordinate and leaving the environment coordinate fixed. -/
def outputEnvEquiv {m m' envDim : ℕ} (eM : Fin m ≃ Fin m') :
    Fin (m * envDim) ≃ Fin (m' * envDim) :=
  finProdFinEquiv.symm.trans
    ((eM.prodCongr (Equiv.refl (Fin envDim))).trans finProdFinEquiv)

/-- Conjugating `A` by a submatrix of `M` equals the submatrix of the M-conjugation
of the appropriately reindexed `A`. Pure submatrix algebra. -/
lemma matrix_conj_submatrix_apply
    {M1 N1 M2 N2 : ℕ}
    (M : Matrix (Fin M1) (Fin N1) ℂ)
    (e_m : Fin M2 ≃ Fin M1) (e_n : Fin N2 ≃ Fin N1)
    (A : Op N2) :
    M.submatrix e_m e_n * A * (M.submatrix e_m e_n).conjTranspose =
      (M * A.submatrix e_n.symm e_n.symm * M.conjTranspose).submatrix e_m e_m := by
  have hA : A = (A.submatrix e_n.symm e_n.symm).submatrix e_n e_n := by
    ext i j; simp [Matrix.submatrix_apply]
  have h1 : (M.submatrix e_m e_n) * A =
      (M * A.submatrix e_n.symm e_n.symm).submatrix e_m e_n := by
    conv_lhs => rw [hA]
    exact Matrix.submatrix_mul_equiv M (A.submatrix e_n.symm e_n.symm) e_m e_n e_n
  rw [h1, Matrix.conjTranspose_submatrix]
  exact Matrix.submatrix_mul_equiv (M * A.submatrix e_n.symm e_n.symm)
    M.conjTranspose e_m e_n e_m

/-- Rectangular row and column reindexing by equivalences preserves `V†V = I`. -/
lemma submatrix_conjTranspose_mul_self_eq_one
    {M1 N1 M2 N2 : ℕ}
    (V : Matrix (Fin M1) (Fin N1) ℂ)
    (e_m : Fin M2 ≃ Fin M1) (e_n : Fin N2 ≃ Fin N1)
    (hV : V.conjTranspose * V = 1) :
    (V.submatrix e_m e_n).conjTranspose * V.submatrix e_m e_n = 1 := by
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv V.conjTranspose V e_n e_m e_n, hV]
  exact Matrix.submatrix_one _ e_n.injective

/-- Partial trace commutes with row reindexing through an `(eM × refl)`-style
product equiv. The row reindex `rowEq : Fin (m * envDim) ≃ Fin (m' * envDim)`
factors through `finProdFinEquiv` and reindexes only the first (output) factor
by `eM`, leaving the second (environment) factor alone. -/
lemma partialTraceB_submatrix_prodEquiv
    {m m' envDim : ℕ} (eM : Fin m ≃ Fin m') (M : Op (m' * envDim)) :
    let rowEq : Fin (m * envDim) ≃ Fin (m' * envDim) :=
      outputEnvEquiv (envDim := envDim) eM
    partialTraceB (M.submatrix rowEq rowEq) =
      (partialTraceB M).submatrix eM eM := by
  intro rowEq
  ext i j
  simp only [partialTraceB, Matrix.of_apply, Matrix.submatrix_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hrow : ∀ (a : Fin m) (b : Fin envDim),
      rowEq (finProdFinEquiv (a, b)) = finProdFinEquiv (eM a, b) := by
    intro a b
    simp [rowEq, outputEnvEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
      Prod.map_apply, Equiv.symm_apply_apply]
  rw [hrow i k, hrow j k]

/-- An entrywise channel reindexing identity can be inverted by applying the
inverse input and output basis equivalences. -/
lemma channel_reindex_relation_symm
    {n n' m m' : ℕ}
    (eN : Fin n ≃ Fin n') (eM : Fin m ≃ Fin m')
    {Φ : Op n →ₗ[ℂ] Op m} {Φ' : Op n' →ₗ[ℂ] Op m'}
    (h_equiv : ∀ A : Op n,
      ⇑Φ A = (⇑Φ' (A.submatrix eN.symm eN.symm)).submatrix eM eM) :
    ∀ A' : Op n',
      ⇑Φ' A' = (⇑Φ (A'.submatrix eN eN)).submatrix eM.symm eM.symm := by
  intro A'
  have heq := h_equiv (A'.submatrix eN eN)
  have hresub : (A'.submatrix eN eN).submatrix eN.symm eN.symm = A' := by
    ext i j; simp [Matrix.submatrix_apply]
  rw [hresub] at heq
  have hresubM : ((⇑Φ' A').submatrix eM eM).submatrix eM.symm eM.symm = ⇑Φ' A' := by
    ext i j; simp [Matrix.submatrix_apply]
  rw [heq, hresubM]

/-- **Reindex transport of a `MinimalStinespringDilation`.**

Given index equivalences `eN : Fin n ≃ Fin n'`, `eM : Fin m ≃ Fin m'`, and a
channel-relationship
`Φ A = (Φ' (A.submatrix eN.symm eN.symm)).submatrix eM eM`
(i.e. the two channels are entrywise reindexes of each other), a minimal
Stinespring dilation of `Φ` transfers to a minimal Stinespring dilation of `Φ'`,
preserving the environment dimension.

The construction is `V' := V.submatrix rowEqInv eN.symm` where `rowEqInv` lifts
`eM.symm` through `outputEnvEquiv` on the output × environment factorization.
The isometry property is preserved (submatrix algebra), the recovery is
transported (via `matrix_conj_submatrix_apply` and `partialTraceB_submatrix_prodEquiv`),
and minimality is preserved by transporting any candidate dilation of `Φ'` back
to one of `Φ`.

References:
* Watrous (2018) "Theory of Quantum Information", §2.2.3 -/
theorem MinimalStinespringDilation.reindex
    {n n' m m' envDim : ℕ}
    [NeZero n] [NeZero n'] [NeZero m] [NeZero m'] [NeZero envDim]
    [NeZero (m * envDim)] [NeZero (m' * envDim)]
    (eN : Fin n ≃ Fin n') (eM : Fin m ≃ Fin m')
    {Φ : Op n →ₗ[ℂ] Op m} {Φ' : Op n' →ₗ[ℂ] Op m'}
    (h_equiv : ∀ A : Op n,
      ⇑Φ A = (⇑Φ' (A.submatrix eN.symm eN.symm)).submatrix eM eM)
    (dil : MinimalStinespringDilation Φ envDim) :
    Nonempty (MinimalStinespringDilation Φ' envDim) := by
  obtain ⟨V, hVV, hRec, hMin⟩ := dil
  let rowEqInv : Fin (m' * envDim) ≃ Fin (m * envDim) :=
    outputEnvEquiv (envDim := envDim) eM.symm
  let V' : Matrix (Fin (m' * envDim)) (Fin n') ℂ :=
    V.submatrix rowEqInv eN.symm
  have h_equiv' : ∀ A' : Op n',
      ⇑Φ' A' = (⇑Φ (A'.submatrix eN eN)).submatrix eM.symm eM.symm :=
    channel_reindex_relation_symm eN eM h_equiv
  refine ⟨{
    isometry := V'
    isometry_adj_mul := ?_
    recovers := ?_
    env_minimal := ?_
  }⟩
  · show V'.conjTranspose * V' = 1
    exact submatrix_conjTranspose_mul_self_eq_one V rowEqInv eN.symm hVV
  · intro A'
    show ⇑Φ' A' = partialTraceB (V' * A' * V'.conjTranspose)
    have hMA :
        V' * A' * V'.conjTranspose =
        (V * A'.submatrix eN eN * V.conjTranspose).submatrix rowEqInv rowEqInv := by
      simpa [Equiv.symm_symm] using matrix_conj_submatrix_apply V rowEqInv eN.symm A'
    rw [hMA]
    have hpt :=
      partialTraceB_submatrix_prodEquiv (m := m') (m' := m) (envDim := envDim) eM.symm
        (V * A'.submatrix eN eN * V.conjTranspose)
    rw [hpt]
    rw [h_equiv' A']
    rw [hRec]
  · intro envDim' hne hne' V'' hVV'' hRec''
    let rowEq' : Fin (m * envDim') ≃ Fin (m' * envDim') :=
      outputEnvEquiv (envDim := envDim') eM
    apply hMin envDim' (V''.submatrix rowEq' eN)
    · exact submatrix_conjTranspose_mul_self_eq_one V'' rowEq' eN hVV''
    · intro A
      show ⇑Φ A = partialTraceB
          (V''.submatrix rowEq' eN * A *
            (V''.submatrix rowEq' eN).conjTranspose)
      have hWA :
          V''.submatrix rowEq' eN * A * (V''.submatrix rowEq' eN).conjTranspose =
          (V'' * A.submatrix eN.symm eN.symm * V''.conjTranspose).submatrix
            rowEq' rowEq' :=
        matrix_conj_submatrix_apply V'' rowEq' eN A
      rw [hWA]
      have hpt :=
        partialTraceB_submatrix_prodEquiv (m := m) (m' := m') (envDim := envDim') eM
          (V'' * A.submatrix eN.symm eN.symm * V''.conjTranspose)
      rw [hpt]
      rw [← hRec'']
      exact h_equiv A

end Quantum.Channels

end -- noncomputable section
