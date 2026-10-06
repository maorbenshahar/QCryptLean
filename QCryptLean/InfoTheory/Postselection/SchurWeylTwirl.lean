import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.Quantum.TensorProducts.TensorPow
import QCryptLean.Quantum.Symmetry.PairedProjector
import QCryptLean.Math.Probability.HaarMeasure

/-!
# QKD postselection — generalized paired symmetric projector and the Schur–Weyl twirl (SP1)

Infrastructure for the fixed-marginal de Finetti reduction of
Nahar–Tupkary–Zhao–Lütkenhaus–Tan 2024 (arXiv:2403.11851), **Lemma 10** (App. A,
lines 1516–1614) and **Theorem 1** (App. A), a faithful transcription of their argument.

The universal CKR machinery already generic in one local dimension `d`
(`InfoTheory.DeFinetti.symmetricProjectorPaired`,
`Quantum/Channels/CPTP/CKRBound/Reference/Paired.lean`) is
here generalized to a pair of dimensions `dA ≤ dR`, in the **blocked `Aⁿ ⊗ Rⁿ` convention**,
so that the Schur–Weyl twirl `Tₙ` of Nahar et al. Lemma 10 can be stated and its flattening
(`κₙ`) proved (`SchurWeylFlatten.lean`).

## Main definitions
- `Quantum.Symmetry.symmetricProjectorPairedGen dA dR n` : `P_Sym`, the projector onto
  `Symⁿ(ℂ^{dA}⊗ℂ^{dR})` in the blocked convention (generalizes `symmetricProjectorPaired`;
  `symmetricProjectorPaired d n = symmetricProjectorPairedGen d d n` definitionally).
- `InfoTheory.Postselection.maxEntangledProjectorPaired dA dR n hdim` : `Θₙ = |Θ⟩⟨Θ|`, the
  (un-normalized) maximally entangled projector between `Aⁿ` and the `dA`-embedded diagonal
  of `Rⁿ` (blocked `|θ⟩^{⊗n}`).
- `InfoTheory.Postselection.maxEntangledUnitaryTwirl dA dR n hdim` : `Tₙ`, Nahar et al.'s Haar twirl
  `∫ (1_{Aⁿ}⊗U^{⊗n}) Θₙ (1_{Aⁿ}⊗U^{⊗n})† dU` (Nahar et al. Lemma 10, line 1521), with
  `U^{⊗n} = Quantum.TensorProducts.Op.tensorPow U n`.

## Main statements
- The projector, Hermitian, positivity, trace, rank and support properties of
  `symmetricProjectorPairedGen` live in `Quantum/Symmetry/PairedProjector.lean` under
  `Quantum.Symmetry`.
- `InfoTheory.Postselection.exists_flatten_maxEntangledUnitaryTwirl` : **SP1 = Nahar et al. Lemma
10**, the
  Schur–Weyl twirl-flattening. Proved in `SchurWeylFlatten.lean` via a
  duality-free route: no Schur–Weyl duality (Specht/Weyl modules) needed. The
  hypothesis `dA ≤ dR` is load-bearing: it is exactly what makes `κₙ` invertible
  (`c_λ = dim[λ]/dim W_R^λ > 0`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Math.RepresentationTheory
open Quantum.Symmetry InfoTheory.DeFinetti Quantum.Channels MeasureTheory Math.HaarMeasure
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

/-! ## Generalized interleaving equivalence `Fin (dAⁿ · dRⁿ) ≃ Fin ((dA·dR)ⁿ)`

Generalizes `InfoTheory.DeFinetti.interleavingEquiv` (the `dA = dR` case) to two dimensions.
Maps the concatenated tensor index `(a₁,…,aₙ, r₁,…,rₙ)` to the interleaved paired index
`((a₁,r₁),…,(aₙ,rₙ))`, conjugating the paired permutation action `U_σ^{dA} ⊗ U_σ^{dR}` to the
standard action `U_σ^{dA·dR}`. -/

/-- **Generalized interleaving equivalence** `W : Fin (dAⁿ · dRⁿ) ≃ Fin ((dA·dR)ⁿ)`.

    Maps `(a₁,…,aₙ, r₁,…,rₙ) ∈ Fin(dAⁿ × dRⁿ)` to `((a₁,r₁),…,(aₙ,rₙ)) ∈ Fin((dA·dR)ⁿ)`. -/
def interleavingEquivGen (dA dR n : ℕ) :
    Fin (dA ^ n * dR ^ n) ≃ Fin ((dA * dR) ^ n) where
  toFun := fun i =>
    let ab := finProdFinEquiv.symm i
    let ta := finFunctionFinEquiv.symm ab.1
    let tb := finFunctionFinEquiv.symm ab.2
    finFunctionFinEquiv (fun j => finProdFinEquiv (ta j, tb j))
  invFun := fun i =>
    let t := finFunctionFinEquiv.symm i
    let pairs := fun j => finProdFinEquiv.symm (t j)
    finProdFinEquiv (finFunctionFinEquiv (fun j => (pairs j).1),
                     finFunctionFinEquiv (fun j => (pairs j).2))
  left_inv := fun i => by
    dsimp only []
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Prod.mk.eta]
  right_inv := fun i => by
    dsimp only []
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Prod.mk.eta]

/-- The `A`-digit of `interleavingEquivGen`'s inverse at position `k` is the first component of
the corresponding `(dA·dR)`-digit. -/
lemma interleavingEquivGen_digit_fst {dA dR n : ℕ} [NeZero dA] [NeZero dR]
    (a : Fin ((dA * dR) ^ n)) (k : Fin n) :
    (@finFunctionFinEquiv dA n).symm ((interleavingEquivGen dA dR n).symm a).divNat k =
      (finProdFinEquiv.symm
        ((@finFunctionFinEquiv (dA * dR) n).symm a k)).1 := by
  simp only [interleavingEquivGen]
  dsimp
  rw [finProdFinEquiv_apply_divNat, Equiv.symm_apply_apply]

/-- The `R`-digit of `interleavingEquivGen`'s inverse at position `k` is the second component of
the corresponding `(dA·dR)`-digit. -/
lemma interleavingEquivGen_digit_snd {dA dR n : ℕ} [NeZero dA] [NeZero dR]
    (a : Fin ((dA * dR) ^ n)) (k : Fin n) :
    (@finFunctionFinEquiv dR n).symm ((interleavingEquivGen dA dR n).symm a).modNat k =
      (finProdFinEquiv.symm
        ((@finFunctionFinEquiv (dA * dR) n).symm a k)).2 := by
  simp only [interleavingEquivGen]
  dsimp
  rw [finProdFinEquiv_apply_modNat, Equiv.symm_apply_apply]

private lemma interleavingEquivGen_perm_condition_iff {dA dR n : ℕ} [NeZero dA] [NeZero dR]
    (σ : Equiv.Perm (Fin n)) (i j : Fin ((dA * dR) ^ n)) :
    let tie_A := @finFunctionFinEquiv dA n
    let tie_R := @finFunctionFinEquiv dR n
    let tie_P := @finFunctionFinEquiv (dA * dR) n
    (tie_P.symm i = tie_P.symm j ∘ ⇑(Equiv.symm σ)) ↔
      (tie_A.symm ((interleavingEquivGen dA dR n).symm i).divNat =
        tie_A.symm ((interleavingEquivGen dA dR n).symm j).divNat
          ∘ ⇑(Equiv.symm σ) ∧
       tie_R.symm ((interleavingEquivGen dA dR n).symm i).modNat =
        tie_R.symm ((interleavingEquivGen dA dR n).symm j).modNat
          ∘ ⇑(Equiv.symm σ)) := by
  dsimp
  constructor
  · intro h
    refine ⟨funext fun k => ?_, funext fun k => ?_⟩
    · rw [interleavingEquivGen_digit_fst, Function.comp_apply, interleavingEquivGen_digit_fst]
      exact congr_arg (fun x => (finProdFinEquiv.symm x).1) (congr_fun h k)
    · rw [interleavingEquivGen_digit_snd, Function.comp_apply, interleavingEquivGen_digit_snd]
      exact congr_arg (fun x => (finProdFinEquiv.symm x).2) (congr_fun h k)
  · intro ⟨h1, h2⟩
    funext k
    have hk1 := congr_fun h1 k
    have hk2 := congr_fun h2 k
    rw [interleavingEquivGen_digit_fst, Function.comp_apply, interleavingEquivGen_digit_fst] at hk1
    rw [interleavingEquivGen_digit_snd, Function.comp_apply, interleavingEquivGen_digit_snd] at hk2
    exact (Equiv.injective finProdFinEquiv.symm) (Prod.ext hk1 hk2)

/-- The generalized interleaving conjugates the paired permutation action
    `U_σ^{dA} ⊗ U_σ^{dR}` to the standard action `U_σ^{dA·dR}`. -/
lemma interleavingEquivGen_conjugates_perm {dA dR n : ℕ} [NeZero dA] [NeZero dR]
    (σ : Equiv.Perm (Fin n)) :
    let e := interleavingEquivGen dA dR n
    Matrix.reindex e e (Op.tensor
      (permutationRepresentation dA n σ)
      (permutationRepresentation dR n σ)) =
    permutationRepresentation (dA * dR) n σ := by
  intro e
  ext i j
  simp only [Op.tensor, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    permutationRepresentation, Matrix.of_apply]
  have cond_iff :
      ((@finFunctionFinEquiv (dA * dR) n).symm i =
          (@finFunctionFinEquiv (dA * dR) n).symm j ∘ ⇑(Equiv.symm σ)) ↔
        ((@finFunctionFinEquiv dA n).symm
            (finProdFinEquiv.symm (e.symm i)).1 =
          (@finFunctionFinEquiv dA n).symm
            (finProdFinEquiv.symm (e.symm j)).1 ∘ ⇑(Equiv.symm σ) ∧
         (@finFunctionFinEquiv dR n).symm
            (finProdFinEquiv.symm (e.symm i)).2 =
         (@finFunctionFinEquiv dR n).symm
            (finProdFinEquiv.symm (e.symm j)).2 ∘ ⇑(Equiv.symm σ)) := by
    simpa [e] using interleavingEquivGen_perm_condition_iff (dA := dA) (dR := dR) σ i j
  split_ifs with h1 h2 h3 h3 h3 h3 <;>
    simp_all [mul_one, mul_zero]

/-! ## The generalized paired symmetric projector `P_Sym` -/

/-- The `dA = dR` specialization recovers `symmetricProjectorPaired`. -/
lemma symmetricProjectorPaired_eq_gen (d n : ℕ) [NeZero d] [NeZero n] :
    symmetricProjectorPaired d n = symmetricProjectorPairedGen d d n := rfl

/-- The generalized interleaving conjugates `P_Sym` to the standard symmetric projector. -/
lemma interleavingEquivGen_conjugates_projector {dA dR n : ℕ}
    [NeZero dA] [NeZero dR] [NeZero n] :
    Matrix.reindex (interleavingEquivGen dA dR n) (interleavingEquivGen dA dR n)
      (symmetricProjectorPairedGen dA dR n) = symmetricProjector (dA * dR) n := by
  unfold symmetricProjectorPairedGen
  simp only [symmetricProjector, symmetricProjectorRep]
  set e := interleavingEquivGen dA dR n
  have h_smul : ∀ (c : ℂ) (M : Op (dA ^ n * dR ^ n)),
      Matrix.reindex e e (c • M) = c • Matrix.reindex e e M := by
    intro c M; ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  have h_sum : ∀ (f : Equiv.Perm (Fin n) → Op (dA ^ n * dR ^ n)),
      Matrix.reindex e e (∑ σ : Equiv.Perm (Fin n), f σ) =
        ∑ σ : Equiv.Perm (Fin n), Matrix.reindex e e (f σ) := by
    intro f; ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [h_smul, h_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact interleavingEquivGen_conjugates_perm σ

/-! ## The maximally entangled Haar twirl `Tₙ` (Nahar et al. Lemma 10) and SP1 -/

-- Frobenius (Hilbert–Schmidt) normed structure on matrices, so the Bochner integral
-- `∫ … ∂(haarProbUnitary dR)` defining `Tₙ` is well-typed (matching `schur_lemma_symmetric`).
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/-- **Maximally entangled paired projector** `Θₙ = |Θ⟩⟨Θ|`, the
    (un-normalized) maximally entangled projector between `Aⁿ` and the `dA`-embedded
    diagonal of `Rⁿ` (the blocked `|θ⟩^{⊗n}`, `|θ⟩ = Σ_{i<dA}|i⟩|i⟩`).

    `⟨(a,r)|Θ⟩ = 1` if `r = ι⁽ⁿ⁾(a)` (else `0`), where `ι⁽ⁿ⁾` is the **factor-wise**
    diagonal embedding `Fin (dAⁿ) ↪ Fin (dRⁿ)` — decode `a` into `n` base-`dA` digits,
    apply `ι = Fin.castLE hdim : Fin dA ↪ Fin dR` to each, re-encode in base `dR`. This is
    the genuine `|θ⟩^{⊗n}` (`|θ⟩ = Σ_{i<dA}|i⟩|i⟩`) in the blocked convention; a *flat*
    `Fin.castLE` on `Fin (dAⁿ)` would embed the wrong subspace and break the tensor-power
    structure the Haar twirl relies on. Explicit-entry form. -/
def maxEntangledProjectorPaired (dA dR n : ℕ) (hdim : dA ≤ dR) :
    Op (dA ^ n * dR ^ n) :=
  let emb : Fin (dA ^ n) → Fin (dR ^ n) := fun a =>
    finFunctionFinEquiv (fun j => Fin.castLE hdim (finFunctionFinEquiv.symm a j))
  let Θ : Fin (dA ^ n * dR ^ n) → ℂ := fun i =>
    if (finProdFinEquiv.symm i).2 = emb (finProdFinEquiv.symm i).1 then 1 else 0
  Matrix.of (fun i j => Θ i * (starRingEnd ℂ) (Θ j))

/-- **Nahar et al.'s Haar twirl** `Tₙ` (Nahar et al. Lemma 10, line 1521):
    `Tₙ = ∫ (1_{Aⁿ} ⊗ U^{⊗n}) Θₙ (1_{Aⁿ} ⊗ U^{⊗n})† dU`,
    the Bochner integral over the normalized Haar measure on `U(dR)`. -/
def maxEntangledUnitaryTwirl (dA dR n : ℕ) (hdim : dA ≤ dR) [NeZero dR] :
    Op (dA ^ n * dR ^ n) :=
  ∫ U : Matrix.unitaryGroup (Fin dR) ℂ,
      (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))
        * maxEntangledProjectorPaired dA dR n hdim
        * (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))ᴴ
    ∂(haarProbUnitary dR)

/- **SP1 = Nahar et al. Lemma 10 (Schur–Weyl twirl-flattening).** There is a positive-semidefinite,
   invertible `κₙ` on `Aⁿ`, `Sₙ`-central (so `κₙ ⊗ id` commutes with `P_Sym`), that flattens
   the sub-maximal Haar twirl `Tₙ` to the symmetric projector:

   `Tₙ = (κₙ ⊗ id_{Rⁿ}) · P_Sym`.

   (Equivalently Nahar et al. Eq. (A1): `(κₙ⊗id)^{-1/2} Tₙ (κₙ⊗id)^{-1/2} = P_Sym`, which follows by
   CFC from this product form and the commutation.)

   `InfoTheory.Postselection.exists_flatten_maxEntangledUnitaryTwirl` — the Lean formalization of
   the
   flattening identity displayed above — is declared and proved in
   `SchurWeylFlatten.lean` (not in this file: the proof needs the Ω-layer
   (`SchurWeylKappa.lean`), the twirl-projection layer (`SchurWeylTwirlProjection.lean`) and the
   E2 commutant assembly (`SchurWeylCommutantAssembly.lean`), all downstream of this file in the
   import order). Witness `κₙ := (symmetricProjectorPairedTraceR dA dR n)⁻¹` (`Ω⁻¹`, a
   duality-free route) — no Schur–Weyl duality (Specht/Weyl modules) needed; see
   `SchurWeylFlatten.lean`'s module docstring for the assembly. -/

end InfoTheory.Postselection

end
