import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import QCryptLean.Quantum.TensorProducts.Rectangular
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Math.LinearAlgebra.KrausCompleteness

/-!
# Separable channels and positivity under partial transpose

A complete product-Kraus family defines a separable channel. Its Choi matrix, reshuffled into
the two laboratory factors, is positive under partial transpose.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- A complete finite Kraus family whose matrices are products across a fixed bipartition. -/
def IsSeparableOperation {rA rB sA sB : ℕ} (Φ : Op (rA * rB) →ₗ[ℂ] Op (sA * sB)) : Prop :=
  ∃ (m : ℕ) (A : Fin m → Matrix (Fin sA) (Fin rA) ℂ)
    (B : Fin m → Matrix (Fin sB) (Fin rB) ℂ),
    (∀ ρ, Φ ρ = ∑ i, tensorRect (A i) (B i) * ρ * (tensorRect (A i) (B i))ᴴ) ∧
    ∑ i, (tensorRect (A i) (B i))ᴴ * tensorRect (A i) (B i) = 1

/-- Any finite complete product-Kraus family presents a separable channel. -/
theorem isSeparableOperation_of_fintype {rA rB sA sB : ℕ} {ι : Type} [Fintype ι]
    (Φ : Op (rA * rB) →ₗ[ℂ] Op (sA * sB))
    (A : ι → Matrix (Fin sA) (Fin rA) ℂ) (B : ι → Matrix (Fin sB) (Fin rB) ℂ)
    (hmap : ∀ ρ, Φ ρ = ∑ i, tensorRect (A i) (B i) * ρ * (tensorRect (A i) (B i))ᴴ)
    (hcomp : ∑ i, (tensorRect (A i) (B i))ᴴ * tensorRect (A i) (B i) = 1) :
    IsSeparableOperation Φ := by
  refine ⟨Fintype.card ι, fun k => A ((Fintype.equivFin ι).symm k),
    fun k => B ((Fintype.equivFin ι).symm k), fun ρ => ?_, ?_⟩
  · rw [hmap]
    exact Fintype.sum_equiv (Fintype.equivFin ι) _ _ (fun i => by simp)
  · rw [← hcomp]
    exact (Fintype.sum_equiv (Fintype.equivFin ι) _ _ (fun i => by simp)).symm

/-- Separable channels are closed under complete sums of product-operator sandwiches. -/
theorem isSeparableOperation_sum_sandwich {rA rB mA mB nA nB sA sB : ℕ} {Xo : Type} [Fintype Xo]
    (Φ : Op (rA * rB) →ₗ[ℂ] Op (sA * sB)) (Ψ : Xo → Op (mA * mB) →ₗ[ℂ] Op (nA * nB))
    (Ra : Xo → Matrix (Fin mA) (Fin rA) ℂ) (Rb : Xo → Matrix (Fin mB) (Fin rB) ℂ)
    (La : Xo → Matrix (Fin sA) (Fin nA) ℂ) (Lb : Xo → Matrix (Fin sB) (Fin nB) ℂ)
    (hΨ : ∀ x, IsSeparableOperation (Ψ x))
    (hL : ∀ x, (tensorRect (La x) (Lb x))ᴴ * tensorRect (La x) (Lb x) = 1)
    (hR : ∑ x, (tensorRect (Ra x) (Rb x))ᴴ * tensorRect (Ra x) (Rb x) = 1)
    (hΦ : ∀ ρ, Φ ρ = ∑ x, tensorRect (La x) (Lb x)
        * Ψ x (tensorRect (Ra x) (Rb x) * ρ * (tensorRect (Ra x) (Rb x))ᴴ)
        * (tensorRect (La x) (Lb x))ᴴ) :
    IsSeparableOperation Φ := by
  choose m A B hmap hcomp using hΨ
  have hprod : ∀ x (i : Fin (m x)),
      tensorRect (La x * A x i * Ra x) (Lb x * B x i * Rb x)
        = tensorRect (La x) (Lb x) * tensorRect (A x i) (B x i) * tensorRect (Ra x) (Rb x) :=
    fun x i => by rw [tensorRect_mul, tensorRect_mul]
  refine isSeparableOperation_of_fintype (ι := (x : Xo) × Fin (m x)) Φ
    (fun p => La p.1 * A p.1 p.2 * Ra p.1) (fun p => Lb p.1 * B p.1 p.2 * Rb p.1)
    (fun ρ => ?_) ?_
  · -- expand `Ψ x` into its Kraus sum and merge the three conjugations
    rw [hΦ, Fintype.sum_sigma]
    refine Fintype.sum_congr _ _ fun x => ?_
    rw [hmap, Matrix.mul_sum, Matrix.sum_mul]
    refine Fintype.sum_congr _ _ fun i => ?_
    rw [hprod, conj_mul_conj, conj_mul_conj]
  · -- completeness: `Lₓ` cancels, the branch family sums to `Rₓᴴ Rₓ`, and those sum to `1`
    rw [Fintype.sum_sigma, ← hR]
    refine Fintype.sum_congr _ _ fun x => ?_
    simp only [hprod]
    exact sum_conjTranspose_mul_self_sandwich _ _ _ (hL x) (hcomp x)

/-- Partial transposition on the second factor of a bipartite register. -/
def partialTransposeB (dA dB : ℕ) (M : Op (dA * dB)) :
    Op (dA * dB) :=
  Matrix.of fun α β =>
    M (finProdFinEquiv ((finProdFinEquiv.symm α).1, (finProdFinEquiv.symm β).2))
      (finProdFinEquiv ((finProdFinEquiv.symm β).1, (finProdFinEquiv.symm α).2))

theorem partialTransposeB_apply (dA dB : ℕ) (M : Op (dA * dB))
    (a c : Fin dA) (b d : Fin dB) :
    partialTransposeB dA dB M (finProdFinEquiv (a, b)) (finProdFinEquiv (c, d))
      = M (finProdFinEquiv (a, d)) (finProdFinEquiv (c, b)) := by
  simp only [partialTransposeB, Matrix.of_apply, Equiv.symm_apply_apply]

/-- Positivity after partial transposition on the second factor. -/
def IsPPT (dA dB : ℕ) (M : Op (dA * dB)) : Prop :=
  (partialTransposeB dA dB M).PosSemidef

theorem partialTransposeB_sum {dA dB : ℕ} {ι : Type*} [Fintype ι]
    (M : ι → Op (dA * dB)) :
    partialTransposeB dA dB (∑ i, M i) = ∑ i, partialTransposeB dA dB (M i) := by
  ext α β
  simp only [partialTransposeB, Matrix.of_apply, Matrix.sum_apply]

theorem partialTransposeB_tensor {dA dB : ℕ} (P : Op dA) (Q : Op dB) :
    partialTransposeB dA dB (Op.tensor P Q) = Op.tensor P Qᵀ := by
  ext α β
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective α
  obtain ⟨⟨c, d⟩, rfl⟩ := finProdFinEquiv.surjective β
  rw [partialTransposeB_apply, Op_tensor_apply_finProd, Op_tensor_apply_finProd]
  simp only [Equiv.symm_apply_apply, Matrix.transpose_apply]

/-- A sum of tensor products of positive semidefinite matrices has positive partial transpose. -/
theorem isPPT_sum_tensor {dA dB : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → Op dA) (Q : ι → Op dB)
    (hP : ∀ i, (P i).PosSemidef) (hQ : ∀ i, (Q i).PosSemidef) :
    IsPPT dA dB (∑ i, Op.tensor (P i) (Q i)) := by
  unfold IsPPT
  rw [partialTransposeB_sum]
  refine Matrix.posSemidef_sum Finset.univ fun i _ => ?_
  rw [partialTransposeB_tensor]
  exact Op.tensor_posSemidef_mathlib (hP i) ((hQ i).transpose)

/-- Regroup the Choi register from input/output order into the two laboratory factors. -/
def choiReshuffle (rA rB sA sB : ℕ) :
    Fin (rA * rB * (sA * sB)) ≃ Fin (rA * sA * (rB * sB)) :=
  (finProdFinEquiv.symm.trans
      ((finProdFinEquiv.symm.prodCongr finProdFinEquiv.symm).trans
        ((Equiv.prodProdProdComm (Fin rA) (Fin rB) (Fin sA) (Fin sB)).trans
          (finProdFinEquiv.prodCongr finProdFinEquiv)))).trans finProdFinEquiv

theorem choiReshuffle_symm_apply (rA rB sA sB : ℕ) (iA : Fin rA) (aA : Fin sA)
    (iB : Fin rB) (aB : Fin sB) :
    (choiReshuffle rA rB sA sB).symm
        (finProdFinEquiv (finProdFinEquiv (iA, aA), finProdFinEquiv (iB, aB)))
      = finProdFinEquiv (finProdFinEquiv (iA, iB), finProdFinEquiv (aA, aB)) := by
  simp [choiReshuffle, Equiv.prodProdProdComm]

/-- The entries of a Choi matrix read directly from a finite Kraus presentation. -/
theorem choi_entry_of_kraus {n m : ℕ} [NeZero n] [NeZero m] {ι : Type*} [Fintype ι]
    (K : ι → Matrix (Fin m) (Fin n) ℂ) (Φ : Op n → Op m)
    (hΦ : ∀ ρ, Φ ρ = ∑ x, K x * ρ * (K x)ᴴ) (i j : Fin n) (a b : Fin m) :
    ChoiMatrix n m Φ (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b))
      = ∑ x, K x a i * (starRingEnd ℂ) (K x b j) := by
  simp only [ChoiMatrix, Matrix.of_apply]
  rw [hΦ]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, ite_and]

/-- The laboratory-grouped Choi matrix of a product-Kraus map is a sum of product states. -/
theorem reindex_choi_eq_sum_tensor {rA rB sA sB : ℕ}
    [NeZero rA] [NeZero rB] [NeZero sA] [NeZero sB] (Φ : Op (rA * rB) →ₗ[ℂ] Op (sA * sB))
    {m : ℕ} (A : Fin m → Matrix (Fin sA) (Fin rA) ℂ)
    (B : Fin m → Matrix (Fin sB) (Fin rB) ℂ)
    (hΦ : ∀ ρ, Φ ρ = ∑ i, tensorRect (A i) (B i) * ρ * (tensorRect (A i) (B i))ᴴ) :
    Matrix.reindex (choiReshuffle rA rB sA sB) (choiReshuffle rA rB sA sB)
        (ChoiMatrix (rA * rB) (sA * sB) ⇑Φ)
      = ∑ x, Op.tensor
          (Matrix.vecMulVec
            (fun γ => A x (finProdFinEquiv.symm γ).2 (finProdFinEquiv.symm γ).1)
            (star fun γ => A x (finProdFinEquiv.symm γ).2 (finProdFinEquiv.symm γ).1))
          (Matrix.vecMulVec
            (fun γ => B x (finProdFinEquiv.symm γ).2 (finProdFinEquiv.symm γ).1)
            (star fun γ => B x (finProdFinEquiv.symm γ).2 (finProdFinEquiv.symm γ).1)) := by
  ext γ δ
  obtain ⟨⟨γA, γB⟩, rfl⟩ := finProdFinEquiv.surjective γ
  obtain ⟨⟨iA, aA⟩, rfl⟩ := finProdFinEquiv.surjective γA
  obtain ⟨⟨iB, aB⟩, rfl⟩ := finProdFinEquiv.surjective γB
  obtain ⟨⟨δA, δB⟩, rfl⟩ := finProdFinEquiv.surjective δ
  obtain ⟨⟨jA, bA⟩, rfl⟩ := finProdFinEquiv.surjective δA
  obtain ⟨⟨jB, bB⟩, rfl⟩ := finProdFinEquiv.surjective δB
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, choiReshuffle_symm_apply,
    choiReshuffle_symm_apply, choi_entry_of_kraus _ _ hΦ]
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Op_tensor_apply_finProd]
  simp only [tensorRect_apply, Matrix.vecMulVec, Pi.star_apply, Complex.star_def,
    Matrix.of_apply, Equiv.symm_apply_apply, map_mul]
  ring

/-- A separable channel has positive partial transpose across the laboratory Choi bipartition. -/
theorem isSeparable_choi_isPPT {rA rB sA sB : ℕ}
    [NeZero rA] [NeZero rB] [NeZero sA] [NeZero sB] (Φ : Op (rA * rB) →ₗ[ℂ] Op (sA * sB))
    (h : IsSeparableOperation Φ) :
    IsPPT (rA * sA) (rB * sB)
      (Matrix.reindex (choiReshuffle rA rB sA sB)
        (choiReshuffle rA rB sA sB) (ChoiMatrix (rA * rB) (sA * sB) ⇑Φ)) := by
  obtain ⟨m, A, B, hΦ, -⟩ := h
  rw [reindex_choi_eq_sum_tensor Φ A B hΦ]
  exact isPPT_sum_tensor _ _ (fun _ => Matrix.posSemidef_vecMulVec_self_star _)
    (fun _ => Matrix.posSemidef_vecMulVec_self_star _)

/-- The Choi entries of a channel that relabels the computational basis. -/
theorem choi_of_reindexMap {d : ℕ} [NeZero d] (f : Fin d ≃ Fin d) (i j a b : Fin d) :
    ChoiMatrix d d (fun ρ => Matrix.submatrix ρ f.symm f.symm)
        (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b))
      = if a = f i ∧ b = f j then 1 else 0 := by
  have hd : ∀ x y : Fin d,
      ((finProdFinEquiv (x, y) : Fin (d * d)).divNat = x ∧
        (finProdFinEquiv (x, y) : Fin (d * d)).modNat = y) := by
    intro x y
    have h := Equiv.symm_apply_apply (finProdFinEquiv (m := d) (n := d)) (x, y)
    rw [finProdFinEquiv_symm_apply] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  simp [ChoiMatrix, Matrix.submatrix_apply, Equiv.symm_apply_eq,
    (hd i a).1, (hd i a).2, (hd j b).1, (hd j b).2]

end Quantum.Channels
