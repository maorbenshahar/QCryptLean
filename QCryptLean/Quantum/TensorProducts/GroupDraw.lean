import QCryptLean.Quantum.TensorProducts.Basic
import QCryptLean.Math.LinearAlgebra.PermutationMatrix

/-!
# Group translations of labelled operator mixtures

A right translation of a finite group index is absorbed by a permutation of its label register.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

/-- Right translation of the announced group element, read through the register naming `eG`. -/
def announceTranslation {G : Type} [Group G] {N : ℕ} (eG : G ≃ Fin N) (σ : G) :
    Equiv.Perm (Fin N) :=
  (eG.symm.trans (Equiv.mulRight σ⁻¹)).trans eG

@[simp] theorem announceTranslation_apply {G : Type} [Group G] {N : ℕ} (eG : G ≃ Fin N)
    (σ g : G) : announceTranslation eG σ (eG g) = eG (g * σ⁻¹) := by
  simp [announceTranslation]

/-- The unitary that relabels the announced-outcome register by the right translation. -/
def announceRelabelOp {G : Type} [Group G] {N p q : ℕ} (eG : G ≃ Fin N) (h : p * N = q)
    (σ : G) : Op q :=
  Op.castDim h (Op.tensor (1 : Op p) (Equiv.Perm.permMatrix ℂ (announceTranslation eG σ).symm))

theorem announceRelabelOp_conjTranspose_mul_self {G : Type} [Group G] {N p q : ℕ}
    (eG : G ≃ Fin N) (h : p * N = q) (σ : G) :
    (announceRelabelOp eG h σ)ᴴ * announceRelabelOp eG h σ = 1 := by
  rw [announceRelabelOp, Op.castDim_conjTranspose, Op.castDim_mul, Op.tensor_conjTranspose,
    Matrix.conjTranspose_one, Op.tensor_mul, Matrix.one_mul,
    Equiv.Perm.permMatrix_conjTranspose_mul_self, Op.tensor_one, Op.castDim_one]

theorem announceRelabelOp_conj_castDim_tensor {G : Type} [Group G] {N p q : ℕ}
    (eG : G ≃ Fin N) (h : p * N = q) (σ : G) (Yop : Op p) (g : G) :
    announceRelabelOp eG h σ *
        Op.castDim h (Op.tensor Yop (Matrix.single (eG g) (eG g) (1 : ℂ))) *
        (announceRelabelOp eG h σ)ᴴ =
      Op.castDim h (Op.tensor Yop (Matrix.single (eG (g * σ⁻¹)) (eG (g * σ⁻¹)) (1 : ℂ))) := by
  rw [announceRelabelOp, Op.castDim_conjTranspose, Op.castDim_mul, Op.castDim_mul,
    Op.tensor_conjTranspose, Matrix.conjTranspose_one, Op.tensor_mul, Op.tensor_mul,
    Matrix.one_mul, Matrix.mul_one, Equiv.Perm.permMatrix_conj_single, announceTranslation_apply]

/-- **The announced-outcome register absorbs a group translation.**

A uniform draw of a group element `g`, announced into its own register and used to build the
branch operator, is invariant under translating the branch label by a fixed `σ`: the translation
reappears as a *relabelling of the announcement*, i.e. as conjugation by a permutation unitary
supported on the announcement register alone.

Nothing here knows about protocols, permutations of rounds, or BB84. -/
theorem sum_castDim_tensor_single_translate {G : Type} [Fintype G] [Group G] {N p q : ℕ}
    (eG : G ≃ Fin N) (h : p * N = q) (Xf : G → Op p) (σ : G) :
    ∑ g : G, Op.castDim h (Op.tensor (Xf (g * σ)) (Matrix.single (eG g) (eG g) (1 : ℂ))) =
      announceRelabelOp eG h σ *
        (∑ g : G, Op.castDim h (Op.tensor (Xf g) (Matrix.single (eG g) (eG g) (1 : ℂ)))) *
        (announceRelabelOp eG h σ)ᴴ := by
  have hsub : ∑ g : G, Op.castDim h (Op.tensor (Xf (g * σ))
        (Matrix.single (eG g) (eG g) (1 : ℂ))) =
      ∑ g : G, Op.castDim h (Op.tensor (Xf g)
        (Matrix.single (eG (g * σ⁻¹)) (eG (g * σ⁻¹)) (1 : ℂ))) := by
    refine Eq.trans ?_ (Equiv.sum_comp (Equiv.mulRight σ)
      (fun g : G => Op.castDim h (Op.tensor (Xf g)
        (Matrix.single (eG (g * σ⁻¹)) (eG (g * σ⁻¹)) (1 : ℂ)))))
    exact Finset.sum_congr rfl fun g _ => by simp
  rw [hsub, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun g _ =>
    (announceRelabelOp_conj_castDim_tensor eG h σ (Xf g) g).symm

end Quantum.TensorProducts
