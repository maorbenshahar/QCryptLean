import QCryptLean.InfoTheory.Postselection.MapSymmetry
import QCryptLean.Quantum.Symmetry.SymmetricSubspace

/-!
# QKD postselection — symmetrization preserves per-site group invariance

Faithful transcription of a structural fact used implicitly throughout
Nahar–Tupkary–Zhao–Lütkenhaus–Tan 2024 (arXiv:2403.11851) whenever a de Finetti-style
symmetrization argument is combined with a symmetry hypothesis on the source (Def. 6
IID-group-invariance, lines 600–605; used by Corollary 3.2): symmetrizing a per-site
`G`-invariant state over the round permutation group `Sₙ` produces a state that is
*both* permutation-invariant *and* still per-site `G`-invariant.

The site-permutation representation and the per-site conjugation by the tensor family
`tensorFamily (W ∘ h)` interact by relabelling the site assignment `h : Fin n → G` along the
permutation (`Quantum.TensorProducts.tensorFamily_mul_permutationRepresentation`), so averaging
over `Sₙ` cannot destroy an invariance that already holds *for every* `h`.

## Main statements
- `symmetrize_iidGroupInvariant` : if a state `ρ` is fixed by conjugation with
  `tensorFamily (W ∘ h)` for *every* `h : Fin n → G` (the state-level form of Nahar et al. Def. 6),
  then so is `symmetrize ρ`. Combined with
  `symmetrize_isPermutationInvariant`, this supplies both a permutation-invariance and a
  group-invariance hypothesis for a reduced fixed-marginal de Finetti bound from the
  group-invariance hypothesis alone.
-/

open Quantum.Operators Quantum.TensorProducts Math.RepresentationTheory Quantum.Symmetry
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

/-! ## Symmetrization preserves per-site group invariance -/

/-- **Symmetrization preserves per-site `G`-invariance.**

If `ρ` is fixed by `tensorFamily (W ∘ h)`-conjugation for *every* site-assignment
`h : Fin n → G` (the state-level Nahar et al. Definition 6), then the same holds for
`symmetrize ρ`.

**Proof idea.** `symmetrize ρ = (1/n!) ∑_σ U_σ ρ U_σᴴ`. Conjugating each summand by
`tensorFamily (W ∘ h)` and sliding it past `U_σ` via `tensorFamily_mul_permutationRepresentation`
turns it into a conjugation of `ρ` by `tensorFamily (W ∘ (h ∘ σ))`, sandwiched between `U_σ`
and `U_σᴴ`; the inner conjugation is `ρ` itself by `hGinv` applied to the relabelled assignment
`h ∘ σ`, leaving `U_σ ρ U_σᴴ` unchanged. Summing over `σ` recovers `symmetrize ρ` unchanged. -/
theorem symmetrize_iidGroupInvariant {dA n : ℕ} [NeZero dA] [NeZero n]
    {G : Type*} (W : G → UnitaryOp dA) (ρ : DensityOp (dA ^ n))
    (hGinv : ∀ h : Fin n → G,
      tensorFamily (fun k => (W (h k)).toOp) * ρ.toOp *
        (tensorFamily (fun k => (W (h k)).toOp))ᴴ = ρ.toOp) :
    ∀ h : Fin n → G,
      tensorFamily (fun k => (W (h k)).toOp) * (symmetrize ρ).toOp *
        (tensorFamily (fun k => (W (h k)).toOp))ᴴ = (symmetrize ρ).toOp := by
  intro h
  have hstep : ∀ σ : Equiv.Perm (Fin n),
      tensorFamily (fun k => (W (h k)).toOp) *
        (permutationRepresentation dA n σ * ρ.toOp * (permutationRepresentation dA n σ)ᴴ) *
        (tensorFamily (fun k => (W (h k)).toOp))ᴴ =
      permutationRepresentation dA n σ * ρ.toOp * (permutationRepresentation dA n σ)ᴴ := by
    intro σ
    have hcomm := tensorFamily_mul_permutationRepresentation (fun k => (W (h k)).toOp) σ
    calc tensorFamily (fun k => (W (h k)).toOp) *
          (permutationRepresentation dA n σ * ρ.toOp * (permutationRepresentation dA n σ)ᴴ) *
          (tensorFamily (fun k => (W (h k)).toOp))ᴴ
        = (tensorFamily (fun k => (W (h k)).toOp) * permutationRepresentation dA n σ) *
            ρ.toOp *
            (tensorFamily (fun k => (W (h k)).toOp) * permutationRepresentation dA n σ)ᴴ := by
          rw [Matrix.conjTranspose_mul]
          simp [Matrix.mul_assoc]
      _ = permutationRepresentation dA n σ *
            (tensorFamily (fun k => (W (h (σ k))).toOp) * ρ.toOp *
              (tensorFamily (fun k => (W (h (σ k))).toOp))ᴴ) *
            (permutationRepresentation dA n σ)ᴴ := by
          rw [hcomm, Matrix.conjTranspose_mul]
          simp [Matrix.mul_assoc]
      _ = permutationRepresentation dA n σ * ρ.toOp * (permutationRepresentation dA n σ)ᴴ := by
          rw [hGinv fun k => h (σ k)]
  rw [symmetrize_toOp, mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun σ _ => hstep σ

end InfoTheory.Postselection

end
