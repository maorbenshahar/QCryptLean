import QCryptLean.Quantum.Channels.CPTP.Basic
import QCryptLean.Quantum.TensorProducts.TensorFamily

/-!
# n-Fold Tensor Power of a Kraus Representation

Given a Kraus representation `K : ℋ_d → ℋ_m` with operators `{Kᵢ}` satisfying the
completeness relation `∑ᵢ Kᵢ† Kᵢ = 1`, this module constructs its `n`-fold tensor
power `K^{⊗n} : ℋ_{d^n} → ℋ_{m^n}`, again as an explicit `KrausRepresentation` with
its completeness relation proved.

The tensor power has `(numOps)^n` Kraus operators, indexed (through
`finFunctionFinEquiv : (Fin n → Fin numOps) ≃ Fin (numOps^n)`) by `n`-tuples
`g : Fin n → Fin numOps`. The operator at index `g` is the rectangular tensor family
`Quantum.TensorProducts.tensorFamily fun k => K.operators (g k)`, in the digit coordinates of
`finFunctionFinEquiv`.

## Main definitions
- `KrausRepresentation.tensorPow K n : KrausRepresentation (d ^ n) (m ^ n)` — the
  `n`-fold tensor power, with completeness proved.

## Main statements
- `KrausRepresentation.tensorPow_operators_apply` — the Kraus operators of the power are tensor
  families of Kraus operators.
- `KrausRepresentation.tensorPow_applyOp_tensorFamily` — the power acts factorwise on tensor
  families: `𝒩^{⊗n}(⊗ₖ Aₖ) = ⊗ₖ 𝒩(Aₖ)`; its entrywise forms follow.

The completeness relation of the power is the tensor family of the completeness relations of the
factors: `∑_g (⊗ₖ K_{g k})ᴴ (⊗ₖ K_{g k}) = ⊗ₖ ∑ᵢ Kᵢᴴ Kᵢ = 1`, by multilinearity of the tensor
family (`tensorFamily_sum`).
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The `n`-fold tensor power `K^{⊗n} : ℋ_{d^n} → ℋ_{m^n}` of a Kraus
representation `K : ℋ_d → ℋ_m`, as an explicit `KrausRepresentation` with the
completeness relation `∑ Kᵢ† Kᵢ = 1` proved.

The power has `K.numOps ^ n` Kraus operators; through
`finFunctionFinEquiv : (Fin n → Fin K.numOps) ≃ Fin (K.numOps ^ n)` the operator
at index `g` is the tensor family `tensorFamily fun k => K.operators (g k)`. -/
def KrausRepresentation.tensorPow {d m : ℕ}
    (K : KrausRepresentation d m) (n : ℕ) :
    KrausRepresentation (d ^ n) (m ^ n) where
  numOps := K.numOps ^ n
  operators := fun i => tensorFamily fun k => K.operators (finFunctionFinEquiv.symm i k)
  completeness := by
    refine (Fintype.sum_equiv finFunctionFinEquiv.symm _
      (fun g => tensorFamily fun k => (K.operators (g k))ᴴ * K.operators (g k))
      fun i => by simp only [conjTranspose_tensorFamily, tensorFamily_mul]).trans ?_
    rw [← tensorFamily_sum fun (_ : Fin n) i => (K.operators i)ᴴ * K.operators i, K.completeness,
      tensorFamily_one]

@[simp] lemma KrausRepresentation.tensorPow_numOps {d m : ℕ}
    (K : KrausRepresentation d m) (n : ℕ) :
    (K.tensorPow n).numOps = K.numOps ^ n := rfl

/-- The Kraus operators of the tensor power, indexed by `Fin n → Fin K.numOps`
through `finFunctionFinEquiv`, are the tensor families of Kraus operators. -/
lemma KrausRepresentation.tensorPow_operators_apply {d m : ℕ}
    (K : KrausRepresentation d m) (n : ℕ) (g : Fin n → Fin K.numOps) :
    (K.tensorPow n).operators (finFunctionFinEquiv g) =
      tensorFamily fun k => K.operators (g k) := by
  simp only [KrausRepresentation.tensorPow, Equiv.symm_apply_apply]

/-- **Entrywise single-round formula for the single-channel `applyOp`.**
The `(a, b)` entry of `K.applyOp A` expands as a double sum over the output
intermediate indices weighted by the Kraus operators (`Σ_i Σ_{a',b'} Kᵢ a a' ·
A a' b' · conj (Kᵢ b b')`). -/
lemma KrausRepresentation.applyOp_entry {d m : ℕ}
    (K : KrausRepresentation d m) (A : Op d)
    (a b : Fin m) :
    (K.applyOp A) a b =
      ∑ i : Fin K.numOps, ∑ a' : Fin d, ∑ b' : Fin d,
        K.operators i a a' * A a' b' *
          (starRingEnd ℂ) (K.operators i b b') := by
  classical
  simp only [KrausRepresentation.applyOp, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b' _
  rw [Finset.sum_mul]

/-- **Channel tensor-power multiplicativity.** The tensor power of a Kraus representation acts
factorwise on a tensor family: `𝒩^{⊗n}(⊗ₖ Aₖ) = ⊗ₖ 𝒩(Aₖ)`, each round processed by an
independent copy of `𝒩`. -/
theorem KrausRepresentation.tensorPow_applyOp_tensorFamily {d m n : ℕ}
    (K : KrausRepresentation d m) (A : Fin n → Op d) :
    (K.tensorPow n).applyOp (tensorFamily A) = tensorFamily fun k => K.applyOp (A k) := by
  simp only [KrausRepresentation.applyOp]
  rw [tensorFamily_sum]
  refine Fintype.sum_equiv finFunctionFinEquiv.symm _ _ fun i => ?_
  simp only [KrausRepresentation.tensorPow, conjTranspose_tensorFamily, tensorFamily_mul]

/-- **Entrywise multi-round factorization of the tensor-power `applyOp`.**

If the input operator `M : Op (d ^ n)` factors entrywise as the product of a
family of single-round operators `A k` — i.e. `M (finFunctionFinEquiv a')
(finFunctionFinEquiv b') = ∏ₖ (A k) (a' k) (b' k)` for all multi-indices
`a' b' : Fin n → Fin d`, which says `M = tensorFamily A` — then so does the image
`(K.tensorPow n).applyOp M`: its entry at the multi-indices `a b : Fin n → Fin m` is the
product over rounds of the single-round images `(K.applyOp (A k)) (a k) (b k)`. It is the
analogue, at the level of `applyOp` entries, of
`Quantum.TensorProducts.quadraticForm_tensorPowVec_of_entrywise_prod`. -/
lemma KrausRepresentation.tensorPow_applyOp_entry_of_entrywise_prod
    {d m : ℕ} (K : KrausRepresentation d m) (n : ℕ)
    (M : Op (d ^ n))
    (A : Fin n → Op d)
    (hM : ∀ a' b' : Fin n → Fin d,
      M (finFunctionFinEquiv a') (finFunctionFinEquiv b') =
        ∏ k : Fin n, (A k) (a' k) (b' k))
    (a b : Fin n → Fin m) :
    ((K.tensorPow n).applyOp M) (finFunctionFinEquiv a) (finFunctionFinEquiv b) =
      ∏ k : Fin n, (K.applyOp (A k)) (a k) (b k) := by
  rw [show M = tensorFamily A from ext_finFunctionFinEquiv fun f g => by
      rw [hM, tensorFamily_apply_finFunctionFinEquiv],
    KrausRepresentation.tensorPow_applyOp_tensorFamily, tensorFamily_apply_finFunctionFinEquiv]

/-- **Entrywise block factorization of the tensor-power `applyOp` at an `m + r`
split (channel tensor-power multiplicativity, block form).**

Let `A : Fin m → Matrix …` and `B : Fin r → Matrix …` be single-round operator
families. If `M : Op (d ^ (m + r))` factors entrywise through the appended family
`Fin.append A B` — i.e. `M (finFunctionFinEquiv c) (finFunctionFinEquiv c') =
∏ₖ (Fin.append A B k) (c k) (c' k)`, the entry form of `tensorFamily (Fin.append A B)` — then
the image `(K.tensorPow (m + r)).applyOp M` factors entrywise as the product of the two block
images:

  `… = (∏_{k<m} (K.applyOp (A k)) (a (castAdd k)) (b (castAdd k)))
       · (∏_{k<r} (K.applyOp (B k)) (a (natAdd k)) (b (natAdd k)))`.

This is the operator-entry form of `𝒩^{⊗(m+r)}(X ⊗ Y) = 𝒩^{⊗m}(X) ⊗ 𝒩^{⊗r}(Y)`:
the first `m` rounds are processed by `K^{⊗m}`, the last `r` by `K^{⊗r}`, each round
independently. -/
lemma KrausRepresentation.tensorPow_applyOp_entry_block_split
    {d m_out : ℕ} (K : KrausRepresentation d m_out) (m r : ℕ)
    (M : Op (d ^ (m + r)))
    (A : Fin m → Op d)
    (B : Fin r → Op d)
    (hM : ∀ c c' : Fin (m + r) → Fin d,
      M (finFunctionFinEquiv c) (finFunctionFinEquiv c') =
        ∏ k : Fin (m + r), (Fin.append A B k) (c k) (c' k))
    (a b : Fin (m + r) → Fin m_out) :
    ((K.tensorPow (m + r)).applyOp M) (finFunctionFinEquiv a) (finFunctionFinEquiv b) =
      (∏ k : Fin m, (K.applyOp (A k)) (a (Fin.castAdd r k)) (b (Fin.castAdd r k))) *
        (∏ k : Fin r, (K.applyOp (B k)) (a (Fin.natAdd m k)) (b (Fin.natAdd m k))) := by
  rw [K.tensorPow_applyOp_entry_of_entrywise_prod (m + r) M (Fin.append A B) hM a b,
    Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **Entrywise tensor-power form of the tensor-power `applyOp` (channel
tensor-power multiplicativity, i.i.d. form).**

If `M : Op (d ^ n)` is the `n`-fold operator tensor power of a single-round
operator `D : Op d` — i.e. `M (finFunctionFinEquiv c) (finFunctionFinEquiv c') =
∏ₖ D (c k) (c' k)`, the entry form of `D^{⊗n}` — then its image under the
tensor-power channel is the `n`-fold operator tensor power of the single-round
image `K.applyOp D`:

  `((K.tensorPow n).applyOp M) (finFunctionFinEquiv a) (finFunctionFinEquiv b)
     = ∏ₖ (K.applyOp D) (a k) (b k)`.

This is the operator-entry form of `𝒩^{⊗n}(D^{⊗n}) = (𝒩(D))^{⊗n}`. -/
lemma KrausRepresentation.tensorPow_applyOp_entry_of_tensorPow_input
    {d m_out : ℕ} (K : KrausRepresentation d m_out) (n : ℕ)
    (M : Op (d ^ n))
    (D : Op d)
    (hM : ∀ c c' : Fin n → Fin d,
      M (finFunctionFinEquiv c) (finFunctionFinEquiv c') =
        ∏ k : Fin n, D (c k) (c' k))
    (a b : Fin n → Fin m_out) :
    ((K.tensorPow n).applyOp M) (finFunctionFinEquiv a) (finFunctionFinEquiv b) =
      ∏ k : Fin n, (K.applyOp D) (a k) (b k) :=
  K.tensorPow_applyOp_entry_of_entrywise_prod n M (fun _ => D) hM a b

end Quantum.Channels

end
