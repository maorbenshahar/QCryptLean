import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Reference-Side Unitary Transport — rotating only the second tensor factor

`Quantum.TensorProducts.rightTensorUnitaryConj W M = (1 ⊗ W) M (1 ⊗ W)†` rotates the
*reference* factor of a bipartite operator and leaves the system factor alone.  This file
supplies the primitives that go with it:

* the unitary `1 ⊗ W` itself, as `rightTensorUnitary` — the right-hand counterpart of the
  existing `Quantum.TensorProducts.tensorUnitary` (`A ⊗ 1`);
* the fact that a reference-side sandwich does not move the system marginal
  `partialTraceB`, which is why a reference-side rotation of a purification is again a
  purification of the *same* state;
* the packaged density-operator statements, including preservation of purity.

The companion `partialTraceA` computation (a reference-side rotation *conjugates* the
reference marginal) is `Quantum.TensorProducts.partialTraceA_rightTensorUnitaryConj` in
`Quantum/TensorProducts/Trace.lean`.

## Main definitions
- `rightTensorUnitary`: the unitary `1 ⊗ W` on `A ⊗ R`.

## Main statements
- `partialTraceB_one_tensor_sandwich_of_mul_eq_one`: `Tr_R((1 ⊗ A) M (1 ⊗ B)) = Tr_R M`
  whenever `B A = 1`.
- `partialTraceB_rightTensorUnitaryConj`: the system marginal is invariant under
  reference-side unitary transport.
- `DensityOp.partialTraceB_rightTensorUnitaryEvolve`,
  `DensityOp.isPure_rightTensorUnitaryEvolve`: the density-operator forms.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

/-- The reference-factor unitary `1 ⊗ W` on `A ⊗ R`.

This is the right-hand counterpart of `tensorUnitary`, which builds `W ⊗ 1`. -/
def rightTensorUnitary {n m : ℕ} (W : UnitaryOp m) : UnitaryOp (n * m) :=
  ⟨Op.tensor (1 : Op n) W.toOp, by
    rw [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul, Matrix.one_mul,
      W.unitary_left, Op.tensor_one], by
    rw [Op.tensor_conjTranspose, conjTranspose_one, Op.tensor_mul, Matrix.one_mul,
      W.unitary_right, Op.tensor_one]⟩

@[simp]
lemma rightTensorUnitary_toOp {n m : ℕ} (W : UnitaryOp m) :
    (rightTensorUnitary (n := n) W).toOp = Op.tensor (1 : Op n) W.toOp :=
  rfl

lemma rightTensorUnitaryConj_eq_unitary_conj {n m : ℕ} (W : UnitaryOp m) (M : Op (n * m)) :
    rightTensorUnitaryConj W M =
      (rightTensorUnitary (n := n) W).toOp * M * (rightTensorUnitary (n := n) W).toOp† :=
  rfl

/-- **A reference-side sandwich leaves the system marginal unchanged**, as soon as the two
operators compose to the identity in the order `B A = 1`.

Entrywise, `Tr_R((1 ⊗ A) M (1 ⊗ B))_{k,l} = Σ_{a,c} M_{(k,a),(l,c)} (B A)_{c,a}`: the two
reference-side factors meet under the trace, so only their product matters. -/
lemma partialTraceB_one_tensor_sandwich_of_mul_eq_one {n m : ℕ}
    (A B : Op m) (hBA : B * A = 1) (M : Op (n * m)) :
    partialTraceB (Op.tensor (1 : Op n) A * M * Op.tensor (1 : Op n) B) =
      partialTraceB M := by
  ext k l
  simp only [partialTraceB, Matrix.of_apply]
  simp_rw [one_tensor_mul_mul_one_tensor_apply]
  have hinner : ∀ a c : Fin m,
      (∑ i : Fin m,
          A i a * M (finProdFinEquiv (k, a)) (finProdFinEquiv (l, c)) * B c i) =
        M (finProdFinEquiv (k, a)) (finProdFinEquiv (l, c)) * (B * A) c a := by
    intro a c
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc
    (∑ i : Fin m, ∑ a : Fin m, ∑ c : Fin m,
        A i a * M (finProdFinEquiv (k, a)) (finProdFinEquiv (l, c)) * B c i) =
        ∑ a : Fin m, ∑ c : Fin m, ∑ i : Fin m,
          A i a * M (finProdFinEquiv (k, a)) (finProdFinEquiv (l, c)) * B c i := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a : Fin m, ∑ c : Fin m,
          M (finProdFinEquiv (k, a)) (finProdFinEquiv (l, c)) * (B * A) c a := by
      simp_rw [hinner]
    _ = ∑ a : Fin m, M (finProdFinEquiv (k, a)) (finProdFinEquiv (l, a)) := by
      rw [hBA]
      exact Finset.sum_congr rfl fun a _ => by
        simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ a
          (fun c => M (finProdFinEquiv (k, a)) (finProdFinEquiv (l, c)))]
        simp

/-- **Reference-side unitary transport preserves the system marginal.**

A right-unitary transport of a purification of `ρ` is therefore again a purification of `ρ`;
only the reference marginal moves, by
`partialTraceA_rightTensorUnitaryConj`. -/
lemma partialTraceB_rightTensorUnitaryConj {n m : ℕ}
    (W : UnitaryOp m) (M : Op (n * m)) :
    partialTraceB (rightTensorUnitaryConj W M) = partialTraceB M := by
  unfold rightTensorUnitaryConj
  rw [Op.tensor_conjTranspose, conjTranspose_one]
  exact partialTraceB_one_tensor_sandwich_of_mul_eq_one W.toOp W.toOp†
    W.unitary_left M

/-- Density-operator form: rotating the reference factor of a bipartite state does not
change its system marginal. -/
lemma DensityOp.partialTraceB_rightTensorUnitaryEvolve {n m : ℕ}
    (W : UnitaryOp m) (ρ : DensityOp (n * m)) :
    (UnitaryOp.evolve (rightTensorUnitary (n := n) W) ρ).partialTraceB =
      ρ.partialTraceB := by
  apply Quantum.Operators.DensityOp.ext
  change partialTraceB (rightTensorUnitaryConj W ρ.toOp) = partialTraceB ρ.toOp
  exact partialTraceB_rightTensorUnitaryConj W ρ.toOp

/-- Unitary conjugation preserves purity, in the reference-side form used here. -/
lemma DensityOp.isPure_rightTensorUnitaryEvolve {n m : ℕ}
    (W : UnitaryOp m) {ρ : DensityOp (n * m)} (hρ : ρ.IsPure) :
    (UnitaryOp.evolve (rightTensorUnitary (n := n) W) ρ).IsPure := by
  set A : Op (n * m) := (rightTensorUnitary (n := n) W).toOp with hA
  change (A * ρ.toOp * A†) * (A * ρ.toOp * A†) = A * ρ.toOp * A†
  calc
    (A * ρ.toOp * A†) * (A * ρ.toOp * A†) =
        A * ρ.toOp * (A† * A) * ρ.toOp * A† := by
      simp only [Matrix.mul_assoc]
    _ = A * (ρ.toOp * ρ.toOp) * A† := by
      rw [hA, (rightTensorUnitary (n := n) W).unitary_left]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = A * ρ.toOp * A† := by rw [hρ]

/-- The transported state's underlying operator is the right-unitary conjugation. -/
@[simp]
lemma DensityOp.toOp_rightTensorUnitaryEvolve {n m : ℕ}
    (W : UnitaryOp m) (ρ : DensityOp (n * m)) :
    (UnitaryOp.evolve (rightTensorUnitary (n := n) W) ρ).toOp =
      rightTensorUnitaryConj W ρ.toOp :=
  rfl

end Quantum.TensorProducts

end -- noncomputable section
