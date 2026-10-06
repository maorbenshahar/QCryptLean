import QCryptLean.Quantum.TensorProducts.RoundRegrouping
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.Quantum.Symmetry.SignalPermutation
import QCryptLean.InfoTheory.QuantumLHL.CollisionAnnounceCharge
import QCryptLean.Quantum.Channels.CPTP.DiamondNormAncilla
import QCryptLean.Quantum.Channels.CPTP.Reindex

/-!
# BB84: the two quantum layers are products across the laboratory cut

The V2 sift `bb84SiftedRotation` and the round permutation `permuteSignalLinear` are, transported
along the round regrouping `roundGroupEquiv 2 2 n`, products of one Alice-side and one Bob-side
operator: each party acts on its own `n` subsystems, and no data crosses the cut.

Nothing here is a security statement. A protocol that announces its raw key is perfectly local and
perfectly insecure.

## Main results

- `QKD.BB84.Model.bb84SiftedSinglePairOp_eq_tensor`,
  `QKD.BB84.Model.bb84SiftedRotation_reindex_roundGroupEquiv`,
  `QKD.BB84.Model.bb84SiftedRotation_conj_reindex_roundGroupEquiv`: the sift layer is a product
  across the cut, at the operator level and at the map level.
- `QKD.BB84.Model.permuteSignalLinear_kraus_reindex_roundGroupEquiv`,
  `QKD.BB84.Model.permuteSignalLinear_reindex_roundGroupEquiv`: the round-permutation layer is a
  product across the cut. This proves that *for each fixed `π`* the layer is conjugation by the
  product unitary `U^A_π ⊗ U^B_π`; it does not say `π` is public, which is a statement about the
  surrounding channel's announcement register.

## What this module is

Everything below is **operator-level index algebra**. This module imports exactly two facts from
`RoundRegrouping.lean` (`Quantum.TensorProducts.tensorFamily_pair_reindex_roundGroupEquiv`,
`Quantum.TensorProducts.reindex_roundGroupEquiv_permRep`) and shows that the two BB84 operators
factor across the laboratory cut.

## References

Bennett–Brassard 1984; Shor–Preskill 2000 (the EB↔P&M reduction); Renner 2005
(arXiv:quant-ph/0512258v2, `main.tex:1800-1801`, the permutation step);
Christandl–König–Renner 2009 (arXiv:0809.3019, `main.tex:414-426`, the normal form
`E = C ∘ M`; `:452-455`, the announced permutation).
-/

open Equiv

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Matrix
open Math.RepresentationTheory QKD.BB84.Engine
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Model

/-! ## 1. The definitional facts the product forms ride on

Each of these is `rfl`; they are named because a reader should not have to unfold a definition to
learn that the BB84 sift is literally a Kronecker product of single-qubit gates. -/

/-- **The per-round sift splits across the cut of a single round.** On an X-test round it is
`H ⊗ H`; elsewhere it is `1 ⊗ 1`. Not `rfl`: the identity branch is spelled `(1 : Op 4)`, and
`Op.tensor_one` is what identifies it with `Op.tensor 1 1`. -/
theorem bb84SiftedSinglePairOp_eq_tensor (peSel xSel : Bool) :
    bb84SiftedSinglePairOp peSel xSel
      = Op.tensor (if peSel && xSel then Quantum.Gates.hadamard else (1 : Op 2))
          (if peSel && xSel then Quantum.Gates.hadamard else (1 : Op 2)) := by
  unfold bb84SiftedSinglePairOp
  by_cases h : (peSel && xSel) = true
  · rw [if_pos h, if_pos h]
    rfl
  · simp only [if_neg h, Op.tensor_one]

/-! ## 2. (a) The sift layer is a product across the laboratory cut -/

/-- **(a), operator level.** Transported along the round regrouping, the V2 sift
`bb84SiftedRotation` is the tensor product of two single-party `n`-qubit operators: Hadamard exactly
on the X-test rounds and the identity elsewhere, **on each side separately**.

Arbitrary `peSel`, `xSel` — a product factorization of an operator cannot depend on how many rounds
are key rounds, so there is no `bb84KeyCount` hypothesis and none would help.

This is the theorem the `bb84SiftedSinglePairOp` and `bb84SiftedRotation` docstrings assert.

**Scope limit.** Both factors are the *same* term, so this statement is blind to the A|B
orientation: the swapped right-hand side is literally this one. The orientation is fixed instead by
`Quantum.TensorProducts.tensorFamily_pair_reindex_roundGroupEquiv`, which this proof consumes,
and which is
false when swapped. -/
theorem bb84SiftedRotation_reindex_roundGroupEquiv (n : ℕ) (peSel xSel : Fin n → Bool) :
    Matrix.reindex (roundGroupEquiv 2 2 n) (roundGroupEquiv 2 2 n)
        (bb84SiftedRotation n peSel xSel)
      = Op.tensor
          (tensorFamily
            (fun a => if peSel a && xSel a then Quantum.Gates.hadamard else (1 : Op 2)))
          (tensorFamily
            (fun a => if peSel a && xSel a then Quantum.Gates.hadamard else (1 : Op 2))) := by
  rw [bb84SiftedRotation]
  simp only [bb84SiftedSinglePairOp_eq_tensor]
  exact Quantum.TensorProducts.tensorFamily_pair_reindex_roundGroupEquiv n _ _

/-- **(a), map level — the consumer-facing form.** Transported along the round regrouping,
conjugation by the V2 sift is conjugation by a **product** unitary: Alice applies `⊗ₐ Hᵃ` to her own
`n` qubits, Bob applies the same to his, and nothing crosses the cut. -/
theorem bb84SiftedRotation_conj_reindex_roundGroupEquiv (n : ℕ) (peSel xSel : Fin n → Bool)
    (ρ : Op (4 ^ n)) :
    Matrix.reindex (roundGroupEquiv 2 2 n) (roundGroupEquiv 2 2 n)
        (bb84SiftedRotation n peSel xSel * ρ * (bb84SiftedRotation n peSel xSel)ᴴ)
      = Op.tensor
            (tensorFamily
              (fun a => if peSel a && xSel a then Quantum.Gates.hadamard else (1 : Op 2)))
            (tensorFamily
              (fun a => if peSel a && xSel a then Quantum.Gates.hadamard else (1 : Op 2))) *
          Matrix.reindex (roundGroupEquiv 2 2 n) (roundGroupEquiv 2 2 n) ρ *
          (Op.tensor
            (tensorFamily
              (fun a => if peSel a && xSel a then Quantum.Gates.hadamard else (1 : Op 2)))
            (tensorFamily
              (fun a => if peSel a && xSel a then Quantum.Gates.hadamard else (1 : Op 2))))ᴴ := by
  rw [← Matrix.reindexAlgEquiv_apply ℂ ℂ, map_mul, map_mul,
    Matrix.reindexAlgEquiv_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindexAlgEquiv_apply,
    bb84SiftedRotation_reindex_roundGroupEquiv, ← Matrix.conjTranspose_reindex,
    bb84SiftedRotation_reindex_roundGroupEquiv]

/-! ## 3. (b) The permutation layer is a product across the laboratory cut -/

/-- **(b), operator level.** The round-permutation unitary on the joint `4 ^ n` register is,
transported along the round regrouping, the tensor product of Alice's and Bob's own copies of the
**same** permutation unitary. This specializes
`Quantum.TensorProducts.reindex_roundGroupEquiv_permRep` to BB84's cut;
`(2 * 2) ^ n` and `4 ^ n` unify at default transparency, so no cast is needed. -/
theorem permuteSignalLinear_kraus_reindex_roundGroupEquiv (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Matrix.reindex (roundGroupEquiv 2 2 n) (roundGroupEquiv 2 2 n)
        (permutationRepresentation 4 n π)
      = Op.tensor (permutationRepresentation 2 n π) (permutationRepresentation 2 n π) :=
  Quantum.TensorProducts.reindex_roundGroupEquiv_permRep (dA := 2) (dB := 2) π

/-- **(b), map level — the consumer-facing form.** Transported along the round regrouping,
`permuteSignalLinear n π` is conjugation by the product unitary `U^A_π ⊗ U^B_π`: each party permutes
its **own** `n` subsystems by the same `π`, and no data crosses the cut.

**Scope limit.** This proves that *for each fixed `π`* the layer is a product across the cut.
It does **not** say `π` is *public*, so both parties can apply it — that is a statement about the
surrounding channel's announcement register and is proved nowhere. Each factor's unitarity is
free. -/
theorem permuteSignalLinear_reindex_roundGroupEquiv (n : ℕ) [NeZero n] [NeZero (4 ^ n)]
    (π : Equiv.Perm (Fin n)) (ρ : Op (4 ^ n)) :
    Matrix.reindex (roundGroupEquiv 2 2 n) (roundGroupEquiv 2 2 n)
        (permuteSignalLinear n π ρ)
      = Op.tensor (permutationRepresentation 2 n π) (permutationRepresentation 2 n π) *
          Matrix.reindex (roundGroupEquiv 2 2 n) (roundGroupEquiv 2 2 n) ρ *
          (Op.tensor (permutationRepresentation 2 n π) (permutationRepresentation 2 n π))ᴴ := by
  simp only [permuteSignalLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Matrix.reindexAlgEquiv_apply ℂ ℂ, map_mul, map_mul,
    Matrix.reindexAlgEquiv_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindexAlgEquiv_apply,
    permuteSignalLinear_kraus_reindex_roundGroupEquiv, ← Matrix.conjTranspose_reindex,
    permuteSignalLinear_kraus_reindex_roundGroupEquiv]

/-- A BB84 outcome is recovered from its own bit pair:
    `finProdFinEquiv (aliceBit k, bobBit k) = k`. -/
theorem finProdFinEquiv_aliceBit_bobBit (k : Fin signalDim) :
    finProdFinEquiv (aliceBit k, bobBit k) = k := by
  fin_cases k <;> rfl

end QKD.BB84.Model

end
