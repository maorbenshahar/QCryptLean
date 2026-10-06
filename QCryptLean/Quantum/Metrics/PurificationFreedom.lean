import QCryptLean.Quantum.Metrics.SameAncillaPurification
import QCryptLean.Math.LinearAlgebra.UnitaryExtension
import QCryptLean.Quantum.TensorProducts.Trace
import QCryptLean.InfoTheory.DeFinetti.MaxEntangled
import QCryptLean.Quantum.Metrics.PolarUnitary

/-!
# Purification Unitary Freedom — canonical form

This file packages the **unitary freedom of purifications** (Watrous Lemma 2.41
/ Nielsen–Chuang §2.5) in the same-ancilla canonical form used by this repo:
given any purification `ψρ : Ket (d * d)` of a density operator `ρ : DensityOp d`
on the doubled space, there exists a unitary `W` on the second (ancilla) factor
such that

  `ψρ = (1 ⊗ W) · sameAncillaPurificationKet ρ`.

The proof is decomposed into small named helpers:

1. `Quantum.Metrics.KitaevWatrousPurification.Ket.exists_vec_repr` — every `ψ : Ket (d * d)` can be
written as
   `(M ⊗ 1) · |Ω⟩` for some matrix `M : Op d`.
2. `Quantum.Metrics.KitaevWatrousPurification.partialTraceB_vec_outer_eq_mul_conjTranspose` — for
such a representation,
   `partialTraceB (ψ * ψ.dag) = M * M†`.
3. `Quantum.Metrics.KitaevWatrousPurification.tensor_one_maxEntangledKet_ricochet` — the maximally
entangled-ket
   "ricochet" identity `(A ⊗ 1) |Ω⟩ = (1 ⊗ Aᵀ) |Ω⟩`.

These helpers, together with the abstract polar decomposition
`Quantum.Metrics.PolarUnitary.Op.exists_unitary_polar_left`, the unitary
transpose `Quantum.Operators.UnitaryOp.transpose`, and the tensor commutation
`Quantum.TensorProducts.Op.tensor_one_mul_one_tensor_comm`, compose to produce
the freedom witness in `purification_unitary_freedom_canonical`.

## Main statements
- `purification_unitary_freedom_canonical`: the same-ancilla canonical form of
  the unitary freedom of purifications
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open Quantum.Metrics.KitaevWatrousPurification
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace Quantum.Metrics

/-- **Purification unitary freedom (canonical form).**

For any density operator `ρ : DensityOp d` and any ket `ψρ : Ket (d * d)` whose
ket-outer product has partial trace equal to `ρ`, there exists a unitary
`W : UnitaryOp d` on the ancilla factor such that

  `ψρ = (1 ⊗ W) · sameAncillaPurificationKet ρ`.

This is the standard "unitary freedom of purifications" theorem (Watrous
Lemma 2.41 / Nielsen–Chuang §2.5), specialized to the same-ancilla canonical
purification used elsewhere in this development. The proof composes
`Quantum.Metrics.KitaevWatrousPurification.Ket.exists_vec_repr`,
`Quantum.Metrics.KitaevWatrousPurification.partialTraceB_vec_outer_eq_mul_conjTranspose`,
`Op.exists_unitary_polar_left`,
`Quantum.Metrics.KitaevWatrousPurification.tensor_one_maxEntangledKet_ricochet`,
and `UnitaryOp.transpose`. -/
theorem purification_unitary_freedom_canonical
    {d : ℕ} [NeZero d] (ρ : DensityOp d) (ψρ : Ket (d * d))
    (hpu : partialTraceB (ψρ * ψρ.dag) = ρ.toOp) :
    ∃ W : UnitaryOp d,
      ψρ = (Op.tensor (1 : Op d) W.toOp) *
        Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet ρ := by
  -- 1. Pull `M` out of the vec representation of `ψρ`.
  obtain ⟨M, hM⟩ := Quantum.Metrics.KitaevWatrousPurification.Ket.exists_vec_repr ψρ
  -- 2. The partial trace of the outer product equals `M * M†`, which equals `ρ`.
  have hMM : M * M.conjTranspose = ρ.toOp := by
    have hψ_outer :
        ψρ * ψρ.dag =
          Op.tensor M (1 : Op d) *
            InfoTheory.DeFinetti.maxEntangledOp d *
            Op.tensor M.conjTranspose (1 : Op d) := by
      rw [hM, dag_op_mul_ket, Op.tensor_conjTranspose, conjTranspose_one,
          InfoTheory.DeFinetti.maxEntangledOp_eq_ketbra, op_mul_ketbra, ketbra_mul_op]
    have hptrace :=
      Quantum.Metrics.KitaevWatrousPurification.partialTraceB_vec_outer_eq_mul_conjTranspose M
    rw [← hptrace, ← hψ_outer]
    exact hpu
  -- 3. Polar decomposition: `M = √(M M†) · W₀`. Substituting `M M† = ρ` then
  --    gives `M = √ρ · W₀`.
  obtain ⟨W₀, hW₀⟩ := Quantum.Metrics.PolarUnitary.Op.exists_unitary_polar_left M
  rw [hMM] at hW₀
  -- 4. The witness is `W := W₀.transpose`.
  refine ⟨UnitaryOp.transpose W₀, ?_⟩
  -- 5. Compose. Start from `ψρ = (M ⊗ 1) |Ω⟩`, substitute `M = √ρ · W₀`,
  --    apply the ricochet to fold `W₀` into the ancilla side, then commute
  --    the two tensor factors past each other to land at the canonical
  --    purification ket.
  have hMrew : Op.tensor M (1 : Op d) =
      Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
        Op.tensor W₀.toOp (1 : Op d) := by
    rw [hW₀, Op.tensor_mul, Matrix.mul_one]
  have hricochet := Quantum.Metrics.KitaevWatrousPurification.tensor_one_maxEntangledKet_ricochet
      W₀.toOp
  calc
    ψρ
        = (Op.tensor M (1 : Op d)) *
            InfoTheory.DeFinetti.maxEntangledKet d := hM
    _ = (Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
            Op.tensor W₀.toOp (1 : Op d)) *
              InfoTheory.DeFinetti.maxEntangledKet d := by rw [hMrew]
    _ = Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
            ((Op.tensor W₀.toOp (1 : Op d)) *
              InfoTheory.DeFinetti.maxEntangledKet d) := by
          rw [← op_op_mul_ket_assoc]
    _ = Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
            ((Op.tensor (1 : Op d) W₀.toOp.transpose) *
              InfoTheory.DeFinetti.maxEntangledKet d) := by
          rw [hricochet]
    _ = (Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
            Op.tensor (1 : Op d) W₀.toOp.transpose) *
              InfoTheory.DeFinetti.maxEntangledKet d := by
          rw [op_op_mul_ket_assoc]
    _ = (Op.tensor (1 : Op d) W₀.toOp.transpose *
            Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d)) *
              InfoTheory.DeFinetti.maxEntangledKet d := by
          rw [Op.tensor_one_mul_one_tensor_comm]
    _ = Op.tensor (1 : Op d) W₀.toOp.transpose *
            (Op.tensor (CFC.sqrt ρ.toOp) (1 : Op d) *
              InfoTheory.DeFinetti.maxEntangledKet d) := by
          rw [← op_op_mul_ket_assoc]
    _ = Op.tensor (1 : Op d) (UnitaryOp.transpose W₀).toOp *
            Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet ρ := by
          rfl

end Quantum.Metrics
