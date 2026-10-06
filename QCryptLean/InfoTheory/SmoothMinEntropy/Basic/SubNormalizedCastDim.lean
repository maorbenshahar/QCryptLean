import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.SubNormalized
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Transporting a sub-normalized state along a dimension equality

`SubDensityOp.castDim h` moves a sub-normalized density operator between two registers whose
dimensions are equal as natural numbers. Its underlying operator is `Op.castDim h` of the original
(`SubDensityOp.castDim_toOp`), the value-preserving relabelling of the indices along `finCongr h`
(`SubDensityOp.castDim_toOp_eq_reindex`). A normalized state is transported by the same relabelling
(`DensityOp.toSubDensityOp_castDim`).

This module carries the `SubDensityOp` counterparts of the `Op.castDim` and `DensityOp.castDim`
laws of the Quantum.TensorProducts.CastDim module. Which proof of a dimension equality is supplied
never
matters.

## Main definitions

- `InfoTheory.SmoothMinEntropy.SubDensityOp.castDim`: transport along `n = m`.

## Main statements

- `SubDensityOp.castDim_toOp`, `SubDensityOp.castDim_toOp_cast`,
  `SubDensityOp.castDim_toOp_eq_reindex`: the underlying operator, entrywise and as a reindex.
- `SubDensityOp.castDim_eq`, `SubDensityOp.castDim_trans`, `SubDensityOp.castDim_cancel`,
  `SubDensityOp.castDim_proof_irrel`: a cast to the same register is the identity, casts compose,
  and a cast is undone by a cast back.
- `SubDensityOp.castDim_trace`, `SubDensityOp.castDim_zero`, `SubDensityOp.castDim_posDef`,
  `SubDensityOp.castDim_rank`: a cast preserves the trace, the zero state, positive definiteness
  and rank.
- `DensityOp.toSubDensityOp_castDim`: casting commutes with viewing a normalized state as a
  sub-normalized one.
- `SubDensityOp.castDim_toOp_congr`, `SubDensityOp.opLe_castDim_toOp_smul`: casts transport
  equalities and Löwner bounds of underlying operators.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- A sub-density operator transported along an equality of dimensions. -/
noncomputable def SubDensityOp.castDim {n m : ℕ} (h : n = m) (ρ : SubDensityOp n) :
    SubDensityOp m := h ▸ ρ

namespace SubDensityOp

/-- The underlying operator of a cast is the cast of the underlying operator. -/
theorem castDim_toOp {n m : ℕ} (h : n = m) (ρ : SubDensityOp n) :
    (castDim h ρ).toOp = Op.castDim h ρ.toOp := by
  subst h; rfl

/-- Accessing an entry of a cast is accessing the original at the inverse index cast. -/
theorem castDim_toOp_cast {n m : ℕ} (h : n = m) (ρ : SubDensityOp n) (i j : Fin m) :
    (castDim h ρ).toOp i j = ρ.toOp (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst h; rfl

/-- A cast relabels each index to the index with the same numeral: its underlying operator is the
reindex along `finCongr h`. -/
theorem castDim_toOp_eq_reindex {n m : ℕ} (h : n = m) (ρ : SubDensityOp n) :
    (castDim h ρ).toOp = Matrix.reindex (finCongr h) (finCongr h) ρ.toOp := by
  subst h; rfl

/-- A cast of a register to itself is the identity. -/
theorem castDim_eq {n : ℕ} (h : n = n) (ρ : SubDensityOp n) : castDim h ρ = ρ := rfl

/-- Casts of sub-density operators compose. -/
theorem castDim_trans {n m k : ℕ} (h₁ : n = m) (h₂ : m = k) (ρ : SubDensityOp n) :
    castDim h₂ (castDim h₁ ρ) = castDim (h₁.trans h₂) ρ := by
  subst h₁; subst h₂; rfl

/-- **A cast is undone by a cast back**, whichever two proofs of the dimension equalities are
supplied. -/
theorem castDim_cancel {n m : ℕ} (h : n = m) (h' : m = n) (ρ : SubDensityOp n) :
    castDim h' (castDim h ρ) = ρ := by
  subst h; rfl

/-- A cast depends only on the dimension equality, not on its proof. -/
theorem castDim_proof_irrel {n m : ℕ} (h₁ h₂ : n = m) (ρ : SubDensityOp n) :
    castDim h₁ ρ = castDim h₂ ρ := rfl

/-- A cast preserves the trace. -/
theorem castDim_trace {n m : ℕ} (h : n = m) (ρ : SubDensityOp n) :
    (castDim h ρ).trace = ρ.trace := by
  subst h; rfl

/-- A cast carries the zero sub-density operator to zero. -/
@[simp] theorem castDim_zero {n m : ℕ} (h : n = m) : castDim h (0 : SubDensityOp n) = 0 := by
  subst h; rfl

/-- A cast preserves positive definiteness of the underlying operator. -/
theorem castDim_posDef {n m : ℕ} (h : n = m) {ρ : SubDensityOp n} (hρ : ρ.toOp.PosDef) :
    (castDim h ρ).toOp.PosDef := by
  subst h; exact hρ

/-- A cast preserves the rank of the underlying operator. -/
theorem castDim_rank {n m : ℕ} (h : n = m) (ρ : SubDensityOp n) :
    (castDim h ρ).toOp.rank = ρ.toOp.rank := by
  subst h; rfl

/-- A cast transports an equality of underlying operators. -/
theorem castDim_toOp_congr {n m : ℕ} (h : n = m) {A B : SubDensityOp n}
    (hAB : A.toOp = B.toOp) : (castDim h A).toOp = (castDim h B).toOp := by
  subst h; exact hAB

/-- A cast transports a Löwner bound `A ⪯ s • B` of underlying operators. -/
theorem opLe_castDim_toOp_smul {n m : ℕ} (h : n = m) (A : SubDensityOp n) (s : ℂ)
    (B : SubDensityOp n) (h_le : opLe A.toOp (s • B.toOp)) :
    opLe (castDim h A).toOp (s • (castDim h B).toOp) := by
  subst h; exact h_le

end SubDensityOp

/-- Casting commutes with viewing a normalized state as a sub-normalized one. -/
theorem DensityOp.toSubDensityOp_castDim {n m : ℕ} (h : n = m) (ρ : DensityOp n) :
    DensityOp.toSubDensityOp (DensityOp.castDim h ρ) =
      SubDensityOp.castDim h (DensityOp.toSubDensityOp ρ) := by
  subst h; rfl

end InfoTheory.SmoothMinEntropy
