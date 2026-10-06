import QCryptLean.QKD.BB84.Engine.Budgets.BellPolyDimTight
import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination
import QCryptLean.InfoTheory.DeFinetti.Purification
import Mathlib.Data.Sym.Card

/-!
# The Bell joint de Finetti mixture state `bb84BellPairedDeFinettiState`

This file constructs the **rank-`C(n+3,3)` Bell joint de Finetti mixture** that the inner B16 AEP
floor for `τ_Bell` needs — the keystone object of the `(n+1)^3` exponent residual.  The `dV = 1`
shortcut purifier is a *pure* state; the AEP floor needs the *mixture*
with one pure term per Bell type, of rank exactly `C(n+3,3) = bb84PolyDimTight n`.

## The construction

`bb84BellDeFinettiDensity n = τ_Bell` is diagonal in the joint Bell basis (`bellRotation n` rotating
the computational basis) with `C(n+3,3)` eigenvalues `τ_T = 3!·∏ᵢ nᵢ!/(n+3)!`, one per Bell **type**
`T = (n₀,n₁,n₂,n₃)`, `∑ᵢ nᵢ = n`.  Grouping the joint Bell basis indices by their type gives a
resolution of identity into `C(n+3,3)` orthogonal projectors `Q_T` (`bellTypeProjector`), and the
Bell joint mixture is the "type-coherent" purification mixture `bb84BellPairedDeFinettiState n = ∑_T
(B_T ⊗ 𝟙)·|Ω⟩⟨Ω|·(B_T ⊗ 𝟙)†`, `B_T = √τ_Bell · Q_T` (`bellPairedKraus`), `|Ω⟩⟨Ω| = maxEntangledOp`.

* Its `A`-marginal (`partialTraceB`) is `∑_T B_T B_T† = √τ_Bell·(∑_T Q_T)·√τ_Bell = √τ_Bell·√τ_Bell
=
  τ_Bell` exactly (each `(B_T ⊗ 𝟙)|Ω⟩⟨Ω|(B_T ⊗ 𝟙)†` has marginal `B_T B_T†` via
  `partialTraceB_sandwich_tensor_one` + `maxEntangledOp_partialTraceB`; the type projectors resolve
  the identity `∑_T Q_T = 1`).
* It is a sum over the `C(n+3,3)`-element type index `Sym (Fin 4) n`
  (`Sym.card_sym_eq_choose`) of rank-`≤ 1` terms, so its rank is `≤ C(n+3,3) = bb84PolyDimTight n`.

This is the genuine **type-mixture** (rank `C(n+3,3)`), not the rank-`1` pure purification.
Protocol-independent (no BB84 or QKD-protocol object beyond the pure scalar dimension
`bb84PolyDimTight`).

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Thm 3, App. B (B13-B19),
Lemma 2 (`x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry); CKR 2009 (`arXiv:0809.3019`) §III; the Bell
domination `bb84_bellSym_deFinetti_domination` (`Quantum/Symmetry/BellDeFinettiDomination.lean`). -/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy Math.ClassicalEntropy Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Engine

noncomputable section

namespace Quantum.Symmetry

/-! ## The Bell type of a joint computational index and the type partition projectors -/

/-- **The Bell type of a joint computational index** `i : Fin (4ⁿ)`: the multiset of the four Bell
symbols `Fin 4` of the length-`n` Bell string `(finFunctionFinEquiv 4 n).symm i`, packaged as an
element of `Sym (Fin 4) n` (a size-`n` multiset over `Fin 4`).  The fibers of this map are the
`C(n+3,3)` Bell **type** sectors; `finFunctionFinEquiv` is the same mixed-radix decoding the joint
Bell rotation `bellRotation` (a `tensorFamily`) uses. -/
def bellTypeOfIndex (n : ℕ) (i : Fin (4 ^ n)) : Sym (Fin 4) n :=
  ⟨(Finset.univ.val : Multiset (Fin n)).map ((@finFunctionFinEquiv 4 n).symm i),
    by rw [Multiset.card_map]; simp⟩

/-- **The computational-basis Bell-type projector** `P_T = diag(𝟙[type i = T])`: the diagonal
indicator of the joint computational indices of Bell type `T`.  Conjugating by the Bell rotation
gives the joint-Bell-basis type-`T` sector projector `bellTypeProjector`. -/
def bellTypeDiagProjector (n : ℕ) (T : Sym (Fin 4) n) : Op (4 ^ n) :=
  Matrix.diagonal (fun i => if bellTypeOfIndex n i = T then (1 : ℂ) else 0)

/-- The computational-basis Bell-type projector is Hermitian (real diagonal). -/
lemma bellTypeDiagProjector_isHermitian (n : ℕ) (T : Sym (Fin 4) n) :
    (bellTypeDiagProjector n T).IsHermitian := by
  unfold Matrix.IsHermitian bellTypeDiagProjector
  rw [Matrix.diagonal_conjTranspose]
  refine congrArg Matrix.diagonal ?_
  funext i
  simp only [Pi.star_apply, apply_ite (Star.star : ℂ → ℂ), star_one, star_zero]

/-- The computational-basis Bell-type projector is idempotent (`0/1` diagonal). -/
lemma bellTypeDiagProjector_mul_self (n : ℕ) (T : Sym (Fin 4) n) :
    bellTypeDiagProjector n T * bellTypeDiagProjector n T = bellTypeDiagProjector n T := by
  unfold bellTypeDiagProjector
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split <;> simp

/-- The computational-basis Bell-type projectors resolve the identity: `∑_T P_T = 𝟙` (every joint
index has exactly one Bell type). -/
lemma bellTypeDiagProjector_sum (n : ℕ) :
    ∑ T : Sym (Fin 4) n, bellTypeDiagProjector n T = 1 := by
  ext i j
  simp only [Matrix.sum_apply, bellTypeDiagProjector, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    rw [Finset.sum_ite_eq Finset.univ (bellTypeOfIndex n i) (fun _ => (1 : ℂ))]
    simp
  · simp [hij]

/-- **The joint-Bell-basis Bell-type sector projector** `Q_T = V^{⊗n}†·P_T·V^{⊗n}`: the orthogonal
projector onto the joint Bell strings of type `T`, obtained by conjugating the computational-basis
type indicator `P_T` back through the Bell rotation `V^{⊗n} = bellRotation n`. -/
def bellTypeProjector (n : ℕ) (T : Sym (Fin 4) n) : Op (4 ^ n) :=
  (bellRotation n)ᴴ * bellTypeDiagProjector n T * bellRotation n

/-- The Bell-type sector projector is Hermitian. -/
lemma bellTypeProjector_isHermitian (n : ℕ) (T : Sym (Fin 4) n) :
    (bellTypeProjector n T).IsHermitian := by
  have hP := bellTypeDiagProjector_isHermitian n T
  unfold Matrix.IsHermitian bellTypeProjector
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]

/-- The Bell-type sector projector is idempotent (uses `V^{⊗n}·V^{⊗n}† = 1` and `P_T² = P_T`). -/
lemma bellTypeProjector_mul_self (n : ℕ) (T : Sym (Fin 4) n) :
    bellTypeProjector n T * bellTypeProjector n T = bellTypeProjector n T := by
  have hW : bellRotation n * (bellRotation n)ᴴ = 1 := bellRotation_mul_conjTranspose n
  have hP : bellTypeDiagProjector n T * bellTypeDiagProjector n T = bellTypeDiagProjector n T :=
    bellTypeDiagProjector_mul_self n T
  unfold bellTypeProjector
  calc (bellRotation n)ᴴ * bellTypeDiagProjector n T * bellRotation n *
          ((bellRotation n)ᴴ * bellTypeDiagProjector n T * bellRotation n)
         = (bellRotation n)ᴴ * bellTypeDiagProjector n T *
          (bellRotation n * (bellRotation n)ᴴ) * bellTypeDiagProjector n T * bellRotation n := by
        noncomm_ring
    _ = (bellRotation n)ᴴ * bellTypeDiagProjector n T * 1 *
          bellTypeDiagProjector n T * bellRotation n := by rw [hW]
    _ = (bellRotation n)ᴴ * (bellTypeDiagProjector n T * bellTypeDiagProjector n T) *
          bellRotation n := by rw [Matrix.mul_one]; noncomm_ring
    _ = (bellRotation n)ᴴ * bellTypeDiagProjector n T * bellRotation n := by rw [hP]

/-- The Bell-type sector projectors resolve the identity: `∑_T Q_T = 𝟙` (uses `∑_T P_T = 𝟙` and
`V^{⊗n}†·V^{⊗n} = 1`). -/
lemma bellTypeProjector_sum (n : ℕ) :
    ∑ T : Sym (Fin 4) n, bellTypeProjector n T = 1 := by
  unfold bellTypeProjector
  simp_rw [Matrix.mul_assoc]
  rw [← Finset.mul_sum, ← Finset.sum_mul, bellTypeDiagProjector_sum, Matrix.one_mul,
    bellRotation_unitary]

/-! ## The Bell joint de Finetti mixture state -/

/-- **The Bell type-coherent Kraus operator** `B_T = √τ_Bell · Q_T`. -/
def bellPairedKraus (n : ℕ) [NeZero n] (T : Sym (Fin 4) n) : Op (4 ^ n) :=
  sqrtOp (bb84BellDeFinettiDensity n) * bellTypeProjector n T

/-- **The key marginal identity**: `∑_T B_T B_T† = τ_Bell`.  The type projectors resolve the
identity, so `∑_T √τ_Bell·Q_T·√τ_Bell = √τ_Bell·(∑_T Q_T)·√τ_Bell = √τ_Bell·√τ_Bell = τ_Bell`. -/
lemma bellPairedKraus_mul_conjTranspose_sum (n : ℕ) [NeZero n] :
    ∑ T : Sym (Fin 4) n, bellPairedKraus n T * (bellPairedKraus n T)ᴴ =
      (bb84BellDeFinettiDensity n).toOp := by
  have hsqrtH : (sqrtOp (bb84BellDeFinettiDensity n))ᴴ = sqrtOp (bb84BellDeFinettiDensity n) :=
    sqrtOp_isHermitian (bb84BellDeFinettiDensity n)
  have hsqrtSq : sqrtOp (bb84BellDeFinettiDensity n) * sqrtOp (bb84BellDeFinettiDensity n) =
      (bb84BellDeFinettiDensity n).toOp := sqrtOp_sq (bb84BellDeFinettiDensity n)
  have hterm : ∀ T : Sym (Fin 4) n, bellPairedKraus n T * (bellPairedKraus n T)ᴴ =
      sqrtOp (bb84BellDeFinettiDensity n) * bellTypeProjector n T *
        sqrtOp (bb84BellDeFinettiDensity n) := by
    intro T
    unfold bellPairedKraus
    rw [conjTranspose_mul, (bellTypeProjector_isHermitian n T), hsqrtH]
    rw [show sqrtOp (bb84BellDeFinettiDensity n) * bellTypeProjector n T *
            (bellTypeProjector n T * sqrtOp (bb84BellDeFinettiDensity n))
          = sqrtOp (bb84BellDeFinettiDensity n) *
            (bellTypeProjector n T * bellTypeProjector n T) *
            sqrtOp (bb84BellDeFinettiDensity n) from by noncomm_ring,
      (bellTypeProjector_mul_self n T)]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, bellTypeProjector_sum, Matrix.mul_one, hsqrtSq]

/-- **The Bell joint de Finetti mixture operator** `∑_T (B_T ⊗ 𝟙)·|Ω⟩⟨Ω|·(B_T ⊗ 𝟙)†`. -/
def bb84BellPairedDeFinettiStateOp (n : ℕ) [NeZero n] : Op ((4 ^ n) * (4 ^ n)) :=
  ∑ T : Sym (Fin 4) n,
    Op.tensor (bellPairedKraus n T) 1 * maxEntangledOp (4 ^ n) *
      (Op.tensor (bellPairedKraus n T) 1)ᴴ

/-- The Bell joint de Finetti mixture operator is positive semidefinite (a sum of `B·Ω·B†` with `Ω`
PSD). -/
lemma bb84BellPairedDeFinettiStateOp_posSemidef (n : ℕ) [NeZero n] :
    (bb84BellPairedDeFinettiStateOp n).PosSemidef := by
  have hΩ : (maxEntangledOp (4 ^ n)).PosSemidef := maxEntangledOp_posSemidef (4 ^ n)
  unfold bb84BellPairedDeFinettiStateOp
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero ?_
  intro T _
  exact hΩ.mul_mul_conjTranspose_same (Op.tensor (bellPairedKraus n T) 1)

/-- **The `A`-marginal is `τ_Bell`**: `partialTraceB` of the Bell joint
mixture is `bb84BellDeFinettiDensity n`.  Each term's marginal is `B_T B_T†`
(`partialTraceB_sandwich_tensor_one` + `maxEntangledOp_partialTraceB`); the sum is the key marginal
identity. -/
lemma bb84BellPairedDeFinettiStateOp_partialTraceB (n : ℕ) [NeZero n] :
    partialTraceB (bb84BellPairedDeFinettiStateOp n) = (bb84BellDeFinettiDensity n).toOp := by
  unfold bb84BellPairedDeFinettiStateOp
  rw [partialTraceB_finset_sum]
  have hterm : ∀ T : Sym (Fin 4) n,
      partialTraceB (Op.tensor (bellPairedKraus n T) 1 * maxEntangledOp (4 ^ n) *
        (Op.tensor (bellPairedKraus n T) 1)ᴴ) =
        bellPairedKraus n T * (bellPairedKraus n T)ᴴ := by
    intro T
    rw [Op.tensor_conjTranspose, Matrix.conjTranspose_one,
      partialTraceB_sandwich_tensor_one, maxEntangledOp_partialTraceB, Matrix.mul_one]
  simp_rw [hterm]
  exact bellPairedKraus_mul_conjTranspose_sum n

/-- The Bell joint de Finetti mixture operator has trace `1` (its `A`-marginal `τ_Bell` does). -/
lemma bb84BellPairedDeFinettiStateOp_trace (n : ℕ) [NeZero n] :
    (bb84BellPairedDeFinettiStateOp n).trace = 1 := by
  rw [← trace_partialTraceB (bb84BellPairedDeFinettiStateOp n),
    bb84BellPairedDeFinettiStateOp_partialTraceB]
  exact (bb84BellDeFinettiDensity n).trace_one

/-- **The Bell joint de Finetti mixture state** `bb84BellPairedDeFinettiState n` on `(4ⁿ)·(4ⁿ)`:
the rank-`C(n+3,3)` type-coherent mixture purifying `τ_Bell`.  Explicit; no
`Classical.choose`, no `sorry`. -/
def bb84BellPairedDeFinettiState (n : ℕ) [NeZero n] : DensityOp ((4 ^ n) * (4 ^ n)) where
  toOp := bb84BellPairedDeFinettiStateOp n
  isHermitian := (bb84BellPairedDeFinettiStateOp_posSemidef n).1
  pos_semidef := fun v =>
    posSemidef_re_quadraticForm_nonneg (bb84BellPairedDeFinettiStateOp_posSemidef n) v
  trace_one := bb84BellPairedDeFinettiStateOp_trace n

/-- **The `A`-marginal of the Bell joint mixture is `τ_Bell`.** -/
theorem bb84BellPairedDeFinettiState_partialTraceB (n : ℕ) [NeZero n] :
    (bb84BellPairedDeFinettiState n).partialTraceB = bb84BellDeFinettiDensity n := by
  apply DensityOp.ext
  change partialTraceB (bb84BellPairedDeFinettiStateOp n) = (bb84BellDeFinettiDensity n).toOp
  exact bb84BellPairedDeFinettiStateOp_partialTraceB n

/-- The maximally entangled operator is the outer product `vecMulVec ω (star ω)` of its canonical
ket vector `ω`. -/
lemma maxEntangledOp_eq_vecMulVec (N : ℕ) :
    maxEntangledOp N =
      Matrix.vecMulVec (maxEntangledKet N).vec (star (maxEntangledKet N).vec) := by
  ext i j
  simp only [maxEntangledOp, Matrix.of_apply, Matrix.vecMulVec_apply, maxEntangledKet,
    Pi.star_apply]
  have hstar :
      (star (if (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm j).2 then (1 : ℂ) else 0))
        = (if (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm j).2 then (1 : ℂ) else 0) := by
    split <;> simp
  rw [hstar]
  split_ifs <;> simp_all

/-- A `M * maxEntangledOp * Mᴴ` sandwich is the rank-at-most-one outer product of `M *ᵥ ω`. -/
lemma op_sandwich_maxEntangled_eq_vecMulVec {N : ℕ} (Mop : Op (N * N)) :
    Mop * maxEntangledOp N * Mopᴴ =
      Matrix.vecMulVec (Mop *ᵥ (maxEntangledKet N).vec)
        (star (Mop *ᵥ (maxEntangledKet N).vec)) := by
  rw [maxEntangledOp_eq_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    ← Matrix.star_mulVec]

/-- **The rank of the Bell joint mixture is `≤ C(n+3,3)`.**

The Bell joint mixture factors as `C·Cᴴ` with the column matrix `C` indexed by the
`C(n+3,3)`-element Bell type set `Sym (Fin 4) n` (`C i T = (B_T ⊗ 𝟙) *ᵥ ω`), so its rank is at most
the number of columns `C(n+3,3)` (`Matrix.rank_mul_le_left` + `Matrix.rank_le_card_width` +
`Sym.card_sym_eq_choose`). -/
theorem bb84BellPairedDeFinettiState_rank_le_polyDimTight (n : ℕ) [NeZero n] :
    Matrix.rank (bb84BellPairedDeFinettiState n).toOp ≤ bb84PolyDimTight n := by
  classical
  set C : Matrix (Fin (4 ^ n * 4 ^ n)) (Sym (Fin 4) n) ℂ :=
    Matrix.of fun i T =>
      (Op.tensor (bellPairedKraus n T) 1 *ᵥ (maxEntangledKet (4 ^ n)).vec) i with hC
  have hJC : (bb84BellPairedDeFinettiState n).toOp = C * Cᴴ := by
    change bb84BellPairedDeFinettiStateOp n = C * Cᴴ
    unfold bb84BellPairedDeFinettiStateOp
    ext i j
    rw [Matrix.sum_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [op_sandwich_maxEntangled_eq_vecMulVec, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply,
      hC, Matrix.of_apply, Matrix.of_apply, Pi.star_apply]
  rw [hJC]
  calc (C * Cᴴ).rank ≤ C.rank := Matrix.rank_mul_le_left C Cᴴ
    _ ≤ Fintype.card (Sym (Fin 4) n) := Matrix.rank_le_card_width C
    _ = bb84PolyDimTight n := by
        rw [Sym.card_sym_eq_choose, Fintype.card_fin, bb84PolyDimTight,
          show 4 + n - 1 = n + 3 from by omega]
        have h := Nat.choose_symm (n := n + 3) (k := 3) (by omega)
        rwa [show n + 3 - 3 = n from by omega] at h

end Quantum.Symmetry

end -- noncomputable section
