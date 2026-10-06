import QCryptLean.Quantum.Gates
import QCryptLean.Quantum.Operators.DensityOperator
import QCryptLean.Quantum.Operators.BraKet.Projector
import QCryptLean.Quantum.TensorProducts.PartialTrace
import QCryptLean.Quantum.Tactic.QISimp
import QCryptLean.Quantum.Metrics.TraceNorm.Fidelity

/-!
# Bell States — definitions, orthonormality, completeness, density operator

The four Bell states are maximally entangled two-qubit states forming an
orthonormal basis for the 4-dimensional Hilbert space.

## Main definitions
- `bellState00`, `bellState01`, `bellState10`, `bellState11`: The four Bell states
- `bellState00_tensor`: n-fold tensor product |β₀₀⟩^⊗n
- `bellState00_density`: The density operator |β₀₀⟩⟨β₀₀|

## Main statements
- `bellStates_orthonormal`: Bell states form an orthonormal basis
- `bell_projectors_sum_identity`: Completeness relation Σᵢ |βᵢ⟩⟨βᵢ| = I
- `bell_fidelity_sum_eq_one`: Fidelities with all Bell states sum to 1
- `bellState00_density_is_pure`: The Bell state density operator is pure
- `X_on_bell00`, `Z_on_bell00`, `Y_on_bell00`: Pauli error transformations
- `hadamard_tensor_hadamard_mul_bellState00` and its three companions: `H ⊗ H` fixes `|β₀₀⟩`,
  exchanges `|β₀₁⟩` and `|β₁₀⟩`, and negates `|β₁₁⟩`
- `bellState00_vec` … `bellState11_vec`: the Bell kets as explicit vectors, via
  `stdKet_tensor_stdKet` (`|a⟩ ⊗ |b⟩` is the basis ket of index `2a + b`)
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Gates
open Quantum.Metrics

noncomputable section

namespace Quantum.Basis.BellStates

/-!
## Bell State Definitions

The four Bell states form an orthonormal basis for the two-qubit Hilbert space.
They are maximally entangled states.

  |β₀₀⟩ = (|00⟩ + |11⟩) / √2
  |β₁₀⟩ = (|00⟩ - |11⟩) / √2
  |β₀₁⟩ = (|01⟩ + |10⟩) / √2
  |β₁₁⟩ = (|01⟩ - |10⟩) / √2
-/

/-- Recast a ket along a dimension equality proof. -/
def ketCast {n m : ℕ} (ψ : Ket n) (h : n = m) : Ket m :=
  ⟨fun i => ψ.vec (i.cast h.symm)⟩

/-- Recast a bra along a dimension equality proof. -/
def braCast {n m : ℕ} (φ : Bra n) (h : n = m) : Bra m :=
  ⟨fun i => φ.vec (i.cast h.symm)⟩

-- Dagger of cast commutes with cast
@[simp]
theorem dag_ketCast {n m : ℕ} (ψ : Ket n) (h : n = m) :
    (ketCast ψ h).dag = braCast ψ.dag h := by
  subst h; rfl

-- Inner product preserved under cast
lemma inner_ketCast {n m : ℕ} (ψ : Ket n) (h : n = m) :
    (ketCast ψ h).dag * (ketCast ψ h) = ψ.dag * ψ := by
  subst h
  rfl

/-- The Bell state |β₀₀⟩ = |Φ⁺⟩ = (|00⟩ + |11⟩) / √2.
    Convention: subscript is (z,x), so (I⊗Z)|β₀₀⟩ = |β₁₀⟩ and (I⊗X)|β₀₀⟩ = |β₀₁⟩.
    This is the transpose of the Nielsen & Chuang convention |β_{x,z}⟩. -/
def bellState00 : Ket 4 := (1 / Real.sqrt 2 : ℂ) • (|0⟩ ⊗ |0⟩ + |1⟩ ⊗ |1⟩)

/-- The Bell state |β₁₀⟩ = |Φ⁻⟩ = (|00⟩ - |11⟩) / √2 -/
def bellState10 : Ket 4 := (1 / Real.sqrt 2 : ℂ) • (|0⟩ ⊗ |0⟩ - |1⟩ ⊗ |1⟩)

/-- The Bell state |β₀₁⟩ = |Ψ⁺⟩ = (|01⟩ + |10⟩) / √2 -/
def bellState01 : Ket 4 := (1 / Real.sqrt 2 : ℂ) • (|0⟩ ⊗ |1⟩ + |1⟩ ⊗ |0⟩)

/-- The Bell state |β₁₁⟩ = |Ψ⁻⟩ = (|01⟩ - |10⟩) / √2 -/
def bellState11 : Ket 4 := (1 / Real.sqrt 2 : ℂ) • (|0⟩ ⊗ |1⟩ - |1⟩ ⊗ |0⟩)

/-!
## Explicit computational-basis vectors

`|a⟩ ⊗ |b⟩` is the basis ket of index `2a + b`, so each Bell ket is `(√2)⁻¹` times an explicit
`±1`/`0` vector. Finite computations with Bell states rewrite with these once instead of unfolding
the tensor-product definition entry by entry.
-/

/-- `|a⟩ ⊗ |b⟩` is the computational-basis ket of the pair index `finProdFinEquiv (a, b)`. -/
theorem stdKet_tensor_stdKet {n m : ℕ} (a : Fin n) (b : Fin m) :
    stdKet n a ⊗ stdKet m b = stdKet (n * m) (finProdFinEquiv (a, b)) := by
  ext k
  rw [Ket.tensor_vec, stdKet_apply, stdKet_apply, stdKet_apply, ite_zero_mul_ite_zero, mul_one]
  refine if_congr ?_ rfl rfl
  rw [Equiv.apply_eq_iff_eq_symm_apply, Prod.ext_iff]

/-- The four computational-basis vectors of `ℂ⁴` as explicit vectors. -/
private theorem stdKet_four_vec :
    (stdKet 4 0).vec = ![1, 0, 0, 0] ∧ (stdKet 4 1).vec = ![0, 1, 0, 0] ∧
      (stdKet 4 2).vec = ![0, 0, 1, 0] ∧ (stdKet 4 3).vec = ![0, 0, 0, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext k <;> fin_cases k <;> rfl

/-- `|β₀₀⟩ = (|00⟩ + |11⟩)/√2` as an explicit vector. -/
theorem bellState00_vec : bellState00.vec = (Real.sqrt 2 : ℂ)⁻¹ • ![1, 0, 0, 1] := by
  rw [bellState00, stdKet_tensor_stdKet, stdKet_tensor_stdKet, one_div]
  change (Real.sqrt 2 : ℂ)⁻¹ • ((stdKet 4 0).vec + (stdKet 4 3).vec) = _
  rw [stdKet_four_vec.1, stdKet_four_vec.2.2.2]
  simp only [Matrix.cons_add_cons, Matrix.empty_add_empty, add_zero, zero_add]

/-- `|β₀₁⟩ = (|01⟩ + |10⟩)/√2` as an explicit vector. -/
theorem bellState01_vec : bellState01.vec = (Real.sqrt 2 : ℂ)⁻¹ • ![0, 1, 1, 0] := by
  rw [bellState01, stdKet_tensor_stdKet, stdKet_tensor_stdKet, one_div]
  change (Real.sqrt 2 : ℂ)⁻¹ • ((stdKet 4 1).vec + (stdKet 4 2).vec) = _
  rw [stdKet_four_vec.2.1, stdKet_four_vec.2.2.1]
  simp only [Matrix.cons_add_cons, Matrix.empty_add_empty, add_zero, zero_add]

/-- `|β₁₀⟩ = (|00⟩ - |11⟩)/√2` as an explicit vector. -/
theorem bellState10_vec : bellState10.vec = (Real.sqrt 2 : ℂ)⁻¹ • ![1, 0, 0, -1] := by
  rw [bellState10, stdKet_tensor_stdKet, stdKet_tensor_stdKet, one_div]
  change (Real.sqrt 2 : ℂ)⁻¹ • ((stdKet 4 0).vec - (stdKet 4 3).vec) = _
  rw [stdKet_four_vec.1, stdKet_four_vec.2.2.2]
  simp only [Matrix.cons_sub_cons, Matrix.empty_sub_empty, sub_zero, zero_sub]

/-- `|β₁₁⟩ = (|01⟩ - |10⟩)/√2` as an explicit vector. -/
theorem bellState11_vec : bellState11.vec = (Real.sqrt 2 : ℂ)⁻¹ • ![0, 1, -1, 0] := by
  rw [bellState11, stdKet_tensor_stdKet, stdKet_tensor_stdKet, one_div]
  change (Real.sqrt 2 : ℂ)⁻¹ • ((stdKet 4 1).vec - (stdKet 4 2).vec) = _
  rw [stdKet_four_vec.2.1, stdKet_four_vec.2.2.1]
  simp only [Matrix.cons_sub_cons, Matrix.empty_sub_empty, sub_zero, zero_sub]

/-!
## Normalization
-/

/-- |β₀₀⟩ is normalized: ⟨β₀₀|β₀₀⟩ = 1 -/
theorem bellState00_normalized : bellState00.dag * bellState00 = 1 := by
  unfold bellState00
  qisimp
  have h : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (by norm_num : (2:ℝ) > 0)
  field_simp [h]
  norm_cast
  exact (Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)).symm

/-- |β₁₀⟩ is normalized: ⟨β₁₀|β₁₀⟩ = 1 -/
theorem bellState10_normalized : bellState10.dag * bellState10 = 1 := by
  unfold bellState10
  simp only [Ket.dag_smul]
  rw [@Ket.dag_sub_eq_add_neg_smul (2 * 2)]
  simp only [Ket.sub_eq_add_neg_smul, Ket.dag_tensor]
  qisimp
  have h : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (by norm_num : (2:ℝ) > 0)
  field_simp [h]
  norm_cast
  exact (Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)).symm

/-- |β₀₁⟩ is normalized: ⟨β₀₁|β₀₁⟩ = 1 -/
theorem bellState01_normalized : bellState01.dag * bellState01 = 1 := by
  unfold bellState01
  qisimp
  have h : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (by norm_num : (2:ℝ) > 0)
  field_simp [h]
  norm_cast
  exact (Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)).symm

/-- |β₁₁⟩ is normalized: ⟨β₁₁|β₁₁⟩ = 1 -/
theorem bellState11_normalized : bellState11.dag * bellState11 = 1 := by
  unfold bellState11
  simp only [Ket.dag_smul]
  rw [@Ket.dag_sub_eq_add_neg_smul (2 * 2)]
  simp only [Ket.sub_eq_add_neg_smul, Ket.dag_tensor]
  qisimp
  have h : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (by norm_num : (2:ℝ) > 0)
  field_simp [h]
  norm_cast
  exact (Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)).symm

/-!
## Orthonormality
-/

/-- Bell states |β₀₁⟩ and |β₁₁⟩ are orthogonal: ⟨β₀₁|β₁₁⟩ = 0 -/
theorem bell01_11_orthogonal : bellState01.dag * bellState11 = 0 := by
  unfold bellState01 bellState11
  qisimp

/-- Bell states |β₁₁⟩ and |β₀₁⟩ are orthogonal: ⟨β₁₁|β₀₁⟩ = 0 -/
theorem bell11_01_orthogonal : bellState11.dag * bellState01 = 0 := by
  unfold bellState01 bellState11
  simp only [Ket.dag_smul]
  rw [@Ket.dag_sub_eq_add_neg_smul (2 * 2)]
  simp only [Ket.dag_tensor]
  qisimp

/-- Bell states |β₁₀⟩ and |β₁₁⟩ are orthogonal: ⟨β₁₀|β₁₁⟩ = 0 -/
theorem bell10_11_orthogonal : bellState10.dag * bellState11 = 0 := by
  unfold bellState10 bellState11
  simp only [Ket.dag_smul]
  rw [@Ket.dag_sub_eq_add_neg_smul (2 * 2)]
  simp only [Ket.dag_tensor]
  qisimp

/-- Bell states |β₁₁⟩ and |β₁₀⟩ are orthogonal: ⟨β₁₁|β₁₀⟩ = 0 -/
theorem bell11_10_orthogonal : bellState11.dag * bellState10 = 0 := by
  unfold bellState10 bellState11
  simp only [Ket.dag_smul]
  rw [@Ket.dag_sub_eq_add_neg_smul (2 * 2)]
  simp only [Ket.dag_tensor]
  qisimp

/-- The unnormalised Bell vectors `√2 · |β_p⟩`, in the order `β₀₀, β₀₁, β₁₀, β₁₁`, as the rows
of an integer matrix. -/
private def bellRows : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 1; 0, 1, 1, 0; 1, 0, 0, -1; 0, 1, -1, 0]

/-- The rows of `bellRows` are orthogonal, each of squared length `2` (an integer identity). -/
private theorem bellRows_mul_transpose :
    bellRows * bellRows.transpose = 2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide

/-- The Bell kets are the rows of `bellRows`, cast to `ℂ` and scaled by `(√2)⁻¹`. -/
private theorem bellStates_vec (p : Fin 4) :
    (![bellState00, bellState01, bellState10, bellState11] p).vec =
      (Real.sqrt 2 : ℂ)⁻¹ • ((Int.cast : ℤ → ℂ) ∘ bellRows p) := by
  -- Casting an explicit integer vector casts it entrywise.
  have hcast (a b c d : ℤ) : ((Int.cast : ℤ → ℂ) ∘ ![a, b, c, d]) = ![(a : ℂ), b, c, d] :=
    (FinVec.map_eq _ _).symm
  have h00 := hcast 1 0 0 1
  have h01 := hcast 0 1 1 0
  have h10 := hcast 1 0 0 (-1)
  have h11 := hcast 0 1 (-1) 0
  simp only [Int.cast_one, Int.cast_zero, Int.cast_neg] at h00 h01 h10 h11
  fin_cases p
  · exact bellState00_vec.trans (congrArg _ h00.symm)
  · exact bellState01_vec.trans (congrArg _ h01.symm)
  · exact bellState10_vec.trans (congrArg _ h10.symm)
  · exact bellState11_vec.trans (congrArg _ h11.symm)

/-- Bell states form an orthonormal basis. -/
theorem bellStates_orthonormal (i j : Fin 4) :
    let states := ![bellState00, bellState01, bellState10, bellState11]
    (states i).dag * (states j) = if i = j then 1 else 0 := by
  dsimp only
  -- With the real scalar `c = (√2)⁻¹`, `⟨β_i|β_j⟩ = conj c · c · (B Bᵀ)ᵢⱼ` for `B = bellRows`.
  have hc : (starRingEnd ℂ) (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat, one_div]
  calc _ = ∑ k, (starRingEnd ℂ) (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ *
          ((bellRows i k * bellRows.transpose k j : ℤ) : ℂ) := by
        rw [bra_mul_ket_eq]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Ket.dag_vec, bellStates_vec, bellStates_vec, Pi.smul_apply, Pi.smul_apply,
          Function.comp_apply, Function.comp_apply, smul_eq_mul, smul_eq_mul, map_mul,
          map_intCast, Matrix.transpose_apply, Int.cast_mul]
        ring
    _ = 1 / 2 * (((bellRows * bellRows.transpose) i j : ℤ) : ℂ) := by
        rw [hc, ← Finset.mul_sum, Matrix.mul_apply, Int.cast_sum]
    _ = if i = j then 1 else 0 := by
        rw [bellRows_mul_transpose, Matrix.smul_apply, Matrix.one_apply]
        split_ifs <;> norm_num

/-!
## Pauli Error Transformations
-/

/-- Bit flip (X) on second qubit transforms |β₀₀⟩ to |β₀₁⟩. -/
theorem X_on_bell00 : (gateI ⊗ X) * bellState00 = bellState01 := by
  unfold bellState00 bellState01
  simp only [op_mul_smul_ket, Op_mul_add_ket, Op.tensor_mulKet]
  simp only [gateI_ket0, gateI_ket1, X_ket0, X_ket1]

/-- Phase flip (Z) on second qubit transforms |β₀₀⟩ to |β₁₀⟩. -/
theorem Z_on_bell00 : (gateI ⊗ Z) * bellState00 = bellState10 := by
  unfold bellState00 bellState10
  simp only [op_mul_smul_ket, Op_mul_add_ket, Op.tensor_mulKet]
  simp only [gateI_ket0, gateI_ket1, Z_ket0, Z_ket1]
  simp only [Ket.tensor_smul_right]
  simp_rw [← Ket.sub_eq_add_neg_smul]

/-- Combined bit+phase flip (Y) on second qubit transforms |β₀₀⟩ to i|β₁₁⟩. -/
theorem Y_on_bell00 : (gateI ⊗ Y) * bellState00 = Complex.I • bellState11 := by
  unfold bellState00 bellState11
  simp only [op_mul_smul_ket, Op_mul_add_ket, Op.tensor_mulKet]
  simp only [gateI_ket0, gateI_ket1, Y_ket0, Y_ket1]
  simp only [Ket.tensor_smul_right]
  ext i
  simp only [Ket.smul_vec, Pi.smul_apply, smul_eq_mul, Ket.add_vec, Ket.sub_vec, Ket.tensor_vec]
  ring

/-- Helper: (1 / √2) * conj(1 / √2) = 1/2 -/
lemma inv_sqrt_two_sq :
    (1 / Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (1 / Real.sqrt 2 : ℂ) = (1 / 2 : ℂ) := by
  norm_num
  have : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  field_simp
  ring_nf
  norm_cast
  linarith [sq_nonneg (Real.sqrt 2)]

/-- Helper: (√2)⁻¹ * (√2)⁻¹ = 1/2 -/
lemma inv_sqrt_two_mul_self :
    ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) = (1/2 : ℂ) := by
  rw [← mul_inv]
  have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    rw [← sq]
    exact Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)
  rw [h]
  norm_num

/-!
## The Hadamard pair on the Bell basis

`H ⊗ H` maps each Bell state to a Bell state: it fixes `|β₀₀⟩`, exchanges `|β₀₁⟩` and `|β₁₀⟩`,
and negates `|β₁₁⟩`. Conjugation by `H ⊗ H` therefore exchanges the projectors onto
`|β₀₁⟩` and `|β₁₀⟩` and fixes the other two Bell projectors.
-/

/-- `H ⊗ H` fixes `|β₀₀⟩`. -/
theorem hadamard_tensor_hadamard_mul_bellState00 :
    (hadamard ⊗ hadamard) * bellState00 = bellState00 := by
  unfold bellState00
  simp only [op_mul_smul_ket, Op_mul_add_ket, Op.tensor_mulKet, hadamard_ket0, hadamard_ket1]
  ext i
  fin_cases i <;>
    simp only [Ket.smul_vec, Ket.add_vec, Ket.sub_vec, Ket.tensor_vec,
      finProdFinEquiv_symm_apply, Pi.smul_apply, smul_eq_mul, Fin.isValue,
      Fin.divNat, Fin.modNat] <;>
    norm_num [pow_two, inv_sqrt_two_mul_self]

/-- `H ⊗ H` maps `|β₁₀⟩` to `|β₀₁⟩`. -/
theorem hadamard_tensor_hadamard_mul_bellState10 :
    (hadamard ⊗ hadamard) * bellState10 = bellState01 := by
  unfold bellState10 bellState01
  simp only [Ket.sub_eq_add_neg_smul, op_mul_smul_ket, Op_mul_add_ket, Op.tensor_mulKet,
    hadamard_ket0, hadamard_ket1]
  ext i
  fin_cases i <;>
    simp only [Ket.smul_vec, Ket.add_vec, Ket.tensor_vec, finProdFinEquiv_symm_apply,
      Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.divNat, Fin.modNat] <;>
    norm_num [pow_two, inv_sqrt_two_mul_self]

/-- `H ⊗ H` maps `|β₀₁⟩` to `|β₁₀⟩`. -/
theorem hadamard_tensor_hadamard_mul_bellState01 :
    (hadamard ⊗ hadamard) * bellState01 = bellState10 := by
  unfold bellState01 bellState10
  simp only [Ket.sub_eq_add_neg_smul, op_mul_smul_ket, Op_mul_add_ket, Op.tensor_mulKet,
    hadamard_ket0, hadamard_ket1]
  ext i
  fin_cases i <;>
    simp only [Ket.smul_vec, Ket.add_vec, Ket.tensor_vec, finProdFinEquiv_symm_apply,
      Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.divNat, Fin.modNat] <;>
    norm_num [pow_two, inv_sqrt_two_mul_self]

/-- `H ⊗ H` negates `|β₁₁⟩`. -/
theorem hadamard_tensor_hadamard_mul_bellState11 :
    (hadamard ⊗ hadamard) * bellState11 = (-1 : ℂ) • bellState11 := by
  unfold bellState11
  simp only [Ket.sub_eq_add_neg_smul, op_mul_smul_ket, Op_mul_add_ket, Op.tensor_mulKet,
    hadamard_ket0, hadamard_ket1]
  ext i
  fin_cases i <;>
    simp only [Ket.smul_vec, Ket.add_vec, Ket.tensor_vec, finProdFinEquiv_symm_apply,
      Pi.smul_apply, smul_eq_mul, Fin.isValue, Fin.divNat, Fin.modNat] <;>
    norm_num [pow_two, inv_sqrt_two_mul_self]

/-!
## Bell Basis Completeness

The four Bell states form a complete orthonormal basis for the 4-dimensional
two-qubit Hilbert space. This means:
1. They are orthonormal (proven above)
2. They satisfy completeness: Σᵢ |βᵢ⟩⟨βᵢ| = I
3. For any density operator ρ, the fidelities with all Bell states sum to 1
-/

/-- Bell basis completeness relation: The four Bell projectors sum to identity.

    |β₀₀⟩⟨β₀₀| + |β₀₁⟩⟨β₀₁| + |β₁₀⟩⟨β₁₀| + |β₁₁⟩⟨β₁₁| = I

    This is the standard completeness relation for an orthonormal basis: the matrix with the
    Bell kets as columns is an isometry (`bellStates_orthonormal`), hence unitary. -/
theorem bell_projectors_sum_identity :
    bellState00 * bellState00.dag + bellState01 * bellState01.dag +
    bellState10 * bellState10.dag + bellState11 * bellState11.dag = (1 : Op 4) := by
  -- `W` has the Bell kets as columns, so `Wᴴ * W = 1` is `bellStates_orthonormal`. A one-sided
  -- inverse of a square matrix is two-sided, and `W * Wᴴ = ∑ₚ |β_p⟩⟨β_p|` entrywise.
  let W : Op 4 :=
    Matrix.of fun k p => (![bellState00, bellState01, bellState10, bellState11] p).vec k
  have hW : W.conjTranspose * W = 1 := by
    ext i j
    rw [Matrix.one_apply, ← bellStates_orthonormal i j]
    simp [W, Matrix.mul_apply, bra_mul_ket_eq, Ket.dag_vec]
  have hW' : W * W.conjTranspose = 1 := mul_eq_one_comm.mp hW
  ext k l
  have hkl := congrFun (congrFun hW' k) l
  rw [Matrix.mul_apply, Fin.sum_univ_four] at hkl
  simpa [W, ket_mul_bra_apply] using hkl

/-- Bell basis completeness: For any density operator ρ on dimension 4,
    the sum of fidelities with all four Bell states equals 1.

    This expresses the completeness relation for the Bell basis:
    F²(ρ, |β₀₀⟩⟨β₀₀|) + F²(ρ, |β₀₁⟩⟨β₀₁|) + F²(ρ, |β₁₀⟩⟨β₁₀|) + F²(ρ, |β₁₁⟩⟨β₁₁|) = 1

    **Proof strategy**:
    1. Each F²(ρ, |β⟩⟨β|) = (⟨β|ρ|β⟩).re = Tr(|β⟩⟨β| · ρ).re
    2. Sum of traces equals trace of sum
    3. Bell completeness: Σᵢ |βᵢ⟩⟨βᵢ| = I
    4. Therefore sum = Tr(I · ρ).re = Tr(ρ).re = 1 -/
theorem bell_fidelity_sum_eq_one (ρ : DensityOp 4) :
    DensityOp.fidelitySq ρ (DensityOp.fromPure bellState00 bellState00_normalized) +
    DensityOp.fidelitySq ρ (DensityOp.fromPure bellState01 bellState01_normalized) +
    DensityOp.fidelitySq ρ (DensityOp.fromPure bellState10 bellState10_normalized) +
    DensityOp.fidelitySq ρ (DensityOp.fromPure bellState11 bellState11_normalized) = 1 := by
  haveI : NeZero 4 := ⟨by norm_num⟩
  -- Rewrite using fidelitySq_fromPure: each F²(ρ, |β⟩⟨β|) = (⟨β|ρ|β⟩).re
  simp only [fidelitySq_fromPure]
  -- Apply helper lemma: each (⟨βᵢ|ρ|βᵢ⟩).re = Tr(|βᵢ⟩⟨βᵢ| · ρ).re
  rw [← trace_ketbra_mul bellState00 ρ.toOp]
  rw [← trace_ketbra_mul bellState01 ρ.toOp]
  rw [← trace_ketbra_mul bellState10 ρ.toOp]
  rw [← trace_ketbra_mul bellState11 ρ.toOp]
  -- Combine: .re distributes over +
  rw [← Complex.add_re, ← Complex.add_re, ← Complex.add_re]
  -- Factor out .re and use linearity of trace
  rw [← Matrix.trace_add, ← Matrix.trace_add, ← Matrix.trace_add]
  -- Distribute multiplication over addition
  rw [← add_mul, ← add_mul, ← add_mul]
  -- Use Bell completeness: sum of projectors = I
  rw [bell_projectors_sum_identity]
  -- Tr(I · ρ) = Tr(ρ) = 1
  simp only [Matrix.one_mul]
  -- Extract real part: Tr(ρ).re = 1
  have h := ρ.trace_one
  -- h : Tr(ρ) = 1, need .re
  rw [h]
  simp

/-!
## n-fold Tensor Products
-/

/-- n-fold tensor product of Bell states.
    |β₀₀⟩^⊗0 = |⟩ (trivial 1-dimensional ket)
    |β₀₀⟩^⊗(n+1) = |β₀₀⟩ ⊗ |β₀₀⟩^⊗n -/
def bellState00_tensor (n : ℕ) : Ket (4 ^ n) :=
  match n with
  | 0 => ⟨![1]⟩  -- The unique normalized 1-dimensional ket
  | n + 1 => ketCast (bellState00 ⊗ bellState00_tensor n) (by ring)

/-- For n=1, the tensor product equals the base Bell state.
    bellState00_tensor 1 = ketCast (bellState00 ⊗ ⟨![1]⟩) h = bellState00
    This holds because tensoring with the 1-dim identity ket is the identity. -/
theorem bellState00_tensor_one : bellState00_tensor 1 = bellState00 := by
  unfold bellState00_tensor
  ext i
  simp only [ketCast]
  unfold Ket.tensor
  simp only
  -- bellState00_tensor 0 = ⟨![1]⟩ so .vec at any Fin 1 index is 1
  have h1 : (bellState00_tensor 0).vec
      (finProdFinEquiv.symm (Fin.cast (by ring : 4 ^ (0 + 1) = 4 * 1) i)).2 = 1 := by
    simp only [bellState00_tensor, Matrix.cons_val_fin_one]
  rw [h1, mul_one]
  congr 1
  ext
  change (Fin.cast _ i).val / 1 = i.val
  simp only [Nat.div_one, Fin.val_cast]

/-- The n-fold tensor product is normalized. -/
theorem bellState00_tensor_normalized (n : ℕ) :
    ((bellState00_tensor n).dag * (bellState00_tensor n)) = 1 := by
  induction n with
  | zero =>
    simp only [bellState00_tensor, bra_mul_ket_eq, Ket.dag_vec]
    simp only [Matrix.cons_val_fin_one, starRingEnd_apply, star_one, one_mul]
    simp only [Finset.sum_const, Finset.card_fin, pow_zero, one_smul]
  | succ n ih =>
    simp only [bellState00_tensor]
    rw [inner_ketCast]
    rw [Ket.dag_tensor]
    rw [bra_tensor_mul_ket_tensor]
    rw [bellState00_normalized, ih]
    ring

/-!
## Bell State Density Operator

The density operator |β₀₀⟩⟨β₀₀| is a pure state used in various quantum protocols.
-/

/-- bellState00 projector is Hermitian: (|β₀₀⟩⟨β₀₀|)† = |β₀₀⟩⟨β₀₀| -/
theorem bellState00_projector_hermitian :
    (bellState00 * bellState00.dag).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply]
  simp only [ket_mul_bra_apply, Ket.dag, starRingEnd_apply]
  rw [star_mul, star_star, mul_comm]

/-- bellState00 projector is positive semidefinite (for PosSemidefOp) -/
theorem bellState00_projector_pos_semidef :
    ∀ x : Fin 4 → ℂ, 0 ≤ (quadraticForm (bellState00 * bellState00.dag) x).re := by
  intro x
  -- ⟨x|(|β₀₀⟩⟨β₀₀|)|x⟩ = |⟨β₀₀|x⟩|² ≥ 0
  unfold quadraticForm
  simp only [ket_mul_bra_apply, Ket.dag, Matrix.mulVec,
             dotProduct, Pi.star_apply, starRingEnd_apply]
  -- Sum collapses to |∑ᵢ star(β₀₀ᵢ) * xᵢ|²
  have h : (∑ i, star (x i) * ∑ j, bellState00.vec i * star (bellState00.vec j) * x j).re =
           Complex.normSq (∑ i, star (bellState00.vec i) * x i) := by
    -- Expand: ∑ᵢⱼ star(xᵢ) * aᵢ * star(aⱼ) * xⱼ = |∑ᵢ star(aᵢ) * xᵢ|²
    -- Strategy: LHS = ∑ᵢⱼ star(xᵢ) * ψᵢ * star(ψⱼ) * xⱼ
    --         = (∑ⱼ star(ψⱼ) * xⱼ) * star(∑ᵢ star(ψᵢ) * xᵢ)
    --         = (∑ᵢ star(ψᵢ) * xᵢ) * conj(∑ᵢ star(ψᵢ) * xᵢ)
    --         = normSq (∑ᵢ star(ψᵢ) * xᵢ)
    -- First, distribute the sum to get double sum
    have step1 : ∑ i, star (x i) * ∑ j, bellState00.vec i * star (bellState00.vec j) * x j =
                 ∑ i, ∑ j, star (x i) * (bellState00.vec i * star (bellState00.vec j) * x j) := by
      congr 1
      ext i
      rw [Finset.mul_sum]
    rw [step1]
    -- Rearrange terms in the double sum using ring
    have step2 : ∑ i, ∑ j, star (x i) * (bellState00.vec i * star (bellState00.vec j) * x j) =
                 ∑ i, ∑ j, (star (bellState00.vec j) * x j) * (bellState00.vec i * star (x i)) := by
      congr 1
      ext i
      congr 1
      ext j
      ring
    rw [step2]
    -- Swap the order of summation
    rw [Finset.sum_comm]
    -- Factor out the first sum
    have step3 : ∑ j, ∑ i, (star (bellState00.vec j) * x j) * (bellState00.vec i * star (x i)) =
                 ∑ j, (star (bellState00.vec j) * x j) * (∑ i, bellState00.vec i * star (x i)) := by
      congr 1
      ext j
      rw [← Finset.mul_sum]
    rw [step3]
    -- Factor out to get product of two sums
    rw [← Finset.sum_mul]
    -- Now we have: ((∑ⱼ star(ψⱼ) * xⱼ) * (∑ᵢ ψᵢ * star(xᵢ))).re
    -- Apply star transformation to the second sum
    have h_star : ∑ i, bellState00.vec i * star (x i) =
                  star (∑ i, star (bellState00.vec i) * x i) := by
      rw [star_sum]
      congr 1
      ext i
      rw [star_mul, star_star, mul_comm]
    rw [h_star]
    -- Now: ((∑ⱼ star(ψⱼ) * xⱼ) * star(∑ star(ψ) * x)).re = normSq(∑ star(ψ) * x)
    -- Use Complex.mul_conj: z * conj z = normSq z
    have h_normSq : ((∑ i, star (bellState00.vec i) * x i) *
                     star (∑ i, star (bellState00.vec i) * x i)).re =
                    Complex.normSq (∑ i, star (bellState00.vec i) * x i) := by
      have h_coe : (∑ i, star (bellState00.vec i) * x i) *
                   star (∑ i, star (bellState00.vec i) * x i) =
                   (Complex.normSq (∑ i, star (bellState00.vec i) * x i) : ℂ) := by
        exact Complex.mul_conj _
      rw [h_coe]
      simp only [Complex.ofReal_re]
    exact h_normSq
  rw [h]
  exact Complex.normSq_nonneg _

/-- bellState00 projector has trace 1: Tr(|β₀₀⟩⟨β₀₀|) = 1 -/
theorem bellState00_projector_trace_one :
    (bellState00 * bellState00.dag).trace = 1 := by
  unfold Matrix.trace Matrix.diag
  simp only [ket_mul_bra_apply, Ket.dag, starRingEnd_apply]
  have h_norm : bellState00.dag * bellState00 = 1 := bellState00_normalized
  simp only [bra_mul_ket_eq, Ket.dag_vec, starRingEnd_apply] at h_norm
  convert h_norm using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The bellState00 density operator: ρ = |β₀₀⟩⟨β₀₀| -/
def bellState00_density : DensityOp 4 :=
  ⟨⟨⟨bellState00 * bellState00.dag, bellState00_projector_hermitian⟩,
     bellState00_projector_pos_semidef⟩,
   bellState00_projector_trace_one⟩

/-- |β₀₀⟩⟨β₀₀| is a pure state (ρ² = ρ) -/
theorem bellState00_density_is_pure : bellState00_density.IsPure := by
  unfold DensityOp.IsPure bellState00_density
  simp only []
  ext i j
  simp only [Matrix.mul_apply, ket_mul_bra_apply, Ket.dag, starRingEnd_apply]
  have h_inner : ∑ k : Fin 4, star (bellState00.vec k) * bellState00.vec k = 1 := by
    have h := bellState00_normalized
    simp only [Ket.dag, starRingEnd_apply] at h
    exact h
  calc ∑ k, bellState00.vec i * star (bellState00.vec k) *
           (bellState00.vec k * star (bellState00.vec j))
    = bellState00.vec i * (∑ k, star (bellState00.vec k) * bellState00.vec k) *
        star (bellState00.vec j) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro k _; ring
    _ = bellState00.vec i * 1 * star (bellState00.vec j) := by rw [h_inner]
    _ = bellState00.vec i * star (bellState00.vec j) := by ring

end Quantum.Basis.BellStates


end
