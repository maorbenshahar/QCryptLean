import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import QCryptLean.Math.LinearAlgebra.GramRigidity
import Mathlib.Tactic.LinearCombination

/-!
# Choi rank and Kraus proportionality

A single Kraus conjugation has Choi rank at most one. A finite sum of conjugations can equal one
conjugation only if every pair of Kraus matrices is proportional.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Channels Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- The **Choi vector** of a rectangular matrix `L`: the same data read as a vector on the
composite index `Fin (p * q)`, input index first, output index second — exactly the index
convention of `Quantum.Channels.ChoiMatrix`. -/
def conjChoiVec {p q : ℕ} (L : Matrix (Fin q) (Fin p) ℂ) : Fin (p * q) → ℂ :=
  fun α => L (finProdFinEquiv.symm α).2 (finProdFinEquiv.symm α).1

/-- The Choi matrix of a **single conjugation** `ρ ↦ L ρ Lᴴ` is the outer product of its Choi
vector with itself.  Reuses `Quantum.Channels.ChoiMatrix` — this module introduces no second
notion of Choi matrix. -/
theorem choiMatrix_matrixConjLinear {p q : ℕ} [NeZero p] [NeZero q]
    (L : Matrix (Fin q) (Fin p) ℂ) :
    ChoiMatrix p q ⇑(krausMapFintype (fun _ : Unit => L)) =
      Matrix.vecMulVec (conjChoiVec L) (star (conjChoiVec L)) := by
  ext α β
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective α
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective β
  simp only [ChoiMatrix, Matrix.of_apply, Matrix.vecMulVec, conjChoiVec, Pi.star_apply,
    Equiv.toFun_as_coe, Equiv.symm_apply_apply, krausMapFintype, LinearMap.coe_mk,
    AddHom.coe_mk, Fintype.sum_unique]
  exact mul_unitMatrix_conjTranspose_apply L i j a b

/-- A single Kraus conjugation `ρ ↦ L ρ Lᴴ` has Choi rank at most `1`. -/
theorem choiMatrix_matrixConjLinear_rank_le_one {p q : ℕ} [NeZero p] [NeZero q]
    (L : Matrix (Fin q) (Fin p) ℂ) :
    Matrix.rank (ChoiMatrix p q ⇑(krausMapFintype (fun _ : Unit => L))) ≤ 1 := by
  rw [choiMatrix_matrixConjLinear]
  exact Matrix.rank_vecMulVec_le _ _

/-- **The obstruction, entrywise.**  If a finite family of conjugations sums to a *single*
conjugation, then every `2×2` minor built from two members of the family vanishes. -/
theorem matrixConjLinear_sum_eq_single_minor {p q : ℕ} {κ : Type*}
    [Fintype κ] (K : κ → Matrix (Fin q) (Fin p) ℂ) (L : Matrix (Fin q) (Fin p) ℂ)
    (h : ∑ x, krausMapFintype (fun _ : Unit => K x) = krausMapFintype (fun _ : Unit => L))
    (x y : κ) (a b : Fin q) (i j : Fin p) :
    K x a i * K y b j = K y a i * K x b j := by
  have hentry : ∀ ai bj : Fin q × Fin p,
      ∑ z, K z ai.1 ai.2 * star (K z bj.1 bj.2) = L ai.1 ai.2 * star (L bj.1 bj.2) := by
    rintro ⟨a', i'⟩ ⟨b', j'⟩
    have hap := congrArg
      (fun F : Op p →ₗ[ℂ] Op q =>
        F (Matrix.of fun r c => if r = i' ∧ c = j' then (1 : ℂ) else 0) a' b') h
    simpa only [LinearMap.sum_apply, Matrix.sum_apply, krausMapFintype, LinearMap.coe_mk,
      AddHom.coe_mk, Fintype.sum_unique, mul_unitMatrix_conjTranspose_apply] using hap
  exact outerSum_eq_outer_minor (fun z ai => K z ai.1 ai.2) (fun ai => L ai.1 ai.2)
    hentry x y (a, i) (b, j)

/-- **The obstruction.**  A fibre sum of conjugations that equals a *single* conjugation forces
the fibre's Kraus operators to be pairwise proportional: for any two members `K x`, `K y`, either
`K x = 0` or `K y` is a scalar multiple of `K x`.

Thus a sum with nonproportional Kraus operators cannot admit a single Kraus conjugation. -/
theorem matrixConjLinear_sum_eq_single_proportional {p q : ℕ} {κ : Type*}
    [Fintype κ] (K : κ → Matrix (Fin q) (Fin p) ℂ) (L : Matrix (Fin q) (Fin p) ℂ)
    (h : ∑ x, krausMapFintype (fun _ : Unit => K x) = krausMapFintype (fun _ : Unit => L))
    (x y : κ) :
    K x = 0 ∨ ∃ c : ℂ, K y = c • K x := by
  by_cases hx : K x = 0
  · exact Or.inl hx
  refine Or.inr ?_
  obtain ⟨a₀, i₀, ha₀⟩ : ∃ a i, K x a i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (by ext a i; simpa using hc a i)
  refine ⟨K y a₀ i₀ / K x a₀ i₀, ?_⟩
  ext b j
  have hmin := matrixConjLinear_sum_eq_single_minor K L h x y a₀ b i₀ j
  rw [Matrix.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff ha₀]
  linear_combination hmin

/-- **The obstruction, two-operator case** — the shape the fibre argument needs.  If
`ρ ↦ A ρ Aᴴ + B ρ Bᴴ` equals a single conjugation `ρ ↦ L ρ Lᴴ`, then `A = 0` or `B` is a scalar
multiple of `A`. -/
theorem matrixConjLinear_add_eq_single_proportional {p q : ℕ}
    (A B L : Matrix (Fin q) (Fin p) ℂ)
    (h : krausMapFintype (fun _ : Unit => A) + krausMapFintype (fun _ : Unit => B) =
      krausMapFintype (fun _ : Unit => L)) :
    A = 0 ∨ ∃ c : ℂ, B = c • A := by
  have h' : ∑ t : Bool, krausMapFintype (fun _ : Unit => cond t B A) =
      krausMapFintype (fun _ : Unit => L) := by
    rw [Fintype.sum_bool]
    simpa only [Bool.cond_true, Bool.cond_false, add_comm] using h
  simpa only [Bool.cond_true, Bool.cond_false] using
    matrixConjLinear_sum_eq_single_proportional (fun t => cond t B A) L h' false true

/-- The sum of two identical Kraus conjugations is the single conjugation by `√2 • A`. -/
theorem matrixConjLinear_add_self_eq_single {p q : ℕ} (A : Matrix (Fin q) (Fin p) ℂ) :
    krausMapFintype (fun _ : Unit => A) + krausMapFintype (fun _ : Unit => A)
      = krausMapFintype (fun _ : Unit => ((Real.sqrt 2 : ℝ) : ℂ) • A) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num)
  refine LinearMap.ext fun ρ => ?_
  simp only [LinearMap.add_apply, krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_unique, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_ofReal, h2]
  rw [two_smul]

end Quantum.Channels
