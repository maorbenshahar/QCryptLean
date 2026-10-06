import QCryptLean.LOCC.Typed.Instrument
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Entry laws of matrix conjugation

Coordinate formulas for the conjugation `ρ ↦ K ρ Kᴴ` by a rectangular Kraus matrix `K`: its
entries, the effect of vanishing products of two rows and of a vanishing row, of rows with a single
nonzero entry, and of a matrix unit.
A row of `K` with a single nonzero entry `c` at column `p` is written `K y = Pi.single p c`.

These are finite coordinate identities; no positivity, completeness or nonempty-type assumption is
made.
-/

open scoped Matrix BigOperators

open Matrix

namespace TypedLOCC

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Entry of a matrix conjugation. -/
theorem matrixConjLinear_apply (K : Matrix B A ℂ) (ρ : Op A) (y z : B) :
    matrixConjLinear K ρ y z = ∑ q, ∑ p, K y p * ρ p q * star (K z q) := by
  simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_mul _ _ _

/-- A conjugation `K ρ Kᴴ` has a zero `(y, z)` entry when every entry of row `y` of `K` times
every conjugated entry of row `z` vanishes. -/
theorem matrixConjLinear_apply_eq_zero (K : Matrix B A ℂ) (ρ : Op A) (y z : B)
    (h : ∀ x x', K y x * star (K z x') = 0) : matrixConjLinear K ρ y z = 0 := by
  rw [matrixConjLinear_apply]
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
  rw [mul_right_comm, h p q, zero_mul]

/-- A conjugation has a zero row wherever the Kraus matrix has one. -/
theorem matrixConjLinear_apply_eq_zero_of_row_left (K : Matrix B A ℂ) (ρ : Op A) {y : B}
    (hy : K y = 0) (z : B) : matrixConjLinear K ρ y z = 0 := by
  rw [matrixConjLinear_apply]
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
  rw [show K y p = 0 from congrFun hy p, zero_mul, zero_mul]

/-- A conjugation has a zero column wherever the Kraus matrix has a zero row. -/
theorem matrixConjLinear_apply_eq_zero_of_row_right (K : Matrix B A ℂ) (ρ : Op A) (y : B)
    {z : B} (hz : K z = 0) : matrixConjLinear K ρ y z = 0 := by
  rw [matrixConjLinear_apply]
  refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun p _ => ?_
  rw [show K z q = 0 from congrFun hz q, star_zero, mul_zero]

/-- The entry of a conjugation between two rows of the Kraus matrix that each have a single
nonzero entry. -/
theorem matrixConjLinear_apply_of_row_eq_single (K : Matrix B A ℂ) (ρ : Op A) {y z : B}
    {p q : A} {c d : ℂ} (hy : K y = Pi.single p c) (hz : K z = Pi.single q d) :
    matrixConjLinear K ρ y z = c * ρ p q * star d := by
  have hrow : ∀ q', ∑ p', K y p' * ρ p' q' * star (K z q') = c * ρ p q' * star (K z q') := by
    intro q'
    rw [Finset.sum_eq_single p (fun p' _ hp' => by rw [hy, Pi.single_eq_of_ne hp', zero_mul,
      zero_mul]) (fun h => absurd (Finset.mem_univ p) h), hy, Pi.single_eq_same]
  rw [matrixConjLinear_apply, Finset.sum_congr rfl fun q' _ => hrow q',
    Finset.sum_eq_single q (fun q' _ hq' => by rw [hz, Pi.single_eq_of_ne hq', star_zero,
      mul_zero]) (fun h => absurd (Finset.mem_univ q) h), hz, Pi.single_eq_same]

/-- **Pullback of a conjugation along rows of single entries.**  If, along `o`, the rows of the
Kraus matrix are the rows of the identity along `i` scaled by `c`, the conjugation reads back the
input operator along `i`, weighted by `star c * c`. -/
theorem matrixConjLinear_submatrix_of_row_eq_single {U : Type} (K : Matrix B A ℂ) (ρ : Op A)
    (o : U → B) (i : U → A) (c : ℂ) (hK : ∀ u, K (o u) = Pi.single (i u) c) :
    (matrixConjLinear K ρ).submatrix o o = (star c * c) • ρ.submatrix i i := by
  ext u v
  rw [Matrix.submatrix_apply, matrixConjLinear_apply_of_row_eq_single K ρ (hK u) (hK v),
    Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
  ring

/-- **Conjugation by a matrix unit** reads one diagonal input entry and prepares one output
coordinate. -/
theorem matrixConjLinear_single (y : B) (x : A) (c : ℂ) (ρ : Op A) :
    matrixConjLinear (Matrix.single y x c) ρ = Matrix.single y y (c * ρ x x * star c) := by
  simp only [matrixConjLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_single,
    Matrix.single_mul_mul_single]

end TypedLOCC
