import QCryptLean.Quantum.TensorProducts.TensorFamilyPi

/-!
# The recursive tensor product of operators of varying dimension

For `dim : Fin k → ℕ` and operators `f j : Op (dim j)`,
`Quantum.TensorProducts.Op.tensorProdFin k dim f` is the tensor product
`f 0 ⊗ f 1 ⊗ ⋯ ⊗ f (k - 1)`, an operator on `∏ j, dim j` dimensions. It is defined by the
recursion `f 0 ⊗ (f 1 ⊗ ⋯)` through `Op.tensor` and the dimension cast
`Fin.prod_univ_succ`, so **factor `0` is the first (high-digit) tensor factor**.
`Quantum.Operators.DensityOp.tensorProdFin` is the same recursion on density operators.

This is the opposite factor order to `tensorFamilyPi` and `tensorFamily`, whose factor `0` is the
low digit. The two conventions differ exactly by reversing the family and casting the dimension
(`Op.tensorProdFin_eq_tensorFamilyPi`, and `Op.tensorProdFin_const` for equal dimensions); the
coordinates are not definitionally identified.

## Main statements

* `Op.tensorProdFin_one`, `Op.tensorProdFin_mul`, `Op.tensorProdFin_conjTranspose`,
  `Op.tensorProdFin_smul`, `Op.tensorProdFin_sum`: unit, multiplicativity, adjoints and
  multilinearity.
* `Op.tensorProdFin_trace`, `Op.tensorProdFin_diag_congr`, `Op.tensorProdFin_isDiag`: traces and
  diagonals.
* `Matrix.IsHermitian.tensorProdFin`, `Matrix.PosSemidef.tensorProdFin`,
  `Matrix.PosDef.tensorProdFin`: positivity.
* `Op.tensorProdFin_eq_tensorFamilyPi`: the product is the tensor product of the reversed family;
  `Op.tensorProdFin_const`: with equal dimensions, of the reversed `tensorFamily`.
* `Quantum.Operators.DensityOp.tensorProdFin_toOp`: the state and operator products agree.
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.TensorProducts

/-! ## The definition and its algebra -/

/-- The tensor product `f 0 ⊗ f 1 ⊗ ⋯ ⊗ f (k - 1)` of operators of dimensions `dim j`, an operator
on `∏ j, dim j` dimensions. Factor `0` is the first (high-digit) tensor factor; over no factors
the product is the identity of the one-dimensional register. -/
def Op.tensorProdFin (k : ℕ) (dim : Fin k → ℕ) (f : ∀ j, Op (dim j)) : Op (∏ j, dim j) :=
  match k, dim, f with
  | 0, _, _ => Op.castDim (by simp) (1 : Op 1)
  | k + 1, dim, f =>
      Op.castDim (Fin.prod_univ_succ dim).symm
        (Op.tensor (f 0) (Op.tensorProdFin k (fun j => dim j.succ) (fun j => f j.succ)))

theorem Op.tensorProdFin_zero (dim : Fin 0 → ℕ) (f : ∀ j, Op (dim j)) :
    Op.tensorProdFin 0 dim f = Op.castDim (by simp) (1 : Op 1) := rfl

/-- The defining recursion: factor `0` is the first tensor factor. -/
theorem Op.tensorProdFin_succ (k : ℕ) (dim : Fin (k + 1) → ℕ) (f : ∀ j, Op (dim j)) :
    Op.tensorProdFin (k + 1) dim f =
      Op.castDim (Fin.prod_univ_succ dim).symm
        (Op.tensor (f 0) (Op.tensorProdFin k (fun j => dim j.succ) (fun j => f j.succ))) := rfl

/-- The tensor product of identities is the identity. -/
@[simp] theorem Op.tensorProdFin_one (k : ℕ) (dim : Fin k → ℕ) :
    Op.tensorProdFin k dim (fun j => (1 : Op (dim j))) = 1 := by
  induction k with
  | zero => rw [Op.tensorProdFin_zero, Op.castDim_one]
  | succ k ih =>
    rw [Op.tensorProdFin_succ, ih (fun j => dim j.succ), Op.tensor_one, Op.castDim_one]

/-- The tensor product is multiplicative factor by factor. -/
theorem Op.tensorProdFin_mul (k : ℕ) (dim : Fin k → ℕ) (A B : ∀ j, Op (dim j)) :
    Op.tensorProdFin k dim (fun j => A j * B j) =
      Op.tensorProdFin k dim A * Op.tensorProdFin k dim B := by
  induction k with
  | zero => rw [Op.tensorProdFin_zero, Op.tensorProdFin_zero, Op.tensorProdFin_zero,
      Op.castDim_mul, Matrix.one_mul]
  | succ k ih =>
    rw [Op.tensorProdFin_succ, Op.tensorProdFin_succ, Op.tensorProdFin_succ,
      ih (fun j => dim j.succ) (fun j => A j.succ) (fun j => B j.succ), Op.castDim_mul,
      Op.tensor_mul]

/-- The tensor product commutes with the adjoint: `(⊗ⱼ Aⱼ)ᴴ = ⊗ⱼ Aⱼᴴ`. -/
theorem Op.tensorProdFin_conjTranspose (k : ℕ) (dim : Fin k → ℕ) (A : ∀ j, Op (dim j)) :
    (Op.tensorProdFin k dim A)ᴴ = Op.tensorProdFin k dim (fun j => (A j)ᴴ) := by
  induction k with
  | zero => rw [Op.tensorProdFin_zero, Op.tensorProdFin_zero, Op.castDim_conjTranspose,
      conjTranspose_one]
  | succ k ih =>
    rw [Op.tensorProdFin_succ, Op.tensorProdFin_succ, Op.castDim_conjTranspose,
      Op.tensor_conjTranspose, ih (fun j => dim j.succ) (fun j => A j.succ)]

/-- Scalars on the factors multiply: `⊗ⱼ (cⱼ Aⱼ) = (∏ⱼ cⱼ) ⊗ⱼ Aⱼ`. -/
theorem Op.tensorProdFin_smul (k : ℕ) (dim : Fin k → ℕ) (c : Fin k → ℂ) (A : ∀ j, Op (dim j)) :
    Op.tensorProdFin k dim (fun j => c j • A j) = (∏ j, c j) • Op.tensorProdFin k dim A := by
  induction k with
  | zero => simp [Op.tensorProdFin_zero]
  | succ k ih =>
    rw [Op.tensorProdFin_succ, Op.tensorProdFin_succ,
      ih (fun j => dim j.succ) (fun j => c j.succ) (fun j => A j.succ), ← tensorRect_square,
      tensorRect_smul_left, tensorRect_smul_right, smul_smul, Op.castDim_smul,
      Fin.prod_univ_succ c, tensorRect_square]

/-- **Multilinearity.** The tensor product of sums is the sum, over all choices of one summand per
factor, of the tensor products. -/
theorem Op.tensorProdFin_sum (k : ℕ) (dim : Fin k → ℕ) {ι : Fin k → Type*}
    [∀ j, Fintype (ι j)] (F : ∀ j, ι j → Op (dim j)) :
    Op.tensorProdFin k dim (fun j => ∑ s, F j s) =
      ∑ g : ∀ j, ι j, Op.tensorProdFin k dim (fun j => F j (g j)) := by
  induction k with
  | zero => simp [Op.tensorProdFin_zero]
  | succ k ih =>
    rw [← (Fin.consEquiv ι).sum_comp, Fintype.sum_prod_type, Op.tensorProdFin_succ,
      ih (fun j => dim j.succ) (fun j => F j.succ), ← tensorRect_square, ← tensorRect_sum_left,
      Op.castDim_sum_univ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← tensorRect_sum_right, Op.castDim_sum_univ]
    exact Finset.sum_congr rfl fun g _ => rfl

/-- The trace of a tensor product is the product of the traces. -/
theorem Op.tensorProdFin_trace (k : ℕ) (dim : Fin k → ℕ) (A : ∀ j, Op (dim j)) :
    (Op.tensorProdFin k dim A).trace = ∏ j, (A j).trace := by
  induction k with
  | zero => simp [Op.tensorProdFin_zero, Op.castDim_trace]
  | succ k ih =>
    rw [Op.tensorProdFin_succ, Op.castDim_trace, Op.trace_tensor,
      ih (fun j => dim j.succ) (fun j => A j.succ), Fin.prod_univ_succ]

/-- The diagonal of a tensor product depends only on the diagonals of the factors. -/
theorem Op.tensorProdFin_diag_congr (k : ℕ) (dim : Fin k → ℕ) {A B : ∀ j, Op (dim j)}
    (h : ∀ j, (A j).diag = (B j).diag) :
    (Op.tensorProdFin k dim A).diag = (Op.tensorProdFin k dim B).diag := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    simp only [diag_apply, Op.tensorProdFin_succ, Op.castDim_apply, ← tensorRect_square,
      tensorRect_apply]
    congr 1
    · exact congrFun (h 0) _
    · exact congrFun (ih (fun j => dim j.succ) fun j => h j.succ) _

/-- `Op.tensor` of diagonal operators is diagonal. -/
theorem Op.tensor_isDiag {n m : ℕ} {A : Op n} {B : Op m} (hA : A.IsDiag) (hB : B.IsDiag) :
    (Op.tensor A B).IsDiag := by
  unfold Op.tensor
  rw [reindex_apply]
  exact (hA.kronecker hB).submatrix finProdFinEquiv.symm.injective

/-- A dimension cast preserves diagonality. -/
theorem Op.castDim_isDiag {n m : ℕ} (h : n = m) {A : Op n} (hA : A.IsDiag) :
    (Op.castDim h A).IsDiag := by
  subst h; exact hA

/-- The tensor product of diagonal operators is diagonal. -/
theorem Op.tensorProdFin_isDiag (k : ℕ) (dim : Fin k → ℕ) (A : ∀ j, Op (dim j))
    (hA : ∀ j, (A j).IsDiag) : (Op.tensorProdFin k dim A).IsDiag := by
  induction k with
  | zero => rw [Op.tensorProdFin_zero]; exact Op.castDim_isDiag _ isDiag_one
  | succ k ih =>
    rw [Op.tensorProdFin_succ]
    exact Op.castDim_isDiag _
      (Op.tensor_isDiag (hA 0) (ih (fun j => dim j.succ) (fun j => A j.succ) fun j => hA j.succ))

/-! ## Positivity -/

/-- The tensor product of Hermitian operators is Hermitian. -/
theorem _root_.Matrix.IsHermitian.tensorProdFin {k : ℕ} {dim : Fin k → ℕ} {A : ∀ j, Op (dim j)}
    (hA : ∀ j, (A j).IsHermitian) : (Op.tensorProdFin k dim A).IsHermitian := by
  rw [IsHermitian, Op.tensorProdFin_conjTranspose]
  exact congrArg _ (funext fun j => (hA j).eq)

/-- The tensor product of positive-semidefinite operators is positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.tensorProdFin {k : ℕ} {dim : Fin k → ℕ} {A : ∀ j, Op (dim j)}
    (hA : ∀ j, (A j).PosSemidef) : (Op.tensorProdFin k dim A).PosSemidef := by
  induction k with
  | zero => rw [Op.tensorProdFin_zero]; exact Op.castDim_posSemidef _ _ PosSemidef.one
  | succ k ih =>
    rw [Op.tensorProdFin_succ]
    exact Op.castDim_posSemidef _ _
      (((hA 0).kronecker (ih fun j => hA j.succ)).submatrix finProdFinEquiv.symm)

/-- The tensor product of positive-definite operators is positive definite: it is positive
semidefinite, and invertible with inverse the tensor product of the inverses. -/
theorem _root_.Matrix.PosDef.tensorProdFin {k : ℕ} {dim : Fin k → ℕ} {A : ∀ j, Op (dim j)}
    (hA : ∀ j, (A j).PosDef) : (Op.tensorProdFin k dim A).PosDef := by
  refine (PosSemidef.tensorProdFin fun j => (hA j).posSemidef).posDef_iff_isUnit.mpr ?_
  have hinv : ∀ j, A j * (A j)⁻¹ = 1 := fun j =>
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (hA j).isUnit)
  have hmul : Op.tensorProdFin k dim A * Op.tensorProdFin k dim (fun j => (A j)⁻¹) = 1 := by
    rw [← Op.tensorProdFin_mul]
    simp only [hinv, Op.tensorProdFin_one]
  exact (isUnit_iff_isUnit_det _).mpr (IsUnit.of_mul_eq_one _ (by rw [← det_mul, hmul, det_one]))

/-! ## The reversed tensor family -/

/-- Evaluating a family of operators at equal indices agrees up to the induced dimension cast. -/
private theorem apply_eq_castDim {m : ℕ} {dim : Fin m → ℕ} (f : ∀ j, Op (dim j)) {i i' : Fin m}
    (h : i = i') : f i = Op.castDim (congrArg dim h).symm (f i') := by
  subst h; rfl

/-- Reindexing a family of operators along equal index maps casts its tensor product. -/
private theorem tensorFamilyPi_comp_eq {k m : ℕ} {dim : Fin m → ℕ} (f : ∀ j, Op (dim j))
    {σ τ : Fin k → Fin m} (h : σ = τ) :
    tensorFamilyPi (fun j => f (σ j)) =
      Op.castDim (congrArg (fun σ : Fin k → Fin m => ∏ j, dim (σ j)) h).symm
        (tensorFamilyPi fun j => f (τ j)) := by
  subst h; rfl

private theorem tensorFamilyPi_rev_castSucc {k : ℕ} {dim : Fin (k + 1) → ℕ}
    (f : ∀ j, Op (dim j)) :
    tensorFamilyPi (fun j : Fin k => f (Fin.rev j.castSucc)) =
      Op.castDim (by simp only [Fin.rev_castSucc])
        (tensorFamilyPi fun j : Fin k => f (Fin.rev j).succ) :=
  tensorFamilyPi_comp_eq f (funext Fin.rev_castSucc)

/-- **The recursive product is the tensor product of the reversed family.** `Op.tensorProdFin`
puts factor `0` on the high digit and `tensorFamilyPi` puts it on the low digit, so reversing the
family converts one convention into the other, up to the cast
`∏ j, dim (Fin.rev j) = ∏ j, dim j`. -/
theorem Op.tensorProdFin_eq_tensorFamilyPi (k : ℕ) (dim : Fin k → ℕ) (f : ∀ j, Op (dim j)) :
    Op.tensorProdFin k dim f =
      Op.castDim (Fintype.prod_equiv Fin.revPerm _ _ fun _ => rfl)
        (tensorFamilyPi fun j => f (Fin.rev j)) := by
  induction k with
  | zero =>
    rw [Op.tensorProdFin_zero, Op.castDim_one,
      Subsingleton.elim (fun j => f (Fin.rev j)) fun _ => 1]
    have hone : tensorFamilyPi (fun j : Fin 0 => (1 : Op (dim (Fin.rev j)))) = 1 :=
      tensorFamilyPi_one
    exact ((congrArg (Op.castDim _) hone).trans (Op.castDim_one _)).symm
  | succ k ih =>
    change Op.tensorProdFin (k + 1) dim f =
      Op.castDim (show (∏ j, dim (Fin.rev j)) = ∏ j, dim j from
        Fintype.prod_equiv Fin.revPerm _ _ fun _ => rfl)
          (tensorFamilyPi (a := fun j => dim (Fin.rev j))
            (b := fun j => dim (Fin.rev j)) fun j => f (Fin.rev j))
    rw [Op.tensorProdFin_succ]
    have htail := ih (fun j => dim j.succ) (fun j => f j.succ)
    rw [tensorFamilyPi_castSucc, tensorRect_square,
      ← Op.castDim_eq_reindex_finCongr, apply_eq_castDim f (Fin.rev_last k)]
    rw [htail]
    conv_rhs =>
      arg 2
      arg 2
      arg 2
      tactic => exact tensorFamilyPi_rev_castSucc f
    simp only [Op.tensor_castDim_right, Op.castDim_trans]
    conv_rhs =>
      arg 2
      tactic => exact Op.tensor_castDim_left _ _ _
    simp only [Op.castDim_trans]
    rfl

/-! ## Equal dimensions -/

/-- **The constant-dimension case is a reversed tensor family.** With every dimension equal to `d`,
the product `f 0 ⊗ ⋯ ⊗ f (k - 1)` is `tensorFamily` of the reversed family (which puts `f 0` on
the high digit), up to the cast `d ^ k = ∏ j, d`. -/
theorem Op.tensorProdFin_const {d : ℕ} (k : ℕ) (f : Fin k → Op d) :
    Op.tensorProdFin k (fun _ => d) f =
      Op.castDim (Fin.prod_const k d).symm (tensorFamily fun j => f (Fin.rev j)) := by
  induction k with
  | zero => simp +instances only [Op.tensorProdFin_zero, tensorFamily_zero, Op.castDim_one]
  | succ k ih =>
    rw [Op.tensorProdFin_succ, ih, tensorFamily_comp_rev_castSucc, tensorRect_square,
      ← Op.castDim_eq_reindex_finCongr, Op.tensor_castDim_right, Op.castDim_trans,
      Op.castDim_trans]

end Quantum.TensorProducts

namespace Quantum.Operators

open Quantum.TensorProducts

/-- The tensor product `f 0 ⊗ f 1 ⊗ ⋯ ⊗ f (k - 1)` of density operators of dimensions `dim j`, a
density operator on `∏ j, dim j` dimensions, by the recursion of `Op.tensorProdFin`: factor `0`
is the first (high-digit) tensor factor, and over no factors the product is the trivial state. -/
def DensityOp.tensorProdFin (k : ℕ) (dim : Fin k → ℕ) (f : ∀ j, DensityOp (dim j)) :
    DensityOp (∏ j, dim j) :=
  match k, dim, f with
  | 0, _, _ => DensityOp.castDim (by simp) DensityOp.trivial
  | k + 1, dim, f =>
      DensityOp.castDim (Fin.prod_univ_succ dim).symm
        ((f 0).tensor (DensityOp.tensorProdFin k (fun j => dim j.succ) (fun j => f j.succ)))

/-- The trivial one-dimensional state is the identity operator. -/
theorem DensityOp.trivial_toOp : DensityOp.trivial.toOp = (1 : Op 1) := by
  ext i j; fin_cases i; fin_cases j
  simp [DensityOp.trivial]

/-- The underlying operator of the tensor product of two states is the tensor product of their
operators. -/
theorem DensityOp.tensor_toOp {n m : ℕ} (ρ : DensityOp n) (σ : DensityOp m) :
    (ρ.tensor σ).toOp = Op.tensor ρ.toOp σ.toOp := rfl

/-- The underlying operator of `DensityOp.tensorProdFin` is the operator tensor product. -/
theorem DensityOp.tensorProdFin_toOp {k : ℕ} (dim : Fin k → ℕ) (f : ∀ j, DensityOp (dim j)) :
    (DensityOp.tensorProdFin k dim f).toOp = Op.tensorProdFin k dim (fun j => (f j).toOp) := by
  induction k with
  | zero =>
    rw [Op.tensorProdFin_zero]
    change (DensityOp.castDim _ DensityOp.trivial).toOp = _
    rw [densityOp_castDim_toOp, DensityOp.trivial_toOp]
  | succ k ih =>
    rw [Op.tensorProdFin_succ]
    change (DensityOp.castDim _ ((f 0).tensor
        (DensityOp.tensorProdFin k (fun j => dim j.succ) (fun j => f j.succ)))).toOp = _
    rw [densityOp_castDim_toOp, DensityOp.tensor_toOp, ih (fun j => dim j.succ) (fun j => f j.succ)]

end Quantum.Operators

end
