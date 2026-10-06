import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDWeightCap
import QCryptLean.InfoTheory.SmoothMinEntropy.PurifiedDistance.UhlmannVectorFamily
import QCryptLean.Quantum.TensorProducts.BlockDiagonalKetEmbedding
import QCryptLean.Quantum.Operators.RectangularKetbra

/-!
# Weight-cap vector family (Renner `thm:Hmincondrep`, main.tex:4617–4706)

This module builds the per-block ket families that represent the tensor-power
state `R = iidAEPTensorState ρ n_copies` and the weight-cap smoothed state
`ρ̄ = weightCapBlockOp` as sum-of-ketbra over the **extended** spectral label set

  `(x, z)` with `x : Fin (n^n_copies)` (block eigenvector index) and
  `z : Fin (n^n_copies + 1)` (cumulative-projector index plus the `∞` discard slot
  `Fin.last`),

so that the domination-free vector-family Uhlmann bound can be applied.  The block
eigenvector `e_x` is `blockEigenKet`; the per-block vectors are

  `v_{x,z} = √(weightCapExtendedCoefficient … x z) · e_x`,
  `w_{x,z} = √(splitCoefficient … x z') · (B_{z'} e_x)` for finite `z = z'.castSucc`,
  `w_{x,∞}  = 0`.

The extended coefficient is `splitCoefficient` on finite indices and
`weightCapDiscardCoefficient` on the `∞` slot, so the `v`-family exactly recovers
`R`'s block `Σ_x p_x e_x e_x†` via
`sum_splitCoefficient_add_discardCoefficient_eq_blockEigenvalue`.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open InfoTheory.SmoothMinEntropy
open scoped ComplexOrder BigOperators ComplexConjugate

noncomputable section

namespace InfoTheory.SmoothMinEntropy

variable {X : Type*} [Fintype X] {n : ℕ} [NeZero n]

/-! ## Generic ket-overlap helpers -/

/-- **Square-root scaling of an overlap.** For a nonnegative real `c`, scaling
both kets by `√c` multiplies their overlap by `c`. -/
lemma sqrt_smul_dag_mul {dB : ℕ} (c : ℝ) (hc : 0 ≤ c) (ψ φ : Ket dB) :
    (((Real.sqrt c : ℂ) • ψ).dag * ((Real.sqrt c : ℂ) • φ) : ℂ)
      = (c : ℂ) * (ψ.dag * φ : ℂ) := by
  rw [bra_mul_ket_eq, bra_mul_ket_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Ket.dag_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  rw [show (Real.sqrt c : ℂ) * conj (ψ.vec i) * ((Real.sqrt c : ℂ) * φ.vec i)
        = ((Real.sqrt c : ℂ) * (Real.sqrt c : ℂ)) * (conj (ψ.vec i) * φ.vec i) from by ring,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hc]

/-- **Trace of a ketbra is the overlap.** `tr(|ψ⟩⟨φ|) = ⟨φ|ψ⟩`. -/
lemma trace_ket_mul_dag {dB : ℕ} (ψ φ : Ket dB) :
    (ψ * φ.dag : Op dB).trace = (φ.dag * ψ : ℂ) := by
  rw [Matrix.trace, bra_mul_ket_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, ket_mul_bra_apply, Ket.dag_vec]
  ring

/-- For an idempotent self-adjoint operator, the diagonal matrix element equals
the squared norm of the image: `⟨ψ|B|ψ⟩ = ⟨Bψ|Bψ⟩`. -/
lemma idempotent_isHermitian_ket_inner {dB : ℕ} (B : Op dB)
    (hB : B.IsHermitian) (hidem : B * B = B) (ψ : Ket dB) :
    (ψ.dag * (B * ψ) : ℂ) = ((B * ψ).dag * (B * ψ) : ℂ) := by
  rw [Ket.dag_op_mul_of_isHermitian B hB ψ, braop_mul_ket]
  have hBB : B * (B * ψ) = B * ψ := by
    ext i
    simp only [op_mul_ket_vec, Matrix.mulVec_mulVec, hidem]
  rw [hBB]

/-! ## The block eigenvector as a ket -/

/-- The `x`-th eigenvector of the conditional block operator `(ρ.stateMap xs)^{⊗}`,
packaged as a `Ket (n^n_copies)`.  Its outer product is `blockSpectralProjector`. -/
def blockEigenKet
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) : Ket (n ^ n_copies) :=
  ⟨(((iidAEPTensorState ρ n_copies).stateMap
      xs).toPosSemidefOp.toHermitianOp.isHermitian.eigenvectorBasis x).ofLp⟩

omit [NeZero n] in
/-- The block eigenprojector is the ketbra of the block eigenvector. -/
lemma blockSpectralProjector_eq_ketbra
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    blockSpectralProjector ρ n_copies xs x
      = (blockEigenKet ρ n_copies xs x) * (blockEigenKet ρ n_copies xs x).dag := by
  ext i j
  simp only [blockSpectralProjector, blockEigenKet, Matrix.vecMulVec_apply,
    ket_mul_bra_apply, Ket.dag_vec, Pi.star_apply, RCLike.star_def]

omit [NeZero n] in
/-- **Block spectral decomposition.** The conditional block operator is the
eigenvalue-weighted sum of its rank-one block eigenprojectors. -/
lemma blockSpectralDecomposition
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (xs : Fin n_copies → X) :
    ((iidAEPTensorState ρ n_copies).stateMap xs).toOp
      = ∑ x : Fin (n ^ n_copies),
          (blockEigenvalue ρ n_copies xs x : ℂ) • blockSpectralProjector ρ n_copies xs x := by
  have h :=
    (isHermitian_eigenvectorBasis_rankOneProjectors_action
      ((iidAEPTensorState ρ n_copies).stateMap
        xs).toPosSemidefOp.toHermitianOp.isHermitian).1
  simpa only [blockEigenvalue, blockSpectralProjector] using h

/-! ## The extended split coefficients and the per-block vector families -/

/-- Renner's extended split coefficient over `z ∈ Z^n ∪ {∞}`: the finite split
coefficient `p_{x,z}(xs)` on the `castSucc` slots and the discard coefficient
`p_{x,∞}(xs)` on the `∞` slot (`Fin.last`). -/
def weightCapExtendedCoefficient
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    Fin (n ^ n_copies + 1) → ℝ :=
  Fin.lastCases (weightCapDiscardCoefficient ρ n_copies W xs x)
    (fun z' => splitCoefficient ρ n_copies W xs x z')

omit [NeZero n] in
/-- Non-negativity of the extended split coefficients. -/
lemma weightCapExtendedCoefficient_nonneg
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hmono : Monotone W.referenceEigenvalue)
    (hq_nonneg : ∀ z, 0 ≤ W.referenceEigenvalue z)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) (z : Fin (n ^ n_copies + 1)) :
    0 ≤ weightCapExtendedCoefficient ρ n_copies W xs x z := by
  refine Fin.lastCases ?_ ?_ z
  · simp only [weightCapExtendedCoefficient, Fin.lastCases_last]
    exact weightCapDiscardCoefficient_nonneg ρ n_copies W xs x
  · intro z'
    simp only [weightCapExtendedCoefficient, Fin.lastCases_castSucc]
    exact splitCoefficient_nonneg ρ n_copies W hmono hq_nonneg xs x z'

omit [NeZero n] in
/-- The extended split coefficients sum to the block eigenvalue. -/
lemma sum_weightCapExtendedCoefficient
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) :
    ∑ z : Fin (n ^ n_copies + 1), weightCapExtendedCoefficient ρ n_copies W xs x z
      = blockEigenvalue ρ n_copies xs x := by
  rw [Fin.sum_univ_castSucc]
  simp only [weightCapExtendedCoefficient, Fin.lastCases_castSucc, Fin.lastCases_last]
  exact sum_splitCoefficient_add_discardCoefficient_eq_blockEigenvalue ρ n_copies W xs x

/-- The `R`-side per-block vector `v_{x,z} = √(p_{x,z}(xs)) · e_x`, including the
`∞` discard slot (where the coefficient is `p_{x,∞}`). -/
def weightCapVBlock
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) (z : Fin (n ^ n_copies + 1)) :
    Ket (n ^ n_copies) :=
  (Real.sqrt (weightCapExtendedCoefficient ρ n_copies W xs x z) : ℂ) •
    blockEigenKet ρ n_copies xs x

/-- The `ρ̄`-side per-block vector `w_{x,z} = √(p_{x,z'}(xs)) · (B_{z'} e_x)` on the
finite `castSucc` slots, and `0` on the `∞` slot. -/
def weightCapWBlock
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (xs : Fin n_copies → X) (x : Fin (n ^ n_copies)) (z : Fin (n ^ n_copies + 1)) :
    Ket (n ^ n_copies) :=
  Fin.lastCases (0 : Ket (n ^ n_copies))
    (fun z' => (Real.sqrt (splitCoefficient ρ n_copies W xs x z') : ℂ) •
      (W.cumulativeProjector z' * blockEigenKet ρ n_copies xs x)) z

omit [NeZero n] in
/-- **R-side ketbra identity.** The extended `v`-family reproduces the conditional
block operator `(ρ.stateMap xs)^{⊗}` exactly: the `∞` slot supplies the residual
mass so that `Σ_{x,z} v_{x,z} v_{x,z}† = Σ_x p_x e_x e_x† = R_xs`. -/
lemma weightCapVBlock_sum_ketbra
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hmono : Monotone W.referenceEigenvalue)
    (hq_nonneg : ∀ z, 0 ≤ W.referenceEigenvalue z)
    (xs : Fin n_copies → X) :
    ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies + 1),
        (weightCapVBlock ρ n_copies W xs x z) * (weightCapVBlock ρ n_copies W xs x z).dag
      = ((iidAEPTensorState ρ n_copies).stateMap xs).toOp := by
  rw [blockSpectralDecomposition ρ n_copies xs]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [blockSpectralProjector_eq_ketbra, ← sum_weightCapExtendedCoefficient ρ n_copies W xs x,
    Complex.ofReal_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [weightCapVBlock,
    sqrt_smul_ketbra _ (weightCapExtendedCoefficient_nonneg ρ n_copies W hmono hq_nonneg xs x z)]

omit [NeZero n] in
/-- **ρ̄-side ketbra identity.** The extended `w`-family reproduces the weight-cap
block `weightCapBlockOp` exactly: the finite slots give
`Σ_{x,z'} p_{x,z'} (B_{z'} e_x)(B_{z'} e_x)† = Σ_{x,z'} p_{x,z'} B_{z'}|x⟩⟨x|B_{z'}`
(using `B_z† = B_z`), and the `∞` slot is `0`. -/
lemma weightCapWBlock_sum_ketbra
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hBherm : ∀ z : Fin (n ^ n_copies), (W.cumulativeProjector z)ᴴ = W.cumulativeProjector z)
    (hmono : Monotone W.referenceEigenvalue)
    (hq_nonneg : ∀ z, 0 ≤ W.referenceEigenvalue z)
    (xs : Fin n_copies → X) :
    ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies + 1),
        (weightCapWBlock ρ n_copies W xs x z) * (weightCapWBlock ρ n_copies W xs x z).dag
      = weightCapBlockOp ρ n_copies W xs := by
  unfold weightCapBlockOp
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Fin.sum_univ_castSucc]
  have hlast : (weightCapWBlock ρ n_copies W xs x (Fin.last _)) *
      (weightCapWBlock ρ n_copies W xs x (Fin.last _)).dag = 0 := by
    simp only [weightCapWBlock, Fin.lastCases_last]
    ext i j; simp
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl (fun z' _ => ?_)
  rw [weightCapWBlock, Fin.lastCases_castSucc,
    sqrt_smul_ketbra _ (splitCoefficient_nonneg ρ n_copies W hmono hq_nonneg xs x z'),
    ketbra_eq_rect_conj_of_vec_eq_mulVec (W.cumulativeProjector z')
      (blockEigenKet ρ n_copies xs x) _ rfl,
    ← blockSpectralProjector_eq_ketbra, hBherm z']

omit [NeZero n] in
/-- **Overlap identity.** The family overlap collapses to the (complex) trace of
the weight-cap block: the `∞` slot contributes `0` (since `w_{x,∞}=0`) and each
finite slot contributes `p_{x,z'} ⟨x|B_{z'}|x⟩ = tr(p_{x,z'} B_{z'}|x⟩⟨x|B_{z'})`,
using `B_z† = B_z` and `B_z·B_z = B_z`. -/
lemma weightCapVBlock_dag_mul_weightCapWBlock_sum
    (ρ : CQState X n) (n_copies : ℕ) [NeZero (n ^ n_copies)]
    (W : IIDAEPSpectralWitness X n n_copies)
    (hBherm : ∀ z : Fin (n ^ n_copies), (W.cumulativeProjector z)ᴴ = W.cumulativeProjector z)
    (hBidem : ∀ z : Fin (n ^ n_copies),
      W.cumulativeProjector z * W.cumulativeProjector z = W.cumulativeProjector z)
    (hmono : Monotone W.referenceEigenvalue)
    (hq_nonneg : ∀ z, 0 ≤ W.referenceEigenvalue z)
    (xs : Fin n_copies → X) :
    ∑ x : Fin (n ^ n_copies), ∑ z : Fin (n ^ n_copies + 1),
        (weightCapVBlock ρ n_copies W xs x z).dag * (weightCapWBlock ρ n_copies W xs x z)
      = (weightCapBlockOp ρ n_copies W xs).trace := by
  rw [← weightCapWBlock_sum_ketbra ρ n_copies W hBherm hmono hq_nonneg xs, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [trace_ket_mul_dag]
  refine Fin.lastCases ?_ ?_ z
  · simp [weightCapWBlock, Fin.lastCases_last, bra_mul_ket_eq]
  · intro z'
    have hsplit_nn := splitCoefficient_nonneg ρ n_copies W hmono hq_nonneg xs x z'
    rw [weightCapVBlock, weightCapWBlock, Fin.lastCases_castSucc]
    simp only [weightCapExtendedCoefficient, Fin.lastCases_castSucc]
    rw [sqrt_smul_dag_mul _ hsplit_nn, sqrt_smul_dag_mul _ hsplit_nn,
      idempotent_isHermitian_ket_inner (W.cumulativeProjector z') (hBherm z') (hBidem z')
        (blockEigenKet ρ n_copies xs x)]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
