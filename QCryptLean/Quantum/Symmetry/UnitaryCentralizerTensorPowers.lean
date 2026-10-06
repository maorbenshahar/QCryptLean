import QCryptLean.Math.SpectralTheory.HermitianCpowAnalytic
import QCryptLean.Quantum.Operators.MatrixSqrt
import QCryptLean.Quantum.Operators.Types
import QCryptLean.Quantum.TensorProducts.TensorPow
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Tensor powers of unitaries in a matrix commutant

Imaginary spectral powers of a positive definite matrix are unitary and remain
in its commutant. Analytic continuation then extends tensor-power commutation
from these unitary powers to the positive matrix itself.
-/

open Matrix Quantum.Operators Quantum.TensorProducts Math.SpectralTheory
open scoped BigOperators ComplexOrder MatrixOrder Topology

noncomputable section

namespace Quantum.Symmetry

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- An entire scalar function vanishing on the imaginary axis vanishes everywhere. -/
lemma entire_eq_zero_of_imaginary {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hzero : ∀ t : ℝ, f ((t : ℂ) * Complex.I) = 0) : f = 0 := by
  apply (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq
    analyticOnNhd_const (z₀ := 0)
  have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I)
      (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) :=
        Complex.continuous_ofReal.mul continuous_const
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact ht.frequently (Filter.Eventually.of_forall hzero).frequently

/-- Tensor powers preserve differentiability of a matrix-valued family. -/
lemma differentiable_tensorPow {d n : ℕ} {f : ℂ → Op d} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => Op.tensorPow (f z) n) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  simp only [Op.tensorPow_apply]
  exact Differentiable.fun_finsetProd fun k _ =>
    differentiable_pi.mp (differentiable_pi.mp hf _) _

/-- Applying a scalar function to a diagonal matrix preserves its commutant. -/
lemma commute_diagonal_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℂ) (f : ℂ → ℂ) {T : Matrix ι ι ℂ}
    (h : Commute (Matrix.diagonal lam) T) : Commute (Matrix.diagonal (f ∘ lam)) T := by
  ext i j
  have hij := congrFun (congrFun h.eq i) j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij ⊢
  by_cases heq : lam i = lam j
  · simp only [Function.comp_apply, heq, mul_comm]
  · have hzero : T i j = 0 := by
      apply (mul_eq_zero.mp (show (lam i - lam j) * T i j = 0 by
        rw [sub_mul, hij, mul_comm (T i j), sub_self])).resolve_left (sub_ne_zero.mpr heq)
    simp only [hzero, mul_zero, zero_mul]

/-- Every complex spectral power of a Hermitian matrix preserves its commutant. -/
lemma hermCpow_commute {d : ℕ} {A T : Op d} (hA : A.IsHermitian)
    (h : Commute A T) (z : ℂ) : Commute (hermCpow hA z) T := by
  let e := Unitary.conjStarAlgAut ℂ (Op d) hA.eigenvectorUnitary
  have hdiag : e.symm A = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    exact (congrArg e.symm hA.spectral_theorem).trans (e.symm_apply_apply _)
  have h' := h.map e.symm
  rw [hdiag] at h'
  have hp := commute_diagonal_map _ (fun x : ℂ => x ^ z) h'
  simpa only [StarAlgEquiv.apply_symm_apply, Function.comp_def, hermCpow, e] using hp.map e

/-- Commutation with constrained unitary tensor powers extends to positive definite matrices. -/
lemma commute_tensorPow_posDef_of_unitaryCentralizer {d n : ℕ} (S : Set (Op d))
    (T : Op (d ^ n))
    (hU : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      (∀ M ∈ S, Commute M (U : Op d)) → Commute (Op.tensorPow (U : Op d) n) T)
    {P : Op d} (hP : P.PosDef) (hPS : ∀ M ∈ S, Commute M P) :
    Commute (Op.tensorPow P n) T := by
  have hpow := differentiable_tensorPow (n := n)
    (hermCpow_differentiable hP.isHermitian fun i => (hP.eigenvalues_pos i).ne')
  have hdiff := (differentiable_matrix_mul_right T hpow).sub
    (differentiable_matrix_mul_left T hpow)
  ext i j
  have hz := entire_eq_zero_of_imaginary
    (differentiable_pi.mp (differentiable_pi.mp hdiff i) j) (by
      intro t
      have hu := posDef_hermCpow_mem_unitary hP (w := (t : ℂ) * Complex.I) (by simp)
      have hc := hU ⟨hermCpow hP.isHermitian ((t : ℂ) * Complex.I), hu⟩ (by
        intro M hM
        exact (hermCpow_commute hP.isHermitian (hPS M hM).symm _).symm)
      exact congrFun (congrFun (sub_eq_zero.mpr hc.eq) i) j)
  have h := congrFun hz 1
  simpa only [Pi.sub_apply, hermCpow_one, Matrix.sub_apply, Pi.zero_apply, sub_eq_zero] using h

/-- The commutant of an adjoint-closed family is adjoint-closed. -/
lemma conjTranspose_mem_commutant {d : ℕ} (S : Set (Op d))
    (hS : ∀ M ∈ S, Mᴴ ∈ S) {A : Op d} (hA : ∀ M ∈ S, Commute M A) :
    ∀ M ∈ S, Commute M Aᴴ := by
  intro M hM
  have h := congrArg Matrix.conjTranspose (hA Mᴴ (hS M hM)).eq
  simpa only [Commute, SemiconjBy, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] using h.symm

/-- Inverting an invertible matrix preserves every commutation relation. -/
lemma nonsing_inv_commute_of_isUnit {d : ℕ} {A M : Op d}
    (hA : IsUnit A) (h : Commute M A) : Commute M A⁻¹ := by
  let := hA.invertible
  simpa only [Matrix.invOf_eq_nonsing_inv] using h.invOf_right

/-- Polar decomposition extends constrained unitary tensor commutation to invertible matrices. -/
lemma commute_tensorPow_isUnit_of_unitaryCentralizer {d n : ℕ}
    (S : Set (Op d)) (hS : ∀ M ∈ S, Mᴴ ∈ S) (T : Op (d ^ n))
    (hU : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      (∀ M ∈ S, Commute M (U : Op d)) → Commute (Op.tensorPow (U : Op d) n) T)
    {A : Op d} (hA : IsUnit A) (hAS : ∀ M ∈ S, Commute M A) :
    Commute (Op.tensorPow A n) T := by
  have hgram : (Aᴴ * A).PosDef :=
    (Matrix.posSemidef_conjTranspose_mul_self A).posDef_iff_isUnit.mpr
      ((isUnit_star.mpr hA).mul hA)
  let P := CFC.sqrt (Aᴴ * A)
  have hP : P.PosDef := hgram.isStrictlyPositive.sqrt.posDef
  have hPP : P * P = Aᴴ * A := CFC.sqrt_mul_sqrt_self _ hgram.posSemidef.nonneg
  have hPS (M : Op d) (hM : M ∈ S) : Commute M P := by
    have hc := ((conjTranspose_mem_commutant S hS hAS M hM).mul_right (hAS M hM)).symm
    -- `hc : (Aᴴ * A) * M = M * (Aᴴ * A)`; reuse the library's spectral-calculus commutation lemma.
    exact (Quantum.Operators.sqrt_commute hc).symm
  let U := A * P⁻¹
  have hUmem : U ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    change (A * P⁻¹)ᴴ * (A * P⁻¹) = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hP.isHermitian.eq]
    calc P⁻¹ * Aᴴ * (A * P⁻¹) = P⁻¹ * (P * P) * P⁻¹ := by rw [hPP]; simp [mul_assoc]
      _ = (P⁻¹ * P) * (P * P⁻¹) := by simp only [mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hP.isUnit),
        Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hP.isUnit), one_mul]
  have hUP : U * P = A := by
    rw [mul_assoc, Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hP.isUnit),
      mul_one]
  rw [← hUP, Op.mul_tensorPow]
  apply Commute.mul_left
  · apply hU ⟨U, hUmem⟩
    intro M hM
    exact (hAS M hM).mul_right (nonsing_inv_commute_of_isUnit hP.isUnit (hPS M hM))
  · exact commute_tensorPow_posDef_of_unitaryCentralizer S T hU hP hPS

/-- The scalar shifts making a square matrix invertible form a dense subset of the complex plane. -/
lemma dense_isUnit_scalar_shift {d : ℕ} (A : Op d) :
    Dense (Set.ofPred fun z : ℂ => IsUnit (A + z • (1 : Op d))) := by
  have hd := Dense.sdiff_finite dense_univ (-A).finite_spectrum
  have hs : Set.univ \ spectrum ℂ (-A) = Set.ofPred (fun z : ℂ => IsUnit (A + z • (1 : Op d))) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_univ, true_and, spectrum.mem_iff, not_not,
      Algebra.algebraMap_eq_smul_one, sub_neg_eq_add, add_comm, Set.mem_ofPred_eq]
  rwa [hs] at hd

/-- Unitary tensor powers suffice inside the commutant of any adjoint-closed matrix family. -/
theorem commute_tensorPow_of_unitaryCentralizer {d n : ℕ}
    (S : Set (Op d)) (hS : ∀ M ∈ S, Mᴴ ∈ S) (T : Op (d ^ n))
    (hU : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      (∀ M ∈ S, Commute M (U : Op d)) → Commute (Op.tensorPow (U : Op d) n) T)
    (A : Op d) (hAS : ∀ M ∈ S, Commute M A) : Commute (Op.tensorPow A n) T := by
  have hp : Continuous (fun z : ℂ => Op.tensorPow (A + z • (1 : Op d)) n) :=
    (Op.continuous_tensorPow n).comp (continuous_const.add (continuous_id.smul continuous_const))
  have heq : (fun z : ℂ => Op.tensorPow (A + z • (1 : Op d)) n * T) =
      (fun z : ℂ => T * Op.tensorPow (A + z • (1 : Op d)) n) := by
    apply Continuous.ext_on (dense_isUnit_scalar_shift A)
      (hp.matrix_mul continuous_const) (continuous_const.matrix_mul hp)
    intro z hz
    exact (commute_tensorPow_isUnit_of_unitaryCentralizer S hS T hU hz fun M hM =>
      (hAS M hM).add_right ((Commute.one_right M).smul_right z)).eq
  simpa only [Commute, SemiconjBy, zero_smul, add_zero] using congrFun heq 0

end Quantum.Symmetry
