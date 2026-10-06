import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.InfoTheory.RelativeEntropy.HolevoBound.IsometricInvariance
import QCryptLean.InfoTheory.RelativeEntropy.SupportProjector

/-!
# Support Compression — compressed states and re-embedding

This file compresses density operators to the support of a reference state `σ`, using the
support isometry and projector of
`QCryptLean.InfoTheory.RelativeEntropy.SupportProjector`.  It builds the compressed
reference and test states and the re-embedding lemmas used by the pinching data-processing
proof.

## Main definitions
- `compressedSigmaOp`: the diagonal positive block of `σ` on its support
- `compressedState`: compression of a supported state to `supp(σ)`
- `compressedSigma`: the support-compressed reference state
- `compressedRhoOfKerSub`: the compression of a state whose kernel contains that of `σ`

## Main statements
- `compressedSigma_isSpectrum`: the compressed reference state is full-rank on its support
- `trace_mul_support_compression`: cyclic trace rotation turns an ambient support
  compression into a compressed trace pairing
- `trace_compressedSigma_weighted_diag_sum`: tracing against `compressedSigma σ`
  reads off the weighted compressed diagonal
- `compressedState_embed`: re-embedding a compressed state recovers the original state
- `exists_compressedSigma`: existence of a full-rank compressed reference state
- `exists_compressedRhoOfKerSub`: existence of a compressed test state under kernel containment
-/

open Quantum.Operators Quantum.TensorProducts

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace InfoTheory.RelativeEntropy

open InfoTheory.VonNeumannEntropy

/-- The diagonal positive block of `σ` on its support. -/
noncomputable def compressedSigmaOp {N : ℕ} (σ : DensityOp N) :
    Matrix (Fin (positiveSpectrumDim σ)) (Fin (positiveSpectrumDim σ)) ℂ :=
  Matrix.diagonal (fun i => (eigenvaluesOf σ (positiveSpectrumEmb σ i) : ℂ))

lemma compressedSigmaOp_apply {N : ℕ} (σ : DensityOp N)
    (i j : Fin (positiveSpectrumDim σ)) :
    compressedSigmaOp σ i j =
      if i = j then (eigenvaluesOf σ (positiveSpectrumEmb σ i) : ℂ) else 0 :=
  Matrix.diagonal_apply _ _ _

lemma compressedSigmaOp_eq {N : ℕ} (σ : DensityOp N) :
    (supportIsometry σ).conjTranspose * σ.toOp * supportIsometry σ =
      compressedSigmaOp σ := by
  set V := eigenbasisOf σ
  set D : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.diagonal (fun i => (eigenvaluesOf σ i : ℂ))
  have hVL : V.conjTranspose * V = 1 := eigenbasisOf_unitary_left σ
  have hVR : V * V.conjTranspose = 1 := eigenbasisOf_unitary_right σ
  have hconj : V * σ.toOp * V.conjTranspose = D := by
    rw [eigenbasisOf_spectral_decomp σ]
    calc
      V * (V.conjTranspose * D * V) * V.conjTranspose
          = (V * V.conjTranspose) * D * (V * V.conjTranspose) := by
              simp [Matrix.mul_assoc]
      _ = 1 * D * 1 := by simp [hVR]
      _ = D := by simp
  calc
    (supportIsometry σ).conjTranspose * σ.toOp * supportIsometry σ
        = ((V.conjTranspose * supportSelector σ).conjTranspose * σ.toOp *
            (V.conjTranspose * supportSelector σ)) := by
            rw [supportIsometry_eq_mul_supportSelector]
    _ = (supportSelector σ).conjTranspose * (V * σ.toOp * V.conjTranspose) *
            supportSelector σ := by
      simp [V, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (supportSelector σ).conjTranspose * D * supportSelector σ := by
      rw [hconj]
    _ = compressedSigmaOp σ := by
      ext i j
      rw [supportSelector_conjTranspose_mul_mul_supportSelector_apply]
      by_cases hij : i = j
      · subst hij
        simp [D, compressedSigmaOp]
      · have hneq : positiveSpectrumEmb σ i ≠ positiveSpectrumEmb σ j := by
          intro h
          exact hij ((positiveSpectrumEmb σ).injective h)
        simp [D, compressedSigmaOp, hneq, hij]

lemma compressedState_isHermitian {N : ℕ} (σ ρ : DensityOp N) :
    Matrix.IsHermitian ((supportIsometry σ).conjTranspose * ρ.toOp * supportIsometry σ) := by
  rw [Matrix.IsHermitian]
  calc
    (((supportIsometry σ).conjTranspose * ρ.toOp * supportIsometry σ).conjTranspose)
        = (supportIsometry σ).conjTranspose * ρ.toOp * supportIsometry σ := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc,
              ρ.toPosSemidefOp.toHermitianOp.isHermitian.eq]
    _ = ((supportIsometry σ).conjTranspose * ρ.toOp * supportIsometry σ) := rfl

lemma compressedState_posSemidef {N : ℕ} (σ ρ : DensityOp N) :
    ∀ x : Fin (positiveSpectrumDim σ) → ℂ,
      0 ≤ (Quantum.Operators.quadraticForm
        ((supportIsometry σ).conjTranspose * ρ.toOp * supportIsometry σ) x).re := by
  intro x
  simpa [Quantum.Operators.quadraticForm, Matrix.mul_assoc, Matrix.mulVec_mulVec,
    Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.conjTranspose_conjTranspose] using
    (density_quadraticForm_nonneg ρ ((supportIsometry σ).mulVec x))

lemma compressedState_trace_one {N : ℕ}
    (σ ρ : DensityOp N)
    (hρP : ρ.toOp * supportProjector σ = ρ.toOp) :
    (((supportIsometry σ).conjTranspose * ρ.toOp * supportIsometry σ).trace = 1) := by
  calc
    (((supportIsometry σ).conjTranspose * ρ.toOp * supportIsometry σ).trace)
        = (((supportIsometry σ).conjTranspose * (ρ.toOp * supportIsometry σ)).trace) := by
            rw [Matrix.mul_assoc]
    _ = (ρ.toOp * supportProjector σ).trace := by
            rw [Matrix.trace_mul_comm (supportIsometry σ).conjTranspose
              (ρ.toOp * supportIsometry σ)]
            simp [supportProjector, Matrix.mul_assoc]
    _ = ρ.toOp.trace := by rw [hρP]
    _ = 1 := ρ.trace_one

/-- Compress a density operator to `supp(σ)` once it is already right-supported there. -/
noncomputable def compressedState {N : ℕ}
    (σ ρ : DensityOp N)
    (hρP : ρ.toOp * supportProjector σ = ρ.toOp) :
    DensityOp (positiveSpectrumDim σ) where
  toPosSemidefOp :=
    { toHermitianOp :=
        { toOp := (supportIsometry σ).conjTranspose * ρ.toOp * supportIsometry σ
          isHermitian := compressedState_isHermitian σ ρ }
      pos_semidef := compressedState_posSemidef σ ρ }
  trace_one := compressedState_trace_one σ ρ hρP

/-- The compressed version of `σ` on its support. -/
noncomputable def compressedSigma {N : ℕ} (σ : DensityOp N) :
    DensityOp (positiveSpectrumDim σ) :=
  compressedState σ σ (sigma_mul_supportProjector σ)

lemma compressedSigma_toOp {N : ℕ} (σ : DensityOp N) :
    (compressedSigma σ).toOp = compressedSigmaOp σ := by
  exact compressedSigmaOp_eq σ

/-- Cyclically rotating the trace moves an ambient compression to the
compressed space. -/
lemma trace_mul_support_compression {N n : ℕ}
    (S : Matrix (Fin N) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    ((S * A * S.conjTranspose) * B).trace =
      (A * (S.conjTranspose * B * S)).trace := by
  calc
    ((S * A * S.conjTranspose) * B).trace
        = ((S * A) * (S.conjTranspose * B)).trace := by
            simp [Matrix.mul_assoc]
    _ = ((S.conjTranspose * B) * (S * A)).trace := by
          rw [Matrix.trace_mul_comm]
    _ = (S.conjTranspose * B * S * A).trace := by
          simp [Matrix.mul_assoc]
    _ = ((S.conjTranspose * B * S) * A).trace := by
          simp [Matrix.mul_assoc]
    _ = (A * (S.conjTranspose * B * S)).trace := by
          rw [Matrix.trace_mul_comm]

/-- Tracing against `compressedSigma σ` reads off the compressed-basis diagonal
with positive-spectrum weights. -/
lemma trace_compressedSigma_weighted_diag_sum {N : ℕ}
    (σ : DensityOp N)
    (A : Matrix (Fin (positiveSpectrumDim σ))
      (Fin (positiveSpectrumDim σ)) ℂ) :
    ((compressedSigma σ).toOp * A).trace.re =
      ∑ i, eigenvaluesOf σ (positiveSpectrumEmb σ i) * (A i i).re := by
  rw [compressedSigma_toOp]
  simp [compressedSigmaOp, Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

lemma compressedSigma_isSpectrum {N : ℕ} (σ : DensityOp N) :
    IsEigenvalueSpectrum (compressedSigma σ)
      (fun i => eigenvaluesOf σ (positiveSpectrumEmb σ i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact le_of_lt (positiveSpectrumEmb_eigenvalue_pos σ i)
  · have htrace : (compressedSigmaOp σ).trace = 1 := by
      simpa [compressedSigma_toOp] using (compressedSigma σ).trace_one
    simpa [compressedSigmaOp, Matrix.trace, Matrix.diag, Complex.ofReal_re] using
      congrArg Complex.re htrace
  · intro i
    have h_nonneg : ∀ j, 0 ≤ eigenvaluesOf σ (positiveSpectrumEmb σ j) := by
      intro j
      exact le_of_lt (positiveSpectrumEmb_eigenvalue_pos σ j)
    calc
      eigenvaluesOf σ (positiveSpectrumEmb σ i)
          ≤ ∑ j, eigenvaluesOf σ (positiveSpectrumEmb σ j) := by
              exact Finset.single_le_sum (fun j _ => h_nonneg j) (Finset.mem_univ i)
      _ = 1 := by
        have htrace : (compressedSigmaOp σ).trace = 1 := by
          simpa [compressedSigma_toOp] using (compressedSigma σ).trace_one
        simpa [compressedSigmaOp, Matrix.trace, Matrix.diag, Complex.ofReal_re] using
          congrArg Complex.re htrace
  · refine ⟨1, ?_, ?_, ?_⟩
    · simp
    · simp
    · rw [compressedSigma_toOp]
      simp [compressedSigmaOp]

lemma compressedSigma_eigenvalues_pos {N : ℕ} (σ : DensityOp N)
    (i : Fin (positiveSpectrumDim σ)) :
    0 < eigenvaluesOf (compressedSigma σ) i := by
  have h_multiset_eq := eigenvalueSpectrum_multiset_eq (compressedSigma σ)
    (fun j => eigenvaluesOf σ (positiveSpectrumEmb σ j))
    (eigenvaluesOf (compressedSigma σ))
    (compressedSigma_isSpectrum σ) (eigenvaluesOf_spec (compressedSigma σ))
  have hi_mem :
      eigenvaluesOf (compressedSigma σ) i ∈
        Finset.univ.val.map (eigenvaluesOf (compressedSigma σ)) :=
    Multiset.mem_map_of_mem (eigenvaluesOf (compressedSigma σ)) (Finset.mem_univ_val i)
  have hpos_mem :
      eigenvaluesOf (compressedSigma σ) i ∈
        Finset.univ.val.map (fun j => eigenvaluesOf σ (positiveSpectrumEmb σ j)) := by
    have : Finset.univ.val.map (fun j => eigenvaluesOf σ (positiveSpectrumEmb σ j)) =
        Finset.univ.val.map (eigenvaluesOf (compressedSigma σ)) := h_multiset_eq
    rw [this]
    exact hi_mem
  obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hpos_mem
  rw [← hj]
  exact positiveSpectrumEmb_eigenvalue_pos σ j

/-- Compress `ρ` to `supp(σ)` under kernel containment. -/
noncomputable def compressedRhoOfKerSub {N : ℕ}
    (ρ σ : DensityOp N)
    (h_ker : ∀ v : Fin N → ℂ, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    DensityOp (positiveSpectrumDim σ) :=
  compressedState σ ρ (rho_mul_supportProjector_of_ker_sub ρ σ h_ker)

lemma compressedState_embed {N : ℕ} [NeZero N]
    (σ ρ : DensityOp N)
    (hρP : ρ.toOp * supportProjector σ = ρ.toOp) :
    DensityOp.isometryEmbed (supportIsometry σ) (supportIsometry_isometry σ)
      (compressedState σ ρ hρP) = ρ := by
  apply DensityOp.ext
  calc
    supportIsometry σ *
        ((compressedState σ ρ hρP).toOp) *
        (supportIsometry σ).conjTranspose
        = supportProjector σ * ρ.toOp * supportProjector σ := by
            simp [compressedState, supportProjector, Matrix.mul_assoc]
    _ = ρ.toOp * supportProjector σ := by
      rw [supportProjector_mul_of_right_supported σ ρ hρP]
    _ = ρ.toOp := hρP

lemma compressedSigma_embed {N : ℕ} [NeZero N] (σ : DensityOp N) :
    DensityOp.isometryEmbed (supportIsometry σ) (supportIsometry_isometry σ)
      (compressedSigma σ) = σ := by
  simpa [compressedSigma] using compressedState_embed σ σ (sigma_mul_supportProjector σ)

lemma compressedRhoOfKerSub_embed {N : ℕ} [NeZero N]
    (ρ σ : DensityOp N)
    (h_ker : ∀ v : Fin N → ℂ, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    DensityOp.isometryEmbed (supportIsometry σ) (supportIsometry_isometry σ)
      (compressedRhoOfKerSub ρ σ h_ker) = ρ := by
  simpa [compressedRhoOfKerSub] using
    compressedState_embed σ ρ (rho_mul_supportProjector_of_ker_sub ρ σ h_ker)

lemma exists_compressedSigma {N : ℕ} [NeZero N] (σ : DensityOp N) :
    ∃ σs : DensityOp (positiveSpectrumDim σ),
      DensityOp.isometryEmbed (supportIsometry σ) (supportIsometry_isometry σ) σs = σ ∧
      (∀ i, 0 < eigenvaluesOf σs i) := by
  refine ⟨compressedSigma σ, compressedSigma_embed σ, ?_⟩
  intro i
  simpa using compressedSigma_eigenvalues_pos σ i

lemma exists_compressedRhoOfKerSub {N : ℕ} [NeZero N]
    (ρ σ : DensityOp N)
    (h_ker : ∀ v : Fin N → ℂ, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    ∃ ρs : DensityOp (positiveSpectrumDim σ),
      DensityOp.isometryEmbed (supportIsometry σ) (supportIsometry_isometry σ) ρs = ρ := by
  refine ⟨compressedRhoOfKerSub ρ σ h_ker, compressedRhoOfKerSub_embed ρ σ h_ker⟩

end InfoTheory.RelativeEntropy

end
