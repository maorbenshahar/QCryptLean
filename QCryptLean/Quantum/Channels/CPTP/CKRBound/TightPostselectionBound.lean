import QCryptLean.Quantum.Channels.CPTP.CKRBound.PostselectionBound
import QCryptLean.Quantum.Channels.CPTP.CKRBound.CovarianceBundles
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction
import QCryptLean.Quantum.Metrics.TraceNormHoelder
import QCryptLean.Quantum.Metrics.KitaevWatrous
import QCryptLean.Quantum.TensorProducts.ProjectiveConditioning

/-!
# Tight CKR Postselection Bound — `(n+1)^3` / `C(n+3,3)` for `PermutationCovariantTight` maps

The tight-path CKR postselection theorem for `PermutationCovariantTight` maps
`Δ : End((ℂ^4)^⊗n) → End(H')`. Combining the Kitaev-Watrous square-ancilla diamond-norm
reduction (no factor-of-2 loss), the symmetric-support reduction (`factors_through_sym`),
and substate extraction on the symmetric subspace `Sym^n(ℂ^4)` gives

    `‖Δ‖_◇ ≤ C(n+3, 3) · ‖(Δ ⊗ id_R)(τ)‖₁ ≤ (n+1)^3 · ‖(Δ ⊗ id_R)(τ)‖₁`.

The exponent `d - 1 = 3` (vs the standard `d² - 1 = 15`) is available because
`PermutationCovariantTight` supplies `factors_through_sym`, restricting the relevant
operators to `Sym^n(ℂ^4)` of dimension `C(n+3, 3)`.

The two tight bounds have no twin in the generic CKR channel-bound layer and are kept for
reuse. Declarations here retain the QKD BB84 engine namespace.

## Main statements
- `diamondNorm_le_of_psd_bound_no_sym`: diamond norm ≤ B via Kitaev-Watrous
- `diamondNorm_le_of_psd_bound_tight`: diamond norm ≤ B from PSD bound (tight path)
- `diamondNorm_le_symDim_mul_ckrTraceNorm_tight`: tight CKR core bound with `C(n+3,3)`
- `ckr_postselection_tight`: tight CKR postselection theorem with `(n+1)^3`

## References
- Christandl-Konig-Renner (2009) "Postselection technique", Theorem 1
- Watrous "Theory of Quantum Information", Theorem 3.46; Kitaev-Watrous Proposition 3.47
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Metrics Quantum.Channels
open Quantum.Symmetry InfoTheory.DeFinetti
open QKD.BB84.Engine InfoTheory.VonNeumannEntropy Math.ClassicalEntropy
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

/-- If Δ factors through P (i.e. Δ(P·X·P) = Δ(X) for all X), then
    mapTensorId Δ ((P ⊗ I) * ρ * (P ⊗ I)) = mapTensorId Δ ρ.

    The proof uses entry-level calculation: the sandwich by (P ⊗ I) replaces each
    basis element E_{ij} in the Δ argument with P·E_{ij}·P, then the factoring
    hypothesis gives Δ(P·E_{ij}·P) = Δ(E_{ij}).

    Concretely, ((P⊗I)*ρ*(P⊗I))_{(i,s),(j,t)} = ∑_{a,b} P_{ia} ρ_{(a,s),(b,t)} P_{bj},
    so mapTensorId Δ ((P⊗I)*ρ*(P⊗I)) involves ∑_{i,j} Δ(E_{ij}) * ∑_{a,b} P_{ia}ρP_{bj}
    = ∑_{a,b} Δ(P·E_{ab}·P) * ρ_{(a,s),(b,t)} = ∑_{a,b} Δ(E_{ab}) * ρ by factoring. -/
lemma mapTensorId_sandwich_factors {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (Δ : Op n →ₗ[ℂ] Op m)
    (P : Op n)
    (h_factors : ∀ (A : Op n), Δ (P * A * P) = Δ A)
    (ρ : Op (n * k)) :
    mapTensorId Δ (Op.tensor P (1 : Op k) * ρ * Op.tensor P (1 : Op k)) =
      mapTensorId Δ ρ := by
  ext p q
  rw [Quantum.Channels.mapTensorId_apply_eq_apply_block,
    Quantum.Channels.mapTensorId_apply_eq_apply_block,
    Quantum.Channels.tensor_sandwich_block, h_factors]

/-- **Symmetric support reduction**: For a permutation-covariant map that factors through
    the symmetric projector, if the PSD bound holds for operators with symmetric support,
    it holds for all PSD operators.

    The key identity: if Δ(P·X·P) = Δ(X) for P = symmetricProjector, then for any PSD ρ,
    define ρ' = (P⊗I)ρ(P⊗I). Then:
    - ρ' is PSD (conjugation by P⊗I preserves PSD)
    - Tr(ρ') ≤ Tr(ρ) (P is a projector, so (P⊗I) contracts trace)
    - partialTraceB(ρ') has symmetric support
    - mapTensorId Δ ρ' = mapTensorId Δ ρ (because Δ factors through P) -/
lemma psd_bound_with_sym_of_factors {n dimOut : ℕ} [NeZero n] [NeZero dimOut]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (h_factors : ∀ (A : Op (4 ^ n)),
      Δ (symmetricProjector 4 n * A * symmetricProjector 4 n) = Δ A)
    (B : ℝ)
    (h_psd_bound : ∀ (ρ : Op (4 ^ n * (4 ^ n))),
      Matrix.PosSemidef ρ → ρ.trace.re ≤ 1 →
      symmetricProjector 4 n * partialTraceB ρ = partialTraceB ρ →
      traceNorm (mapTensorId Δ ρ) ≤ B) :
    ∀ (ρ : Op (4 ^ n * (4 ^ n))),
      Matrix.PosSemidef ρ → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Δ ρ) ≤ B := by
  intro ρ hρ_psd hρ_trace
  set P := symmetricProjector 4 n with hP_def
  set PI := Op.tensor P (1 : Op (4 ^ n)) with hPI_def
  set ρ' := PI * ρ * PI with hρ'_def
  have hP_idem : P * P = P := (symmetricProjector_is_projector 4 n).1
  have hP_herm : P† = P := (symmetricProjector_is_projector 4 n).2
  have hPI_idem : PI * PI = PI := by
    rw [hPI_def, Op.tensor_mul, hP_idem, mul_one]
  have hPI_herm : PI† = PI := by
    simp only [hPI_def, Op.tensor_conjTranspose, hP_herm, conjTranspose_one]
  -- mapTensorId Δ ρ' = mapTensorId Δ ρ because Δ factors through P
  rw [← mapTensorId_sandwich_factors Δ P h_factors ρ]
  apply h_psd_bound ρ'
  · -- ρ' is PSD
    rw [hρ'_def, show PI * ρ * PI = PI† * ρ * PI from by rw [hPI_herm]]
    exact hρ_psd.conjTranspose_mul_mul_same PI
  · -- Tr(ρ').re ≤ 1: sandwich by projector contracts trace
    rw [hρ'_def]
    exact (trace_re_projector_sandwich_le (P := PI) (M := ρ)
      hPI_idem hPI_herm hρ_psd).trans hρ_trace
  · -- Symmetric support: P * partialTraceB ρ' = partialTraceB ρ'
    rw [hρ'_def, partialTraceB_sandwich_tensor_one P P ρ]
    simp only [← Matrix.mul_assoc]
    rw [hP_idem]

/-- **Kitaev-Watrous reduction**: For Hermiticity-preserving maps, the diamond norm
    is bounded by B when ‖mapTensorId Δ ρ‖₁ ≤ B for all PSD ρ with Tr(ρ) ≤ 1.

    Uses the Kitaev-Watrous square-ancilla PSD maximization theorem (Watrous TQI
    Prop 3.47) to avoid the factor-of-2 loss from Cartesian decomposition. -/
lemma diamondNorm_le_of_psd_bound_no_sym {n m : ℕ} [NeZero n] [NeZero m]
    [NeZero (n * n)] [NeZero (m * n)]
    (Δ : Op n →ₗ[ℂ] Op m)
    (hΔ_conj : ∀ M : Op n, Δ M.conjTranspose = (Δ M).conjTranspose)
    (B : ℝ)
    (h_psd : ∀ (ρ : Op (n * n)),
      Matrix.PosSemidef ρ → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Δ ρ) ≤ B) :
    diamondNorm Δ ≤ B := by
  have hB : 0 ≤ B := by
    have h0 : traceNorm (mapTensorId Δ 0) ≤ B :=
      h_psd 0 Matrix.PosSemidef.zero (by simp)
    simpa [mapTensorId_zero, traceNorm_zero] using h0
  -- Unfold diamondNorm and use csSup_le
  unfold diamondNorm
  apply csSup_le
  · -- Set is nonempty (contains 0)
    exact ⟨0, 0, by rw [traceNorm_zero]; exact zero_le_one,
      by rw [mapTensorId_zero, traceNorm_zero]⟩
  · -- Every element of the set is ≤ B via Kitaev-Watrous
    rintro t ⟨W, hW_norm, rfl⟩
    exact Quantum.Metrics.KitaevWatrous.kw_nonhermitian_reduction Δ B hB hΔ_conj h_psd W hW_norm

/-- A normalized square-ancilla state bound controls the diamond norm of an
adjoint-preserving map without a dimension or factor-of-two loss. -/
lemma diamondNorm_le_of_density_bound
    {n m : ℕ} [NeZero n] [NeZero m]
    [NeZero (n * n)] [NeZero (m * n)]
    (Δ : Op n →ₗ[ℂ] Op m)
    (hΔ : ∀ M : Op n, Δ M.conjTranspose = (Δ M).conjTranspose)
    (B : ℝ) (hB : 0 ≤ B)
    (hρ : ∀ ρ : DensityOp (n * n),
      traceNorm (mapTensorId (k := n) Δ ρ.toOp) ≤ B) :
    diamondNorm Δ ≤ B := by
  apply diamondNorm_le_of_psd_bound_no_sym Δ hΔ B
  intro A hA htr
  by_cases hz : A.trace = 0
  · rw [hA.trace_eq_zero_iff.mp hz, mapTensorId_zero, traceNorm_zero]
    exact hB
  · have hnonneg := hA.trace_nonneg
    rw [Complex.le_def] at hnonneg
    have hpos : 0 < A.trace.re :=
      lt_of_le_of_ne hnonneg.1 (fun he => hz (Complex.ext he.symm hnonneg.2.symm))
    obtain ⟨ρ, hρeq⟩ := densityOp_of_psd_pos_trace A hA hpos
    have hscale : A = A.trace • ρ.toOp := by
      rw [hρeq, smul_smul, one_div, mul_inv_cancel₀ hz, one_smul]
    have hnorm : ‖A.trace‖ = A.trace.re := by
      have hre : (A.trace.re : ℂ) = A.trace := Complex.ext rfl hnonneg.2
      calc
        ‖A.trace‖ = ‖(A.trace.re : ℂ)‖ := congrArg norm hre.symm
        _ = A.trace.re := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]
    calc
      traceNorm (mapTensorId Δ A) =
          A.trace.re * traceNorm (mapTensorId Δ ρ.toOp) := by
        conv_lhs => rw [hscale, mapTensorId_smul_basic,
          Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq, hnorm]
      _ ≤ A.trace.re * B := mul_le_mul_of_nonneg_left (hρ ρ) hpos.le
      _ ≤ B := mul_le_of_le_one_left hB htr

/-- **TIGHT PATH ONLY**: PSD characterization of diamond norm for Hermiticity-preserving maps.

    This theorem belongs to the stronger `PermutationCovariantTight` route and is
    not the standard CKR theorem from the paper.

    For a permutation-covariant (hence Hermiticity-preserving) map Δ, the diamond
    norm sSup over all operators X with ‖X‖₁ ≤ 1 equals the sSup over PSD operators
    with Tr(X) ≤ 1. This is because:
    1. For PSD X with Tr(X) ≤ 1, we have ‖X‖₁ = Tr(X) ≤ 1, so PSD operators are
       in the feasible set.
    2. By Watrous Theorem 3.46, for Hermiticity-preserving maps the diamond norm
       sup is attained on PSD operators.

    This lemma bridges the gap between the diamond norm definition (general operators)
    and the CKR bound (which requires PSD operators via substate extraction).

    The `PermutationCovariantTight` hypothesis provides both:
    - Hermiticity-preservation (for Watrous reduction to PSD operators)
    - `factors_through_sym` (for reducing PSD to PSD with symmetric support)

    Reference: Watrous "Theory of Quantum Information" Theorem 3.46;
    Kitaev-Watrous Proposition 3.47. -/
theorem diamondNorm_le_of_psd_bound_tight {n dimOut : ℕ} [NeZero n] [NeZero dimOut]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ : PermutationCovariantTight Δ)
    (B : ℝ)
    (h_psd_bound : ∀ (ρ : Op (4 ^ n * (4 ^ n))),
      Matrix.PosSemidef ρ → ρ.trace.re ≤ 1 →
      symmetricProjector 4 n * partialTraceB ρ = partialTraceB ρ →
      traceNorm (mapTensorId Δ ρ) ≤ B) :
    diamondNorm Δ ≤ B := by
  -- Derive 0 ≤ B from h_psd_bound by plugging in ρ = 0
  have hB : 0 ≤ B := by
    have h0 := h_psd_bound 0 Matrix.PosSemidef.zero
      (by simp [Matrix.trace_zero, Complex.zero_re])
      (by ext i j; simp [partialTraceB, Matrix.mul_apply])
    simp only [mapTensorId_zero, traceNorm_zero] at h0
    exact h0
  -- Step 1: Use symmetric factoring to remove the sym support condition
  have h_psd_no_sym : ∀ (ρ : Op (4 ^ n * (4 ^ n))),
      Matrix.PosSemidef ρ → ρ.trace.re ≤ 1 →
      traceNorm (mapTensorId Δ ρ) ≤ B :=
    psd_bound_with_sym_of_factors Δ hΔ.factors_through_sym B h_psd_bound
  -- Step 2: Use Kitaev-Watrous square-ancilla reduction (general → PSD, no factor loss)
  exact diamondNorm_le_of_psd_bound_no_sym Δ hΔ.preserves_conjTranspose
    B h_psd_no_sym

/-- **TIGHT PATH ONLY**: CKR core bound with symmetric-subspace coefficient.

    This is the stronger `PermutationCovariantTight` route. It is not the
    paper's standard Theorem 1 statement.

    For a permutation-covariant map Δ on (ℂ^4)^⊗n and de Finetti purification τ:
      ‖Δ‖_◇ ≤ C(n+3, 3) · ‖(Δ ⊗ id_R)(τ)‖₁

    The factor C(n+3, 3) = dim(Sym^n(ℂ^4)) is the dimension of the symmetric
    subspace of n copies of ℂ^4 (d=4 for BB84). It arises from the substate
    extraction lemma: any PSD operator with symmetric support is dominated by
    C(n+3,3) · σ_H, the symmetric projector.

    The proof uses three steps from CKR:
    1. **Reduction to PSD operators**: For perm-covariant (Hermiticity-preserving) Δ,
       the diamond norm sup is attained on PSD operators (Watrous Theorem 3.46).
    2. **Substate extraction** (CKR Lemma 1): Any PSD ρ on Sym^n satisfies
       ρ ≤ g_{n,d} · (id ⊗ T†T)(ω) for trace-non-increasing T.
    3. **Trace norm bound**: ‖(Δ⊗id)(ρ)‖₁ ≤ g_{n,d} · ‖(Δ⊗id)(ω)‖₁.

    Reference: CKR (2009) arXiv:0809.3019, Theorem 1 + Lemma 1. -/
theorem diamondNorm_le_symDim_mul_ckrTraceNorm_tight {n dimOut dimR : ℕ}
    [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ : PermutationCovariantTight Δ)
    (τ : DensityOp ((4 ^ n) * dimR))
    (hτ : IsDeFinettiPurification (d := 4) τ) :
    diamondNorm Δ ≤ ↑(Nat.choose (n + 3) 3) * ckrTensorTraceNorm Δ τ := by
  apply diamondNorm_le_of_psd_bound_tight Δ hΔ _ _
  intro X₀ hX₀_psd hX₀_trace hX₀_support
  unfold ckrTensorTraceNorm
  have hτ_toOp : τ.partialTraceB.toOp =
      (1 / Matrix.trace (symmetricProjector 4 n)) •
        symmetricProjector 4 n := by
    rw [hτ.isDeFinetti]; rfl
  exact ckr_psd_bound Δ hΔ.preserves_conjTranspose X₀ hX₀_psd hX₀_trace τ
    hτ.isPure hτ_toOp hX₀_support

/-- **TIGHT PATH ONLY**: CKR postselection corollary for the stronger route.

    This corollary uses `PermutationCovariantTight` and the `d - 1 = 3` exponent.
    It is not the standard CKR Theorem 1 statement.

    For a permutation-covariant linear map Δ : End(H^⊗n) → End(H'),
      ‖Δ‖_◇ ≤ (n+1)^{d-1} · ‖(Δ ⊗ id_R)(τ_{H^n R})‖₁

    where:
    - ‖·‖_◇ is the diamond norm (completely bounded trace norm)
    - τ_{H^n R} is a purification of τ_{H^n} = ∫ σ^⊗n dσ
    - Permutation covariance: ∀ π, ∃ K_π CPTP, Δ ∘ π = K_π ∘ Δ

    For BB84 (d = dim(H_A ⊗ H_B) = 4, so d-1 = 3):
      ‖Δ‖_◇ ≤ (n+1)^3 · ‖(Δ ⊗ id_R)(τ)‖₁

    **Note on exponent**: The standard CKR Theorem 1 (without the
    `factors_through_sym` hypothesis) gives exponent d²-1 = 15. The tighter
    exponent d-1 = 3 here is possible because `PermutationCovariantTight` includes
    `factors_through_sym`, which restricts the relevant operators to the
    symmetric subspace Sym^n(ℂ^d) of dimension C(n+d-1, d-1) = C(n+3, 3),
    rather than the full space of dimension C(n+d²-1, d²-1) = C(n+15, 15).

    Reference: Christandl-Konig-Renner (2009) "Postselection technique
    for quantum channels with applications to quantum cryptography", Theorem 1. -/
theorem ckr_postselection_tight {n : ℕ} [NeZero n]
    (dimOut dimR : ℕ) [NeZero dimOut] [NeZero dimR]
    (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ : PermutationCovariantTight Δ)
    (τ : DensityOp ((4 ^ n) * dimR))
    (hτ : IsDeFinettiPurification (d := 4) τ) :
    diamondNorm Δ ≤ (↑n + 1) ^ (3 : ℕ) * ckrTensorTraceNorm Δ τ := by
  calc diamondNorm Δ
      ≤ ↑(Nat.choose (n + 3) 3) * ckrTensorTraceNorm Δ τ :=
        diamondNorm_le_symDim_mul_ckrTraceNorm_tight Δ hΔ τ hτ
    _ ≤ (↑n + 1) ^ (3 : ℕ) * ckrTensorTraceNorm Δ τ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast choose_add_le_pow_succ n 3)
          (ckrTensorTraceNorm_nonneg Δ τ)

end QKD.BB84.Engine
