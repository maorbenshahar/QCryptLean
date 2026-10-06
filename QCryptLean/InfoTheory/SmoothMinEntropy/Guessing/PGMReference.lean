import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.PovmCompactness
import QCryptLean.InfoTheory.SmoothMinEntropy.Guessing.PGMDualWitness
import QCryptLean.Math.SpectralTheory.LiebThirring

/-!
# PGM (Pretty-Good-Measurement) Reference Operator

Supporting lemmas for the `σ*` construction used in the strong-duality direction of
`conditionalMinEntropyReal_cq_guess_eq` (Tomamichel 2016, eq. 6.30).

Given a CQ state `ρ : CQState X n` and a POVM `M : X → Op n`, the PGM operator
is the (un-normalized) sum

    `pgmOp M ρ = ∑ x, √(M x) · ρ_A(x) · √(M x)`.

Each summand is PSD (`Math.SpectralTheory.posSemidef_sqrt_conj`), so the sum is
Hermitian and PSD.  Moreover, when every `M x` is PSD, the trace identity
`√(M x) · √(M x) = M x` and cyclicity give

    `(pgmOp M ρ).trace.re = ∑ x, ((M x) * ρ_A(x)).trace.re`,

i.e. the PGM trace equals the POVM guessing objective.

When `M` attains the POVM guessing supremum with value `p > 0`, the
normalized reference `σ* := (1/p) • pgmOp M ρ` is a `SubDensityOp` (trace ≤ 1
by the optimality value `p`).  The feasibility witness used downstream is,
however, built from an SDP strong-duality operator `Y` rather than from
`pgmOp` directly, since the PGM of a primal-optimal POVM is not always the
dual-optimal reference (Helstrom-qubit counterexample).

## Main declarations

- `pgmOp` : the un-normalized PGM operator.
- `pgmOp_isHermitian`, `pgmOp_posSemidef`, `pgmOp_trace_re_eq_povm_objective`.
- `exists_sdp_dual_witness_of_optimal_povm` : SDP strong-duality existential
  giving a PSD operator `Y` dominating each classical fibre.
- `pgmSigma` : the normalized PGM reference packaged as `SubDensityOp`.
- `pgm_sigma_feasible_of_hermitian_povm` : existential feasibility built from
  the SDP dual witness, for a Hermitian optimal POVM.
-/

open Quantum.Operators Matrix Real
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The PGM operator -/

/-- The (un-normalized) Pretty-Good-Measurement operator
    `pgmOp M ρ = ∑ x, √(M x) · ρ_A(x) · √(M x)`. -/
noncomputable def pgmOp {X : Type*} [Fintype X] {n : ℕ}
    (M : X → Op n) (ρ : CQState X n) : Op n :=
  ∑ x : X, (CFC.sqrt (M x)) * (ρ.stateMap x).toOp * (CFC.sqrt (M x))

/-- Each summand `√(M x) · ρ_A(x) · √(M x)` is PSD when `M x` is PSD. -/
private lemma pgmOp_summand_posSemidef {X : Type*} [Fintype X] {n : ℕ}
    (M : X → Op n) (ρ : CQState X n)
    (hM_psd : ∀ x : X, (M x).PosSemidef) (x : X) :
    Matrix.PosSemidef
      ((CFC.sqrt (M x)) * (ρ.stateMap x).toOp * (CFC.sqrt (M x))) :=
  Math.SpectralTheory.posSemidef_sqrt_conj (M x) (ρ.stateMap x).toOp (hM_psd x)
    (Quantum.Operators.posSemidefOp_implies_mathlib (ρ.stateMap x).toPosSemidefOp)

/-- Each summand `√(M x) · ρ_A(x) · √(M x)` is Hermitian unconditionally:
`CFC.sqrt (M x)` is self-adjoint for any `M x` (it is in fact `≥ 0`), and
`(ρ.stateMap x).toOp` is Hermitian by construction (it is PSD). -/
private lemma pgmOp_summand_isHermitian {X : Type*} [Fintype X] {n : ℕ}
    (M : X → Op n) (ρ : CQState X n) (x : X) :
    ((CFC.sqrt (M x)) * (ρ.stateMap x).toOp * (CFC.sqrt (M x))).IsHermitian := by
  refine IsSelfAdjoint.isHermitian ?_
  exact (ρ.stateMap x).isHermitian.isSelfAdjoint.conjugate_self
    (hz := (CFC.sqrt_nonneg (M x)).isSelfAdjoint)

/-- `pgmOp M ρ` is Hermitian unconditionally. -/
lemma pgmOp_isHermitian {X : Type*} [Fintype X] {n : ℕ}
    (M : X → Op n) (ρ : CQState X n) :
    (pgmOp M ρ).IsHermitian := by
  unfold pgmOp
  -- Hermiticity of a finset sum.
  refine IsSelfAdjoint.isHermitian ?_
  exact isSelfAdjoint_sum _ (fun x _ =>
    (pgmOp_summand_isHermitian M ρ x))

/-- `pgmOp M ρ` is PSD when every `M x` is PSD. -/
lemma pgmOp_posSemidef {X : Type*} [Fintype X] {n : ℕ}
    (M : X → Op n) (ρ : CQState X n)
    (hM_psd : ∀ x : X, (M x).PosSemidef) :
    Matrix.PosSemidef (pgmOp M ρ) := by
  unfold pgmOp
  exact Matrix.posSemidef_sum (s := Finset.univ) (fun x _ =>
    pgmOp_summand_posSemidef M ρ hM_psd x)

/-- Trace identity: under the PSD hypothesis on `M`, the trace of the PGM
operator equals the POVM guessing objective. -/
lemma pgmOp_trace_re_eq_povm_objective {X : Type*} [Fintype X] {n : ℕ}
    (M : X → Op n) (ρ : CQState X n)
    (hM_psd : ∀ x : X, (M x).PosSemidef) :
    (pgmOp M ρ).trace.re =
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re := by
  unfold pgmOp
  rw [Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  -- Rearrange: Tr(√M · ρ · √M) = Tr(ρ · √M · √M) = Tr(ρ · M) = Tr(M · ρ)
  have h_sq : (CFC.sqrt (M x)) * (CFC.sqrt (M x)) = M x :=
    CFC.sqrt_mul_sqrt_self (M x) (hM_psd x).nonneg
  have h_trace_eq :
      ((CFC.sqrt (M x)) * (ρ.stateMap x).toOp * (CFC.sqrt (M x))).trace =
        ((M x) * (ρ.stateMap x).toOp).trace := by
    rw [mul_assoc (CFC.sqrt (M x)) (ρ.stateMap x).toOp (CFC.sqrt (M x)),
        Matrix.trace_mul_comm,
        mul_assoc (ρ.stateMap x).toOp (CFC.sqrt (M x)) (CFC.sqrt (M x)),
        h_sq,
        Matrix.trace_mul_comm]
  rw [h_trace_eq]

/-! ## Strong-duality existential

The feasible σ witness downstream is built from an SDP strong-duality
operator `Y` that dominates each `ρ_A(x)` and has trace equal to the
guessing probability.  This is **not** in general `pgmOp M ρ` itself: the
Helstrom qubit (with `ρ_A(0) = diag(1/2, 0)`) is dominated by its optimal
dual witness but not by the corresponding PGM operator `pgmOp M ρ ≈ 0.427·I`.

References: Tomamichel 2016 §6.2, Koenig–Renner–Schaffner 2009 Lemma 2,
Barnum et al. 2000 §III. -/

/-- **SDP strong-duality existential**.

For a CQ state `ρ` with a primal-optimal POVM `M` attaining the guessing
supremum, strong duality produces a PSD dual witness `Y` that dominates
every classical fibre `ρ_A(x)` and whose trace equals the guessing
probability.  `Y` is **not** in general equal to `pgmOp M ρ`; the consumer
must build its feasible σ from `Y` directly. -/
lemma exists_sdp_dual_witness_of_optimal_povm
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n)
    (M : X → Op n)
    (hM_psd : ∀ x : X, (M x).PosSemidef)
    (hM_sum : ∑ x : X, M x = 1)
    (hp_eq :
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re = povmGuessingProb ρ) :
    ∃ Y : Op n, Y.PosSemidef ∧
      (∀ x : X, opLe (ρ.stateMap x).toOp Y) ∧
      Y.trace.re = povmGuessingProb ρ := by
  -- Derive `Nonempty X` from `∑ x, M x = 1` together with `NeZero n`.
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  haveI : Nonempty X := by
    rcases isEmpty_or_nonempty X with hE | hNE
    · exfalso
      have hsum0 : (∑ x : X, M x) = (0 : Op n) := by
        rw [Finset.sum_of_isEmpty]
      rw [hsum0] at hM_sum
      exact one_ne_zero hM_sum.symm
    · exact hNE
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  refine ⟨pgmDualWitness ρ M, ?_, ?_, ?_⟩
  · exact pgmDualWitness_posSemidef ρ M hM_psd hM_sum hp_eq x₀
  · exact pgmDualWitness_dominates ρ M hM_psd hM_sum hp_eq
  · rw [pgmDualWitness_trace_re_eq]; exact hp_eq

/-! ## Packaging: the `SubDensityOp` wrapper `pgmSigma` -/

/-- Trace of the (un-normalized) PGM operator, under PSD hypothesis on `M`,
equals the POVM guessing objective (restatement). -/
private lemma pgmOp_trace_re_eq_of_optimal {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n)
    (hM_psd : ∀ x : X, (M x).PosSemidef)
    (hp_eq :
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re = povmGuessingProb ρ) :
    (pgmOp M ρ).trace.re = povmGuessingProb ρ := by
  rw [pgmOp_trace_re_eq_povm_objective M ρ hM_psd, hp_eq]

/-- The scaled PGM operator `(1/p) • pgmOp M ρ` is Hermitian. -/
private lemma pgmSigma_aux_isHermitian {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n) (p : ℝ) :
    ((Complex.ofReal (1 / p)) • pgmOp M ρ).IsHermitian :=
  isHermitian_real_smul (pgmOp_isHermitian M ρ) (1 / p)

/-- The scaled PGM operator `(1/p) • pgmOp M ρ` has non-negative quadratic
form when `p ≥ 0`. -/
private lemma pgmSigma_aux_pos_semidef {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n)
    (hM_psd : ∀ x : X, (M x).PosSemidef) {p : ℝ} (hp_nn : 0 ≤ p) :
    ∀ v : Fin n → ℂ,
      0 ≤ (quadraticForm ((Complex.ofReal (1 / p)) • pgmOp M ρ) v).re := by
  intro v
  rw [quadraticForm_ofReal_smul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hp_inv_nn : 0 ≤ 1 / p := by positivity
  refine mul_nonneg hp_inv_nn ?_
  have hpsd := pgmOp_posSemidef M ρ hM_psd
  exact posSemidef_re_quadraticForm_nonneg hpsd v

/-- Trace of the scaled PGM operator `(1/p) • pgmOp M ρ` equals `1` when
`p > 0` and `M` attains the sup. -/
private lemma pgmSigma_aux_trace_re_eq_one {X : Type*} [Fintype X] {n : ℕ}
    (ρ : CQState X n) (M : X → Op n)
    (hM_psd : ∀ x : X, (M x).PosSemidef)
    (hp_pos : 0 < povmGuessingProb ρ)
    (hp_eq :
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re = povmGuessingProb ρ) :
    ((Complex.ofReal (1 / povmGuessingProb ρ)) • pgmOp M ρ).trace.re = 1 := by
  rw [trace_real_smul_re,
      pgmOp_trace_re_eq_of_optimal ρ M hM_psd hp_eq]
  field_simp

/-- The Pretty-Good-Measurement reference operator, packaged as a
`SubDensityOp`.  Its trace equals `1` exactly (so in particular `≤ 1`). -/
noncomputable def pgmSigma
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n) (M : X → Op n)
    (hM_psd : ∀ x : X, (M x).PosSemidef)
    (hp_pos : 0 < povmGuessingProb ρ)
    (hp_eq :
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re = povmGuessingProb ρ) :
    SubDensityOp n where
  toOp := (Complex.ofReal (1 / povmGuessingProb ρ)) • pgmOp M ρ
  isHermitian := pgmSigma_aux_isHermitian ρ M (povmGuessingProb ρ)
  pos_semidef :=
    pgmSigma_aux_pos_semidef ρ M hM_psd (le_of_lt hp_pos)
  trace_le_one := by
    rw [pgmSigma_aux_trace_re_eq_one ρ M hM_psd hp_pos hp_eq]

/-! ## Consumer lemma: feasibility via SDP strong duality

The witness σ is built from the SDP dual witness `Y` directly; `pgmSigma`
and friends remain as definitions but are not used in the feasibility
conclusion, since in general the PGM is not the dual-optimal reference
(Helstrom counterexample). -/

/-- **Feasibility from strong duality**.

If `M : X → Op n` is a Hermitian POVM attaining the POVM-guessing supremum
with value `p := povmGuessingProb ρ > 0`, then by SDP strong duality (via
`exists_sdp_dual_witness_of_optimal_povm`) there exists a PSD operator `Y`
dominating each `ρ_A(x)` with `Tr(Y) = p`.  The normalized witness
`σ := (1/p) • Y` is a sub-density operator with `isFeasible ρ σ p`.

Note: this lemma does NOT claim `σ = (1/p) • pgmOp M ρ`; that claim is
false in general (the PGM of a primal-optimal POVM is not always the
dual-optimal reference — Helstrom qubit is a counterexample). -/
lemma pgm_sigma_feasible_of_hermitian_povm
    {X : Type*} [Fintype X] {n : ℕ} [NeZero n]
    (ρ : CQState X n)
    (M : X → Op n)
    (hM_psd : ∀ x : X, (M x).PosSemidef)
    (hM_sum : ∑ x : X, M x = 1)
    (hp_pos : 0 < povmGuessingProb ρ)
    (hp_eq :
      ∑ x : X, ((M x) * (ρ.stateMap x).toOp).trace.re = povmGuessingProb ρ) :
    ∃ σ : SubDensityOp n, isFeasible ρ σ (povmGuessingProb ρ) := by
  -- Obtain the SDP-dual witness via strong duality.
  obtain ⟨Y, hY_psd, hY_dom, hY_trace⟩ :=
    exists_sdp_dual_witness_of_optimal_povm ρ M hM_psd hM_sum hp_eq
  set p : ℝ := povmGuessingProb ρ
  have hp_inv_nn : 0 ≤ 1 / p := by positivity
  refine ⟨{ toOp := (Complex.ofReal (1 / p)) • Y,
            isHermitian := isHermitian_real_smul hY_psd.1 (1 / p),
            pos_semidef := fun v => by
              rw [quadraticForm_ofReal_smul, Complex.mul_re]
              simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
              refine mul_nonneg hp_inv_nn ?_
              exact posSemidef_re_quadraticForm_nonneg hY_psd v,
            trace_le_one := by
              rw [trace_real_smul_re, hY_trace]
              have hpp : (1 / p) * p = 1 := by field_simp
              linarith },
          le_of_lt hp_pos, fun x => ?_⟩
  -- Feasibility: ρ_A(x) ≤_PSD p • σ = p • ((1/p) • Y) = Y, which is hY_dom x.
  intro v
  have h_rescale : (Complex.ofReal p) • ((Complex.ofReal (1 / p)) • Y) = Y := by
    rw [smul_smul, ← Complex.ofReal_mul]
    have hpp : p * (1 / p) = 1 := by field_simp
    rw [hpp, Complex.ofReal_one, one_smul]
  rw [h_rescale]
  exact hY_dom x v

end InfoTheory.SmoothMinEntropy

end
