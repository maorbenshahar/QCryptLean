import QCryptLean.InfoTheory.Renyi.DivergenceVariance
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CQJointEntropyLowerBound

/-!
# The `vonNeumannEntropy` ↔ `condVonNeumann` bridge

`InfoTheory.Renyi.condVonNeumann` is Dupuis–Fawzi's `H(A|B)_ρ = −D(ρ_AB ‖ 1_A ⊗ ρ_B)`
(arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex:271`–`:275`,
`\label{def:von-neumann-entropy}` at `:274`), written through `CFC.log` and a trace.  The BB84
finite-size chain carries the same number in its **spectral** form, `(S(ρ_XB) − S(ρ_B))/log 2`,
because `InfoTheory.VonNeumannEntropy.vonNeumannEntropy` is the Shannon entropy of
`eigenvaluesOf`.  This module proves the two are equal.

No new mathematics beyond one step: `trace_mul_log_re_eq_sum`, which evaluates
`Tr[A · log A]` in `A`'s own eigenbasis.  Everything else is packaging over existing
public machinery — `CQState.isEigenvalueSpectrum_toJointDensityOp_jointEigenvalues`
(`Renner/CQJointEntropyLowerBound.lean`) for the block-diagonal spectrum,
`condVonNeumann_eq_blockwise` (`Renyi/DivergenceVariance.lean`) for the blockwise `CFC` form.

## Units

`vonNeumannEntropy` is in **nats** (`entropyTerm p = −p·log p` with the natural log,
`VonNeumannEntropy/Defs.lean:113`, `Math/ClassicalEntropy/Entropy.lean:41`), while
`condVonNeumann = −relEntropyBase2(ρ_XB ‖ 1_X ⊗ ρ_B)` is in **bits**.  The `/ Real.log 2` in
`condVonNeumann_eq_vonNeumannEntropy_sub_div_log_two` is that conversion.  `Real.log 0 = 0` is
load-bearing on both sides: it is what makes `entropyTerm 0 = 0` agree with `−0·log 0` at the
zero eigenvalues that a rank-deficient block contributes.
-/

open Quantum.Operators Matrix InfoTheory.SmoothMinEntropy
open Math.ClassicalEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

/-! ## Traces of a continuous functional calculus in the eigenbasis -/

private lemma contOn_spec_bridge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (a : Matrix ι ι ℂ) : ContinuousOn f (spectrum ℝ a) :=
  (Matrix.finite_real_spectrum (A := a)).continuousOn f

/-- `Tr[f(A)] = ∑ᵢ f(λᵢ)` for Hermitian `A`, at the generic continuous functional calculus.

The unitary conjugation of `Matrix.IsHermitian.cfc` cancels under the trace, leaving the trace of
a diagonal matrix. -/
theorem trace_cfc_eq_sum_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ((∑ i, f (hA.eigenvalues i) : ℝ) : ℂ) := by
  classical
  rw [hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hstar : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hstar, Matrix.one_mul, Matrix.trace_diagonal,
    Complex.ofReal_sum]
  rfl

/-- `Tr[A · log A].re = ∑ᵢ λᵢ · log λᵢ` for Hermitian `A`.

This is the one genuinely new step of this module: it is what connects the `CFC.log` trace form
that `relEntropyBase2` is written in to the eigenvalue form that `vonNeumannEntropy` is written
in.  `Real.log 0 = 0` makes the zero-eigenvalue summands vanish on both sides. -/
theorem trace_mul_log_re_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A * CFC.log A).trace.re = ∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i) := by
  have hcfc : cfc (fun t : ℝ => t * Real.log t) A = A * CFC.log A := by
    rw [cfc_mul (fun t : ℝ => t) Real.log A (contOn_spec_bridge _ A) (contOn_spec_bridge _ A),
      cfc_id' ℝ A hA.isSelfAdjoint]
    rfl
  rw [← hcfc, trace_cfc_eq_sum_eigenvalues hA (fun t : ℝ => t * Real.log t), Complex.ofReal_re]

/-! ## The von Neumann entropy as a `CFC` trace -/

/-- `S(ρ) = −Tr[ρ · log ρ].re`, i.e. `InfoTheory.VonNeumannEntropy.vonNeumannEntropy` in the
`CFC` trace form the Dupuis–Fawzi objects are written in. -/
theorem vonNeumannEntropy_eq_neg_trace_mul_log {N : ℕ} [NeZero N] (ρ : DensityOp N) :
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy ρ = -(ρ.toOp * CFC.log ρ.toOp).trace.re := by
  have hH : ρ.toOp.IsHermitian := ρ.toPosSemidefOp.toHermitianOp.isHermitian
  rw [trace_mul_log_re_eq_sum hH,
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy,
    shannonEntropy_eq_neg_sum_mul_log]
  rfl

/-- `S(ρ_XB) = −∑ₓ Tr[σₓ · log σₓ].re` for a normalized cq state: the joint entropy of the
block-diagonal joint operator, read blockwise.

The joint spectrum is `CQState.jointEigenvalues`
(`CQState.isEigenvalueSpectrum_toJointDensityOp_jointEigenvalues`), which is the disjoint union of
the per-block spectra, so the Shannon sum splits along the blocks. -/
theorem vonNeumannEntropy_toJointDensityOp_eq_neg_sum_blocks
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} [NeZero n] [NeZero (n * Fintype.card X)]
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    InfoTheory.VonNeumannEntropy.vonNeumannEntropy (ρ.toJointDensityOp hnorm)
      = -∑ x : X, ((ρ.stateMap x).toOp * CFC.log (ρ.stateMap x).toOp).trace.re := by
  classical
  rw [InfoTheory.VonNeumannEntropy.vonNeumannEntropy_eq_shannonEntropy (ρ.toJointDensityOp hnorm)
      ρ.jointEigenvalues (ρ.isEigenvalueSpectrum_toJointDensityOp_jointEigenvalues hnorm),
    shannonEntropy_eq_neg_sum_mul_log]
  congr 1
  have hblocks : ∀ x : X,
      ((ρ.stateMap x).toOp * CFC.log (ρ.stateMap x).toOp).trace.re
        = ∑ i : Fin n, ρ.blockEigenvalues x i * Real.log (ρ.blockEigenvalues x i) := by
    intro x
    exact trace_mul_log_re_eq_sum (ρ.stateMap x).isHermitian
  simp_rw [hblocks]
  rw [show (∑ k, ρ.jointEigenvalues k * Real.log (ρ.jointEigenvalues k))
        = ∑ p : Fin n × X,
            ρ.blockEigenvalues p.2 p.1 * Real.log (ρ.blockEigenvalues p.2 p.1) from by
      rw [← Equiv.sum_comp (cqJointEquiv X n).symm
        (fun p : Fin n × X =>
          ρ.blockEigenvalues p.2 p.1 * Real.log (ρ.blockEigenvalues p.2 p.1))]
      rfl,
    Fintype.sum_prod_type_right]

/-! ## The identity -/

/-- **`H(X|B)_ρ = (S(ρ_XB) − S(ρ_B)) / log 2`.**

The Dupuis–Fawzi conditional von Neumann entropy `condVonNeumann`
(arXiv:1805.11652, `EAT-second-order-ieee-1col-r2.tex:271`–`:275`) equals the spectral
entropy difference, in bits.

`hnorm` is required and not cosmetic: `relEntropyBase2` divides by `Tr[ρ_XB].re`, so the identity
holds only at trace one.  The reference `1_X ⊗ ρ_B` is the pinned one of `condPetzRenyiDown`. -/
theorem condVonNeumann_eq_vonNeumannEntropy_sub_div_log_two
    {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} [NeZero n] [NeZero (n * Fintype.card X)]
    (ρ : CQState X n) (hnorm : ∑ x : X, (ρ.stateMap x).trace = 1) :
    condVonNeumann ρ
      = (InfoTheory.VonNeumannEntropy.vonNeumannEntropy (ρ.toJointDensityOp hnorm)
          - InfoTheory.VonNeumannEntropy.vonNeumannEntropy (ρ.quantumMarginalDensityOp hnorm))
        / Real.log 2 := by
  classical
  have hJtr : ρ.toJointOp.trace.re = 1 := by
    rw [CQState.toJointOp_trace_re_eq_sum]; exact hnorm
  -- the marginal side
  have hmarg : InfoTheory.VonNeumannEntropy.vonNeumannEntropy (ρ.quantumMarginalDensityOp hnorm)
      = -(ρ.quantumMarginalOp * CFC.log ρ.quantumMarginalOp).trace.re := by
    have h := vonNeumannEntropy_eq_neg_trace_mul_log (ρ.quantumMarginalDensityOp hnorm)
    rwa [show (ρ.quantumMarginalDensityOp hnorm).toOp = ρ.quantumMarginalOp from rfl] at h
  -- the joint side
  have hjoint := vonNeumannEntropy_toJointDensityOp_eq_neg_sum_blocks ρ hnorm
  -- the cross term: `∑ₓ Tr[σₓ · log ρ_B] = Tr[ρ_B · log ρ_B]`
  have hcross : ∑ x : X, ((ρ.stateMap x).toOp * CFC.log ρ.quantumMarginalOp).trace.re
      = (ρ.quantumMarginalOp * CFC.log ρ.quantumMarginalOp).trace.re := by
    rw [show ρ.quantumMarginalOp = ∑ x : X, (ρ.stateMap x).toOp from rfl, Finset.sum_mul,
      Matrix.trace_sum, Complex.re_sum]
  -- split the blockwise numerator
  have hsplit : ∑ x : X, ((ρ.stateMap x).toOp
        * (CFC.log (ρ.stateMap x).toOp - CFC.log ρ.quantumMarginalOp)).trace.re
      = (∑ x : X, ((ρ.stateMap x).toOp * CFC.log (ρ.stateMap x).toOp).trace.re)
        - ∑ x : X, ((ρ.stateMap x).toOp * CFC.log ρ.quantumMarginalOp).trace.re := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [condVonNeumann_eq_blockwise ρ, hJtr, one_mul, hsplit, hcross, hjoint, hmarg]
  ring

end InfoTheory.Renyi

end -- noncomputable section
