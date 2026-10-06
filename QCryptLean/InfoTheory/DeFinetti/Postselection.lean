import QCryptLean.InfoTheory.DeFinetti.Measure
import QCryptLean.InfoTheory.DeFinetti.Purification
import QCryptLean.Quantum.Symmetry.SymmetricSubspace
import QCryptLean.Quantum.TensorProducts.PSDOrder
import QCryptLean.Quantum.Operators.PSDTraceBound

/-!
# de Finetti / CKR postselection operator bound

This module states the **multiplicative** Christandl–König–Renner postselection bound
for a permutation-symmetric state and its de Finetti measure, and derives the
trace-pairing corollary used by parameter-estimation soundness arguments.

The CKR postselection technique (Christandl–König–Renner 2009, arXiv:0809.3019, main.tex:268–:401
(\emph{Main Result}: Theorem `\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}`
:319–:328);
restated in Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024, arXiv:2403.11851, Thm 1/2) says: a state
`ρ_n` on the symmetric subspace of `(ℂᵈ)^{⊗n}` is dominated, *as an operator*, by the
**postselection factor** `g_{n,d} = C(n + d²−1, d²−1)` times the de Finetti mixture
`∫ σ^{⊗n} dν(σ)` for a suitable measure `ν`:

  `ρ_n ≤ g_{n,d} · ∫ σ^{⊗n} dν`.

The factor is **multiplicative**, never additive, and never divided by `2ⁿ`.  We use the
elementary polynomial over-estimate `g_{n,d} ≤ (n+1)^{d²−1}` (`Nat.choose_add_le_pow_succ`,
local `choose_add_le_pow_succ`) so the factor appearing here is `(n+1)^{d²−1}`.

The symmetric-subspace dimension `C(n+d-1,d-1)` is `symmetricSubspace_dim`; the paired
`d²`-dimensional version (the one that drives the purified postselection factor here) lives
in the Quantum.Symmetry symmetric-subspace file and in the CKRBound.Reference files under the
Quantum.Channels namespace. The operator-domination engine already present for the `d=4`
marginal case is `Quantum.Channels.partial_trace_symmetric_bound`.

## Main statements
- `deFinetti_postselection_op_le`: the operator inequality (open `sorry`) — for a
  symmetric `ρ : DensityOp (d^n)` there is a de Finetti measure `ν` with
  `(n+1)^{d²−1} • (∫ σ^{⊗n} dν) − ρ ⪰ 0`.
- `deFinetti_postselection_traceMul_le`: the trace-pairing corollary (**proved** from the
  operator inequality) — for any PSD measurement operator `M`,
  `Tr(M ρ) ≤ (n+1)^{d²−1} · Tr(M ∫ σ^{⊗n} dν)`.
-/

open Quantum.Operators Matrix InfoTheory.DeFinetti Quantum.Symmetry
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace InfoTheory.DeFinetti

/-- For Hermitian operators, left support by a projector implies the right-support identity.
(Local copy of the Quantum.Channels lemma to avoid inverting the module layering.) -/
private lemma right_support_of_left_support_of_isHermitian {d : ℕ} [NeZero d]
    {P A : Op d}
    (hP_herm : P.IsHermitian) (hA_herm : A.IsHermitian)
    (h_support : P * A = A) :
    A * P = A := by
  calc A * P = (A * P)ᴴᴴ := by rw [conjTranspose_conjTranspose]
    _ = (Pᴴ * Aᴴ)ᴴ := by rw [conjTranspose_mul]
    _ = (P * A)ᴴ := by rw [hP_herm, hA_herm]
    _ = Aᴴ := by rw [h_support]
    _ = A := hA_herm

/-- A PSD operator of trace at most one and supported on a projector is dominated by that
projector.  (Local copy of the Quantum.Channels lemma to avoid inverting the module layering.) -/
private lemma projector_sub_psd_of_support {d : ℕ} [NeZero d]
    (P A : Op d)
    (hP_idem : P * P = P) (hP_herm : P.IsHermitian)
    (hA_psd : A.PosSemidef) (hA_tr : A.trace.re ≤ 1)
    (h_support : P * A = A) :
    (P - A).PosSemidef := by
  have hAP : A * P = A :=
    right_support_of_left_support_of_isHermitian hP_herm hA_psd.isHermitian h_support
  have h1A := Quantum.Operators.psd_le_one_of_trace_le_one A hA_psd hA_tr
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hP_herm.sub hA_psd.isHermitian, fun x => ?_⟩
  set w := P.mulVec x with hw_def
  have h_adj : ∀ u v, star u ⬝ᵥ P.mulVec v = star (P.mulVec u) ⬝ᵥ v := by
    intro u v
    rw [dotProduct_mulVec, Matrix.star_mulVec, hP_herm]
  have hxPx : star x ⬝ᵥ P.mulVec x = star w ⬝ᵥ w := by
    conv_lhs => rw [show P.mulVec x = P.mulVec w from by
      rw [hw_def]
      conv_lhs => rw [← hP_idem]
      rw [← Matrix.mulVec_mulVec]]
    exact h_adj x w
  have hxAx : star x ⬝ᵥ A.mulVec x = star w ⬝ᵥ A.mulVec w := by
    calc star x ⬝ᵥ A.mulVec x
        = star x ⬝ᵥ A.mulVec w := by
            congr 1
            rw [hw_def]
            conv_lhs => rw [← hAP]
            rw [← Matrix.mulVec_mulVec]
      _ = star x ⬝ᵥ P.mulVec (A.mulVec w) := by
            congr 1
            conv_lhs => rw [← h_support]
            rw [← Matrix.mulVec_mulVec]
      _ = star w ⬝ᵥ A.mulVec w := by
            rw [h_adj, hw_def]
  rw [Matrix.sub_mulVec, dotProduct_sub, hxPx, hxAx]
  have h1A_dot := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h1A).2 w
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at h1A_dot

/-- Binomial bound `C(n+k, k) ≤ (n+1)^k`.  (Local copy of `choose_add_le_pow_succ` to avoid
importing the BB84 layer, which sits above this de Finetti module.) -/
private theorem choose_add_le_pow_succ (n k : ℕ) : Nat.choose (n + k) k ≤ (n + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hid := Nat.add_one_mul_choose_eq (n + k) k
    have hk : 0 < k + 1 := Nat.succ_pos k
    change (n + k + 1).choose (k + 1) ≤ (n + 1) ^ (k + 1)
    apply Nat.le_of_mul_le_mul_right _ hk
    show (n + k + 1).choose (k + 1) * (k + 1) ≤ (n + 1) ^ (k + 1) * (k + 1)
    rw [← hid, Nat.pow_add_one']
    calc
      (n + k + 1) * (n + k).choose k ≤ (n + k + 1) * (n + 1) ^ k :=
        Nat.mul_le_mul_left _ ih
      _ ≤ ((n + 1) * (k + 1)) * (n + 1) ^ k :=
        Nat.mul_le_mul_right _ (by nlinarith [Nat.zero_le (n * k)])
      _ = (n + 1) * (n + 1) ^ k * (k + 1) := by ring

/-- **CKR postselection operator bound (open de Finetti content).**

For a permutation-**symmetric** state `ρ : DensityOp (d^n)` — symmetric meaning its support
lies in the symmetric subspace, `symmetricProjector d n * ρ = ρ` — there is a de Finetti
measure `ν : DensityMeasure d` whose de Finetti mixture `∫ σ^{⊗n} dν` dominates `ρ` as an
operator, up to the multiplicative postselection factor `(n+1)^{d²−1}`:

  `(n+1)^{d²−1} • (∫ σ^{⊗n} dν).toOp − ρ.toOp ⪰ 0`.

This is the Christandl–König–Renner postselection inequality (arXiv:0809.3019, main.tex:268–:401
(\emph{Main Result}: Theorem `\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}`
:319–:328)),
restated as Theorem 1/2 of Nahar, Tupkary, Zhao, Lütkenhaus, Tan (arXiv:2403.11851).  The factor is
multiplicative: the exact CKR factor is `g_{n,d} = C(n+d²−1, d²−1)`, here over-estimated by
`(n+1)^{d²−1}` via `choose_add_le_pow_succ`.

The genuine open content is the construction of `ν` (the universal de Finetti / Haar
measure) and the symmetric-subspace domination; the `d=4` marginal engine
`partial_trace_symmetric_bound` is the existing analogue. -/
theorem deFinetti_postselection_op_le {d : ℕ} [NeZero d] (n : ℕ) [NeZero n] [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n))
    (hsupp : symmetricProjector d n * ρ.toOp = ρ.toOp) :
    ∃ ν : DensityMeasure d,
      (((n + 1 : ℝ) ^ (d ^ 2 - 1) : ℂ) • (integralTensorPower n ν).toOp - ρ.toOp).PosSemidef := by
  -- Choose the universal de Finetti (Haar) measure; its mixture is the
  -- normalized symmetric projector `P / Tr P`, the maximally mixed state on `Sym^n(ℂᵈ)`.
  refine ⟨deFinetti_haarMeasure d, ?_⟩
  set P := symmetricProjector d n with hP_def
  obtain ⟨hP_idem, hP_herm⟩ := symmetricProjector_is_projector d n
  -- Identify `∫ σ^{⊗n} dν` with `(1 / Tr P) • P`.
  have hτ : (integralTensorPower n (deFinetti_haarMeasure d)).toOp = (1 / P.trace) • P := by
    rw [← deFinettiState_eq_haar_integral d n]; rfl
  rw [hτ, smul_smul]
  -- The complex postselection scalar is the coercion of the real factor `g`.
  rw [show ((((n : ℝ) + 1 : ℝ) : ℂ)) ^ (d ^ 2 - 1) = ((((n : ℝ) + 1 : ℝ) ^ (d ^ 2 - 1) : ℝ) : ℂ)
      from (Complex.ofReal_pow _ _).symm]
  set g : ℝ := ((n : ℝ) + 1 : ℝ) ^ (d ^ 2 - 1) with hg_def
  -- Split `(g / Tr P) • P − ρ = ((g / Tr P − 1) • P) + (P − ρ)`.
  have h_eq : ((g : ℂ) * (1 / P.trace)) • P - ρ.toOp =
      (((g : ℂ) * (1 / P.trace) - 1) • P) + (P - ρ.toOp) := by
    rw [sub_smul, one_smul]; abel
  rw [h_eq]
  -- Real part and positivity facts about `Tr P`.
  have htrP_real : P.trace.im = 0 := by rw [hP_def, symmetricProjector_trace]; simp
  have htrP_re_pos : 0 < P.trace.re := by rw [hP_def]; exact symmetricProjector_trace_re_pos d n
  have hP_psd : P.PosSemidef := by rw [hP_def]; exact symmetricProjector_posSemidef d n
  -- First summand: `((g / Tr P − 1) • P)` is PSD because `g ≥ Tr P = C(n+d−1,d−1)`.
  set t : ℝ := P.trace.re with ht_def
  have htP : P.trace = (t : ℂ) :=
    Complex.ext (Complex.ofReal_re _).symm (by simp [htrP_real, ht_def])
  have hfirst : (((g : ℂ) * (1 / P.trace) - 1) • P).PosSemidef := by
    have h_sc : ((g : ℂ) * (1 / P.trace) - 1) • P =
        (((g / t - 1 : ℝ)) : ℂ) • P := by
      congr 1
      rw [htP]
      push_cast
      ring
    rw [h_sc]
    apply hP_psd.smul
    rw [Complex.zero_le_real, sub_nonneg, le_div_iff₀ htrP_re_pos, one_mul]
    rw [ht_def, hP_def, symmetricSubspace_dim, hg_def]
    -- `C(n+d−1, d−1) ≤ (n+1)^(d²−1)`.
    have hd1 : (Nat.choose (n + d - 1) (d - 1) : ℝ) ≤ (n + 1 : ℝ) ^ (d - 1) := by
      have h := choose_add_le_pow_succ n (d - 1)
      have hnd : n + (d - 1) = n + d - 1 := by
        have : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
        omega
      rw [hnd] at h
      calc (Nat.choose (n + d - 1) (d - 1) : ℝ)
          ≤ (((n + 1) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast h
        _ = (n + 1 : ℝ) ^ (d - 1) := by push_cast; ring
    have hexp : (n + 1 : ℝ) ^ (d - 1) ≤ (n + 1 : ℝ) ^ (d ^ 2 - 1) := by
      apply pow_le_pow_right₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))
      have : d ≤ d ^ 2 := Nat.le_self_pow (by norm_num) d
      omega
    linarith
  -- Second summand: `(P − ρ)` is PSD by projector domination of symmetric-support states.
  have hsecond : (P - ρ.toOp).PosSemidef :=
    projector_sub_psd_of_support P ρ.toOp hP_idem hP_herm
      (posSemidefOp_implies_mathlib ρ.toPosSemidefOp)
      (by rw [ρ.trace_one]; simp) hsupp
  exact hfirst.add hsecond

/-- **Trace-pairing corollary of the postselection operator bound.**

Given the postselection operator bound `g • τ − ρ ⪰ 0` (with `τ = ∫ σ^{⊗n} dν` the de
Finetti mixture and `g` the postselection factor) and **any** positive-semidefinite
measurement operator `M` (e.g. an acceptance projector `0 ≤ M`), the real trace pairing is
dominated multiplicatively:

  `Tr(M ρ) ≤ g · Tr(M τ)`.

Proof: `Tr(M (g•τ − ρ)) = g·Tr(M τ) − Tr(M ρ) ≥ 0` since the product of two PSD operators
has nonnegative real trace (`trace_mul_psd_nonneg`).  Only PSD-ness of `M` is needed for this
direction; the customary `M ≤ 1` is not required here. -/
theorem deFinetti_postselection_traceMul_le {d : ℕ} [NeZero d] (n : ℕ) [NeZero n] [NeZero (d ^ n)]
    (ρ : DensityOp (d ^ n)) (ν : DensityMeasure d) (g : ℝ)
    (hbound : (((g : ℝ) : ℂ) • (integralTensorPower n ν).toOp - ρ.toOp).PosSemidef)
    (M : Op (d ^ n)) (hM : M.PosSemidef) :
    (M * ρ.toOp).trace.re ≤ g * (M * (integralTensorPower n ν).toOp).trace.re := by
  have hnn : 0 ≤ (M * (((g : ℝ) : ℂ) • (integralTensorPower n ν).toOp - ρ.toOp)).trace.re :=
    Quantum.Operators.trace_mul_psd_nonneg M _ hM hbound
  have hexp :
      (M * (((g : ℝ) : ℂ) • (integralTensorPower n ν).toOp - ρ.toOp)).trace.re =
        g * (M * (integralTensorPower n ν).toOp).trace.re - (M * ρ.toOp).trace.re := by
    rw [mul_sub, Matrix.mul_smul, trace_sub, trace_smul]
    simp [Complex.sub_re]
  rw [hexp] at hnn
  linarith
end InfoTheory.DeFinetti

end
