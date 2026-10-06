import Mathlib.Data.Nat.Choose.Bounds
import QCryptLean.Quantum.Channels.CPTP.DiamondNorm
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Paired
import QCryptLean.Quantum.Symmetry.Covariance

/-!
# CKR Postselection Reduction — channel-agnostic security predicate and exact-binomial bound

The channel-agnostic (d-generic, `Δ`-generic) core of the Christandl-König-Renner
postselection reduction: the `ε`-security predicate `IsProtocolSecure`, the exact
symmetric-subspace CKR correction scalar `ckrSecurityCorrectionExact`, the exact-binomial
core bound `diamondNorm_le_symDim_mul_ckrTraceNorm`, and the postselection reduction theorem
`ckr_security_reduction_exact` that combines them.

None of the content here mentions BB84, a QKD transcript, or any protocol-level object — `Δ` is
an arbitrary linear map `Op (d ^ n) →ₗ[ℂ] Op dimOut` for arbitrary `d`, so the generic reduction
is available to any `Quantum/`-pathed module (e.g. the tight postselection bound in
`TightPostselectionBound.lean`) without importing the protocol layer.

`choose_add_le_pow_succ_real` is the real-valued form of Mathlib’s binomial bound
`Nat.choose_add_le_add_one_pow`: `C(n+k,k) ≤ (n+1)^k`.

## Main definitions
- `IsProtocolSecure`: ε-security against general attacks (`diamondNorm Δ ≤ ε`)
- `ckrSecurityCorrectionExact`: CKR security correction at the exact symmetric-subspace
  dimension `g_{n,d} = C(n + d² − 1, d² − 1)`

## Main statements
- `Nat.choose_add_le_add_one_pow` and `choose_add_le_pow_succ_real`: binomial bounds
  `C(n + k, k) ≤ (n + 1)^k`
- `diamondNorm_le_symDim_mul_ckrTraceNorm`: CKR core bound with exact binomial coefficient
  (CKR 2009, Theorem 1 + Lemma 1)
- `ckr_security_reduction_exact`: CKR security reduction at the exact symmetric-subspace
  dimension (CKR 2009, Theorem 1 + Lemma 1)

## References
- Christandl-König-Renner (2009) "Postselection technique for quantum channels", Theorem 1
  and Lemma 1.
-/

open Quantum.Operators
open Quantum.Symmetry
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- Real-valued form of the binomial dimension bound
`C(n + k, k) ≤ (n + 1)^k`. -/
lemma choose_add_le_pow_succ_real (n k : ℕ) :
    (Nat.choose (n + k) k : ℝ) ≤ (n + 1 : ℝ) ^ k := by
  have h :
      (Nat.choose (n + k) k : ℝ) ≤ (((n + 1) ^ k : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.choose_add_le_add_one_pow n k)
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using h

/-- A QKD protocol is **ε-secure** if the diamond norm of the difference
    map Δ = E - F between real and ideal protocol is at most ε:
      ‖Δ‖_◇ ≤ ε

    Reference: CKR (2009) arXiv:0809.3019, eq. below (8). -/
def IsProtocolSecure {d n dimOut : ℕ} [NeZero d] [NeZero n] [NeZero dimOut]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut) (ε : ℝ) : Prop :=
  diamondNorm Δ ≤ ε

/-- **CKR security correction at the exact symmetric-subspace dimension** (d-generic).

    The constant the postselection technique actually produces is the dimension of the symmetric
    subspace `Sym^n(ℂ^{d²})`,

    `g_{n,d} = C(n + d² − 1, d² − 1)` .

    The polynomial bound `C(n + k, k) ≤ (n+1)^k` (`Nat.choose_add_le_add_one_pow`) loosens this
    scalar by a factor approaching `(d² − 1)!`; for BB84 (`d = 4`, `d² − 1 = 15`) that factor is
    `15! ≈ 1.307·10¹²`, i.e. `40.25` bits of budget lost by applying the loosening.

    Reference: Christandl–König–Renner (2009) `arXiv:0809.3019`, Theorem 1 and Lemma 1, where the
    constant is `g_{n,d}`. -/
noncomputable def ckrSecurityCorrectionExact (d n : ℕ) (ε_coll : ℝ) : ℝ :=
  (Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℝ) * ε_coll

/-- The exact CKR security correction is non-negative. -/
lemma ckrSecurityCorrectionExact_nonneg (d n : ℕ) (ε_coll : ℝ) (hε : 0 ≤ ε_coll) :
    0 ≤ ckrSecurityCorrectionExact d n ε_coll :=
  mul_nonneg (Nat.cast_nonneg _) hε

/-- CKR core bound with the exact symmetric-subspace dimension.

For a permutation-covariant, Hermiticity-preserving map `Δ` on `(ℂ^d)^⊗n` and a
de Finetti purification `τ`,
`‖Δ‖_◇ ≤ C(n + d² - 1, d² - 1) * ‖(Δ ⊗ id_R)(τ)‖₁`.
The hypothesis `hΔ_conj` expresses Hermiticity preservation by commutation with
conjugate transpose; it holds for differences of quantum channels.

The symmetric subspace is `Sym^n(ℂ^d ⊗ ℂ^d)`, of dimension
`g_{n,d} = C(n + d² - 1, d² - 1)`. CKR's Lemma 1 gives the equality
`ρ = g_{n,d} * (id ⊗ T)(ω)` for a state supported on this subspace, a purification
`ω` of its maximally mixed state, and a trace-non-increasing map `T` from the
purifying system to the scalars. Symmetric reduction and trace-norm contraction
then give the bound.

Reference: CKR (2009), arXiv:0809.3019, `main.tex`, Theorem 1
(`\label{thm:main}`) and Lemma 1 (`\label{lem:extractpart}`, `\label{eq:substate}`). -/
theorem diamondNorm_le_symDim_mul_ckrTraceNorm {d n dimOut dimR : ℕ}
    [NeZero d] [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ : PermutationCovariant Δ)
    (hΔ_conj : ∀ M : Op (d ^ n), Δ M.conjTranspose = (Δ M).conjTranspose)
    (τ : DensityOp ((d ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ) :
    diamondNorm Δ ≤
      ↑(Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1)) * ckrTensorTraceNorm Δ τ := by
  -- The diamond norm is sSup of a set; bound each element
  unfold diamondNorm
  have : NeZero (d ^ n * (d ^ n)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  have : NeZero (dimOut * (d ^ n)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))⟩
  apply csSup_le
  -- Nonemptiness: X = 0 gives element 0
  · exact ⟨0, 0, by rw [traceNorm_zero]; exact zero_le_one,
      by rw [mapTensorId_zero, traceNorm_zero]⟩
  -- For each element: ‖(Δ⊗id)(X)‖₁ ≤ C(n+d²-1,d²-1) · ‖(Δ⊗id_R)(τ)‖₁
  · intro t ⟨X₀, hX₀_norm, ht_eq⟩
    rw [ht_eq]
    -- Apply the CKR per-operator bound (factored into CKRBound.lean)
    unfold ckrTensorTraceNorm
    exact Quantum.Channels.ckr_per_operator_bound_paired_core Δ X₀ hX₀_norm τ
      hΔ_conj hΔ.covariance hτ

/-- **CKR security reduction at the exact symmetric-subspace dimension** (CKR 2009, Theorem 1 +
Lemma 1).

States the reduction at the constant the postselection argument actually produces: the
dimension of the symmetric subspace `Sym^n(ℂ^{d²})`,

`g_{n,d} = C(n + d² − 1, d² − 1)` ,

in place of the polynomial upper bound `(n+1)^{d²−1}` obtained by composing with
`Nat.choose_add_le_add_one_pow`; the two differ by a factor `(d²−1)!` in the limit (`1.3·10¹²` at
`d = 4`), so applying that loosening is a pure loss and is not done here.

Reference: CKR (2009) `arXiv:0809.3019`, `main.tex:268`–`:401` (\emph{Main Result}: the
Post-Selection Theorem `\label{thm:main}` :291–:301, the substate-extraction Lemma
`\label{lem:extractpart}` :319–:328), where the constant is the symmetric-subspace dimension
`g_{n,d}`. -/
theorem ckr_security_reduction_exact (d : ℕ) [NeZero d] {n dimOut dimR : ℕ}
    [NeZero n] [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (hΔ : PermutationCovariant Δ)
    (hΔ_conj : ∀ M : Op (d ^ n), Δ M.conjTranspose = (Δ M).conjTranspose)
    (τ : DensityOp ((d ^ n) * dimR))
    (hτ : IsCKRDeFinettiPurification τ)
    (ε_coll : ℝ)
    (hbound : ckrTensorTraceNorm Δ τ ≤ ε_coll) :
    IsProtocolSecure Δ (ckrSecurityCorrectionExact d n ε_coll) := by
  unfold IsProtocolSecure ckrSecurityCorrectionExact
  calc diamondNorm Δ
      ≤ (Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℝ) * ckrTensorTraceNorm Δ τ :=
        diamondNorm_le_symDim_mul_ckrTraceNorm Δ hΔ hΔ_conj τ hτ
    _ ≤ (Nat.choose (n + (d ^ 2 - 1)) (d ^ 2 - 1) : ℝ) * ε_coll :=
        mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)

end Quantum.Channels
