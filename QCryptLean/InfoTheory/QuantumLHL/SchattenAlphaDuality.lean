import QCryptLean.InfoTheory.QuantumLHL.SchattenAlpha
import QCryptLean.InfoTheory.SmoothMinEntropy.Basic.CfcSpectral
import QCryptLean.Math.SpectralTheory.HermitianCpow
import QCryptLean.Quantum.Metrics.PolarUnitary
import QCryptLean.Quantum.Metrics.TraceOpNormBound

/-!
# Schatten-α: singular-value form, complex spectral powers, duality, Hölder

The Schatten-α infrastructure the
Rényi-α leftover-hash moment inequality is assembled from. `schattenPow` and
`renyiCollisionQuantity` are defined in `SchattenAlpha.lean`.

## Main declarations

Real powers of positive semidefinite matrices (`CFC.rpow` bookkeeping absent from Mathlib
at singular arguments):
- `posSemidef_rpow_add_of_pos` : `X ^ (x + y) = X ^ x * X ^ y` for `0 < x`, `0 < y` — the
  invertibility hypothesis of `CFC.rpow_add` is not needed at strictly positive exponents.
- `posSemidef_rpow_smul` : `(r • X) ^ q = r ^ q • X ^ q` for `0 ≤ r`.
- `posSemidef_rpow_conj` : `(Uᴴ X U) ^ q = Uᴴ (X ^ q) U` for unitary `U`.
(The spectral trace formula `Re Tr (X ^ q) = ∑ᵢ λᵢ ^ q` these use is
`Math.SpectralTheory.trace_posSemidef_rpow_re`.)

Singular values and the Schatten power sum:
- `singularValues` : `sᵢ(A) = √(λᵢ(Aᴴ A))`, so that `traceNorm A = ∑ᵢ sᵢ(A)`
  (`traceNorm_eq_sum_singularValues`).
- `schattenPow_eq_sum_singularValues` : `schattenPow α A = ∑ᵢ sᵢ(A) ^ α`.
- `schattenPow_one` : `schattenPow 1 A = traceNorm A`, the `α = 1` anchor.
- `schattenPow_smul`, `schattenPow_unitary_mul_left`, `schattenPow_pos_of_ne_zero`.

Complex spectral powers (the Hadamard three-lines interpolation needs `|A| ^ w` for `w ∈ ℂ`). The
spectral
power `Math.SpectralTheory.hermCpow` and its algebra — exponent additivity, imaginary
unitarity, the `CFC.rpow` and monoid-power anchors, the adjoint and Gram laws — live in
`QCryptLean.Math.SpectralTheory.HermitianCpow`. The Schatten bridge is here:
- `schattenPow_hermCpow` : `‖X ^ w‖_p^p = Re Tr (X ^ (p Re w))` for `0 < Re w`. The
  hypothesis is load-bearing on a singular `X`; at `Re w = 0` the Gram matrix
  `(X ^ w)ᴴ (X ^ w)` is the support projection, not `X ^ 0 = 1`.

Duality with an explicit witness and the two per-block Hölder wrappers:
- `schattenPow_eq_trace_dual_witness` : explicit dual witness
  `B = t^{1-α} · |Y|^{α-1} U` built from the polar decomposition — no von Neumann trace
  inequality is used.
- `norm_trace_mul_le_opNorm_mul_schattenPow_one` : Hölder `(∞, 1)`.
- `norm_trace_mul_sq_le_schattenPow_two_mul` : Hölder `(2, 2)`.

Not in this file: the analytic family and the Hadamard three-lines interpolation that
consume the above.
-/

open Quantum.Operators Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace InfoTheory.QuantumLHL

variable {n : ℕ}

/-!
## Real powers of positive semidefinite matrices
-/

/-- **Additivity of `CFC.rpow` at strictly positive exponents.** Mathlib's `CFC.rpow_add`
assumes `IsUnit a`, which fails for a singular positive semidefinite matrix; at strictly
positive exponents the identity `t ^ (x + y) = t ^ x * t ^ y` holds on all of `ℝ≥0`
(both sides vanish at `t = 0`), so no invertibility is needed. -/
theorem posSemidef_rpow_add_of_pos {X : Op n} (hX : X.PosSemidef) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) : X ^ (x + y) = X ^ x * X ^ y := by
  have hXn : (0 : Op n) ≤ X := hX.nonneg
  simp only [CFC.rpow_def]
  rw [← cfc_mul _ _ X ((NNReal.continuous_rpow_const hx.le).continuousOn)
    ((NNReal.continuous_rpow_const hy.le).continuousOn)]
  refine cfc_congr fun z _ => ?_
  exact NNReal.rpow_add' (by positivity) z

/-- **Homogeneity of `CFC.rpow`.** For `0 ≤ r` and positive semidefinite `X`,
`(r • X) ^ q = r ^ q • X ^ q`. The scalar factors out because `r • X = (r • 1) * X` with
`r • 1` positive semidefinite and central. -/
theorem posSemidef_rpow_smul {X : Op n} (hX : X.PosSemidef) {r : ℝ} (hr : 0 ≤ r) (q : ℝ) :
    (((r : ℂ) • X) ^ q) = ((r ^ q : ℝ) : ℂ) • (X ^ q) := by
  have hscal : ∀ c : ℝ, 0 ≤ c → ∀ y : ℝ,
      (((c : ℂ) • (1 : Op n)) ^ y) = ((c ^ y : ℝ) : ℂ) • (1 : Op n) := by
    intro c hc y
    have halg : ∀ t : NNReal, algebraMap NNReal (Op n) t = ((t : ℝ) : ℂ) • (1 : Op n) := by
      intro t
      rw [Algebra.algebraMap_eq_smul_one, NNReal.smul_def, ← Complex.coe_smul]
    have hc' : ((c.toNNReal : ℝ) : ℂ) = (c : ℂ) := by rw [Real.coe_toNNReal c hc]
    rw [← hc', ← halg, CFC.rpow_algebraMap, halg, NNReal.coe_rpow, Real.coe_toNNReal c hc]
  have hone : ((r : ℂ) • (1 : Op n)).PosSemidef := by
    have : ((r : ℂ) • (1 : Op n)) = ((r.toNNReal : ℝ) : ℂ) • (1 : Op n) := by
      rw [Real.coe_toNNReal r hr]
    rw [this]
    exact (Matrix.PosSemidef.one).smul (by positivity)
  have hcomm : Commute ((r : ℂ) • (1 : Op n)) X := by
    simp [Commute, SemiconjBy]
  have hprod : ((r : ℂ) • X) = ((r : ℂ) • (1 : Op n)) * X := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [hprod, CfcSpectral.matrix_rpow_mul_of_commute _ _ hone.nonneg hX.nonneg hcomm q,
    hscal r hr q, Matrix.smul_mul, Matrix.one_mul]

/-- **Unitary equivariance of `CFC.rpow`.** For a unitary `U` and positive semidefinite `X`,
`(Uᴴ X U) ^ q = Uᴴ (X ^ q) U`. -/
theorem posSemidef_rpow_conj {X : Op n} (hX : X.PosSemidef) {U : Op n}
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (q : ℝ) :
    ((Uᴴ * X * U) ^ q) = Uᴴ * (X ^ q) * U := by
  have hu : Uᴴ ∈ unitary (Op n) := by
    constructor
    · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]; exact hU2
    · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]; exact hU1
  set u : unitary (Op n) := ⟨Uᴴ, hu⟩ with hu_def
  have hconj : ∀ Z : Op n, Unitary.conjStarAlgAut ℂ _ u Z = Uᴴ * Z * U := by
    intro Z
    rw [Unitary.conjStarAlgAut_apply]
    change Uᴴ * Z * star Uᴴ = Uᴴ * Z * U
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hXq : ((Uᴴ * X * U)).PosSemidef := hX.conjTranspose_mul_mul_same U
  rw [CFC.rpow_eq_cfc_real hXq.nonneg, ← hconj X,
    Math.SpectralTheory.cfc_conjStarAlgAut X hX.1 u (fun t => t ^ q), hconj,
    ← CFC.rpow_eq_cfc_real hX.nonneg]

/-!
## Singular values and the Schatten power sum
-/

/-- **Singular values.** `singularValues A i = √(λᵢ(Aᴴ A))`, in the eigenvalue indexing of
`Matrix.IsHermitian.eigenvalues` for the positive semidefinite Gram matrix `Aᴴ A`. The
trace norm is their sum (`traceNorm_eq_sum_singularValues`) and `schattenPow α A` is the
sum of their `α`-th powers (`schattenPow_eq_sum_singularValues`). -/
def singularValues (A : Op n) (i : Fin n) : ℝ :=
  Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).1.eigenvalues i)

theorem singularValues_nonneg (A : Op n) (i : Fin n) : 0 ≤ singularValues A i :=
  Real.sqrt_nonneg _

/-- The trace norm is the sum of the singular values — the project's `traceNorm` is
literally this sum. -/
theorem traceNorm_eq_sum_singularValues [NeZero n] (A : Op n) :
    Quantum.Metrics.traceNorm A = ∑ i, singularValues A i := rfl

/-- **Singular-value form of `schattenPow`**: `‖A‖_α^α = ∑ᵢ sᵢ(A) ^ α`. -/
theorem schattenPow_eq_sum_singularValues (α : ℝ) (A : Op n) :
    schattenPow α A = ∑ i, singularValues A i ^ α := by
  rw [schattenPow,
    Math.SpectralTheory.trace_posSemidef_rpow_re (Matrix.posSemidef_conjTranspose_mul_self A)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [singularValues, Real.sqrt_eq_rpow,
    ← Real.rpow_mul ((Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i)]
  ring_nf

/-- **`α = 1` anchor for `schattenPow`.** `schattenPow 1 A = traceNorm A`: the exponent
`α/2` is `1/2`, and `CFC.rpow` at `1/2` is `CFC.sqrt`. -/
theorem schattenPow_one [NeZero n] (A : Op n) :
    schattenPow 1 A = Quantum.Metrics.traceNorm A := by
  rw [schattenPow, Quantum.Metrics.traceNorm_eq_re_trace_cfcSqrt_conjTranspose_mul A,
    CFC.sqrt_eq_rpow]

/-- **Homogeneity of `schattenPow`.** `‖r • A‖_α^α = r^α ‖A‖_α^α` for a nonnegative real
scalar `r`. -/
theorem schattenPow_smul (p : ℝ) {r : ℝ} (hr : 0 ≤ r) (A : Op n) :
    schattenPow p ((r : ℂ) • A) = r ^ p * schattenPow p A := by
  have hgram : (((r : ℂ) • A)ᴴ * ((r : ℂ) • A)) = (((r ^ 2 : ℝ) : ℂ)) • (Aᴴ * A) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num
    ring_nf
  rw [schattenPow, hgram,
    posSemidef_rpow_smul (Matrix.posSemidef_conjTranspose_mul_self A) (by positivity) (p / 2),
    Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, schattenPow]
  congr 1
  rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr]
  congr 1
  push_cast
  ring

/-- **Left unitary invariance of `schattenPow`.** The Gram matrix `(U A)ᴴ (U A)` is `Aᴴ A`. -/
theorem schattenPow_unitary_mul_left (p : ℝ) (U : UnitaryOp n) (A : Op n) :
    schattenPow p (U.toOp * A) = schattenPow p A := by
  have h : ((U.toOp * A)ᴴ * (U.toOp * A)) = Aᴴ * A := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U.toOpᴴ,
      U.unitary_left, Matrix.one_mul]
  rw [schattenPow, schattenPow, h]

/-- **Strict positivity.** `schattenPow α A > 0` whenever `A ≠ 0`. No sign condition on
`α` is needed: `∑ᵢ λᵢ ^ (α/2) = 0` forces every `λᵢ` to vanish for *any* exponent
(`Real.rpow_eq_zero_iff_of_nonneg`), hence `Aᴴ A = 0` and `A = 0`. -/
theorem schattenPow_pos_of_ne_zero (α : ℝ) {A : Op n} (hA : A ≠ 0) :
    0 < schattenPow α A := by
  set hG := Matrix.posSemidef_conjTranspose_mul_self A with hG_def
  rw [schattenPow, Math.SpectralTheory.trace_posSemidef_rpow_re hG]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hG.eigenvalues_nonneg i) _)
    fun hsum => hA ?_
  have hall : ∀ i, hG.1.eigenvalues i ^ (α / 2 : ℝ) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Real.rpow_nonneg (hG.eigenvalues_nonneg j) _)).mp hsum.symm i (Finset.mem_univ i)
  have hzero : hG.1.eigenvalues = 0 := by
    funext i
    have := hall i
    rcases Real.rpow_eq_zero_iff_of_nonneg (hG.eigenvalues_nonneg i) |>.mp this with ⟨h0, _⟩
    exact h0
  exact Matrix.conjTranspose_mul_self_eq_zero.mp
    ((Matrix.IsHermitian.eigenvalues_eq_zero_iff hG.1).mp hzero)

/-!
## Complex spectral powers and their Schatten norms
-/

/-- **Schatten power of a complex spectral power** (boundary form).
For `0 ≤ p` and `0 < Re w`, `‖X ^ w‖_p^p = Re Tr (X ^ (p · Re w))`: on the interpolation
strip the Schatten norms of the analytic family `w ↦ X ^ w`
(`Math.SpectralTheory.hermCpow`) depend on `w` only through `Re w`. -/
theorem schattenPow_hermCpow {X : Op n} (hX : X.PosSemidef) {w : ℂ} (hw : 0 < w.re)
    {p : ℝ} (hp : 0 ≤ p) :
    schattenPow p (Math.SpectralTheory.hermCpow hX.1 w) = ((X ^ (p * w.re)).trace).re := by
  rw [schattenPow, Math.SpectralTheory.posSemidef_hermCpow_gram hX hw,
    CFC.rpow_rpow_of_exponent_nonneg X (2 * w.re) (p / 2) (by positivity) (by positivity)
      hX.nonneg,
    show (2 * w.re) * (p / 2) = p * w.re from by ring]

/-!
## Schatten-α duality with an explicit dual witness
-/

/-- **Schatten-α duality, explicit witness**. For `1 < α`, conjugate
exponent `α' = α/(α-1)`, and `Y ≠ 0`, there is `B` with `‖B‖_{α'}^{α'} = 1` and
`Re Tr (B Y) = (‖Y‖_α^α)^{1/α} = ‖Y‖_α`.

The witness is written down rather than obtained from a variational principle: with the
polar decomposition `Y = Uᴴ |Y|`, `|Y| = (Yᴴ Y)^{1/2}`, and `t = (‖Y‖_α^α)^{1/α}`, it is
`B = t^{1-α} · |Y|^{α-1} U`. Only `CFC.rpow` and the polar unitary enter, so **no von
Neumann trace inequality is needed** — that is what makes the step self-contained. The two
computations are `Tr (B Y) = t^{1-α} Tr |Y|^α = t` and, since the singular values of `B`
are `t^{1-α} sᵢ^{α-1}` and `(α-1)α' = α`, `‖B‖_{α'}^{α'} = t^{-α} Tr |Y|^α = 1`. -/
theorem schattenPow_eq_trace_dual_witness {α : ℝ} (hα : 1 < α) {Y : Op n} (hY : Y ≠ 0) :
    ∃ B : Op n, schattenPow (α / (α - 1)) B = 1 ∧
      (B * Y).trace.re = (schattenPow α Y) ^ (1 / α) := by
  have hα0 : (0 : ℝ) < α := lt_trans zero_lt_one hα
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  set M : Op n := Yᴴ * Y with hM_def
  have hM : M.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Y
  -- Polar decomposition `Y = Wᴴ |Y|` with `|Y| = M ^ (1/2)`.
  obtain ⟨W, hW⟩ := Quantum.Metrics.PolarUnitary.Op.exists_unitary_polar_left Yᴴ
  have hPherm : (M ^ (1 / 2 : ℝ))ᴴ = M ^ (1 / 2 : ℝ) :=
    (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg).isHermitian.eq
  have hYpolar : Y = W.toOpᴴ * M ^ (1 / 2 : ℝ) := by
    have h := congrArg Matrix.conjTranspose hW
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, ← hM_def,
      CFC.sqrt_eq_rpow, hPherm] at h
    exact h
  -- The normalising scalars.
  set S : ℝ := schattenPow α Y with hS_def
  have hSpos : 0 < S := schattenPow_pos_of_ne_zero α hY
  set t : ℝ := S ^ (1 / α : ℝ) with ht_def
  have htpos : 0 < t := Real.rpow_pos_of_pos hSpos _
  have htα : t ^ α = S := by
    rw [ht_def, ← Real.rpow_mul hSpos.le, one_div, inv_mul_cancel₀ (ne_of_gt hα0),
      Real.rpow_one]
  set c : ℝ := t ^ (1 - α) with hc_def
  have hcpos : 0 < c := Real.rpow_pos_of_pos htpos _
  have hcS : c * S = t := by
    rw [← htα, hc_def, ← Real.rpow_add htpos]
    norm_num
  -- `Tr M ^ (α/2) = S` by definition of `schattenPow`.
  have hMtrace : ((M ^ (α / 2 : ℝ)).trace).re = S := rfl
  refine ⟨(c : ℂ) • (M ^ ((α - 1) / 2 : ℝ) * W.toOp), ?_, ?_⟩
  · -- `‖B‖_{α'}^{α'} = 1`
    have hHalf : M ^ ((α - 1) / 2 : ℝ) * M ^ ((α - 1) / 2 : ℝ) = M ^ (α - 1 : ℝ) := by
      rw [← posSemidef_rpow_add_of_pos hM (by linarith) (by linarith :
        (0:ℝ) < (α - 1) / 2)]
      norm_num
    have hMhalfHerm : (M ^ ((α - 1) / 2 : ℝ))ᴴ = M ^ ((α - 1) / 2 : ℝ) :=
      (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg).isHermitian.eq
    have hgram : (((c : ℂ) • (M ^ ((α - 1) / 2 : ℝ) * W.toOp))ᴴ *
          ((c : ℂ) • (M ^ ((α - 1) / 2 : ℝ) * W.toOp)))
        = ((c ^ 2 : ℝ) : ℂ) • (W.toOpᴴ * M ^ (α - 1 : ℝ) * W.toOp) := by
      rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hMhalfHerm, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc (M ^ ((α - 1) / 2 : ℝ)),
        hHalf, ← Matrix.mul_assoc]
      congr 1
      rw [Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    have hXpsd : (M ^ (α - 1 : ℝ)).PosSemidef := Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg
    have hconjpsd : (W.toOpᴴ * M ^ (α - 1 : ℝ) * W.toOp).PosSemidef :=
      hXpsd.conjTranspose_mul_mul_same W.toOp
    have hexp : (α - 1) * (α / (α - 1) / 2) = α / 2 := by
      field_simp
    rw [schattenPow, hgram, posSemidef_rpow_smul hconjpsd (by positivity),
      posSemidef_rpow_conj hXpsd W.unitary_left W.unitary_right,
      Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, W.unitary_right, Matrix.one_mul,
      CFC.rpow_rpow_of_exponent_nonneg M (α - 1) (α / (α - 1) / 2) (by linarith)
        (by positivity) hM.nonneg, hexp, hMtrace]
    have hcpow : (c ^ 2 : ℝ) ^ (α / (α - 1) / 2 : ℝ) = t ^ (-α) := by
      rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hcpos.le, hc_def, ← Real.rpow_mul htpos.le]
      congr 1
      push_cast
      field_simp
      ring
    rw [hcpow, ← htα, ← Real.rpow_add htpos, neg_add_cancel, Real.rpow_zero]
  · -- `Re Tr (B Y) = t`
    have hBY : ((c : ℂ) • (M ^ ((α - 1) / 2 : ℝ) * W.toOp)) * Y
        = (c : ℂ) • (M ^ (α / 2 : ℝ)) := by
      rw [hYpolar, Matrix.smul_mul]
      congr 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc W.toOp, W.unitary_right, Matrix.one_mul,
        ← posSemidef_rpow_add_of_pos hM (by linarith : (0:ℝ) < (α - 1) / 2) (by norm_num)]
      congr 1
      ring
    rw [hBY, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, hMtrace, hcS]

/-!
## Per-block Hölder wrappers
-/

/-- **Hölder `(∞, 1)` in `schattenPow` form**: `‖Tr (A B)‖ ≤ ‖A‖_∞ · ‖B‖_1`. -/
theorem norm_trace_mul_le_opNorm_mul_schattenPow_one [NeZero n] (A B : Op n) :
    ‖(A * B).trace‖ ≤ ‖A‖ * schattenPow 1 B := by
  rw [schattenPow_one]
  exact Quantum.Metrics.TraceOpNormBound.norm_trace_mul_le_opNorm_mul_traceNorm A B

/-- **Hölder `(2, 2)` in `schattenPow` form**: `‖Tr (A B)‖² ≤ ‖A‖_2² · ‖B‖_2²`. -/
theorem norm_trace_mul_sq_le_schattenPow_two_mul (A B : Op n) :
    ‖(A * B).trace‖ ^ 2 ≤ schattenPow 2 A * schattenPow 2 B := by
  have h := Quantum.Metrics.norm_trace_mul_sq_le_trace_mul_trace_conjTranspose A B
  rwa [show (A * Aᴴ).trace = (Aᴴ * A).trace from Matrix.trace_mul_comm A Aᴴ,
    ← schattenPow_two A, ← schattenPow_two B] at h

end InfoTheory.QuantumLHL

end
