import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.MeasurementDilation
import QCryptLean.Quantum.Bases.WalshHadamard

/-!
# Concrete rank-one projective measurements: the computational and Walsh–Hadamard bases

`RankOneProjectiveBasis` (in `MeasurementDilation.lean`)
packages an orthonormal basis together with its resolution of the identity, and carries the
measurement-dilation and overlap-constant API used by the entropic-uncertainty layer.  Until now
the structure had no instance in the library, so every statement about it was conditional on data
that was never exhibited.  This file supplies the two standard instances and computes their
overlap constant:

* `RankOneProjectiveBasis.computational d` — the computational (`Z`-) basis of `ℂ^d`;
* `RankOneProjectiveBasis.walsh n` — the `n`-qubit Walsh–Hadamard (`X`-) basis of `ℂ^{2ⁿ}`,
  re-indexed along the binary-digit equivalence `Quantum.Bases.bitIndex`;
* `RankOneProjectiveBasis.overlapConst_computational_walsh` — their overlap constant is `2^{-n}`,
  the smallest value attainable in dimension `2ⁿ`.

In particular the bounds of `MeasurementDilation.lean` — for instance
`sqrtN_M_sqrtN_opLe_overlapConst_smul_one`, which asserts `√N_z M_x √N_z ⪯ c · 1` — are now known
to be non-vacuous and to be attained at a genuinely small constant: for `n = 1` this is the BB84
pair with `c = 1/2`.

## Main definitions

* `InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis.computational`
* `InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis.walsh`

## Main statements

* the computational-basis completeness relation `∑_i |i⟩⟨i| = 1` is
  `Quantum.Operators.stdKet_complete`, with the standard-basis projectors' home.
* `InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis.overlapConst_computational_walsh` —
  `c(Z, X^{⊗n}) = 2^{-n}`.
-/

open Quantum.Operators Quantum.Bases Matrix
open scoped BigOperators ComplexConjugate

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The two concrete bases -/

namespace RankOneProjectiveBasis

/-- **The computational basis** `{|i⟩}` of `ℂ^d` as a rank-one projective measurement. -/
def computational (d : ℕ) : RankOneProjectiveBasis d where
  vec := stdKet d
  orthonormal := stdKet_braket d
  complete := stdKet_complete d

@[simp] lemma computational_vec (d : ℕ) (i : Fin d) : (computational d).vec i = stdKet d i := rfl

/-- **The `n`-qubit Walsh–Hadamard basis** of `ℂ^{2ⁿ}` as a rank-one projective measurement,
indexed by `Fin (2ⁿ)` through the binary-digit equivalence `Quantum.Bases.bitIndex`.  Physically
this is the BB84 `X`-basis measurement on `n` qubits. -/
def walsh (n : ℕ) : RankOneProjectiveBasis (2 ^ n) where
  vec e := walshKet (bitIndex n e)
  orthonormal i j := by
    rw [walshKet_orthonormal]
    by_cases h : i = j
    · rw [if_pos h, if_pos (congrArg (bitIndex n) h)]
    · rw [if_neg h, if_neg fun hb => h ((bitIndex n).injective hb)]
  complete := by
    rw [Equiv.sum_comp (bitIndex n) fun e => walshKet e * (walshKet e).dag]
    exact walshKet_complete

@[simp] lemma walsh_vec (n : ℕ) (e : Fin (2 ^ n)) :
    (walsh n).vec e = walshKet (bitIndex n e) := rfl

/-! ## The overlap constant of the pair -/

/-- **The computational and Walsh–Hadamard bases are mutually unbiased**, in the `Fin (2ⁿ)`
indexing used by `RankOneProjectiveBasis`. -/
theorem normSq_overlap_computational_walsh (n : ℕ) (x z : Fin (2 ^ n)) :
    Complex.normSq (((computational (2 ^ n)).vec x).dag * (walsh n).vec z) =
      1 / ((2 ^ n : ℕ) : ℝ) :=
  stdKet_walshKet_mutuallyUnbiased n x (bitIndex n z)

/-- **The overlap constant of the `Z`/`X^{⊗n}` pair is `2^{-n}`.**

`overlapConst P Q = max_{x,z} |⟨x|z⟩|²` is by definition a maximum over a nonempty index set; here
every entry equals `2^{-n}` by mutual unbiasedness, so the maximum is `2^{-n}`.  At `n = 1` this
is the familiar BB84 value `1/2`, and it de-vacuates
`RankOneProjectiveBasis.sqrtN_M_sqrtN_opLe_overlapConst_smul_one`. -/
theorem overlapConst_computational_walsh (n : ℕ) :
    overlapConst (computational (2 ^ n)) (walsh n) = 1 / ((2 ^ n : ℕ) : ℝ) := by
  unfold overlapConst
  rw [show (fun p : Fin (2 ^ n) × Fin (2 ^ n) =>
      Complex.normSq (((computational (2 ^ n)).vec p.1).dag * (walsh n).vec p.2)) =
      fun _ : Fin (2 ^ n) × Fin (2 ^ n) => 1 / ((2 ^ n : ℕ) : ℝ) from
    funext fun p => normSq_overlap_computational_walsh n p.1 p.2]
  exact Finset.sup'_const _ _

/-- **The preparation quality of the `Z`/`X^{⊗n}` pair is `n`.**

`q = log₂(1/c) = log₂ 2ⁿ = n`: each of the `n` mutually-unbiased qubits contributes one bit. This
de-vacuates `RankOneProjectiveBasis.preparationQuality`, and it is the quantity the uncertainty
relations of `MeasurementTransport.lean` and `SmoothUncertaintyRelation.lean` subtract. At `n = 1`
it is the familiar BB84 value `q = 1`. -/
theorem preparationQuality_computational_walsh (n : ℕ) :
    (computational (2 ^ n)).preparationQuality (walsh n) = (n : ℝ) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  unfold preparationQuality
  rw [overlapConst_computational_walsh, hcast, one_div, Real.log_inv, Real.log_pow, neg_neg]
  field_simp

end RankOneProjectiveBasis

end InfoTheory.SmoothMinEntropy

end
