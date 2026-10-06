import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.SmoothUncertaintyRelation
import QCryptLean.InfoTheory.SmoothMinEntropy.Uncertainty.ConcreteMeasurementBases

/-!
# Worked instances of the entropic uncertainty relations

The relations of `MeasurementTransport.lean` and `SmoothUncertaintyRelation.lean` are stated for an
arbitrary pair of rank-one projective measurements.  This file instantiates them at the standard
pair — the computational basis and the `n`-qubit Walsh–Hadamard basis of `ℂ^{2ⁿ}`, which are
mutually unbiased — where the preparation quality is exactly `n`
(`RankOneProjectiveBasis.preparationQuality_computational_walsh`).  At `n = 1` this is the BB84
pair with `q = 1`.

It also records the matching **negative** instance: the nonvanishing hypothesis of the `ε = 0`
relation is not removable, because at `ρ_AB = 0` both sides collapse to the `Real.log 0 = 0`
sentinel and the inequality becomes `0 ≤ −n`.

## Main statements

* `InfoTheory.SmoothMinEntropy.measDilation_pure_core_computational_walsh`
* `InfoTheory.SmoothMinEntropy.measDilation_smooth_core_computational_walsh`
* `InfoTheory.SmoothMinEntropy.measDilation_pure_core_computational_walsh_fails_at_zero`
-/

open Quantum.Operators Quantum.TensorProducts
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open RankOneProjectiveBasis

variable {n dB : ℕ}

/-- **The `ε = 0` uncertainty relation for `n` qubits measured in the computational or
Walsh–Hadamard basis:**

`H_min(Z|Z′AB)_ρ ≤ H_min(X|B)_ρ − n` .

The mutually-unbiased pair has `c = 2^{-n}`, hence `q = n`
(`preparationQuality_computational_walsh`). -/
theorem measDilation_pure_core_computational_walsh [NeZero dB]
    (ρAB : SubDensityOp (2 ^ n * dB)) (hρ : ρAB.toOp ≠ 0) :
    bipartiteMinEntropyOptReal (zDilatedState (walsh n) ρAB) ≤
      bipartiteMinEntropyOptReal (xMeasuredMarginal (computational (2 ^ n)) ρAB) - (n : ℝ) := by
  have h := measDilation_pure_core (computational (2 ^ n)) (walsh n) ρAB hρ
  rwa [preparationQuality_computational_walsh] at h

/-- **The ε-smooth uncertainty relation for `n` qubits measured in the computational or
Walsh–Hadamard basis:**

`H_min^ε(Z|Z′AB)_ρ ≤ H_min^ε(X|B)_ρ − n` ,

for a normalized `ρ_AB` and a smoothing radius `ε < 1`. No regularity hypothesis is carried; see
`measDilation_smooth_core`. -/
theorem measDilation_smooth_core_computational_walsh [NeZero dB]
    (ρAB : SubDensityOp (2 ^ n * dB)) (hρ : ρAB.trace = 1) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) :
    smoothBipartiteMinEntropyOptReal ε (zDilatedState (walsh n) ρAB) ≤
      smoothBipartiteMinEntropyOptReal ε
          (xMeasuredMarginal (computational (2 ^ n)) ρAB) - (n : ℝ) := by
  have h := measDilation_smooth_core (computational (2 ^ n)) (walsh n) ρAB hρ hε hε1
  rwa [preparationQuality_computational_walsh] at h

/-- **The nonvanishing hypothesis is necessary, at explicit objects.** For `n ≥ 1` qubits measured
in the computational or Walsh–Hadamard basis the `ε = 0` relation fails at `ρ_AB = 0`: the
`Real.log 0 = 0` sentinel makes both sides `0`, so the conclusion would assert `0 ≤ −n`. -/
theorem measDilation_pure_core_computational_walsh_fails_at_zero [NeZero dB] (hn : 0 < n) :
    ¬ (bipartiteMinEntropyOptReal (zDilatedState (walsh n) (0 : SubDensityOp (2 ^ n * dB))) ≤
        bipartiteMinEntropyOptReal
            (xMeasuredMarginal (computational (2 ^ n)) (0 : SubDensityOp (2 ^ n * dB)))
          - (n : ℝ)) := by
  have hq : 0 < (computational (2 ^ n)).preparationQuality (walsh n) := by
    rw [preparationQuality_computational_walsh]
    exact_mod_cast hn
  have h := measDilation_pure_core_fails_at_zero (dB := dB) (computational (2 ^ n)) (walsh n) hq
  rwa [preparationQuality_computational_walsh] at h

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
