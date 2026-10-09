import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Math.LinearAlgebra.GramRigidity

/-!
# Qubit dephasing has no single Kraus conjugation
-/

open Quantum.Operators Matrix
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Channels

/-- First witness Kraus operator: the qubit projector `|0⟩⟨0|`. -/
def witnessKraus₀ : Op (Fin 2) := Matrix.single 0 0 1

/-- Second witness Kraus operator: the qubit projector `|1⟩⟨1|`. -/
def witnessKraus₁ : Op (Fin 2) := Matrix.single 1 1 1

/-- The witness pair is a genuine two-outcome instrument: it satisfies the completeness relation
`∑ₓ Kₓᴴ Kₓ = 1`.  So the sum below is an honest announced step, not a filter. -/
theorem witnessKraus_complete :
    witnessKraus₀ᴴ * witnessKraus₀ + witnessKraus₁ᴴ * witnessKraus₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witnessKraus₀, witnessKraus₁]

/-- The first witness operator is nonzero. -/
theorem witnessKraus₀_ne_zero : witnessKraus₀ ≠ 0 := by
  intro hc
  have h00 := congrArg (fun M : Op (Fin 2) => M 0 0) hc
  simp [witnessKraus₀] at h00

/-- The two witness operators are **not** proportional. -/
theorem witnessKraus_not_proportional : ¬ ∃ c : ℂ, witnessKraus₁ = c • witnessKraus₀ := by
  rintro ⟨c, hc⟩
  have h11 := congrArg (fun M : Op (Fin 2) => M 1 1) hc
  simp [witnessKraus₀, witnessKraus₁] at h11

/-- **The obstruction is not vacuous.**  The two-outcome dephasing announcement
`ρ ↦ |0⟩⟨0| ρ |0⟩⟨0| + |1⟩⟨1| ρ |1⟩⟨1|` on a qubit is not `ρ ↦ L ρ Lᴴ` for **any** single `L`,
so the dephasing map does not admit a single Kraus conjugation. -/
theorem not_exists_single_conj_eq_witnessSum :
    ¬ ∃ L : Op (Fin 2),
      krausMap (fun _ : Unit => witnessKraus₀) +
        krausMap (fun _ : Unit => witnessKraus₁) = krausMap (fun _ : Unit => L) := by
  rintro ⟨L, hL⟩
  let K (t : Bool) := cond t witnessKraus₁ witnessKraus₀
  have hentry (ai bj : Fin 2 × Fin 2) :
      ∑ t, K t ai.2 ai.1 * star (K t bj.2 bj.1) = L ai.2 ai.1 * star (L bj.2 bj.1) := by
    have h := congrArg (fun Φ => choiMatrix Φ ai bj) hL
    change choiMatrix (krausMap (fun _ : Unit => witnessKraus₀)) ai bj +
      choiMatrix (krausMap (fun _ : Unit => witnessKraus₁)) ai bj = _ at h
    simpa [choiMatrix_krausMap, Matrix.vecMulVec, K, add_comm] using h
  have hm := Matrix.outerSum_eq_outer_minor (fun t ai => K t ai.2 ai.1)
    (fun ai => L ai.2 ai.1) hentry false true (0, 0) (1, 1)
  norm_num [K, witnessKraus₀, witnessKraus₁] at hm

end Quantum.Channels
