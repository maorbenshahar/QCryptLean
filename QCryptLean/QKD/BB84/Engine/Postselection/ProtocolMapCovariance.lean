import QCryptLean.QKD.BB84.Engine.Postselection.RoundKernel
import QCryptLean.QKD.BB84.Model.EveVisibleProtocol
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.Real

/-!
# The Bell-twirl outcome permutation, and signed Kraus-family conjugation

The explicit outcome permutation induced by the IID bilateral-Pauli (Bell) twirl on the
computational basis, the unit-modulus phase it carries per Kraus operator (the twirl unitary is a
*signed* permutation matrix, not a plain one), and the channel-level conjugation lift that
accounts for that phase.

The per-round Bell twirl relabels the key-round computational-basis outcome by
`ω_i ↦ bellKeyOutcomePerm (g_i) ω_i` (`bb84BellSinglePair_conj_compProjector`); `bellOutcomePerm`
is the explicit `n`-round outcome permutation this induces on `Fin (4 ^ n)`, and
`bellTwirlUnitary_conj_single` shows the twirl unitary permutes the computational outcome
projectors via it. Because the per-round twirl elements `Y⊗Y`, `Z⊗Z` carry a `±1` sign, the twirl
unitary is a *signed* permutation matrix: `bellTwirlSign` is the resulting per-outcome
unit-modulus phase, and `krausMapFintype_conj_of_phased_intertwining` is the channel-level
conjugation lift that cancels it.

## Main definitions and results

* `bellOutcomePerm`, `bellOutcomePerm_apply`, `bellOutcomePerm_involutive` — the explicit
  outcome permutation induced by the Bell twirl, and its involutivity.
* `bellTwirlUnitary_conj_single` — the twirl unitary permutes computational outcome projectors via
  `bellOutcomePerm`.
* `bellTwirlSign`, `bellTwirlSign_unit` — the per-outcome unit-modulus phase carried by the signed
  permutation `bellTwirlUnitary`.
* `single_mul_bellTwirlUnitary` — the signed monomial identity: right-multiplying a `single`
  column by the twirl relabels its column and rescales by `bellTwirlSign`.
* `krausMapFintype_conj_of_phased_intertwining` — a per-Kraus intertwining up to a unit-modulus
  phase still lifts to a channel-level conjugation identity (the phase cancels); generalizes
  `krausMapFintype_conj_of_intertwining`.
* `permMatrix_mul_single` — a generic matrix fact: left-multiplying a `single` by a permutation
  matrix relabels its row.
* `bellStringRelabel`, `bellStringRelabelEquiv` — the per-round Bell relabel of an outcome string,
  and its form as a permutation (it is an involution).

## References

Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B, Thm 3; Renner (2005),
`arXiv:quant-ph/0512258v2`, §5, §6.5.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

open QKD.BB84.Model.bb84

/-!
## Generic Kraus-family infrastructure for the signed (Bell) twirl

A per-Kraus intertwining `K_i · U = W · K'_i` lifts a channel-level conjugation via
`krausMapFintype_conj_of_intertwining`.  The signed Bell twirl carries a per-Kraus **unit phase**
`ε_i` (the `±1` of `Y⊗Y`/`Z⊗Z`), so the intertwining is `K_i · U = ε_i • (W · K'_i)`; the phase
cancels (`ε · conj ε = 1`) inside `K · (U M U†) · K†`.  The phased channel lift below is the only
structural difference from the sign-free version.
-/

/-- **Phased Kraus-family conjugation lift.**  If two finite Kraus families are intertwined up to a
per-index **unit-modulus** phase `c i` (`Km i · Wa = c i • (Wb · Kn i)` with `c i · conj (c i) =
1`), then the Kraus maps are intertwined by conjugation — the phase cancels.  Phased twin of
`krausMapFintype_conj_of_intertwining`.  Public so that `PEAnnounceRelabel.lean`'s phased
intertwining step can cite it directly instead of re-deriving a local copy. -/
theorem krausMapFintype_conj_of_phased_intertwining {κ : Type*} [Fintype κ]
    {aM aN bM bN : ℕ}
    (Km : κ → Matrix (Fin bM) (Fin aM) ℂ)
    (Kn : κ → Matrix (Fin bN) (Fin aN) ℂ)
    (Wa : Matrix (Fin aM) (Fin aN) ℂ)
    (Wb : Matrix (Fin bM) (Fin bN) ℂ)
    (c : κ → ℂ)
    (hc : ∀ i, c i * (starRingEnd ℂ) (c i) = 1)
    (hInter : ∀ i, Km i * Wa = c i • (Wb * Kn i))
    (A : Matrix (Fin aN) (Fin aN) ℂ) :
    krausMapFintype Km (Wa * A * Wa.conjTranspose) =
      Wb * krausMapFintype Kn A * Wb.conjTranspose := by
  -- absorb the unit phase into the (output) Kraus family, then invoke the sign-free lift
  have hInter' : ∀ i, Km i * Wa = Wb * ((c i) • Kn i) := by
    intro i; rw [hInter i, Matrix.mul_smul]
  have hcancel : krausMapFintype (fun i => (c i) • Kn i) A = krausMapFintype Kn A := by
    simp only [krausMapFintype, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hci : c i * star (c i) = 1 := by rw [← starRingEnd_apply]; exact hc i
    rw [hci, one_smul]
  rw [krausMapFintype_conj_of_intertwining Km (fun i => (c i) • Kn i) Wa Wb hInter' A, hcancel]

/-- **Row-monomial action of a projector-permuting unitary.**  If `U` is a unitary that permutes the
coordinate projectors (`U · |ν⟩⟨ν| · U† = |πν⟩⟨πν|`), then right-multiplying a `single` by `U`
relabels its column by `π.symm` and rescales by the unit-modulus diagonal entry `U c (π.symm c)`. -/
private theorem single_mul_unitary_perm {N b : ℕ}
    (U : Op N) (π : Equiv.Perm (Fin N))
    (hperm : ∀ ν, U * (Matrix.single ν ν 1 : Op N) * Uᴴ = Matrix.single (π ν) (π ν) 1)
    (a : Fin b) (c : Fin N) :
    (Matrix.single a c 1 : Matrix (Fin b) (Fin N) ℂ) * U =
      (U c (π.symm c)) • (Matrix.single a (π.symm c) 1 : Matrix (Fin b) (Fin N) ℂ) := by
  -- entry of the conjugated projector: `(U |ν⟩⟨ν| U†)_{ij} = U_{iν} · conj U_{jν}`
  have hconj : ∀ ν i j,
      (U * (Matrix.single ν ν 1 : Op N) * Uᴴ) i j = U i ν * (starRingEnd ℂ) (U j ν) := by
    intro ν i j
    rw [Matrix.mul_apply, Finset.sum_eq_single ν]
    · rw [Matrix.mul_single_apply_same, mul_one, Matrix.conjTranspose_apply, starRingEnd_apply]
    · intro l _ hl; rw [Matrix.mul_single_apply_of_ne (hbj := hl), zero_mul]
    · intro hcon; exact (hcon (Finset.mem_univ _)).elim
  have hkey : ∀ ν i j, U i ν * (starRingEnd ℂ) (U j ν) =
      (if i = π ν then (1 : ℂ) else 0) * (if j = π ν then 1 else 0) := by
    intro ν i j
    rw [← hconj ν i j, hperm ν, Matrix.single_apply]
    rcases eq_or_ne i (π ν) with hi | hi <;> rcases eq_or_ne j (π ν) with hj | hj <;>
      simp [hi, hj, eq_comm]
  have hdiag : ∀ ν, U (π ν) ν * (starRingEnd ℂ) (U (π ν) ν) = 1 := by
    intro ν; rw [hkey ν (π ν) (π ν), ite_eq_left rfl, mul_one]
  have hoff : ∀ ν i, i ≠ π ν → U i ν = 0 := by
    intro ν i hi
    have h := hkey ν i (π ν)
    rw [ite_eq_right hi, ite_eq_left rfl, zero_mul] at h
    have hne : (starRingEnd ℂ) (U (π ν) ν) ≠ 0 := fun hz => by
      simpa [hz] using hdiag ν
    exact (mul_eq_zero.mp h).resolve_right hne
  ext p q
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  by_cases hp : p = a
  · subst hp
    rw [Matrix.single_mul_apply_same, one_mul]
    by_cases hq : q = π.symm c
    · subst hq; rw [ite_eq_left ⟨rfl, rfl⟩, mul_one]
    · rw [ite_eq_right (fun h => hq h.2.symm), mul_zero]
      exact hoff q c (fun hcon => hq (by rw [hcon, Equiv.symm_apply_apply]))
  · rw [Matrix.single_mul_apply_of_ne (h := hp), ite_eq_right (fun h => hp h.1.symm), mul_zero]

/-- The explicit `n`-fold outcome permutation `π_g` on `Fin (4ⁿ)` induced by the Bell twirl
`bellTwirlUnitary n g`: per round `ω_i ↦ bellKeyOutcomePerm (g_i) ω_i`.  (This is the witness of
`bellTwirlUnitary_permutes_compProjectors`, made explicit.) -/
def bellOutcomePerm (n : ℕ) (g : Fin n → Fin 4) : Equiv.Perm (Fin (4 ^ n)) :=
  (@finFunctionFinEquiv 4 n).symm.trans
    ((Equiv.piCongrRight (fun a => bellKeyOutcomePermEquiv (g a))).trans (@finFunctionFinEquiv 4 n))

/-- `π_g (finFunctionFinEquiv ω) = finFunctionFinEquiv (g·ω)`: on the computational outcome index of
`ω`, the Bell outcome permutation acts as the per-round relabel `ω_i ↦ bellKeyOutcomePerm (g_i)
ω_i`. -/
theorem bellOutcomePerm_apply (n : ℕ) (g : Fin n → Fin 4) (ω : Fin n → Fin 4) :
    bellOutcomePerm n g (finFunctionFinEquiv ω) =
      finFunctionFinEquiv (fun i => bellKeyOutcomePerm (g i) (ω i)) := by
  simp only [bellOutcomePerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- `π_g` is an involution (each per-round `bellKeyOutcomePerm (g_i)` is). -/
theorem bellOutcomePerm_involutive (n : ℕ) (g : Fin n → Fin 4) :
    Function.Involutive (bellOutcomePerm n g) := by
  intro ν
  rw [← finFunctionFinEquiv.apply_symm_apply ν]
  set ω := finFunctionFinEquiv.symm ν with hω
  rw [bellOutcomePerm_apply, bellOutcomePerm_apply]
  congr 1
  funext i
  exact bellKeyOutcomePerm_involutive (g i) (ω i)

/-- `(π_g).symm = π_g` (involution). -/
theorem bellOutcomePerm_symm (n : ℕ) (g : Fin n → Fin 4) :
    (bellOutcomePerm n g).symm = bellOutcomePerm n g := by
  apply Equiv.ext
  intro ν
  rw [Equiv.symm_apply_eq]
  exact (bellOutcomePerm_involutive n g ν).symm

/-- The diagonal entry of a projector-permuting unitary is unit-modulus: `U_{πν,ν} · conj = 1`. -/
private theorem unitary_perm_diag_unit {N : ℕ}
    (U : Op N) (π : Equiv.Perm (Fin N))
    (hperm : ∀ ν, U * (Matrix.single ν ν 1 : Op N) * Uᴴ = Matrix.single (π ν) (π ν) 1)
    (ν : Fin N) :
    U (π ν) ν * (starRingEnd ℂ) (U (π ν) ν) = 1 := by
  have hconj : (U * (Matrix.single ν ν 1 : Op N) * Uᴴ) (π ν) (π ν) =
      U (π ν) ν * (starRingEnd ℂ) (U (π ν) ν) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single ν]
    · rw [Matrix.mul_single_apply_same, mul_one, Matrix.conjTranspose_apply, starRingEnd_apply]
    · intro l _ hl; rw [Matrix.mul_single_apply_of_ne (hbj := hl), zero_mul]
    · intro hc; exact (hc (Finset.mem_univ _)).elim
  rw [← hconj, hperm ν, Matrix.single_apply, ite_eq_left ⟨rfl, rfl⟩]

/-- The Bell twirl unitary permutes the computational outcome projectors via the explicit `π_g`:
`U_g · |ν⟩⟨ν| · U_g† = |π_g ν⟩⟨π_g ν|`.  (Explicit-witness form of
`bellTwirlUnitary_permutes_compProjectors`.) -/
theorem bellTwirlUnitary_conj_single (n : ℕ) (g : Fin n → Fin 4) (ν : Fin (4 ^ n)) :
    bellTwirlUnitary n g * (Matrix.single ν ν 1 : Op (4 ^ n)) * (bellTwirlUnitary n g)ᴴ =
      Matrix.single (bellOutcomePerm n g ν) (bellOutcomePerm n g ν) 1 := by
  set s : Fin n → Fin 4 := (@finFunctionFinEquiv 4 n).symm ν with hs
  have hU : bellTwirlUnitary n g = tensorFamily (fun a => bb84BellSinglePairTwirlGroup (g a)) := rfl
  have hsingle : (Matrix.single ν ν 1 : Op (4 ^ n)) =
      tensorFamily (fun a => (Matrix.single (s a) (s a) 1 : Op 4)) := by
    rw [tensorFamily_single_one, hs, Equiv.apply_symm_apply]
  rw [hU, hsingle, conjTranspose_tensorFamily, tensorFamily_mul, tensorFamily_mul]
  have hbody : (fun a => bb84BellSinglePairTwirlGroup (g a) * (Matrix.single (s a) (s a) 1 : Op 4) *
        (bb84BellSinglePairTwirlGroup (g a))ᴴ) =
      (fun a => (Matrix.single (bellKeyOutcomePerm (g a) (s a))
        (bellKeyOutcomePerm (g a) (s a)) 1 : Op 4)) :=
    funext (fun a => bb84BellSinglePair_conj_compProjector (g a) (s a))
  rw [hbody, tensorFamily_single_one]
  have hν : ν = finFunctionFinEquiv s := by rw [hs]; simp
  rw [hν, bellOutcomePerm_apply]

/-- The **unit-modulus Bell-twirl phase** carried per Kraus: the `±1` diagonal entry of the signed
permutation `bellTwirlUnitary n g` at the outcome string `ω`. -/
def bellTwirlSign (n : ℕ) (g : Fin n → Fin 4) (ω : Fin n → Fin 4) : ℂ :=
  bellTwirlUnitary n g (finFunctionFinEquiv ω)
    (finFunctionFinEquiv (fun i => bellKeyOutcomePerm (g i) (ω i)))

/-- The Bell-twirl phase is unit-modulus: `ε · conj ε = 1`. -/
theorem bellTwirlSign_unit (n : ℕ) (g : Fin n → Fin 4) (ω : Fin n → Fin 4) :
    bellTwirlSign n g ω * (starRingEnd ℂ) (bellTwirlSign n g ω) = 1 := by
  have hbop : bellOutcomePerm n g (finFunctionFinEquiv (fun i => bellKeyOutcomePerm (g i) (ω i))) =
      finFunctionFinEquiv ω := by
    rw [bellOutcomePerm_apply]
    congr 1
    funext i
    exact bellKeyOutcomePerm_involutive (g i) (ω i)
  have h := unitary_perm_diag_unit (bellTwirlUnitary n g) (bellOutcomePerm n g)
    (bellTwirlUnitary_conj_single n g)
    (finFunctionFinEquiv (fun i => bellKeyOutcomePerm (g i) (ω i)))
  rw [hbop] at h
  simpa [bellTwirlSign] using h

/-- **The single-`single` signed monomial identity.**  Right-multiplying a `single`-column at `ω` by
the Bell twirl relabels the column to `g·ω` and rescales by the unit phase `ε_{g,ω}`:
`single a (idx ω) 1 · U_g = ε_{g,ω} • single a (idx (g·ω)) 1`. -/
theorem single_mul_bellTwirlUnitary {b n : ℕ} (a : Fin b) (g : Fin n → Fin 4) (ω : Fin n → Fin 4) :
    (Matrix.single a (finFunctionFinEquiv ω) 1 : Matrix (Fin b) (Fin (4 ^ n)) ℂ) *
        bellTwirlUnitary n g =
      bellTwirlSign n g ω •
        (Matrix.single a (finFunctionFinEquiv (fun i => bellKeyOutcomePerm (g i) (ω i))) 1 :
          Matrix (Fin b) (Fin (4 ^ n)) ℂ) := by
  have h := single_mul_unitary_perm (bellTwirlUnitary n g) (bellOutcomePerm n g)
    (bellTwirlUnitary_conj_single n g) a (finFunctionFinEquiv ω)
  rw [bellOutcomePerm_symm, bellOutcomePerm_apply] at h
  rw [h, bellTwirlSign]

/-- Left-multiplying a `single` by a permutation matrix relabels its row by `σ.symm`.  Generic
matrix fact (no BB84/dimension dependence); public so that `PEAnnounceRelabel.lean`'s relabel
unitary step can cite it directly instead of re-deriving a local copy. -/
theorem permMatrix_mul_single {β γ : Type*} [Fintype β] [DecidableEq β] [DecidableEq γ]
    (σ : Equiv.Perm β) (out : β) (col : γ) (v : ℂ) :
    Equiv.Perm.permMatrix ℂ σ * (Matrix.single out col v) =
      Matrix.single (σ.symm out) col v := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext p q
  rw [Matrix.submatrix_apply, id_eq, Matrix.single_apply, Matrix.single_apply]
  have hcond : (out = σ p) ↔ (σ.symm out = p) := by
    constructor
    · intro h; rw [h, Equiv.symm_apply_apply]
    · intro h; rw [← h, Equiv.apply_symm_apply]
  by_cases hq : col = q
  · by_cases hp : σ.symm out = p
    · rw [ite_eq_left ⟨hcond.mpr hp, hq⟩, ite_eq_left ⟨hp, hq⟩]
    · rw [ite_eq_right (fun h => hp (hcond.mp h.1)), ite_eq_right (fun h => hp h.1)]
  · rw [ite_eq_right (fun h => hq h.2), ite_eq_right (fun h => hq h.2)]

/-!
### §4.6 — the Kraus-family reindexings and per-Kraus signed-monomial intertwinings
-/

/-- The per-round Bell relabel of an outcome string, `ω_i ↦ bellKeyOutcomePerm (g_i) ω_i`. -/
def bellStringRelabel (n : ℕ) (g : Fin n → Fin 4) (ω : Fin n → Fin signalDim) :
    Fin n → Fin signalDim :=
  fun i => bellKeyOutcomePerm (g i) (ω i)

theorem bellStringRelabel_involutive (n : ℕ) (g : Fin n → Fin 4) :
    Function.Involutive (bellStringRelabel n g) := by
  intro ω
  funext i
  exact bellKeyOutcomePerm_involutive (g i) (ω i)

/-- The outcome-string Bell relabel as a permutation (it is an involution). -/
def bellStringRelabelEquiv (n : ℕ) (g : Fin n → Fin 4) :
    (Fin n → Fin signalDim) ≃ (Fin n → Fin signalDim) :=
  (bellStringRelabel_involutive n g).toPerm

end QKD.BB84.Engine

end
