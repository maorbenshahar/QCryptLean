import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination
import QCryptLean.QKD.BB84.Model.BellPostMeasurement
import QCryptLean.Quantum.Channels.CPTP.BlockPinchingChannel

/-!
# The Bell twirl's monomial structure, and its covariance with the computational measurement

The bilateral-Pauli (Bell) twirl unitary is a *signed permutation matrix* in the computational
basis: conjugating a computational-basis outcome projector by a single-pair bilateral Pauli
returns the relabelled projector, the sign cancelling in the projector. This file establishes
that monomial structure and uses it to show the `n`-round computational-basis measurement
commutes with conjugation by the (`n`-fold) Bell twirl unitary.

## Main definitions and results

* `bellKeyOutcomePerm`, `bellKeyOutcomePermEquiv` — the single-pair key-round outcome
  permutation `ω ↦ g·ω`: the identity for the diagonal Paulis `I⊗I, Z⊗Z`, the involution
  `ω ↦ 3 - ω` for the off-diagonal Paulis `X⊗X, Y⊗Y`.
* `bb84BellSinglePair_conj_compProjector` — conjugating a computational-basis outcome
  projector by a bilateral Pauli returns the relabelled projector.
* `bellTwirlUnitary_permutes_compProjectors` — the `n`-fold Bell twirl unitary permutes the
  computational-basis outcome projectors.
* `bb84CompProjector`, `measurementChannel_eq_sum_compProjector_conj` — the computational
  measurement channel as a sum of outcome-projector conjugations.
* `measurementChannel_conj_eq_of_permutesCompProjectors` — a generic measurement-covariance
  lemma: the computational measurement commutes with conjugation by any monomial that permutes
  the outcome projectors.
* `measurementChannel_bellTwirl_outcomeRelabel` — the computational measurement commutes with
  conjugation by the `n`-fold Bell twirl unitary.

## References

Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B; Renner (2005),
`arXiv:quant-ph/0512258v2`, §6.5.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Gates Quantum.Basis.BellStates
open Quantum.Symmetry Matrix Math.RepresentationTheory Quantum.Channels
open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder

noncomputable section

namespace QKD.BB84.Engine

/-!
## Key round: the signed-Pauli pass-through (single-pair outcome relabel)

In the **computational** basis (the key-round measurement basis) every bilateral Pauli is a signed
permutation matrix; conjugating a computational-basis outcome projector `|ω⟩⟨ω|` by it returns the
relabelled projector `|g·ω⟩⟨g·ω|` (the `±1` signs cancel in the projector).  The single-pair outcome
bijection `g·ω` is `bellKeyOutcomePerm`: the identity for `k ∈ {I⊗I, Z⊗Z}` and the swap
`(0 3)(1 2)` for `k ∈ {X⊗X, Y⊗Y}`.
-/

/-- The single-pair **key-round outcome permutation** `ω ↦ g·ω` (computational basis): identity for
`G_k ∈ {I⊗I, Z⊗Z}` (diagonal Paulis), the involution `ω ↦ 3 - ω` (`(0 3)(1 2)`) for
`G_k ∈ {X⊗X, Y⊗Y}` (off-diagonal Paulis). -/
def bellKeyOutcomePerm : Fin 4 → Fin 4 → Fin 4 :=
  ![![0,1,2,3], ![3,2,1,0], ![3,2,1,0], ![0,1,2,3]]

/-- The signs of the single-pair bilateral Paulis as signed permutations:
`G k |ω⟩ = s_k(ω) |g·ω⟩` in the computational basis, with `s_k(ω) = ±1` (the `Y⊗Y` and `Z⊗Z`
phases). -/
private def bellKeyOutcomeSign : Fin 4 → Fin 4 → ℂ :=
  ![![1,1,1,1], ![1,1,1,1], ![-1,1,1,-1], ![1,-1,-1,1]]

/-- **Each bilateral Pauli is a signed permutation matrix**: column `ω` of `G k` is
`s_k(ω) · e_{g·ω}`. Read off entrywise from the explicit matrices
`bb84BellSinglePairTwirlGroup_zero_eq` … `bb84BellSinglePairTwirlGroup_three_eq`. -/
private theorem bb84BellSinglePairTwirlGroup_eq_monomial (k : Fin 4) :
    bb84BellSinglePairTwirlGroup k = Matrix.of fun i ω =>
      if i = bellKeyOutcomePerm k ω then bellKeyOutcomeSign k ω else 0 := by
  -- for each `k`: rewrite `G k`, `g·` and `s_k` to explicit form, then compare the 16 entries
  fin_cases k <;>
    simp only [Fin.reduceFinMk, bb84BellSinglePairTwirlGroup_zero_eq,
      bb84BellSinglePairTwirlGroup_one_eq, bb84BellSinglePairTwirlGroup_two_eq,
      bb84BellSinglePairTwirlGroup_three_eq, bellKeyOutcomePerm, bellKeyOutcomeSign,
      Matrix.cons_val] <;>
    ext i ω <;> fin_cases i <;> fin_cases ω <;>
    simp only [Matrix.of_apply, Fin.reduceFinMk, Matrix.cons_val, Fin.reduceEq, ↓reduceIte]

/-- Conjugating a computational-basis outcome projector `|ω⟩⟨ω|` by a Hermitian operator `A` whose
`ω`-th column is a unit-modulus scalar times the basis vector `e_{πω}` (i.e. `A` is monomial on
column `ω`) returns the relabelled projector `|πω⟩⟨πω|`.  The `±1`/unit phase cancels:
`(A · |ω⟩⟨ω| · Aᴴ)_{ij} = A_{iω} · conj(A_{jω}) = |s|² · [i = πω][j = πω]`. -/
private theorem conj_single_of_col {A : Op 4} {ω πω : Fin 4}
    (hzero : ∀ i, i ≠ πω → A i ω = 0)
    (hunit : A πω ω * (starRingEnd ℂ) (A πω ω) = 1) :
    A * (Matrix.single ω ω 1 : Op 4) * Aᴴ =
      (Matrix.single πω πω 1 : Op 4) := by
  ext i j
  have hbody : (A * (Matrix.single ω ω 1 : Op 4) * Aᴴ) i j =
      A i ω * (starRingEnd ℂ) (A j ω) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single ω]
    · rw [Matrix.mul_apply, Finset.sum_eq_single ω]
      · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, Matrix.conjTranspose_apply,
          ← starRingEnd_apply]; ring
      · intro c _ hc
        rw [Matrix.single_apply, if_neg (fun h => hc h.1.symm), mul_zero]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intro l _ hl
      rw [Matrix.mul_apply, Finset.sum_eq_zero (fun c _ => ?_), zero_mul]
      rw [Matrix.single_apply, if_neg (fun h => hl h.2.symm), mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hbody, Matrix.single_apply]
  by_cases hi : i = πω
  · by_cases hj : j = πω
    · subst hi; subst hj; rw [if_pos ⟨rfl, rfl⟩]; exact hunit
    · rw [if_neg (fun h => hj h.2.symm), hzero j hj, map_zero, mul_zero]
  · rw [if_neg (fun h => hi h.1.symm), hzero i hi, zero_mul]

/-- **Key round (single pair): the signed-Pauli pass-through.**  Conjugating a
computational-basis outcome projector `|ω⟩⟨ω|` by a bilateral Pauli `G_k` returns the relabelled
projector `|g·ω⟩⟨g·ω|`, with `g·ω = bellKeyOutcomePerm k ω` — the key-round outcome bijection.  This
is the per-pair monomial (signed-permutation) structure that lets the twirl pass through the
computational-basis measurement as a clean outcome relabel.  (The `±1` phases of `Y⊗Y`/`Z⊗Z` cancel
in the projector.) -/
theorem bb84BellSinglePair_conj_compProjector (k ω : Fin 4) :
    bb84BellSinglePairTwirlGroup k * (Matrix.single ω ω 1 : Op 4) *
        (bb84BellSinglePairTwirlGroup k)ᴴ =
      (Matrix.single (bellKeyOutcomePerm k ω) (bellKeyOutcomePerm k ω) 1 : Op 4) := by
  refine conj_single_of_col (fun i hi => ?_) ?_
  · -- off the relabelled row the column vanishes
    rw [bb84BellSinglePairTwirlGroup_eq_monomial, Matrix.of_apply, if_neg hi]
  · -- on it sits the sign `s = ±1`, and `s · conj s = 1`
    rw [bb84BellSinglePairTwirlGroup_eq_monomial, Matrix.of_apply, if_pos rfl]
    fin_cases k <;> fin_cases ω <;>
      simp only [bellKeyOutcomeSign, Fin.reduceFinMk, Matrix.cons_val, map_one, map_neg, mul_one,
        mul_neg, neg_neg]

/-!
## The `n`-round measurement-channel covariance (outcome relabel)

The key-round computational-basis measurement `measurementChannel` **commutes** with conjugation by
the `n`-fold bilateral-Pauli twirl unitary `bellTwirlUnitary n g ⊗ 1_E`: because the twirl unitary
is a computational-basis monomial (signed permutation), conjugating by it permutes the AB outcome
projectors, and the measurement (a dephasing in those projectors) is invariant under that
permutation.

The covariance is phrased with the **public** measurement API only (`measurementChannel`,
`measurementChannel_apply`) — the protocol's `outcomeRemapKraus` is `private`, so the outcome
relabel is realised intrinsically as conjugation by the monomial twirl unitary, not via a private
Kraus.  The reusable generic lemma `measurementChannel_conj_eq_of_permutesCompProjectors` takes the
"permutes the AB outcome projectors" property as a hypothesis; the BB84 instance feeds it the (true,
single-pair-proven) `n`-fold monomial property `bellTwirlUnitary_permutes_compProjectors`.
-/

/-- The AB computational-basis outcome projector `P_ω = |ω⟩⟨ω|_AB ⊗ 1_E` on `(4ⁿ)·eveDim`. -/
def bb84CompProjector (n eveDim : ℕ) (ω : Fin (4 ^ n)) : Op (4 ^ n * eveDim) :=
  Op.tensor (Matrix.single ω ω 1 : Op (4 ^ n)) (1 : Op eveDim)

/-- Two indices of `Fin (4ⁿ · eveDim)` agree iff their `divNat` (AB) and `modNat` (Eve) parts
    agree. -/
private theorem fin_divNat_modNat_ext {n eveDim : ℕ} [NeZero eveDim]
    {i k : Fin (4 ^ n * eveDim)} (hd : i.divNat = k.divNat) (hm : i.modNat = k.modNat) :
    i = k := by
  apply finProdFinEquiv.symm.injective
  rw [finProdFinEquiv_symm_apply, finProdFinEquiv_symm_apply, hd, hm]

/-- Entry of the AB outcome projector. -/
private theorem bb84CompProjector_apply {n eveDim : ℕ} [NeZero eveDim] (ω : Fin (4 ^ n))
    (i k : Fin (4 ^ n * eveDim)) :
    bb84CompProjector n eveDim ω i k =
      (if ω = i.divNat ∧ ω = k.divNat then (1 : ℂ) else 0) *
        (if i.modNat = k.modNat then (1 : ℂ) else 0) := by
  rw [bb84CompProjector, Op_tensor_apply_finProd, finProdFinEquiv_symm_apply,
    finProdFinEquiv_symm_apply, Matrix.single_apply, Matrix.one_apply]

/-- Left-multiplying by the AB outcome projector keeps the rows in block `ω` and kills the rest. -/
private theorem compProjector_mul_apply {n eveDim : ℕ} [NeZero eveDim] (ω : Fin (4 ^ n))
    (N : Op (4 ^ n * eveDim)) (i l : Fin (4 ^ n * eveDim)) :
    (bb84CompProjector n eveDim ω * N) i l = if i.divNat = ω then N i l else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : i.divNat = ω
  · rw [if_pos hi, Finset.sum_eq_single i]
    · rw [bb84CompProjector_apply, if_pos ⟨hi.symm, hi.symm⟩, if_pos rfl, mul_one, one_mul]
    · intro k _ hk
      have : bb84CompProjector n eveDim ω i k = 0 := by
        rw [bb84CompProjector_apply]
        by_cases hkd : ω = k.divNat
        · rw [if_pos ⟨hi.symm, hkd⟩,
            if_neg (fun hm => hk (fin_divNat_modNat_ext (hi.trans hkd) hm).symm), mul_zero]
        · rw [if_neg (fun h => hkd h.2), zero_mul]
      rw [this, zero_mul]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · rw [if_neg hi, Finset.sum_eq_zero]
    intro k _
    rw [bb84CompProjector_apply, if_neg (fun h => hi h.1.symm), zero_mul, zero_mul]

/-- Right-multiplying by the AB outcome projector keeps the columns in block `ω` and kills the
    rest. -/
private theorem mul_compProjector_apply {n eveDim : ℕ} [NeZero eveDim] (ω : Fin (4 ^ n))
    (N : Op (4 ^ n * eveDim)) (l j : Fin (4 ^ n * eveDim)) :
    (N * bb84CompProjector n eveDim ω) l j = if j.divNat = ω then N l j else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : j.divNat = ω
  · rw [if_pos hj, Finset.sum_eq_single j]
    · rw [bb84CompProjector_apply, if_pos ⟨hj.symm, hj.symm⟩, if_pos rfl, mul_one, mul_one]
    · intro k _ hk
      have : bb84CompProjector n eveDim ω k j = 0 := by
        rw [bb84CompProjector_apply]
        by_cases hkd : ω = k.divNat
        · rw [if_pos ⟨hkd, hj.symm⟩,
            if_neg (fun hm => hk (fin_divNat_modNat_ext (hkd.symm.trans hj.symm) hm)), mul_zero]
        · rw [if_neg (fun h => hkd h.1), zero_mul]
      rw [this, mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · rw [if_neg hj, Finset.sum_eq_zero]
    intro k _
    rw [bb84CompProjector_apply, if_neg (fun h => hj h.2.symm), zero_mul, mul_zero]

/-- Conjugating `N` by the AB outcome projector keeps only the `(ω, ω)` AB block of `N`. -/
private theorem compProjector_conj_apply {n eveDim : ℕ} [NeZero eveDim] (ω : Fin (4 ^ n))
    (N : Op (4 ^ n * eveDim)) (i j : Fin (4 ^ n * eveDim)) :
    (bb84CompProjector n eveDim ω * N * bb84CompProjector n eveDim ω) i j =
      if i.divNat = ω ∧ j.divNat = ω then N i j else 0 := by
  rw [Matrix.mul_assoc, compProjector_mul_apply]
  by_cases hi : i.divNat = ω
  · rw [if_pos hi, mul_compProjector_apply]
    by_cases hj : j.divNat = ω
    · rw [if_pos hj, if_pos ⟨hi, hj⟩]
    · rw [if_neg hj, if_neg (fun h => hj h.2)]
  · rw [if_neg hi, if_neg (fun h => hi h.1)]

/-- **The measurement channel as a sum of AB-outcome-projector conjugations**:
`measurementChannel N = Σ_ω P_ω · N · P_ω`.  This reconstructs the (private-Kraus) measurement map
from the public entry formula `measurementChannel_apply`. -/
theorem measurementChannel_eq_sum_compProjector_conj {n eveDim : ℕ} [NeZero eveDim]
    (N : Op (4 ^ n * eveDim)) :
    measurementChannel n eveDim N =
      ∑ ω : Fin (4 ^ n), bb84CompProjector n eveDim ω * N * bb84CompProjector n eveDim ω := by
  ext i j
  rw [measurementChannel_apply, Matrix.sum_apply,
    Finset.sum_congr rfl (fun ω _ => compProjector_conj_apply ω N i j)]
  by_cases h : i.divNat = j.divNat
  · rw [if_pos h, Finset.sum_eq_single i.divNat]
    · rw [if_pos ⟨rfl, h.symm⟩]
    · intro ω _ hω; rw [if_neg (fun hcon => hω hcon.1.symm)]
    · intro hcon; exact (hcon (Finset.mem_univ _)).elim
  · rw [if_neg h, Finset.sum_eq_zero]
    intro ω _
    rw [if_neg (fun hcon => h (hcon.1.trans hcon.2.symm))]

/-- Conjugating an AB outcome projector by a monomial `U ⊗ 1` relabels it: if `U` permutes the
single-block projectors via `π` (`U · |ω⟩⟨ω| · Uᴴ = |πω⟩⟨πω|`), then
`(U⊗1)ᴴ · P_ω · (U⊗1) = P_{π⁻¹ ω}`. -/
private theorem compProjector_tensorU_conj {n eveDim : ℕ} [NeZero eveDim]
    (U : Op (4 ^ n)) (π : Equiv.Perm (Fin (4 ^ n)))
    (hU : Uᴴ * U = 1)
    (hperm : ∀ ω, U * (Matrix.single ω ω 1 : Op (4 ^ n)) * Uᴴ =
      Matrix.single (π ω) (π ω) 1)
    (ω : Fin (4 ^ n)) :
    (Op.tensor U (1 : Op eveDim))ᴴ * bb84CompProjector n eveDim ω * Op.tensor U (1 : Op eveDim) =
      bb84CompProjector n eveDim (π.symm ω) := by
  have hconj : Uᴴ * (Matrix.single ω ω 1 : Op (4 ^ n)) * U =
      Matrix.single (π.symm ω) (π.symm ω) 1 := by
    have h1 : U * (Matrix.single (π.symm ω) (π.symm ω) 1 : Op (4 ^ n)) * Uᴴ =
        Matrix.single ω ω 1 := by
      rw [hperm (π.symm ω), Equiv.apply_symm_apply]
    calc Uᴴ * (Matrix.single ω ω 1 : Op (4 ^ n)) * U
           = Uᴴ * (U * (Matrix.single (π.symm ω) (π.symm ω) 1) * Uᴴ) * U := by rw [h1]
      _ = (Uᴴ * U) * (Matrix.single (π.symm ω) (π.symm ω) 1) * (Uᴴ * U) := by noncomm_ring
      _ = Matrix.single (π.symm ω) (π.symm ω) 1 := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  simp only [bb84CompProjector, Op.tensor_conjTranspose, Matrix.conjTranspose_one, Op.tensor_mul,
    Matrix.mul_one, hconj]

/-- **Generic measurement covariance under a projector-permuting monomial.**  If `U` permutes the AB
computational-basis outcome projectors (`U · |ω⟩⟨ω| · Uᴴ = |πω⟩⟨πω|` for a permutation `π`), then
the `n`-round computational measurement channel commutes with conjugation by `U ⊗ 1_E`:
`measurementChannel((U⊗1) · M · (U⊗1)ᴴ) = (U⊗1) · measurementChannel(M) · (U⊗1)ᴴ`.

This realises the "outcome relabel" intrinsically (conjugation by the monomial), using only the
public measurement API.  Reusable for any monomial conjugation, not just the Bell twirl. -/
theorem measurementChannel_conj_eq_of_permutesCompProjectors {n eveDim : ℕ} [NeZero eveDim]
    (U : Op (4 ^ n)) (π : Equiv.Perm (Fin (4 ^ n)))
    (hU : Uᴴ * U = 1)
    (hperm : ∀ ω, U * (Matrix.single ω ω 1 : Op (4 ^ n)) * Uᴴ =
      Matrix.single (π ω) (π ω) 1)
    (M : Op (4 ^ n * eveDim)) :
    measurementChannel n eveDim (Op.tensor U (1 : Op eveDim) * M * (Op.tensor U (1 : Op eveDim))ᴴ) =
      Op.tensor U (1 : Op eveDim) * measurementChannel n eveDim M *
        (Op.tensor U (1 : Op eveDim))ᴴ := by
  set Ut := Op.tensor U (1 : Op eveDim) with hUt
  have hUtU : Utᴴ * Ut = 1 := by
    rw [hUt, Op.tensor_conjTranspose, Matrix.conjTranspose_one, Op.tensor_mul, hU,
      Matrix.one_mul, Op.tensor_one]
  have hUUt : Ut * Utᴴ = 1 := mul_eq_one_comm.mpr hUtU
  have hconjP : ∀ ω, Utᴴ * bb84CompProjector n eveDim ω * Ut =
      bb84CompProjector n eveDim (π.symm ω) :=
    fun ω => compProjector_tensorU_conj U π hU hperm ω
  have hPUt : ∀ ξ, bb84CompProjector n eveDim ξ * Ut =
      Ut * bb84CompProjector n eveDim (π.symm ξ) := by
    intro ξ
    calc bb84CompProjector n eveDim ξ * Ut
           = Ut * (Utᴴ * bb84CompProjector n eveDim ξ * Ut) := by
          rw [show Ut * (Utᴴ * bb84CompProjector n eveDim ξ * Ut)
                = (Ut * Utᴴ) * bb84CompProjector n eveDim ξ * Ut from by noncomm_ring,
            hUUt, Matrix.one_mul]
      _ = Ut * bb84CompProjector n eveDim (π.symm ξ) := by rw [hconjP]
  have hUtP : ∀ ξ, Utᴴ * bb84CompProjector n eveDim ξ =
      bb84CompProjector n eveDim (π.symm ξ) * Utᴴ := by
    intro ξ
    calc Utᴴ * bb84CompProjector n eveDim ξ
           = (Utᴴ * bb84CompProjector n eveDim ξ * Ut) * Utᴴ := by
          rw [show (Utᴴ * bb84CompProjector n eveDim ξ * Ut) * Utᴴ
                = Utᴴ * bb84CompProjector n eveDim ξ * (Ut * Utᴴ) from by noncomm_ring,
            hUUt, Matrix.mul_one]
      _ = bb84CompProjector n eveDim (π.symm ξ) * Utᴴ := by rw [hconjP]
  rw [measurementChannel_eq_sum_compProjector_conj, measurementChannel_eq_sum_compProjector_conj,
    Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp π (fun ω => bb84CompProjector n eveDim ω * (Ut * M * Utᴴ) *
      bb84CompProjector n eveDim ω)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  calc bb84CompProjector n eveDim (π ω) * (Ut * M * Utᴴ) * bb84CompProjector n eveDim (π ω)
         = (bb84CompProjector n eveDim (π ω) * Ut) * M *
          (Utᴴ * bb84CompProjector n eveDim (π ω)) := by noncomm_ring
    _ = (Ut * bb84CompProjector n eveDim (π.symm (π ω))) * M *
          (bb84CompProjector n eveDim (π.symm (π ω)) * Utᴴ) := by rw [hPUt, hUtP]
    _ = (Ut * bb84CompProjector n eveDim ω) * M * (bb84CompProjector n eveDim ω * Utᴴ) := by
          rw [Equiv.symm_apply_apply]
    _ = Ut * (bb84CompProjector n eveDim ω * M * bb84CompProjector n eveDim ω) * Utᴴ := by
          noncomm_ring

/-- The single-pair key-round outcome map `bellKeyOutcomePerm k` is an involution of `Fin 4`
(identity or the reversal `(0 3)(1 2)`), hence a permutation. -/
theorem bellKeyOutcomePerm_involutive (k : Fin 4) :
    Function.Involutive (bellKeyOutcomePerm k) := by
  intro x; fin_cases k <;> fin_cases x <;> rfl

/-- The single-pair key-round outcome **permutation** `ω ↦ g·ω` as an `Equiv.Perm (Fin 4)`,
built from the involution `bellKeyOutcomePerm k`. -/
def bellKeyOutcomePermEquiv (k : Fin 4) : Equiv.Perm (Fin 4) :=
  (bellKeyOutcomePerm_involutive k).toPerm

/-- **The `n`-fold monomial (signed-permutation) property of the Bell twirl unitary.**  Each
per-string bilateral-Pauli twirl unitary `bellTwirlUnitary n g` permutes the computational-basis
outcome projectors: there is a permutation `π` of the `4ⁿ` outcome strings with `U · |ω⟩⟨ω| · Uᴴ =
|πω⟩⟨πω|`.  `bellTwirlUnitary n g = ⊗ₐ G(g a)` is the `n`-fold tensor of the single-pair signed
permutations, each proven monomial by `bb84BellSinglePair_conj_compProjector`; the outcome
permutation `π` is the product of the per-pair `bellKeyOutcomePerm`, and the outcome projector is
the tensor family of the per-pair projectors (`tensorFamily_single_one`). -/
theorem bellTwirlUnitary_permutes_compProjectors {n : ℕ} (g : Fin n → Fin 4) :
    ∃ π : Equiv.Perm (Fin (4 ^ n)),
      ∀ ω : Fin (4 ^ n),
        bellTwirlUnitary n g * (Matrix.single ω ω 1 : Op (4 ^ n)) * (bellTwirlUnitary n g)ᴴ =
          Matrix.single (π ω) (π ω) 1 := by
  refine ⟨(@finFunctionFinEquiv 4 n).symm.trans
      ((Equiv.piCongrRight (fun a => bellKeyOutcomePermEquiv (g a))).trans
          (@finFunctionFinEquiv 4 n)),
      fun ω => ?_⟩
  set s : Fin n → Fin 4 := (@finFunctionFinEquiv 4 n).symm ω with hs
  have hU : bellTwirlUnitary n g = tensorFamily (fun a => bb84BellSinglePairTwirlGroup (g a)) := rfl
  have hsingle : (Matrix.single ω ω 1 : Op (4 ^ n)) =
      tensorFamily (fun a => (Matrix.single (s a) (s a) 1 : Op 4)) := by
    rw [tensorFamily_single_one, hs, Equiv.apply_symm_apply]
  rw [hU, hsingle, conjTranspose_tensorFamily, tensorFamily_mul, tensorFamily_mul]
  have hbody : (fun a => bb84BellSinglePairTwirlGroup (g a) * (Matrix.single (s a) (s a) 1 : Op 4) *
        (bb84BellSinglePairTwirlGroup (g a))ᴴ) =
      (fun a => (Matrix.single (bellKeyOutcomePerm (g a) (s a))
        (bellKeyOutcomePerm (g a) (s a)) 1 : Op 4)) :=
    funext (fun a => bb84BellSinglePair_conj_compProjector (g a) (s a))
  rw [hbody, tensorFamily_single_one]
  have hfun : (fun a => bellKeyOutcomePerm (g a) (s a)) =
      (Equiv.piCongrRight (fun a => bellKeyOutcomePermEquiv (g a)))
        ((@finFunctionFinEquiv 4 n).symm ω) := by
    funext a
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, bellKeyOutcomePermEquiv,
      Function.Involutive.coe_toPerm, hs]
  have hAB : @finFunctionFinEquiv 4 n (fun a => bellKeyOutcomePerm (g a) (s a)) =
      ((@finFunctionFinEquiv 4 n).symm.trans
        ((Equiv.piCongrRight (fun a => bellKeyOutcomePermEquiv (g a))).trans
          (@finFunctionFinEquiv 4 n))) ω := by
    rw [Equiv.trans_apply, Equiv.trans_apply, ← hfun]
  rw [hAB]

/-- **The `n`-round measurement-channel covariance (outcome relabel).**  The key-round
computational measurement commutes with conjugation by the IID bilateral-Pauli twirl unitary
`bellTwirlUnitary n g ⊗ 1_E`:
`measurementChannel((U⊗1) · M · (U⊗1)ᴴ) = (U⊗1) · measurementChannel(M) · (U⊗1)ᴴ`.

This is the "key round = signed Pauli passing through as an outcome relabel" of the round kernel:
because the twirl unitary is a computational-basis monomial it permutes the outcome projectors, and
the dephasing measurement is invariant under that permutation (the relabel is realised intrinsically
as the conjugation, with the public measurement API only).  Assembled from the reusable
`measurementChannel_conj_eq_of_permutesCompProjectors` and the (single-pair-proven) `n`-fold
monomial property `bellTwirlUnitary_permutes_compProjectors`. -/
theorem measurementChannel_bellTwirl_outcomeRelabel {n eveDim : ℕ} [NeZero eveDim]
    (g : Fin n → Fin 4) (M : Op (4 ^ n * eveDim)) :
    measurementChannel n eveDim
        (Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim) * M *
          (Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim))ᴴ) =
      Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim) *
        measurementChannel n eveDim M *
        (Op.tensor (bellTwirlUnitary n g) (1 : Op eveDim))ᴴ := by
  obtain ⟨π, hπ⟩ := bellTwirlUnitary_permutes_compProjectors g
  exact measurementChannel_conj_eq_of_permutesCompProjectors (bellTwirlUnitary n g) π
    (bellTwirlUnitary_unitary n g) hπ M

end QKD.BB84.Engine

end
