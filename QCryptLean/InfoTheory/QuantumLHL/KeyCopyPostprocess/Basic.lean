import QCryptLean.InfoTheory.QuantumLHL.SmoothingSideConditions
import QCryptLean.Quantum.Channels.CPTP.FintypeKraus
import QCryptLean.Quantum.TensorProducts.Trace

/-!
# Key-Copy Postprocessing — fixed-transcript LHL channel and block formulas

Defines the fixed-transcript key-copy postprocessing channel used to map LHL
joint states into protocol output registers.  The channel traces Eve's register,
copies the classical key into Alice and Bob output keys, writes a fixed transcript,
and preserves the reference register.

## Main definitions
- `keyCopyPostprocessInputIndex`: packed input index for Eve, reference, and key.
- `keyCopyPostprocessOutputIndex`: packed output index for copied keys, transcript, and reference.
- `keyCopyPostprocessKraus`: Kraus operator for a fixed Eve basis index.
- `keyCopyPostprocess`: fixed-transcript postprocessing channel.
- `keyCopyPostprocessOutputBlock`: embedded reference block for one copied key.

## Main statements
- `keyCopyPostprocess_isCPTP`: the fixed-transcript channel is CPTP.
- `keyCopyPostprocess_toJointDensity_eq_sum_outputBlocks`: action on a CQ joint density.
- `keyCopyPostprocess_uniformOutput_toJointDensity_eq_sum_outputBlocks`:
  action on the uniform target.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.QuantumLHL

open InfoTheory.SmoothMinEntropy
open Quantum.Channels

/-- Reverse three finite sums, keeping the middle sum in the middle. -/
lemma fintype_sum_three_reverse
    {α β γ M : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M]
    (f : α → β → γ → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, f a b c) =
      ∑ c : γ, ∑ b : β, ∑ a : α, f a b c := by
  calc
    (∑ a : α, ∑ b : β, ∑ c : γ, f a b c)
        = ∑ b : β, ∑ a : α, ∑ c : γ, f a b c := by
          exact Finset.sum_comm
    _ = ∑ b : β, ∑ c : γ, ∑ a : α, f a b c := by
          apply Finset.sum_congr rfl
          intro b _
          exact Finset.sum_comm
    _ = ∑ c : γ, ∑ b : β, ∑ a : α, f a b c := by
          exact Finset.sum_comm

/-- Reverse the order of four finite sums. -/
lemma fintype_sum_four_reverse
    {α β γ δ M : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M]
    (f : α → β → γ → δ → M) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d) =
      ∑ d : δ, ∑ c : γ, ∑ b : β, ∑ a : α, f a b c d := by
  calc
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a b c d)
        = ∑ a : α, ∑ b : β, ∑ d : δ, ∑ c : γ, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          exact Finset.sum_comm
    _ = ∑ a : α, ∑ d : δ, ∑ b : β, ∑ c : γ, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
    _ = ∑ d : δ, ∑ a : α, ∑ b : β, ∑ c : γ, f a b c d := by
          exact Finset.sum_comm
    _ = ∑ d : δ, ∑ a : α, ∑ c : γ, ∑ b : β, f a b c d := by
          apply Finset.sum_congr rfl
          intro d _
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
    _ = ∑ d : δ, ∑ c : γ, ∑ a : α, ∑ b : β, f a b c d := by
          apply Finset.sum_congr rfl
          intro d _
          exact Finset.sum_comm
    _ = ∑ d : δ, ∑ c : γ, ∑ b : β, ∑ a : α, f a b c d := by
          apply Finset.sum_congr rfl
          intro d _
          apply Finset.sum_congr rfl
          intro c _
          exact Finset.sum_comm

/-- Reverse four finite sums and push a matrix-entry `if` past scalar
multiplication. -/
lemma fintype_sum_four_reverse_mul_ite_matrix_apply
    {α β γ δ ρ σ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (P : α → Prop) [DecidablePred P]
    (c : ℂ)
    (M : α → β → γ → δ → Matrix ρ σ ℂ)
    (p : ρ) (q : σ) :
    (∑ a : α, ∑ b : β, ∑ g : γ, ∑ d : δ,
      c * ((if P a then M a b g d else 0) p q)) =
      ∑ d : δ, ∑ g : γ, ∑ a : α, ∑ b : β,
        if P a then c * M a b g d p q else 0 := by
  rw [fintype_sum_four_reverse]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : P a
  · simp [h]
  · simp [h]

/-- Applying a bundled linear map after transporting its domain is the same as
transporting the argument in the opposite direction. -/
lemma linearMap_cast_domain_apply
    {n n' m : ℕ}
    (h : n' = n)
    (Φ : Op n' →ₗ[ℂ] Op m)
    (M : Op n) :
    (cast (congrArg (fun d => Op d →ₗ[ℂ] Op m) h) Φ) M =
      Φ (cast (congrArg Op h.symm) M) := by
  cases h
  rfl

/-- `CQState.toJointDensity` specialized to a `Fin keyDim` classical register,
transported from `Fintype.card (Fin keyDim)` to `keyDim`.

The resulting concrete key coordinate is the `Fintype.equivFin` coordinate used
internally by `CQState.toJointDensity`. -/
lemma cqState_toJointDensity_toOp_fin_cast_eq_reindex_blockDiagonal
    (keyDim n : ℕ) [NeZero keyDim]
    (ρ : CQState (Fin keyDim) n) :
    cast
        (congrArg Op
          (show n * Fintype.card (Fin keyDim) = n * keyDim by
            rw [Fintype.card_fin]))
        ρ.toJointDensity.toOp =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.blockDiagonal fun z : Fin keyDim =>
          (ρ.stateMap
            ((Fintype.equivFin (Fin keyDim)).symm
              (Fin.cast (Fintype.card_fin keyDim).symm z))).toOp) := by
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  ext i j
  rw [Quantum.Operators.Op.cast_congrArg_apply
    (h := (show n * Fintype.card (Fin keyDim) = n * keyDim by
      rw [Fintype.card_fin]))]
  have hcard : Fintype.card (Fin keyDim) = keyDim := Fintype.card_fin keyDim
  have hmod_i :
      (Fin.cast
        (by rw [Fintype.card_fin] :
          n * keyDim = n * Fintype.card (Fin keyDim)) i).modNat =
        Fin.cast hcard.symm i.modNat := by
    ext
    simp [Fin.val_cast, Fin.coe_modNat]
  have hmod_j :
      (Fin.cast
        (by rw [Fintype.card_fin] :
          n * keyDim = n * Fintype.card (Fin keyDim)) j).modNat =
        Fin.cast hcard.symm j.modNat := by
    ext
    simp [Fin.val_cast, Fin.coe_modNat]
  have hdiv_i :
      (Fin.cast
        (by rw [Fintype.card_fin] :
          n * keyDim = n * Fintype.card (Fin keyDim)) i).divNat =
        i.divNat := by
    ext
    simp [Fin.val_cast, Fin.coe_divNat]
  have hdiv_j :
      (Fin.cast
        (by rw [Fintype.card_fin] :
          n * keyDim = n * Fintype.card (Fin keyDim)) j).divNat =
        j.divNat := by
    ext
    simp [Fin.val_cast, Fin.coe_divNat]
  simp [Matrix.reindex_apply, Matrix.blockDiagonal_apply,
    hmod_i, hmod_j, hdiv_i, hdiv_j]

/-- Input index for the key-copy postprocessing channel:
`((eve, reference), key)`. -/
def keyCopyPostprocessInputIndex {keyDim eveDim refDim : ℕ}
    (e : Fin eveDim) (r : Fin refDim) (z : Fin keyDim) :
    Fin ((eveDim * refDim) * keyDim) :=
  finProdFinEquiv (finProdFinEquiv (e, r), z)

/-- Output index for the key-copy postprocessing channel:
`(((Alice key, Bob key), transcript), reference)`. -/
def keyCopyPostprocessOutputIndex {keyDim refDim transcriptDim : ℕ}
    (passTranscript : Fin transcriptDim) (z : Fin keyDim) (r : Fin refDim) :
    Fin ((keyDim * keyDim * transcriptDim) * refDim) :=
  finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (z, z), passTranscript), r)

/-- The reference coordinate of a key-copy output index is the reference index
used to build it. -/
lemma keyCopyPostprocessOutputIndex_modNat
    {keyDim refDim transcriptDim : ℕ}
    [NeZero refDim]
    (passTranscript : Fin transcriptDim) (z : Fin keyDim) (r : Fin refDim) :
    (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
      (transcriptDim := transcriptDim) passTranscript z r).modNat = r := by
  have h := finProdFinEquiv.symm_apply_apply
    (finProdFinEquiv (finProdFinEquiv (z, z), passTranscript), r)
  rw [finProdFinEquiv_symm_apply] at h
  exact congrArg Prod.snd h

/-- Equality of output indices with the transcript fixed is equality of the key
and reference indices. -/
lemma keyCopyPostprocessOutputIndex_eq_iff
    {keyDim refDim transcriptDim : ℕ}
    [NeZero keyDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim)
    {z z' : Fin keyDim} {r r' : Fin refDim} :
    keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
        passTranscript z r =
      keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
        passTranscript z' r' ↔
      z = z' ∧ r = r' := by
  constructor
  · intro h
    simpa [keyCopyPostprocessOutputIndex] using h
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A finite sum of matrix units with injective output labels has diagonal
adjoint-product on its input labels. -/
lemma matrix_single_sum_conjTranspose_mul_of_injective
    {ι outIdx inIdx : Type*}
    [Fintype ι]
    [Fintype outIdx] [DecidableEq outIdx]
    [DecidableEq inIdx]
    (out : ι → outIdx) (inn : ι → inIdx)
    (hout : Function.Injective out) :
    ((∑ i : ι, Matrix.single (out i) (inn i) (1 : ℂ))ᴴ *
        (∑ i : ι, Matrix.single (out i) (inn i) (1 : ℂ))) =
      ∑ i : ι, Matrix.single (inn i) (inn i) (1 : ℂ) := by
  classical
  rw [Matrix.conjTranspose_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : out i ≠ out j := by
      intro h
      exact hji (hout h).symm
    simp [hne]
  · intro hi
    simp at hi

/-- Conjugating by a finite sum of matrix units extracts the corresponding
input entries and writes them into the matching output matrix units. -/
lemma matrix_single_sum_mul_mul_conjTranspose
    {ι outIdx inIdx : Type*}
    [Fintype ι] [Fintype inIdx]
    [DecidableEq outIdx] [DecidableEq inIdx]
    (out : ι → outIdx) (inn : ι → inIdx)
    (A : Matrix inIdx inIdx ℂ) :
    (∑ i : ι, Matrix.single (out i) (inn i) (1 : ℂ)) * A *
        (∑ i : ι, Matrix.single (out i) (inn i) (1 : ℂ))ᴴ =
      ∑ i : ι, ∑ j : ι,
        A (inn i) (inn j) • Matrix.single (out i) (out j) (1 : ℂ) := by
  rw [Matrix.conjTranspose_sum]
  rw [Matrix.mul_sum]
  simp_rw [Matrix.sum_mul]
  simp only [Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single,
    one_mul, mul_one, Matrix.smul_single, smul_eq_mul]
  rw [Finset.sum_comm]

/-- A matrix unit is additive in its scalar entry over finite sums. -/
lemma matrix_single_finset_sum
    {ι outIdx inIdx : Type*}
    [Fintype ι] [DecidableEq outIdx] [DecidableEq inIdx]
    (out : outIdx) (inn : inIdx) (f : ι → ℂ) :
    Matrix.single out inn (∑ i : ι, f i) =
      ∑ i : ι, Matrix.single out inn (f i) := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.single_apply]
  by_cases h : out = p ∧ inn = q
  · simp [h]
  · simp [h]

/-- Kraus operator for a fixed Eve basis index.  It traces out Eve while preserving
the coherent reference block and copying the classical key to both output keys. -/
noncomputable def keyCopyPostprocessKraus
    (keyDim eveDim refDim transcriptDim : ℕ)
    (passTranscript : Fin transcriptDim)
    (e : Fin eveDim) :
    Matrix (Fin ((keyDim * keyDim * transcriptDim) * refDim))
      (Fin ((eveDim * refDim) * keyDim)) ℂ :=
  ∑ r : Fin refDim, ∑ z : Fin keyDim,
    Matrix.single
      (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
        passTranscript z r)
      (keyCopyPostprocessInputIndex (keyDim := keyDim) (eveDim := eveDim)
        (refDim := refDim) e r z)
      (1 : ℂ)

/-- Product-index form of `keyCopyPostprocessKraus`. -/
lemma keyCopyPostprocessKraus_eq_sum_prod
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim)
    (e : Fin eveDim) :
    keyCopyPostprocessKraus keyDim eveDim refDim transcriptDim passTranscript e =
      ∑ p : Fin refDim × Fin keyDim,
        Matrix.single
          (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
            passTranscript p.2 p.1)
          (keyCopyPostprocessInputIndex (keyDim := keyDim) (eveDim := eveDim)
            (refDim := refDim) e p.1 p.2)
          (1 : ℂ) := by
  unfold keyCopyPostprocessKraus
  exact (Fintype.sum_prod_type'
    (fun r : Fin refDim => fun z : Fin keyDim =>
      Matrix.single
        (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
          passTranscript z r)
        (keyCopyPostprocessInputIndex (keyDim := keyDim) (eveDim := eveDim)
          (refDim := refDim) e r z)
        (1 : ℂ))).symm

/-- For a fixed Eve index, the key-copy Kraus operator is an isometry on the
input block with that Eve index. -/
lemma keyCopyPostprocessKraus_adjoint_mul
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim)
    (e : Fin eveDim) :
    (keyCopyPostprocessKraus keyDim eveDim refDim transcriptDim passTranscript e)ᴴ *
        keyCopyPostprocessKraus keyDim eveDim refDim transcriptDim passTranscript e =
      ∑ r : Fin refDim, ∑ z : Fin keyDim,
        Matrix.single
          (keyCopyPostprocessInputIndex (keyDim := keyDim) (eveDim := eveDim)
            (refDim := refDim) e r z)
          (keyCopyPostprocessInputIndex (keyDim := keyDim) (eveDim := eveDim)
            (refDim := refDim) e r z)
          (1 : ℂ) := by
  rw [keyCopyPostprocessKraus_eq_sum_prod]
  rw [matrix_single_sum_conjTranspose_mul_of_injective]
  · exact Fintype.sum_prod_type'
      (fun r : Fin refDim => fun z : Fin keyDim =>
        Matrix.single
          (keyCopyPostprocessInputIndex (keyDim := keyDim) (eveDim := eveDim)
            (refDim := refDim) e r z)
          (keyCopyPostprocessInputIndex (keyDim := keyDim) (eveDim := eveDim)
            (refDim := refDim) e r z)
          (1 : ℂ))
  · intro p q h
    have hp := (keyCopyPostprocessOutputIndex_eq_iff
      (keyDim := keyDim) (refDim := refDim) (transcriptDim := transcriptDim)
      passTranscript).1 h
    exact Prod.ext hp.2 hp.1

/-- The diagonal matrix units indexed by `((e, r), z)` partition the whole input
space. -/
lemma keyCopyPostprocessInputIndex_sum_single_one
    (keyDim eveDim refDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] :
    (∑ e : Fin eveDim, ∑ r : Fin refDim, ∑ z : Fin keyDim,
      Matrix.single
        (keyCopyPostprocessInputIndex (keyDim := keyDim) (eveDim := eveDim)
          (refDim := refDim) e r z)
        (keyCopyPostprocessInputIndex (keyDim := keyDim) (eveDim := eveDim)
          (refDim := refDim) e r z)
        (1 : ℂ)) =
      (1 : Op ((eveDim * refDim) * keyDim)) := by
  rw [← Fintype.sum_prod_type']
  rw [← Fintype.sum_prod_type']
  let f : (Fin eveDim × Fin refDim) × Fin keyDim ≃
      Fin ((eveDim * refDim) * keyDim) :=
    (finProdFinEquiv.prodCongr (Equiv.refl (Fin keyDim))).trans finProdFinEquiv
  exact Eq.trans
    (Equiv.sum_comp f
      (fun i : Fin ((eveDim * refDim) * keyDim) => Matrix.single i i (1 : ℂ)))
    Matrix.sum_single_one

/-- The generic postprocessing map from an LHL joint extractor state to the
protocol output layout. -/
noncomputable def keyCopyPostprocess
    (keyDim eveDim refDim transcriptDim : ℕ)
    (passTranscript : Fin transcriptDim) :
    Op ((eveDim * refDim) * keyDim) →ₗ[ℂ]
      Op ((keyDim * keyDim * transcriptDim) * refDim) :=
  krausMapFintype (keyCopyPostprocessKraus keyDim eveDim refDim transcriptDim passTranscript)

/-- Completeness of the key-copy Kraus family.  This is the low-level finite-index
calculation: for every input basis vector `((e, r), z)`, exactly the Kraus operator
indexed by `e` contributes, and the output embedding is injective in `(r, z)`. -/
lemma keyCopyPostprocessKraus_completeness
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim) :
    ∑ e : Fin eveDim,
        (keyCopyPostprocessKraus keyDim eveDim refDim transcriptDim passTranscript e)ᴴ *
          keyCopyPostprocessKraus keyDim eveDim refDim transcriptDim passTranscript e =
      (1 : Op ((eveDim * refDim) * keyDim)) := by
  simp_rw [keyCopyPostprocessKraus_adjoint_mul]
  exact keyCopyPostprocessInputIndex_sum_single_one keyDim eveDim refDim

/-- The key-copy postprocessing map is CPTP. -/
theorem keyCopyPostprocess_isCPTP
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    [NeZero ((eveDim * refDim) * keyDim)]
    [NeZero ((keyDim * keyDim * transcriptDim) * refDim)]
    (passTranscript : Fin transcriptDim) :
    IsCPTP (⇑(keyCopyPostprocess keyDim eveDim refDim transcriptDim passTranscript)) := by
  exact
    krausMapFintype_isCPTP
      (K := keyCopyPostprocessKraus keyDim eveDim refDim transcriptDim passTranscript)
      (keyCopyPostprocessKraus_completeness keyDim eveDim refDim transcriptDim
        passTranscript)

/-- Embed a reference operator into the output block indexed by a duplicated key
and the fixed transcript value. -/
noncomputable def keyCopyPostprocessOutputBlock
    (keyDim refDim transcriptDim : ℕ)
    (passTranscript : Fin transcriptDim)
    (z : Fin keyDim)
    (B : Op refDim) :
    Op ((keyDim * keyDim * transcriptDim) * refDim) :=
  ∑ r : Fin refDim, ∑ r' : Fin refDim,
    B r r' •
      Matrix.single
        (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
          passTranscript z r)
        (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
          passTranscript z r')
        (1 : ℂ)

/-- At a fixed matrix entry, summing key-copy output matrix units over reference
coordinates picks the unit indexed by the reference coordinates of that entry. -/
lemma keyCopyPostprocessOutputIndex_sum_single_apply
    (keyDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim)
    (z : Fin keyDim)
    (F : Fin refDim → Fin refDim → ℂ)
    (p q : Fin ((keyDim * keyDim * transcriptDim) * refDim)) :
    (∑ r : Fin refDim, ∑ r' : Fin refDim,
      Matrix.single
        (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
          (transcriptDim := transcriptDim) passTranscript z r)
        (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
          (transcriptDim := transcriptDim) passTranscript z r')
        (F r r')) p q =
      Matrix.single
        (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
          (transcriptDim := transcriptDim) passTranscript z p.modNat)
        (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
          (transcriptDim := transcriptDim) passTranscript z q.modNat)
        (F p.modNat q.modNat) p q := by
  classical
  simp only [Matrix.sum_apply]
  rw [Finset.sum_eq_single p.modNat]
  · rw [Finset.sum_eq_single q.modNat]
    · intro r' _ hr'
      have hright :
          keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
              (transcriptDim := transcriptDim) passTranscript z r' ≠ q := by
        intro h
        have hmod := congrArg
          (fun x : Fin ((keyDim * keyDim * transcriptDim) * refDim) => x.modNat) h
        exact hr' (by simpa [keyCopyPostprocessOutputIndex_modNat] using hmod)
      simp [hright]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ q.modNat))
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro r' _
    have hleft :
        keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
            (transcriptDim := transcriptDim) passTranscript z r ≠ p := by
      intro h
      have hmod := congrArg
        (fun x : Fin ((keyDim * keyDim * transcriptDim) * refDim) => x.modNat) h
      exact hr (by simpa [keyCopyPostprocessOutputIndex_modNat] using hmod)
    simp [hleft]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ p.modNat))

/-- Entry form of a key-copy output block.  The block is supported on the fixed
copied-key/transcript coordinates, with the reference entry read from the
reference coordinates of the ambient output entry. -/
lemma keyCopyPostprocessOutputBlock_apply
    (keyDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim)
    (z : Fin keyDim)
    (B : Op refDim)
    (p q : Fin ((keyDim * keyDim * transcriptDim) * refDim)) :
    keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z B p q =
      Matrix.single
        (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
          (transcriptDim := transcriptDim) passTranscript z p.modNat)
        (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
          (transcriptDim := transcriptDim) passTranscript z q.modNat)
        (B p.modNat q.modNat) p q := by
  simpa [keyCopyPostprocessOutputBlock, Matrix.smul_single] using
    keyCopyPostprocessOutputIndex_sum_single_apply
      keyDim refDim transcriptDim passTranscript z B p q

/-- Action of one Eve-index Kraus operator on a Fin-indexed block family. -/
lemma keyCopyPostprocessKraus_reindex_blockDiagonal_conjTranspose
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim)
    (B : Fin keyDim → Op (eveDim * refDim))
    (e : Fin eveDim) :
    keyCopyPostprocessKraus keyDim eveDim refDim transcriptDim passTranscript e *
        (Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.blockDiagonal B)) *
        (keyCopyPostprocessKraus keyDim eveDim refDim transcriptDim passTranscript e)ᴴ =
      ∑ z : Fin keyDim, ∑ r : Fin refDim, ∑ r' : Fin refDim,
        B z (finProdFinEquiv (e, r)) (finProdFinEquiv (e, r')) •
          Matrix.single
            (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
              passTranscript z r)
            (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
              passTranscript z r')
            (1 : ℂ) := by
  rw [keyCopyPostprocessKraus_eq_sum_prod]
  rw [matrix_single_sum_mul_mul_conjTranspose]
  simp only [keyCopyPostprocessInputIndex, keyCopyPostprocessOutputIndex,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.blockDiagonal_apply, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [Fintype.sum_prod_type_right]
  simp_rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single z]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hz
    exfalso
    exact hz (Finset.mem_univ z)

/-- Fin-indexed block-family action of the key-copy postprocessing channel. -/
lemma keyCopyPostprocess_reindex_blockDiagonal_fin_eq_sum_outputBlocks
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim)
    (B : Fin keyDim → Op (eveDim * refDim)) :
    keyCopyPostprocess keyDim eveDim refDim transcriptDim passTranscript
        (Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.blockDiagonal B)) =
      ∑ z : Fin keyDim,
        keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
          (partialTraceA (B z)) := by
  unfold keyCopyPostprocess Quantum.Channels.krausMapFintype
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [keyCopyPostprocessKraus_reindex_blockDiagonal_conjTranspose]
  simp only [keyCopyPostprocessOutputBlock, Quantum.TensorProducts.partialTraceA,
    Matrix.of_apply, Matrix.smul_single, smul_eq_mul, mul_one]
  simp_rw [matrix_single_finset_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]

/-- Relabeling an arbitrary classical block diagonal by `Fintype.equivFin`
produces the corresponding `Fin`-indexed block family. -/
lemma reindex_equivFin_blockDiagonal_eq_fin
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    {n : ℕ}
    (B : Z → Op n) :
    Matrix.reindex
        (((Equiv.refl (Fin n)).prodCongr (Fintype.equivFin Z)).trans finProdFinEquiv)
        (((Equiv.refl (Fin n)).prodCongr (Fintype.equivFin Z)).trans finProdFinEquiv)
        (Matrix.blockDiagonal B) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.blockDiagonal fun z : Fin (Fintype.card Z) =>
          B ((Fintype.equivFin Z).symm z)) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.blockDiagonal_apply]

/-- Block action on a CQ joint-density input.  The `CQState.toJointDensity`
quantum-first block at key `z` is traced over Eve and embedded as the duplicated
key output block.  The channel key dimension is `Fintype.card Z`, matching the
classical register dimension used by `CQState.toJointDensity`. -/
theorem keyCopyPostprocess_toJointDensity_eq_sum_outputBlocks
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (eveDim refDim transcriptDim : ℕ)
    [NeZero (Fintype.card Z)] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim)
    (ρ : CQState Z (eveDim * refDim)) :
    keyCopyPostprocess (Fintype.card Z) eveDim refDim transcriptDim passTranscript
        ρ.toJointDensity.toOp =
      ∑ z : Z,
        keyCopyPostprocessOutputBlock (Fintype.card Z) refDim transcriptDim passTranscript
          (Fintype.equivFin Z z)
          (partialTraceA ((ρ.stateMap z).toOp)) := by
  rw [CQState.toJointDensity_toOp_eq_reindex_blockDiagonal]
  rw [reindex_equivFin_blockDiagonal_eq_fin]
  rw [keyCopyPostprocess_reindex_blockDiagonal_fin_eq_sum_outputBlocks]
  rw [← Equiv.sum_comp (Fintype.equivFin Z)]
  simp

/-- Summing copied-key output blocks is invariant under relabeling the output
key and oppositely relabeling the payload family. -/
lemma keyCopyPostprocessOutputBlock_sum_equiv
    (keyDim refDim transcriptDim : ℕ)
    (passTranscript : Fin transcriptDim)
    (π : Fin keyDim ≃ Fin keyDim)
    (B : Fin keyDim → Op refDim) :
    (∑ z : Fin keyDim,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z (B (π.symm z))) =
    ∑ z : Fin keyDim,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript (π z) (B z) := by
  rw [← Equiv.sum_comp π]
  simp only [Equiv.symm_apply_apply]

/-- Block action on a `Fin keyDim` CQ joint-density input after transporting
the input dimension from `Fintype.card (Fin keyDim)` to `keyDim`.

The output key coordinate is the concrete coordinate induced by the
`Fintype.equivFin` convention inside `CQState.toJointDensity`. -/
theorem keyCopyPostprocess_fin_toJointDensity_eq_sum_outputBlocks
    (keyDim eveDim refDim transcriptDim : ℕ)
    [NeZero keyDim] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim)
    (ρ : CQState (Fin keyDim) (eveDim * refDim)) :
    (cast
      (congrArg
        (fun d => Op d →ₗ[ℂ] Op ((keyDim * keyDim * transcriptDim) * refDim))
        (show (eveDim * refDim) * keyDim =
            (eveDim * refDim) * Fintype.card (Fin keyDim) by
          rw [Fintype.card_fin]))
      (keyCopyPostprocess keyDim eveDim refDim transcriptDim passTranscript))
      ρ.toJointDensity.toOp =
    ∑ z : Fin keyDim,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript
        (Fin.cast (Fintype.card_fin keyDim) ((Fintype.equivFin (Fin keyDim)) z))
        (partialTraceA ((ρ.stateMap z).toOp)) := by
  rw [linearMap_cast_domain_apply
    (h := (show (eveDim * refDim) * keyDim =
        (eveDim * refDim) * Fintype.card (Fin keyDim) by
      rw [Fintype.card_fin]))]
  rw [cqState_toJointDensity_toOp_fin_cast_eq_reindex_blockDiagonal]
  rw [keyCopyPostprocess_reindex_blockDiagonal_fin_eq_sum_outputBlocks]
  let π : Fin keyDim ≃ Fin keyDim :=
    (Fintype.equivFin (Fin keyDim)).trans (finCongr (Fintype.card_fin keyDim))
  change (∑ z : Fin keyDim,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
        (partialTraceA
          ((ρ.stateMap (π.symm z)).toOp))) =
    ∑ z : Fin keyDim,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript (π z)
        (partialTraceA ((ρ.stateMap z).toOp))
  exact keyCopyPostprocessOutputBlock_sum_equiv keyDim refDim transcriptDim passTranscript π
    (fun z => partialTraceA ((ρ.stateMap z).toOp))

/-- Uniform-output block action.  A uniform extractor key produces the same
reference marginal in every duplicated-key output block, scaled by `1 / |Z|`. -/
theorem keyCopyPostprocess_uniformOutput_toJointDensity_eq_sum_outputBlocks
    {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (eveDim refDim transcriptDim : ℕ)
    [NeZero (Fintype.card Z)] [NeZero eveDim] [NeZero refDim] [NeZero transcriptDim]
    (passTranscript : Fin transcriptDim)
    (σ : SubDensityOp (eveDim * refDim)) :
    keyCopyPostprocess (Fintype.card Z) eveDim refDim transcriptDim passTranscript
        ((uniformOutputState (Z := Z) σ :
          CQState Z (eveDim * refDim)).toJointDensity.toOp) =
    ∑ z : Z,
      keyCopyPostprocessOutputBlock (Fintype.card Z) refDim transcriptDim passTranscript
        (Fintype.equivFin Z z)
        (((1 / (Fintype.card Z : ℝ) : ℝ) : ℂ) • partialTraceA σ.toOp) := by
  rw [keyCopyPostprocess_toJointDensity_eq_sum_outputBlocks]
  simp_rw [uniformOutput_stateMap_toOp]
  simp_rw [Quantum.TensorProducts.partialTraceA_smul]

end InfoTheory.QuantumLHL

end -- noncomputable section
