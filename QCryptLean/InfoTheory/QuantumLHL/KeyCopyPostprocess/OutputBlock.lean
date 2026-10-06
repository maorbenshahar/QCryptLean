import QCryptLean.InfoTheory.QuantumLHL.KeyCopyPostprocess.Basic

/-!
# Key-Copy Output Blocks — linearity, partial traces, and hash-indexed sums

Provides algebraic lemmas for copied-key output blocks.  These lemmas distribute
output-block embeddings over sums, scalar multiples, partial traces, and hash-fiber
sums, giving the entrywise bridge used by concrete protocol LHL comparisons.

## Main statements
- `keyCopyPostprocessOutputBlock_add`: output blocks are additive in the payload.
- `keyCopyPostprocessOutputBlock_smul`: output blocks are homogeneous in the payload.
- `keyCopyPostprocessOutputBlock_sum_hash_smul_partialTraceA_sum_ite_apply`:
  entrywise hash-fiber expansion.
- `keyCopyPostprocessOutputBlock_sum_hash_real_smul_partialTraceA_sum_ite_apply`:
  real-weighted hash-fiber expansion.
-/

open Quantum.Operators Quantum.TensorProducts Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.QuantumLHL

lemma keyCopyPostprocessOutputBlock_add
    (keyDim refDim transcriptDim : ℕ)
    (passTranscript : Fin transcriptDim)
    (z : Fin keyDim)
    (B C : Op refDim) :
    keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z (B + C) =
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z B +
        keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z C := by
  simp [keyCopyPostprocessOutputBlock, Finset.sum_add_distrib, add_smul]

/-- A copied-key output block is homogeneous in its reference operator. -/
lemma keyCopyPostprocessOutputBlock_smul
    (keyDim refDim transcriptDim : ℕ)
    (passTranscript : Fin transcriptDim)
    (z : Fin keyDim)
    (c : ℂ)
    (B : Op refDim) :
    keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z (c • B) =
      c • keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z B := by
  simp [keyCopyPostprocessOutputBlock, Finset.smul_sum]

/-- A copied-key output block distributes over finite sums of reference operators. -/
lemma keyCopyPostprocessOutputBlock_finset_sum
    (keyDim refDim transcriptDim : ℕ)
    (passTranscript : Fin transcriptDim)
    (z : Fin keyDim)
    {ι : Type*} (s : Finset ι) (B : ι → Op refDim) :
    keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
        (∑ i ∈ s, B i) =
      ∑ i ∈ s,
        keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
          (B i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [keyCopyPostprocessOutputBlock]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [keyCopyPostprocessOutputBlock_add]
      rw [ih]

/-- A copied-key output block distributes over finite type sums of reference operators. -/
lemma keyCopyPostprocessOutputBlock_sum
    (keyDim refDim transcriptDim : ℕ)
    (passTranscript : Fin transcriptDim)
    (z : Fin keyDim)
    {ι : Type*} [Fintype ι] (B : ι → Op refDim) :
    keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
        (∑ i, B i) =
      ∑ i,
        keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
          (B i) := by
  simpa using
    (keyCopyPostprocessOutputBlock_finset_sum keyDim refDim transcriptDim
      passTranscript z Finset.univ B)

/-- A copied-key output block distributes over a scaled partial trace of a finite sum. -/
lemma keyCopyPostprocessOutputBlock_smul_partialTraceA_finset_sum
    (keyDim refDim transcriptDim eveDim : ℕ)
    (passTranscript : Fin transcriptDim)
    (z : Fin keyDim)
    (c : ℂ)
    {ι : Type*} (s : Finset ι) (B : ι → Op (eveDim * refDim)) :
    keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
        (c • partialTraceA (∑ i ∈ s, B i)) =
      c • ∑ i ∈ s,
        keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
          (partialTraceA (B i)) := by
  rw [partialTraceA_finset_sum]
  rw [keyCopyPostprocessOutputBlock_smul]
  rw [keyCopyPostprocessOutputBlock_finset_sum]

/-- A copied-key output block distributes over a scaled partial trace of a finite-type sum. -/
lemma keyCopyPostprocessOutputBlock_smul_partialTraceA_sum
    (keyDim refDim transcriptDim eveDim : ℕ)
    (passTranscript : Fin transcriptDim)
    (z : Fin keyDim)
    (c : ℂ)
    {ι : Type*} [Fintype ι] (B : ι → Op (eveDim * refDim)) :
    keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
        (c • partialTraceA (∑ i, B i)) =
      c • ∑ i,
        keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
          (partialTraceA (B i)) := by
  simpa using
    (keyCopyPostprocessOutputBlock_smul_partialTraceA_finset_sum
      keyDim refDim transcriptDim eveDim passTranscript z c Finset.univ B)

/-- A copied-key output block distributes over a scaled partial trace of a filtered sum. -/
lemma keyCopyPostprocessOutputBlock_smul_partialTraceA_sum_ite
    (keyDim refDim transcriptDim eveDim : ℕ)
    (passTranscript : Fin transcriptDim)
    (z : Fin keyDim)
    (c : ℂ)
    {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (B : ι → Op (eveDim * refDim)) :
    keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
        (c • partialTraceA (∑ i, if P i then B i else 0)) =
      c • ∑ i,
        if P i then
          keyCopyPostprocessOutputBlock keyDim refDim transcriptDim passTranscript z
            (partialTraceA (B i))
        else 0 := by
  rw [keyCopyPostprocessOutputBlock_smul_partialTraceA_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : P i
  · simp [h]
  · simp [h, keyCopyPostprocessOutputBlock, partialTraceA]

/-- Entry form for a finite sum of copied-key output blocks whose payload is a
scaled partial trace of a filtered finite sum. -/
lemma keyCopyPostprocessOutputBlock_sum_smul_partialTraceA_sum_ite_apply
    (keyDim refDim transcriptDim eveDim : ℕ)
    [NeZero keyDim] [NeZero refDim] [NeZero transcriptDim]
    {S Ω : Type*} [Fintype S] [Fintype Ω]
    (passTranscript : S → Fin transcriptDim)
    (key : S → Fin keyDim)
    (c : ℂ)
    (P : Ω → Prop) [DecidablePred P]
    (B : Ω → Op (eveDim * refDim))
    (p q : Fin ((keyDim * keyDim * transcriptDim) * refDim)) :
    (∑ s : S,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim
        (passTranscript s) (key s)
        (c • partialTraceA (∑ ω : Ω, if P ω then B ω else 0))) p q =
      ∑ s : S,
        c * ∑ ω : Ω,
          if P ω then
            Matrix.single
              (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
                (transcriptDim := transcriptDim) (passTranscript s) (key s) p.modNat)
              (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
                (transcriptDim := transcriptDim) (passTranscript s) (key s) q.modNat)
              (∑ e : Fin eveDim,
                B ω (finProdFinEquiv (e, p.modNat)) (finProdFinEquiv (e, q.modNat))) p q
          else 0 := by
  simp_rw [keyCopyPostprocessOutputBlock_smul_partialTraceA_sum_ite]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω
  · simp [h, keyCopyPostprocessOutputBlock_apply, partialTraceA]
  · simp [h]

/-- Entry form for copied-key output blocks indexed by a hash constraint.  The
sum over output keys collapses to the key selected by `hash s ω`. -/
lemma keyCopyPostprocessOutputBlock_sum_hash_smul_partialTraceA_sum_ite_apply
    (keyDim refDim transcriptDim eveDim : ℕ)
    [NeZero keyDim] [NeZero refDim] [NeZero transcriptDim]
    {S Ω : Type*} [Fintype S] [Fintype Ω]
    (passTranscript : S → Fin transcriptDim)
    (hash : S → Ω → Fin keyDim)
    (c : ℂ)
    (B : S → Ω → Op (eveDim * refDim))
    (p q : Fin ((keyDim * keyDim * transcriptDim) * refDim)) :
    (∑ sz : S × Fin keyDim,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim
        (passTranscript sz.1) sz.2
        (c • partialTraceA
          (∑ ω : Ω, if hash sz.1 ω = sz.2 then B sz.1 ω else 0))) p q =
      ∑ s : S, ∑ ω : Ω,
        c * Matrix.single
          (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
            (transcriptDim := transcriptDim) (passTranscript s) (hash s ω) p.modNat)
          (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
            (transcriptDim := transcriptDim) (passTranscript s) (hash s ω) q.modNat)
          (∑ e : Fin eveDim,
            B s ω (finProdFinEquiv (e, p.modNat)) (finProdFinEquiv (e, q.modNat)))
          p q := by
  rw [Fintype.sum_prod_type]
  simp_rw [keyCopyPostprocessOutputBlock_smul_partialTraceA_sum_ite]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single (hash s ω)]
  · simp [keyCopyPostprocessOutputBlock_apply, partialTraceA]
  · intro z _ hz
    rw [if_neg]
    · rfl
    · exact hz.symm
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ (hash s ω)))

/-- Entry form for copied-key output blocks indexed by a hash constraint when the
payload is scaled by a real probability weight before partial tracing. -/
lemma keyCopyPostprocessOutputBlock_sum_hash_real_smul_partialTraceA_sum_ite_apply
    (keyDim refDim transcriptDim eveDim : ℕ)
    [NeZero keyDim] [NeZero refDim] [NeZero transcriptDim]
    {S Ω : Type*} [Fintype S] [Fintype Ω]
    (passTranscript : S → Fin transcriptDim)
    (hash : S → Ω → Fin keyDim)
    (c : ℝ)
    (B : S → Ω → Op (eveDim * refDim))
    (p q : Fin ((keyDim * keyDim * transcriptDim) * refDim)) :
    (∑ sz : S × Fin keyDim,
      keyCopyPostprocessOutputBlock keyDim refDim transcriptDim
        (passTranscript sz.1) sz.2
        (partialTraceA
          (c • ∑ ω : Ω, if hash sz.1 ω = sz.2 then B sz.1 ω else 0))) p q =
      ∑ s : S, ∑ ω : Ω,
        (c : ℂ) * Matrix.single
          (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
            (transcriptDim := transcriptDim) (passTranscript s) (hash s ω) p.modNat)
          (keyCopyPostprocessOutputIndex (keyDim := keyDim) (refDim := refDim)
            (transcriptDim := transcriptDim) (passTranscript s) (hash s ω) q.modNat)
          (∑ e : Fin eveDim,
            B s ω (finProdFinEquiv (e, p.modNat)) (finProdFinEquiv (e, q.modNat)))
          p q := by
  simp_rw [Quantum.TensorProducts.partialTraceA_real_smul]
  exact keyCopyPostprocessOutputBlock_sum_hash_smul_partialTraceA_sum_ite_apply
    keyDim refDim transcriptDim eveDim passTranscript hash (c : ℂ) B p q

end InfoTheory.QuantumLHL

end -- noncomputable section
