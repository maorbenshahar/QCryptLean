import QCryptLean.Quantum.Symmetry.PairedProjector

/-!
# Symmetric projectors on aligned direct sums

The aligned subspace selects matching block labels in each pair. Its symmetric projector has
trace `Nat.choose (n + x - 1) (x - 1)`, where `x` is the sum of the paired block dimensions.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Math.RepresentationTheory
open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace Quantum.Symmetry

/-- **Aligned-blocks indicator projector**: the diagonal projector onto tuples
    `(a₁,…,aₙ,r₁,…,rₙ)` lying in the *same* block at every round, i.e. onto
    `(⊕ᵢ(Aᵢ⊗Rᵢ))^{⊗n} ⊆ Aᵗᵒᵗⁿ ⊗ Rᵗᵒᵗⁿ`. -/
def alignedDirectSumProjector {k : ℕ} (dAv dRv : Fin k → ℕ) (n : ℕ)
    [NeZero (∑ i, dAv i)] [NeZero (∑ i, dRv i)] :
    Op ((∑ i, dAv i) ^ n * (∑ i, dRv i) ^ n) :=
  Matrix.diagonal (fun idx : Fin ((∑ i, dAv i) ^ n * (∑ i, dRv i) ^ n) =>
    let p := finProdFinEquiv.symm idx
    let a := (@finFunctionFinEquiv (∑ i, dAv i) n).symm p.1
    let r := (@finFunctionFinEquiv (∑ i, dRv i) n).symm p.2
    if ∀ t : Fin n, (finSigmaFinEquiv.symm (a t)).1 = (finSigmaFinEquiv.symm (r t)).1
      then (1 : ℂ) else 0)

/-- The aligned-blocks projector is Hermitian (diagonal, real 0/1 entries). -/
theorem alignedDirectSumProjector_isHermitian {k : ℕ} (dAv dRv : Fin k → ℕ) (n : ℕ)
    [NeZero (∑ i, dAv i)] [NeZero (∑ i, dRv i)] :
    (alignedDirectSumProjector dAv dRv n).IsHermitian := by
  unfold alignedDirectSumProjector
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  dsimp only
  split <;> simp [IsSelfAdjoint]

/-- The aligned-blocks projector is idempotent (diagonal, 0/1 entries). -/
theorem alignedDirectSumProjector_idem {k : ℕ} (dAv dRv : Fin k → ℕ) (n : ℕ)
    [NeZero (∑ i, dAv i)] [NeZero (∑ i, dRv i)] :
    alignedDirectSumProjector dAv dRv n * alignedDirectSumProjector dAv dRv n
      = alignedDirectSumProjector dAv dRv n := by
  unfold alignedDirectSumProjector
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext idx
  dsimp only
  split <;> ring

/-- The aligned-blocks projector is positive semidefinite. -/
theorem alignedDirectSumProjector_posSemidef {k : ℕ} (dAv dRv : Fin k → ℕ) (n : ℕ)
    [NeZero (∑ i, dAv i)] [NeZero (∑ i, dRv i)] :
    (alignedDirectSumProjector dAv dRv n).PosSemidef := by
  have hherm := alignedDirectSumProjector_isHermitian dAv dRv n
  have hidem := alignedDirectSumProjector_idem dAv dRv n
  rw [show alignedDirectSumProjector dAv dRv n
      = (alignedDirectSumProjector dAv dRv n)ᴴ * alignedDirectSumProjector dAv dRv n from by
    rw [hherm, hidem]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **`P_Sym` on the direct sum**: the sandwich `A · P_Sym · A` of the
    aligned-blocks projector `A` with the (single-space) symmetric projector `P_Sym` on
    `Aᵗᵒᵗ ⊗ Rᵗᵒᵗ`. This is `Symⁿ(⊕ᵢ(Aᵢ⊗Rᵢ))` — the intersection of the `Sₙ`-symmetric subspace
    with the aligned-blocks subspace (both are `Sₙ`-invariant and, mathematically, commute; the
    sandwich form makes Hermitian/PSD unconditional, §`symmetricProjectorDirectSum_isHermitian` /
    `_posSemidef` below, regardless of that commutation fact). -/
def symmetricProjectorDirectSum {k : ℕ} (dAv dRv : Fin k → ℕ) (n : ℕ)
    [NeZero (∑ i, dAv i)] [NeZero (∑ i, dRv i)] [NeZero n] :
    Op ((∑ i, dAv i) ^ n * (∑ i, dRv i) ^ n) :=
  alignedDirectSumProjector dAv dRv n
    * symmetricProjectorPairedGen (∑ i, dAv i) (∑ i, dRv i) n
    * alignedDirectSumProjector dAv dRv n

/-- `P_Sym` on the direct sum is Hermitian. -/
theorem symmetricProjectorDirectSum_isHermitian {k : ℕ} (dAv dRv : Fin k → ℕ) (n : ℕ)
    [NeZero (∑ i, dAv i)] [NeZero (∑ i, dRv i)] [NeZero n] :
    (symmetricProjectorDirectSum dAv dRv n).IsHermitian := by
  have hA : (alignedDirectSumProjector dAv dRv n)ᴴ = alignedDirectSumProjector dAv dRv n :=
    alignedDirectSumProjector_isHermitian dAv dRv n
  have hP : (symmetricProjectorPairedGen (∑ i, dAv i) (∑ i, dRv i) n)ᴴ
      = symmetricProjectorPairedGen (∑ i, dAv i) (∑ i, dRv i) n :=
    (symmetricProjectorPairedGen_is_projector (∑ i, dAv i) (∑ i, dRv i) n).2
  change (alignedDirectSumProjector dAv dRv n
      * symmetricProjectorPairedGen (∑ i, dAv i) (∑ i, dRv i) n
      * alignedDirectSumProjector dAv dRv n)ᴴ
    = alignedDirectSumProjector dAv dRv n
      * symmetricProjectorPairedGen (∑ i, dAv i) (∑ i, dRv i) n
      * alignedDirectSumProjector dAv dRv n
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hP]
  exact (mul_assoc _ _ _).symm

/-- `P_Sym` on the direct sum is positive semidefinite (via `(P_Sym·A)ᴴ·(P_Sym·A) = A·P_Sym·A`,
    using that `A` and `P_Sym` are each Hermitian and idempotent). -/
theorem symmetricProjectorDirectSum_posSemidef {k : ℕ} (dAv dRv : Fin k → ℕ) (n : ℕ)
    [NeZero (∑ i, dAv i)] [NeZero (∑ i, dRv i)] [NeZero n] :
    (symmetricProjectorDirectSum dAv dRv n).PosSemidef := by
  unfold symmetricProjectorDirectSum
  set A := alignedDirectSumProjector dAv dRv n with hAdef
  set P := symmetricProjectorPairedGen (∑ i, dAv i) (∑ i, dRv i) n with hPdef
  have hA : Aᴴ = A := alignedDirectSumProjector_isHermitian dAv dRv n
  have hP : Pᴴ = P := (symmetricProjectorPairedGen_is_projector (∑ i, dAv i) (∑ i, dRv i) n).2
  have hPidem : P * P = P :=
    (symmetricProjectorPairedGen_is_projector (∑ i, dAv i) (∑ i, dRv i) n).1
  have hkey : A * P * A = (P * A)ᴴ * (P * A) := by
    rw [Matrix.conjTranspose_mul, hA, hP, mul_assoc A P (P * A), ← mul_assoc P P A, hPidem,
      mul_assoc A P A]
  rw [hkey]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-! ## Counting the aligned per-round space

`Tr(P_Sym on the direct sum)` reduces, by the same orbit-counting argument as
`Math.RepresentationTheory.symmetricProjectorRep_trace`, to counting `Sₙ`-orbits of functions
valued in the **aligned per-round space** `Y = ⊕ᵢ(Aᵢ⊗Rᵢ)`, realized here as the subtype of
block-aligned `(Aᵗᵒᵗ,Rᵗᵒᵗ)`-index pairs (`IsAlignedPair`); `Fintype.card Y = Σᵢ dAv i · dRv i`
(`card_alignedPair_eq`), via `Equiv.subtypeProdEquivSigmaSubtype` plus the per-block fiber count
`card_blockIndexFiber_eq` (the fiber of `finSigmaFinEquiv` over block `i` has size `dv i`). -/

/-- The block index of an `Aᵗᵒᵗ := Σⱼ dv j`-index (decode via `finSigmaFinEquiv`). -/
private def blockIndex {k : ℕ} (dv : Fin k → ℕ) (a : Fin (∑ j, dv j)) : Fin k :=
  (finSigmaFinEquiv.symm a).1

/-- **Aligned pair predicate**: an `(Aᵗᵒᵗ,Rᵗᵒᵗ)`-index pair lying in the same block. -/
private def IsAlignedPair {k : ℕ} (dAv dRv : Fin k → ℕ)
    (p : Fin (∑ i, dAv i) × Fin (∑ i, dRv i)) : Prop :=
  blockIndex dAv p.1 = blockIndex dRv p.2

private instance instDecidablePredIsAlignedPair {k : ℕ} (dAv dRv : Fin k → ℕ) :
    DecidablePred (IsAlignedPair dAv dRv) :=
  fun p => inferInstanceAs (Decidable (blockIndex dAv p.1 = blockIndex dRv p.2))

/-- The fiber of `blockIndex dv` over `i` is in bijection with the block `Fin (dv i)`
(via the second `finSigmaFinEquiv` coordinate, `Nat`-cast along the fiber condition). -/
private def blockIndexFiberEquiv {k : ℕ} (dv : Fin k → ℕ) (i : Fin k) :
    {a : Fin (∑ j, dv j) // blockIndex dv a = i} ≃ Fin (dv i) where
  toFun a := Fin.cast (congrArg dv a.2) (finSigmaFinEquiv.symm a.1).2
  invFun x := ⟨finSigmaFinEquiv ⟨i, x⟩, by simp [blockIndex]⟩
  left_inv := by
    rintro ⟨a, ha⟩
    apply Subtype.ext
    simp only [blockIndex] at ha
    subst ha
    simpa only [Fin.cast_eq_self] using finSigmaFinEquiv.apply_symm_apply a
  right_inv := by
    intro x
    dsimp only
    apply Fin.ext
    rw [Fin.val_cast]
    exact congrArg (fun p => (p.snd : ℕ))
      (Equiv.symm_apply_apply finSigmaFinEquiv (⟨i, x⟩ : Σ j, Fin (dv j)))

/-- The block-`i` fiber of `blockIndex dv` has exactly `dv i` elements. -/
private lemma card_blockIndexFiber_eq {k : ℕ} (dv : Fin k → ℕ) (i : Fin k) :
    Fintype.card {a : Fin (∑ j, dv j) // blockIndex dv a = i} = dv i := by
  rw [Fintype.card_congr (blockIndexFiberEquiv dv i), Fintype.card_fin]

/-- **The aligned per-round space has dimension `x = Σᵢ dAv i · dRv i`.** -/
private lemma card_alignedPair_eq {k : ℕ} (dAv dRv : Fin k → ℕ) :
    Fintype.card {p : Fin (∑ i, dAv i) × Fin (∑ i, dRv i) // IsAlignedPair dAv dRv p}
      = ∑ i, dAv i * dRv i := by
  rw [Fintype.card_congr
    (Equiv.subtypeProdEquivSigmaSubtype (fun a r => IsAlignedPair dAv dRv (a, r))),
    Fintype.card_sigma]
  have hfib : ∀ a : Fin (∑ i, dAv i),
      Fintype.card {r : Fin (∑ i, dRv i) // IsAlignedPair dAv dRv (a, r)} =
        dRv (blockIndex dAv a) := by
    intro a
    rw [Fintype.card_congr
      (Equiv.subtypeEquivRight
        (fun r => show IsAlignedPair dAv dRv (a, r) ↔ blockIndex dRv r = blockIndex dAv a from
          Iff.symm eq_comm)),
      card_blockIndexFiber_eq]
  simp_rw [hfib]
  rw [show (∑ a : Fin (∑ i, dAv i), dRv (blockIndex dAv a))
      = ∑ x : (Σ i : Fin k, Fin (dAv i)), dRv x.1 from
    Fintype.sum_equiv finSigmaFinEquiv.symm _ _ (fun x => by simp [blockIndex]),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Finset.sum_const]

/-- **`σ`-fixed aligned-pair functions ≃ `σ`-fixed `Y`-valued functions**: the standard
"arrow of a subtype ≃ subtype of an arrow with the pointwise predicate" correspondence,
specialized to the aligned per-round space `Y = {p // IsAlignedPair dAv dRv p}` and further
restricted to the `σ`-fixed points on each side (needed to match the two Burnside sums). -/
private def alignedFixedEquiv {k : ℕ} (dAv dRv : Fin k → ℕ) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    {f : Fin n → {p : Fin (∑ i, dAv i) × Fin (∑ i, dRv i) // IsAlignedPair dAv dRv p} //
      f ∘ ⇑σ = f} ≃
    {q : (Fin n → Fin (∑ i, dAv i)) × (Fin n → Fin (∑ i, dRv i)) //
      (∀ t, IsAlignedPair dAv dRv (q.1 t, q.2 t)) ∧ q.1 ∘ ⇑σ = q.1 ∧ q.2 ∘ ⇑σ = q.2} where
  toFun f := ⟨(fun t => (f.1 t).1.1, fun t => (f.1 t).1.2), (fun t => (f.1 t).2),
      funext fun t => congrArg (fun y => y.1.1) (congr_fun f.2 t),
      funext fun t => congrArg (fun y => y.1.2) (congr_fun f.2 t)⟩
  invFun q := ⟨fun t => ⟨(q.1.1 t, q.1.2 t), q.2.1 t⟩, by
    funext t
    apply Subtype.ext
    exact Prod.ext (congr_fun q.2.2.1 t) (congr_fun q.2.2.2 t)⟩
  left_inv f := by
    apply Subtype.ext
    funext t
    rfl
  right_inv q := by
    apply Subtype.ext
    rfl

/-- The aligned per-round dimension `x = Σᵢ dAv i · dRv i` is nonzero (some block `i` exists,
since `Σᵢ dAv i ≠ 0`, and both `dAv i, dRv i ≠ 0` there). -/
private lemma aligned_dim_ne_zero {k : ℕ} (dAv dRv : Fin k → ℕ)
    [∀ i, NeZero (dAv i)] [∀ i, NeZero (dRv i)] [NeZero (∑ i, dAv i)] :
    (∑ i, dAv i * dRv i) ≠ 0 := by
  have hk : Nonempty (Fin k) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact (NeZero.ne (∑ i, dAv i)) (by simp [Finset.univ_eq_empty])
  obtain ⟨i0⟩ := hk
  have hterm : dAv i0 * dRv i0 ≠ 0 :=
    Nat.mul_ne_zero (NeZero.ne (dAv i0)) (NeZero.ne (dRv i0))
  intro hzero
  exact hterm (Nat.eq_zero_of_le_zero (hzero ▸ Finset.single_le_sum
    (fun i _ => Nat.zero_le (dAv i * dRv i)) (Finset.mem_univ i0)))

/-- **Burnside sum, aligned per-round pairs**: summed over `σ ∈ Sₙ`, the number of `σ`-fixed
aligned function pairs `(a,r) : (Fin n → Aᵗᵒᵗ) × (Fin n → Rᵗᵒᵗ)` is
`n! * Nat.choose (n + x - 1) (x - 1)`,
`x = Σᵢ dAv i · dRv i` (the same combinatorics as `symmetricProjectorRep_trace`, restricted to
the aligned per-round space `Y`, `Math.RepresentationTheory.sum_card_fixedBy_perm_fun_eq_of_fintype`
transported by `alignedFixedEquiv`). -/
private lemma sum_card_alignedPair_fixed_eq {k : ℕ} (dAv dRv : Fin k → ℕ) (n : ℕ)
    [∀ i, NeZero (dAv i)] [∀ i, NeZero (dRv i)]
    [NeZero (∑ i, dAv i)] [NeZero (∑ i, dRv i)] [NeZero n] :
    ∑ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun q : (Fin n → Fin (∑ i, dAv i)) × (Fin n → Fin (∑ i, dRv i)) =>
        (∀ t, IsAlignedPair dAv dRv (q.1 t, q.2 t)) ∧ q.1 ∘ ⇑σ = q.1 ∧ q.2 ∘ ⇑σ = q.2)).card
      = n.factorial * (Nat.choose (n + (∑ i, dAv i * dRv i) - 1) ((∑ i, dAv i * dRv i) - 1)) := by
  have hcardY : Fintype.card
      {p : Fin (∑ i, dAv i) × Fin (∑ i, dRv i) // IsAlignedPair dAv dRv p} =
        ∑ i, dAv i * dRv i := card_alignedPair_eq dAv dRv
  haveI : NeZero
      (Fintype.card {p : Fin (∑ i, dAv i) × Fin (∑ i, dRv i) // IsAlignedPair dAv dRv p}) :=
    ⟨hcardY ▸ aligned_dim_ne_zero dAv dRv⟩
  have key := Math.RepresentationTheory.sum_card_fixedBy_perm_fun_eq_of_fintype
    (β := {p : Fin (∑ i, dAv i) × Fin (∑ i, dRv i) // IsAlignedPair dAv dRv p}) n
  rw [hcardY] at key
  rw [← key]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Fintype.card_subtype, ← Fintype.card_subtype,
    ← Fintype.card_congr (alignedFixedEquiv dAv dRv n σ)]

/-! ## Entry and trace identities: trace against a diagonal, tensor entries, permutation diagonal -/

/-- `Tr(M · diag d) = Σᵢ Mᵢᵢ · dᵢ`. -/
private lemma trace_mul_diagonal_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (d : ι → ℂ) :
    (M * Matrix.diagonal d).trace = ∑ i, M i i * d i := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]

/-- The diagonal entry of `permutationRepresentation d n σ` at a `finFunctionFinEquiv`-encoded
tensor index `a` is the indicator of `a` being `σ`-fixed. -/
private lemma permutationRepresentation_diag_eq {d n : ℕ} [NeZero d] (σ : Equiv.Perm (Fin n))
    (a : Fin n → Fin d) :
    permutationRepresentation d n σ (@finFunctionFinEquiv d n a) (@finFunctionFinEquiv d n a)
      = if a ∘ ⇑σ = a then (1 : ℂ) else 0 := by
  unfold permutationRepresentation
  simp only [Matrix.of_apply, Equiv.symm_apply_apply]
  congr 1
  exact propext (eq_comp_perm_symm_iff_comp_perm_eq a a σ)

/-- The trace of the symmetric projector on the aligned direct sum is
`Nat.choose (n + x - 1) (x - 1)`, where `x = ∑ i, dAv i * dRv i`.
The proof counts permutation orbits of strings of aligned coordinate pairs. -/
theorem symmetricProjectorDirectSum_trace
    {k : ℕ} (dAv dRv : Fin k → ℕ) (n : ℕ)
    [∀ i, NeZero (dAv i)] [∀ i, NeZero (dRv i)]
    [NeZero (∑ i, dAv i)] [NeZero (∑ i, dRv i)] [NeZero n] :
    (symmetricProjectorDirectSum dAv dRv n).trace
      = ((Nat.choose (n + (∑ i, dAv i * dRv i) - 1) ((∑ i, dAv i * dRv i) - 1)) : ℂ) := by
  unfold symmetricProjectorDirectSum
  set A := alignedDirectSumProjector dAv dRv n with hAdef
  set P := symmetricProjectorPairedGen (∑ i, dAv i) (∑ i, dRv i) n with hPdef
  have hidem : A * A = A := alignedDirectSumProjector_idem dAv dRv n
  have hstep : (A * P * A).trace = (P * A).trace := by
    rw [Matrix.trace_mul_comm (A * P) A, ← mul_assoc, hidem, Matrix.trace_mul_comm A P]
  rw [hstep, hAdef]
  unfold alignedDirectSumProjector
  rw [trace_mul_diagonal_eq]
  set Ψ : (Fin n → Fin (∑ i, dAv i)) × (Fin n → Fin (∑ i, dRv i)) ≃
      Fin ((∑ i, dAv i) ^ n * (∑ i, dRv i) ^ n) :=
    (Equiv.prodCongr (@finFunctionFinEquiv (∑ i, dAv i) n)
        (@finFunctionFinEquiv (∑ i, dRv i) n)).trans
      finProdFinEquiv with hΨdef
  rw [← Equiv.sum_comp Ψ]
  have hg : ∀ q : (Fin n → Fin (∑ i, dAv i)) × (Fin n → Fin (∑ i, dRv i)),
      (have p := finProdFinEquiv.symm (Ψ q);
       have a := (@finFunctionFinEquiv (∑ i, dAv i) n).symm p.1;
       have r := (@finFunctionFinEquiv (∑ i, dRv i) n).symm p.2;
       if ∀ t : Fin n, (finSigmaFinEquiv.symm (a t)).1 = (finSigmaFinEquiv.symm (r t)).1
         then (1 : ℂ) else 0)
      = if (∀ t : Fin n, IsAlignedPair dAv dRv (q.1 t, q.2 t)) then (1 : ℂ) else 0 := by
    intro q
    simp only [hΨdef, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Equiv.symm_apply_apply, IsAlignedPair, blockIndex]
    rfl
  simp_rw [hg]
  have hPdiag : ∀ q : (Fin n → Fin (∑ i, dAv i)) × (Fin n → Fin (∑ i, dRv i)),
      P (Ψ q) (Ψ q) = (1 / (n.factorial : ℂ)) * ∑ σ : Equiv.Perm (Fin n),
        (if q.1 ∘ ⇑σ = q.1 then (1 : ℂ) else 0) * (if q.2 ∘ ⇑σ = q.2 then (1 : ℂ) else 0) := by
    intro q
    rw [hPdef]
    unfold symmetricProjectorPairedGen
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have hΨq : Ψ q = finProdFinEquiv
        (@finFunctionFinEquiv (∑ i, dAv i) n q.1, @finFunctionFinEquiv (∑ i, dRv i) n q.2) := by
      rw [hΨdef]; rfl
    rw [hΨq, Op_tensor_apply_finProd]
    simp only [Equiv.symm_apply_apply, permutationRepresentation_diag_eq]
  simp_rw [hPdiag]
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hcombine : ∀ (σ : Equiv.Perm (Fin n))
      (x : (Fin n → Fin (∑ i, dAv i)) × (Fin n → Fin (∑ i, dRv i))),
      ((if x.1 ∘ ⇑σ = x.1 then (1 : ℂ) else 0) * if x.2 ∘ ⇑σ = x.2 then (1 : ℂ) else 0) *
          (if (∀ t, IsAlignedPair dAv dRv (x.1 t, x.2 t)) then (1 : ℂ) else 0)
        = if (∀ t, IsAlignedPair dAv dRv (x.1 t, x.2 t)) ∧ x.1 ∘ ⇑σ = x.1 ∧ x.2 ∘ ⇑σ = x.2
            then (1 : ℂ) else 0 := by
    intro σ x
    by_cases h1 : x.1 ∘ ⇑σ = x.1 <;> by_cases h2 : x.2 ∘ ⇑σ = x.2 <;>
      by_cases h3 : (∀ t, IsAlignedPair dAv dRv (x.1 t, x.2 t)) <;> simp [h1, h2, h3]
  simp_rw [hcombine]
  simp_rw [Finset.sum_boole]
  rw [← Nat.cast_sum, sum_card_alignedPair_fixed_eq, Nat.cast_mul]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

end Quantum.Symmetry
