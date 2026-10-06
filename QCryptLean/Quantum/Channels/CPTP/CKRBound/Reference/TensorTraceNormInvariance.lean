import QCryptLean.Quantum.Channels.CPTP.IdTensorRect
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Basic
import QCryptLean.Quantum.Metrics.PurificationUhlmannUniqueness
import QCryptLean.Quantum.Operators.BraKet.Projector

/-!
# Purification-register invariance of the CKR tensor trace norm

The generic CKR tensor trace norm `ckrTensorTraceNorm Δ τ = ‖(Δ ⊗ id_R)(τ)‖₁`
(`CKRBound/Reference/Basic.lean`) depends on a purification `τ` of a marginal `σ` only through
`σ` itself, not through the purifying register `R`.  Any two purifications of the same marginal are
related by a reference-side left-isometry `W` (Uhlmann,
`purification_unique_up_to_partial_isometry_on_reference`).  Since the channel map `Δ ⊗ id` acts on
the signal register and `W` on the reference register they commute, and the trace norm is invariant
under the rectangular tensor isometry `1 ⊗ W`; hence the two trace norms agree.

This is the purpose-built, *reference-agnostic* core of the App. B (B19) purification-register
change of the Christandl-Konig-Renner / Renner postselection chain.  It applies to any two
purifications of a shared marginal — in particular to the
Bell de Finetti reference (Nahar et al. Lemma 2, `x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry) and the full
CKR reference (`x = 15`).

## Main statements

- `ckrTensorTraceNorm_eq_of_shared_marginal_of_le` — one-directional form (with the reference
  dimensions ordered `dimR₁ ≤ dimR₂`).
- `tensorTraceNorm_eq_of_shared_marginal` — symmetric form: any two purifications of the same
  marginal have equal `ckrTensorTraceNorm`.

## References

- Christandl, König, Renner (2009), `arXiv:0809.3019`, main.tex:268–:401 (\emph{Main Result}:
Theorem `\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}` :319–:328).
- Renner, *Security of QKD* (2005), §4.2.2 / §6.5.
- Watrous, *The Theory of Quantum Information* (2018), §2.2 (Uhlmann / purification freedom).
- Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, Thm 3, main.tex:1411–:1413
(unlabeled; the closing bound of Theorem 3's proof), Lemma 2 (`x = 4`, joint Bell `ℤ₂×ℤ₂` symmetry).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker

noncomputable section

namespace Quantum.Channels

/-! ## Index-conjugation algebra for the rectangular tensor isometry `1 ⊗ W`

These are branch-agnostic block-index identities for the rectangular tensor `idTensorRectMatrix`
and the identity-tensored map `mapTensorId`. -/

/-- Entry form of the rectangular tensor isometry `1_c ⊗ W`. -/
private lemma idTensorRectMatrix_apply' {c m k : ℕ}
    (W : Matrix (Fin m) (Fin k) ℂ) (p : Fin (c * m)) (q : Fin (c * k)) :
    idTensorRectMatrix c m k W p q =
      if (finProdFinEquiv.symm p).1 = (finProdFinEquiv.symm q).1
        then W (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2 else 0 := by
  rw [idTensorRectMatrix, ← idTensorRect_eq_of, Matrix.of_apply]

/-- Entry of the reference-side conjugation `(1 ⊗ W)·A·(1 ⊗ W)ᴴ` of an operator `A` on
`a ⊗ R`, with both indices given as explicit `(signal, reference)` pairs. -/
private lemma idTensorRect_conj_entry'
    {a drin drout : ℕ} [NeZero a] [NeZero drin] [NeZero drout]
    (W : Matrix (Fin drout) (Fin drin) ℂ) (A : Op (a * drin))
    (cp dq : Fin a) (sp tq : Fin drout) :
    (idTensorRectMatrix a drout drin W * A *
        (idTensorRectMatrix a drout drin W)ᴴ)
        (finProdFinEquiv (cp, sp)) (finProdFinEquiv (dq, tq)) =
      ∑ s' : Fin drin, ∑ t' : Fin drin,
        W sp s' * star (W tq t') *
          A (finProdFinEquiv (cp, s')) (finProdFinEquiv (dq, t')) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, idTensorRectMatrix_apply',
    Equiv.symm_apply_apply]
  -- reindex+collapse the inner `signal` summation against the `cp`-delta of `W`
  have hinner : ∀ (d' : Fin a) (t' : Fin drin),
      (∑ x_1 : Fin (a * drin), (if cp = (finProdFinEquiv.symm x_1).1
          then W sp (finProdFinEquiv.symm x_1).2 else 0) *
          A x_1 (finProdFinEquiv (d', t')))
        = ∑ s' : Fin drin, W sp s' * A (finProdFinEquiv (cp, s')) (finProdFinEquiv (d', t')) := by
    intro d' t'
    rw [← Equiv.sum_comp finProdFinEquiv
          (fun x_1 => (if cp = (finProdFinEquiv.symm x_1).1
              then W sp (finProdFinEquiv.symm x_1).2 else 0) *
            A x_1 (finProdFinEquiv (d', t'))), Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  -- reindex the outer `reference` summation, substitute the inner collapse, then collapse `dq`
  rw [← Equiv.sum_comp finProdFinEquiv
        (fun x => (∑ x_1 : Fin (a * drin), (if cp = (finProdFinEquiv.symm x_1).1
            then W sp (finProdFinEquiv.symm x_1).2 else 0) * A x_1 x) *
          star (if dq = (finProdFinEquiv.symm x).1
            then W tq (finProdFinEquiv.symm x).2 else 0)), Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, hinner]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t' _ => ?_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  simp only [apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  ring

/-- The signal-side map `Δ ⊗ id` commutes with reference-side conjugation by the rectangular
tensor isometry `1 ⊗ W`: `(Δ ⊗ id)((1 ⊗ W)·X·(1 ⊗ W)ᴴ) = (1 ⊗ W)·(Δ ⊗ id)(X)·(1 ⊗ W)ᴴ`. -/
private lemma mapTensorId_idTensorRect_conj
    {ds dout drin drout : ℕ}
    [NeZero ds] [NeZero dout] [NeZero drin] [NeZero drout]
    (Δ : Op ds →ₗ[ℂ] Op dout)
    (W : Matrix (Fin drout) (Fin drin) ℂ)
    (A : Op (ds * drin)) :
    mapTensorId Δ (idTensorRectMatrix ds drout drin W * A *
        (idTensorRectMatrix ds drout drin W)ᴴ) =
      idTensorRectMatrix dout drout drin W * mapTensorId Δ A *
        (idTensorRectMatrix dout drout drin W)ᴴ := by
  ext p q
  rw [show p = finProdFinEquiv (finProdFinEquiv.symm p) from
        (finProdFinEquiv.apply_symm_apply p).symm,
      show q = finProdFinEquiv (finProdFinEquiv.symm q) from
        (finProdFinEquiv.apply_symm_apply q).symm]
  rcases finProdFinEquiv.symm p with ⟨cp, sp⟩
  rcases finProdFinEquiv.symm q with ⟨dq, tq⟩
  rw [idTensorRect_conj_entry' W (mapTensorId Δ A) cp dq sp tq,
    mapTensorId_apply_eq_apply_block Δ
      (idTensorRectMatrix ds drout drin W * A * (idTensorRectMatrix ds drout drin W)ᴴ)]
  simp only [Equiv.symm_apply_apply]
  -- the block of `(1⊗W) A (1⊗W)ᴴ` is the `W`-weighted sum of `A`-blocks
  have hblk :
      (Matrix.of fun i j =>
          (idTensorRectMatrix ds drout drin W * A *
              (idTensorRectMatrix ds drout drin W)ᴴ)
            (finProdFinEquiv (i, sp)) (finProdFinEquiv (j, tq)) : Op ds) =
        ∑ s' : Fin drin, ∑ t' : Fin drin,
          (W sp s' * star (W tq t')) •
            (Matrix.of fun i j =>
              A (finProdFinEquiv (i, s')) (finProdFinEquiv (j, t')) : Op ds) := by
    ext i j
    rw [Matrix.of_apply, idTensorRect_conj_entry']
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [hblk]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t' _ => ?_
  congr 1
  rw [mapTensorId_apply_eq_apply_block]
  simp only [Equiv.symm_apply_apply]

/-- Conjugation of a rank-one ketbra `vecMulVec u (star u)` by a rectangular matrix `M` transforms
the underlying vector: `M·(u uᴴ)·Mᴴ = (Mu)(Mu)ᴴ`. -/
private lemma vecMulVec_conjugate {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ) (u : Fin q → ℂ) :
    M * Matrix.vecMulVec u (star u) * Mᴴ =
      Matrix.vecMulVec (M.mulVec u) (star (M.mulVec u)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Pi.star_apply]
  have hmul : ∀ c : Fin p, (M.mulVec u) c = ∑ j, M c j * u j := fun c => rfl
  rw [hmul a, hmul b, star_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [star_mul']
  ring

/-! ## The purification-register invariance lemmas -/

/-- **Purification-register invariance of `ckrTensorTraceNorm` (ordered form).**

If `τ₁` (reference dimension `dimR₁`) and `τ₂` (reference dimension `dimR₂ ≥ dimR₁`) are two pure
purifications of the *same* marginal `σ : DensityOp (d ^ n)` and `dimR₁ ≤ dimR₂`, then they have
equal CKR tensor trace norms.

By Uhlmann purification freedom (`purification_unique_up_to_partial_isometry_on_reference`) there is
a reference-side left-isometry `V : Matrix (Fin dimR₂) (Fin dimR₁) ℂ` (`Vᴴ V = 1`) with
`τ₂.toOp = (1 ⊗ V)·τ₁.toOp·(1 ⊗ V)ᴴ`.  The signal-side map `Δ ⊗ id` commutes with the
reference conjugation (`mapTensorId_idTensorRect_conj`) and the trace norm is invariant under the
rectangular tensor isometry `1 ⊗ V` (`Quantum.Channels.traceNorm_idTensorRect_isometry_mul_left`).

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) main.tex:1411–:1413
(unlabeled; the closing bound of Theorem 3's proof); Watrous §2.2. -/
lemma ckrTensorTraceNorm_eq_of_shared_marginal_of_le
    {d n dimOut dimR₁ dimR₂ : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    [NeZero dimOut] [NeZero dimR₁] [NeZero dimR₂]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (σ : DensityOp (d ^ n))
    (τ₁ : DensityOp ((d ^ n) * dimR₁)) (τ₂ : DensityOp ((d ^ n) * dimR₂))
    (h₁pure : τ₁.IsPure) (h₂pure : τ₂.IsPure)
    (h₁ : τ₁.partialTraceB = σ) (h₂ : τ₂.partialTraceB = σ)
    (hle : dimR₁ ≤ dimR₂) :
    ckrTensorTraceNorm Δ τ₂ = ckrTensorTraceNorm Δ τ₁ := by
  obtain ⟨V, hV, hop⟩ :=
    Quantum.Metrics.exists_isometry_eq_idTensorRect_conj_of_partialTraceB_eq
      τ₁ τ₂ h₁pure h₂pure (h₂.trans h₁.symm) hle
  unfold ckrTensorTraceNorm
  rw [hop, mapTensorId_idTensorRect_conj]
  exact Quantum.Channels.traceNorm_idTensorRect_isometry_mul_left V (mapTensorId Δ τ₁.toOp) hV

/-- **Purification-register invariance of `ckrTensorTraceNorm`.**

Any two pure purifications `τ₁, τ₂` of the *same* marginal `σ : DensityOp (d ^ n)` have equal CKR
tensor trace norms `ckrTensorTraceNorm Δ τ₁ = ckrTensorTraceNorm Δ τ₂`, regardless of their
purifying-register dimensions.  This is the reference-agnostic App. B (B19) purification-change
identity of the postselection chain.

References: Nahar et al. 2024 (`arXiv:2403.11851`) main.tex:1411–:1413 (unlabeled; the closing bound
of Theorem 3's proof); Christandl-König-Renner (2009) main.tex:268–:401 (\emph{Main Result}: Theorem
`\label{thm:main}` :291–:301, Lemma `\label{lem:extractpart}` :319–:328);
Watrous §2.2. -/
theorem tensorTraceNorm_eq_of_shared_marginal
    {d n dimOut dimR₁ dimR₂ : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)]
    [NeZero dimOut] [NeZero dimR₁] [NeZero dimR₂]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (σ : DensityOp (d ^ n))
    (τ₁ : DensityOp ((d ^ n) * dimR₁)) (τ₂ : DensityOp ((d ^ n) * dimR₂))
    (h₁pure : τ₁.IsPure) (h₂pure : τ₂.IsPure)
    (h₁ : τ₁.partialTraceB = σ) (h₂ : τ₂.partialTraceB = σ) :
    ckrTensorTraceNorm Δ τ₁ = ckrTensorTraceNorm Δ τ₂ := by
  rcases le_total dimR₁ dimR₂ with hle | hle
  · exact (ckrTensorTraceNorm_eq_of_shared_marginal_of_le Δ σ τ₁ τ₂
      h₁pure h₂pure h₁ h₂ hle).symm
  · exact ckrTensorTraceNorm_eq_of_shared_marginal_of_le Δ σ τ₂ τ₁
      h₂pure h₁pure h₂ h₁ hle

end Quantum.Channels

end -- noncomputable section
