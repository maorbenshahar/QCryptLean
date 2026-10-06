import QCryptLean.QKD.BB84.Engine.EntropyFloor.EnVDecompositionReferee
import QCryptLean.Quantum.Channels.CPTP.CKRBound.Reference.Purification
import QCryptLean.QKD.BB84.Engine.PerRound.DevetakWinter
import QCryptLean.QKD.BB84.Engine.EntropyFloor.IsometricInvarianceReferee
import QCryptLean.QKD.BB84.Engine.EntropyFloor.AnnouncePEFloorChain

/-! The Nahar et al. B19 bridge infrastructure: `ckrTensorTraceNorm` purification-register
    invariance and the `bb84_ckrTensorTraceNorm_EnV_eq_canonical` factorization. -/

-- The paired-Haar per-σ family wiring (below) states Bochner integrability of `Op`-valued block
-- maps; as in `FinitePostFilterFloor.lean`/`Reference/Mixed.lean`, this uses the Frobenius norm on
-- matrices.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open InfoTheory.SmoothMinEntropy.SymmetricAEP
open InfoTheory.QuantumLHL
open InfoTheory.VonNeumannEntropy
open Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker

noncomputable section

namespace QKD.BB84.Engine

/-! ### B19 bridge infrastructure — `ckrTensorTraceNorm` purification-register invariance

The CKR tensor trace norm `‖(Δ ⊗ id_R)(τ)‖₁` of a CKR de Finetti purification `τ` does not
depend on the purifying register `R`: any two CKR purifications share the canonical `Aⁿ`-marginal
and are related by a reference-side left-isometry `W`, which commutes with `Δ ⊗ id` (acting on the
signal register) and leaves the trace norm invariant. -/

/-- Entry form of the rectangular tensor isometry `1_c ⊗ W`. -/
private lemma idTensorRectMatrix_apply {c m k : ℕ}
    (W : Matrix (Fin m) (Fin k) ℂ) (p : Fin (c * m)) (q : Fin (c * k)) :
    idTensorRectMatrix c m k W p q =
      if (finProdFinEquiv.symm p).1 = (finProdFinEquiv.symm q).1
        then W (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2 else 0 := by
  rw [idTensorRectMatrix, ← idTensorRect_eq_of, Matrix.of_apply]

/-- Entry of the reference-side conjugation `(1 ⊗ W)·A·(1 ⊗ W)ᴴ` of an operator `A` on
`a ⊗ R`, with both indices given as explicit `(signal, reference)` pairs: the `W`-isometry
mixes only the reference block, so the entry is the `W`-weighted sum over reference indices of
`A`-entries with the same signal components. -/
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
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, idTensorRectMatrix_apply,
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

/-- **Purification-register invariance of `ckrTensorTraceNorm`.**

Any CKR de Finetti purification `τ` (reference dimension `dimR ≥ d^n`) has the same CKR tensor trace
norm as the canonical square purification: writing `τ.toOp = (1 ⊗ W)·τ_canon·(1 ⊗ W)ᴴ` for the
reference-side left-isometry `W` from
`ckrDeFinettiPurification_relate_canonical_via_partial_isometry`, the signal-side map `Δ ⊗ id`
commutes with the reference conjugation (`mapTensorId_idTensorRect_conj`) and the trace norm is
invariant under the reference isometry
(`Quantum.Channels.traceNorm_idTensorRect_isometry_mul_left`). -/
private lemma ckrTensorTraceNorm_eq_canonical
    {d n dimOut dimR : ℕ} [NeZero d] [NeZero n] [NeZero (d ^ n)] [NeZero (d ^ n * d ^ n)]
    [NeZero dimOut] [NeZero dimR]
    (Δ : Op (d ^ n) →ₗ[ℂ] Op dimOut)
    (τ : DensityOp ((d ^ n) * dimR))
    (hτ : Quantum.Channels.IsCKRDeFinettiPurification τ) (hdim : d ^ n ≤ dimR) :
    ckrTensorTraceNorm Δ τ =
      ckrTensorTraceNorm Δ (Quantum.Channels.ckrDeFinettiCanonicalPurification d n) := by
  obtain ⟨W, hW, hvec⟩ :=
    Quantum.Channels.ckrDeFinettiPurification_relate_canonical_via_partial_isometry d n τ hτ hdim
  set Min := idTensorRectMatrix (d ^ n) dimR (d ^ n) W with hMindef
  -- `τ.toOp = Min · τ_canon · Minᴴ`
  have hψeq : (τ.pureKetOf hτ.isPure).vec =
      Min.mulVec (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet
        (Quantum.Channels.ckrDeFinettiState d n)).vec := by
    rw [hvec]
    funext k
    have hr : Min.mulVec
          (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet
            (Quantum.Channels.ckrDeFinettiState d n)).vec k =
        ∑ pair : Fin (d ^ n) × Fin (d ^ n), Min k (finProdFinEquiv pair) *
          (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet
            (Quantum.Channels.ckrDeFinettiState d n)).vec (finProdFinEquiv pair) := by
      rw [show Min.mulVec _ k = ∑ j, Min k j *
            (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet
              (Quantum.Channels.ckrDeFinettiState d n)).vec j from rfl,
        ← Equiv.sum_comp finProdFinEquiv (fun j => Min k j *
            (Quantum.Metrics.KitaevWatrousPurification.sameAncillaPurificationKet
              (Quantum.Channels.ckrDeFinettiState d n)).vec j)]
    rw [hr]
    refine Finset.sum_congr rfl fun pair _ => ?_
    rw [hMindef, idTensorRectMatrix_apply, Matrix.one_apply, Equiv.symm_apply_apply]
    by_cases hc : (finProdFinEquiv.symm k).1 = pair.1
    · rw [if_pos hc, if_pos hc.symm]; ring
    · rw [if_neg hc, if_neg (fun h => hc h.symm), zero_mul, zero_mul]
  have hop : τ.toOp =
      Min * (Quantum.Channels.ckrDeFinettiCanonicalPurification d n).toOp * Minᴴ := by
    rw [DensityOp.pureKetOf_spec τ hτ.isPure,
      Quantum.Channels.ckrDeFinettiCanonicalPurification_toOp_eq_ketbra,
      ket_mul_dag_eq_vecMulVec, ket_mul_dag_eq_vecMulVec, vecMulVec_conjugate, hψeq]
  unfold ckrTensorTraceNorm
  rw [hop, mapTensorId_idTensorRect_conj]
  exact Quantum.Channels.traceNorm_idTensorRect_isometry_mul_left W
    (mapTensorId Δ (Quantum.Channels.ckrDeFinettiCanonicalPurification d n).toOp) hW

/-- **Nahar et al. B19 — `ckrTensorTraceNorm` is invariant under the choice of CKR de Finetti
    purification
register (canonical `R = 4ⁿ` vs the `Eⁿ⊗V` split register, of dimension `4ⁿ` times the purifier's
own dimension).**

`ckrTensorTraceNorm Δ τ = ‖(Δ ⊗ id_R)(τ)‖₁` (`CKRBound/Reference/Basic.lean`) depends on `τ` only
through its action transported by the reference register `R`.  Any two CKR de Finetti purifications
share the canonical `Aⁿ`-marginal `ckrDeFinettiState signalDim n`, so they are related by a
reference-side left-isometry `W` (`Wᴴ W = 1`,
`ckrDeFinettiPurification_relate_canonical_via_partial_isometry`, via
`isCKRDeFinettiPurification_dimR_ge`); concretely `τ_EnV = (1_{4ⁿ} ⊗ W)·τ_canon·(1 ⊗ W)ᴴ`.  Since `Δ
⊗ id` acts on the signal register and `W` on the reference register, they commute, so `(Δ ⊗
id)(τ_EnV) = (1_{dimOut} ⊗ W)·(Δ ⊗ id)(τ_canon)·(1 ⊗ W)ᴴ`, and trace-norm invariance under the
rectangular tensor isometry `1 ⊗ W` (`Quantum.Channels.traceNorm_idTensorRect_isometry_mul_left`)
gives the equality.

This is the B19 bridge that moves the privacy-amplification bound from the `Eⁿ⊗V` register — where
the affordable `2 log g` smooth-min-entropy floor lives — back to the canonical `R = 4ⁿ` register
the endpoint consumer fixes.  Proved by applying `ckrTensorTraceNorm_eq_canonical` to both
purifications with their respective purification witnesses, reducing both sides to the same
canonical purification form.  References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(arXiv:2403.11851) App. B, the final security bound of the Postselection Theorem's proof
(main.tex:1420–1422, B19 in this codebase's convention); Watrous, *Theory of Quantum Information*,
§2.2. -/
theorem bb84_ckrTensorTraceNorm_EnV_eq_canonical
    {n dimOut : ℕ} [NeZero n] [NeZero (4 ^ n)] [NeZero dimOut]
    (V : BB84SymmetricPurifier n)
    (Δ : Op (signalDim ^ n) →ₗ[ℂ] Op dimOut) :
    haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
    haveI : NeZero ((signalDim ^ n) * V.dV) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    ckrTensorTraceNorm Δ (bb84SymCKRDeFinettiPurification n) =
      ckrTensorTraceNorm Δ (bb84EnVCKRPurification V) := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI : NeZero ((signalDim ^ n) * V.dV) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  haveI : NeZero ((signalDim ^ n) * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  rw [ckrTensorTraceNorm_eq_canonical Δ (bb84SymCKRDeFinettiPurification n)
        (bb84SymCKRDeFinettiPurification_isPurification n) (le_refl _),
    ckrTensorTraceNorm_eq_canonical Δ (bb84EnVCKRPurification V)
        (bb84EnVCKRPurification_isPurification V)
        (Quantum.Channels.isCKRDeFinettiPurification_dimR_ge _
          (bb84EnVCKRPurification_isPurification V))]

end QKD.BB84.Engine

end -- noncomputable section
