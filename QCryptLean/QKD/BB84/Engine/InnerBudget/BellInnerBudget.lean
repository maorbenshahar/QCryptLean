import QCryptLean.QKD.BB84.Engine.InnerBudget.InnerBudgetPinned
import QCryptLean.QKD.BB84.Engine.EntropyFloor.BellFloorChain
import QCryptLean.QKD.BB84.Engine.EntropyFloor.BellPurifier
import QCryptLean.Quantum.Symmetry.BellTwirlIdempotent
import QCryptLean.Quantum.Channels.CPTP.CKRBound.PermutationReduction
import QCryptLean.QKD.BB84.Engine.Postselection.BellReference
import QCryptLean.QKD.BB84.Engine.InnerBudget.BaseScheme
import QCryptLean.Quantum.Symmetry.Covariance
import QCryptLean.QKD.BB84.Engine.EntropyFloor.BellPELabelledMixture
import QCryptLean.InfoTheory.DistanceBounds.AcceptSplit
import QCryptLean.InfoTheory.QuantumLHL.SeedKeyAcceptSplit
import QCryptLean.InfoTheory.SmoothMinEntropy.Announcement.BlockRefRegularization

-- The de Finetti coarsening assembler states Bochner integrability of `Op`-valued block maps; as in
-- `PerSigmaFamily.lean` / `AcceptSplit.lean`, this uses the Frobenius norm on matrices.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/-!
# The Bell de Finetti reference inner budget

Re-keys the postselection inner-budget endpoint from the full CKR de Finetti reference
`τ = bb84SymCKRDeFinettiPurification n` (postselection dimension `bb84PolyDim n = C(n+15,15)`) to
the **Bell** de Finetti reference `τ_Bell = bb84BellCKRDeFinettiPurification n` (postselection
dimension `bb84PolyDimTight n = C(n+3,3)`), the register at which the outer CKR postselection
prefactor drops from `(n+1)^15` to `(n+1)^3`. For the joint Bell `ℤ₂ × ℤ₂` action, Nahar et al.’s
compact-group purification lemma (arXiv:2403.11851, `main.tex:354–355`,
`\label{lem:groupPurification}`) gives effective dimension `x = ∑ᵢ mᵢ² = 4`, hence
`g_{n,4} = C(n+3,3)`. The product-group corollaries at `main.tex:362` and `main.tex:521` do not
directly apply to this diagonal bilateral action.

The inner budget `bb84CKRPostselectionInnerBudgetOfTail` is reference-independent: none of its
scalar terms takes the reference dimension as an argument. The reference dimension enters only
through the `−2·log₂ g` register-extension penalty of `\label{eq:splittingoffV}`
(arXiv:2403.11851, `main.tex:1393`). Each component uses its own marginal as reference, so the
carried floor has no reference-dimension cost. The register-extension penalty shrinks under
`τ → τ_Bell`, and a key-rate condition that funds the CKR floor also funds the Bell floor.

## Main definitions and results

* `bb84BellDeFinettiDensity_isPermutationInvariant`,
  `bb84BellCKRDeFinettiPurification_isPairedPermInvariant` — the Bell de Finetti `A`-marginal and
  its square-root purification `τ_Bell` are permutation- resp. paired-permutation-invariant, the
  structural hypothesis the symmetrization-to-base lift requires.
* `bb84BellEnVRhoEtilde` — the fail-closed local-PE-pass-filtered post-measurement state run on the
  Bell joint de Finetti mixture, the Bell analogue of the CKR `Eⁿ`-marginal reference.
* `bb84_EnV_bellRhoEV_partialTraceB_eq_forCoarsen` — Nahar et al. Appendix B step B13: tracing the
  purifier register `V` out of the Bell `Eⁿ⊗V` reference recovers `bb84BellEnVRhoEtilde` blockwise.
* `bb84BellEnVRhoEtilde_acceptWeight_eq` — the Bell mixture's accept weight equals the
  `τ_Bell`-side accepted weight.
* `bb84BellEnVRhoEtilde_eq_haar_integral_blocks` — the Bell mixture as a Bochner integral over
  Haar-random single-pair states (Appendix B step B13, the block-integral form).

## The Appendix-B step names used below

Nahar et al.'s appendix equations are numbered by LaTeX at build time; those numbers do not occur in
arXiv:2403.11851, `main.tex`.  Where this file writes `B13`, `B16`, `B17` it means the
following source locations, inside the appendix proof of `\label{thm:maintheorem}`
(`main.tex:1331`–`:1421`):

* `B13` — the accept-block mixture split `\label{eq:tausplit}`, `main.tex:1356`–`:1361`;
* `B16` — the smoothed min-entropy bound `\label{eq:boundingsmoothedmin}`, `main.tex:1380`–`:1387`;
* `B17` — the purifying-register split `\label{eq:splittingoffV}`, `main.tex:1392`–`:1395`.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`),
`main.tex:362` `\label{cor:symmetryDeFinetti}`, `main.tex:481`
`\label{thm:maintheorem}`, `main.tex:521` `\label{cor:liftToCoherentSymmetries}`, `main.tex:1380`
`\label{eq:boundingsmoothedmin}`, `main.tex:1393` `\label{eq:splittingoffV}`; Renner 2005
(`arXiv:quant-ph/0512258v2`) §6.5; Christandl-König-Renner 2009 (`arXiv:0809.3019`)
`main.tex:268`–`:401` (Main Result: the Post-Selection Theorem `\label{thm:main}` :291–:301, the
substate-extraction Lemma `\label{lem:extractpart}` :319–:328).
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry InfoTheory.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.Engine

/-!
## The Bell de Finetti reference is paired-permutation invariant
-/

/-- **The Bell de Finetti A-marginal is permutation invariant.**

`bb84BellDeFinettiDensity n = bb84BellTwirl n (C(n+3,3)⁻¹ • symmetricProjector 4 n)`.  The
symmetric projector is fixed by permutation conjugation (`permRep_conj_symmetricProjector`)
and the IID Bell twirl commutes with round-permutation conjugation (`bellTwirl_perm_conj`),
so the twirl of the permutation-invariant normalized symmetric projector stays permutation
invariant. -/
theorem bb84BellDeFinettiDensity_isPermutationInvariant (n : ℕ) [NeZero n] :
    IsPermutationInvariant (bb84BellDeFinettiDensity n) := by
  intro σ
  -- The underlying operator: the Bell twirl of the normalized symmetric projector.
  change permutationRepresentation 4 n σ *
        bb84BellTwirl n ((Nat.choose (n + 3) 3 : ℂ)⁻¹ • symmetricProjector 4 n) *
        (permutationRepresentation 4 n σ)ᴴ =
      bb84BellTwirl n ((Nat.choose (n + 3) 3 : ℂ)⁻¹ • symmetricProjector 4 n)
  -- Slide the conjugation through the twirl, then through the scalar and the projector.
  rw [← bellTwirl_perm_conj n σ ((Nat.choose (n + 3) 3 : ℂ)⁻¹ • symmetricProjector 4 n)]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul, permRep_conj_symmetricProjector n σ]

/-- **The Bell de Finetti purification reference `τ_Bell` is paired-permutation invariant.**

`bb84BellCKRDeFinettiPurification n = purificationDensityOp (bb84BellDeFinettiDensity n)`, the
square-root/vectorization purification of the permutation-invariant Bell de Finetti A-marginal
(`bb84BellDeFinettiDensity_isPermutationInvariant`).  The square-root purification of a
permutation-invariant state is paired-permutation invariant
(`purificationDensityOp_isPairedPermInvariant`), the structural hypothesis the
symmetrization-to-base lift requires.

References: Renner (2005) §6.5; CKR (2009) §III. -/
theorem bb84BellCKRDeFinettiPurification_isPairedPermInvariant (n : ℕ) [NeZero n] [NeZero (4 ^ n)] :
    IsPairedPermInvariant (bb84BellCKRDeFinettiPurification n) := by
  haveI : NeZero ((4 : ℕ) ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  exact purificationDensityOp_isPairedPermInvariant (bb84BellDeFinettiDensity n)
    (bb84BellDeFinettiDensity_isPermutationInvariant n)

/-!
## The Bell `Eⁿ`-marginal de Finetti mixture and the Nahar et al. B13 trace-out-`V` identity
-/

/-- **The Bell `Eⁿ`-marginal de Finetti reference.**

The fail-closed local-PE-pass-filtered τ-side post-measurement CQ state run on the Bell joint
de Finetti mixture `bb84BellPairedDeFinettiState n` (register `Aⁿ ⊗ Eⁿ`, `dimR = 4ⁿ`), the Bell
analogue of the CKR `Eⁿ`-marginal reference.

It is the trace-out-`V` marginal of the Bell `Eⁿ⊗V` reference, blockwise
(`bb84_EnV_bellRhoEV_partialTraceB_eq_forCoarsen`), because
`partialTraceB V.purifier = bb84BellPairedDeFinettiState n`
(`BB84BellPurifierOfMarginal.purifier_partialTraceB`, Nahar et al. B13).

The retained-Eve slot is the bare triple `(eveDim, pre, hpre)`: an arbitrary CPTP map
`Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)`, with no adversary object in the statement.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`),
`main.tex:1380` `\label{eq:boundingsmoothedmin}`, `main.tex:1393`
`\label{eq:splittingoffV}`. -/
noncomputable def bb84BellEnVRhoEtilde {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    CQState (Fin n → Fin signalDim) (eveDim * (signalDim ^ n)) :=
  haveI : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI : NeZero (eveDim * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
    (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
      (bb84BellPairedDeFinettiState n)).toCQState

/-- A CQ register-dimension cast transports each block's operator along the matrix cast.  Local
re-derivation of the private `bb84CastCQState_stateMap_toOpEnV` of `AnnouncePEFloorChainEnV.lean`.
-/
private lemma bellCastCQState_stateMap_toOp {Xc : Type*} [Fintype Xc] {a b : ℕ} (h : a = b)
    (ρ : CQState Xc a) (x : Xc) :
    ((bb84CastCQState h ρ).stateMap x).toOp = h ▸ ((ρ.stateMap x).toOp) := by
  subst h; rfl

/-- The fail-closed local-PE pass filter reads only the classical outcome, so it commutes with a
register-dimension cast.  Local re-derivation of the private
`bb84CastCQState_SiftedLocalPEPassFilter` of `AnnouncePEFloorChainEnV.lean`. -/
private lemma bellCastCQState_siftedLocalPEPassFilter {n a b : ℕ} [NeZero a] [NeZero b]
    (h : a = b) (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (ρ : CQState (Fin n → Fin signalDim) a) :
    bb84CastCQState h (bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ ρ) =
      bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ (bb84CastCQState h ρ) := by
  subst h; rfl

/-- **Nahar et al. B13 (spectator-`V` τ-conditioning commutation), at an arbitrary joint marginal
`ρ₀`.**

The Bell re-key of `bb84_EnV_siftedTauEveRefConditioned_partialTraceB_eq`
(`AnnouncePEFloorChainEnV.lean`): tracing out only the trailing purifier register `V` from the
reassociated sifted τ-conditioned `Eⁿ ⊗ V` block of the Bell EnV purification recovers the
sifted τ-conditioned `Eⁿ` block of `ρ₀`.

The σ-independent pre-channel and the sifted rotation act as the identity on the reference
register, so tracing out the trailing `V` factor commutes with the conditioning, and the τ-side
fact is `partialTraceB V.purifier = ρ₀`
(`BB84BellPurifierOfMarginal.purifier_partialTraceB`).  Every step is one of the three
register-generic trailing bridges `partialTraceB_mapTensorId_trailing`,
`partialTraceB_sandwich_tensor_one_trailing`,
`bb84Sifted_partialTraceB_trailing_submatrix_tauEmbedding`, so nothing here is specific to the Bell
de Finetti mixture.

References: Nahar et al. 2024 (`arXiv:2403.11851`), `main.tex:1393`
`\label{eq:splittingoffV}`. -/
theorem bb84_EnV_bellSiftedTauEveRefConditionedLocalPE_partialTraceB_eq_ofMarginal {n : ℕ}
    [NeZero n] [NeZero (4 ^ n)] (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) {ρ₀ : DensityOp ((4 ^ n) * (4 ^ n))}
    (V : BB84BellPurifierOfMarginal n ρ₀)
    (ω : Fin n → Fin signalDim) :
    Quantum.TensorProducts.partialTraceB
        ((Nat.mul_assoc eveDim (signalDim ^ n) V.dV).symm ▸
          (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel (bb84EnVBellPurification V)
              ω).toOp) =
      (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel ρ₀ ω).toOp := by
  haveI hVdv : NeZero V.dV := V.dV_neZero
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hR : NeZero (signalDim ^ n * V.dV) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hcancel : ∀ {p q : ℕ} (h : p = q) (x : Op p),
      (h.symm ▸ (h ▸ x : Op q) : Op p) = x := by
    intro p q h x; subst h; rfl
  have hCastToOp : ∀ {a b : ℕ} (h : a = b) (ρ : DensityOp a),
      (DensityOp.castDim h ρ).toOp = h ▸ ρ.toOp := by
    intro a b h ρ; subst h; rfl
  -- The trailing-`V` marginal of the Bell EnV purification is the prescribed joint marginal `ρ₀`.
  have hbottom : Quantum.TensorProducts.partialTraceB
      ((Nat.mul_assoc (signalDim ^ n) (signalDim ^ n) V.dV).symm ▸
        (bb84EnVBellPurification V).toOp) =
      ρ₀.toOp := by
    have hcast : (Nat.mul_assoc (signalDim ^ n) (signalDim ^ n) V.dV).symm ▸
        (bb84EnVBellPurification V).toOp = V.purifier.toOp := by
      simp only [bb84EnVBellPurification, hCastToOp]
      exact hcancel _ _
    rw [hcast]
    exact congrArg (·.toOp) V.purifier_partialTraceB
  -- The σ-independent pre-channel acts as the identity on the reference.
  have hM : Quantum.TensorProducts.partialTraceB
      ((Nat.mul_assoc (4 ^ n * eveDim) (signalDim ^ n) V.dV).symm ▸
        (bb84TauOutputDensity eveDim pre hpre (bb84EnVBellPurification V)).toOp) =
      (bb84TauOutputDensity eveDim pre hpre ρ₀).toOp := by
    rw [show (bb84TauOutputDensity eveDim pre hpre (bb84EnVBellPurification V)).toOp =
          mapTensorId pre (bb84EnVBellPurification V).toOp from rfl,
      partialTraceB_mapTensorId_trailing, hbottom,
      show mapTensorId pre ρ₀.toOp =
          (bb84TauOutputDensity eveDim pre hpre ρ₀).toOp from rfl]
  -- The sift conjugation acts as the identity on the reference.
  have hcore : Quantum.TensorProducts.partialTraceB
      ((Nat.mul_assoc (4 ^ n * eveDim) (signalDim ^ n) V.dV).symm ▸
        (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel (bb84EnVBellPurification V)).toOp)
            =
      (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel ρ₀).toOp := by
    simp only [bb84SiftedTauPreOutputDensity, densityOpUnitaryConj_toOp,
      Op.tensor_conjTranspose, Matrix.conjTranspose_one]
    rw [partialTraceB_sandwich_tensor_one_trailing, hM]
  -- The conditioned block is a τ-embedding submatrix.
  rw [show
      (bb84SiftedTauEveRefConditioned eveDim pre hpre peSel xSel (bb84EnVBellPurification V) ω).toOp
      =
        (bb84SiftedTauPreOutputDensity eveDim pre hpre peSel xSel
            (bb84EnVBellPurification V)).toOp.submatrix
          (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
            (dimR := signalDim ^ n * V.dV) (bb84OutcomeIndex ω))
          (bb84TauOutcomeEveRefEmbedding (eveDim := eveDim)
            (dimR := signalDim ^ n * V.dV) (bb84OutcomeIndex ω)) from rfl,
    bb84Sifted_partialTraceB_trailing_submatrix_tauEmbedding, hcore]
  rfl

/-- **Nahar et al. B13 — tracing out `V` from the Bell `Eⁿ⊗V` reference recovers
`bb84BellEnVRhoEtilde`.**

Each local-PE-pass-filtered Bell `Eⁿ⊗V` block (register `(eveDim·4ⁿ)·V.dV` after reassociation),
partial-traced over the `dV`-dimensional purifier register, equals the corresponding block of
`bb84BellEnVRhoEtilde`. Bell re-key of `bb84_EnV_rhoEV_partialTraceB_eq_forCoarsen`
(`AnnouncePEFloorChainEnV.lean`).

References: Nahar et al. 2024 (`arXiv:2403.11851`), `main.tex:1393`
`\label{eq:splittingoffV}`. -/
theorem bb84_EnV_bellRhoEV_partialTraceB_eq_forCoarsen {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (eveDim : ℕ) [NeZero eveDim]
    (pre : Op (4 ^ n) →ₗ[ℂ] Op (4 ^ n * eveDim)) (hpre : IsCPTP ⇑pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (V : BB84BellSymmetricPurifier n) :
    ∀ x : Fin n → Fin signalDim,
      Quantum.TensorProducts.partialTraceB
          (((bb84CastCQState (Nat.mul_assoc eveDim (signalDim ^ n) V.dV).symm
            (bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
              (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
                (bb84EnVBellPurification V)).toCQState)).stateMap x).toOp) =
        ((bb84BellEnVRhoEtilde eveDim pre hpre peSel xSel Q δ).stateMap x).toOp := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  haveI hVdv : NeZero V.dV := V.dV_neZero
  haveI hEnDim : NeZero (eveDim * (signalDim ^ n)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  intro x
  rw [bellCastCQState_siftedLocalPEPassFilter
    (Nat.mul_assoc eveDim (signalDim ^ n) V.dV).symm peSel xSel Q δ
    (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
      (bb84EnVBellPurification V)).toCQState]
  refine (bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq
    (dE := eveDim * (signalDim ^ n)) (dR := V.dV) peSel xSel Q δ
    (bb84CastCQState (Nat.mul_assoc eveDim (signalDim ^ n) V.dV).symm
      (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
        (bb84EnVBellPurification V)).toCQState)
    (bb84SiftedTauPostMeasurementNormalizedCQState eveDim pre hpre peSel xSel
      (bb84BellPairedDeFinettiState n)).toCQState ?_ x).trans rfl
  intro ω
  rw [bellCastCQState_stateMap_toOp]
  exact bb84_EnV_bellSiftedTauEveRefConditionedLocalPE_partialTraceB_eq_ofMarginal
    eveDim pre hpre peSel xSel V ω

/-!
## The Bell mixture accept weight equals the `τ_Bell`-side accept weight
-/

/-- **The Bell mixture accept weight equals the `τ_Bell`-side local-PE accepted weight.**

`∑_ω tr (bb84BellEnVRhoEtilde)_ω = bb84SiftedEveVisible_tauLocalPEAcceptedWeight … τ_Bell`.

The τ-side local-PE accepted weight of a base `τ` reads only `τ.partialTraceB`:
each filtered block's trace is the
trace of its `partialTraceB`, which is the corresponding block of the post-measurement CQ
state at `τ.partialTraceB` (`bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq`
fed `bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned`).  Both
`bb84BellPairedDeFinettiState n` and `bb84BellCKRDeFinettiPurification n` have `Eⁿ`-marginal
`bb84BellDeFinettiDensity n` (`bb84BellPairedDeFinettiState_partialTraceB` and
`bb84BellCKRDeFinettiPurification_isPurification`), so the two weights coincide.  The CKR
identification `bb84SiftedEveVisible_tauLocalPEAcceptedWeight_eq_localPEAcceptedWeight` is an
`IsCKRDeFinettiPurification` statement and is unavailable here: `τ_Bell` is an
`IsBellCKRDeFinettiPurification`, whose marginal is `bb84BellDeFinettiDensity n`, not
`ckrDeFinettiState signalDim n`.

Reference: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) App. B, the accept-block
mixture split `\label{eq:tausplit}` (`main.tex:1356`–`:1361`) through the smoothed min-entropy bound
`\label{eq:boundingsmoothedmin}` (`main.tex:1380`–`:1387`). -/
theorem bb84BellEnVRhoEtilde_acceptWeight_eq {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    ∑ x : Fin n → Fin signalDim,
        ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel
            xSel Q δ).stateMap x).trace =
      bb84SiftedEveVisible_tauLocalPEAcceptedWeight 1 (bb84UnitRegisterEmbed n)
          (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
        (bb84BellCKRDeFinettiPurification n) := by
  haveI hSignal : NeZero (signalDim ^ n) := signalDim_pow_neZero n
  -- Each filtered τ-block's trace is the trace of its `Eⁿ`-marginal, hence a function of
  -- `τ.partialTraceB` alone.
  have hmarg : ∀ (τ : DensityOp ((signalDim ^ n) * (signalDim ^ n)))
      (ω : Fin n → Fin signalDim),
      ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
          (bb84SiftedTauPostMeasurementNormalizedCQState 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
            τ).toCQState).stateMap ω).trace =
        ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
          (bb84SiftedPostMeasurementCQState 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
            τ.partialTraceB)).stateMap ω).trace := by
    intro τ ω
    unfold SubDensityOp.trace
    congr 1
    rw [← trace_partialTraceB (((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
        (bb84SiftedTauPostMeasurementNormalizedCQState 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
          τ).toCQState).stateMap ω).toOp),
      bb84PostMeasurementCQSiftedLocalPEPassFilter_stateMap_partialTraceB_eq peSel xSel Q δ
        (bb84SiftedTauPostMeasurementNormalizedCQState 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
          τ).toCQState
        (bb84SiftedPostMeasurementCQState 1 (bb84UnitRegisterEmbed n)
            (bb84UnitRegisterEmbed_isCPTP n) peSel xSel τ.partialTraceB)
        (fun ω' => bb84SiftedTauEveRefConditioned_partialTraceB_eq_bb84SiftedEveConditioned
          1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel τ ω') ω]
  have hL : ∑ x : Fin n → Fin signalDim,
      ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
          Q δ).stateMap x).trace =
      ∑ x : Fin n → Fin signalDim,
        ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
          (bb84SiftedPostMeasurementCQState 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
            (bb84BellPairedDeFinettiState n).partialTraceB)).stateMap x).trace :=
    Finset.sum_congr rfl fun x _ => hmarg (bb84BellPairedDeFinettiState n) x
  have hR : bb84SiftedEveVisible_tauLocalPEAcceptedWeight 1 (bb84UnitRegisterEmbed n)
      (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
        (bb84BellCKRDeFinettiPurification n) =
      ∑ x : Fin n → Fin signalDim,
        ((bb84PostMeasurementCQSiftedLocalPEPassFilter peSel xSel Q δ
          (bb84SiftedPostMeasurementCQState 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
            (bb84BellCKRDeFinettiPurification n).partialTraceB)).stateMap x).trace :=
    Finset.sum_congr rfl fun x _ => hmarg (bb84BellCKRDeFinettiPurification n) x
  rw [hL, hR, bb84BellPairedDeFinettiState_partialTraceB,
    (bb84BellCKRDeFinettiPurification_isPurification n).marginal]

/-!
## The Bell mixture as a Haar block integral
-/

/-- **The Nahar et al. B13 integral split at the Bell de Finetti measure.**

Each register-block entry of the Bell `Eⁿ`-marginal mixture `bb84BellEnVRhoEtilde` is the
Bochner integral, over Haar-random single-pair states `φ : DensityOp 4`, of the corresponding entry
of the per-σ family at the Bell-doubled source `bellWembed φ`.

The source-generic block-integral lemma
`bb84_siftedLocalPE_blocks_eq_integral_of_toOp_eq_integral` fed the Bell joint Haar-integral
identity `bb84BellPairedDeFinettiState_eq_haar_integral` and the integrability of the interleaved
Bell-doubled power `bb84_bellWembed_reindexedTensorPow_integrable`.  Bell re-key of
`bb84_rhoEtilde_eq_haar_integral_blocks`.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, the accept-block mixture split
`\label{eq:tausplit}` (`main.tex:1356`–`:1361`). -/
theorem bb84BellEnVRhoEtilde_eq_haar_integral_blocks {n : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    ∀ (x : Fin n → Fin signalDim)
      (i j : Fin (1 * (signalDim ^ n))),
      ((bb84BellEnVRhoEtilde 1 (bb84UnitRegisterEmbed n) (bb84UnitRegisterEmbed_isCPTP n) peSel xSel
          Q δ).stateMap x).toOp i j =
        ∫ φ : DensityOp 4,
          ((bb84PairedHaarPerSigmaFamily 1 (bb84UnitRegisterEmbed n)
              (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
            (bellWembed φ)).stateMap x).toOp i j ∂(deFinetti_haarMeasure 4).measure :=
  bb84_siftedLocalPE_blocks_eq_integral_of_toOp_eq_integral 1 (bb84UnitRegisterEmbed n)
      (bb84UnitRegisterEmbed_isCPTP n) peSel xSel Q δ
    (bb84BellPairedDeFinettiState n)
    (fun φ : DensityOp 4 =>
      densityOp_reindex (interleavingEquiv signalDim n).symm ((bellWembed φ).tensorPowGen n))
    bb84_bellWembed_reindexedTensorPow_integrable
    bb84BellPairedDeFinettiState_eq_haar_integral

end QKD.BB84.Engine

end -- noncomputable section
