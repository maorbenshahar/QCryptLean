import QCryptLean.QKD.BB84.Engine.Postselection.ProtocolMapCovariance
import QCryptLean.Quantum.Symmetry.TwirlPermCommute
import QCryptLean.QKD.BB84.Engine.PrivacyAmplification.B19Bridge
import QCryptLean.Quantum.Channels.CPTP.CKRBound.SymAverageBound
import QCryptLean.QKD.BB84.Engine.Postselection.AnnounceOrthogonalSectors
import QCryptLean.Quantum.Symmetry.BellDeFinettiDomination

/-!
# The Bell register extension

The CKR register extension over the Bell strings `(Fin 4)^n`, mirroring `blockDiagExt` over
`Equiv.Perm (Fin n)`. `bellRegExt ρ` embeds each twirl conjugate `(U_g ⊗ 1)·ρ·(U_g ⊗ 1)†` in a
separate `|g⟩⟨g|` block; the orthogonal blocks add, and (for any Bell-twirl trace-norm invariant
channel `Δ`, `RegisterTrick.lean`) each block is invariant, so `Δ`'s trace norm is preserved
**exactly** by the extension — no convexity loss, the gain the bare twirl average lacks. The
AB-marginal of `bellRegExt ρ` is the Bell twirl of `ρ`'s marginal.

## Main definitions and results

* `prodAssocFin` — the multiplication-associativity reindex `Fin (a*(c*k)) ≃ Fin ((a*c)*k)`, the
  bookkeeping that lets the announce-orthogonal trace-norm lemmas tensorize.
* `bellRegExt`, `bellRegBlock` — the Bell register extension and its per-string block.
* `bellRegExt_posSemidef` — the extension of a PSD operator is PSD.
* `bellRegReindexOut`, `bellRegExt_traceNorm_as_sum` — the extension's trace norm as a sum over
  the orthogonal Bell-string blocks.
* `bellRegExt_partialTraceB` — the AB-marginal of the extension is the Bell twirl of the input's
  marginal.

## References

Nahar, Tupkary, Zhao, Lütkenhaus, Tan (2024), `arXiv:2403.11851`, §II.B; Renner (2005),
`arXiv:quant-ph/0512258v2`, §6.5; Christandl–König–Renner (2009), `arXiv:0809.3019`, §III.
-/

open Quantum.Operators Quantum.TensorProducts Matrix Quantum.Channels Quantum.Symmetry
open Quantum.Metrics Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.Engine

open QKD.BB84.Model.bb84

/-!
## Generic `mapTensorId` register reassociation

`mapTensorId` over an outer register `k`, of `mapTensorId` over an inner register `c`, of a map
`Φ`, equals `mapTensorId` over the combined register `c * k` of `Φ`, up to the pure
multiplication-associativity reindex `Fin ((a*c)*k) ≃ Fin (a*(c*k))`.  This is the bookkeeping that
lets the announce-orthogonal trace-norm lemmas tensorize: appending the de Finetti reference
register `R` to the announce register `eveDim` is the same announce over the combined register.
-/

/-- The multiplication-associativity reindex `Fin (a*(c*k)) ≃ Fin ((a*c)*k)`, built from
`finProdFinEquiv` and `Equiv.prodAssoc`.  Forward sends `finProdFinEquiv (α, finProdFinEquiv (γ,
ρ))` to `finProdFinEquiv (finProdFinEquiv (α, γ), ρ)`. -/
def prodAssocFin (a c k : ℕ) : Fin (a * (c * k)) ≃ Fin ((a * c) * k) :=
  finProdFinEquiv.symm.trans
    ((Equiv.refl (Fin a)).prodCongr finProdFinEquiv.symm |>.trans
      (Equiv.prodAssoc (Fin a) (Fin c) (Fin k)).symm |>.trans
      (finProdFinEquiv.prodCongr (Equiv.refl (Fin k))) |>.trans
      finProdFinEquiv)

/-- Forward action of `prodAssocFin` on a doubly-nested index:
`finProdFinEquiv (i, finProdFinEquiv (c', k')) ↦ finProdFinEquiv (finProdFinEquiv (i, c'), k')`. -/
lemma prodAssocFin_apply_finProdFinEquiv (a c k : ℕ) [NeZero c] [NeZero k] [NeZero (c * k)]
    (i : Fin a) (c' : Fin c) (k' : Fin k) :
    prodAssocFin a c k (finProdFinEquiv (i, finProdFinEquiv (c', k'))) =
      finProdFinEquiv (finProdFinEquiv (i, c'), k') := by
  simp only [prodAssocFin, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply,
    id_eq, finProdFinEquiv_symm_apply, Equiv.prodAssoc_symm_apply, finProdFinEquiv_apply_divNat,
    finProdFinEquiv_apply_modNat]

/-- The inverse of `prodAssocFin` in `divNat`/`modNat` coordinates. -/
lemma prodAssocFin_symm_apply (a c k : ℕ) [NeZero c] [NeZero k] [NeZero (a * c)] [NeZero (c * k)]
    (x : Fin ((a * c) * k)) :
    (prodAssocFin a c k).symm x =
      finProdFinEquiv (x.divNat.divNat, finProdFinEquiv (x.divNat.modNat, x.modNat)) := by
  simp only [prodAssocFin, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodCongr_symm,
    Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
    Equiv.prodAssoc_apply, finProdFinEquiv_symm_apply]

/-- `mapTensorId` register reassociation (matrix form).  Threading an outer register `k` through a
`mapTensorIdLinear` over the inner register `c` is the same as a single `mapTensorId` over the
combined register `c * k`, conjugated by the associativity reindex. -/
lemma mapTensorId_mapTensorIdLinear_reassoc {a b c k : ℕ}
    [NeZero a] [NeZero b] [NeZero c] [NeZero k] [NeZero (a * c)] [NeZero (b * c)]
    [NeZero (c * k)]
    (Φ : Op a →ₗ[ℂ] Op b) (W : Op ((a * c) * k)) :
    mapTensorId (k := k) (mapTensorIdLinear (k := c) Φ) W =
      (mapTensorId (k := c * k) Φ (W.submatrix (prodAssocFin a c k) (prodAssocFin a c k))).submatrix
        (prodAssocFin b c k).symm (prodAssocFin b c k).symm := by
  classical
  ext p q
  simp only [Matrix.submatrix_apply]
  rw [mapTensorId_apply_eq_apply_block]
  change (mapTensorId (k := c) Φ _) _ _ = _
  rw [mapTensorId_apply_eq_apply_block, mapTensorId_apply_eq_apply_block]
  simp only [Matrix.of_apply, Matrix.submatrix_apply, prodAssocFin_symm_apply,
    finProdFinEquiv_symm_apply, finProdFinEquiv_apply_divNat, finProdFinEquiv_apply_modNat,
    prodAssocFin_apply_finProdFinEquiv]

/-!
## `bellRegExt`, the CKR register extension over the Bell strings

The Bell analogue of `blockDiagExt`: it averages `ρ` over all Bell-twirl conjugates, embedding each
conjugate `(U_g ⊗ 1)·ρ·(U_g ⊗ 1)†` in a separate `|g⟩⟨g|` block indexed by the twirl string
`g ∈ (Fin 4)^n` (the `4^n`-dimensional CKR label register).  The orthogonal `|g⟩` blocks add, and
for a Bell-twirl trace-norm invariant channel each block is invariant, so the trace norm is
preserved exactly (no convexity loss — the gain the bare twirl average lacks), and the AB-marginal
is the Bell twirl of `ρ`'s marginal.
-/

/-- **The Bell register extension of `ρ`** over all Bell-twirl conjugates.

Defined entry-by-entry (mirroring `blockDiagExt`): for indices `(a, (b, ν))` and `(a', (b', ν'))`,
the entry is `(1/4^n) · ((U_{g(ν)} ⊗ 1) ρ (U_{g(ν)} ⊗ 1)†)[(a,b),(a',b')]` when `ν = ν'` and `0`
otherwise, where `g(ν) = (finFunctionFinEquiv 4 n).symm ν` is the Bell string indexed by the
`4^n`-dimensional label `ν`.  Explicit; no `Classical.choose`. -/
noncomputable def bellRegExt {n dimR : ℕ} [NeZero (4 ^ n)] (ρ : Op (4 ^ n * dimR)) :
    Op (4 ^ n * (dimR * 4 ^ n)) :=
  let c : ℂ := 1 / (4 ^ n : ℂ)
  Matrix.of fun α β =>
    let p := finProdFinEquiv.symm α
    let ps := finProdFinEquiv.symm p.2
    let q := finProdFinEquiv.symm β
    let qs := finProdFinEquiv.symm q.2
    if ps.2 = qs.2 then
      let g := (@finFunctionFinEquiv 4 n).symm ps.2
      c * (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR) * ρ *
           (Op.tensor (bellTwirlUnitary n g) (1 : Op dimR))ᴴ)
        (finProdFinEquiv (p.1, ps.1)) (finProdFinEquiv (q.1, qs.1))
    else 0

/-- The Bell-block family on the `4^n`-dimensional label register. Public so that generic-in-`Δ`
consumers (`RegisterTrickReferee.lean`) can cite it directly instead of re-deriving a local copy. -/
noncomputable def bellRegBlock {n dimR : ℕ} [NeZero (4 ^ n)] (ρ : Op (4 ^ n * dimR)) :
    Fin (4 ^ n) → Op (4 ^ n * dimR) :=
  fun ν => (1 / (4 ^ n : ℂ)) •
    (Op.tensor (bellTwirlUnitary n ((@finFunctionFinEquiv 4 n).symm ν)) (1 : Op dimR) * ρ *
      (Op.tensor (bellTwirlUnitary n ((@finFunctionFinEquiv 4 n).symm ν)) (1 : Op dimR))ᴴ)

/-- The reindex `Fin (4^n * (dimR * 4^n)) ≃ Fin (4^n * dimR) × Fin (4^n)` peeling off the Bell
label register. -/
private def bellRegReindex (n dimR : ℕ) :
    Fin (4 ^ n * (dimR * 4 ^ n)) ≃ Fin (4 ^ n * dimR) × Fin (4 ^ n) :=
  finProdFinEquiv.symm.trans
    ((Equiv.refl _).prodCongr finProdFinEquiv.symm |>.trans
      (Equiv.prodAssoc _ _ _).symm |>.trans
      (finProdFinEquiv.prodCongr (Equiv.refl _)))

/-- `bellRegExt ρ` is the reindexed block-diagonal of the Bell-block family. -/
private lemma bellRegExt_eq_blockDiagonal {n dimR : ℕ} [NeZero (4 ^ n)] [NeZero dimR]
    (ρ : Op (4 ^ n * dimR)) :
    bellRegExt ρ =
      (Matrix.blockDiagonal (bellRegBlock ρ)).submatrix (bellRegReindex n dimR)
        (bellRegReindex n dimR) := by
  ext α β
  simp only [bellRegExt, bellRegBlock, bellRegReindex, Matrix.of_apply, Matrix.submatrix_apply,
    Matrix.blockDiagonal_apply, Matrix.smul_apply, smul_eq_mul,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq,
    Equiv.prodAssoc_symm_apply]

/-- **The Bell register extension is positive semidefinite** (sum of PSD conjugates, scaled by
`(1/4^n) ≥ 0`).  Mirror of `blockDiagExt_posSemidef`. -/
lemma bellRegExt_posSemidef {n dimR : ℕ} [NeZero (4 ^ n)] [NeZero dimR]
    (ρ : Op (4 ^ n * dimR)) (hρ : ρ.PosSemidef) :
    (bellRegExt ρ).PosSemidef := by
  rw [bellRegExt_eq_blockDiagonal ρ]
  refine (posSemidef_submatrix_equiv (bellRegReindex n dimR)).mpr
    (Matrix.posSemidef_blockDiagonal fun ν => ?_)
  refine (hρ.mul_mul_conjTranspose_same _).smul ?_
  rw [one_div, show ((4 : ℂ) ^ n) = (((4 : ℝ) ^ n : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_inv]
  exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (by positivity))

/-- The output-side reindex `Fin (dimOut * (dimR * 4^n)) ≃ Fin (dimOut * dimR) × Fin (4^n)`. Public
so that generic-in-`Δ` consumers (`RegisterTrickReferee.lean`) can cite it directly instead of
re-deriving a local copy. -/
def bellRegReindexOut (dimOut dimR n : ℕ) :
    Fin (dimOut * (dimR * 4 ^ n)) ≃ Fin (dimOut * dimR) × Fin (4 ^ n) :=
  finProdFinEquiv.symm.trans
    ((Equiv.refl _).prodCongr finProdFinEquiv.symm |>.trans
      (Equiv.prodAssoc _ _ _).symm |>.trans
      (finProdFinEquiv.prodCongr (Equiv.refl _)))

/-- **The trace norm of `(Δ ⊗ id)(bellRegExt ρ)` decomposes over the orthogonal Bell-label blocks**
(mirror of `Quantum.Channels.blockDiagExtFamily_traceNorm_as_sum`). Already generic in `Δ`; public
so that `RegisterTrickReferee.lean`'s generic-in-`Δ` invariance argument can cite it directly
instead of re-deriving a local copy. -/
lemma bellRegExt_traceNorm_as_sum {n dimR dimOut : ℕ} [NeZero (4 ^ n)] [NeZero dimR]
    [NeZero dimOut] (Δ : Op (4 ^ n) →ₗ[ℂ] Op dimOut) (ρ : Op (4 ^ n * dimR)) :
    traceNorm (mapTensorId (k := dimR * 4 ^ n) Δ (bellRegExt ρ)) =
      ∑ ν : Fin (4 ^ n),
        ‖(1 : ℂ) / (4 ^ n : ℂ)‖ *
          traceNorm (mapTensorId (k := dimR) Δ
            (Op.tensor (bellTwirlUnitary n ((@finFunctionFinEquiv 4 n).symm ν)) (1 : Op dimR) * ρ *
              (Op.tensor (bellTwirlUnitary n ((@finFunctionFinEquiv 4 n).symm ν)) (1 : Op dimR))ᴴ))
                  := by
  set M := bellRegBlock ρ with hM
  set M' := fun ν : Fin (4 ^ n) => mapTensorId (k := dimR) Δ (M ν) with hM'
  set e_out : Fin (dimOut * (dimR * 4 ^ n)) ≃ Fin (dimOut * dimR) × Fin (4 ^ n) :=
    bellRegReindexOut dimOut dimR n with he_out
  -- Step 1: `(Δ ⊗ id)` preserves the block-diagonal structure of `bellRegExt`.
  have h_map_bd : mapTensorId (k := dimR * 4 ^ n) Δ (bellRegExt ρ) =
      (Matrix.blockDiagonal M').submatrix e_out e_out := by
    ext p q
    simp only [mapTensorId, Matrix.of_apply, bellRegExt, Matrix.blockDiagonal_apply,
      Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, Equiv.symm_apply_apply, e_out,
      bellRegReindexOut, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst,
      Prod.map_snd, id_eq, Equiv.prodAssoc_symm_apply, M', M, bellRegBlock,
      Matrix.smul_apply, smul_eq_mul]
    split_ifs with h
    · rfl
    · simp [mul_zero]
  -- Step 2: trace norm of the reindexed block diagonal = sum of block trace norms.
  have h_tn_bd : traceNorm ((Matrix.blockDiagonal M').submatrix e_out e_out) =
      ∑ ν, traceNorm (M' ν) := by
    set φ : Fin (dimOut * (dimR * 4 ^ n)) ≃ Fin ((dimOut * dimR) * 4 ^ n) :=
      e_out.trans finProdFinEquiv with hφ
    have h_eq : (Matrix.blockDiagonal M').submatrix (⇑e_out) (⇑e_out) =
        (∑ ν, M' ν ⊗ (Matrix.single ν ν (1 : ℂ) : Op (4 ^ n))).submatrix φ φ := by
      rw [sum_tensor_single_eq_reindex_blockDiagonal, Matrix.reindex_apply,
        Matrix.submatrix_submatrix]
      congr 1 <;> funext x <;> simp [φ, Equiv.symm_apply_apply]
    rw [h_eq, traceNorm_submatrix_equiv]
    exact traceNorm_blockDiagonal_sum M'
  rw [h_map_bd, h_tn_bd]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  simp only [hM', hM, bellRegBlock]
  rw [mapTensorId_smul_basic, Quantum.Metrics.TraceNormHoelder.traceNorm_smul_eq]

/-- **The AB-marginal of `bellRegExt ρ` is the Bell twirl of `ρ`'s marginal.**

`partialTraceB (bellRegExt ρ) = bb84BellTwirl n (partialTraceB ρ)`: tracing out the reference and
label registers leaves the IID Bell twirl of `ρ`'s AB-marginal, hence `IsIIDBellDiagonal` — the
hypothesis that feeds the de Finetti domination.  Mirror of `blockDiagExt_partialTraceB`. -/
theorem bellRegExt_partialTraceB {n dimR : ℕ} [NeZero (4 ^ n)] [NeZero dimR]
    (ρ : Op (4 ^ n * dimR)) :
    partialTraceB (bellRegExt ρ) = bb84BellTwirl n (partialTraceB ρ) := by
  -- the per-label sandwich identity
  have h_sandwich : ∀ ν : Fin (4 ^ n),
      partialTraceB
          (Op.tensor (bellTwirlUnitary n ((@finFunctionFinEquiv 4 n).symm ν)) (1 : Op dimR) * ρ *
            (Op.tensor (bellTwirlUnitary n ((@finFunctionFinEquiv 4 n).symm ν)) (1 : Op dimR))ᴴ) =
        bellTwirlUnitary n ((@finFunctionFinEquiv 4 n).symm ν) * partialTraceB ρ *
          (bellTwirlUnitary n ((@finFunctionFinEquiv 4 n).symm ν))ᴴ := by
    intro ν
    rw [Op.tensor_conjTranspose, conjTranspose_one]
    exact partialTraceB_sandwich_tensor_one _ _ _
  -- the block-diagonal partial trace collapses to the label average
  have havg : partialTraceB (bellRegExt ρ) =
      (1 / (4 ^ n : ℂ)) • ∑ ν : Fin (4 ^ n),
        partialTraceB
          (Op.tensor (bellTwirlUnitary n ((@finFunctionFinEquiv 4 n).symm ν)) (1 : Op dimR) * ρ *
            (Op.tensor (bellTwirlUnitary n ((@finFunctionFinEquiv 4 n).symm ν)) (1 : Op dimR))ᴴ) :=
                by
    ext a a'
    simp only [partialTraceB, bellRegExt, Matrix.of_apply, Matrix.smul_apply, Finset.smul_sum,
      Matrix.sum_apply]
    simp only [Equiv.symm_apply_apply, if_true, smul_eq_mul]
    rw [Finset.sum_comm, ← Equiv.sum_comp finProdFinEquiv]
    simp_rw [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type]
  rw [havg]
  simp_rw [h_sandwich]
  rw [bb84BellTwirl,
    ← Equiv.sum_comp (@finFunctionFinEquiv 4 n).symm
      (fun g => bellTwirlUnitary n g * partialTraceB ρ * (bellTwirlUnitary n g)ᴴ), one_div]

end QKD.BB84.Engine

end
