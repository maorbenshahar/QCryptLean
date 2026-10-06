import QCryptLean.Quantum.Symmetry.FiniteGroupUnitaryRep
import QCryptLean.Quantum.TensorProducts.TensorFamily
import QCryptLean.Quantum.TensorProducts.TensorPow
import QCryptLean.InfoTheory.DeFinetti.MaxEntangled
import QCryptLean.InfoTheory.DeFinetti.Purification
import QCryptLean.InfoTheory.Postselection.SchurWeylTwirl
import QCryptLean.InfoTheory.Postselection.PairedBlockedOperators
import QCryptLean.InfoTheory.Postselection.GroupInvariantStates

/-!
# The group-symmetric purification lemma

The paired group twirl `Π_π^{⊗n}` — the tensor power of the projector onto the
invariant vectors of `π ⊗ conj π`, regrouped onto `ℂ^(d^n) ⊗ ℂ^(d^n)` — and its
interaction with the paired symmetric projector.

Main result: `groupPurification` (arXiv:2403.11851, Lemma `lem:groupPurification`).
A permutation-invariant, IID-group-invariant state has a pure purification
supported on both the paired symmetric subspace and the paired group-twirl
range. `groupPurification_prod` is its specialization to independent product-group
actions `G_A × G_B` (the form used for two-party protocols), and
`groupTwirlProjector_prod_trace` records the multiplicativity of the twirl trace under
product representations.
-/

open Quantum.Operators Quantum.TensorProducts Quantum.Symmetry Matrix
open InfoTheory.DeFinetti MeasureTheory
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace InfoTheory.Postselection

/-! ### The paired group twirl projector -/

/-- The tensor power of the paired group twirl, regrouped onto the two registers
`ℂ^(d^n) ⊗ ℂ^(d^n)`. -/
def groupPairedTwirlProjector {G : Type*} [Group G] [Fintype G] {d : ℕ} (n : ℕ) (π : G → Op d) :
    Op (d ^ n * d ^ n) :=
  Matrix.reindex (interleavingEquivGen d d n).symm (interleavingEquivGen d d n).symm
    (Op.tensorPow (groupTwirlProjector π) n)

/-! ### Helpers for `groupPurification` -/

/-- Two-factor left ricochet for the maximally entangled operator: `(X ⊗ Y) |Ω⟩⟨Ω| =
    (X·Yᵀ ⊗ 1) |Ω⟩⟨Ω|` (generalizes `maxEntangledOp_tensor_one_ricochet`, which is the `Y = 1`
    case read backwards). -/
lemma maxEntangledOp_tensor_ricochet {m : ℕ} (X Y : Op m) :
    Op.tensor X Y * maxEntangledOp m =
      Op.tensor (X * Y.transpose) (1 : Op m) * maxEntangledOp m := by
  have hsplit : Op.tensor X Y = Op.tensor X (1 : Op m) * Op.tensor (1 : Op m) Y := by
    rw [Op.tensor_mul]; simp
  have h1 : Op.tensor (1 : Op m) Y * maxEntangledOp m =
      Op.tensor Y.transpose (1 : Op m) * maxEntangledOp m := by
    rw [maxEntangledOp_tensor_one_ricochet (A := Y.transpose), Matrix.transpose_transpose]
  calc Op.tensor X Y * maxEntangledOp m
      = Op.tensor X (1 : Op m) * (Op.tensor (1 : Op m) Y * maxEntangledOp m) := by
        rw [hsplit, Matrix.mul_assoc]
    _ = Op.tensor X (1 : Op m) * (Op.tensor Y.transpose (1 : Op m) * maxEntangledOp m) := by
        rw [h1]
    _ = Op.tensor (X * Y.transpose) (1 : Op m) * maxEntangledOp m := by
        rw [← Matrix.mul_assoc, Op.tensor_mul]; simp

/-- If a unitary `U` (`U·Uᴴ = 1`) commutes with `ρ`, then `U √ρ Uᴴ = √ρ` (combine
    `sqrtOp_commutes_of_commutes` with unitarity). -/
lemma sqrtOp_conj_invariant {m : ℕ} (ρ : DensityOp m) (U : Op m)
    (hU : U * Uᴴ = 1) (hcomm : U * ρ.toOp = ρ.toOp * U) :
    U * sqrtOp ρ * Uᴴ = sqrtOp ρ := by
  rw [sqrtOp_commutes_of_commutes ρ U hcomm, Matrix.mul_assoc, hU, mul_one]

/-- **Left invariance of the canonical purification under the round-paired group action**: for
    `v ∈ Gⁿ`, the operator `⊗ₐ π(vₐ) ⊗ ⊗ₐ conj(π(vₐ))` fixes the purification `Ψ_ρ` on the left.

    Key computation: with `W := ⊗ₐ π(vₐ)`, the second factor's transpose is
    `conj(W)ᵀ = Wᴴ`, so the ricochet lemma turns the sandwich into
    `W √ρ Wᴴ = √ρ` (the IID-`G`-invariance transported to `√ρ`). -/
lemma purificationOp_group_left_invariant {G : Type*} [Group G] {d n : ℕ} [NeZero d] [NeZero n]
    [NeZero (d ^ n)] (π : G → Op d) (hπ : IsUnitaryRep π) (ρ : DensityOp (d ^ n))
    (hiid : IsIIDGroupInvariant π ρ) (v : Fin n → G) :
    Op.tensor (tensorFamily fun a => π (v a))
      (tensorFamily fun a => entryConj (π (v a))) * (purificationDensityOp ρ).toOp =
      (purificationDensityOp ρ).toOp := by
  set W : Op (d ^ n) := tensorFamily fun a => π (v a) with hW
  set C : Op (d ^ n) := tensorFamily fun a => entryConj (π (v a)) with hC
  -- Each `π (v a)` is unitary, hence `W` is unitary (both ways)
  have hunit : ∀ g : G, π g * (π g)ᴴ = 1 := fun g => by
    rw [← IsUnitaryRep.inv hπ g, ← hπ.1 g g⁻¹, mul_inv_cancel, IsUnitaryRep.one hπ]
  have hWu : W * Wᴴ = 1 := by
    rw [hW]; exact tensorFamily_mul_conjTranspose_self fun a => hunit (v a)
  have hWW : Wᴴ * W = 1 := by
    rw [hW]; exact conjTranspose_tensorFamily_mul_self fun a => hπ.2 (v a)
  -- The conjugate family has transpose `Wᴴ`
  have hCt : Cᵀ = Wᴴ := by
    ext i j
    simp [hC, hW, entryConj, Matrix.transpose_apply, tensorFamily_apply,
      Matrix.conjTranspose_apply, star_prod]
  -- `G`-invariance of `ρ` makes `W` commute with `ρ`
  have hcomm : W * ρ.toOp = ρ.toOp * W := by
    calc W * ρ.toOp = W * ρ.toOp * (Wᴴ * W) := by rw [hWW, mul_one]
      _ = (W * ρ.toOp * Wᴴ) * W := by rw [← Matrix.mul_assoc]
      _ = ρ.toOp * W := by rw [hiid v]
  -- Hence `W` fixes `√ρ` under conjugation
  have hsqrt : W * sqrtOp ρ * Wᴴ = sqrtOp ρ := sqrtOp_conj_invariant ρ W hWu hcomm
  have hkey : W * sqrtOp ρ * Cᵀ = sqrtOp ρ := by rw [hCt]; exact hsqrt
  -- The canonical purification is `Ψ = (√ρ ⊗ 1) |Ω⟩⟨Ω| (√ρ ⊗ 1)ᴴ`
  have hpur : (purificationDensityOp ρ).toOp
      = Op.tensor (sqrtOp ρ) (1 : Op (d ^ n)) * maxEntangledOp (d ^ n)
        * (Op.tensor (sqrtOp ρ) (1 : Op (d ^ n)))ᴴ := rfl
  -- Push `W ⊗ conj W` through the first factor, ricochet it through `|Ω⟩⟨Ω|`, use `hkey`
  calc Op.tensor W C * (purificationDensityOp ρ).toOp
      = (Op.tensor W C * Op.tensor (sqrtOp ρ) (1 : Op (d ^ n)) * maxEntangledOp (d ^ n)) *
          (Op.tensor (sqrtOp ρ) (1 : Op (d ^ n)))ᴴ := by
        rw [hpur, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    _ = (Op.tensor (W * sqrtOp ρ * Cᵀ) (1 : Op (d ^ n)) * maxEntangledOp (d ^ n)) *
          (Op.tensor (sqrtOp ρ) (1 : Op (d ^ n)))ᴴ := by
        rw [Op.tensor_mul, mul_one, maxEntangledOp_tensor_ricochet]
    _ = (Op.tensor (sqrtOp ρ) (1 : Op (d ^ n)) * maxEntangledOp (d ^ n)) *
          (Op.tensor (sqrtOp ρ) (1 : Op (d ^ n)))ᴴ := by rw [hkey]
    _ = (purificationDensityOp ρ).toOp := by rw [hpur]

/-- **Expansion of the round-paired twirl projector as an average over `v ∈ Gⁿ`**: the
    interleaving transport of `Π_π^{⊗n}` equals the average of the round-paired group actions
    `⊗ₐ π(vₐ) ⊗ ⊗ₐ conj(π(vₐ))` (tensor-power multilinearity
    `tensorFamily_sum` + entrywise reindexing through `interleavingEquivGen`). -/
lemma groupPairedTwirlProjector_eq_sum {G : Type*} [Group G] [Fintype G] {d n : ℕ} [NeZero d]
    [NeZero n] [NeZero (d ^ n)] (π : G → Op d) :
    groupPairedTwirlProjector n π = ((Fintype.card (Fin n → G) : ℕ) : ℂ)⁻¹ •
      ∑ v : Fin n → G, Op.tensor (tensorFamily fun a => π (v a))
        (tensorFamily fun a => entryConj (π (v a))) := by
  -- `|Fin n → G| = |G|ⁿ`
  have hcard : ((Fintype.card (Fin n → G) : ℕ) : ℂ)⁻¹ = ((Fintype.card G : ℕ) : ℂ)⁻¹ ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, inv_pow]
  -- The tensor power of `Π_π` expands, by multilinearity, over the average over `G`
  have hexpand : Op.tensorPow (groupTwirlProjector π) n
      = ((Fintype.card G : ℕ) : ℂ)⁻¹ ^ n •
        ∑ v : Fin n → G, tensorFamily fun k => Op.tensor (π (v k)) (entryConj (π (v k))) := by
    simp only [groupTwirlProjector, groupTwirlProjectorPair, Op.tensorPow_eq_tensorFamily,
      tensorFamily_const_smul]
    exact congrArg (fun X => ((Fintype.card G : ℕ) : ℂ)⁻¹ ^ n • X)
      (tensorFamily_sum fun k (g : G) => Op.tensor (π g) (entryConj (π g)))
  -- Reindexing through the interleaving equivalence is linear (entrywise)
  have hlin : ∀ (c : ℂ) (F : (Fin n → G) → Op ((d * d) ^ n)),
      Matrix.reindex (interleavingEquivGen d d n).symm (interleavingEquivGen d d n).symm
          (c • ∑ v : Fin n → G, F v)
        = c • ∑ v : Fin n → G, Matrix.reindex (interleavingEquivGen d d n).symm
            (interleavingEquivGen d d n).symm (F v) := by
    intro c F
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.smul_apply,
      Matrix.sum_apply, Finset.mul_sum, Finset.smul_sum, smul_eq_mul]
  rw [groupPairedTwirlProjector, hexpand, hlin]
  simp only [tensorFamily_tensor_interleaving]
  rw [hcard]

/-- Every paired round-family group action fixes the group-twirl range pointwise. -/
lemma pairedGroupAction_mul_groupPairedTwirlProjector
    {G : Type*} [Group G] [Fintype G] {d n : ℕ} [NeZero d] [NeZero n]
    (π : G → Op d) (hπ : IsUnitaryRep π) (v : Fin n → G) :
    Op.tensor (tensorFamily fun k => π (v k)) (tensorFamily fun k => entryConj (π (v k))) *
      groupPairedTwirlProjector n π = groupPairedTwirlProjector n π := by
  haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  rw [groupPairedTwirlProjector_eq_sum, mul_smul_comm, Finset.mul_sum]
  congr 1
  simp_rw [Op.tensor_mul, tensorFamily_mul]
  simp_rw [← entryConj_mul, ← hπ.1]
  exact Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun _ => rfl)

/-- The round-paired twirl projector is Hermitian (it is a reindexing of a tensor power of the
    Hermitian projector `Π_π`; `Matrix.conjTranspose_reindex` + `Op.conjTranspose_tensorPow`). -/
lemma groupPairedTwirlProjector_isHermitian {G : Type*} [Group G] [Fintype G] {d n : ℕ}
    [NeZero d] (π : G → Op d) (hπ : IsUnitaryRep π) :
    (groupPairedTwirlProjector n π)ᴴ = groupPairedTwirlProjector n π := by
  have hProj := (groupTwirlProjector_isOrthogonalProjection π hπ).1
  unfold groupPairedTwirlProjector
  rw [Matrix.conjTranspose_reindex, Op.conjTranspose_tensorPow, hProj]

/-- The round-paired twirl projector is idempotent (it is a reindexing of a tensor power of the
    orthogonal-projection twirl `Π_π`; `Op.tensorPow` is multiplicative and `Π_π · Π_π = Π_π`
    by `groupTwirlProjector_isOrthogonalProjection`). -/
lemma groupPairedTwirlProjector_isProjection {G : Type*} [Group G] [Fintype G] {d n : ℕ}
    [NeZero d] (π : G → Op d) (hπ : IsUnitaryRep π) :
    groupPairedTwirlProjector n π * groupPairedTwirlProjector n π =
      groupPairedTwirlProjector n π := by
  have hProj := (groupTwirlProjector_isOrthogonalProjection π hπ).2
  unfold groupPairedTwirlProjector
  rw [← Matrix.reindex_mul, ← Op.mul_tensorPow, hProj]

/-- The round-paired twirl projector commutes with the paired symmetric projector. Both are
    the transports (via `interleavingEquivGen d d n`) of flat-register objects on
    `(ℂ^{d·d})^{⊗n}`: `Π_π^{⊗n}` commutes with every round permutation of its copies
    (`Op.commute_tensorPow_permutationRepresentation`, base `ℂ^{d·d}`), hence with their
    normalized average `P_sym`; `Matrix.reindex_mul` transports the commutation back. -/
lemma groupPairedTwirlProjector_commute_symmetricProjectorPaired {G : Type*} [Group G] [Fintype G]
    {d n : ℕ} [NeZero d] [NeZero n] (π : G → Op d) :
    groupPairedTwirlProjector n π * symmetricProjectorPaired d n =
      symmetricProjectorPaired d n * groupPairedTwirlProjector n π := by
  haveI : NeZero (d * d) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d)⟩
  -- both projectors, pulled back to the flat register `(ℂ^{d·d})^{⊗n}`
  have hQ' : groupPairedTwirlProjector n π =
      Matrix.reindex (interleavingEquivGen d d n).symm (interleavingEquivGen d d n).symm
        (Op.tensorPow (groupTwirlProjector π) n) := rfl
  have hPflat : Matrix.reindex (interleavingEquivGen d d n) (interleavingEquivGen d d n)
      (symmetricProjectorPaired d n) = symmetricProjector (d * d) n := by
    rw [symmetricProjectorPaired_eq_gen]
    exact interleavingEquivGen_conjugates_projector (dA := d) (dR := d) (n := n)
  have hP' : symmetricProjectorPaired d n =
      Matrix.reindex (interleavingEquivGen d d n).symm (interleavingEquivGen d d n).symm
        (symmetricProjector (d * d) n) := by
    rw [← hPflat, Matrix.reindex_symm_reindex]
  -- on the flat register, `Π_π^{⊗n}` commutes with the averaged round permutations
  have havg : Op.tensorPow (groupTwirlProjector π) n * symmetricProjector (d * d) n =
      symmetricProjector (d * d) n * Op.tensorPow (groupTwirlProjector π) n := by
    unfold symmetricProjector Math.RepresentationTheory.symmetricProjectorRep
    rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
    refine congrArg ((1 / (Nat.factorial n : ℂ)) • ·)
      (Finset.sum_congr rfl fun σ _ => ?_)
    exact (Op.commute_tensorPow_permutationRepresentation (groupTwirlProjector π) σ).eq
  rw [hQ', hP', ← Matrix.reindex_mul, ← Matrix.reindex_mul, havg]

/-- Tracing out the reference of a group-twirl-supported Hermitian operator
leaves an operator invariant under each round-family group action. -/
lemma partialTraceB_groupPairedTwirl_supported_invariant
    {G : Type*} [Group G] [Fintype G] {d n : ℕ} [NeZero d] [NeZero n]
    (π : G → Op d) (hπ : IsUnitaryRep π) (X : Op (d ^ n * d ^ n))
    (hX : X.IsHermitian) (hsupp : groupPairedTwirlProjector n π * X = X)
    (v : Fin n → G) :
    tensorFamily (fun k => π (v k)) * partialTraceB X *
      (tensorFamily (fun k => π (v k)))ᴴ = partialTraceB X := by
  let U := tensorFamily (fun k => π (v k))
  let V := tensorFamily (fun k => entryConj (π (v k)))
  have hRX : Op.tensor U V * X = X := by
    rw [← hsupp, ← mul_assoc, pairedGroupAction_mul_groupPairedTwirlProjector π hπ]
  have hXR : X * (Op.tensor U V)ᴴ = X := by
    have h := congrArg Matrix.conjTranspose hRX
    simpa only [Matrix.conjTranspose_mul, hX.eq] using h
  have hV : Vᴴ * V = 1 := by
    apply conjTranspose_tensorFamily_mul_self
    intro k
    rw [entryConj_conjTranspose, ← entryConj_mul, hπ.2, entryConj_one]
  have hconj : Op.tensor U V * X * Op.tensor Uᴴ Vᴴ = X := by
    rw [← Op.tensor_conjTranspose, hRX, hXR]
  have h := partialTraceB_sandwich_tensor_unitary U Uᴴ V hV X
  rw [hconj] at h
  exact h.symm

/-! ### The group purification lemma -/

/-- The canonical purification of an IID-`G`-invariant state is fixed on both sides by the
paired group-twirl projector. -/
theorem purificationDensityOp_groupTwirlSupported {G : Type*} [Group G] [Fintype G]
    {d n : ℕ} [NeZero d] [NeZero n] (π : G → Op d) (hπ : IsUnitaryRep π)
    (ρ : DensityOp (d ^ n)) (hiid : IsIIDGroupInvariant π ρ) :
    groupPairedTwirlProjector n π * (purificationDensityOp ρ).toOp *
      groupPairedTwirlProjector n π = (purificationDensityOp ρ).toOp := by
  haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  -- left-invariance: average the per-round-pattern left-invariance over `Gⁿ`
  have hQleft : groupPairedTwirlProjector n π * (purificationDensityOp ρ).toOp
      = (purificationDensityOp ρ).toOp := by
    have hc : ((Fintype.card (Fin n → G) : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
    rw [groupPairedTwirlProjector_eq_sum π, smul_mul_assoc, Finset.sum_mul,
      Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) =>
        purificationOp_group_left_invariant π hπ ρ hiid v,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  -- right-invariance from left-invariance by Hermiticity of `Ψ` and of the projector
  have hΨherm : ((purificationDensityOp ρ).toOp)ᴴ = (purificationDensityOp ρ).toOp :=
    (purificationDensityOp ρ).isHermitian.eq
  have hQright : (purificationDensityOp ρ).toOp * groupPairedTwirlProjector n π
      = (purificationDensityOp ρ).toOp := by
    calc (purificationDensityOp ρ).toOp * groupPairedTwirlProjector n π
        = (groupPairedTwirlProjector n π * (purificationDensityOp ρ).toOp)ᴴ := by
          rw [conjTranspose_mul, groupPairedTwirlProjector_isHermitian π hπ, hΨherm]
      _ = (purificationDensityOp ρ).toOp := by rw [hQleft, hΨherm]
  rw [hQleft, hQright]

/-- A permutation-invariant, IID group-invariant state has a pure purification
supported on both the paired symmetric subspace and the paired group-twirl range. -/
theorem groupPurification {G : Type*} [Group G] [Fintype G] {d n : ℕ} [NeZero d] [NeZero n]
    (π : G → Op d) (hπ : IsUnitaryRep π) (ρ : DensityOp (d ^ n))
    (hperm : IsPermutationInvariant ρ) (hiid : IsIIDGroupInvariant π ρ) :
    ∃ Ψ : DensityOp (d ^ n * d ^ n),
      Ψ.IsPure ∧
      partialTraceB Ψ.toOp = ρ.toOp ∧
      groupPairedTwirlProjector n π * Ψ.toOp * groupPairedTwirlProjector n π = Ψ.toOp ∧
      symmetricProjectorPaired d n * Ψ.toOp * symmetricProjectorPaired d n = Ψ.toOp := by
  -- The canonical purification `Ψ_ρ = (√ρ ⊗ 1)|Ω⟩⟨Ω|(√ρ ⊗ 1)†`
  haveI : NeZero (d ^ n) := ⟨pow_ne_zero n (NeZero.ne d)⟩
  refine ⟨purificationDensityOp ρ, purificationDensityOp_isPure ρ, ?_, ?_, ?_⟩
  · -- Partial trace recovers `ρ` (the canonical purification's marginal)
    exact congrArg (fun τ : DensityOp (d ^ n) => τ.toOp)
      (purificationDensityOp_partialTraceB ρ)
  · -- Round-paired twirl sandwich: the canonical purification is group-twirl supported
    exact purificationDensityOp_groupTwirlSupported π hπ ρ hiid
  · -- The paired symmetric sandwich is the permutation-invariance part
    exact purificationDensityOp_in_paired_symmetric_subspace ρ hperm

/-- A permutation-invariant state invariant under independent product-group
actions has a purification supported on the symmetric tensor power of the paired
product-group invariant subspace. -/
theorem groupPurification_prod {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A]
    [Fintype G_B] {dA dB n : ℕ} [NeZero dA] [NeZero dB] [NeZero (dA * dB)] [NeZero n]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA) (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (ρ : DensityOp ((dA * dB) ^ n))
    (hperm : IsPermutationInvariant ρ)
    (hiid : IsIIDGroupInvariant (prodRep πA πB) ρ) :
    ∃ Ψ : DensityOp ((dA * dB) ^ n * (dA * dB) ^ n),
      Ψ.IsPure ∧
      partialTraceB Ψ.toOp = ρ.toOp ∧
      groupPairedTwirlProjector n (prodRep πA πB) * Ψ.toOp *
        groupPairedTwirlProjector n (prodRep πA πB) = Ψ.toOp ∧
      symmetricProjectorPaired (dA * dB) n * Ψ.toOp *
        symmetricProjectorPaired (dA * dB) n = Ψ.toOp := by
  -- Specialize `groupPurification` to `G = G_A × G_B` with the product representation.
  exact groupPurification (prodRep πA πB) (prodRep_isUnitaryRep πA hπA πB hπB) ρ hperm hiid

/-- The paired twirl trace of a product representation is the product of the
paired twirl traces. Thus squared irreducible multiplicities multiply across the factors. -/
theorem groupTwirlProjector_prod_trace {G_A G_B : Type*} [Group G_A] [Group G_B] [Fintype G_A]
    [Fintype G_B] {dA dB : ℕ} [NeZero dA] [NeZero dB]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA) (πB : G_B → Op dB) (hπB : IsUnitaryRep πB) :
      (groupTwirlProjector (prodRep πA πB)).trace =
      (groupTwirlProjector πA).trace * (groupTwirlProjector πB).trace := by
  rw [groupTwirlProjector_trace_inv _ (prodRep_isUnitaryRep πA hπA πB hπB),
    groupTwirlProjector_trace_inv πA hπA, groupTwirlProjector_trace_inv πB hπB]
  have hsum : ∑ g : G_A × G_B, (prodRep πA πB g).trace * (prodRep πA πB g⁻¹).trace =
      (∑ a : G_A, (πA a).trace * (πA a⁻¹).trace) *
        ∑ b : G_B, (πB b).trace * (πB b⁻¹).trace := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [prodRep, Op.trace_tensor]
    exact mul_mul_mul_comm _ _ _ _
  rw [hsum, Fintype.card_prod, Nat.cast_mul, mul_inv]
  ring

/-- The one-round product-group twirl trace is the sum of squared irreducible
multiplicities `∑ i ∑ j (mA i)² (mB j)²` — the product of the factor traces
(`groupTwirlProjector_prod_trace`) rewritten via `Finset.sum_mul_sum`. -/
theorem groupTwirlProjector_prod_trace_sumSq {G_A G_B : Type*} [Group G_A] [Group G_B]
    [Fintype G_A] [Fintype G_B] {dA dB kA kB : ℕ} [NeZero dA] [NeZero dB]
    (πA : G_A → Op dA) (hπA : IsUnitaryRep πA) (πB : G_B → Op dB) (hπB : IsUnitaryRep πB)
    (mA : Fin kA → ℕ) (mB : Fin kB → ℕ)
    (hxA : (groupTwirlProjector πA).trace = ∑ i : Fin kA, (((mA i : ℕ) : ℂ) ^ 2))
    (hxB : (groupTwirlProjector πB).trace = ∑ j : Fin kB, (((mB j : ℕ) : ℂ) ^ 2)) :
    (groupTwirlProjector (prodRep πA πB)).trace =
      ∑ i : Fin kA, ∑ j : Fin kB, (((mA i : ℕ) : ℂ) ^ 2 * ((mB j : ℕ) : ℂ) ^ 2) := by
  rw [groupTwirlProjector_prod_trace πA hπA πB hπB, hxA, hxB, Finset.sum_mul_sum]

end InfoTheory.Postselection

end
