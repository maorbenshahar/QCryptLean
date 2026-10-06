import QCryptLean.InfoTheory.Postselection.SchurWeylCommutantAssembly

/-!
# QKD postselection — Schur–Weyl argument: the Schur–Weyl twirl-flattening

Nahar, Tupkary, Zhao, Lütkenhaus, Tan Lemma 10. Closes
`InfoTheory.Postselection.exists_flatten_maxEntangledUnitaryTwirl` (stated in
`SchurWeylTwirl.lean`, moved here because its proof needs the Ω-layer (`SchurWeylKappa.lean`),
the twirl-projection layer (`SchurWeylTwirlProjection.lean`), and the E2 commutant assembly
(`SchurWeylCommutantAssembly.lean`), all downstream of `SchurWeylTwirl.lean` in the import
order, so the theorem cannot be proved in the file where it is declared).

## The assembly (duality-free route)

Set `κ := Ω⁻¹` where `Ω := symmetricProjectorPairedTraceR dA dR n = Tr_Rⁿ(P_Sym)` (`Ω` is
`PosDef`, hence invertible, exactly when `dA ≤ dR`, `symmetricProjectorPairedTraceR_posDef`).
Write `Θₙ := maxEntangledProjectorPaired dA dR n hdim` and `Tₙ := maxEntangledUnitaryTwirl dA dR
n hdim = twirlMap dA dR n Θₙ`.

**Key elementary fact (no Schur–Weyl duality needed):** for *any* `X : Op (dA^n)` and
`π : Equiv.Perm (Fin n)`, the generator `X ⊗ P_R(π)` commutes with every Kraus operator
`1_{Aⁿ} ⊗ U^{⊗n}` (`U` unitary on `Rⁿ`) — because `U^{⊗n}` commutes with `P_R(π)` termwise
(permuting `n` tensor legs commutes with applying the same operator to every leg, the "easy
direction" of Schur–Weyl, pure tensor algebra). Hence:

1. `(κ ⊗ 1) * P_Sym` is itself a sum of such generators, so it is a `twirlMap`-fixed point:
   `twirlMap dA dR n ((κ⊗1)*P_Sym) = (κ⊗1)*P_Sym`.
2. `Tₙ` is a `twirlMap`-fixed point too (`twirlMap_idempotent`, applied to `Θₙ`).
3. `D := Tₙ - (κ⊗1)*P_Sym` therefore commutes with every Kraus operator, hence (E2 §1b,
   `commutant_pairedUnitaryTensorPow_eq_tensorPermSpan`) lies in the span of the generators
   `{X ⊗ P_R(π)}`.
4. For *every* generator `S = X ⊗ P_R(π)`, `Tr[Sᴴ * D] = 0`: `S` is itself a `twirlMap`-fixed
   point, so by self-adjointness (`twirlMap_selfAdjoint`) `Tr[Sᴴ * Tₙ] = Tr[Sᴴ * Θₙ]`; the RHS
   (and the analogous `(κ⊗1)*P_Sym` pairing) both reduce, via the ricochet identity
   (`ricochet_permutationRepresentation_thetaKet`) and Identity 2
   (`thetaKet_tensor_one_bilinear`), to `Tr[X' * P_A(π'⁻¹)]` for suitable `X', π'` — matching
   exactly when `κΩ = 1` (`Matrix.nonsing_inv_mul`), i.e. `κ = Ω⁻¹`.
5. Since `D` lies in the span (step 3) and pairs to zero against every generator (step 4), it
   pairs to zero against itself (`Submodule.span_induction`), i.e. `Tr[Dᴴ D] = 0`, forcing
   `D = 0` (`Matrix.trace_conjTranspose_mul_self_eq_zero_iff`). Hence `Tₙ = (κ⊗1)*P_Sym`.

`κ`'s positivity/invertibility come directly from `Ω`'s (`Matrix.PosDef.inv`,
`Matrix.PosDef.isUnit`); the `Commute (κ⊗1) P_Sym` conjunct comes from `Ω`'s `Sₙ`-centrality
(`symmetricProjectorPairedTraceR_commute`) lifted to `κ = Ω⁻¹` (a unit commuting with `Ω`
commutes with `Ω⁻¹` too), then through `Op.tensor_mul` against the `Σ_π P_A(π)⊗P_R(π)` expansion
of `P_Sym`.
-/

open Quantum.Symmetry

open Quantum.Operators Quantum.TensorProducts Matrix Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

noncomputable section

namespace InfoTheory.Postselection

/-! ## Small elementary helpers -/

/-- Any generator `X ⊗ P_R(π)` commutes with every Kraus operator `1_{Aⁿ} ⊗ U^{⊗n}`
(`U : Op dR` arbitrary): a tensor power commutes with the permutations of its copies
(`Op.commute_tensorPow_permutationRepresentation`, the "easy direction" of Schur–Weyl), lifted
across the disjoint `A`/`R` factors. -/
private lemma tensorGenerator_commute_kraus (dA dR n : ℕ) [NeZero dA] [NeZero dR] [NeZero n]
    (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)) (U : Op dR) :
    Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow U n))
      (Op.tensor X (permutationRepresentation dR n π)) := by
  unfold Commute SemiconjBy
  simp only [Op.tensor_mul, one_mul, mul_one]
  exact congrArg (Op.tensor X) (Op.commute_tensorPow_permutationRepresentation U π)

/-- **Step 7 assembly.** `⟨θ|(X⊗P_R(π))|θ⟩ = Tr[X·P_A(π⁻¹)]`: factor `X⊗P_R(π)` as
`(X⊗1)·(1⊗P_R(π))`, ricochet the `R`-side permutation across `θ` into an `A`-side
`P_A(π⁻¹)` (`ricochet_permutationRepresentation_thetaKet`), then apply Identity 2
(`thetaKet_tensor_one_bilinear`). -/
private lemma thetaKet_tensor_permRep_bilinear (dA dR n : ℕ) [NeZero dA] [NeZero dR]
    (hdim : dA ≤ dR) (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)) :
    dotProduct (star (thetaKet dA dR n hdim))
        ((Op.tensor X (permutationRepresentation dR n π)).mulVec (thetaKet dA dR n hdim))
      = (X * permutationRepresentation dA n π⁻¹).trace := by
  have hfactor : Op.tensor X (permutationRepresentation dR n π) =
      Op.tensor X (1 : Op (dR ^ n)) *
        Op.tensor (1 : Op (dA ^ n)) (permutationRepresentation dR n π) := by
    rw [Op.tensor_mul, mul_one, one_mul]
  rw [hfactor, ← Matrix.mulVec_mulVec, ricochet_permutationRepresentation_thetaKet,
    Matrix.mulVec_mulVec, Op.tensor_mul, mul_one]
  exact thetaKet_tensor_one_bilinear dA dR n hdim _

/-- The trace of `(ketbra Θ) * S` is the quadratic form `⟨Θ|S|Θ⟩` — a purely algebraic
rearrangement of the double sum, independent of what `Θ` is. -/
private lemma ketbra_mul_trace_eq_dotProduct {N : ℕ} (Θ : Fin N → ℂ) (S : Op N) :
    ((Matrix.of (fun i j => Θ i * (starRingEnd ℂ) (Θ j))) * S).trace
      = dotProduct (star Θ) (S.mulVec Θ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `Θₙ = maxEntangledProjectorPaired` is literally the ket-bra of `thetaKet` (both defined by
the same digit-wise indicator formula). -/
private lemma maxEntangledProjectorPaired_eq_thetaKet_of (dA dR n : ℕ) (hdim : dA ≤ dR) :
    maxEntangledProjectorPaired dA dR n hdim
      = Matrix.of (fun i j =>
          thetaKet dA dR n hdim i * (starRingEnd ℂ) (thetaKet dA dR n hdim j)) := rfl

/-- **The `Θₙ`-generator pairing.** `Tr[(X⊗P_R(π)) * Θₙ] = Tr[X·P_A(π⁻¹)]`. -/
private lemma theta_generator_trace_pairing (dA dR n : ℕ) [NeZero dA] [NeZero dR]
    (hdim : dA ≤ dR) (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)) :
    (Op.tensor X (permutationRepresentation dR n π) *
        maxEntangledProjectorPaired dA dR n hdim).trace
      = (X * permutationRepresentation dA n π⁻¹).trace := by
  rw [Matrix.trace_mul_comm, maxEntangledProjectorPaired_eq_thetaKet_of,
    ketbra_mul_trace_eq_dotProduct, thetaKet_tensor_permRep_bilinear]

/-! ## The Ω-layer: `κ := Ω⁻¹` -/

/-- A matrix commuting with a matrix invertible by nonsingular inverse also commutes with its
inverse (standard: sandwich the commutation identity by `B⁻¹` on both sides). -/
private lemma commute_nonsing_inv_right {N : ℕ} {A B : Op N} (hAB : Commute A B)
    (hdet : IsUnit B.det) : Commute A B⁻¹ := by
  have h1 : B⁻¹ * (A * B) * B⁻¹ = B⁻¹ * (B * A) * B⁻¹ := by rw [hAB]
  rw [show B⁻¹ * (A * B) * B⁻¹ = (B⁻¹ * A) * (B * B⁻¹) from by noncomm_ring,
      Matrix.mul_nonsing_inv B hdet, Matrix.mul_one,
      show B⁻¹ * (B * A) * B⁻¹ = (B⁻¹ * B) * (A * B⁻¹) from by noncomm_ring,
      Matrix.nonsing_inv_mul B hdet, Matrix.one_mul] at h1
  exact h1.symm

variable {dA dR n : ℕ}

/-- `Ω.det` is a unit (`Ω` is `PosDef`, hence invertible as a matrix). -/
private lemma omega_det_isUnit [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    IsUnit (symmetricProjectorPairedTraceR dA dR n).det :=
  Matrix.isUnit_iff_isUnit_det _ |>.mp
    (Matrix.PosDef.isUnit (symmetricProjectorPairedTraceR_posDef dA dR n hdim))

/-- **`κ := Ω⁻¹`.** -/
private noncomputable def kappa (dA dR n : ℕ) [NeZero dA] [NeZero dR] [NeZero n] : Op (dA ^ n) :=
  (symmetricProjectorPairedTraceR dA dR n)⁻¹

private lemma kappa_posSemidef [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    (kappa dA dR n).PosSemidef :=
  (Matrix.PosDef.inv (symmetricProjectorPairedTraceR_posDef dA dR n hdim)).posSemidef

private lemma kappa_isUnit [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    IsUnit (kappa dA dR n) :=
  (Matrix.PosDef.inv (symmetricProjectorPairedTraceR_posDef dA dR n hdim)).isUnit

/-- **`κΩ = 1`.** -/
private lemma kappa_mul_omega [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    kappa dA dR n * symmetricProjectorPairedTraceR dA dR n = 1 :=
  Matrix.nonsing_inv_mul _ (omega_det_isUnit hdim)

/-- **`κ` is `Sₙ`-central**, lifted from `Ω`'s centrality
(`symmetricProjectorPairedTraceR_commute`). -/
private lemma kappa_commute [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR)
    (τ : Equiv.Perm (Fin n)) :
    Commute (permutationRepresentation dA n τ) (kappa dA dR n) :=
  commute_nonsing_inv_right (symmetricProjectorPairedTraceR_commute dA dR n τ)
    (omega_det_isUnit hdim)

/-- **The `Commute` conjunct.** `κ⊗1` commutes with `P_Sym`: termwise from `κ`'s
`Sₙ`-centrality against the `Σ_σ P_A(σ)⊗P_R(σ)` expansion of `P_Sym`. -/
private lemma kappa_tensor_commute [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    Commute (Op.tensor (kappa dA dR n) (1 : Op (dR ^ n)))
      (symmetricProjectorPairedGen dA dR n) := by
  unfold Commute SemiconjBy symmetricProjectorPairedGen
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  -- termwise: `(κ ⊗ 1)(P_A(σ) ⊗ P_R(σ)) = (P_A(σ) ⊗ P_R(σ))(κ ⊗ 1)`, i.e. `κ P_A(σ) = P_A(σ) κ`
  refine congrArg ((1 / (Nat.factorial n : ℂ)) • ·) (Finset.sum_congr rfl fun σ _ => ?_)
  rw [Op.tensor_mul, Op.tensor_mul, one_mul, mul_one, (kappa_commute hdim σ).eq]

/-- **The `(κ⊗1)*P_Sym`-generator pairing.** `Tr[(X⊗P_R(π)) * (κ⊗1) * P_Sym] = Tr[X·P_A(π⁻¹)]`
— the computation that pins `κ := Ω⁻¹` exactly. -/
private lemma kappa_generator_trace_pairing [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR)
    (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)) :
    (Op.tensor X (permutationRepresentation dR n π) *
        (Op.tensor (kappa dA dR n) (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n)).trace
      = (X * permutationRepresentation dA n π⁻¹).trace := by
  set κ := kappa dA dR n with hκ
  have hstep1 : Op.tensor X (permutationRepresentation dR n π) * Op.tensor κ (1 : Op (dR ^ n))
      = Op.tensor (X * κ) (permutationRepresentation dR n π) := by
    rw [Op.tensor_mul, mul_one]
  have hexpand :
      Op.tensor X (permutationRepresentation dR n π) *
        (Op.tensor κ (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n)
      = (1 / (Nat.factorial n : ℂ)) • ∑ σ : Equiv.Perm (Fin n),
          Op.tensor (X * κ * permutationRepresentation dA n σ)
            (permutationRepresentation dR n (π * σ)) := by
    rw [← Matrix.mul_assoc, hstep1]
    unfold symmetricProjectorPairedGen
    rw [Matrix.mul_smul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    rw [Op.tensor_mul, permutationRepresentation_mul]
  rw [hexpand, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  simp_rw [Op.trace_tensor]
  have hreindex : ∑ σ : Equiv.Perm (Fin n),
        (X * κ * permutationRepresentation dA n σ).trace *
          (permutationRepresentation dR n (π * σ)).trace
      = ∑ ρ : Equiv.Perm (Fin n),
        (X * κ * permutationRepresentation dA n (π⁻¹ * ρ)).trace *
          (permutationRepresentation dR n ρ).trace := by
    apply Fintype.sum_bijective (π * ·) (Group.mulLeft_bijective π)
    intro σ
    rw [inv_mul_cancel_left]
  rw [hreindex]
  have hM : ∀ ρ : Equiv.Perm (Fin n),
      X * κ * permutationRepresentation dA n (π⁻¹ * ρ)
        = (X * κ * permutationRepresentation dA n π⁻¹) * permutationRepresentation dA n ρ := by
    intro ρ
    rw [← permutationRepresentation_mul, ← mul_assoc]
  simp_rw [hM]
  have hsum_eq : ∑ ρ : Equiv.Perm (Fin n),
        ((X * κ * permutationRepresentation dA n π⁻¹) *
            permutationRepresentation dA n ρ).trace *
          (permutationRepresentation dR n ρ).trace
      = ((X * κ * permutationRepresentation dA n π⁻¹) *
          ∑ ρ : Equiv.Perm (Fin n),
            (permutationRepresentation dR n ρ).trace • permutationRepresentation dA n ρ).trace := by
    rw [Finset.mul_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_comm]
  rw [hsum_eq]
  have hΩsum : (∑ ρ : Equiv.Perm (Fin n),
        (permutationRepresentation dR n ρ).trace • permutationRepresentation dA n ρ)
      = (Nat.factorial n : ℂ) • symmetricProjectorPairedTraceR dA dR n := by
    rw [symmetricProjectorPairedTraceR_eq_traceWeightedSum, smul_smul,
      show (Nat.factorial n : ℂ) * (1 / (Nat.factorial n : ℂ)) = 1 by
        field_simp, one_smul]
  rw [hΩsum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
    show (1 / (Nat.factorial n : ℂ)) * (Nat.factorial n : ℂ) = 1 by field_simp, one_mul,
    Matrix.mul_assoc, Matrix.mul_assoc,
    show κ * (permutationRepresentation dA n π⁻¹ * symmetricProjectorPairedTraceR dA dR n) =
        permutationRepresentation dA n π⁻¹ * (κ * symmetricProjectorPairedTraceR dA dR n) from by
      rw [← Matrix.mul_assoc, ← (kappa_commute hdim π⁻¹), Matrix.mul_assoc],
    kappa_mul_omega hdim, Matrix.mul_one]

/-! ## `twirlMap`-fixed points -/

/-- Any generator `X ⊗ P_R(π)` is a `twirlMap`-fixed point (elementary tensor commutation,
`tensorGenerator_commute_kraus`). -/
private lemma tensorGenerator_fixed [NeZero dA] [NeZero dR] [NeZero n]
    (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)) :
    twirlMap dA dR n (Op.tensor X (permutationRepresentation dR n π))
      = Op.tensor X (permutationRepresentation dR n π) :=
  (twirlMap_eq_iff_commute dA dR n _).mpr
    (fun U => tensorGenerator_commute_kraus dA dR n X π (U : Op dR))

/-- `κ⊗1` trivially commutes with every Kraus operator (disjoint tensor factors). -/
private lemma kraus_commute_kappaTensorOne [NeZero dA] [NeZero dR] [NeZero n] (U : Op dR) :
    Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow U n))
      (Op.tensor (kappa dA dR n) (1 : Op (dR ^ n))) := by
  unfold Commute SemiconjBy
  simp only [Op.tensor_mul, one_mul, mul_one]

/-- `P_Sym` commutes with every Kraus operator (termwise, `tensorGenerator_commute_kraus` with
`X := P_A(σ)`). -/
private lemma kraus_commute_symProj [NeZero dA] [NeZero dR] [NeZero n] (U : Op dR) :
    Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow U n))
      (symmetricProjectorPairedGen dA dR n) := by
  unfold Commute SemiconjBy symmetricProjectorPairedGen
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  -- termwise: each generator `P_A(σ) ⊗ P_R(σ)` commutes with the Kraus operator
  refine congrArg ((1 / (Nat.factorial n : ℂ)) • ·) (Finset.sum_congr rfl fun σ _ => ?_)
  exact tensorGenerator_commute_kraus dA dR n (permutationRepresentation dA n σ) σ U

/-- `Tₙ = twirlMap Θₙ` is itself a `twirlMap`-fixed point (idempotence). -/
private lemma T_fixed [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    twirlMap dA dR n (maxEntangledUnitaryTwirl dA dR n hdim)
      = maxEntangledUnitaryTwirl dA dR n hdim := by
  rw [twirlMap_maxEntangledProjectorPaired dA dR n hdim]
  exact twirlMap_idempotent dA dR n _

/-- The conjugate transpose of a generator is again a generator. -/
private lemma tensorGenerator_conjTranspose [NeZero dA] [NeZero dR] [NeZero n]
    (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)) :
    (Op.tensor X (permutationRepresentation dR n π))ᴴ
      = Op.tensor Xᴴ (permutationRepresentation dR n π⁻¹) := by
  rw [Op.tensor_conjTranspose, ← permutationRepresentation_inv]

/-- **The generator/dagger pairing.** For every generator `X⊗P_R(π)`,
`Tr[(X⊗P_R(π))ᴴ · Tₙ] = Tr[(X⊗P_R(π))ᴴ · (κ⊗1)·P_Sym]`: `X⊗P_R(π)` is itself a `twirlMap`
fixed point, so self-adjointness (`twirlMap_selfAdjoint`) reduces the `Tₙ`-pairing to the
`Θₙ`-pairing (`theta_generator_trace_pairing`), which matches the `(κ⊗1)·P_Sym`-pairing
(`kappa_generator_trace_pairing`) exactly. -/
private lemma generator_conjTranspose_pairing_eq [NeZero dA] [NeZero dR] [NeZero n]
    (hdim : dA ≤ dR) (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)) :
    ((Op.tensor X (permutationRepresentation dR n π))ᴴ *
        maxEntangledUnitaryTwirl dA dR n hdim).trace
      = ((Op.tensor X (permutationRepresentation dR n π))ᴴ *
          (Op.tensor (kappa dA dR n) (1 : Op (dR ^ n)) *
            symmetricProjectorPairedGen dA dR n)).trace := by
  have hSfixed : twirlMap dA dR n (Op.tensor X (permutationRepresentation dR n π))
      = Op.tensor X (permutationRepresentation dR n π) := tensorGenerator_fixed X π
  have hSadj := twirlMap_selfAdjoint dA dR n (Op.tensor X (permutationRepresentation dR n π))
    (maxEntangledProjectorPaired dA dR n hdim)
  rw [hSfixed, ← twirlMap_maxEntangledProjectorPaired dA dR n hdim] at hSadj
  rw [← hSadj, tensorGenerator_conjTranspose,
    theta_generator_trace_pairing dA dR n hdim Xᴴ π⁻¹,
    kappa_generator_trace_pairing hdim Xᴴ π⁻¹]

/-! ## Final assembly: `D := Tₙ - (κ⊗1)·P_Sym = 0` -/

/-- `D` pairs to zero against every generator `X⊗P_R(π)`. -/
private lemma generator_conjTranspose_pairing_D_zero [NeZero dA] [NeZero dR] [NeZero n]
    (hdim : dA ≤ dR) (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)) :
    ((Op.tensor X (permutationRepresentation dR n π))ᴴ *
      (maxEntangledUnitaryTwirl dA dR n hdim -
        Op.tensor (kappa dA dR n) (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n)).trace
      = 0 := by
  rw [Matrix.mul_sub, Matrix.trace_sub, generator_conjTranspose_pairing_eq hdim X π, sub_self]

/-- `D` commutes with every Kraus operator (difference of two `twirlMap`-fixed points). -/
private lemma D_commute_kraus [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR)
    (U : Matrix.unitaryGroup (Fin dR) ℂ) :
    Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))
      (maxEntangledUnitaryTwirl dA dR n hdim -
        Op.tensor (kappa dA dR n) (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n) := by
  have h1 : Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n))
      (maxEntangledUnitaryTwirl dA dR n hdim) :=
    (twirlMap_eq_iff_commute dA dR n _).mp (T_fixed hdim) U
  exact h1.sub_right ((kraus_commute_kappaTensorOne (U : Op dR)).mul_right
    (kraus_commute_symProj (U : Op dR)))

/-- `D` lies in the span of the generators `{X⊗P_R(π)}` (E2 §1b,
`commutant_pairedUnitaryTensorPow_eq_tensorPermSpan`). -/
private lemma D_mem_span [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    (maxEntangledUnitaryTwirl dA dR n hdim -
        Op.tensor (kappa dA dR n) (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n) ∈
      Submodule.span ℂ
        (Set.ofPred fun T : Op (dA ^ n * dR ^ n) => ∃ (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)),
          T = Op.tensor X (permutationRepresentation dR n π)) := by
  have hcomm : (maxEntangledUnitaryTwirl dA dR n hdim -
      Op.tensor (kappa dA dR n) (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n) ∈
      (Set.ofPred fun T : Op (dA ^ n * dR ^ n) => ∀ U : Matrix.unitaryGroup (Fin dR) ℂ,
        Commute (Op.tensor (1 : Op (dA ^ n)) (Op.tensorPow (U : Op dR) n)) T) :=
    fun U => D_commute_kraus hdim U
  rw [commutant_pairedUnitaryTensorPow_eq_tensorPermSpan] at hcomm
  exact hcomm

/-- The zero-pairing against generators extends, by linearity, to every element of their
span — in particular to `D` itself, giving `Tr[Dᴴ D] = 0`. -/
private lemma trace_conjTranspose_mul_D_eq_zero_of_mem_span [NeZero dA] [NeZero dR] [NeZero n]
    (hdim : dA ≤ dR) (S : Op (dA ^ n * dR ^ n))
    (hS : S ∈ Submodule.span ℂ
        (Set.ofPred fun T : Op (dA ^ n * dR ^ n) => ∃ (X : Op (dA ^ n)) (π : Equiv.Perm (Fin n)),
          T = Op.tensor X (permutationRepresentation dR n π))) :
    (Sᴴ * (maxEntangledUnitaryTwirl dA dR n hdim -
        Op.tensor (kappa dA dR n) (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n)).trace
      = 0 := by
  induction hS using Submodule.span_induction with
  | mem S' hS' =>
      obtain ⟨X, π, rfl⟩ := hS'
      exact generator_conjTranspose_pairing_D_zero hdim X π
  | zero => simp
  | add S1 S2 _ _ h1 h2 =>
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add, h1, h2, add_zero]
  | smul c S' _ h =>
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul, h, smul_zero]

/-- **SP1 = Nahar et al. Lemma 10, assembled.** `κ := Ω⁻¹` flattens the Haar twirl `Tₙ` to
`(κ⊗1)·P_Sym`. -/
theorem exists_flatten_maxEntangledUnitaryTwirl
    (dA dR n : ℕ) [NeZero dA] [NeZero dR] [NeZero n] (hdim : dA ≤ dR) :
    ∃ κ : Op (dA ^ n),
      κ.PosSemidef ∧
      IsUnit κ ∧
      Commute (Op.tensor κ (1 : Op (dR ^ n))) (symmetricProjectorPairedGen dA dR n) ∧
      maxEntangledUnitaryTwirl dA dR n hdim
        = Op.tensor κ (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n := by
  refine ⟨kappa dA dR n, kappa_posSemidef hdim, kappa_isUnit hdim, kappa_tensor_commute hdim, ?_⟩
  have hzero : ((maxEntangledUnitaryTwirl dA dR n hdim -
        Op.tensor (kappa dA dR n) (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n)ᴴ *
      (maxEntangledUnitaryTwirl dA dR n hdim -
        Op.tensor (kappa dA dR n) (1 : Op (dR ^ n)) * symmetricProjectorPairedGen dA dR n)).trace
      = 0 :=
    trace_conjTranspose_mul_D_eq_zero_of_mem_span hdim _ (D_mem_span hdim)
  have hD0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hzero
  exact sub_eq_zero.mp hD0

end InfoTheory.Postselection

end
