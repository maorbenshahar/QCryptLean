import QCryptLean.Math.CodingTheory.CSS.ErrorModel
import QCryptLean.Quantum.TensorProducts.PSDOrder

/-!
# CSS Code Structure — syndrome decoding, error correction, minimum weight representatives

CSS (Calderbank-Shor-Steane) quantum error-correcting code structure: syndrome computation,
coset representatives, minimum weight decoding, and the main error correction theorem.

## Main definitions
- `CSSCode`: CSS code from nested classical codes C₁ ⊇ C₂
- `CSSCode.Syndrome`: syndrome type for error detection
- `CSSCode.InCodeSpace`: code space membership predicate
- `CSSCode.minWeightCorrection`: minimum weight correction operator

## Main statements
- `CSSCode.corrects_errors`: CSS codes correct t errors when 2t+1 ≤ distance
- `PauliError.equiv_act_same`: equivalent errors act identically on code space
-/

open Quantum.Operators Quantum.TensorProducts Math.CodingTheory

noncomputable section

namespace Math.CodingTheory.CSS

/-- CSS code constructed from C₁ ⊇ C₂ -/
structure CSSCode (n : ℕ) where
  k1 : ℕ
  k2 : ℕ
  C1 : LinearCode n k1
  C2 : LinearCode n k2
  C2_subset_C1 : C2.codewords ⊆ C1.codewords
  k2_le_k1 : k2 ≤ k1

/-- Number of logical qubits encoded by a CSS code -/
def CSSCode.numLogicalQubits {n : ℕ} (code : CSSCode n) : ℕ :=
  code.k1 - code.k2

/-!
## Distance Properties
-/

/-- Bit flip distance: minimum weight of nontrivial logical X operators.
    These are nonzero vectors in C₁ \ C₂ (codewords of C₁ not in the stabilizer code C₂).
    Since C₂ ⊆ C₁, this measures how far apart distinct logical X coset representatives are. -/
noncomputable def CSSCode.bitFlipDistance {n : ℕ} (code : CSSCode n) : ℕ :=
  sInf (hammingWeight '' { v | v ∈ code.C1.codewords ∧ v ∉ code.C2.codewords })

/-- Phase flip correction capability: minimum weight of nontrivial logical Z operators.
    These are vectors in C₂⊥ \ C₁⊥ (dual of C₂ but not stabilizers from C₁⊥).
    Since C₂ ⊆ C₁ implies C₁⊥ ⊆ C₂⊥, this is the minimum weight of
    coset representatives of C₂⊥/C₁⊥. -/
noncomputable def CSSCode.phaseFlipDistance {n : ℕ} (code : CSSCode n) : ℕ :=
  sInf (hammingWeight '' { v | v ∈ code.C2.dual ∧ v ∉ code.C1.dual })

/-- CSS code distance is minimum of bit and phase flip distances -/
def CSSCode.distance {n : ℕ} (code : CSSCode n) : ℕ :=
  min code.bitFlipDistance code.phaseFlipDistance

/-!
## Syndromes

For CSS codes, error correction is based on syndrome measurement:
- X syndrome: detects bit flip errors via inner products with C₁⊥
- Z syndrome: detects phase flip errors via inner products with C₂

Two errors have the same syndrome iff they differ by an element of the
appropriate code (C₁ for X errors, C₂⊥ for Z errors).
-/

/-- Inner product over F₂ -/
def innerProductF2 {n : ℕ} (v w : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, v i * w i

/-- X syndrome: the function v ↦ ⟨e, v⟩ for v ∈ C₁⊥.
    Two X error patterns have the same syndrome iff they differ by an element of C₁.
    Abstractly, the X syndrome identifies the coset e + C₁ in F₂ⁿ/C₁. -/
def PauliError.xSyndromeFunc {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    code.C1.dual → ZMod 2 :=
  fun ⟨v, _⟩ => innerProductF2 e.xPattern v

/-- Z syndrome: the function w ↦ ⟨f, w⟩ for w ∈ C₂.
    Two Z error patterns have the same syndrome iff they differ by an element of C₂⊥.
    Abstractly, the Z syndrome identifies the coset f + C₂⊥ in F₂ⁿ/C₂⊥. -/
def PauliError.zSyndromeFunc {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    code.C2.codewords → ZMod 2 :=
  fun ⟨w, _⟩ => innerProductF2 e.zPattern w

/-- Two X error patterns have the same syndrome iff they differ by a codeword in C₁ -/
def PauliError.SameXSyndrome {n : ℕ} (code : CSSCode n)
    (e₁ e₂ : PauliError n) : Prop :=
  (e₁.xPattern - e₂.xPattern) ∈ code.C1.codewords

/-- Two Z error patterns have the same syndrome iff they differ by an element of C₂⊥ -/
def PauliError.SameZSyndrome {n : ℕ} (code : CSSCode n)
    (e₁ e₂ : PauliError n) : Prop :=
  (e₁.zPattern - e₂.zPattern) ∈ code.C2.dual

/-- **Syndrome Type for CSS Codes**

    The syndrome of a Pauli error captures which coset it belongs to.
    Two errors have the same syndrome iff their syndrome functions are equal.

    The X syndrome is a function C₁⊥ → ZMod 2 (testing against dual codewords)
    The Z syndrome is a function C₂ → ZMod 2 (testing against codewords)

    Key property: errors with equal syndromes get the same correction,
    since correction is defined as a function of the syndrome directly. -/
@[ext]
structure CSSCode.Syndrome {n : ℕ} (code : CSSCode n) where
  xSyn : code.C1.dual → ZMod 2
  zSyn : code.C2.codewords → ZMod 2

/-- Extract the syndrome of a Pauli error -/
def PauliError.syndrome {n : ℕ} (code : CSSCode n) (e : PauliError n) : code.Syndrome :=
  ⟨e.xSyndromeFunc code, e.zSyndromeFunc code⟩

/-- Two errors have equal syndromes iff they satisfy SameXSyndrome and SameZSyndrome -/
theorem PauliError.syndrome_eq_iff {n : ℕ} (code : CSSCode n) (e₁ e₂ : PauliError n) :
    e₁.syndrome code = e₂.syndrome code ↔
    (e₁.SameXSyndrome code e₂ ∧ e₁.SameZSyndrome code e₂) := by
  constructor
  · -- Same syndrome functions → same coset membership
    intro heq
    constructor
    · -- X syndrome: show e₁.x - e₂.x ∈ C₁
      -- Same X syndrome function means ⟨e₁.x, v⟩ = ⟨e₂.x, v⟩ for all v ∈ C₁⊥
      -- This means ⟨e₁.x - e₂.x, v⟩ = 0 for all v ∈ C₁⊥
      -- By duality (C₁⊥⊥ = C₁ for linear codes), this means e₁.x - e₂.x ∈ C₁
      unfold SameXSyndrome
      -- The syndrome functions being equal means they agree on all inputs
      have hfun : e₁.xSyndromeFunc code = e₂.xSyndromeFunc code := by
        have h := congrArg CSSCode.Syndrome.xSyn heq
        exact h
      -- This means the difference is orthogonal to all of C₁⊥
      -- By double dual theorem: d ∈ C iff d ⊥ C⊥
      rw [LinearCode.mem_codewords_iff_orthogonal_to_dual]
      intro v hv
      -- hfun says the syndrome functions are equal, so they agree on v
      have heq : xSyndromeFunc code e₁ ⟨v, hv⟩ = xSyndromeFunc code e₂ ⟨v, hv⟩ :=
        congrFun hfun ⟨v, hv⟩
      unfold xSyndromeFunc innerProductF2 at heq
      -- heq : ∑ i, e₁.xPattern i * v i = ∑ i, e₂.xPattern i * v i
      -- Goal: ∑ i, (e₁.xPattern - e₂.xPattern) i * v i = 0
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr heq
    · -- Z syndrome: show e₁.z - e₂.z ∈ C₂⊥
      unfold SameZSyndrome
      have hfun : e₁.zSyndromeFunc code = e₂.zSyndromeFunc code := by
        have h := congrArg CSSCode.Syndrome.zSyn heq
        exact h
      -- Same argument: diff is orthogonal to C₂, so diff ∈ C₂⊥
      -- By definition of dual: v ∈ C⊥ iff ∀ c ∈ C.codewords, ⟨v, c⟩ = 0
      rw [LinearCode.dual]
      simp only [Set.mem_setOf_eq]
      intro c hc
      -- hfun says the syndrome functions are equal, so they agree on c
      have heq : zSyndromeFunc code e₁ ⟨c, hc⟩ = zSyndromeFunc code e₂ ⟨c, hc⟩ :=
        congrFun hfun ⟨c, hc⟩
      unfold zSyndromeFunc innerProductF2 at heq
      -- heq : ∑ i, e₁.zPattern i * c i = ∑ i, e₂.zPattern i * c i
      -- Goal: ∑ i, (e₁.zPattern - e₂.zPattern) i * c i = 0
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr heq
  · -- Same coset membership → same syndrome functions
    intro ⟨hx, hz⟩
    unfold syndrome xSyndromeFunc zSyndromeFunc
    ext
    · -- X syndrome function equality
      rename_i x
      obtain ⟨v, hv⟩ := x
      simp only
      unfold innerProductF2
      -- e₁.x - e₂.x ∈ C₁ and v ∈ C₁⊥, so ⟨v, e₁.x - e₂.x⟩ = 0
      have hdiff : e₁.xPattern - e₂.xPattern ∈ code.C1.codewords := hx
      have horth : v ∈ code.C1.dual := hv
      -- By definition of dual: ⟨v, c⟩ = 0 for all c ∈ C₁
      have hinner : ∑ i, v i * (e₁.xPattern - e₂.xPattern) i = 0 :=
        horth (e₁.xPattern - e₂.xPattern) hdiff
      -- Expand and distribute
      simp only [Pi.sub_apply, mul_sub] at hinner
      rw [Finset.sum_sub_distrib] at hinner
      -- Commutativity: e.x * v = v * e.x
      have hcomm₁ : ∑ i, e₁.xPattern i * v i = ∑ i, v i * e₁.xPattern i := by
        congr 1; ext i; ring
      have hcomm₂ : ∑ i, e₂.xPattern i * v i = ∑ i, v i * e₂.xPattern i := by
        congr 1; ext i; ring
      rw [hcomm₁, hcomm₂]
      -- hinner says ∑(v * e₁.x) - ∑(v * e₂.x) = 0, so they're equal
      exact sub_eq_zero.mp hinner
    · -- Z syndrome function equality
      rename_i x
      obtain ⟨w, hw⟩ := x
      simp only
      unfold innerProductF2
      have hdiff : e₁.zPattern - e₂.zPattern ∈ code.C2.dual := hz
      -- By definition of dual: ⟨diff, w⟩ = 0 for all w ∈ C₂
      have hinner : ∑ i, (e₁.zPattern - e₂.zPattern) i * w i = 0 :=
        hdiff w hw
      simp only [Pi.sub_apply, sub_mul] at hinner
      rw [Finset.sum_sub_distrib] at hinner
      exact sub_eq_zero.mp hinner

/-!
## Code Space

CSS code states are superpositions over cosets of C₂ in C₁:
  |c + C₂⟩ = (1/√|C₂|) Σ_{w∈C₂} |c + w⟩
for coset representatives c ∈ C₁/C₂.

The code space is the span of these coset states.
-/

/-- Predicate: a ket is in the CSS code space.
    A state is in the code space iff it is stabilized by all X-type stabilizers
    (X^w for w ∈ C₂) and all Z-type stabilizers (Z^v for v ∈ C₁⊥).

    **PauliError structure**: ⟨xPattern, zPattern⟩ where:
    - X^w operator has xPattern = w, zPattern = 0
    - Z^v operator has xPattern = 0, zPattern = v -/
def CSSCode.InCodeSpace {n : ℕ} (code : CSSCode n) (ψ : Ket (2 ^ n)) : Prop :=
  -- X stabilizers: X^w |ψ⟩ = |ψ⟩ for all w ∈ C₂
  -- X^w has xPattern = w and zPattern = 0
  (∀ w, w ∈ code.C2.codewords →
    (⟨w, fun _ => 0⟩ : PauliError n).toOp * ψ = ψ) ∧
  -- Z stabilizers: Z^v |ψ⟩ = |ψ⟩ for all v ∈ C₁⊥
  -- Z^v has xPattern = 0 and zPattern = v
  (∀ v, v ∈ code.C1.dual →
    (⟨fun _ => 0, v⟩ : PauliError n).toOp * ψ = ψ)

/-!
## Symplectic Inner Product and Pauli Commutation

The Pauli group has the commutation relation: (X^a Z^b)(X^c Z^d) = (-1)^{bc} X^{a+c} Z^{b+d}.
For n-qubit Paulis, the phase is (-1)^{⟨b,c⟩} where ⟨·,·⟩ is the inner product over F₂.
-/

/-- Inner product over F₂ (counts positions where both are 1, mod 2).

    **Note on naming**: This computes the standard F₂ bilinear form ⟨a,b⟩ = ∑ aᵢbᵢ,
    not the symplectic form on the full 2n-dimensional Pauli space. The "symplectic"
    structure arises from *how* this is called: `symplecticInnerProduct z₁ x₂` computes
    the z₁·x₂ component of the symplectic pairing ω((x₁,z₁),(x₂,z₂)) = x₁·z₂ + z₁·x₂.
    See `symplecticInnerProduct_eq_innerProductF2` for the definitional equality with
    `innerProductF2`. -/
def symplecticInnerProduct {n : ℕ} (a b : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, a i * b i

/-- The phase factor (-1)^{⟨a,b⟩} arising from Pauli commutation.
    Returns 1 if inner product is 0, returns -1 if inner product is 1. -/
def pauliCommutationSign {n : ℕ} (a b : Fin n → ZMod 2) : ℂ :=
  if symplecticInnerProduct a b = 0 then 1 else -1

/-!
## Error Equivalence

Two Pauli errors are equivalent (act the same on code states UP TO SIGN) if they
differ by a stabilizer. For CSS codes:
- X errors e₁, e₂ are equivalent if e₁ - e₂ ∈ C₂
- Z errors f₁, f₂ are equivalent if f₁ - f₂ ∈ C₁⊥

**IMPORTANT**: Equivalent errors act the same only up to a sign factor
(-1)^{⟨e₂.z, s_x⟩} where s_x = e₁.x - e₂.x is the X-stabilizer difference.
This sign arises from the non-commutativity of X and Z operators.
-/

/-- Two Pauli errors are equivalent on the code space if they differ by a stabilizer -/
def PauliError.EquivOnCode {n : ℕ} (code : CSSCode n)
    (e₁ e₂ : PauliError n) : Prop :=
  (e₁.xPattern - e₂.xPattern) ∈ code.C2.codewords ∧
  (e₁.zPattern - e₂.zPattern) ∈ code.C1.dual

/-!
## Minimum-Weight Coset Representatives

For CSS codes, X and Z errors are corrected independently. The key to a working
decoder is to pick minimum-weight representatives from syndrome cosets:
- X coset: all vectors with the same X syndrome (differ by elements of C₁)
- Z coset: all vectors with the same Z syndrome (differ by elements of C₂⊥)

The minimum-weight decoder guarantees that the correction has weight ≤ any
error in the same coset, which is essential for the proof.
-/

/-- The X-syndrome coset of a vector: all vectors with the same X syndrome.
    Two vectors are in the same X coset iff they differ by an element of C₁. -/
def CSSCode.xCoset {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : Set (Fin n → ZMod 2) :=
  { w | (v - w) ∈ code.C1.codewords }

/-- The Z-syndrome coset of a vector: all vectors with the same Z syndrome.
    Two vectors are in the same Z coset iff they differ by an element of C₂⊥. -/
def CSSCode.zCoset {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : Set (Fin n → ZMod 2) :=
  { w | (v - w) ∈ code.C2.dual }

/-- Every vector is in its own X coset. -/
theorem CSSCode.mem_xCoset_self {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    v ∈ code.xCoset v := by
  unfold xCoset
  simp only [Set.mem_setOf_eq, sub_self]
  exact code.C1.zero_mem_codewords

/-- Every vector is in its own Z coset. -/
theorem CSSCode.mem_zCoset_self {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    v ∈ code.zCoset v := by
  unfold zCoset
  simp only [Set.mem_setOf_eq, sub_self]
  intro c _
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- X cosets are nonempty. -/
theorem CSSCode.xCoset_nonempty {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    (code.xCoset v).Nonempty :=
  ⟨v, code.mem_xCoset_self v⟩

/-- Z cosets are nonempty. -/
theorem CSSCode.zCoset_nonempty {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    (code.zCoset v).Nonempty :=
  ⟨v, code.mem_zCoset_self v⟩

/-- The set of Hamming weights achieved by elements of an X coset. -/
def CSSCode.xCosetWeights {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : Set ℕ :=
  hammingWeight '' (code.xCoset v)

/-- The set of Hamming weights achieved by elements of a Z coset. -/
def CSSCode.zCosetWeights {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : Set ℕ :=
  hammingWeight '' (code.zCoset v)

/-- X coset weights are nonempty. -/
theorem CSSCode.xCosetWeights_nonempty {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    (code.xCosetWeights v).Nonempty := by
  unfold xCosetWeights
  exact Set.Nonempty.image hammingWeight (code.xCoset_nonempty v)

/-- Z coset weights are nonempty. -/
theorem CSSCode.zCosetWeights_nonempty {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    (code.zCosetWeights v).Nonempty := by
  unfold zCosetWeights
  exact Set.Nonempty.image hammingWeight (code.zCoset_nonempty v)

/-- The minimum X weight in a coset. -/
noncomputable def CSSCode.minXWeight {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : ℕ :=
  sInf (code.xCosetWeights v)

/-- The minimum Z weight in a coset. -/
noncomputable def CSSCode.minZWeight {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) : ℕ :=
  sInf (code.zCosetWeights v)

/-- There exists an element of the X coset achieving the minimum weight. -/
theorem CSSCode.exists_minXWeight_rep {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    ∃ w ∈ code.xCoset v, hammingWeight w = code.minXWeight v := by
  have hne := code.xCosetWeights_nonempty v
  -- Nat.sInf_mem says: if s is nonempty, then sInf s ∈ s
  have hinf_mem : code.minXWeight v ∈ code.xCosetWeights v := Nat.sInf_mem hne
  -- The infimum is in the image of hammingWeight
  unfold xCosetWeights at hinf_mem
  rw [Set.mem_image] at hinf_mem
  obtain ⟨w, hw_coset, hw_wt⟩ := hinf_mem
  exact ⟨w, hw_coset, hw_wt⟩

/-- There exists an element of the Z coset achieving the minimum weight. -/
theorem CSSCode.exists_minZWeight_rep {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    ∃ w ∈ code.zCoset v, hammingWeight w = code.minZWeight v := by
  have hne := code.zCosetWeights_nonempty v
  have hinf_mem : code.minZWeight v ∈ code.zCosetWeights v := Nat.sInf_mem hne
  unfold zCosetWeights at hinf_mem
  rw [Set.mem_image] at hinf_mem
  obtain ⟨w, hw_coset, hw_wt⟩ := hinf_mem
  exact ⟨w, hw_coset, hw_wt⟩

/-- Minimum-weight X coset representative (chosen by Classical.choose). -/
noncomputable def CSSCode.minWeightXRep {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    Fin n → ZMod 2 :=
  Classical.choose (code.exists_minXWeight_rep v)

/-- Minimum-weight Z coset representative (chosen by Classical.choose). -/
noncomputable def CSSCode.minWeightZRep {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    Fin n → ZMod 2 :=
  Classical.choose (code.exists_minZWeight_rep v)

/-- The min-weight X rep is in the X coset. -/
theorem CSSCode.minWeightXRep_mem {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    code.minWeightXRep v ∈ code.xCoset v :=
  (Classical.choose_spec (code.exists_minXWeight_rep v)).1

/-- The min-weight Z rep is in the Z coset. -/
theorem CSSCode.minWeightZRep_mem {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    code.minWeightZRep v ∈ code.zCoset v :=
  (Classical.choose_spec (code.exists_minZWeight_rep v)).1

/-- The min-weight X rep achieves the minimum weight. -/
theorem CSSCode.minWeightXRep_weight {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    hammingWeight (code.minWeightXRep v) = code.minXWeight v :=
  (Classical.choose_spec (code.exists_minXWeight_rep v)).2

/-- The min-weight Z rep achieves the minimum weight. -/
theorem CSSCode.minWeightZRep_weight {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    hammingWeight (code.minWeightZRep v) = code.minZWeight v :=
  (Classical.choose_spec (code.exists_minZWeight_rep v)).2

/-- Key lemma: The min X weight is at most the weight of any element in the coset. -/
theorem CSSCode.minXWeight_le {n : ℕ} (code : CSSCode n) (v w : Fin n → ZMod 2)
    (hw : w ∈ code.xCoset v) : code.minXWeight v ≤ hammingWeight w := by
  unfold minXWeight xCosetWeights
  apply Nat.sInf_le
  exact ⟨w, hw, rfl⟩

/-- Key lemma: The min Z weight is at most the weight of any element in the coset. -/
theorem CSSCode.minZWeight_le {n : ℕ} (code : CSSCode n) (v w : Fin n → ZMod 2)
    (hw : w ∈ code.zCoset v) : code.minZWeight v ≤ hammingWeight w := by
  unfold minZWeight zCosetWeights
  apply Nat.sInf_le
  exact ⟨w, hw, rfl⟩

/-- The min-weight X rep has weight at most the weight of the original vector. -/
theorem CSSCode.minWeightXRep_weight_le {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    hammingWeight (code.minWeightXRep v) ≤ hammingWeight v := by
  rw [code.minWeightXRep_weight v]
  exact code.minXWeight_le v v (code.mem_xCoset_self v)

/-- The min-weight Z rep has weight at most the weight of the original vector. -/
theorem CSSCode.minWeightZRep_weight_le {n : ℕ} (code : CSSCode n) (v : Fin n → ZMod 2) :
    hammingWeight (code.minWeightZRep v) ≤ hammingWeight v := by
  rw [code.minWeightZRep_weight v]
  exact code.minZWeight_le v v (code.mem_zCoset_self v)

/-- Minimum-weight Pauli correction for an error.
    This picks minimum-weight representatives for both X and Z components. -/
noncomputable def CSSCode.minWeightCorrection {n : ℕ} (code : CSSCode n)
    (e : PauliError n) : PauliError n :=
  ⟨code.minWeightXRep e.xPattern, code.minWeightZRep e.zPattern⟩

/-- The min-weight correction has the same X syndrome as the original error. -/
theorem CSSCode.minWeightCorrection_sameXSyndrome {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    e.SameXSyndrome code (code.minWeightCorrection e) := by
  unfold PauliError.SameXSyndrome minWeightCorrection
  simp only
  exact code.minWeightXRep_mem e.xPattern

/-- The min-weight correction has the same Z syndrome as the original error. -/
theorem CSSCode.minWeightCorrection_sameZSyndrome {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    e.SameZSyndrome code (code.minWeightCorrection e) := by
  unfold PauliError.SameZSyndrome minWeightCorrection
  simp only
  exact code.minWeightZRep_mem e.zPattern

/-- The min-weight correction has X weight at most the original error's X weight. -/
theorem CSSCode.minWeightCorrection_xWeight_le {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    (code.minWeightCorrection e).xWeight ≤ e.xWeight := by
  unfold PauliError.xWeight minWeightCorrection
  simp only
  exact code.minWeightXRep_weight_le e.xPattern

/-- The min-weight correction has Z weight at most the original error's Z weight. -/
theorem CSSCode.minWeightCorrection_zWeight_le {n : ℕ} (code : CSSCode n) (e : PauliError n) :
    (code.minWeightCorrection e).zWeight ≤ e.zWeight := by
  unfold PauliError.zWeight minWeightCorrection
  simp only
  exact code.minWeightZRep_weight_le e.zPattern

/-!
## Main Error Correction Theorem

The fundamental theorem of CSS codes: there exists a syndrome-based recovery
procedure that corrects all errors within the correction capability.

Key insight: The recovery map depends ONLY on the syndrome, not on knowing
which specific error occurred. Different correctable errors with the same
syndrome are equivalent (differ by a stabilizer).
-/

/-- **Syndrome Distinguishes Correctable Errors** (Key Lemma)

    If two errors e₁ and e₂ both have weight ≤ t and have the same syndrome,
    then they are equivalent on the code space (differ by a stabilizer).

    **Proof idea**: Same syndrome means e₁ - e₂ ∈ C₁ (for X) and e₁ - e₂ ∈ C₂⊥ (for Z).
    By triangle inequality, wt(e₁ - e₂) ≤ wt(e₁) + wt(e₂) ≤ 2t < d.
    A nonzero codeword in C₁ has weight ≥ d(C₁) ≥ d, contradiction.
    So e₁ - e₂ = 0 (for X errors) or e₁ - e₂ ∈ C₂ (stabilizer).

    This is the core of why CSS codes work: low-weight errors with the
    same syndrome must be equivalent. -/
theorem CSSCode.syndrome_determines_equivalence {n : ℕ} (code : CSSCode n)
    (t : ℕ) (ht : 2 * t + 1 ≤ code.distance)
    (e₁ e₂ : PauliError n)
    (hx₁ : e₁.xWeight ≤ t) (hx₂ : e₂.xWeight ≤ t)
    (hz₁ : e₁.zWeight ≤ t) (hz₂ : e₂.zWeight ≤ t)
    (hsame_x : e₁.SameXSyndrome code e₂)
    (hsame_z : e₁.SameZSyndrome code e₂) :
    e₁.EquivOnCode code e₂ := by
  constructor
  · -- X pattern: show diff ∈ C2.codewords
    -- Key insight: diff ∈ C1.codewords (from SameXSyndrome) and wt(diff) ≤ 2t < d.
    -- Either diff ∈ C2 (done) or diff ∈ C1 \ C2, giving bitFlipDistance ≤ wt(diff) ≤ 2t < d.
    have hdiff : e₁.xPattern - e₂.xPattern ∈ code.C1.codewords := hsame_x
    by_cases hC2 : e₁.xPattern - e₂.xPattern ∈ code.C2.codewords
    · exact hC2
    · exfalso
      -- diff ∈ C1 \ C2, so bitFlipDistance ≤ wt(diff)
      have hmin : code.bitFlipDistance ≤ hammingWeight (e₁.xPattern - e₂.xPattern) := by
        unfold CSSCode.bitFlipDistance
        apply Nat.sInf_le
        rw [Set.mem_image]
        exact ⟨e₁.xPattern - e₂.xPattern, ⟨hdiff, hC2⟩, rfl⟩
      -- Triangle inequality: wt(e₁ - e₂) ≤ wt(e₁) + wt(e₂)
      have hwt_bound : hammingWeight (e₁.xPattern - e₂.xPattern) ≤ e₁.xWeight + e₂.xWeight := by
        unfold PauliError.xWeight
        have htri := hammingDistance_triangle e₁.xPattern 0 e₂.xPattern
        unfold hammingDistance at htri
        simp only [sub_zero, zero_sub] at htri
        -- In ZMod 2, -x = x (characteristic 2)
        have hneg : -e₂.xPattern = e₂.xPattern := by
          ext i; simp only [Pi.neg_apply]; exact CharTwo.neg_eq (e₂.xPattern i)
        rw [hneg] at htri
        exact htri
      have hwt_2t : e₁.xWeight + e₂.xWeight ≤ 2 * t := by omega
      have hdist_bf : code.distance ≤ code.bitFlipDistance := Nat.min_le_left _ _
      omega
  · -- Z pattern: show diff ∈ C1.dual
    -- diff ∈ C2.dual (from SameZSyndrome). Either diff ∈ C1.dual (done) or
    -- diff ∈ C2.dual \ C1.dual, giving phaseFlipDistance ≤ wt(diff) ≤ 2t < distance.
    have hdiff_in_C2_dual : e₁.zPattern - e₂.zPattern ∈ code.C2.dual := hsame_z
    by_cases h_stab : e₁.zPattern - e₂.zPattern ∈ code.C1.dual
    · exact h_stab
    · exfalso
      -- phaseFlipDistance ≤ wt(diff) since diff ∈ C2.dual \ C1.dual
      have hmin : code.phaseFlipDistance ≤ hammingWeight (e₁.zPattern - e₂.zPattern) := by
        unfold CSSCode.phaseFlipDistance
        apply Nat.sInf_le
        rw [Set.mem_image]
        exact ⟨e₁.zPattern - e₂.zPattern, ⟨hdiff_in_C2_dual, h_stab⟩, rfl⟩
      have hwt_bound : hammingWeight (e₁.zPattern - e₂.zPattern) ≤ e₁.zWeight + e₂.zWeight := by
        unfold PauliError.zWeight
        have htri := hammingDistance_triangle e₁.zPattern 0 e₂.zPattern
        unfold hammingDistance at htri
        simp only [sub_zero, zero_sub] at htri
        have hneg : -e₂.zPattern = e₂.zPattern := by
          ext i; simp only [Pi.neg_apply]; exact CharTwo.neg_eq (e₂.zPattern i)
        rw [hneg] at htri
        exact htri
      have hwt_2t : e₁.zWeight + e₂.zWeight ≤ 2 * t := by omega
      have hdist_pf : code.distance ≤ code.phaseFlipDistance := Nat.min_le_right _ _
      omega

/-!
## Helper Lemmas for equiv_act_same

The proof of `equiv_act_same` requires showing that Pauli errors related by stabilizers
act the same (up to phase) on code states. This involves:
1. Decomposing the error operators
2. Using that stabilizers act trivially on code states
3. Computing the phase from Pauli commutation
-/

/-- Helper: The pure X-stabilizer operator for pattern s_x -/
private def pureXStabilizer {n : ℕ} (s_x : Fin n → ZMod 2) : PauliError n :=
  ⟨s_x, fun _ => 0⟩

/-- Helper: The pure Z-stabilizer operator for pattern s_z -/
private def pureZStabilizer {n : ℕ} (s_z : Fin n → ZMod 2) : PauliError n :=
  ⟨fun _ => 0, s_z⟩

/-- Helper: The symplectic inner product of first components times inner product of rest. -/
lemma symplecticInnerProduct_succ {n : ℕ} (a b : Fin (n + 1) → ZMod 2) :
    symplecticInnerProduct a b =
      a 0 * b 0 + symplecticInnerProduct (a ∘ Fin.succ) (b ∘ Fin.succ) := by
  unfold symplecticInnerProduct
  rw [Fin.sum_univ_succ]
  simp only [Function.comp_apply]

/-- Helper lemma: ZMod 2 dichotomy - any element is 0 or 1 -/
private lemma ZMod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  have hlt : v < 2 := hv
  interval_cases v
  · left; rfl
  · right; rfl

/-- pauliCommutationSign decomposes over Fin (n+1) as product of first and rest.
    This is the key to the inductive proof of pauliError_mul. -/
lemma pauliCommutationSign_succ {n : ℕ} (a b : Fin (n + 1) → ZMod 2) :
    pauliCommutationSign a b =
    (if a 0 * b 0 = 1 then -1 else 1 : ℂ) *
    pauliCommutationSign (a ∘ Fin.succ) (b ∘ Fin.succ) := by
  unfold pauliCommutationSign
  rw [symplecticInnerProduct_succ]
  -- Now we have: if (a 0 * b 0 + inner_rest) = 0 then 1 else -1
  --            = (if a 0 * b 0 = 1 then -1 else 1) * (if inner_rest = 0 then 1 else -1)
  set x := a 0 * b 0 with hx_def
  set y := symplecticInnerProduct (a ∘ Fin.succ) (b ∘ Fin.succ) with hy_def
  rcases ZMod2_eq_zero_or_one x with hx0 | hx1 <;> rcases ZMod2_eq_zero_or_one y with hy0 | hy1
  · -- x = 0, y = 0: sum = 0
    simp only [hx0, hy0, zero_add, ↓reduceIte]
    have hne : (0 : ZMod 2) ≠ 1 := by decide
    simp only [hne, ↓reduceIte, mul_one]
  · -- x = 0, y = 1: sum = 1
    simp only [hx0, hy1, zero_add]
    have hne : (0 : ZMod 2) ≠ 1 := by decide
    have h1ne : (1 : ZMod 2) ≠ 0 := by decide
    simp only [hne, h1ne, ↓reduceIte, one_mul]
  · -- x = 1, y = 0: sum = 1
    simp only [hx1, hy0, add_zero, ↓reduceIte]
    have h1ne : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h1ne, ↓reduceIte, mul_one]
  · -- x = 1, y = 1: sum = 0 (1 + 1 = 0 in ZMod 2)
    have hsum : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [hx1, hy1, hsum, ↓reduceIte]
    have h1ne : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h1ne, ↓reduceIte]
    ring

/-- Helper: (-1)^v for v ∈ ZMod 2, as a complex number -/
private def negOnePow (v : ZMod 2) : ℂ := if v = 0 then 1 else -1

/-- Key property: negOnePow (a + b) = negOnePow a * negOnePow b -/
private lemma negOnePow_add (a b : ZMod 2) : negOnePow (a + b) = negOnePow a * negOnePow b := by
  match a, b with
  | 0, 0 => simp only [negOnePow, add_zero, ↓reduceIte, mul_one]
  | 0, 1 => simp only [negOnePow, zero_add, ↓reduceIte, one_mul]
  | 1, 0 => simp only [negOnePow, add_zero, ↓reduceIte, mul_one]
  | 1, 1 => -- 1 + 1 = 0 in ZMod 2
    unfold negOnePow
    have h_add : (1 : ZMod 2) + 1 = 0 := by decide
    have h_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h_add, ↓reduceIte, h_one_ne_zero, neg_mul_neg, mul_one]

/-- pauliCommutationSign is negOnePow of the symplectic inner product -/
private lemma pauliCommutationSign_eq_negOnePow {n : ℕ} (a b : Fin n → ZMod 2) :
    pauliCommutationSign a b = negOnePow (symplecticInnerProduct a b) := by
  unfold pauliCommutationSign negOnePow
  rfl

/-- Helper: pauliCommutationSign splits over sums of inner products -/
lemma pauliCommutationSign_mul {n : ℕ} (a₁ a₂ b₁ b₂ : Fin n → ZMod 2)
    (h : symplecticInnerProduct (a₁ + a₂) (b₁ + b₂) =
         symplecticInnerProduct a₁ b₁ + symplecticInnerProduct a₁ b₂ +
         symplecticInnerProduct a₂ b₁ + symplecticInnerProduct a₂ b₂) :
    pauliCommutationSign (a₁ + a₂) (b₁ + b₂) =
    pauliCommutationSign a₁ b₁ * pauliCommutationSign a₁ b₂ *
    pauliCommutationSign a₂ b₁ * pauliCommutationSign a₂ b₂ := by
  simp only [pauliCommutationSign_eq_negOnePow, h]
  -- Use negOnePow_add repeatedly
  rw [negOnePow_add, negOnePow_add, negOnePow_add]

/-- Key algebraic lemma: The n-qubit Pauli product rule.

    For Pauli errors e₁ = (x₁, z₁) and e₂ = (x₂, z₂):
      e₁.toOp * e₂.toOp = (-1)^{⟨z₁, x₂⟩} · (x₁+x₂, z₁+z₂).toOp

    This is the fundamental n-qubit generalization of X*Z = -Z*X.
    The phase factor comes from moving Z operators past X operators.

    **Proof approach**: By induction on n, using the tensor product structure
    and the single-qubit singleQubitPauli_mul lemma. -/
lemma pauliError_mul {n : ℕ} (e₁ e₂ : PauliError n) :
    e₁.toOp * e₂.toOp = pauliCommutationSign e₁.zPattern e₂.xPattern •
      (⟨e₁.xPattern + e₂.xPattern, e₁.zPattern + e₂.zPattern⟩ : PauliError n).toOp := by
  match n with
  | 0 =>
    -- Base case: n = 0, dimension 1, operators are just scalars
    simp only [PauliError.toOp, pauliCommutationSign, symplecticInnerProduct]
    -- The sum over Fin 0 is empty, so inner product is 0
    simp only [Finset.univ_eq_empty, Finset.sum_empty, ↓reduceIte, one_smul, one_mul]
  | k + 1 =>
    -- Inductive case: use tensor structure
    -- e₁.toOp = firstQubit₁ ⊗ rest₁.toOp (up to castDim)
    -- e₂.toOp = firstQubit₂ ⊗ rest₂.toOp (up to castDim)
    -- Product: (A ⊗ B) * (C ⊗ D) = (A * C) ⊗ (B * D)
    -- Then use singleQubitPauli_mul for the first qubit and IH for the rest
    simp only [PauliError.toOp]
    -- Define the components
    let x1_0 := e₁.xPattern 0
    let z1_0 := e₁.zPattern 0
    let x2_0 := e₂.xPattern 0
    let z2_0 := e₂.zPattern 0
    let fq1 : Op 2 := singleQubitPauli x1_0 z1_0
    let fq2 : Op 2 := singleQubitPauli x2_0 z2_0
    let rest1 : PauliError k := ⟨e₁.xPattern ∘ Fin.succ, e₁.zPattern ∘ Fin.succ⟩
    let rest2 : PauliError k := ⟨e₂.xPattern ∘ Fin.succ, e₂.zPattern ∘ Fin.succ⟩
    let h_dim : 2 * 2^k = 2^(k+1) := by ring
    -- The product of castDim operators
    have hprod : Op.castDim h_dim (fq1 ⊗ rest1.toOp) * Op.castDim h_dim (fq2 ⊗ rest2.toOp) =
                 Op.castDim h_dim ((fq1 ⊗ rest1.toOp) * (fq2 ⊗ rest2.toOp)) :=
      Op.castDim_mul h_dim _ _
    rw [hprod]
    -- Tensor product multiplication: (A ⊗ B) * (C ⊗ D) = (AC) ⊗ (BD)
    rw [Op.tensor_mul]
    -- Step 1: Apply singleQubitPauli_mul for the first qubit
    have hfq : fq1 * fq2 = (if z1_0 * x2_0 = 1 then -1 else 1 : ℂ) •
                          singleQubitPauli (x1_0 + x2_0) (z1_0 + z2_0) :=
      singleQubitPauli_mul x1_0 z1_0 x2_0 z2_0
    -- Step 2: Apply the inductive hypothesis for the rest
    have hrest : rest1.toOp * rest2.toOp =
                 pauliCommutationSign rest1.zPattern rest2.xPattern •
                 (⟨rest1.xPattern + rest2.xPattern,
                   rest1.zPattern + rest2.zPattern⟩ : PauliError k).toOp :=
      pauliError_mul rest1 rest2
    -- Rewrite using these facts
    rw [hfq, hrest]
    -- Step 3: Combine the scalar multiplications using Quantum.TensorProducts.Op.smul_tensor_smul
    rw [Quantum.TensorProducts.Op.smul_tensor_smul]
    -- Step 4: Apply castDim_smul to pull scalar out
    rw [← Op.castDim_smul]
    -- Now we need to show the phases match and the operators match
    -- First rewrite pauliCommutationSign using the succ decomposition
    rw [pauliCommutationSign_succ]
    -- The goal is now definitionally equal (variables match)
    rfl

/-- Key lemma: X-stabilizers (from C₂) act trivially on code states.
    This is half of the definition of InCodeSpace. -/
private lemma xStabilizer_acts_trivially {n : ℕ} (code : CSSCode n)
    (s_x : Fin n → ZMod 2) (hs : s_x ∈ code.C2.codewords)
    (ψ : Ket (2 ^ n)) (hψ : code.InCodeSpace ψ) :
    (pureXStabilizer s_x).toOp * ψ = ψ := by
  exact hψ.1 s_x hs

/-- Key lemma: Z-stabilizers (from C₁⊥) act trivially on code states.
    This is the other half of the definition of InCodeSpace. -/
private lemma zStabilizer_acts_trivially {n : ℕ} (code : CSSCode n)
    (s_z : Fin n → ZMod 2) (hs : s_z ∈ code.C1.dual)
    (ψ : Ket (2 ^ n)) (hψ : code.InCodeSpace ψ) :
    (pureZStabilizer s_z).toOp * ψ = ψ := by
  exact hψ.2 s_z hs

/-- The symplectic inner product equals the inner product over F₂.
    Just a naming convenience. -/
lemma symplecticInnerProduct_eq_innerProductF2 {n : ℕ}
    (a b : Fin n → ZMod 2) : symplecticInnerProduct a b = innerProductF2 a b := rfl

/-- Helper: pauliCommutationSign is 1 when inner product is 0 -/
lemma pauliCommutationSign_zero {n : ℕ} (a b : Fin n → ZMod 2)
    (h : symplecticInnerProduct a b = 0) : pauliCommutationSign a b = 1 := by
  unfold pauliCommutationSign
  simp only [h, ↓reduceIte]

/-- Helper: pauliCommutationSign is -1 when inner product is 1 -/
lemma pauliCommutationSign_one {n : ℕ} (a b : Fin n → ZMod 2)
    (h : symplecticInnerProduct a b = 1) : pauliCommutationSign a b = -1 := by
  unfold pauliCommutationSign
  simp only [h]
  -- 1 ≠ 0 in ZMod 2
  have hne : (1 : ZMod 2) ≠ 0 := by norm_num
  simp only [hne, ↓reduceIte]

/-- Helper: The inner product of a zero pattern with anything is 0 -/
lemma symplecticInnerProduct_zero_left {n : ℕ} (b : Fin n → ZMod 2) :
    symplecticInnerProduct (fun _ => 0) b = 0 := by
  unfold symplecticInnerProduct
  simp only [zero_mul, Finset.sum_const_zero]

/-- Helper: The inner product of anything with a zero pattern is 0 -/
lemma symplecticInnerProduct_zero_right {n : ℕ} (a : Fin n → ZMod 2) :
    symplecticInnerProduct a (fun _ => 0) = 0 := by
  unfold symplecticInnerProduct
  simp only [mul_zero, Finset.sum_const_zero]

/-- Equivalent errors act on code states with a relative phase.

    If e₁ and e₂ differ by a stabilizer (s_x, s_z), then:
      e₁|ψ⟩ = (-1)^{⟨e₂.z, s_x⟩} · e₂|ψ⟩

    The phase arises from Pauli commutation: when we factor e₁ = S · e₂ (up to phase),
    moving the stabilizer S past e₂ introduces (-1)^{⟨s_z, e₂.x⟩}, and the overall
    algebra gives (-1)^{⟨e₂.z, s_x⟩}.

    **Note**: Exact equality without the relative phase is false.
-/
theorem PauliError.equiv_act_same {n : ℕ} (code : CSSCode n)
    (e₁ e₂ : PauliError n) (heq : e₁.EquivOnCode code e₂)
    (ψ : Ket (2 ^ n)) (hψ : code.InCodeSpace ψ) :
    e₁.toOp * ψ = pauliCommutationSign e₂.zPattern (e₁.xPattern - e₂.xPattern) • (e₂.toOp * ψ) := by
  -- Extract the stabilizer differences from the equivalence
  obtain ⟨hx_stab, hz_stab⟩ := heq
  -- s_x = e₁.xPattern - e₂.xPattern is in C₂ (X-stabilizer)
  -- s_z = e₁.zPattern - e₂.zPattern is in C₁⊥ (Z-stabilizer)
  let s_x := e₁.xPattern - e₂.xPattern
  let s_z := e₁.zPattern - e₂.zPattern
  -- Define the X-stabilizer and Z-stabilizer as PauliErrors
  let X_stab : PauliError n := pureXStabilizer s_x
  let Z_stab : PauliError n := pureZStabilizer s_z
  -- The stabilizers act trivially on code states
  have hX_trivial : X_stab.toOp * ψ = ψ := xStabilizer_acts_trivially code s_x hx_stab ψ hψ
  have hZ_trivial : Z_stab.toOp * ψ = ψ := zStabilizer_acts_trivially code s_z hz_stab ψ hψ
  -- Step 1: Establish that e₁ has patterns s_x + e₂.x and s_z + e₂.z
  have he1_eq : e₁ = ⟨s_x + e₂.xPattern, s_z + e₂.zPattern⟩ :=
    congrArg₂ PauliError.mk (sub_add_cancel _ _).symm (sub_add_cancel _ _).symm
  -- Step 2: Compute e₂ * X_stab using pauliError_mul
  -- e₂ * X_stab = pauliCommutationSign e₂.z s_x • ⟨e₂.x + s_x, e₂.z + 0⟩
  --             = pauliCommutationSign e₂.z s_x • ⟨s_x + e₂.x, e₂.z⟩
  let intermediate : PauliError n := ⟨s_x + e₂.xPattern, e₂.zPattern⟩
  have h_e2_Xstab : e₂.toOp * X_stab.toOp =
      pauliCommutationSign e₂.zPattern s_x • intermediate.toOp := by
    have hmul := pauliError_mul e₂ X_stab
    -- X_stab.xPattern = s_x and X_stab.zPattern = 0
    have hx_stab_x : X_stab.xPattern = s_x := rfl
    have hx_stab_z : X_stab.zPattern = fun _ => 0 := rfl
    rw [hx_stab_x, hx_stab_z] at hmul
    -- e₂.z + 0 = e₂.z
    have hz_simp : e₂.zPattern + (fun _ => 0) = e₂.zPattern := add_zero _
    -- e₂.x + s_x = s_x + e₂.x
    have hx_comm : e₂.xPattern + s_x = s_x + e₂.xPattern := add_comm _ _
    -- The result PauliError is intermediate
    have heq : (⟨e₂.xPattern + s_x, e₂.zPattern + (fun _ => 0)⟩ : PauliError n) = intermediate := by
      change (⟨e₂.xPattern + s_x, e₂.zPattern + (fun _ => 0)⟩ : PauliError n) =
             ⟨s_x + e₂.xPattern, e₂.zPattern⟩
      rw [PauliError.mk.injEq]
      exact ⟨hx_comm, hz_simp⟩
    rw [heq] at hmul
    exact hmul
  -- Step 3: Compute intermediate * Z_stab using pauliError_mul
  -- intermediate * Z_stab = pauliCommutationSign e₂.z 0 • ⟨s_x + e₂.x + 0, e₂.z + s_z⟩
  --                       = 1 • e₁
  have h_int_Zstab : intermediate.toOp * Z_stab.toOp = e₁.toOp := by
    have hmul := pauliError_mul intermediate Z_stab
    -- Z_stab.xPattern = 0 and Z_stab.zPattern = s_z
    have hz_stab_x : Z_stab.xPattern = fun _ => 0 := rfl
    have hz_stab_z : Z_stab.zPattern = s_z := rfl
    rw [hz_stab_x, hz_stab_z] at hmul
    -- intermediate patterns
    have hint_x : intermediate.xPattern = s_x + e₂.xPattern := rfl
    have hint_z : intermediate.zPattern = e₂.zPattern := rfl
    rw [hint_x, hint_z] at hmul
    -- Simplify: (s_x + e₂.x) + 0 = s_x + e₂.x
    have hx_simp : (s_x + e₂.xPattern) + (fun _ => 0) = s_x + e₂.xPattern := add_zero _
    -- Simplify: e₂.z + s_z = s_z + e₂.z
    have hz_comm : e₂.zPattern + s_z = s_z + e₂.zPattern := add_comm _ _
    -- Simplify: pauliCommutationSign e₂.z 0 = 1
    have hphase : pauliCommutationSign e₂.zPattern (fun _ => 0) = 1 :=
      pauliCommutationSign_zero e₂.zPattern (fun _ => 0) (symplecticInnerProduct_zero_right _)
    -- The result PauliError is e₁
    have heq : (⟨(s_x + e₂.xPattern) + (fun _ => 0), e₂.zPattern + s_z⟩ : PauliError n) =
               ⟨s_x + e₂.xPattern, s_z + e₂.zPattern⟩ := by
      simp only [PauliError.mk.injEq]
      exact ⟨hx_simp, hz_comm⟩
    rw [heq, hphase, one_smul] at hmul
    rw [he1_eq]
    exact hmul
  -- Step 4: Combine to get e₂ * X_stab * Z_stab = phase • e₁
  have h_combined : e₂.toOp * X_stab.toOp * Z_stab.toOp =
      pauliCommutationSign e₂.zPattern s_x • e₁.toOp := by
    calc e₂.toOp * X_stab.toOp * Z_stab.toOp
        = (pauliCommutationSign e₂.zPattern s_x • intermediate.toOp) * Z_stab.toOp := by
            rw [h_e2_Xstab]
      _ = pauliCommutationSign e₂.zPattern s_x • (intermediate.toOp * Z_stab.toOp) := by
            rw [Matrix.smul_mul]
      _ = pauliCommutationSign e₂.zPattern s_x • e₁.toOp := by rw [h_int_Zstab]
  -- Step 5: Invert to get e₁ in terms of e₂ and stabilizers
  -- Since pauliCommutationSign² = 1, we have:
  -- e₁ = phase • (e₂ * X_stab * Z_stab)
  have hphase_sq : pauliCommutationSign e₂.zPattern s_x *
      pauliCommutationSign e₂.zPattern s_x = 1 := by
    unfold pauliCommutationSign
    split_ifs with h
    · ring
    · ring
  have h_e1_decomp : e₁.toOp = pauliCommutationSign e₂.zPattern s_x •
      (e₂.toOp * X_stab.toOp * Z_stab.toOp) := by
    -- Multiply both sides of h_combined by the phase (which is its own inverse)
    calc e₁.toOp
        = 1 • e₁.toOp := (one_smul ℂ _).symm
      _ = (pauliCommutationSign e₂.zPattern s_x * pauliCommutationSign e₂.zPattern s_x) •
          e₁.toOp := by rw [← hphase_sq]
      _ = pauliCommutationSign e₂.zPattern s_x •
          (pauliCommutationSign e₂.zPattern s_x • e₁.toOp) := by rw [smul_smul]
      _ = pauliCommutationSign e₂.zPattern s_x •
          (e₂.toOp * X_stab.toOp * Z_stab.toOp) := by rw [← h_combined]
  -- Helper: Op * Op * Ket associativity: (A * B) * ψ = A * (B * ψ)
  have op_op_ket_assoc : ∀ (A B : Op (2^n)) (χ : Ket (2^n)), (A * B) * χ = A * (B * χ) := by
    intro A B χ
    ext i
    simp only [Quantum.Operators.op_mul_ket_vec]
    rw [Matrix.mulVec_mulVec]
  -- Step 6: Act on ψ and use that stabilizers act trivially
  calc e₁.toOp * ψ
      = (pauliCommutationSign e₂.zPattern s_x • (e₂.toOp * X_stab.toOp * Z_stab.toOp)) * ψ := by
          rw [h_e1_decomp]
    _ = pauliCommutationSign e₂.zPattern s_x • ((e₂.toOp * X_stab.toOp * Z_stab.toOp) * ψ) := by
          rw [Quantum.Operators.smul_op_mul_ket]
    _ = pauliCommutationSign e₂.zPattern s_x • ((e₂.toOp * X_stab.toOp) * (Z_stab.toOp * ψ)) := by
          rw [op_op_ket_assoc]
    _ = pauliCommutationSign e₂.zPattern s_x • ((e₂.toOp * X_stab.toOp) * ψ) := by
          rw [hZ_trivial]
    _ = pauliCommutationSign e₂.zPattern s_x • (e₂.toOp * (X_stab.toOp * ψ)) := by
          rw [op_op_ket_assoc]
    _ = pauliCommutationSign e₂.zPattern s_x • (e₂.toOp * ψ) := by rw [hX_trivial]

theorem PauliError.equiv_act_same_when_orthogonal {n : ℕ} (code : CSSCode n)
    (e₁ e₂ : PauliError n) (heq : e₁.EquivOnCode code e₂)
    (horth : symplecticInnerProduct e₂.zPattern (e₁.xPattern - e₂.xPattern) = 0)
    (ψ : Ket (2 ^ n)) (hψ : code.InCodeSpace ψ) :
    e₁.toOp * ψ = e₂.toOp * ψ := by
  have h := PauliError.equiv_act_same code e₁ e₂ heq ψ hψ
  simp only [pauliCommutationSign, horth, ↓reduceIte] at h
  -- h : e₁.toOp * ψ = (1 : ℂ) • (e₂.toOp * ψ)
  rw [Quantum.Operators.Ket.one_smul] at h
  exact h

/-- **CSS Error Correction Theorem** (Syndrome-based recovery, up to global phase)

    For a CSS code with distance d and correction capability t = ⌊(d-1)/2⌋:

    There exists a correction map from syndromes to Pauli operators such that
    for ANY error e with weight ≤ t, applying the correction (based only on
    the syndrome) after the error recovers the original code state **up to a
    global phase factor**.

    **Key property**: The correction depends only on the syndrome, not on
    knowing which error occurred. This is what makes it a true error correction
    code, not just "undo the error if you know what it is."

    **Why up to phase?**: When correction c and error e are equivalent (differ
    by a stabilizer), c * e produces a phase factor from the Pauli commutation:
      c.toOp * e.toOp = (-1)^{⟨c.z, e.x⟩} · (c + e).toOp
    Different errors in the same syndrome coset may have different phases.
    Since global phases are unobservable in quantum mechanics, this is the
    correct statement for quantum error correction.

    **Why it works**: If e₁ and e₂ have the same syndrome and both have weight ≤ t,
    then e₁ - e₂ has weight ≤ 2t < d, so e₁ - e₂ must be a stabilizer (or zero).
    Thus e₁ and e₂ act the same (up to phase) on code states.

    The correction function takes a representative error for each syndrome
    (a "coset leader" - typically the minimum weight error with that syndrome). -/
theorem CSSCode.corrects_errors {n : ℕ} (code : CSSCode n)
    (t : ℕ) (ht : 2 * t + 1 ≤ code.distance) :
    ∃ (correction : PauliError n → PauliError n),
      -- The correction depends only on syndrome (same syndrome → same correction)
      (∀ e₁ e₂ : PauliError n,
        e₁.SameXSyndrome code e₂ → e₁.SameZSyndrome code e₂ →
        correction e₁ = correction e₂) ∧
      -- The correction works up to global phase for all correctable errors
      (∀ (e : PauliError n),
        e.xWeight ≤ t → e.zWeight ≤ t →
        ∀ (ψ : Ket (2 ^ n)), code.InCodeSpace ψ →
          ∃ (phase : ℂ), ‖phase‖ = 1 ∧
            (correction e).toOp * (e.toOp * ψ) = phase • ψ) := by
  -- Use minimum-weight correction
  use code.minWeightCorrection
  constructor
  · -- Property 1: Same syndrome → same correction
    intro e₁ e₂ hsx hsz
    unfold CSSCode.minWeightCorrection
    -- Same X syndrome means e₁.xPattern and e₂.xPattern are in the same xCoset
    have hx_same_coset : code.xCoset e₁.xPattern = code.xCoset e₂.xPattern := by
      ext w
      unfold CSSCode.xCoset
      simp only [Set.mem_setOf_eq]
      constructor
      · -- `e₂ - w = (e₁ - w) - (e₁ - e₂)`
        intro hw
        rw [← sub_sub_sub_cancel_left w e₂.xPattern e₁.xPattern]
        exact code.C1.codewords_sub _ _ hw hsx
      · -- `e₁ - w = (e₁ - e₂) + (e₂ - w)`
        intro hw
        rw [← sub_add_sub_cancel e₁.xPattern e₂.xPattern w]
        exact code.C1.codewords_add _ _ hsx hw
    -- Same Z syndrome means e₁.zPattern and e₂.zPattern are in the same zCoset
    have hz_same_coset : code.zCoset e₁.zPattern = code.zCoset e₂.zPattern := by
      ext w
      unfold CSSCode.zCoset
      simp only [Set.mem_setOf_eq]
      constructor
      · -- `e₂ - w = (e₁ - w) - (e₁ - e₂)`
        intro hw
        rw [← sub_sub_sub_cancel_left w e₂.zPattern e₁.zPattern]
        exact code.C2.dual_sub _ _ hw hsz
      · -- `e₁ - w = (e₁ - e₂) + (e₂ - w)`
        intro hw
        rw [← sub_add_sub_cancel e₁.zPattern e₂.zPattern w]
        exact code.C2.dual_add _ _ hsz hw
    -- Now show the minWeight reps are equal using congrArg
    have hx_weights_eq : code.xCosetWeights e₁.xPattern = code.xCosetWeights e₂.xPattern := by
      unfold CSSCode.xCosetWeights; rw [hx_same_coset]
    have hz_weights_eq : code.zCosetWeights e₁.zPattern = code.zCosetWeights e₂.zPattern := by
      unfold CSSCode.zCosetWeights; rw [hz_same_coset]
    have hx_min_eq : code.minXWeight e₁.xPattern = code.minXWeight e₂.xPattern := by
      unfold CSSCode.minXWeight; rw [hx_weights_eq]
    have hz_min_eq : code.minZWeight e₁.zPattern = code.minZWeight e₂.zPattern := by
      unfold CSSCode.minZWeight; rw [hz_weights_eq]
    -- The key: minWeightXRep/ZRep use Classical.choose on a predicate involving the coset
    -- Since the cosets are equal, the predicates are equal, hence the choices are equal
    have hx_rep_eq : code.minWeightXRep e₁.xPattern = code.minWeightXRep e₂.xPattern := by
      unfold CSSCode.minWeightXRep
      -- Both choices satisfy: w ∈ xCoset v ∧ hammingWeight w = minXWeight v
      -- Since xCoset e₁.x = xCoset e₂.x and minXWeight e₁.x = minXWeight e₂.x,
      -- the predicates are equal, so Classical.choose returns the same value
      -- Classical.choose on equal predicates gives equal results
      congr 1
      ext w; rw [hx_same_coset, hx_min_eq]
    have hz_rep_eq : code.minWeightZRep e₁.zPattern = code.minWeightZRep e₂.zPattern := by
      unfold CSSCode.minWeightZRep
      -- Classical.choose on equal predicates gives equal results
      congr 1
      ext w; rw [hz_same_coset, hz_min_eq]
    simp only [PauliError.mk.injEq]
    exact ⟨hx_rep_eq, hz_rep_eq⟩
  · -- Property 2: Correction works up to phase for correctable errors
    intro e hxwt hzwt ψ hψ
    let c := code.minWeightCorrection e
    -- The phase from Pauli commutation: either 1 or -1
    let phase := pauliCommutationSign c.zPattern e.xPattern
    use phase
    constructor
    · -- Phase has norm 1 (it's either 1 or -1)
      simp only [phase, pauliCommutationSign]
      split_ifs with h
      · simp only [norm_one]
      · simp only [norm_neg, norm_one]
    · -- Correction works: c.toOp * (e.toOp * ψ) = phase • ψ
      -- Step 1: c has weight ≤ e's weight ≤ t
      have hcxwt : c.xWeight ≤ t := le_trans (code.minWeightCorrection_xWeight_le e) hxwt
      have hczwt : c.zWeight ≤ t := le_trans (code.minWeightCorrection_zWeight_le e) hzwt
      -- Step 2: c and e have the same syndrome
      have hesame_x : e.SameXSyndrome code c := code.minWeightCorrection_sameXSyndrome e
      have hesame_z : e.SameZSyndrome code c := code.minWeightCorrection_sameZSyndrome e
      -- Convert to c.SameXSyndrome code e (by negation symmetry)
      have hcsame_x : c.SameXSyndrome code e := by
        unfold PauliError.SameXSyndrome at hesame_x ⊢
        rw [← neg_sub]
        exact code.C1.codewords_neg _ hesame_x
      have hcsame_z : c.SameZSyndrome code e := by
        unfold PauliError.SameZSyndrome at hesame_z ⊢
        rw [← neg_sub]
        exact code.C2.dual_neg _ hesame_z
      -- Step 3: By syndrome_determines_equivalence, c and e are equivalent
      have hequiv : c.EquivOnCode code e :=
        CSSCode.syndrome_determines_equivalence code t ht c e hcxwt hxwt hczwt hzwt
          hcsame_x hcsame_z
      -- Step 4: Use pauliError_mul to compute c.toOp * e.toOp
      have hprod : c.toOp * e.toOp = phase •
          (⟨c.xPattern + e.xPattern, c.zPattern + e.zPattern⟩ : PauliError n).toOp :=
        pauliError_mul c e
      -- Step 5: c.EquivOnCode e means c + e is a combined stabilizer
      obtain ⟨hx_stab, hz_stab⟩ := hequiv
      have hx_add : c.xPattern + e.xPattern ∈ code.C2.codewords := by
        have h : c.xPattern + e.xPattern = c.xPattern - e.xPattern := by
          ext i; simp only [Pi.add_apply, Pi.sub_apply]; exact (CharTwo.sub_eq_add _ _).symm
        rw [h]; exact hx_stab
      have hz_add : c.zPattern + e.zPattern ∈ code.C1.dual := by
        have h : c.zPattern + e.zPattern = c.zPattern - e.zPattern := by
          ext i; simp only [Pi.add_apply, Pi.sub_apply]; exact (CharTwo.sub_eq_add _ _).symm
        rw [h]; exact hz_stab
      -- Step 6: Combined stabilizer (c + e) acts trivially on code states
      let combined := (⟨c.xPattern + e.xPattern, c.zPattern + e.zPattern⟩ : PauliError n)
      let X_part := pureXStabilizer (c.xPattern + e.xPattern)
      let Z_part := pureZStabilizer (c.zPattern + e.zPattern)
      -- X_part.toOp * Z_part.toOp = combined.toOp
      have hfactor : X_part.toOp * Z_part.toOp = combined.toOp := by
        have hmul := pauliError_mul X_part Z_part
        simp only [X_part, Z_part, pureXStabilizer, pureZStabilizer] at hmul
        have hphase0 : pauliCommutationSign (fun _ : Fin n => 0) (fun _ : Fin n => 0) = 1 := by
          unfold pauliCommutationSign symplecticInnerProduct
          simp only [zero_mul, Finset.sum_const_zero, ↓reduceIte]
        have hx_simp : (c.xPattern + e.xPattern) + (fun _ => 0) = c.xPattern + e.xPattern :=
          add_zero _
        have hz_simp : (fun _ => (0 : ZMod 2)) + (c.zPattern + e.zPattern) =
                       c.zPattern + e.zPattern := zero_add _
        simp only [hphase0, one_smul] at hmul
        have heq : (⟨(c.xPattern + e.xPattern) + (fun _ => 0),
                    (fun _ => (0 : ZMod 2)) + (c.zPattern + e.zPattern)⟩ : PauliError n) =
                   combined := by
          simp only [combined, PauliError.mk.injEq]
          exact ⟨hx_simp, hz_simp⟩
        rw [heq] at hmul
        exact hmul
      -- X-stabilizer acts trivially
      have hX_triv : X_part.toOp * ψ = ψ := xStabilizer_acts_trivially code _ hx_add ψ hψ
      -- Z-stabilizer acts trivially
      have hZ_triv : Z_part.toOp * ψ = ψ := zStabilizer_acts_trivially code _ hz_add ψ hψ
      -- Combined stabilizer acts trivially
      have hcombined_triv : combined.toOp * ψ = ψ := by
        rw [← hfactor]
        have hassoc : ∀ (A B : Op (2^n)) (χ : Ket (2^n)), (A * B) * χ = A * (B * χ) := by
          intro A B χ; ext i
          simp only [Quantum.Operators.op_mul_ket_vec]
          rw [Matrix.mulVec_mulVec]
        rw [hassoc, hZ_triv, hX_triv]
      -- Step 7: Put it all together
      have hassoc' : ∀ (A B : Op (2^n)) (χ : Ket (2^n)), A * (B * χ) = (A * B) * χ := by
        intro A B χ; ext i
        simp only [Quantum.Operators.op_mul_ket_vec]
        rw [← Matrix.mulVec_mulVec]
      calc (c.toOp) * (e.toOp * ψ)
          = (c.toOp * e.toOp) * ψ := by rw [← hassoc']
        _ = (phase • combined.toOp) * ψ := by rw [hprod]
        _ = phase • (combined.toOp * ψ) := by rw [Quantum.Operators.smul_op_mul_ket]
        _ = phase • ψ := by rw [hcombined_triv]

end Math.CodingTheory.CSS

end
