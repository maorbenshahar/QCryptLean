import QCryptLean

/-!
# Definitional identities for finite-key bounds and quantum constructions

Each equality expands a composition of named quantities into its explicit formula.
Proposition-valued conditions are compared by equivalence.
-/

noncomputable section

section
open Quantum.DeFinetti
open Math.Combinatorics
open Equiv
open Quantum.Operators Quantum.Channels Quantum.Metrics 
open Quantum.Symmetry
open InfoTheory.SmoothMinEntropy Quantum.DeFinetti InfoTheory.QuantumLHL
open scoped Matrix BigOperators ComplexOrder
namespace InfoTheory.Postselection

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.coherentIIDSecrecy_eq_original (εAT εPA εbar : ℝ) :
    coherentIIDSecrecy εAT εPA εbar =
      (fun (εAT εPA εbar : ℝ) =>
  εPA + 2 * εbar + 2 * Real.sqrt (2 * εAT)) εAT εPA εbar := by
  rfl

end InfoTheory.Postselection
end

section
open Quantum.Operators Matrix InfoTheory.SmoothMinEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators
namespace InfoTheory.Renyi

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.petzContinuityK_eq_original {m : Type*} [Fintype m] [DecidableEq m]
    (α μ : ℝ) (ρ σ : Matrix m m ℂ) :
    petzContinuityK α μ ρ σ =
      (fun (α μ : ℝ) (ρ σ : Matrix m m ℂ) =>
  (1 / (6 * μ ^ 3 * Real.log 2))
    * (2 : ℝ) ^ ((α - 1) * (petzRenyiDivergence α ρ σ - relativeEntropyBits ρ σ))
    * (Real.log ((2 : ℝ) ^ ((α + μ - 1)
        * (petzRenyiDivergence (α + μ) ρ σ - relativeEntropyBits ρ σ))
        + Real.exp 2)) ^ 3) α μ ρ σ := by
  rfl

end InfoTheory.Renyi
end

section
open InfoTheory.Renyi
namespace InfoTheory.Renyi

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.clampedRenyiOffset_eq_original (V : ℝ) (m : ℕ) (ε : ℝ) :
    clampedRenyiOffset V m ε =
      (fun (V : ℝ) (m : ℕ) (ε : ℝ) =>
  min (1 / 16) (Real.sqrt (2 * Real.logb 2 (2 / ε ^ 2) / (V * Real.log 2 * (m : ℝ))))) V m ε := by
  rfl

end InfoTheory.Renyi
end

section
open InfoTheory.Renyi
namespace InfoTheory.Renyi

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.clampedRenyiPenalty_eq_original (V : ℝ) (m : ℕ) (ε : ℝ) :
    clampedRenyiPenalty V m ε =
      (fun (V : ℝ) (m : ℕ) (ε : ℝ) =>
  V / 2 * Real.log 2 * (m : ℝ) * clampedRenyiOffset V m ε
    + binarySecondOrderRemainderBound (clampedRenyiOffset V m ε) * (m : ℝ)
        * clampedRenyiOffset V m ε ^ 2
    + Real.logb 2 (2 / ε ^ 2) / clampedRenyiOffset V m ε) V m ε := by
  rfl

end InfoTheory.Renyi
end

section
open InfoTheory.Renyi
namespace InfoTheory.Renyi

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.renyiPenalty_eq_original (V : ℝ) (m : ℕ) (ε β : ℝ) :
    renyiPenalty V m ε β =
      (fun (V : ℝ) (m : ℕ) (ε β : ℝ) =>
  V / 2 * Real.log 2 * (m : ℝ) * β
    + binarySecondOrderRemainderBound β * (m : ℝ) * β ^ 2
    + Real.logb 2 (2 / ε ^ 2) / β) V m ε β := by
  rfl

end InfoTheory.Renyi
end

section
open Math.Combinatorics
open Math.ClassicalEntropy
namespace QKD.BB84.Comparison

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.literatureFiniteSizePenalty_eq_original (nK : ℕ) (εPA : ℝ) :
    literatureFiniteSizePenalty nK εPA =
      (fun (nK : ℕ) (εPA : ℝ) =>
  (nK : ℝ) * literatureRenyiOffset nK εPA * literatureContinuityConstant
    + (1 + literatureRenyiOffset nK εPA) / literatureRenyiOffset nK εPA
        * (Real.logb 2 (1 / (4 * εPA)) + 2 / (1 + literatureRenyiOffset nK εPA))) nK εPA := by
  rfl

end QKD.BB84.Comparison
end

section
open scoped QuantumAdjoint QuantumTensor
open Quantum.Operators  Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.FiniteKey
open QKD.BB84.Model
namespace QKD.BB84

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.hoeffdingTestAbortBound_eq_original (mZ mX : ℕ) (δ εEC : ℝ) :
    hoeffdingTestAbortBound mZ mX δ εEC =
      (fun (mZ mX : ℕ) (δ εEC : ℝ) =>
  2 * Real.exp (-2 * (mZ : ℝ) * δ ^ 2) + 2 * Real.exp (-2 * (mX : ℝ) * δ ^ 2) + εEC)
        mZ mX δ εEC := by
  rfl

end QKD.BB84
end

section
open scoped QuantumAdjoint QuantumTensor
open Quantum.Operators  Matrix
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.FiniteKey
open QKD.BB84.Model
namespace QKD.BB84

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.testAbortBound_eq_original (mZ mX : ℕ) (Q δ q εEC : ℝ) :
    testAbortBound mZ mX Q δ q εEC =
      (fun (mZ mX : ℕ) (Q δ q εEC : ℝ) =>
  (Real.exp (-(mZ : ℝ) * Math.Concentration.BernoulliKL.klBer (Q + δ) q) +
      Real.exp (-(mZ : ℝ) * Math.Concentration.BernoulliKL.klBer (Q - δ) q)) +
    (Real.exp (-(mX : ℝ) * Math.Concentration.BernoulliKL.klBer (Q + δ) q) +
      Real.exp (-(mX : ℝ) * Math.Concentration.BernoulliKL.klBer (Q - δ) q)) + εEC)
        mZ mX Q δ q εEC := by
  rfl

end QKD.BB84
end

section
open Math.ClassicalEntropy
namespace QKD.BB84.FiniteKey

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.aepSecrecyBudget_eq_original (E : ℝ) (n m : ℕ) (Q δ ε_AEP : ℝ) :
    aepSecrecyBudget E n m Q δ ε_AEP =
      (fun (E : ℝ) (n m : ℕ) (Q δ ε_AEP : ℝ) =>
  2 * Real.sqrt (2 * E) +
    2 * ε_AEP +
    (1 / 2) * Real.exp (-(keyRounds n m : ℝ) / 4 *
      (Real.log 2 - binaryEntropy (Q + 2 * δ)))) E n m Q δ ε_AEP := by
  rfl

end QKD.BB84.FiniteKey
end

section
open Math.ClassicalEntropy
namespace QKD.BB84.FiniteKey

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.aepBudget_eq_original (E : ℝ) (n m ℓEV : ℕ) (Q δ ε_AEP : ℝ) :
    aepBudget E n m ℓEV Q δ ε_AEP =
      (fun (E : ℝ) (n m ℓEV : ℕ) (Q δ ε_AEP : ℝ) =>
  (2 : ℝ) ^ (-(ℓEV : ℝ)) +
    (Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1) : ℝ) *
      aepSecrecyBudget E n m Q δ ε_AEP) E n m ℓEV Q δ ε_AEP := by
  rfl

end QKD.BB84.FiniteKey
end

section
open Quantum.DeFinetti
open Quantum.Operators  Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model
namespace QKD.BB84.FiniteKey

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.bellRenyiSecrecyBudget_eq_original (E ε_AEP epsPA : ℝ) :
    bellRenyiSecrecyBudget E ε_AEP epsPA =
      (fun (E ε_AEP epsPA : ℝ) =>
  epsPA + 2 * (ε_AEP + Real.sqrt (2 * E))) E ε_AEP epsPA := by
  unfold bellRenyiSecrecyBudget InfoTheory.Security.smoothingError
    InfoTheory.Security.acceptanceError
  ring

end QKD.BB84.FiniteKey
end

section
open Quantum.DeFinetti
open Quantum.Operators  Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model
namespace QKD.BB84.FiniteKey

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.bellRenyiBudget_eq_original (E : ℝ) (n ℓEV : ℕ) (ε_AEP εPA : ℝ) :
    bellRenyiBudget E n ℓEV ε_AEP εPA =
      (fun (E : ℝ) (n ℓEV : ℕ) (ε_AEP εPA : ℝ) =>
  (2 : ℝ) ^ (-(ℓEV : ℝ)) +
    (Nat.choose (n + 3) 3 : ℝ) *
    bellRenyiSecrecyBudget E ε_AEP εPA) E n ℓEV ε_AEP εPA := by
  simp only [bellRenyiBudget, InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor_four]

end QKD.BB84.FiniteKey
end

section
open Math.ClassicalEntropy
namespace QKD.BB84.FiniteKey

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.aepKeyRate_eq_original (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP : ℝ) :
    AEPKeyRate n m ℓ ℓEV leakEC Q δ ε_AEP ↔
      (fun (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP : ℝ) =>
  2 * (ℓ : ℝ) * Real.log 2 + 2 * (leakEC : ℝ) * Real.log 2 +
      2 * (ℓEV : ℝ) * Real.log 2 +
      4 * Real.log
        (Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1) : ℝ) +
      2 * Real.log 2 *
        finiteSizePenalty (keyRounds n m) ε_AEP ≤
    (keyRounds n m : ℝ) * (Real.log 2 - binaryEntropy (Q + 2 * δ))) n m ℓ ℓEV leakEC Q δ ε_AEP := by
  exact aepKeyRate_iff n m ℓ ℓEV leakEC Q δ ε_AEP

end QKD.BB84.FiniteKey
end

section
open Math.Combinatorics
open InfoTheory.Renyi
open Math.ClassicalEntropy
namespace QKD.BB84.FiniteKey

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.bellRenyiWindowKeyRate_eq_original
    (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP εPA β : ℝ) :
    BellRenyiWindowKeyRate n m ℓ ℓEV leakEC Q δ ε_AEP εPA β ↔
      (fun (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP εPA β : ℝ) =>
  (ℓ : ℝ) * Real.log 2 + (leakEC : ℝ) * Real.log 2 + (ℓEV : ℝ) * Real.log 2 +
      2 * Real.log (Nat.choose (n + 3) 3 : ℝ) +
      Real.log 2 * renyiPenalty binaryVarianceBound
        (keyRounds n m) ε_AEP β +
      (2 * Real.log (1 / εPA) - 2 * Real.log 2) ≤
    (keyRounds n m : ℝ) * (Real.log 2 - binaryEntropy (Q + 2 * δ)))
        n m ℓ ℓEV leakEC Q δ ε_AEP εPA β := by
  exact bellRenyiWindowKeyRate_iff n m ℓ ℓEV leakEC Q δ ε_AEP εPA β

end QKD.BB84.FiniteKey
end

section
open Math.Combinatorics
open InfoTheory.Renyi
open Math.ClassicalEntropy
namespace QKD.BB84.FiniteKey

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.bellRenyiKeyRate_eq_original
    (n m ℓ ℓEV leakEC : ℕ) (Q δ dev ε_AEP εPA β : ℝ) :
    BellRenyiKeyRate n m ℓ ℓEV leakEC Q δ dev ε_AEP εPA β ↔
      (fun (n m ℓ ℓEV leakEC : ℕ) (Q δ dev ε_AEP εPA β : ℝ) =>
  (ℓ : ℝ) * Real.log 2 + (leakEC : ℝ) * Real.log 2 + (ℓEV : ℝ) * Real.log 2 +
      2 * Real.log (Nat.choose (n + 3) 3 : ℝ) +
      Real.log 2 * renyiPenalty binaryVarianceBound
        (keyRounds n m) ε_AEP β +
      (2 * Real.log (1 / εPA) - 2 * Real.log 2) ≤
    (keyRounds n m : ℝ) * (Real.log 2 - binaryEntropy (Q + δ + dev)))
        n m ℓ ℓEV leakEC Q δ dev ε_AEP εPA β := by
  exact bellRenyiKeyRate_iff n m ℓ ℓEV leakEC Q δ dev ε_AEP εPA β

end QKD.BB84.FiniteKey
end

section
open Matrix Quantum.Operators Quantum.Channels
open QKD.BB84.Measurement QKD.BB84.FiniteKey
open scoped Kronecker
/-- Recording the Bell action uses the natural group label and its exact uniform weight. -/
theorem QKD.BB84.FiniteKey.DefinitionShapes.recordedBellConjugation_eq_formula
    {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R] (ρ : Op (Signals n × R)) :
    recordedConjugation (signalBellUnitary (n := n)) ρ =
      Matrix.of (fun p q => if p.2.2 = q.2.2 then
        (Fintype.card (Fin n → Fin 4) : ℂ)⁻¹ *
          ((signalBellUnitary p.2.2 ⊗ₖ (1 : Op R)) * ρ *
            (signalBellUnitary p.2.2 ⊗ₖ (1 : Op R))ᴴ) (p.1, p.2.1) (q.1, q.2.1)
        else 0) := rfl

end

section
open Quantum.Operators Matrix
open QKD.BB84.Measurement QKD.BB84.FiniteKey
open scoped Kronecker
namespace QKD.BB84.Model.Announced

open scoped Classical in
/-- The branch has its literal acceptance gate, output point and retained reference identity. -/
theorem DefinitionShapes.passKraus_eq_original (E : Type*) (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q =
      (fun ⟨st, ω⟩ => if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        Matrix.single (passOutputIndex n m ℓ ℓEV peSel leakEC ec st ω) ω (1 : ℂ) ⊗ₖ (1 : Op E)
      else 0) := rfl

open scoped Classical in
/-- The branch has its literal acceptance gate, output point and retained reference identity. -/
theorem DefinitionShapes.failKraus_eq_original (E : Type*) (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    failKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q =
      (fun ⟨st, ω⟩ => if ¬ siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        Matrix.single (failOutputIndex n m ℓ ℓEV peSel leakEC ec st ω) ω (1 : ℂ) ⊗ₖ (1 : Op E)
      else 0) := rfl

open scoped Classical in
/-- The branch has its literal acceptance gate, output point and retained reference identity. -/
theorem DefinitionShapes.idealPassKraus_eq_original (E : Type*) (n m ℓ ℓEV : ℕ)
    (peSel xSel : Fin n → Bool) (leakEC : ℕ) (ec : ECScheme n peSel leakEC) (δ Q : ℝ) :
    idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q =
      (fun ⟨ω, k, st⟩ => if siftedLocalPEAndEVPassed ℓEV peSel xSel ec δ Q st.2 ω then
        Matrix.single (idealPassOutputIndex n m ℓ ℓEV peSel leakEC ec k st ω) ω (1 : ℂ) ⊗ₖ
          (1 : Op E)
      else 0) := rfl

end QKD.BB84.Model.Announced
end

section
open scoped ENNReal
namespace QKD.BB84

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.hoeffdingAbortBound_eq_original (N mZ mX : ℕ) (ηS η εEC : ℝ) :
    hoeffdingAbortBound N mZ mX ηS η εEC =
      (fun (N mZ mX : ℕ) (ηS η εEC : ℝ) =>
  2 * Real.exp (-2 * ηS ^ 2 * N) + hoeffdingTestAbortBound mZ mX η εEC) N mZ mX ηS η εEC := by
  unfold hoeffdingAbortBound Math.Concentration.hoeffdingTwoSidedTail
  congr 3
  ring

end QKD.BB84
end

section
open scoped ENNReal
namespace QKD.BB84

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.abortBound_eq_original (N nK mZ mX : ℕ) (pZ pX Q δ q εEC : ℝ) :
    abortBound N nK mZ mX pZ pX Q δ q εEC =
      (fun (N nK mZ mX : ℕ) (pZ pX Q δ q εEC : ℝ) =>
  Real.exp (-(N : ℝ) * Math.Concentration.BernoulliKL.klBer (((nK + mZ : ℝ) - 1) / N) pZ) +
    Real.exp (-(N : ℝ) * Math.Concentration.BernoulliKL.klBer (((mX : ℝ) - 1) / N) pX) +
    testAbortBound mZ mX Q δ q εEC) N nK mZ mX pZ pX Q δ q εEC := by
  rfl

end QKD.BB84
end

section
open scoped ENNReal BigOperators
open LOCC
open QKD.BB84.Measurement
open Math.FiniteEmbedding
namespace QKD.BB84.Sampling

/-- The definition agrees with its explicit formula. -/
theorem DefinitionShapes.totalizedReconstructedStatusRawLaw_eq_original
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    totalizedReconstructedStatusRawLaw N nK mZ mX pA pB hN =
      (fun (N nK mZ mX : ℕ) (pA pB : PMF Basis) (hN : nK + mZ + mX ≤ N) =>
  if hn : nK + mZ + mX = 0 then
    (uniformRetainedSubset hN).bind fun S =>
      (uniformInnerPerm (nK + mZ + mX)).bind fun π =>
        (totalSelectedControlKernel N nK mZ mX pA pB (joinSubsetPerm S π)).bind
          fun omega => PMF.pure (true, omega)
  else
    let j : Fin (nK + mZ + mX) := ⟨0, Nat.pos_of_ne_zero hn⟩
    (selectionStatusLaw N nK mZ mX pA pB).bind fun status =>
      if status then
        (uniformRetainedSubset hN).bind fun S =>
          (uniformInnerPerm (nK + mZ + mX)).bind fun π =>
            (totalSelectedControlKernel N nK mZ mX pA pB (joinSubsetPerm S π)).bind
              fun omega => PMF.pure (true, omega)
      else
        (totalFailureControlKernel N nK mZ mX pA pB j).bind fun omega =>
          PMF.pure (false, omega)) N nK mZ mX pA pB hN := by
  rfl

end QKD.BB84.Sampling
end

