import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricAEP.CorrectionAndWitness
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricAEP.Transport
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.SymmetricAEP.MainBound

/-!
# Symmetric-state AEP corrections

The symmetric-state estimates use real entropy rates and finite-size corrections measured
in bits. Component IID witnesses give canonical extended smooth entropy floors; register
transport and finite-mixture constructions assemble the corresponding bounds.
-/

/-!
## Module organization (re-export hub)

This module is a thin re-export hub. Its declarations live, unchanged, in three
dependency-ordered sub-modules under `SymmetricAEP/`:

- `SymmetricAEP/CorrectionAndWitness.lean` — AEP correction term + properties, the
  symmetric-subspace and CQ-channel-image witnesses, the conditional VN entropy
  definitions, the per-component image/reference, and the nonneg/posdef helpers.
- `SymmetricAEP/Transport.lean` — Renner Step A/B/C transport, reindex/relabel
  invariance, per-component product factorization, and the superposition
  reference pin.
- `SymmetricAEP/MainBound.lean` — dephasing/counting bounds and correction-term
  aggregation, ending at `aep_correction_distvN_aggregation`. It does NOT contain a
  per-round smooth min-entropy lower bound; see
  `smoothMinEntropy_tensorPower_ge_classical_aep_floor`.

Importing this hub resolves every name exactly as before the split.
-/
