# Task 5 report: PBR measurement and PBR theorem

**Status:** DONE

## Commits
- `7a2ae785` feat(PhyslibAlpha/PBR): add the PBR measurement vectors and exists_measurement
  (Measurement.lean + its import in PhyslibAlpha.lean)
- `eb94e0a6` feat(PhyslibAlpha/PBR): add the Pusey-Barrett-Rudolph theorem
  (Theorem.lean + its import + Theorems.txt)

## Files
- `PhyslibAlpha/QuantumMechanics/Foundations/PBR/Measurement.lean` (new), namespace
  `QuantumMechanics.PBR`: `QubitFrame.frameVec`, `inner_frameVec_frameVec`,
  `inner_frameVec_piProdVec`, `sum_norm_sq_inner_frameVec_piProdVec`, `measurementVec`,
  `inner_measurementVec`, `inner_frameVec_measurementVec` (helper, extra), 
  `orthonormal_measurementVec`, `inner_measurementVec_piProdVec_self`,
  `sum_norm_sq_inner_measurementVec`, `exists_measurement`.
- `PhyslibAlpha/QuantumMechanics/Foundations/PBR/Theorem.lean` (new):
  `PBR.eq_zero_of_le_of_exists_lintegral_eq_zero`,
  `PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero` (verbatim port),
  `theorem OntologicalModel.PreparationIndependent.isPsiOntic` (all under `QuantumMechanics`),
  with the bold-titled docstring adapted to unit vectors / vector states / Born rule.
- `PhyslibAlpha.lean`: both modules imported, sorted.
- `scripts/lint/exemptions/Theorems.txt`: `QuantumMechanics.OntologicalModel.PreparationIndependent.isPsiOntic`
  added under `[PhyslibAlpha]`, after the `QuantumMechanics.HarmonicOscillator.*` entries (the section
  is not globally sorted; placed in local alphabetical order).
- Spelling words: none needed (Parseval, Walsh, Pusey, Barrett, Rudolph, ontic, Spekkens, Harrigan,
  Leifer, Bessel already present).
- `OntologicalModel.lean` forward reference unchanged (theorem name kept).

## Deviation (cosmetic only)
- `exists_measurement` binder written `∀ x : Fin n → Fin 2, ...` instead of `∀ x, ...`: with the
  untyped binder, elaborating `hψ (x i)` before `x`'s type is fixed hit a `whnf` heartbeat timeout
  (line 193:50). The statement is identical.

## Verification
- `lake build PhyslibAlpha.QuantumMechanics.Foundations.PBR.Theorem`:
  `Built ...PBR.Measurement (358s)`, `Built ...PBR.Theorem (69s)`, `Build completed successfully
  (3268 jobs)`; 0 warnings in the log.
- `lake exe module_doc_lint`: reports only pre-existing problems in other files; none in the new
  PBR files.
- No lines > 100 chars, no trailing whitespace.
- Not run (time/scope): lint_all, theorem_lint, auxillary_script_test, lint-style.sh, Alpha linters
  (these need full library builds; this machine takes hours for those).

## Concerns
- Measurement.lean takes ~6 min to elaborate on this machine; no single proof was profiled.
