# Task 2 report: measurement in an orthonormal family

Status: DONE. Commit `c50d1136 feat(PhyslibAlpha/FiniteTarget): add orthonormalMeasurement and its Born rule`.

## Implemented

File `PhyslibAlpha/QuantumMechanics/HilbertSpaces/FiniteTarget/Measurement.lean`, namespace
`QuantumMechanics.FiniteHilbertSpace` (imported in `PhyslibAlpha.lean`, sorted).

Brief names/signatures (verbatim):
- `rankOneObservable (v : 𝓗[d]) : Observable (𝓗[d] →L[ℂ] 𝓗[d])`, `rankOneObservable_nonneg`
- `orthonormalObservable (b : X → 𝓗[d]) (x₀ x : X)` := `rankOneObservable (b x) + if x = x₀ then 1 - ∑ y, rankOneObservable (b y) else 0`
- `sum_orthonormalObservable : ∑ x, orthonormalObservable b x₀ x = 1`
- `orthonormalObservable_nonneg (hb : Orthonormal ℂ b) (x₀ x)`
- `orthonormalMeasurement {b} (hb) (x₀) [MeasurableSpace X] : Measurement X (Observable …)` via `Measurement.ofAtoms`
- `expectation_orthonormalMeasurement [MeasurableSingletonClass X] (hb) (x₀) {φ} (hφ : ‖φ‖ = 1) (x)` with the exact RHS of the brief. No hypothesis on the remainder being nonzero.

Supporting API: `coe_rankOneObservable`, `inner_rankOne_self_apply`, `inner_sum_rankOne_self_apply`,
`isPositive_one_sub_sum_rankOne` (Bessel), `coe_orthonormalObservable`, `orthonormalEffect`,
`coe_orthonormalEffect`, `coe_orthonormalMeasurement_singleton`.

## Fixes to the draft

- `Measurement.ofAtoms` failed to elaborate (expected `selfAdjoint.instIsOrderUnit`, got
  `ArchimedeanOrderUnitSpace.toOrderUnitSpace ?m` with `E` still a metavariable). Fixed by passing
  `(E := Observable (𝓗[d] →L[ℂ] 𝓗[d]))`; the instances are defeq (checked in scratch with
  `with_reducible_and_instances rfl`), no Operators.lean change needed.
- Deprecated names replaced (`sub_apply`, `sum_apply`, `one_apply_eq_self`, `add_apply`, `zero_apply`); `IsSelfAdjoint.one _`.
- Bessel positivity step: `norm_cast` leaves an RCLike coercion; a `change` to `Complex.ofReal` form then `← Complex.ofReal_sub, conj_ofReal, zero_le_real, sub_nonneg`.
- `[DecidableEq X]` moved to section B (unused-section-variable warnings).
- Born rule: rewrite through `coe_orthonormalMeasurement_singleton`, `ofVec_apply`,
  `ContinuousLinearMap.smul_def`, `coe_orthonormalObservable`, then `split_ifs`.

## Build

```
lake build PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.Measurement
Build completed successfully (3241 jobs).
```
No errors, no warnings. `lake exe module_doc_lint`: no entries for this file (the tool reports
pre-existing problems in other files). No lines over 100 characters, no trailing whitespace.

## Files changed

- `PhyslibAlpha/QuantumMechanics/HilbertSpaces/FiniteTarget/Measurement.lean` (new)
- `PhyslibAlpha.lean` (import)

## Concerns

- Not run: `lake build` of the whole project, `lint_all`, `theorem_lint`, `auxillary_script_test`,
  `lint-style.sh` (whole-project, slow). Name clash check: all new names live in
  `QuantumMechanics.FiniteHilbertSpace`.
- Extra declarations beyond the brief (`orthonormalEffect`, coe/inner lemmas,
  `coe_orthonormalMeasurement_singleton`) are the minimal API to build and compute the measurement.
