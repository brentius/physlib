### Task 2: Measurement in an orthonormal family

**Files:** Create `PhyslibAlpha/QuantumMechanics/HilbertSpaces/FiniteTarget/Measurement.lean` (unverified draft exists in the working tree); import it in `PhyslibAlpha.lean`.

**Consumes:** Alpha `ProbabilisticTheory.Measurement`, `Measurement.ofAtoms`, `Measurement.coe_ofAtoms_singleton` (`PhyslibAlpha/ProbabilisticTheory/Measurement/Finite.lean`), `selfAdjoint` order-unit instances (`PhyslibAlpha/ProbabilisticTheory/CStarAlgebra/OrderUnit.lean`), operator instances on `𝓗[d]` (`…/FiniteTarget/Operators.lean`), `apply_observable_eq_expectation` (`…/StarAlgebra/Statistics.lean`); Mathlib `InnerProductSpace.rankOne`, `isPositive_rankOne_self`, `ContinuousLinearMap.nonneg_iff_isPositive`, `ContinuousLinearMap.isPositive_iff'`, `Orthonormal.sum_inner_products_le` (Bessel).

**Produces (in `QuantumMechanics.FiniteHilbertSpace`):**
- `rankOneObservable (v : 𝓗[d]) : Observable (𝓗[d] →L[ℂ] 𝓗[d])` (`|v⟩⟨v|`), `rankOneObservable_nonneg`.
- `orthonormalObservable (b : X → 𝓗[d]) (x₀ x : X) : Observable (𝓗[d] →L[ℂ] 𝓗[d]) := rankOneObservable (b x) + if x = x₀ then 1 - ∑ y, rankOneObservable (b y) else 0`; `sum_orthonormalObservable : ∑ x, orthonormalObservable b x₀ x = 1`; `orthonormalObservable_nonneg (hb : Orthonormal ℂ b)`.
- `orthonormalMeasurement {b : X → 𝓗[d]} (hb : Orthonormal ℂ b) (x₀ : X) [MeasurableSpace X] : Measurement X (Observable (𝓗[d] →L[ℂ] 𝓗[d]))` (built with `Measurement.ofAtoms`).
- `expectation_orthonormalMeasurement [MeasurableSingletonClass X] (hb) (x₀) {φ} (hφ : ‖φ‖ = 1) (x : X) : (ofVec hφ)⟨orthonormalMeasurement hb x₀ {x} (measurableSet_singleton x)⟩ = ‖⟪b x, φ⟫_ℂ‖ ^ 2 + if x = x₀ then 1 - ∑ y, ‖⟪b y, φ⟫_ℂ‖ ^ 2 else 0`.
  (`X` has `[Fintype X] [DecidableEq X]`.)

- [ ] `lake build PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.Measurement` → no errors, no new warnings. If an instance search on `𝓗[d] →L[ℂ] 𝓗[d]` times out, see the comment in `…/FiniteTarget/Operators.lean` and register what is missing there rather than raising `maxHeartbeats`.
- [ ] One commit.

