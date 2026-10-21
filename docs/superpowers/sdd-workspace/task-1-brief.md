### Task 1: Product vectors, phase invariance of vector states, `Measure.pi_mono`

**Files (unverified drafts already exist in the working tree — compile, fix, finish):**
- Modify: `PhyslibAlpha/QuantumMechanics/HilbertSpaces/FiniteTarget/ProductState.lean` — new section `F. Product vectors of finite families` (draft at end of file; module doc already updated).
- Modify: `PhyslibAlpha/ProbabilisticTheory/HilbertSpace/State/Vector.lean` — new section `B. Phase invariance` (draft), old `B. Example` renamed `C. Example`.
- Create: `PhyslibAlpha/Mathematics/MeasureTheory/Pi.lean` — draft copied from `pbr-theorem:QuantumInfo/ForMathlib/MeasureTheory/Pi.lean`.
- Modify: `PhyslibAlpha.lean` — import `PhyslibAlpha.Mathematics.MeasureTheory.Pi` (sorted).

**Produces (exact names/signatures):**
- `QuantumMechanics.FiniteHilbertSpace.piProdVec {ι} [Fintype ι] [DecidableEq ι] (v : ι → 𝓗[α]) : 𝓗[ι → α]`, `piProdVec_val`, `inner_piProdVec (v w : ι → 𝓗[α]) : ⟪piProdVec v, piProdVec w⟫_ℂ = ∏ i, ⟪v i, w i⟫_ℂ`, `norm_piProdVec (v) : ‖piProdVec v‖ = ∏ i, ‖v i‖`, `norm_piProdVec_eq_one {v} (hv : ∀ i, ‖v i‖ = 1) : ‖piProdVec v‖ = 1`.
- `ProbabilisticTheory.UnitalPositiveLinearMap.ofVec_smul {ψ : H} (h : ‖ψ‖ = 1) {c : 𝕜} (hc : ‖c‖ = 1) (h' : ‖c • ψ‖ = 1) : ofVec (𝕜 := 𝕜) h' = ofVec (𝕜 := 𝕜) h`.
- `ProbabilisticTheory.UnitalPositiveLinearMap.norm_inner_lt_one_of_ofVec_ne {ψ φ : H} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (h : ofVec (𝕜 := 𝕜) hψ ≠ ofVec (𝕜 := 𝕜) hφ) : ‖⟪ψ, φ⟫_𝕜‖ < 1` (proof: Cauchy–Schwarz, and Mathlib's `norm_inner_eq_norm_iff` in the equality case gives `φ = c • ψ`).
- `MeasureTheory.Measure.pi_mono (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν`.

- [ ] `lake build PhyslibAlpha.Mathematics.MeasureTheory.Pi PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.Vector PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.ProductState` → builds with no errors and no new warnings.
- [ ] Three commits: `Measure.pi_mono`; `piProdVec`; `ofVec_smul`/`norm_inner_lt_one_of_ofVec_ne`.

