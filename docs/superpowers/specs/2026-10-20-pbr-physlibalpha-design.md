# PBR theorem on the PhyslibAlpha formalism — design

## Intent

The upstream review (2026-10-20, `awaiting-author`) asked that the PBR work stop building on
`QuantumInfo` (which is to be folded into `Physlib`) and instead build on the `ProbabilisticTheory`
/ `QuantumMechanics` formalism of `Physlib` / `PhyslibAlpha`. The user chose a
**quantum-specific** port into **PhyslibAlpha** (Physlib proper cannot import the Alpha measurement
and vector-state API, and Alpha review is lighter).

Success: the same mathematical result — every preparation-independent ontological model of a
finite-dimensional quantum system is ψ-ontic — stated with `𝓗[d]`, Alpha `Measurement`s and vector
states, with no `QuantumInfo` imports, passing all Physlib and PhyslibAlpha linters.

## Goals / non-goals

- Goal: port all five old PRs' content; same theorem strength (arbitrary `n`-copy ontic spaces
  `Λn n` with measurable `ι n`, ket-indexed preparations, Cartesian-product corollary).
- Non-goal: a GPT-general `OntologicalModel` over an arbitrary `OrderUnitSpace` (rejected by the
  user for now).
- Non-goal: touching the old `pbr/*` QuantumInfo branches (left as they are; the user decides
  what to do with the open PR).
- Anti-goal: duplicating Alpha API (POVMs, vector states) instead of using it.

## Building blocks used

| Concept | Upstream API |
|---|---|
| Hilbert space of `d` levels | `QuantumMechanics.FiniteHilbertSpace d` = `𝓗[d]` (Physlib) |
| Observables | `ProbabilisticTheory.Observable (𝓗[d] →L[ℂ] 𝓗[d])` (= `selfAdjoint`, Alpha) |
| Pure state of a unit vector | `UnitalPositiveLinearMap.ofVec (h : ‖ψ‖ = 1)` (Alpha) |
| Born probability | `(ofVec hψ)⟨a⟩` (`expectation`, Alpha) of the outcome effect |
| Finite-outcome measurement | `ProbabilisticTheory.Measurement X E`, built with `Measurement.ofAtoms` (Alpha) |
| Effects | `ProbabilisticTheory.Effect` (Physlib) |
| Rank-one projections, Bessel | Mathlib `InnerProductSpace.rankOne`, `Orthonormal.sum_inner_products_le` |

## Files and contents

### 1. Supporting API

- `PhyslibAlpha/QuantumMechanics/HilbertSpaces/FiniteTarget/ProductState.lean` (existing; new
  section after binary product vectors): `piProdVec (ψ : ι → 𝓗[α]) : 𝓗[ι → α]`,
  `(piProdVec ψ).val k = ∏ i, (ψ i).val (k i)`; `inner_piProdVec` (`⟪⊗ψ, ⊗φ⟫ = ∏ ⟪ψ i, φ i⟫`);
  `norm_piProdVec`, `norm_piProdVec_eq_one`.
- `PhyslibAlpha/ProbabilisticTheory/HilbertSpace/State/Vector.lean` (existing): vector states are
  phase invariant (`ofVec (c • ψ) = ofVec ψ` for `‖c‖ = 1`), hence
  `norm_inner_lt_one_of_ofVec_ne`: unit vectors with different vector states have
  `‖⟪ψ, φ⟫‖ < 1`.
- New file for the measurement of an orthonormal family (general complex Hilbert space `H` if the
  instances allow it, else `𝓗[d]`): `Measurement.ofOrthonormal (b : X → H) (hb : Orthonormal ℂ b)
  (x₀ : X) : Measurement X (Observable (H →L[ℂ] H))`, outcome `x` having effect
  `|b x⟩⟨b x|`, plus the remainder `1 - ∑ y, |b y⟩⟨b y|` on the outcome `x₀`; Born rule lemma
  `(ofVec hφ)⟨M {x}⟩ = ‖⟪b x, φ⟫‖² + if x = x₀ then 1 - ∑ y, ‖⟪b y, φ⟫‖² else 0`.
  Positivity of the remainder is Bessel's inequality.
  (Folding the remainder into `x₀` avoids an `Option` outcome type, which has no
  `MeasurableSpace` instance in Mathlib, and yields the textbook PBR statement below.)
- `Measure.pi_mono` moves to `PhyslibAlpha/Mathematics/MeasureTheory/` (new small file; not in
  Mathlib).

### 2. Ontological models — `PhyslibAlpha/QuantumMechanics/Foundations/OntologicalModel.lean`

`OntologicalModel d Λ`:
- `prep (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1) : Measure Λ`, a probability measure (instance);
- `resp {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  (M : Measurement X (Observable (𝓗[d] →L[ℂ] 𝓗[d]))) : X → Λ → ℝ≥0∞`, measurable, summing to 1;
- Born rule: `∫⁻ l, resp M x l ∂prep ψ hψ = ENNReal.ofReal ((ofVec hψ)⟨M {x} _⟩)`.

`IsPsiOntic`: `ofVec hψ ≠ ofVec hφ → prep ψ hψ ⟂ₘ prep φ hφ`.
`PreparationIndependent M Mn`: measurable `ι n : (Fin n → Λ) → Λn n` with
`(Mn n).prep (piProdVec ψ) _ = (Measure.pi fun i => M.prep (ψ i) (hψ i)).map (ι n)`.
`PreparationIndependent.of_prep_piProd` (Cartesian product assumption).

### 3. PBR — `PhyslibAlpha/QuantumMechanics/Foundations/PBR/`

- `Phases.lean`: moved verbatim (Mathlib-only: `sign`, `walsh`, `exists_phases`, …), plus a
  Walsh Parseval identity replacing the old `Braket.sum_norm_sq_sum_mul_of_orthonormal`.
- `QubitFrame.lean`: `QubitFrame (ψ : Fin 2 → 𝓗[d])` with `e : Fin 2 → 𝓗[d]`,
  `Orthonormal ℂ e`, `⟪e j, ψ b⟫ = phase b * sign j b * ![c, s] j`; built from
  `ψ 0 ± ζ • ψ 1` using inner-product algebra; existence from `‖⟪ψ 0, ψ 1⟫‖ < 1`.
- `Measurement.lean`: product frame vectors `piProdVec (e ∘ z)`, measurement vectors
  `b x = 2^{-n/2} ∑ z, conj (ω z) walsh x z • E z` (orthonormal, orthogonal to `Ψ x`, Parseval on
  product states), and
  `PBR.exists_measurement : ∃ n (M : Measurement (Fin n → Fin 2) _), ∀ x,
  (ofVec _)⟨M {x} _⟩ = 0` on `Ψ x = piProdVec (ψ ∘ x)` — "outcome `x` never occurs on `Ψ x`".
- `Theorem.lean`: classical part unchanged (now indexed by `x` directly);
  `theorem OntologicalModel.PreparationIndependent.isPsiOntic`, listed under `[PhyslibAlpha]` in
  `Theorems.txt`.

## Conventions and checks

- Follow AGENTS.md (module-doc headings, docstrings, `lemma` vs `theorem`, ≤ 50-line proofs,
  references in `docs/references.bib`, spelling exemptions, imports in `PhyslibAlpha.lean`).
- Verify: `lake build PhyslibAlpha` (new modules), `lake exe lint_all`, `theorem_lint`,
  `module_doc_lint`, `auxillary_script_test`, `runPhyslibAlphaLinters`, `noAlphaImports`,
  `alphaFileImports`, `alphaPythonLinters.sh`, `lint-style.sh` (after committing).
- Branch from current `origin/master` (`abd1c0f3`; same toolchain/manifest as the local build).
  Atomic commits per component, then stacked branches for PRs — proposed split:
  (1) supporting API, (2) ontological models, (3) PBR. Push only to `fork`.

## Builder's calls (not discussed with the user)

- Preparations indexed by unit vectors with a norm hypothesis (matching `ofVec`'s style), not a
  sphere subtype.
- The `ofOrthonormal` remainder goes on a chosen outcome `x₀` (rather than an extra outcome).
- New directory `PhyslibAlpha/QuantumMechanics/Foundations/`.
- Three-PR split.
