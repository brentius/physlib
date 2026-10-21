# PBR on PhyslibAlpha Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Re-prove the PBR theorem in PhyslibAlpha on `𝓗[d]`, Alpha `Measurement`s and vector states, with no `QuantumInfo` imports.

**Architecture:** Supporting API in existing Alpha files (product vectors, vector-state phase invariance) plus two small new files (orthonormal measurement, `Measure.pi_mono`); then `OntologicalModel`; then the four PBR files ported from `QuantumInfo/Foundations/PBR/` on the old branch `pbr-theorem` (read old files with `git show pbr-theorem:<path>`).

**Tech Stack:** Lean 4 v4.35.0, Mathlib (local `.lake`, no network cache), Physlib / PhyslibAlpha.

**Spec:** `docs/superpowers/specs/2026-10-20-pbr-physlibalpha-design.md`

## Global Constraints

- Repository: `<repo>` (the physlib checkout), branch `pbr-alpha` (from upstream master). Work in place; never switch branches, never push.
- Lean tools are not on PATH. In Git Bash prefix every command with
  `export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH";`. Build a module with `lake build <Module.Name>`. Never run `lake exe cache get` or any network download (the network blocks the Mathlib cache and repeated blocked requests get the user's internet suspended). Only one `lake` process may run at a time in this checkout: before building, check none is running (PowerShell `Get-Process lake -ErrorAction SilentlyContinue`) and wait if one is.
- No Python in this environment; use the Edit tool or sed for edits.
- `AGENTS.md` (repo root) is binding; read it once. In particular: module docs (`/-! … -/`) with a title `# …`, a one-line summary, `## i. Overview`, `## ii. Key results`, `## iii. Table of contents`, `## iv. References`, then sections `## A. …`, `### A.1. …` listed in the table of contents, no heading ending in a full stop; every `def` has a docstring; use `lemma` (only the final PBR result is a `theorem`); never `sorry`, `axiom`, `True`-valued fields; proofs ≤ 50 lines where possible (comment long ones); no trailing whitespace; hypotheses laid out compactly.
- No `QuantumInfo` import anywhere in new code.
- New files: copyright header `Copyright (c) 2026 brent. All rights reserved.` / `Authors: brent`, `module` keyword, `public import`s, `@[expose] public section` — copy the header shape from `PhyslibAlpha/QuantumMechanics/HilbertSpaces/FiniteTarget/Measurement.lean`. Every new file must be imported (sorted) in `PhyslibAlpha.lean`.
- Namespaces: everything new lives under `QuantumMechanics` (`QuantumMechanics.FiniteHilbertSpace` for Hilbert-space API, `QuantumMechanics.PBR` for PBR internals), except `MeasureTheory.Measure.pi_mono` and the `ProbabilisticTheory.UnitalPositiveLinearMap` lemmas in `Vector.lean`.
- Commits: one per logical unit, title describing the lemmas/definitions added (e.g. `feat(PhyslibAlpha/…): add piProdVec and inner_piProdVec`), body listing them, ending with the trailer line
  `Co-authored-by: Claude Opus 5.5 <no-reply+claude-opus-5-5@anthropic.com>`.
  Stage only the files of your task (`git add <paths>`); the untracked `.claude/`, `.superpowers/` and `docs/superpowers/` must never be committed.
- House idioms (from Alpha): Hilbert space `𝓗[d]` (scoped notation, `open QuantumMechanics` or be inside `namespace QuantumMechanics`); observables `Observable (𝓗[d] →L[ℂ] 𝓗[d])`; vector state `UnitalPositiveLinearMap.ofVec (h : ‖ψ‖ = 1)` (write `ofVec (𝕜 := ℂ) h` when nothing else fixes the field); expectation notation `(ofVec h)⟨a⟩` (scoped in `ProbabilisticTheory.UnitalPositiveLinearMap`; `open ProbabilisticTheory UnitalPositiveLinearMap`); inner product `⟪x, y⟫_ℂ`.

## Review Focus

- `d` with one level: distinct vector states impossible; the theorem is vacuous but must need no extra hypotheses on `d`.
- Vectors differing by a global phase must give the same `ofVec` (Task 1 `ofVec_smul`), so ψ-ontic does not demand singular measures for them.
- `n = 0` copies: `piProdVec` over `Fin 0` is a unit vector; `norm_piProdVec_eq_one` must hold for empty families.
- Remainder outcome `x₀` in `orthonormalMeasurement` when `b` already spans the space: the Born lemma must not assume the remainder is nonzero.
- Name clashes: `lake exe auxillary_script_test` fails on names shared with `Physlib`/`QuantumInfo` — keep the namespaces above.

---

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

### Task 3: Ontological models

**Files:** Create `PhyslibAlpha/QuantumMechanics/Foundations/OntologicalModel.lean` (unverified draft exists); import it in `PhyslibAlpha.lean`; add the bib entries `Harrigan:2007wfc` and `Pusey:2011de` to `docs/references.bib` (copy them verbatim from `git show pbr-theorem:docs/references.bib`, keeping the file's ordering convention); add any new words the spell-checker trips on to `scripts/lint/exemptions/spellingWords.txt` (sorted; the old branch added `epistemic`, `harrigan`, `ontic`, `pusey`, `rudolph`, `spekkens`).

**Consumes:** Tasks 1 and 2 (`piProdVec`, `norm_piProdVec_eq_one`, Alpha `Measurement`).

**Produces (in `QuantumMechanics`):**
- `structure OntologicalModel (d : Type*) [Fintype d] [DecidableEq d] (Λ : Type*) [MeasurableSpace Λ]` with fields `prep (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1) : Measure Λ`; `isProbabilityMeasure_prep` (made an instance); `resp {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] : Measurement X (Observable (𝓗[d] →L[ℂ] 𝓗[d])) → X → Λ → ℝ≥0∞`; `measurable_resp`; `sum_resp (M) (l) : ∑ x, resp M x l = 1`; `lintegral_resp (M) (ψ) (hψ) (x) : ∫⁻ l, resp M x l ∂prep ψ hψ = ENNReal.ofReal ((ofVec hψ)⟨M {x} (measurableSet_singleton x)⟩)`.
- `OntologicalModel.IsPsiOntic (M) : Prop := ∀ (ψ φ : 𝓗[d]) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1), ofVec (𝕜 := ℂ) hψ ≠ ofVec (𝕜 := ℂ) hφ → M.prep ψ hψ ⟂ₘ M.prep φ hφ`.
- `OntologicalModel.PreparationIndependent (M) (Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Λn n)) : Prop := ∃ ι : (n : ℕ) → (Fin n → Λ) → Λn n, (∀ n, Measurable (ι n)) ∧ ∀ n (ψ : Fin n → 𝓗[d]) (hψ : ∀ i, ‖ψ i‖ = 1), (Mn n).prep (piProdVec ψ) (norm_piProdVec_eq_one hψ) = (Measure.pi fun i => M.prep (ψ i) (hψ i)).map (ι n)`.
- `OntologicalModel.PreparationIndependent.of_prep_piProdVec` (Cartesian product assumption ⇒ preparation independence, `ι n = id`).

- [ ] `lake build PhyslibAlpha.QuantumMechanics.Foundations.OntologicalModel` → no errors/new warnings; `lake exe module_doc_lint` passes for the file.
- [ ] One commit (file + bib + spelling + `PhyslibAlpha.lean`).

### Task 4: Walsh phases and the qubit frame

**Files:**
- Create `PhyslibAlpha/QuantumMechanics/Foundations/PBR/Phases.lean` (draft exists: the old `pbr-theorem:QuantumInfo/Foundations/PBR/Phases.lean`, moved into `namespace QuantumMechanics.PBR`, plus the new lemma `sum_norm_sq_sum_mul_inv_sqrt_mul_walsh (n) (β) : ∑ x, ‖∑ z, β z * ((√(2 ^ n))⁻¹ * walsh x z)‖ ^ 2 = ∑ z, ‖β z‖ ^ 2` at the end of section D).
- Create `PhyslibAlpha/QuantumMechanics/Foundations/PBR/QubitFrame.lean` — port of `pbr-theorem:QuantumInfo/Foundations/PBR/QubitFrame.lean` from `Ket`/bra-kets to `𝓗[d]` and inner products (no draft).
- Import both in `PhyslibAlpha.lean`; spelling words as needed (`bernoulli`, `walsh`, `qubit`, `parseval`).

**Consumes:** Task 1 (`norm_inner_lt_one_of_ofVec_ne` is NOT needed here; `exists_qubitFrame` takes the norm hypothesis directly).

**Produces (in `QuantumMechanics.PBR`; `variable {d : Type*} [Fintype d] [DecidableEq d]`):**
- `structure QubitFrame (ψ : Fin 2 → 𝓗[d])` with fields `e : Fin 2 → 𝓗[d]`, `c s : ℝ`, `phase : Fin 2 → ℂ`, `s_pos : 0 < s`, `s_le_c : s ≤ c`, `sq_add_sq : c ^ 2 + s ^ 2 = 1`, `norm_phase (b) : ‖phase b‖ = 1`, `orthonormal_e : Orthonormal ℂ e`, `inner_e_state (j b : Fin 2) : ⟪e j, ψ b⟫_ℂ = phase b * sign j b * ![(c : ℂ), (s : ℂ)] j` (field docstrings as in the old file).
- `QubitFrame.c_pos`, `QubitFrame.sum_norm_sq_inner_e_state (F) (b) : ∑ j, ‖⟪F.e j, ψ b⟫_ℂ‖ ^ 2 = 1`.
- `QubitFrame.ofPhase (ψ) (hψ : ∀ b, ‖ψ b‖ = 1) {ζ : ℂ} {r : ℝ} (hζ : ‖ζ‖ = 1) (hr : ζ * ⟪ψ 0, ψ 1⟫_ℂ = r) (hr0 : 0 ≤ r) (hr1 : r < 1) : QubitFrame ψ` with `e = ![(√(2 * (1 + r)))⁻¹ • u, (√(2 * (1 - r)))⁻¹ • v]` (real scalars, or their complex casts) for `u = ψ 0 + ζ • ψ 1`, `v = ψ 0 - ζ • ψ 1`; `c = √((1 + r) / 2)`, `s = √((1 - r) / 2)`, `phase = ![1, star ζ]`.
- `exp_neg_arg_mul_self` (kept), `exists_qubitFrame (ψ) (hψ : ∀ b, ‖ψ b‖ = 1) (h : ‖⟪ψ 0, ψ 1⟫_ℂ‖ < 1) : Nonempty (QubitFrame ψ)` (ζ = `exp (-i arg γ)`, r = `‖γ‖`).

**The algebra (γ = ⟪ψ 0, ψ 1⟫, ζγ = r, ‖ζ‖ = 1, unit ψ b; Mathlib inner products are conjugate-linear in the first slot):** `⟪u, ψ 0⟫ = 1 + r`, `⟪u, ψ 1⟫ = conj ζ * (1 + r)`, `⟪v, ψ 0⟫ = 1 - r`, `⟪v, ψ 1⟫ = -(conj ζ * (1 - r))`, `⟪u, v⟫ = 0`, `‖u‖ ^ 2 = 2 * (1 + r)`, `‖v‖ ^ 2 = 2 * (1 - r)`, and `(1 ± r) / √(2 * (1 ± r)) = √((1 ± r) / 2)`. Replace the old section A (bra-ket lemmas on `ψ.vec ± ζ • φ.vec`) by inner-product lemmas of this shape; drop lemmas that become one-liners. The old `lt_one_of_pure_ne` is not ported.

- [ ] `lake build PhyslibAlpha.QuantumMechanics.Foundations.PBR.QubitFrame` (builds Phases too) → no errors/new warnings.
- [ ] Two commits (Phases; QubitFrame).

### Task 5: The PBR measurement and the PBR theorem

**Files:**
- Create `PhyslibAlpha/QuantumMechanics/Foundations/PBR/Measurement.lean` — port of `pbr-theorem:QuantumInfo/Foundations/PBR/Measurement.lean`.
- Create `PhyslibAlpha/QuantumMechanics/Foundations/PBR/Theorem.lean` — port of `pbr-theorem:QuantumInfo/Foundations/PBR/Theorem.lean` (the classical part, section A, is unchanged apart from namespace).
- Import both in `PhyslibAlpha.lean`; add `QuantumMechanics.OntologicalModel.PreparationIndependent.isPsiOntic` under `[PhyslibAlpha]` in `scripts/lint/exemptions/Theorems.txt` (sorted); spelling words as needed.

**Consumes:** `piProdVec`, `inner_piProdVec`, `norm_piProdVec_eq_one`, `norm_inner_lt_one_of_ofVec_ne` (Task 1); `orthonormalMeasurement`, `expectation_orthonormalMeasurement` (Task 2); `OntologicalModel`, `PreparationIndependent`, `IsPsiOntic` (Task 3); `QubitFrame`, `exists_qubitFrame`, `walsh` lemmas, `exists_two_mul_pow_le`, `exists_phases`, `sum_norm_sq_sum_mul_inv_sqrt_mul_walsh` (Task 4); `MeasureTheory.Measure.pi_mono` (Task 1).

**Produces (Measurement.lean, `QuantumMechanics.PBR.QubitFrame` namespace, `{n : ℕ}`):**
- `frameVec (F : QubitFrame ψ) (z : Fin n → Fin 2) : 𝓗[Fin n → d] := piProdVec fun i => F.e (z i)`; `inner_frameVec_frameVec : ⟪F.frameVec z, F.frameVec z'⟫_ℂ = if z = z' then 1 else 0`; `inner_frameVec_piProdVec (z x) : ⟪F.frameVec z, piProdVec fun i => ψ (x i)⟫_ℂ = (∏ i, F.phase (x i)) * walsh z x * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i)`; `sum_norm_sq_inner_frameVec_piProdVec (y) : ∑ z, ‖⟪F.frameVec z, piProdVec fun i => ψ (y i)⟫_ℂ‖ ^ 2 = 1`.
- `measurementVec (F) (ω : (Fin n → Fin 2) → ℂ) (x : Fin n → Fin 2) : 𝓗[Fin n → d] := ∑ z, ((Real.sqrt (2 ^ n))⁻¹ * starRingEnd ℂ (ω z) * walsh x z) • F.frameVec z` (no norm hypothesis in the definition); `inner_measurementVec`; `orthonormal_measurementVec (hω : ∀ z, ‖ω z‖ = 1) : Orthonormal ℂ (F.measurementVec ω)`; `inner_measurementVec_piProdVec_self (hsum : ∑ z, ω z * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i) = 0) (x) : ⟪F.measurementVec ω x, piProdVec fun i => ψ (x i)⟫_ℂ = 0`; `sum_norm_sq_inner_measurementVec (hω) (y) : ∑ x, ‖⟪F.measurementVec ω x, piProdVec fun i => ψ (y i)⟫_ℂ‖ ^ 2 = 1`.
- `PBR.exists_measurement (ψ : Fin 2 → 𝓗[d]) (hψ : ∀ b, ‖ψ b‖ = 1) (h : ofVec (𝕜 := ℂ) (hψ 0) ≠ ofVec (𝕜 := ℂ) (hψ 1)) : ∃ (n : ℕ) (M : Measurement (Fin n → Fin 2) (Observable (𝓗[Fin n → d] →L[ℂ] 𝓗[Fin n → d]))), ∀ x, (ofVec (norm_piProdVec_eq_one fun i => hψ (x i)))⟨M {x} (measurableSet_singleton x)⟩ = 0` — "outcome `x` never occurs on `ψ (x 0) ⊗ ⋯ ⊗ ψ (x (n - 1))`". Use `orthonormalMeasurement (orthonormal_measurementVec …) 0`: for `x ≠ 0` the probability is `‖⟪b x, Ψ x⟫‖ ^ 2 = 0`; for `x = 0` add the remainder `1 - ∑ y, ‖⟪b y, Ψ 0⟫‖ ^ 2 = 0` by Parseval.

**Produces (Theorem.lean):** `PBR.eq_zero_of_le_of_exists_lintegral_eq_zero`, `PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero` (unchanged statements), and
`theorem QuantumMechanics.OntologicalModel.PreparationIndependent.isPsiOntic {d Λ : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Λ] {M : OntologicalModel d Λ} {Λn : ℕ → Type*} [∀ n, MeasurableSpace (Λn n)] {Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Λn n)} (h : M.PreparationIndependent Mn) : M.IsPsiOntic` with the old docstring (bold title **Pusey–Barrett–Rudolph theorem.**), adapted.

- [ ] `lake build PhyslibAlpha.QuantumMechanics.Foundations.PBR.Theorem` → no errors/new warnings.
- [ ] Two commits (Measurement; Theorem + Theorems.txt).

### Task 6: Whole-repo verification

- [ ] `lake build PhyslibAlpha` (full library) → success.
- [ ] Run and pass: `lake exe lint_all`; `lake exe theorem_lint`; `lake exe module_doc_lint`; `lake exe forMathlib_lint`; `lake exe auxillary_script_test`; `lake exe runPhyslibAlphaLinters`; `lake exe noAlphaImports`; `lake exe alphaFileImports`; `./scripts/lint/required/alpha/alphaPythonLinters.sh` (skip and report if it needs Python, which is absent); `./scripts/lint/required/lint-style.sh` (reads committed state). Fix any failure in the file that caused it, in a separate commit per fix (title naming what was fixed).
