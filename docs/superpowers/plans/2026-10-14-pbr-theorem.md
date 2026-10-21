# PBR Theorem Formalisation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A complete, `sorry`-free Lean 4 proof of the general Pusey–Barrett–Rudolph theorem in physlib's `QuantumInfo` library.

**Architecture:** Definitions of ontological models live in `QuantumInfo/Foundations/OntologicalModel.lean`; the PBR proof is split into pure combinatorics/analysis (`PBR/Phases.lean`), the single-system frame (`PBR/QubitFrame.lean`), the `n`-copy entangled measurement (`PBR/Measurement.lean`) and the measure-theoretic argument plus main theorem (`PBR/Theorem.lean`). General lemmas go into existing files (`Braket.lean`, `POVM.lean`) or a QuantumInfo `ForMathlib` file.

**Tech Stack:** Lean 4.34.1, Mathlib v4.34.1, physlib `QuantumInfo` (`Ket`, `Ket.piProd`, `Braket.dot`, `MState.pure`, `POVM`, `POVM.measure`).

**Spec:** `docs/superpowers/specs/2026-10-14-pbr-theorem-design.md` (read it: it contains the full proof outline and every formula used below).

## Global Constraints

- Repo root: `<repo>`, branch `pbr-theorem`. Never push, never open a PR.
- Every shell needs Lean on PATH. PowerShell: `$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"`; Git Bash: `export PATH="$HOME/.elan/bin:$PATH"`. For any download (`lake exe cache get` etc.) also set `CURL_HOME=<scratchpad>\curlhome`.
- Scratch tests live in `<scratchpad>\pbr-tests\` (call it `$T`). They are never committed. Run one with `lake env lean $T\TaskN.lean` from the repo root, after `lake build <Module>` for the module under test.
- `lakefile.toml` passes `-Dwarn.sorry=false`: a `sorry` produces **no warning**. Every test file ends with `#print axioms <main decl of the task>` and the output must list only `propext`, `Classical.choice`, `Quot.sound` (any subset). `sorryAx` or `Lean.ofReduceBool` = failure.
- Follow `AGENTS.md` exactly: `lemma` not `theorem` (only the main PBR theorem is a `theorem`); every `def`/`structure`/field has a docstring; no `axiom`, `sorry`, `True`-valued fields; no trailing whitespace; lines ≤ 100 chars; proofs < 50 lines (split otherwise, by meaning); module doc headings `# Title` + one-line summary, `## i. Overview`, `## ii. Key results`, `## iii. Table of contents`, `## iv. References`, then `## A. …`, `### A.1. …` listed in the ToC; no heading ends in a full stop.
- File header: `/-` / `Copyright (c) 2026 brent. All rights reserved.` / `Released under Apache 2.0 license as described in the file LICENSE.` / `Authors: brent` / `-/`, then `module`, `public import …` lines, module doc, `@[expose] public section` (match `QuantumInfo/States/Pure/Braket.lean`).
- New modules are added to `QuantumInfo.lean` in sorted position.
- Commits: one per task, title naming the lemmas/defs added, ending with the trailer `Co-authored-by: Claude Opus 5.5 <no-reply+claude-opus-5-5@anthropic.com>`. Never `--no-verify`.
- Bra-ket notation `〈ψ‖φ〉` is `scoped` in `Braket`: use `open Braket` where needed. `〈ψ‖φ〉 = ∑ i, conj (ψ i) * φ i`.

## Review Focus

1. Vacuity: the `OntologicalModel` structure could be unsatisfiable (wrong universe, Born rule mistyped), making the theorem trivially true. Task 4's test builds the Beltrametti–Bugajski model as an `OntologicalModel` and proves it `IsPsiOntic`.
2. Outcome `none` of the PBR POVM must have probability 0 on **every** product state, not just one; Task 7's test checks `sum_norm_sq_dot_measurementKet` for arbitrary `y`.
3. Orthogonal input states (`〈ψ₀‖ψ₁〉 = 0`, so `c = s`, `arg 0 = 0`) must not be excluded by a strict inequality; Task 5/6 hypotheses use `s ≤ c` and `0 ≤ r`, never `s < c`.
4. `n = 0` copies: the classical lemma must not assume `n ≠ 0` (Task 8 test instantiates it with an arbitrary `n`).
5. Phase-equivalent but unequal kets: hypotheses use `MState.pure ψ ≠ MState.pure φ`, not `ψ ≠ φ` (Task 8 test applies the theorem to a pair stated that way).

---

### Task 1: Monotonicity of product measures

**Files:**
- Create: `QuantumInfo/ForMathlib/MeasureTheory/Pi.lean`
- Modify: `QuantumInfo.lean` (add import, sorted)
- Test: `$T\Task1.lean`

**Interfaces:**
- Produces: `MeasureTheory.Measure.pi_mono {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)] {μ ν : (i : ι) → Measure (α i)} (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν`

- [ ] **Step 1: Write the failing test** `$T\Task1.lean`: `import QuantumInfo.ForMathlib.MeasureTheory.Pi`, then
  `example {α : Type*} [MeasurableSpace α] (μ ν : Measure α) (h : μ ≤ ν) (n : ℕ) : Measure.pi (fun _ : Fin n => μ) ≤ Measure.pi (fun _ => ν) := Measure.pi_mono fun _ => h` and `#print axioms MeasureTheory.Measure.pi_mono`.
- [ ] **Step 2: Run it** — `lake env lean $T\Task1.lean`; expected: unknown module error.
- [ ] **Step 3: Implement** in the new file. Approach: `Measure.le_iff` (measurable sets), unfold `Measure.pi` with `toMeasure_apply` (as in Mathlib `Constructions/Pi.lean:220`), then `OuterMeasure.le_pi` + `OuterMeasure.pi_pi_le` + `Finset.prod_le_prod'` + `Measure.le_iff'`.
- [ ] **Step 4: Build and test** — `lake build QuantumInfo.ForMathlib.MeasureTheory.Pi` then the test; expected: no errors, axioms ⊆ {propext, Classical.choice, Quot.sound}.
- [ ] **Step 5: Commit** — `feat(QuantumInfo/ForMathlib): add Measure.pi_mono`.

### Task 2: Bra-ket of product kets

**Files:**
- Modify: `QuantumInfo/States/Pure/Braket.lean` (after `Ket.piProd_apply`, section `prod`)
- Test: `$T\Task2.lean`

**Interfaces:**
- Produces: `Braket.dot_piProd {ι : Type*} [DecidableEq ι] [Fintype ι] {d : ι → Type*} [∀ i, Fintype (d i)] (ψ φ : (i : ι) → Ket (d i)) : 〈Ket.piProd ψ‖Ket.piProd φ〉 = ∏ i, 〈ψ i‖φ i〉`

- [ ] **Step 1: Test** `$T\Task2.lean`: import `QuantumInfo.States.Pure.Braket`, `open Braket`, an `example` restating the signature `:= Braket.dot_piProd ψ φ`, `#print axioms Braket.dot_piProd`.
- [ ] **Step 2: Run** — expect unknown identifier.
- [ ] **Step 3: Implement** with `Finset.prod_univ_sum`/`Fintype.prod_sum` and `map_prod` for `conj`.
- [ ] **Step 4: Build** `lake build QuantumInfo.States.Pure.Braket`, run test; expected pass.
- [ ] **Step 5: Commit** — `feat(QuantumInfo/Braket): add Braket.dot_piProd`.

### Task 3: POVM from an orthonormal family of kets

**Files:**
- Modify: `QuantumInfo/Measurements/POVM.lean` (new section at end of `namespace POVM`, before `end POVM`)
- Test: `$T\Task3.lean`

**Interfaces:**
- Consumes: `MState.pure`, `MState.val_inner`, `MState.pure_inner`, `HermitianMat.le_iff`/`zero_le_iff`, `Matrix.vecMulVec_mul_vecMulVec`, `Matrix.posSemidef_conjTranspose_mul_self`.
- Produces (all with `{X d : Type*} [Fintype X] [DecidableEq X] [Fintype d] [DecidableEq d] (b : X → Ket d) (hb : ∀ x y, 〈b x‖b y〉 = if x = y then 1 else 0)`):
  - `POVM.ofOrthonormal b hb : POVM (Option X) d` — `mats (some x) = (MState.pure (b x)).M`, `mats none = 1 - ∑ x, (MState.pure (b x)).M`.
  - `POVM.measure_ofOrthonormal_some (ψ : Ket d) (x : X) : ((POVM.ofOrthonormal b hb).measure (MState.pure ψ) (some x) : ℝ) = ‖〈b x‖ψ〉‖ ^ 2`
  - `POVM.measure_ofOrthonormal_none (ψ : Ket d) : ((POVM.ofOrthonormal b hb).measure (MState.pure ψ) none : ℝ) = 1 - ∑ x, ‖〈b x‖ψ〉‖ ^ 2`

- [ ] **Step 1: Test** `$T\Task3.lean`: import `QuantumInfo.Measurements.POVM`; `example`s instantiating both measure lemmas with `X := Fin 2`, `d := Fin 2`, `b := Ket.basis`-based family is optional — restating the signatures with variables suffices; `#print axioms POVM.measure_ofOrthonormal_none`.
- [ ] **Step 2: Run** — expect unknown identifiers.
- [ ] **Step 3: Implement.** Nonnegativity of `none`: with `P = ∑ x, vecMulVec (b x) (star (b x))`, show `P * P = P` and `Pᴴ = P`, so `1 - P = (1 - P)ᴴ * (1 - P)` is PSD. `some x` probability: `MState.val_inner` + `MState.pure_inner`. `none` probability: from `ProbDistribution.normalized` and `Fintype.sum_option`.
- [ ] **Step 4: Build** `lake build QuantumInfo.Measurements.POVM` (rebuilds the chain from `Braket`; may take a while), run test; pass.
- [ ] **Step 5: Commit** — `feat(QuantumInfo/POVM): add POVM.ofOrthonormal and its outcome probabilities`.

### Task 4: Ontological models

**Files:**
- Create: `QuantumInfo/Foundations/OntologicalModel.lean`; Modify: `QuantumInfo.lean`
- Test: `$T\Task4.lean`

**Interfaces:**
- Produces:
```lean
structure OntologicalModel (d : Type*) [Fintype d] [DecidableEq d] (Λ : Type*) [MeasurableSpace Λ] where
  prep : Ket d → Measure Λ
  isProbabilityMeasure_prep (ψ : Ket d) : IsProbabilityMeasure (prep ψ)
  resp {X : Type} [Fintype X] [DecidableEq X] : POVM X d → X → Λ → ℝ≥0∞
  measurable_resp {X : Type} [Fintype X] [DecidableEq X] (E : POVM X d) (x : X) : Measurable (resp E x)
  sum_resp {X : Type} [Fintype X] [DecidableEq X] (E : POVM X d) (l : Λ) : ∑ x, resp E x l = 1
  lintegral_resp {X : Type} [Fintype X] [DecidableEq X] (E : POVM X d) (ψ : Ket d) (x : X) :
    ∫⁻ l, resp E x l ∂prep ψ = ENNReal.ofReal (E.measure (MState.pure ψ) x)
-- attribute [instance] OntologicalModel.isProbabilityMeasure_prep
def OntologicalModel.IsPsiOntic (M : OntologicalModel d Λ) : Prop :=
  ∀ ψ φ : Ket d, MState.pure ψ ≠ MState.pure φ → M.prep ψ ⟂ₘ M.prep φ
def OntologicalModel.PreparationIndependent (M : OntologicalModel d Λ)
    (Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Fin n → Λ)) : Prop :=
  ∀ (n : ℕ) (ψ : Fin n → Ket d), (Mn n).prep (Ket.piProd ψ) = Measure.pi fun i => M.prep (ψ i)
```
  Docstrings explain the physics (Harrigan–Spekkens ontological models; PBR preparation independence).

- [ ] **Step 1: Test** `$T\Task4.lean`: build the Beltrametti–Bugajski model `bb : OntologicalModel (Fin 2) (Ket (Fin 2))` with `letI : MeasurableSpace (Ket (Fin 2)) := ⊤`, `prep ψ := Measure.dirac ψ`, `resp E x l := ENNReal.ofReal (E.measure (MState.pure l) x)`, prove every field, then `example : bb.IsPsiOntic`; `#print axioms`.
- [ ] **Step 2: Run** — expect unknown identifier `OntologicalModel`.
- [ ] **Step 3: Implement** the file (definitions only; module doc with sections A. Ontological models, B. ψ-ontic models, C. Preparation independence; references: Harrigan–Spekkens 2010, PBR 2012).
- [ ] **Step 4: Build + test**; the model must be constructible and ψ-ontic.
- [ ] **Step 5: Commit** — `feat(QuantumInfo/Foundations): add OntologicalModel, IsPsiOntic, PreparationIndependent`.

### Task 5: Walsh signs and phases

**Files:**
- Create: `QuantumInfo/Foundations/PBR/Phases.lean`; Modify: `QuantumInfo.lean`
- Test: `$T\Task5.lean`

**Interfaces (namespace `PBR`):**
- `def sign (j k : Fin 2) : ℂ := if j = 1 ∧ k = 1 then -1 else 1`
- `lemma sign_comm`, `lemma sign_mul_self (j k) : sign j k * sign j k = 1`, `lemma conj_sign (j k) : starRingEnd ℂ (sign j k) = sign j k`
- `def walsh {n : ℕ} (x z : Fin n → Fin 2) : ℂ := ∏ i, sign (x i) (z i)`, with `walsh_comm`, `walsh_mul_self`, `conj_walsh` analogues
- `lemma sum_walsh_mul_walsh {n : ℕ} (x y : Fin n → Fin 2) : ∑ z, walsh x z * walsh y z = if x = y then 2 ^ n else 0`
- `lemma exists_two_mul_pow_le {c s : ℝ} (hc : 0 < c) (hs : 0 < s) : ∃ n : ℕ, 2 * c ^ n ≤ (c + s) ^ n`
- `lemma exists_norm_pow_sub_pow_eq {c s : ℝ} {n : ℕ} (hs : 0 ≤ s) (hsc : s ≤ c) (hn : 2 * c ^ n ≤ (c + s) ^ n) : ∃ α : ℝ, ‖((c : ℂ) + Complex.exp (α * Complex.I) * s) ^ n - (c : ℂ) ^ n‖ = c ^ n`
- `lemma exists_phases {c s : ℝ} {n : ℕ} (hc : 0 < c) (hs : 0 ≤ s) (hsc : s ≤ c) (hn : 2 * c ^ n ≤ (c + s) ^ n) : ∃ ω : (Fin n → Fin 2) → ℂ, (∀ z, ‖ω z‖ = 1) ∧ ∑ z, ω z * ∏ i, ![(c : ℂ), (s : ℂ)] (z i) = 0`

- [ ] **Step 1: Test**: examples using each lemma, including `exists_phases` with `c = s` (orthogonal case, Review Focus 3); `#print axioms PBR.exists_phases`, `#print axioms PBR.sum_walsh_mul_walsh`.
- [ ] **Step 2: Run** — fails.
- [ ] **Step 3: Implement.** Walsh orthogonality: `Finset.prod_univ_sum` turns the sum into `∏ i, ∑ k, sign (x i) k * sign (y i) k`. `exists_two_mul_pow_le`: Bernoulli `one_add_mul_le_pow` with `t = s / c` and `n ≥ c / s` (`exists_nat_ge`). `exists_norm_pow_sub_pow_eq`: `intermediate_value_Icc'` on `[0, π]` for `α ↦ ‖(c + e^{iα}s)ⁿ - cⁿ‖` (value `≥ cⁿ` at 0, `≤ cⁿ` at π since `0 ≤ c - s ≤ c`). `exists_phases`: with that `α` and `w = (c + e^{iα}s)ⁿ - cⁿ`, take `ω 0 = -w / cⁿ` and `ω z = ∏ i, ![1, e^{iα}] (z i)` otherwise; the sum telescopes via `Finset.prod_univ_sum`.
- [ ] **Step 4: Build + test**; pass.
- [ ] **Step 5: Commit** — `feat(QuantumInfo/PBR): Walsh signs and the PBR phase choice`.

### Task 6: Qubit frame of two pure states

**Files:**
- Create: `QuantumInfo/Foundations/PBR/QubitFrame.lean`; Modify: `QuantumInfo.lean`
- Test: `$T\Task6.lean`

**Interfaces (namespace `PBR`):**
```lean
structure QubitFrame {d : Type*} [Fintype d] (ψ : Fin 2 → Ket d) where
  e : Fin 2 → Ket d
  c : ℝ
  s : ℝ
  phase : Fin 2 → ℂ
  s_pos : 0 < s
  s_le_c : s ≤ c
  sq_add_sq : c ^ 2 + s ^ 2 = 1
  norm_phase (b : Fin 2) : ‖phase b‖ = 1
  dot_e_e (j k : Fin 2) : 〈e j‖e k〉 = if j = k then 1 else 0
  dot_e_ψ (j b : Fin 2) : 〈e j‖ψ b〉 = phase b * sign j b * ![(c : ℂ), (s : ℂ)] j
```
- `lemma QubitFrame.c_pos (F : QubitFrame ψ) : 0 < F.c`
- `lemma QubitFrame.sum_norm_sq_dot_e_ψ (F : QubitFrame ψ) (b : Fin 2) : ∑ j, ‖〈F.e j‖ψ b〉‖ ^ 2 = 1`
- `lemma exists_qubitFrame {d : Type*} [Fintype d] [DecidableEq d] (ψ : Fin 2 → Ket d) (h : MState.pure (ψ 0) ≠ MState.pure (ψ 1)) : Nonempty (QubitFrame ψ)`

- [ ] **Step 1: Test**: `example` applying `exists_qubitFrame` to `![Ket.basis 0, Ket.basis 1]` on `Fin 2` (orthogonal pair, Review Focus 3) given the `pure` inequality as a hypothesis; `#print axioms PBR.exists_qubitFrame`.
- [ ] **Step 2: Run** — fails.
- [ ] **Step 3: Implement** following the spec: `γ = 〈ψ 0‖ψ 1〉`, `r = ‖γ‖`, `ζ = Complex.exp (-(γ.arg) * I)` (`Complex.norm_mul_exp_arg_mul_I`), `e 0 = Ket.normalize (ψ 0 + ζ • ψ 1)`, `e 1 = Ket.normalize (ψ 0 - ζ • ψ 1)`, `c = √((1+r)/2)`, `s = √((1-r)/2)`, `phase = ![1, conj ζ]`. `r < 1` from `MState.pure_eq_pure_iff` (if `r = 1` then `ψ 0 = ζ • ψ 1`). Extract the norm-square expansions `∑ ‖ψ₀ ± ζψ₁‖² = 2 ± 2r` as lemmas.
- [ ] **Step 4: Build + test**; pass.
- [ ] **Step 5: Commit** — `feat(QuantumInfo/PBR): QubitFrame and exists_qubitFrame`.

### Task 7: The PBR measurement

**Files:**
- Create: `QuantumInfo/Foundations/PBR/Measurement.lean`; Modify: `QuantumInfo.lean`
- Test: `$T\Task7.lean`

**Interfaces (namespace `PBR`; `F : QubitFrame ψ`, `ω : (Fin n → Fin 2) → ℂ`, `hω : ∀ z, ‖ω z‖ = 1`):**
- `lemma sum_norm_sq_sum_mul_of_orthonormal {ι κ : Type*} [Fintype ι] [Fintype κ] (v : κ → ι → ℂ) (hv : ∀ a b, ∑ i, starRingEnd ℂ (v a i) * v b i = if a = b then 1 else 0) (β : κ → ℂ) : ∑ i, ‖∑ a, β a * v a i‖ ^ 2 = ∑ a, ‖β a‖ ^ 2`
- `def QubitFrame.frameKet (F) (z : Fin n → Fin 2) : Ket (Fin n → d) := Ket.piProd fun i => F.e (z i)`
- `lemma QubitFrame.dot_frameKet_frameKet (z z') : 〈F.frameKet z‖F.frameKet z'〉 = if z = z' then 1 else 0`
- `lemma QubitFrame.dot_frameKet_piProd (z x : Fin n → Fin 2) : 〈F.frameKet z‖Ket.piProd fun i => ψ (x i)〉 = (∏ i, F.phase (x i)) * walsh z x * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i)`
- `def QubitFrame.measurementKet (F) (ω) (hω) (x : Fin n → Fin 2) : Ket (Fin n → d)` with `vec k = ∑ z, ((Real.sqrt (2 ^ n))⁻¹ * starRingEnd ℂ (ω z) * walsh x z) * F.frameKet z k`
- `lemma QubitFrame.dot_measurementKet (x) (φ : Ket (Fin n → d)) : 〈F.measurementKet ω hω x‖φ〉 = ∑ z, (Real.sqrt (2 ^ n))⁻¹ * ω z * walsh x z * 〈F.frameKet z‖φ〉`
- `lemma QubitFrame.dot_measurementKet_measurementKet (x y) : 〈F.measurementKet ω hω x‖F.measurementKet ω hω y〉 = if x = y then 1 else 0`
- `lemma QubitFrame.dot_measurementKet_piProd_self (hsum : ∑ z, ω z * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i) = 0) (x) : 〈F.measurementKet ω hω x‖Ket.piProd fun i => ψ (x i)〉 = 0`
- `lemma QubitFrame.sum_norm_sq_dot_measurementKet (y) : ∑ x, ‖〈F.measurementKet ω hω x‖Ket.piProd fun i => ψ (y i)〉‖ ^ 2 = 1`
- `lemma exists_povm {d : Type*} [Fintype d] [DecidableEq d] (ψ : Fin 2 → Ket d) (h : MState.pure (ψ 0) ≠ MState.pure (ψ 1)) : ∃ (n : ℕ) (E : POVM (Option (Fin n → Fin 2)) (Fin n → d)), ∀ o, ∃ x : Fin n → Fin 2, E.measure (MState.pure (Ket.piProd fun i => ψ (x i))) o = 0`

- [ ] **Step 1: Test**: `example`s restating `exists_povm` and `sum_norm_sq_dot_measurementKet` for arbitrary `y` (Review Focus 2); `#print axioms PBR.exists_povm`.
- [ ] **Step 2: Run** — fails.
- [ ] **Step 3: Implement** per the spec formulas. Normalisation of `measurementKet` and the Parseval identity both come from `sum_norm_sq_sum_mul_of_orthonormal` (once for `frameKet`, once for the unitary columns `z ↦ (x ↦ (√2ⁿ)⁻¹ ω z walsh x z)`), with `sum_walsh_mul_walsh`. `∑_z ∏_i ‖〈e (z i)‖ψ (y i)〉‖² = ∏_i 1` via `Finset.prod_univ_sum` and `QubitFrame.sum_norm_sq_dot_e_ψ`. `exists_povm`: `exists_qubitFrame` → `exists_two_mul_pow_le F.c_pos F.s_pos` → `exists_phases` → `POVM.ofOrthonormal`; outcome `some x` uses witness `x`, outcome `none` any witness (probability `1 - 1`).
- [ ] **Step 4: Build + test**; pass.
- [ ] **Step 5: Commit** — `feat(QuantumInfo/PBR): the PBR measurement and exists_povm`.

### Task 8: The PBR theorem

**Files:**
- Create: `QuantumInfo/Foundations/PBR/Theorem.lean`; Modify: `QuantumInfo.lean`, `scripts/lint/exemptions/Theorems.txt` (append `OntologicalModel.PreparationIndependent.isPsiOntic` at the end of `[QuantumInfo]`), `docs/references.bib` (PBR 2012 entry from InspireHEP; Harrigan–Spekkens 2010)
- Test: `$T\Task8.lean`

**Interfaces:**
- `lemma PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero {Λ O : Type*} [MeasurableSpace Λ] [Fintype O] (μ : Fin 2 → Measure Λ) [∀ b, IsFiniteMeasure (μ b)] {n : ℕ} (ξ : O → (Fin n → Λ) → ℝ≥0∞) (hξ : ∀ o, Measurable (ξ o)) (hsum : ∀ l, ∑ o, ξ o l = 1) (hzero : ∀ o, ∃ x : Fin n → Fin 2, ∫⁻ l, ξ o l ∂Measure.pi (fun i => μ (x i)) = 0) : μ 0 ⟂ₘ μ 1`
- `theorem OntologicalModel.PreparationIndependent.isPsiOntic {d Λ : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Λ] {M : OntologicalModel d Λ} {Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Fin n → Λ)} (h : M.PreparationIndependent Mn) : M.IsPsiOntic` — docstring: "**Pusey–Barrett–Rudolph theorem** …".

- [ ] **Step 1: Test**: apply the theorem to arbitrary `ψ φ` with `hne : MState.pure ψ ≠ MState.pure φ` (Review Focus 5); apply the classical lemma with arbitrary `n` (Review Focus 4); `#print axioms OntologicalModel.PreparationIndependent.isPsiOntic`.
- [ ] **Step 2: Run** — fails.
- [ ] **Step 3: Implement.** Classical lemma: `Measure.mutuallySingular_iff_disjoint`; for `ν ≤ μ 0`, `ν ≤ μ 1`: `isFiniteMeasure_of_le`, `Measure.pi_mono` (Task 1), `lintegral_mono'`, `lintegral_finsetSum`, `Measure.pi_univ`, `pow_eq_zero`, `Measure.measure_univ_eq_zero`. Theorem: `PBR.exists_povm ![ψ, φ]`, then the classical lemma with `μ b = M.prep (![ψ, φ] b)` and `ξ = (Mn n).resp E`, rewriting with `h n` and `(Mn n).lintegral_resp`.
- [ ] **Step 4: Build + test**; pass; axioms clean.
- [ ] **Step 5: Commit** — `feat(QuantumInfo/PBR): the Pusey–Barrett–Rudolph theorem`.

### Task 9: Whole-repository verification

**Files:** possibly `scripts/lint/exemptions/spellingWords.txt`; fixes anywhere in the new/changed files.

- [ ] **Step 1:** `lake build` (Physlib + QuantumInfo) — no errors.
- [ ] **Step 2:** `lake build PhyslibAlpha` (needed by `theorem_lint`, `auxillary_script_test`).
- [ ] **Step 3:** `lake exe lint_all`, `lake exe theorem_lint`, `lake exe forMathlib_lint`, `lake exe module_doc_lint`, `lake exe auxillary_script_test`, `lake exe sorry_lint`, `lake exe spelling` (add genuine physics words to `spellingWords.txt`) — all pass.
- [ ] **Step 4:** Commit fixes, then `./scripts/lint/required/lint-style.sh` (needs Python; reads committed state) — pass.
- [ ] **Step 5:** `grep -rn "sorry\|axiom " ` over new files — nothing; final `#print axioms` on the main theorem.
