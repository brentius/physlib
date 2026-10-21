# Task 1 report: product vectors, phase invariance of vector states, `Measure.pi_mono`

Status: DONE

## What was implemented

All names and signatures are exactly as in the brief.

- `PhyslibAlpha/Mathematics/MeasureTheory/Pi.lean` (new, imported in `PhyslibAlpha.lean` between
  `...LiftingAndConditioning` and `...PositiveFunctionalIntegral`):
  `MeasureTheory.Measure.pi_mono (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν`.
  The controller's draft compiled unchanged.
- `PhyslibAlpha/QuantumMechanics/HilbertSpaces/FiniteTarget/ProductState.lean`, new section
  `F. Product vectors of finite families`:
  `piProdVec`, `piProdVec_val`, `inner_piProdVec`, `norm_piProdVec`, `norm_piProdVec_eq_one`
  (namespace `QuantumMechanics.FiniteHilbertSpace`).
  Fixes to the draft:
  - `inner_piProdVec`: on `EuclideanSpace`, `RCLike.inner_apply` produces `w * conj v`, not
    `conj v * w`, so the final `Fintype.prod_sum` term needed its factors swapped.
  - `norm_piProdVec_eq_one`: `simp [norm_piProdVec, hv]` failed because the simp lemma
    `norm_eq_val` fires first and rewrites the goal to `‖(piProdVec v).val‖`. Replaced by
    `rw [norm_piProdVec]; exact Finset.prod_eq_one fun i _ => hv i` (this holds for empty
    families, since `Finset.prod_eq_one` is vacuous there).
  - Added a docstring to `piProdVec_val`; extended the module-doc Key results to name
    `norm_piProdVec` and `norm_piProdVec_eq_one`.
- `PhyslibAlpha/ProbabilisticTheory/HilbertSpace/State/Vector.lean`, new section
  `B. Phase invariance`, old `B. Example` is now `C. Example`:
  `UnitalPositiveLinearMap.ofVec_smul`, `UnitalPositiveLinearMap.norm_inner_lt_one_of_ofVec_ne`
  (namespace `ProbabilisticTheory`). Fixes to the draft:
  - `ofVec_smul`: the draft used `RCLike.conj_mul` after `← mul_assoc`, but the goal has the
    shape `c * conj c * _`, so it needs `RCLike.mul_conj`. Now
    `rw [← mul_assoc, RCLike.mul_conj, hc]; simp`.
  - `norm_inner_lt_one_of_ofVec_ne`: `ne_zero_of_norm_ne_zero (by simp [hψ])` left a metavariable
    goal; replaced by `norm_ne_zero_iff.1 (hψ ▸ one_ne_zero)` (and likewise for `φ`).

## Commands and output

Waited for the controller's lake process (PID 10840) to exit first, then:

```
lake build PhyslibAlpha.Mathematics.MeasureTheory.Pi \
           PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.Vector \
           PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.ProductState
```

First run: `Pi` built clean (25s); `Vector` failed with the two errors above. After the fixes:

```
✔ [3168/3168] Built PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.ProductState (45s)
Build completed successfully (3168 jobs).
```

No errors, no warnings (no `sorry`, no linter warnings).

Extra checks:

- Temporarily appended `#lint` to each of the three modules, built them, then restored the files
  from backups (no `#lint` left, verified by grep). Results: "Found 0 errors in 1 declarations" (Pi),
  "0 errors in 6 declarations (plus 8 automatically generated)" (Vector),
  "0 errors in 30 declarations (plus 16 automatically generated)" (ProductState); "All linting
  checks passed!" for each (15 linters, including `simpNF`, `docBlame`, `unusedArguments`).
- `lake exe noAlphaImports`: no violations.
- `lake exe alphaFileImports`: only lists the three later-task files
  (`FiniteTarget.Measurement`, `Foundations.OntologicalModel`, `Foundations.PBR.Phases`); `Pi` is
  imported.
- `lake exe module_doc_lint`: reports 2691 pre-existing problems in `Physlib/` files; it does not
  scan `PhyslibAlpha/` and none of my files is mentioned. Module docs were checked by hand against
  AGENTS.md (title, one-line summary, `i`-`iv` headings, TOC lists every section, no heading ends in
  a full stop, Key results name the new declarations).
- Trailing whitespace: none in the four files. No line over 100 characters (counted in characters).
- Not run: `lake exe lint_all` (does a full `lake build`), `runPhyslibAlphaLinters` (imports all of
  `PhyslibAlpha`, needs a full build; replaced by per-module `#lint` above),
  `lint-style.sh` (needs Python, absent, and covers only `Physlib`/`QuantumInfo`),
  `alphaPythonLinters.sh` (needs Python), `theorem_lint` (no `theorem` added: all new results are
  `lemma`), `forMathlib_lint` (nothing under `ForMathlib` touched), `auxillary_script_test`
  (needs everything built).

## Commits (on `pbr-alpha`, nothing pushed)

- `15b9c49e feat(PhyslibAlpha/MeasureTheory): add Measure.pi_mono` (Pi.lean, PhyslibAlpha.lean)
- `9bc3f215 feat(PhyslibAlpha/FiniteTarget): add piProdVec and inner_piProdVec` (ProductState.lean)
- `b72381d6 feat(PhyslibAlpha/ProbabilisticTheory): add ofVec_smul and norm_inner_lt_one_of_ofVec_ne`
  (Vector.lean)

Each message lists its declarations and ends with
`Co-authored-by: Claude Opus 5.5 <no-reply+claude-opus-5-5@anthropic.com>` (confirmed with
`git interpret-trailers --parse`). Only the task's files were staged; `Measurement.lean`,
`Foundations/` and `.claude/` remain untracked and untouched.

## Files changed

- `PhyslibAlpha.lean` (+1 import)
- `PhyslibAlpha/Mathematics/MeasureTheory/Pi.lean` (new, 60 lines)
- `PhyslibAlpha/ProbabilisticTheory/HilbertSpace/State/Vector.lean` (+33/-2)
- `PhyslibAlpha/QuantumMechanics/HilbertSpaces/FiniteTarget/ProductState.lean` (+49)

## Self-review

- Completeness: every name/signature in the brief is present and matches.
  `norm_piProdVec_eq_one` has no non-emptiness hypothesis, so `n = 0` is covered.
  `ofVec_smul` is stated for any `RCLike 𝕜` (so `ℂ` and `ℝ`).
- Quality: all definitions have docstrings, each lemma has a one-line docstring, every proof is under
  15 lines, nothing is dead. The one comment in `norm_inner_lt_one_of_ofVec_ne` explains the
  equality case of Cauchy-Schwarz.
- Discipline: nothing beyond the brief. The Pi.lean copyright header reads
  `Copyright (c) 2026 brent` per the global constraints; the two modified files keep their original
  headers.
- Scratch files live under `.superpowers/sdd/2026-10-20-pbr-physlibalpha/scratch/` (`t1_vec.lean`,
  plus `*.bak` copies used while restoring the temporary `#lint`); none is in the library or
  committed.

## Concerns

- Git warns "LF will be replaced by CRLF" for these files (`core.autocrlf=true`; the working tree
  mixes LF and CRLF files). The index holds LF, so the commits are unaffected.
- The `module_doc_lint` baseline already fails on upstream `Physlib/` files; unrelated to this task.
