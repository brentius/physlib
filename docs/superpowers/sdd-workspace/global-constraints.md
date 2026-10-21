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

