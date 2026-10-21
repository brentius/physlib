# Handoff: PBR theorem on PhyslibAlpha (`pbr-alpha`)

Paused on 2026-10-21 after Task 5 of 6. This file and the rest of `docs/superpowers/` travel on the
branch `fork/pbr-alpha-notes` (not for merging); the code is on `fork/pbr-alpha`.

## Why this work exists

The upstream PR for the PBR theorem (built on `QuantumInfo`'s `Ket`/`MState`/`POVM`) came back
`awaiting-author`: maintainers plan to fold `QuantumInfo` into `Physlib` and asked that the work be
built on the `ProbabilisticTheory`/`QuantumMechanics` formalism of `Physlib`/`PhyslibAlpha`. The
chosen port is **quantum-specific, in PhyslibAlpha**: unit vectors of `𝓗[d]`, Alpha `Measurement`s,
vector states `ofVec`. Design: `docs/superpowers/specs/2026-10-20-pbr-physlibalpha-design.md`.
Plan: `docs/superpowers/plans/2026-10-20-pbr-physlibalpha.md`.

Policy reminders (repo `AGENTS.md`, `AI-POLICY.md` §3): all communication with reviewers is
human-to-human — no AI-written replies on the PR; the author must independently check that review
feedback is addressed before asking for re-review. Push only to your fork (`brentius/physlib`);
`brentius` has no write access to `leanprover-community/physlib`.

## Setting up on a new machine

```bash
git clone https://github.com/brentius/physlib.git physlib
cd physlib
git remote rename origin fork
git remote add origin https://github.com/leanprover-community/physlib.git
git fetch --all
git switch -c pbr-alpha --track fork/pbr-alpha
# bring the (untracked) notes back without committing them
git restore --source=fork/pbr-alpha-notes -- docs/superpowers
echo "docs/superpowers/" >> .git/info/exclude
# Lean: install elan (the VS Code "Lean 4" extension does this; or
# https://github.com/leanprover/elan). The toolchain (v4.35.0, from `lean-toolchain`) is
# downloaded automatically on the first `lake` command. Then fetch Physlib's prebuilt cache
# (Mathlib + upstream Physlib) and build only what changed:
lake exe get_cache
lake build PhyslibAlpha.QuantumMechanics.Foundations.PBR.Theorem
```

Nothing under `.lake/` travels with git; the cache download replaces it. Claude's memory from the
old machine does not travel either — the rules it held are repeated in this file.

The old QuantumInfo version (source of the port) is on `fork/pbr/5-pbr-theorem`
(`git show fork/pbr/5-pbr-theorem:QuantumInfo/Foundations/PBR/<File>.lean`).

To resume with Claude Code + the superpowers plugin (subagent-driven development): copy the ledger
into the plan workspace, then ask Claude to resume the plan from Task 6.

```bash
mkdir -p .superpowers/sdd/2026-10-20-pbr-physlibalpha
cp -r docs/superpowers/sdd-workspace/. .superpowers/sdd/2026-10-20-pbr-physlibalpha/
printf '*\n' > .superpowers/sdd/.gitignore
```

The ledger (`progress.md`) records every completed task, every ruling made on your behalf, and the
deferred minor review findings that the final review must triage.

## Done (Tasks 1–5, on `pbr-alpha`)

Nine commits on top of `origin/master` `4ed4eb11`, each reviewed (spec + quality, no Critical or
Important findings):

| Commit | Content |
|---|---|
| `15b9c49e` | `MeasureTheory.Measure.pi_mono` — `PhyslibAlpha/Mathematics/MeasureTheory/Pi.lean` (new) |
| `9bc3f215` | `piProdVec`, `inner_piProdVec`, `norm_piProdVec(_eq_one)` — `…/FiniteTarget/ProductState.lean` §F |
| `b72381d6` | `ofVec_smul`, `norm_inner_lt_one_of_ofVec_ne` — `PhyslibAlpha/ProbabilisticTheory/HilbertSpace/State/Vector.lean` §B |
| `c50d1136` | `orthonormalMeasurement` + Born rule `expectation_orthonormalMeasurement` — `…/FiniteTarget/Measurement.lean` (new) |
| `65cea05c` | `OntologicalModel`, `IsPsiOntic`, `PreparationIndependent`, `of_prep_piProdVec` — `PhyslibAlpha/QuantumMechanics/Foundations/OntologicalModel.lean` (new); bib + spelling |
| `5911056b` | Walsh characters, `exists_phases`, Walsh Parseval — `…/Foundations/PBR/Phases.lean` (new) |
| `49a7ba06` | `QubitFrame`, `exists_qubitFrame` — `…/Foundations/PBR/QubitFrame.lean` (new) |
| `7a2ae785` | `frameVec`, `measurementVec`, `exists_measurement` — `…/Foundations/PBR/Measurement.lean` (new) |
| `eb94e0a6` | `theorem QuantumMechanics.OntologicalModel.PreparationIndependent.isPsiOntic` — `…/Foundations/PBR/Theorem.lean` (new); `Theorems.txt` |

Verified so far: each module builds with no errors and no warnings
(`lake build PhyslibAlpha.QuantumMechanics.Foundations.PBR.Theorem` builds them all; 3268 jobs);
`noAlphaImports` passed after Task 1. **Not yet run:** the full-library build and the lint suite
(Task 6). `Measurement.lean` alone takes ~6 minutes to compile — worth profiling (ledger has the
suspected lines).

## Left to do

1. **Task 6 — whole-repo verification** (plan, Task 6): `lake build PhyslibAlpha`, then
   `lake exe lint_all`, `theorem_lint`, `module_doc_lint`, `forMathlib_lint`,
   `auxillary_script_test`, `runPhyslibAlphaLinters`, `noAlphaImports`, `alphaFileImports`,
   `./scripts/lint/required/alpha/alphaPythonLinters.sh`, `./scripts/lint/required/lint-style.sh`
   (after committing). `theorem_lint` and `auxillary_script_test` need `Physlib`, `QuantumInfo` and
   `PhyslibAlpha` built. Known oddity: on the old machine `module_doc_lint` reported 2691 problems,
   all in upstream `Physlib`/`QuantumInfo` files (possibly a Windows/CRLF artefact) — check whether
   they also appear on a clean checkout of `origin/master`; only problems in the new files matter.
2. **Final whole-branch review** of `origin/master..pbr-alpha` (Opus, high effort), pointed at the
   ledger's `minor (deferred)` lines; one fix wave; one scoped re-review.
3. **PR branches** (stacked, pushed to `fork` only): (1) supporting API — commits for
   `Measure.pi_mono`, `piProdVec`, `ofVec_smul`/`norm_inner_lt_one_of_ofVec_ne`,
   `orthonormalMeasurement`; (2) `OntologicalModel`; (3) PBR — Phases, QubitFrame, Measurement,
   Theorem. PR descriptions: list every declaration with its file and a one-line explanation, plus a
   reviewer map (AGENTS.md "PR descriptions"); end with the Claude Code attribution line.
4. **The old PR**: decide yourself whether to close the QuantumInfo PR(s) or repurpose them; reply
   to the reviewer in your own words.
