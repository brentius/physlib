# Task 3 report: ontological models

**Status:** DONE

## Commit

`65cea05c feat(PhyslibAlpha/Foundations): add OntologicalModel, IsPsiOntic and PreparationIndependent`

Files: `PhyslibAlpha/QuantumMechanics/Foundations/OntologicalModel.lean` (new),
`PhyslibAlpha.lean`, `docs/references.bib`, `scripts/lint/exemptions/spellingWords.txt`.

## Declarations (all in `QuantumMechanics`, signatures exactly as in the brief)

- `structure OntologicalModel (d) [Fintype d] [DecidableEq d] (Λ) [MeasurableSpace Λ]` with fields
  `prep`, `isProbabilityMeasure_prep` (made an instance via `attribute [instance]`), `resp`,
  `measurable_resp`, `sum_resp`, `lintegral_resp`
  (`∫⁻ l, resp M x l ∂prep ψ hψ = ENNReal.ofReal ((ofVec hψ)⟨M {x} (measurableSet_singleton x)⟩)`).
- `OntologicalModel.IsPsiOntic`.
- `OntologicalModel.PreparationIndependent` (with implicit `{Λn : ℕ → Type*} [∀ n, MeasurableSpace (Λn n)]`).
- `OntologicalModel.PreparationIndependent.of_prep_piProdVec` (lemma, one-line term proof with `ι n = id`).

The draft compiled as-is; no elaboration problems (no explicit `E :=` needed). Docstrings on the
structure, every field, both defs and the lemma. Module doc has title, summary, i–iv, sections
A–C listed in the table of contents, `[ref: …]` keys.

## Other edits

- `PhyslibAlpha.lean`: import inserted (sorted) between `Blackbody.RayleighJeans` and `HarmonicOscillator.LadderSystem`.
- `docs/references.bib`: `Harrigan:2007wfc` (after `Dreiner:2008tw`) and `Pusey:2011de` (after
  `ParticleDataGroup:2018ovx`) copied verbatim from `pbr-theorem`; file is ASCII-sorted by key
  (uppercase keys first).
- `spellingWords.txt`: added `epistemic`, `harrigan`, `leifer`, `ontic`, `pusey`, `rudolph`,
  `spekkens` in sorted position. `leifer` was added beyond the old branch's list because the module
  doc cites Leifer.

## Verification

- `lake build PhyslibAlpha.QuantumMechanics.Foundations.OntologicalModel` →
  `✔ [3263/3263] Built PhyslibAlpha.QuantumMechanics.Foundations.OntologicalModel (298s)`,
  `Build completed successfully`, no warnings.
- `lake exe module_doc_lint` → exits 1 with 2691 pre-existing problems, none in any
  `PhyslibAlpha` file (grep for `PhyslibAlpha` in the output: 0 hits).
- No lines over 100 chars, no trailing whitespace.

## Notes / concerns

- The overview forward-references `OntologicalModel.PreparationIndependent.isPsiOntic` in
  `PhyslibAlpha/QuantumMechanics/Foundations/PBR/Theorem.lean`, which Task 5 creates (matches the plan).
- The spelling dictionary lacks many ordinary English words used in the file (e.g. "reproduces");
  the spelling script is optional and only scans `Physlib`, so only proper names / physics terms were added.
- `PBR/` (untracked, later task) and `.claude/` were left untouched and unstaged.
