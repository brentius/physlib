# SDD ledger — plan: docs/superpowers/plans/2026-10-20-pbr-physlibalpha.md

Spec: docs/superpowers/specs/2026-10-20-pbr-physlibalpha-design.md
Branch: pbr-alpha (from origin/master 4ed4eb11). MERGE_BASE = 4ed4eb11.

## Pre-flight scan

| Pair / task | Produces vs consumes | Finding |
|---|---|---|
| T1 → T3 | piProdVec, norm_piProdVec_eq_one (T1) used in PreparationIndependent (T3) | consistent names/signatures |
| T1 → T5 | inner_piProdVec, norm_inner_lt_one_of_ofVec_ne, pi_mono (T1) used in T5 | consistent |
| T2 → T3 | Measurement X (Observable (𝓗[d] →L[ℂ] 𝓗[d])) type used in resp | consistent |
| T2 → T5 | orthonormalMeasurement hb x₀, expectation_orthonormalMeasurement | consistent; T5 uses x₀ = 0 |
| T3 → T5 | OntologicalModel/IsPsiOntic (ofVec (𝕜 := ℂ) ≠)/PreparationIndependent | T5 exists_measurement hypothesis uses same ofVec ≠ form — consistent |
| T4 → T5 | QubitFrame fields (orthonormal_e, inner_e_state), exists_qubitFrame (norm hyp), Parseval lemma | consistent; T5 converts ofVec ≠ to norm hyp via T1 lemma |
| T1–T5 share PhyslibAlpha.lean | each adds its own imports | sequential tasks, no conflict |
| T3,T4,T5 share spellingWords.txt; T5 Theorems.txt | additive edits | sequential, no conflict |
| T1 self | drafts exist; build + 3 commits | agrees |
| T2 self | draft; Born lemma signature matches Produces | agrees |
| T3 self | draft; bib + spelling | agrees |
| T4 self | Phases draft + QubitFrame port; algebra stated | agrees |
| T5 self | two files + Theorems.txt | agrees |
| T6 self | lints; alphaPythonLinters needs Python (absent) | skip-and-report allowed by plan |

Ruling: work in place on branch pbr-alpha, no git worktree — the Mathlib cache cannot be re-downloaded (network block on the old machine) so a worktree would need a from-scratch Mathlib build; only untracked .claude/ etc. at risk — cost if wrong: none to code.
Ruling: controller-written drafts (T1 ProductState/Vector/Pi, T2 Measurement, T3 OntologicalModel, T4 Phases) are handed to implementers as unverified drafts — written before the user asked for subagents; reviewers judge them like any code — cost if wrong: none beyond normal review.
Ruling: plan rewritten into 6 tasks (old Task 3 split into T4/T5, verification T6); PR-branch split and push to `fork` done by controller at finish (design-approved) — cost if wrong: re-split branches.
Ruling: commit trailer `Co-authored-by: Claude Opus 5.5 <no-reply+claude-opus-5-5@anthropic.com>` (AGENTS.md form, actual model, as on old pbr/* commits) — cost if wrong: reword commits.

## Progress
Task 1: dispatched implementer (sonnet), BASE 4ed4eb11
Ruling: per user (2026-10-20), later dispatches use opus at reduced effort — implementers and task reviewers effort=medium, scoped re-reviews effort=low, final review effort=high; Task 1's already-running sonnet implementer is left to finish (stopping it mid-edit risks overlapping edits on the same files) — cost if wrong: Task 1 may take more fix rounds.
Task 1: implementer DONE — commits 15b9c49e, 9bc3f215, b72381d6; 3-module build clean. Concern: `lake exe module_doc_lint` reports 2691 problems in upstream Physlib/ files (suspect CRLF working-tree checkout, core.autocrlf=true) — carry to Task 6.
Task 1: review dispatched (opus/medium) on 4ed4eb11..b72381d6
Task 1: complete (commits 4ed4eb11..b72381d6, review clean)
Task 1: minor (deferred): piProdVec docstrings say `ψ 0 ⊗ ⋯ ⊗ ψ (n - 1)` though ι is any Fintype
Task 1: minor (deferred): ofVec_smul hypothesis h' redundant (plan-mandated convenient form) — docstring note
Task 1: minor (deferred): inner_piProdVec relies on simp-only output order
Task 1: minor (deferred): commit 9bc3f215 title omits norm_piProdVec(_eq_one)
Task 1: minor (deferred): Measure.pi_mono may be ambiguous with Set.pi_mono when both namespaces open
Task 2: dispatched implementer (opus/medium), BASE b72381d6
Task 2: implementer DONE — commit c50d1136; module build clean; added helper API (orthonormalEffect, coe lemmas, coe_orthonormalMeasurement_singleton)
Task 2: complete (commits b72381d6..c50d1136, review clean)
Task 2: minor (deferred): inner_rankOne_self_apply / inner_sum_rankOne_self_apply / isPositive_one_sub_sum_rankOne hold in any inner product space (AGENTS general-placement); cite Mathlib inner_right_rankOne_apply
Task 2: minor (deferred): brittle `push_cast; rfl`, long `change`/`show` casts in Measurement.lean
Task 2: minor (deferred): coe_orthonormalObservable not @[simp]
Task 3: dispatched implementer (opus/medium), BASE c50d1136
Task 3: implementer DONE — commit 65cea05c; build clean; added spelling word leifer
Task 3: complete (commits c50d1136..65cea05c, review clean; ⚠️ bib verbatim + trailer verified by controller)
Task 3: minor (deferred): PreparationIndependent also constrains n = 0 (harmless; plan-mandated shape)
Task 3: minor (deferred): Leifer reference lacks [ref:] key / bib entry
Task 3: minor (deferred): overview forward-references PreparationIndependent.isPsiOntic (confirm after Task 5)
Task 3: minor (deferred): resp restricted to X : Type (universe 0)
Task 4: dispatched implementer (opus/medium), BASE 65cea05c
Task 4: implementer DONE — commits 5911056b, 49a7ba06; both modules build clean. Note for T5: plain simp rewrites ⟪·,·⟫_ℂ on 𝓗[d] into .val form — use simp only + named inner lemmas.
Task 4: complete (commits 65cea05c..49a7ba06, review clean; trailers verified by controller)
Task 4: minor (deferred): QubitFrame section-A names use _fst/_snd for ψ/φ slot — misleading vs Mathlib convention
Task 4: minor (deferred): inner_inv_sqrt_smul_add_smul_{fst,snd} take 0 ≤ r where -1 ≤ r suffices (inconsistent with sub lemmas)
Task 4: minor (deferred): possibly unused `open InnerProductSpace` in QubitFrame.lean
Task 4: minor (deferred): overview writes (-1) ^ (j b) for (-1) ^ (j * b)
Task 4: minor (deferred): sum_norm_sq_inner_e_state docstring overclaims "lies in the span"
Task 4: minor (deferred): spellingWords.txt `bernoulli` placement in already-unsorted region
Task 4: minor (deferred): Phases ofReal_inv_sqrt_two_pow_sq ends `push_cast; rfl` (fragile, pre-existing)
Task 5: dispatched implementer (opus/medium), BASE 49a7ba06
PAUSE requested by user (2026-10-21 ~01:00): stop after Task 5 completes (incl. review/fix loop); do not start Task 6; then hand off for another machine (push WIP + notes to fork).
Task 5: implementer DONE_WITH_CONCERNS — commits 7a2ae785, eb94e0a6; Theorem build clean (3268 jobs). Concerns: typed binder ∀ x : Fin n → Fin 2 in exists_measurement (whnf timeout otherwise); Theorems.txt [PhyslibAlpha] section unsorted upstream; Measurement.lean ~6 min build; extra helper inner_frameVec_measurementVec
Task 5: complete (commits 49a7ba06..eb94e0a6, review clean; trailers verified by controller)
Task 5: minor (deferred): Measurement.lean builds in ~358 s — profile (set_option profiler true) linear_combination/sqrt casts at :190-191, :210-211, ring under binders :219-222, exists_measurement :239-252
Task 5: minor (deferred): exists_measurement uses typed binder ∀ x : Fin n → Fin 2 (whnf timeout otherwise) — accepted
Task 5: minor (deferred): Theorems.txt [PhyslibAlpha] section unsorted upstream; entry placed beside QuantumMechanics.* — mention in PR description
Task 5: minor (deferred): Theorem.lean overview could say the PBR measurement uses O = Fin n → Fin 2 with witness x
PAUSED after Task 5 (user request). Next: Task 6 (whole-repo verification), then final review, PR split. See docs/superpowers/HANDOFF-pbr-alpha.md.
Handoff: pushed pbr-alpha (eb94e0a6) to fork, tracking fork/pbr-alpha; notes (spec, plan, this ledger, briefs/reports, HANDOFF-pbr-alpha.md) on fork/pbr-alpha-notes — not for merging.
