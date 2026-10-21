# PBR stack — PR descriptions (paste-ready)

Five stacked branches, each based on the previous one. Open them in order; from a fork each
PR's diff will include its predecessors until those merge, so each description says what is new.
Replace `#PR1` … `#PR4` with the real numbers. Suggested label: `t-quantum-info` (or whichever
`t-…` label the repo uses for QuantumInfo).

---

## PR 1 — `pbr/1-quantum-helpers`

**Title:** feat(QuantumInfo): bra-kets of product kets, Parseval's identity and `POVM.ofOrthonormal`

General API needed for the Pusey–Barrett–Rudolph theorem (follow-up PRs), each placed in the
existing file it belongs to. 6 files, +207.

Added:
- `QuantumInfo/ForMathlib/MeasureTheory/Pi.lean` (new)
  - `MeasureTheory.Measure.pi_mono` — `Measure.pi` is monotone in each factor (not in Mathlib).
- `QuantumInfo/States/Pure/Braket.lean`
  - `Braket.dot_piProd` — bra-ket of `Ket.piProd` states is the product of the bra-kets.
  - `Braket.dot_eq_star_dotProduct`, `Braket.ofReal_sum_norm_sq_eq_star_dotProduct` — bra-kets and squared norms as dot products.
  - `Braket.exists_ne_zero_of_sum_norm_sq_ne_zero`, `Braket.dot_normalize_left`, `Braket.dot_normalize_normalize` — bra-kets of `Ket.normalize` vectors.
  - `Braket.sum_norm_sq_sum_mul_of_orthonormal` — Parseval's identity for orthonormal vectors.
- `QuantumInfo/States/Mixed/MState.lean`
  - `MState.pure_mul_pure_of_orthonormal`, `MState.sum_pure_mul_sum_pure_of_orthonormal` — projector algebra of an orthonormal family.
- `QuantumInfo/Measurements/POVM.lean`
  - `POVM.ofOrthonormal` — the POVM of rank-one projectors onto orthonormal kets plus the complementary projector (outcome `none`).
  - `POVM.one_sub_sum_pure_nonneg_of_orthonormal`, `POVM.measure_ofOrthonormal_some`, `POVM.measure_ofOrthonormal_none` — positivity and Born probabilities on pure states.

Reviewer map: `Braket.lean` → `MState.lean` → `POVM.lean` → `Pi.lean`.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

---

## PR 2 — `pbr/2-ontological-model` (depends on #PR1 only through the stack; no code dependency)

**Title:** feat(QuantumInfo/Foundations): ontological models, ψ-ontic models and preparation independence

New: `QuantumInfo/Foundations/OntologicalModel.lean`, 4 files, +192.

Added:
- `OntologicalModel` — Harrigan–Spekkens ontological model of a finite-dimensional quantum system: preparation measures for pure states, response functions for every POVM, Born rule.
- `OntologicalModel.IsPsiOntic` — distinct pure states (not equal up to phase) have mutually singular preparation measures.
- `OntologicalModel.PreparationIndependent` — PBR's preparation independence: independently prepared product states give independent ontic states which determine the `n`-copy ontic state through a measurable map (the `n`-copy ontic space is arbitrary).
- `OntologicalModel.PreparationIndependent.of_prep_piProd` — the Cartesian-product formulation implies it.
- References `Pusey:2011de`, `Harrigan:2007wfc` in `docs/references.bib`; spelling words.

Reviewer map: the structure fields' docstrings, then `IsPsiOntic`, then `PreparationIndependent`.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

---

## PR 3 — `pbr/3-walsh-phases` (depends on #PR2)

**Title:** feat(QuantumInfo/PBR): Walsh characters and the choice of PBR phases

New: `QuantumInfo/Foundations/PBR/Phases.lean` (Mathlib-only imports), 3 files, +322.

Added:
- `PBR.sign`, `PBR.walsh` with `sign_comm`, `sign_mul_self`, `conj_sign`, `norm_sign`, `sum_sign_mul_sign`, `walsh_comm`, `walsh_mul_self`, `conj_walsh`, `norm_walsh` — `±1` characters.
- `PBR.sum_walsh_mul_walsh` — orthogonality of Walsh characters.
- `PBR.exists_two_mul_pow_le` — the number of copies with `2 cⁿ ≤ (c + s)ⁿ` (Bernoulli).
- `PBR.exists_norm_pow_sub_pow_eq` — intermediate value theorem for the angle.
- `PBR.prod_phase_mul_prod_amp`, `PBR.norm_prod_phase`, `PBR.sum_phases_mul_amp`, `PBR.exists_phases` — unit phases cancelling the amplitude products.
- `PBR.ofReal_inv_sqrt_two_pow_sq`, `PBR.ofReal_inv_sqrt_two_pow_sq_mul_ite`, `PBR.sum_conj_inv_sqrt_mul_walsh`, `PBR.sum_norm_sq_inv_sqrt_mul` — rescaled Walsh vectors are orthonormal.

Reviewer map: §A (signs, Walsh) → §B (copies) → §C (phases) → §D.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

---

## PR 4 — `pbr/4-qubit-frame` (depends on #PR1, #PR3)

**Title:** feat(QuantumInfo/PBR): the qubit frame of two pure states

New: `QuantumInfo/Foundations/PBR/QubitFrame.lean`, 3 files, +377.

Added:
- `PBR.star_mul_star_dot`, `PBR.star_add_dotProduct_add`, `PBR.star_sub_dotProduct_sub`, `PBR.star_add_dotProduct_sub`, `PBR.star_sub_dotProduct_add`, `PBR.star_add_dotProduct_left/right`, `PBR.star_sub_dotProduct_left/right`, `PBR.sum_norm_sq_add/sub` — inner products of `ψ ± ζφ`.
- `PBR.dot_normalize_add_left/right`, `PBR.dot_normalize_sub_left/right`, `PBR.dot_normalize_add_sub`, `PBR.dot_normalize_sub_add` — bra-kets of the normalised vectors.
- `PBR.QubitFrame` — orthonormal `e 0, e 1` in the span of `ψ 0, ψ 1`, amplitudes `c ≥ s > 0`, unit phases, `〈e j‖ψ b〉 = phase b · (-1)^{jb} · ![c, s] j`; `QubitFrame.c_pos`, `QubitFrame.sum_norm_sq_dot_e_state`.
- `PBR.QubitFrame.ofPhase`, `PBR.exp_neg_arg_mul_self`, `PBR.lt_one_of_pure_ne` — construction.
- `PBR.exists_qubitFrame` — two pure states not equal up to a phase have a qubit frame.

Reviewer map: §B (the structure) → §C (`exists_qubitFrame`) → §A (computations).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

---

## PR 5 — `pbr/5-pbr-theorem` (depends on #PR1–#PR4)

**Title:** feat(QuantumInfo/PBR): the Pusey–Barrett–Rudolph theorem

New: `QuantumInfo/Foundations/PBR/Measurement.lean`, `QuantumInfo/Foundations/PBR/Theorem.lean`, 4 files, +363.

Added:
- `Measurement.lean`
  - `PBR.QubitFrame.frameKet` with `dot_frameKet_frameKet`, `dot_frameKet_piProd`, `sum_norm_sq_dot_frameKet_piProd` — the product frame.
  - `PBR.QubitFrame.measurementKet` with `measurementKet_apply`, `dot_measurementKet`, `dot_frameKet_measurementKet`, `dot_measurementKet_measurementKet` (orthonormal), `dot_measurementKet_piProd_self` (`〈b x‖Ψ x〉 = 0`), `sum_norm_sq_dot_measurementKet` (Parseval).
  - `PBR.exists_povm` — the PBR measurement: a POVM on `n` copies each outcome of which has probability zero on some product state.
- `Theorem.lean`
  - `PBR.eq_zero_of_le_of_exists_lintegral_eq_zero`, `PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero` — the classical half.
  - `theorem OntologicalModel.PreparationIndependent.isPsiOntic` — **the PBR theorem**: every preparation-independent ontological model is ψ-ontic (listed in `Theorems.txt`).

Reviewer map: `Theorem.lean` (statement and 9-line proof) → `PBR.exists_povm` → the measurement-ket lemmas.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
