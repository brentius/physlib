# Task 4 report: Walsh phases and the qubit frame

**Status:** DONE

## Commits (branch `pbr-alpha`, on top of 65cea05c)

- `5911056b` feat(PhyslibAlpha/PBR): add Walsh characters and the choice of PBR phases
  (Phases.lean, import in PhyslibAlpha.lean, spelling words bernoulli/parseval/walsh)
- `49a7ba06` feat(PhyslibAlpha/PBR): add QubitFrame and exists_qubitFrame
  (QubitFrame.lean, import in PhyslibAlpha.lean, spelling word qubit)

## Phases.lean

The draft compiled except for the new lemma `sum_norm_sq_sum_mul_inv_sqrt_mul_walsh`:
`push_cast` rewrote `↑(√(2 ^ n))⁻¹` to `(↑√(2 ^ n))⁻¹` on one side only, so `ring` and the
final `simp [sum_conj_inv_sqrt_mul_walsh]` failed. Fixed by `apply Complex.ofReal_injective`
plus `simp only [Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.conj_mul', map_sum,
Finset.sum_mul_sum]` (no `push_cast`), `rw [map_mul (starRingEnd ℂ) (β z)]; ring` in the
summand, and a closing `simp only [sum_conj_inv_sqrt_mul_walsh, mul_ite, mul_one, mul_zero,
Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]`. Statement unchanged. Rest of the file
identical to the draft.

## QubitFrame.lean (new)

Imports `Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic` and `...PBR.Phases`.
Namespace `QuantumMechanics.PBR`, `variable {d : Type*} [Fintype d] [DecidableEq d]`,
`open InnerProductSpace`.

- A.1 (vectors `ψ ± ζ φ`, `ψ φ : 𝓗[d]` unit, `‖ζ‖ = 1`, `ζ * ⟪ψ, φ⟫_ℂ = r`):
  private `conj_mul_self_of_norm_eq_one`; `conj_mul_inner_swap`; `inner_add_smul_fst`
  (`= 1 + r`), `inner_add_smul_snd` (`= conj ζ * (1 + r)`), `inner_sub_smul_fst` (`= 1 - r`),
  `inner_sub_smul_snd` (`= -(conj ζ * (1 - r))`), `inner_add_smul_sub_smul`,
  `inner_sub_smul_add_smul` (`= 0`), `norm_add_smul_sq` (`= 2 * (1 + r)`),
  `norm_sub_smul_sq` (`= 2 * (1 - r)`). All match the brief's algebra (no sign issues).
- A.2: private `inv_sqrt_two_mul_mul` (`(√(2a))⁻¹ * a = √(a/2)`), `norm_inv_sqrt_smul`,
  `inner_ofReal_smul_ofReal_smul`; public `inner_inv_sqrt_smul_{add,sub}_smul_{fst,snd}`.
- B: `QubitFrame ψ` with exactly the brief's fields (`orthonormal_e : Orthonormal ℂ e`,
  `inner_e_state`), field docstrings ported; `QubitFrame.c_pos`,
  `QubitFrame.sum_norm_sq_inner_e_state`.
- C: `QubitFrame.ofPhase ψ hψ hζ hr hr0 hr1` with
  `e = ![(((√(2 * (1 + r)))⁻¹ : ℝ) : ℂ) • (ψ 0 + ζ • ψ 1), (((√(2 * (1 - r)))⁻¹ : ℝ) : ℂ) • (ψ 0 - ζ • ψ 1)]`
  (complex casts of real scalars), `c`, `s`, `phase = ![1, star ζ]` as in the brief;
  `exp_neg_arg_mul_self` (kept verbatim); `exists_qubitFrame ψ hψ h`.
  `lt_one_of_pure_ne` not ported (per brief).

Note for Task 5: in `ofPhase` proofs, plain `simp` unfolds `⟪·,·⟫_ℂ` on `𝓗[d]` into `.val`
(EuclideanSpace) form, so the field proofs use `simp only [Fin.zero_eta, Fin.mk_one,
Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]` and then `rw` with the named lemmas.
Downstream code should likewise avoid bare `simp` on inner products of `𝓗[d]` vectors.

Docs: no mention of kets/bra-kets/`MState`; headings per AGENTS.md; key results with `PBR.`
prefix; reference `[ref: Pusey:2011de]`. All proofs well under 50 lines, no lines > 100 chars,
no trailing whitespace.

## Verification

- `lake build PhyslibAlpha.QuantumMechanics.Foundations.PBR.Phases` -> `✔ Built ... Build completed successfully (1991 jobs).` (no warnings)
- `lake build PhyslibAlpha.QuantumMechanics.Foundations.PBR.QubitFrame` -> `✔ Built ... (26s) Build completed successfully (2486 jobs).` (no warnings; final run after all edits)
- `lake exe module_doc_lint`: exits 1 with 2691 pre-existing problems in 486 files (all in
  QuantumInfo/Physlib, apparently exemptions not applied on this Windows checkout); no
  PhyslibAlpha file, and no PBR file, is reported.
- Not run (need full library builds / Python): lint_all, theorem_lint, runPhyslibAlphaLinters,
  noAlphaImports, alphaFileImports, alphaPythonLinters.sh, lint-style.sh.
