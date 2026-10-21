# PBR theorem formalisation — design

## Intent

Formalise, in physlib (Lean 4, Mathlib v4.34.1), the general Pusey–Barrett–Rudolph (PBR)
theorem from M. F. Pusey, J. Barrett, T. Rudolph, *On the reality of the quantum state*,
Nature Physics 8, 475–478 (2012), arXiv:1111.3328: in any ontological model of a
finite-dimensional quantum system satisfying *preparation independence*, the ontic
distributions of any two distinct pure states are mutually singular (the model is ψ-ontic).
Complete, `sorry`-free, axiom-free, compiles, passes every check in `AGENTS.md`.
Local branch `pbr-theorem` only; no push or PR.

## Goals

- Standard definitions: ontological model, ψ-ontic, preparation independence, stated with the
  existing QuantumInfo objects (`Ket`, `Ket.piProd`, `MState.pure`, `POVM`, `POVM.measure`)
  and Mathlib measure theory (`Measure`, `Measure.pi`, `Measure.MutuallySingular`).
- The general PBR theorem for an arbitrary pair of pure states (not only `|0⟩, |+⟩`), with the
  paper's `n`-copy entangled measurement, in arbitrary finite dimension `d`.

## Non-goals

- Mixed-state preparations, preparation contextuality, approximate/robust (noise-tolerant)
  versions, other ψ-ontology theorems (Hardy, Colbeck–Renner), Bell/Kochen–Specker.

## Anti-goals

- A vacuous or trivial theorem (inconsistent model hypotheses, `True`-valued fields,
  hypotheses that assume the conclusion). A sanity check must show the model structure is
  inhabited.
- `sorry`, `axiom`, `Lean.ofReduceBool`.

## Decided (my calls, user opted out of questions)

- Location: `QuantumInfo/Foundations/` (QuantumInfo already owns `Ket`, `MState`, `POVM`).
  General lemmas go in existing files (`Braket.lean`, `POVM.lean`) or QuantumInfo `ForMathlib`.
- Pure states are indexed by `Ket d` (more general than by `MState`: phase-equivalent kets may
  receive different distributions). "Distinct" means `MState.pure ψ ≠ MState.pure φ`.
- Response functions are `ℝ≥0∞`-valued, one per POVM (outcome type in `Type`), summing to 1;
  the Born rule is `∫⁻ resp ∂prep ψ = ENNReal.ofReal (E.measure (MState.pure ψ) x)`.
- Preparation independence: a family of models `Mn n` for `n` copies (basis index
  `Fin n → d`, ontic space `Fin n → Λ`) with
  `(Mn n).prep (Ket.piProd ψ) = Measure.pi (fun i => M.prep (ψ i))`.
- Conclusion: `M.prep ψ ⟂ₘ M.prep φ`.

## Proof outline

Quantum part. Let `γ = ⟨ψ₀|ψ₁⟩`, `r = |γ|`, `ζ = exp(-i arg γ)`. Non-phase-equivalence gives
`r < 1`. With `c = √((1+r)/2)`, `s = √((1-r)/2)` (`c ≥ s > 0`), `e₀ ∝ ψ₀ + ζψ₁`,
`e₁ ∝ ψ₀ - ζψ₁` are orthonormal and `⟨e_j|ψ_b⟩ = phase_b · (-1)^{jb} · amp_j`
(`amp = (c, s)`, `phase = (1, conj ζ)`). Pick `n` with `2cⁿ ≤ (c+s)ⁿ` (Bernoulli). By the IVT
pick `α` with `|(c + e^{iα}s)ⁿ - cⁿ| = cⁿ`, giving unit phases `ω_z` (`z ∈ {0,1}ⁿ`) with
`Σ_z ω_z Π_i amp_{z_i} = 0`. With `E_z = ⊗ e_{z_i}` and Walsh signs `χ(x,z) = Π(-1)^{x_i z_i}`,
`b_x = 2^{-n/2} Σ_z conj(ω_z) χ(x,z) E_z` is orthonormal, `⟨b_x|Ψ_x⟩ = 0` for
`Ψ_x = ⊗ ψ_{x_i}`, and `Σ_x |⟨b_x|Ψ_y⟩|² = 1`. The POVM `{|b_x⟩⟨b_x|} ∪ {1 - Σ_x |b_x⟩⟨b_x|}`
therefore has every outcome of probability 0 on some `Ψ_x`.

Classical part. `μ₀ ⟂ μ₁ ↔ Disjoint μ₀ μ₁` (Mathlib). If `ν ≤ μ₀, ν ≤ μ₁` then
`ν^{⊗n} ≤ μ_{x}^{⊗n}` for every `x`, so
`ν(Λ)ⁿ = ∫ Σ_o ξ_o dν^{⊗n} ≤ Σ_o ∫ ξ_o dμ_{x(o)}^{⊗n} = 0`, hence `ν = 0`.

## Left to the builder

Proof scripts, private helper lemmas, exact section structure of module docs.

## Revision (2026-10-18, after the final review)

Preparation independence is generalised: the n-copy model may have any ontic space `Λn n`,
with a measurable `ι n : (Fin n → Λ) → Λn n` such that the product state `⊗ ψ i` is prepared by
`(Measure.pi fun i => M.prep (ψ i)).map (ι n)`. The Cartesian-product version (`ι = id`) is a
special case, kept as a lemma. Reason: the Cartesian form is Leifer's Cartesian Product
Assumption, strictly stronger than PBR's assumption, and is not satisfied by the
Beltrametti–Bugajski model.
