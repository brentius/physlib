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

