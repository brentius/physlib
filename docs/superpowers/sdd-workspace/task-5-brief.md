### Task 5: The PBR measurement and the PBR theorem

**Files:**
- Create `PhyslibAlpha/QuantumMechanics/Foundations/PBR/Measurement.lean` — port of `pbr-theorem:QuantumInfo/Foundations/PBR/Measurement.lean`.
- Create `PhyslibAlpha/QuantumMechanics/Foundations/PBR/Theorem.lean` — port of `pbr-theorem:QuantumInfo/Foundations/PBR/Theorem.lean` (the classical part, section A, is unchanged apart from namespace).
- Import both in `PhyslibAlpha.lean`; add `QuantumMechanics.OntologicalModel.PreparationIndependent.isPsiOntic` under `[PhyslibAlpha]` in `scripts/lint/exemptions/Theorems.txt` (sorted); spelling words as needed.

**Consumes:** `piProdVec`, `inner_piProdVec`, `norm_piProdVec_eq_one`, `norm_inner_lt_one_of_ofVec_ne` (Task 1); `orthonormalMeasurement`, `expectation_orthonormalMeasurement` (Task 2); `OntologicalModel`, `PreparationIndependent`, `IsPsiOntic` (Task 3); `QubitFrame`, `exists_qubitFrame`, `walsh` lemmas, `exists_two_mul_pow_le`, `exists_phases`, `sum_norm_sq_sum_mul_inv_sqrt_mul_walsh` (Task 4); `MeasureTheory.Measure.pi_mono` (Task 1).

**Produces (Measurement.lean, `QuantumMechanics.PBR.QubitFrame` namespace, `{n : ℕ}`):**
- `frameVec (F : QubitFrame ψ) (z : Fin n → Fin 2) : 𝓗[Fin n → d] := piProdVec fun i => F.e (z i)`; `inner_frameVec_frameVec : ⟪F.frameVec z, F.frameVec z'⟫_ℂ = if z = z' then 1 else 0`; `inner_frameVec_piProdVec (z x) : ⟪F.frameVec z, piProdVec fun i => ψ (x i)⟫_ℂ = (∏ i, F.phase (x i)) * walsh z x * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i)`; `sum_norm_sq_inner_frameVec_piProdVec (y) : ∑ z, ‖⟪F.frameVec z, piProdVec fun i => ψ (y i)⟫_ℂ‖ ^ 2 = 1`.
- `measurementVec (F) (ω : (Fin n → Fin 2) → ℂ) (x : Fin n → Fin 2) : 𝓗[Fin n → d] := ∑ z, ((Real.sqrt (2 ^ n))⁻¹ * starRingEnd ℂ (ω z) * walsh x z) • F.frameVec z` (no norm hypothesis in the definition); `inner_measurementVec`; `orthonormal_measurementVec (hω : ∀ z, ‖ω z‖ = 1) : Orthonormal ℂ (F.measurementVec ω)`; `inner_measurementVec_piProdVec_self (hsum : ∑ z, ω z * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i) = 0) (x) : ⟪F.measurementVec ω x, piProdVec fun i => ψ (x i)⟫_ℂ = 0`; `sum_norm_sq_inner_measurementVec (hω) (y) : ∑ x, ‖⟪F.measurementVec ω x, piProdVec fun i => ψ (y i)⟫_ℂ‖ ^ 2 = 1`.
- `PBR.exists_measurement (ψ : Fin 2 → 𝓗[d]) (hψ : ∀ b, ‖ψ b‖ = 1) (h : ofVec (𝕜 := ℂ) (hψ 0) ≠ ofVec (𝕜 := ℂ) (hψ 1)) : ∃ (n : ℕ) (M : Measurement (Fin n → Fin 2) (Observable (𝓗[Fin n → d] →L[ℂ] 𝓗[Fin n → d]))), ∀ x, (ofVec (norm_piProdVec_eq_one fun i => hψ (x i)))⟨M {x} (measurableSet_singleton x)⟩ = 0` — "outcome `x` never occurs on `ψ (x 0) ⊗ ⋯ ⊗ ψ (x (n - 1))`". Use `orthonormalMeasurement (orthonormal_measurementVec …) 0`: for `x ≠ 0` the probability is `‖⟪b x, Ψ x⟫‖ ^ 2 = 0`; for `x = 0` add the remainder `1 - ∑ y, ‖⟪b y, Ψ 0⟫‖ ^ 2 = 0` by Parseval.

**Produces (Theorem.lean):** `PBR.eq_zero_of_le_of_exists_lintegral_eq_zero`, `PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero` (unchanged statements), and
`theorem QuantumMechanics.OntologicalModel.PreparationIndependent.isPsiOntic {d Λ : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Λ] {M : OntologicalModel d Λ} {Λn : ℕ → Type*} [∀ n, MeasurableSpace (Λn n)] {Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Λn n)} (h : M.PreparationIndependent Mn) : M.IsPsiOntic` with the old docstring (bold title **Pusey–Barrett–Rudolph theorem.**), adapted.

- [ ] `lake build PhyslibAlpha.QuantumMechanics.Foundations.PBR.Theorem` → no errors/new warnings.
- [ ] Two commits (Measurement; Theorem + Theorems.txt).

