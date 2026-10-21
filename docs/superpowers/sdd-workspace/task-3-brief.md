### Task 3: Ontological models

**Files:** Create `PhyslibAlpha/QuantumMechanics/Foundations/OntologicalModel.lean` (unverified draft exists); import it in `PhyslibAlpha.lean`; add the bib entries `Harrigan:2007wfc` and `Pusey:2011de` to `docs/references.bib` (copy them verbatim from `git show pbr-theorem:docs/references.bib`, keeping the file's ordering convention); add any new words the spell-checker trips on to `scripts/lint/exemptions/spellingWords.txt` (sorted; the old branch added `epistemic`, `harrigan`, `ontic`, `pusey`, `rudolph`, `spekkens`).

**Consumes:** Tasks 1 and 2 (`piProdVec`, `norm_piProdVec_eq_one`, Alpha `Measurement`).

**Produces (in `QuantumMechanics`):**
- `structure OntologicalModel (d : Type*) [Fintype d] [DecidableEq d] (Λ : Type*) [MeasurableSpace Λ]` with fields `prep (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1) : Measure Λ`; `isProbabilityMeasure_prep` (made an instance); `resp {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] : Measurement X (Observable (𝓗[d] →L[ℂ] 𝓗[d])) → X → Λ → ℝ≥0∞`; `measurable_resp`; `sum_resp (M) (l) : ∑ x, resp M x l = 1`; `lintegral_resp (M) (ψ) (hψ) (x) : ∫⁻ l, resp M x l ∂prep ψ hψ = ENNReal.ofReal ((ofVec hψ)⟨M {x} (measurableSet_singleton x)⟩)`.
- `OntologicalModel.IsPsiOntic (M) : Prop := ∀ (ψ φ : 𝓗[d]) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1), ofVec (𝕜 := ℂ) hψ ≠ ofVec (𝕜 := ℂ) hφ → M.prep ψ hψ ⟂ₘ M.prep φ hφ`.
- `OntologicalModel.PreparationIndependent (M) (Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Λn n)) : Prop := ∃ ι : (n : ℕ) → (Fin n → Λ) → Λn n, (∀ n, Measurable (ι n)) ∧ ∀ n (ψ : Fin n → 𝓗[d]) (hψ : ∀ i, ‖ψ i‖ = 1), (Mn n).prep (piProdVec ψ) (norm_piProdVec_eq_one hψ) = (Measure.pi fun i => M.prep (ψ i) (hψ i)).map (ι n)`.
- `OntologicalModel.PreparationIndependent.of_prep_piProdVec` (Cartesian product assumption ⇒ preparation independence, `ι n = id`).

- [ ] `lake build PhyslibAlpha.QuantumMechanics.Foundations.OntologicalModel` → no errors/new warnings; `lake exe module_doc_lint` passes for the file.
- [ ] One commit (file + bib + spelling + `PhyslibAlpha.lean`).

