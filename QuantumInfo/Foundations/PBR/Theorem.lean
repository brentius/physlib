/-
Copyright (c) 2026 brent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: brent
-/
module

public import QuantumInfo.ForMathlib.MeasureTheory.Pi
public import QuantumInfo.Foundations.OntologicalModel
public import QuantumInfo.Foundations.PBR.Measurement

/-!
# The Pusey–Barrett–Rudolph theorem

Every preparation-independent ontological model of a quantum system is ψ-ontic.

## i. Overview

The Pusey–Barrett–Rudolph (PBR) theorem says that the quantum state is a real property of a
system rather than a state of knowledge about it. Precisely, consider an ontological model of a
finite-dimensional quantum system which reproduces the quantum statistics of every POVM, both
for one system and for `n` independently prepared systems, and which is preparation
independent: preparing `n` systems independently in the product state
`χ 0 ⊗ ⋯ ⊗ χ (n - 1)` (the ket `Ket.piProd χ`) gives independent ontic states
`l 0, …, l (n - 1)`, distributed according to `prep (χ 0), …, prep (χ (n - 1))`, which jointly
determine the ontic state `ι n l` of the `n` systems. The `n`-copy ontic space need not be the
Cartesian product of `n` copies of the single-copy one (taking it to be, with `ι n = id`, is
the Cartesian-product formulation, see `OntologicalModel.PreparationIndependent.of_prep_piProd`).
Then the preparation measures of any two distinct pure states are mutually singular, i.e. the
model is ψ-ontic.

The proof has a quantum part and a classical part. Fix two distinct pure states `ψ` and `φ`
and write `ψ₀ = ψ`, `ψ₁ = φ` (in Lean, `![ψ, φ]`). The quantum part is the PBR measurement
`PBR.exists_povm`: there is a POVM on `n` copies every outcome `o` of which has probability
zero on some product state `ψ_{x 0} ⊗ ⋯ ⊗ ψ_{x (n - 1)}`, for some `x : Fin n → Fin 2`
depending on `o`. Pulling the response functions of this POVM back along `ι n` gives functions
`ξ o` on `n`-tuples of single-copy ontic states. The classical part, proved here, shows that
this forces the preparation measures `μ 0 = prep ψ`, `μ 1 = prep φ` to be mutually singular: a
common lower bound `ν` of `μ 0` and `μ 1` satisfies
`ν(Λ) ^ n = ∑ o, ∫ ξ o dν^{⊗n} ≤ ∑ o, ∫ ξ o dμ_{x(o)}^{⊗n} = 0`.

## ii. Key results

- `PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero` : the classical part of the proof.
- `OntologicalModel.PreparationIndependent.isPsiOntic` : the PBR theorem.

## iii. Table of contents

- A. The classical part of the proof
- B. The PBR theorem

## iv. References

- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]
- N. Harrigan and R. W. Spekkens, *Einstein, incompleteness, and the epistemic view of quantum
  states*, Found. Phys. 40, 125–157 (2010), arXiv:0706.2661. [ref: Harrigan:2007wfc]

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PBR

/-!
## A. The classical part of the proof

-/

/-- Let `ξ o` be measurable response functions on `n` copies which sum to one at every point,
and suppose every outcome `o` integrates to zero against some product measure
`μ (x 0) ⊗ ⋯ ⊗ μ (x (n - 1))`. Then a finite measure `ν` with `ν ≤ μ b` for both `b : Fin 2`
is zero. -/
lemma eq_zero_of_le_of_exists_lintegral_eq_zero {Λ O : Type*}
    [MeasurableSpace Λ] [Fintype O] (μ : Fin 2 → Measure Λ) {n : ℕ}
    (ξ : O → (Fin n → Λ) → ℝ≥0∞) (hξ : ∀ o, Measurable (ξ o)) (hsum : ∀ l, ∑ o, ξ o l = 1)
    (hzero : ∀ o, ∃ x : Fin n → Fin 2, ∫⁻ l, ξ o l ∂Measure.pi (fun i => μ (x i)) = 0)
    (ν : Measure Λ) [IsFiniteMeasure ν] (hν : ∀ b, ν ≤ μ b) : ν = 0 := by
  have hle : ∀ o, ∫⁻ l, ξ o l ∂Measure.pi (fun _ : Fin n => ν) = 0 := fun o => by
    obtain ⟨x, hx⟩ := hzero o
    exact nonpos_iff_eq_zero.1 <|
      (lintegral_mono' (Measure.pi_mono fun i => hν (x i)) le_rfl).trans hx.le
  have hpi : Measure.pi (fun _ : Fin n => ν) Set.univ = 0 := by
    calc _ = ∫⁻ l, ∑ o, ξ o l ∂Measure.pi (fun _ : Fin n => ν) := by simp [hsum]
      _ = 0 := by
        rw [lintegral_finsetSum _ fun o _ => hξ o]
        exact Finset.sum_eq_zero fun o _ => hle o
  rw [Measure.pi_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hpi
  exact Measure.measure_univ_eq_zero.1 (pow_eq_zero_iff'.1 hpi).1

/-- The classical part of the PBR theorem: if every outcome `o` of a family of response
functions `ξ o` on `n` copies (measurable, summing to one) integrates to zero against some
product measure `μ (x 0) ⊗ ⋯ ⊗ μ (x (n - 1))`, then the finite measures `μ 0` and `μ 1` are
mutually singular. -/
lemma mutuallySingular_of_forall_exists_lintegral_eq_zero {Λ O : Type*} [MeasurableSpace Λ]
    [Fintype O] (μ : Fin 2 → Measure Λ) [∀ b, IsFiniteMeasure (μ b)] {n : ℕ}
    (ξ : O → (Fin n → Λ) → ℝ≥0∞) (hξ : ∀ o, Measurable (ξ o)) (hsum : ∀ l, ∑ o, ξ o l = 1)
    (hzero : ∀ o, ∃ x : Fin n → Fin 2, ∫⁻ l, ξ o l ∂Measure.pi (fun i => μ (x i)) = 0) :
    μ 0 ⟂ₘ μ 1 := by
  refine Measure.mutuallySingular_iff_disjoint.2 fun ν h0 h1 => le_bot_iff.2 ?_
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le (μ 0) h0
  exact eq_zero_of_le_of_exists_lintegral_eq_zero μ ξ hξ hsum hzero ν
    (Fin.forall_fin_two.2 ⟨h0, h1⟩)

end PBR

/-!
## B. The PBR theorem

-/

namespace OntologicalModel

/-- **Pusey–Barrett–Rudolph theorem.** An ontological model of a quantum system which
reproduces the quantum statistics of every POVM, for one system and for any number `n` of
systems, and which is preparation independent (independently prepared product states give
independent ontic states, which jointly determine the ontic state of the `n` systems) is
ψ-ontic: the preparation measures of any two pure states which differ as quantum states are
mutually singular. The `n`-copy ontic spaces `Λn n` are arbitrary. -/
theorem PreparationIndependent.isPsiOntic {d Λ : Type*} [Fintype d] [DecidableEq d]
    [MeasurableSpace Λ] {M : OntologicalModel d Λ} {Λn : ℕ → Type*}
    [∀ n, MeasurableSpace (Λn n)] {Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Λn n)}
    (h : M.PreparationIndependent Mn) : M.IsPsiOntic := by
  obtain ⟨ι, hι, h⟩ := h
  intro ψ φ hne
  -- the PBR measurement on `n` copies, every outcome of which excludes a product state
  obtain ⟨n, E, hE⟩ := PBR.exists_povm ![ψ, φ] hne
  -- its response functions, pulled back to `n`-tuples of single-copy ontic states
  refine PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero (fun b => M.prep (![ψ, φ] b))
    (fun o => (Mn n).resp E o ∘ ι n) (fun o => ((Mn n).measurable_resp E o).comp (hι n))
    (fun l => (Mn n).sum_resp E (ι n l)) fun o => ?_
  obtain ⟨x, hx⟩ := hE o
  have key := (Mn n).lintegral_resp E (Ket.piProd fun i => ![ψ, φ] (x i)) o
  rw [h n, lintegral_map ((Mn n).measurable_resp E o) (hι n), hx] at key
  exact ⟨x, by simpa using key⟩

end OntologicalModel
