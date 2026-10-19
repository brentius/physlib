/-
Copyright (c) 2026 brent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: brent
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import QuantumInfo.Measurements.POVM

/-!
# Ontological models of a quantum system

Ontological models of a finite-dimensional quantum system, ψ-ontic models and preparation
independence.

## i. Overview

An ontological model (in the sense of Harrigan and Spekkens) of a quantum system reproduces
the predictions of quantum mechanics by assigning to the system a "real" or ontic state `l` in a
measurable space `Λ`. Preparing the pure state `ψ` samples `l` from a probability measure
`prep ψ` on `Λ`, and measuring a POVM `E` in the ontic state `l` gives outcome `x` with
probability `resp E x l`. Averaging over `l` must give the Born rule.

The model is ψ-ontic if the ontic state determines the quantum state: the preparation measures
of two distinct pure states are mutually singular. Otherwise it is ψ-epistemic, and the quantum
state is (at least partly) a state of knowledge about `l`.

Pusey, Barrett and Rudolph (PBR) show that every model satisfying their preparation-independence
assumption is ψ-ontic. Preparation independence says that `n` independently prepared systems
have independent ontic states `l 0, …, l (n - 1)`, each distributed according to the
single-copy preparation measure, and that these jointly determine the ontic state of the `n`
systems: preparing the product state gives the ontic state `ι n (l 0, …, l (n - 1))` for some
measurable map `ι n`. The ontic space of the `n` systems need not be the Cartesian product of
`n` copies of `Λ`. Requiring it to be, with `ι n` the identity, is what Leifer calls the
Cartesian Product Assumption; it is strictly stronger, and it is recovered by
`OntologicalModel.PreparationIndependent.of_prep_piProd`. The PBR theorem itself is
`OntologicalModel.PreparationIndependent.isPsiOntic` in
`QuantumInfo/Foundations/PBR/Theorem.lean`.

## ii. Key results

- `OntologicalModel` : an ontological model of a quantum system with basis index type `d`.
- `OntologicalModel.IsPsiOntic` : the ψ-ontic property.
- `OntologicalModel.PreparationIndependent` : the PBR preparation-independence assumption.
- `OntologicalModel.PreparationIndependent.of_prep_piProd` : the Cartesian-product form of
  preparation independence implies preparation independence.

## iii. Table of contents

- A. Ontological models
- B. ψ-ontic models
- C. Preparation independence

## iv. References

- N. Harrigan and R. W. Spekkens, *Einstein, incompleteness, and the epistemic view of quantum
  states*, Found. Phys. 40, 125–157 (2010), arXiv:0706.2661. [ref: Harrigan:2007wfc]
- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]
- M. S. Leifer, *Is the quantum state real? An extended review of ψ-ontology theorems*,
  Quanta 3, 67–155 (2014), arXiv:1409.1570.

-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

/-!
## A. Ontological models

-/

/-- An ontological model (Harrigan–Spekkens) of the quantum system with basis index type `d`,
with ontic state space `Λ`.

Preparations are indexed by kets rather than by `MState`s. This is more general: a model whose
preparations depend only on `MState.pure ψ` is a special case, while here two kets differing by
a global phase, which have the same `MState.pure` and hence the same measurement statistics,
may be prepared with different measures. Only pure-state
preparations are modelled, as only these are needed for the PBR theorem. Measurements are
POVMs with a finite outcome type, and response functions take values in `ℝ≥0∞` so that they
can be integrated with the Lebesgue integral `∫⁻`. -/
structure OntologicalModel (d : Type*) [Fintype d] [DecidableEq d] (Λ : Type*)
    [MeasurableSpace Λ] where
  /-- The preparation measure: preparing the pure state `ψ` puts the system in an ontic state
  distributed according to `prep ψ`. -/
  prep : Ket d → Measure Λ
  /-- Each preparation measure is a probability measure on the ontic states. -/
  isProbabilityMeasure_prep (ψ : Ket d) : IsProbabilityMeasure (prep ψ)
  /-- The response function: `resp E x l` is the probability of obtaining the outcome `x` when
  measuring the POVM `E` on a system in the ontic state `l`. -/
  resp {X : Type} [Fintype X] [DecidableEq X] : POVM X d → X → Λ → ℝ≥0∞
  /-- The response functions are measurable, so they can be averaged over a preparation. -/
  measurable_resp {X : Type} [Fintype X] [DecidableEq X] (E : POVM X d) (x : X) :
    Measurable (resp E x)
  /-- In every ontic state, measuring `E` gives some outcome: the response probabilities sum
  to one. -/
  sum_resp {X : Type} [Fintype X] [DecidableEq X] (E : POVM X d) (l : Λ) : ∑ x, resp E x l = 1
  /-- The model reproduces the Born rule: averaging the response function over the preparation
  measure of `ψ` gives the quantum probability of outcome `x` on the pure state `ψ`. -/
  lintegral_resp {X : Type} [Fintype X] [DecidableEq X] (E : POVM X d) (ψ : Ket d) (x : X) :
    ∫⁻ l, resp E x l ∂prep ψ = ENNReal.ofReal (E.measure (MState.pure ψ) x)

attribute [instance] OntologicalModel.isProbabilityMeasure_prep

namespace OntologicalModel

variable {d : Type*} [Fintype d] [DecidableEq d] {Λ : Type*} [MeasurableSpace Λ]

/-!
## B. ψ-ontic models

-/

/-- An ontological model is ψ-ontic if the preparation measures of any two distinct pure
states are mutually singular, so that the ontic state determines the quantum state. Two kets
are distinct as quantum states when their `MState.pure`s differ, i.e. when they are not equal
up to a global phase; kets differing only by a phase may share ontic states. -/
def IsPsiOntic (M : OntologicalModel d Λ) : Prop :=
  ∀ ψ φ : Ket d, MState.pure ψ ≠ MState.pure φ → M.prep ψ ⟂ₘ M.prep φ

/-!
## C. Preparation independence

-/

/-- The preparation-independence assumption of Pusey, Barrett and Rudolph for the model `M`,
relative to a family of models `Mn n` of `n` copies of the system (basis index `Fin n → d`,
ontic states `Λn n`). It asks that `n` independently prepared systems have independent ontic
states which jointly determine the ontic state of the `n` copies: there are measurable maps
`ι n : (Fin n → Λ) → Λn n` such that preparing the product state `Ket.piProd ψ` gives the ontic
state `ι n l`, where the `l i` are independent and distributed according to `M.prep (ψ i)`.

The ontic space `Λn n` need not be the Cartesian product `Fin n → Λ`; taking `Λn n = Fin n → Λ`
and `ι n = id` gives the stronger Cartesian Product Assumption (in Leifer's terminology), see
`PreparationIndependent.of_prep_piProd`. -/
def PreparationIndependent (M : OntologicalModel d Λ) {Λn : ℕ → Type*}
    [∀ n, MeasurableSpace (Λn n)] (Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Λn n)) : Prop :=
  ∃ ι : (n : ℕ) → (Fin n → Λ) → Λn n, (∀ n, Measurable (ι n)) ∧ ∀ (n : ℕ) (ψ : Fin n → Ket d),
    (Mn n).prep (Ket.piProd ψ) = (Measure.pi fun i => M.prep (ψ i)).map (ι n)

/-- The Cartesian-product form of preparation independence: if the `n`-copy models have ontic
space `Fin n → Λ` and prepare the product state `Ket.piProd ψ` with the product of the
measures `M.prep (ψ i)`, then `M` is preparation independent (with `ι n = id`). -/
lemma PreparationIndependent.of_prep_piProd {M : OntologicalModel d Λ}
    {Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Fin n → Λ)}
    (h : ∀ n (ψ : Fin n → Ket d), (Mn n).prep (Ket.piProd ψ) = Measure.pi fun i => M.prep (ψ i)) :
    M.PreparationIndependent Mn :=
  ⟨fun _ => id, fun _ => measurable_id, fun n ψ => by rw [h, Measure.map_id]⟩

end OntologicalModel
