# The PBR theorem in physlib — a review walkthrough

This document walks through the formalisation of the general Pusey–Barrett–Rudolph (PBR)
theorem on branch `pbr-theorem` (all changes uncommitted). It explains *what* is stated, *why*
the statement is the right one, and *how* each sub-proof works, in the order you would want to
check it. Every Lean name below is a real declaration; file paths are relative to the repo
root. The companion file `docs/superpowers/pbr-summary.md` has the verification log and the
list of rulings; this file is about the mathematics and its encoding.

Contents

1. Notation and conventions
2. The theorem, informally and in Lean
3. The definitions (the part you must certify most carefully)
4. Proof architecture at a glance
5. The classical half: from "every outcome is excluded" to mutual singularity
6. The headline proof: gluing the two halves
7. The quantum half: the PBR measurement
   - 7.1 The qubit frame of two states
   - 7.2 Signs, Walsh characters, the number of copies, the phases
   - 7.3 The measurement kets and their inner products
   - 7.4 Turning orthonormal kets into a POVM
   - 7.5 `exists_povm`: assembling the measurement
8. General lemmas added to existing files
9. How this relates to the PBR paper
10. Edge cases and how they are handled
11. Review checklist
12. Re-checking it yourself

---

## 1. Notation and conventions

- A quantum system has a finite basis index type `d`; a pure state is a `Ket d`
  (`QuantumInfo/States/Pure/Braket.lean`): a function `d → ℂ` with `∑ x, ‖ψ x‖² = 1`.
- `〈ψ‖φ〉` (scoped notation `Braket.dot`) is `∑ x, conj (ψ x) * φ x`. It is linear in the right
  argument and conjugate-linear in the left.
- `Ket.piProd ψ` for `ψ : Fin n → Ket d` is the tensor product `ψ 0 ⊗ ⋯ ⊗ ψ (n-1)`, a ket on
  `Fin n → d` with amplitude `∏ i, ψ i (k i)` at the basis index `k`.
- `MState.pure ψ` is the density matrix `|ψ⟩⟨ψ|`. Two kets are the *same quantum state* iff
  their `MState.pure` agree, iff they differ by a global phase (`MState.pure_eq_pure_iff`).
- A `POVM X d` is a family of positive semidefinite `HermitianMat`s indexed by a finite outcome
  type `X`, summing to `1`; `E.measure ρ : ProbDistribution X` gives Born probabilities
  `⟪E x, ρ⟫`. Probabilities have type `Prob` (a real in `[0,1]`); `(p : ℝ)` is its value.
- Measure theory is Mathlib's: `Measure Λ`, `∫⁻` (Lebesgue integral of `ℝ≥0∞`-valued
  functions), `Measure.pi` (finite product measure), `μ ⟂ₘ ν` (mutual singularity: some
  measurable set is null for `μ` and co-null for `ν`).
- The pair of states in the theorem is passed to the quantum lemmas as `![ψ, φ] : Fin 2 → Ket d`,
  so `ψ 0`, `ψ 1` in those lemmas are the two states; a string `x : Fin n → Fin 2` selects the
  product state `Ψ x = ψ (x 0) ⊗ ⋯ ⊗ ψ (x (n-1))`, written `Ket.piProd fun i => ψ (x i)`.

## 2. The theorem, informally and in Lean

**Informal.** Take any ontological model of a finite-dimensional quantum system: preparing a
pure state samples an ontic state from a probability measure, measuring a POVM in an ontic state
gives each outcome with some probability, and averaging reproduces the Born rule. Suppose it is
*preparation independent*: independently preparing `n` systems in pure states gives independent
ontic states which together determine the ontic state of the `n` systems (which also satisfies
the Born rule, for measurements on all `n` systems). Then any two distinct pure states have
mutually singular ontic distributions: the ontic state determines which of them was prepared.

**Lean** (`QuantumInfo/Foundations/PBR/Theorem.lean`):

```lean
theorem OntologicalModel.PreparationIndependent.isPsiOntic {d Λ : Type*} [Fintype d]
    [DecidableEq d] [MeasurableSpace Λ] {M : OntologicalModel d Λ} {Λn : ℕ → Type*}
    [∀ n, MeasurableSpace (Λn n)] {Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Λn n)}
    (h : M.PreparationIndependent Mn) : M.IsPsiOntic
```

Unfolding `IsPsiOntic`, the conclusion is
`∀ ψ φ : Ket d, MState.pure ψ ≠ MState.pure φ → M.prep ψ ⟂ₘ M.prep φ`.

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` — the standard Lean axioms, no
`sorry`.

## 3. The definitions (the part you must certify most carefully)

All in `QuantumInfo/Foundations/OntologicalModel.lean`. A machine-checked proof only certifies
that the *stated* theorem follows; whether it is *the PBR theorem* depends entirely on these.

### 3.1 `OntologicalModel d Λ`

```lean
structure OntologicalModel (d : Type*) [Fintype d] [DecidableEq d] (Λ : Type*)
    [MeasurableSpace Λ] where
  prep : Ket d → Measure Λ
  isProbabilityMeasure_prep (ψ : Ket d) : IsProbabilityMeasure (prep ψ)
  resp {X : Type} [Fintype X] [DecidableEq X] : POVM X d → X → Λ → ℝ≥0∞
  measurable_resp ... : Measurable (resp E x)
  sum_resp ... (E : POVM X d) (l : Λ) : ∑ x, resp E x l = 1
  lintegral_resp ... (E : POVM X d) (ψ : Ket d) (x : X) :
    ∫⁻ l, resp E x l ∂prep ψ = ENNReal.ofReal (E.measure (MState.pure ψ) x)
```

Points to check, and the reasoning behind each choice:

- **Preparations are indexed by kets, not by quantum states.** This is *more* general than
  indexing by `MState`: a model may prepare `ψ` and `e^{iθ}ψ` differently. (Any model indexed by
  states gives one indexed by kets.) Only pure-state preparations are modelled — PBR needs no
  more.
- **One response function per POVM.** Every POVM with a finite outcome type in `Type` has a
  response function. A model with several measurement procedures per POVM can be restricted to
  one procedure per POVM, so this loses no generality for PBR, which uses one measurement.
- **Response functions are `ℝ≥0∞`-valued**, measurable, and sum to `1` at every ontic state
  (so each is automatically `≤ 1`). `ℝ≥0∞` lets us use `∫⁻` with no integrability side
  conditions.
- **Born rule.** `ENNReal.ofReal` of the real value of the `Prob` returned by `POVM.measure`.
  Since that value is in `[0,1]`, `ofReal` loses nothing.
- `isProbabilityMeasure_prep` is registered as an instance, so `Measure.pi` of preparation
  measures finds `SigmaFinite` automatically.

**Non-vacuity check (scratch test `Task4.lean`).** The Beltrametti–Bugajski model — ontic
states are kets (`⊤` σ-algebra), `prep ψ = dirac ψ`, `resp E x l = ofReal (E.measure (pure l) x)`
— was built as an `OntologicalModel (Fin 2) (Ket (Fin 2))`, every field proved, and shown
`IsPsiOntic` (separating set `{ψ}ᶜ`). So the structure is satisfiable and not secretly
contradictory.

### 3.2 `IsPsiOntic`

```lean
def IsPsiOntic (M : OntologicalModel d Λ) : Prop :=
  ∀ ψ φ : Ket d, MState.pure ψ ≠ MState.pure φ → M.prep ψ ⟂ₘ M.prep φ
```

This is Harrigan–Spekkens ψ-onticity: distinct states have disjoint supports (up to null sets).
"Distinct" means *different quantum states* — kets differing only by a global phase are
correctly exempt.

### 3.3 `PreparationIndependent`

```lean
def PreparationIndependent (M : OntologicalModel d Λ) {Λn : ℕ → Type*}
    [∀ n, MeasurableSpace (Λn n)] (Mn : (n : ℕ) → OntologicalModel (Fin n → d) (Λn n)) : Prop :=
  ∃ ι : (n : ℕ) → (Fin n → Λ) → Λn n, (∀ n, Measurable (ι n)) ∧ ∀ (n : ℕ) (ψ : Fin n → Ket d),
    (Mn n).prep (Ket.piProd ψ) = (Measure.pi fun i => M.prep (ψ i)).map (ι n)
```

Read: for each `n` there is an ontological model `Mn n` of `n` copies of the system (basis index
`Fin n → d`, its own ontic space `Λn n`), and a measurable way `ι n` to combine `n` single-copy
ontic states into an `n`-copy ontic state, such that preparing the product state
`ψ 0 ⊗ ⋯ ⊗ ψ (n-1)` produces `ι n (l 0, …, l (n-1))` with the `l i` independent and
`l i ∼ M.prep (ψ i)`.

- This is PBR's assumption: "systems prepared independently have independent physical states",
  and the measuring device's response depends on those physical states.
- `Mn n` must reproduce the Born rule for *every* POVM on the `n`-copy system and *every*
  `n`-copy ket (including entangled ones) — that is what "ontological model of `n` copies"
  means. PBR's proof only uses product preparations and one entangled measurement, but a model
  of quantum theory must handle the rest too.
- **History of this definition.** The first version required `Λn n = Fin n → Λ` and `ι n = id`
  (the Cartesian product of ontic spaces). The final whole-branch review pointed out that this is
  Leifer's *Cartesian Product Assumption*, strictly stronger than PBR needs, and that even the
  Beltrametti–Bugajski model cannot satisfy it (it would need entangled kets to be prepared on
  tuples of single kets). The definition was therefore generalised to the form above, which
  makes the theorem *stronger* (weaker hypothesis). The old form is recovered by
  `PreparationIndependent.of_prep_piProd` (take `ι n = id`; `Measure.map_id`).

## 4. Proof architecture at a glance

```
OntologicalModel.PreparationIndependent.isPsiOntic            (Theorem.lean, §6)
├── PBR.exists_povm                                            (Measurement.lean, §7.5)
│   ├── PBR.exists_qubitFrame                                  (QubitFrame.lean, §7.1)
│   ├── PBR.exists_two_mul_pow_le         choice of n          (Phases.lean, §7.2)
│   ├── PBR.exists_phases                 choice of ω          (Phases.lean, §7.2)
│   ├── QubitFrame.measurementKet + inner products             (Measurement.lean, §7.3)
│   │   ├── Braket.dot_piProd, Braket.sum_norm_sq_sum_mul_of_orthonormal   (Braket.lean, §8)
│   │   └── PBR.sum_walsh_mul_walsh, PBR.sum_conj_inv_sqrt_mul_walsh       (Phases.lean)
│   └── POVM.ofOrthonormal + measure_ofOrthonormal_some/none   (POVM.lean, §7.4)
└── PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero    (Theorem.lean, §5)
    ├── Measure.mutuallySingular_iff_disjoint                  (Mathlib)
    └── MeasureTheory.Measure.pi_mono                          (ForMathlib/MeasureTheory/Pi.lean)
```

The split mirrors the paper: a **quantum** fact (there is a measurement on `n` copies each of
whose outcomes is impossible for one of the `2ⁿ` product states) and a **classical** fact (no
probability theory over ontic states can reproduce that unless the two preparation measures are
disjoint).

## 5. The classical half

File: `QuantumInfo/Foundations/PBR/Theorem.lean`, section A. Purely measure-theoretic; no
quantum mechanics.

### 5.1 Statement

```lean
lemma PBR.mutuallySingular_of_forall_exists_lintegral_eq_zero {Λ O : Type*} [MeasurableSpace Λ]
    [Fintype O] (μ : Fin 2 → Measure Λ) [∀ b, IsFiniteMeasure (μ b)] {n : ℕ}
    (ξ : O → (Fin n → Λ) → ℝ≥0∞) (hξ : ∀ o, Measurable (ξ o)) (hsum : ∀ l, ∑ o, ξ o l = 1)
    (hzero : ∀ o, ∃ x : Fin n → Fin 2, ∫⁻ l, ξ o l ∂Measure.pi (fun i => μ (x i)) = 0) :
    μ 0 ⟂ₘ μ 1
```

`ξ o` are "response functions on `n`-tuples of ontic states" for a finite outcome set `O`; they
sum to one everywhere; each outcome `o` integrates to zero against some product measure
`μ (x 0) ⊗ ⋯ ⊗ μ (x (n-1))` (some choice of preparing state `0` or state `1` in each slot).

### 5.2 Mathematical proof

1. Mathlib: `μ 0 ⟂ₘ μ 1 ↔ Disjoint (μ 0) (μ 1)` in the lattice of measures
   (`Measure.mutuallySingular_iff_disjoint`). So it suffices: every measure `ν` with `ν ≤ μ 0`
   and `ν ≤ μ 1` is zero.
2. Such a `ν` is finite (`isFiniteMeasure_of_le`), so `ν^{⊗n} := Measure.pi (fun _ => ν)` makes
   sense.
3. Since `ν ≤ μ b` for both `b`, `ν^{⊗n} ≤ μ (x 0) ⊗ ⋯ ⊗ μ (x (n-1))` for *every* `x`
   (`Measure.pi_mono`, new lemma). Hence for each `o`, with the `x` from `hzero`:
   `∫ ξ o dν^{⊗n} ≤ ∫ ξ o d(μ_x) = 0` (`lintegral_mono'`).
4. Sum over `o`: `ν^{⊗n}(univ) = ∫ 1 dν^{⊗n} = ∫ ∑_o ξ o dν^{⊗n} = ∑_o ∫ ξ o dν^{⊗n} = 0`
   (`hsum`, `lintegral_finsetSum` using measurability).
5. `ν^{⊗n}(univ) = ν(univ)ⁿ` (`Measure.pi_univ`), so `ν(univ)ⁿ = 0`, so `ν(univ) = 0`
   (`pow_eq_zero_iff'`), so `ν = 0` (`Measure.measure_univ_eq_zero`).

The helper `PBR.eq_zero_of_le_of_exists_lintegral_eq_zero` is steps 2–5; the main lemma does
step 1 and calls it.

### 5.3 Why this is the rigorous version of the paper's step

The paper argues with an "overlap region" `Δ` that both preparations hit with probability at
least `q > 0`. Taken literally that is not enough (two mutually singular measures can both give
a set positive mass). The correct notion is a *common sub-measure* `ν ≤ μ 0, μ 1` with `ν ≠ 0`,
which is exactly what non-mutual-singularity provides via `Disjoint`. Then `ν^{⊗n}` is a common
lower bound of all `2ⁿ` product preparations, which is the paper's "λ is compatible with all
`2ⁿ` preparations" made precise.

### 5.4 `Measure.pi_mono`

`QuantumInfo/ForMathlib/MeasureTheory/Pi.lean`: `(h : ∀ i, μ i ≤ ν i) → Measure.pi μ ≤ Measure.pi ν`,
with no σ-finiteness assumption. Proof: on a measurable set, `Measure.pi` is the outer measure
`OuterMeasure.pi`; `OuterMeasure.le_pi` reduces the comparison to boxes, where
`OuterMeasure.pi_pi_le` and `Finset.prod_le_prod` with `μ i (t i) ≤ ν i (t i)` finish. Not in
Mathlib (checked).

## 6. The headline proof

`OntologicalModel.PreparationIndependent.isPsiOntic`, 9 lines:

1. Unpack `h` into `ι`, its measurability `hι`, and the product-preparation equations.
2. Fix `ψ φ` with `MState.pure ψ ≠ MState.pure φ`.
3. `PBR.exists_povm ![ψ, φ] hne` gives `n` and a POVM `E` on `n` copies such that every outcome
   `o` has Born probability `0` on some product state `Ket.piProd fun i => ![ψ, φ] (x i)`.
4. Apply the classical lemma with `μ b = M.prep (![ψ, φ] b)` and
   `ξ o = (Mn n).resp E o ∘ ι n` — the `n`-copy response functions pulled back to tuples of
   single-copy ontic states. Measurability: composition with measurable `ι n`. Sum to one:
   `(Mn n).sum_resp` at `ι n l`.
5. The zero-integral hypothesis: by the Born rule of `Mn n` for the product state,
   `∫⁻ resp E o ∂(Mn n).prep (piProd …) = ofReal (E.measure … o) = 0`. Rewriting the preparation
   with `h n` turns the left side into an integral against `(Measure.pi …).map (ι n)`, and
   `lintegral_map` turns that into `∫⁻ (resp E o ∘ ι n) ∂Measure.pi …` — exactly `ξ o`.
6. The conclusion `μ 0 ⟂ₘ μ 1` is `M.prep ψ ⟂ₘ M.prep φ` because `![ψ, φ] 0 = ψ` and
   `![ψ, φ] 1 = φ` definitionally.

## 7. The quantum half: the PBR measurement

Goal (`PBR.exists_povm`, `QuantumInfo/Foundations/PBR/Measurement.lean`):

```lean
lemma PBR.exists_povm {d : Type*} [Fintype d] [DecidableEq d] (ψ : Fin 2 → Ket d)
    (h : MState.pure (ψ 0) ≠ MState.pure (ψ 1)) :
    ∃ (n : ℕ) (E : POVM (Option (Fin n → Fin 2)) (Fin n → d)), ∀ o, ∃ x : Fin n → Fin 2,
      E.measure (MState.pure (Ket.piProd fun i => ψ (x i))) o = 0
```

The mathematical idea in one paragraph: write both states in a 2-dimensional orthonormal frame
`e 0, e 1` as `ψ_b = phase_b (c e₀ + (-1)^b s e₁)` with `c ≥ s > 0`. Expand the `2ⁿ` product
states in the product frame `E z = e (z 0) ⊗ ⋯ ⊗ e (z (n-1))`. A "Walsh–Hadamard after phases"
basis `b x = 2^{-n/2} ∑ z conj(ω z) walsh(x,z) E z` has `⟨b x|Ψ x⟩ ∝ ∑ z ω z ∏ i amp(z i)`,
independent of `x`; choosing unit phases `ω` that make that sum vanish (possible once
`2cⁿ ≤ (c+s)ⁿ`) makes every `b x` orthogonal to its own product state `Ψ x`. Adding the complement
projector gives a POVM whose extra outcome never fires on product states.

### 7.1 The qubit frame of two states

File: `QuantumInfo/Foundations/PBR/QubitFrame.lean`.

**The structure** (`PBR.QubitFrame ψ`): kets `e : Fin 2 → Ket d`, reals `c s`, phases
`phase : Fin 2 → ℂ`, with

- `s_pos : 0 < s`, `s_le_c : s ≤ c`, `sq_add_sq : c² + s² = 1`, `norm_phase : ‖phase b‖ = 1`,
- `dot_e_e : 〈e j‖e k〉 = if j = k then 1 else 0` (orthonormal),
- `dot_e_state : 〈e j‖ψ b〉 = phase b * sign j b * ![c, s] j`.

So `〈e 0‖ψ b〉 = phase b · c` and `〈e 1‖ψ b〉 = ± phase b · s` with the minus sign exactly for
`b = 1`. Two derived facts: `c_pos` and `sum_norm_sq_dot_e_state : ∑ j, ‖〈e j‖ψ b〉‖² = 1`
(each `ψ b` lies in the span of the frame).

**Existence** (`PBR.exists_qubitFrame`, assuming `MState.pure (ψ 0) ≠ MState.pure (ψ 1)`):

1. **Align the overlap.** Let `γ = 〈ψ 0‖ψ 1〉` and `ζ = exp(-i arg γ)`; then `‖ζ‖ = 1` and
   `ζ γ = r := ‖γ‖ ≥ 0` (`exp_neg_arg_mul_self`, from Mathlib's
   `Complex.norm_mul_exp_arg_mul_I`). Rotating `ψ 1` by `ζ` makes the overlap real and
   nonnegative — but rather than rotating the ket (which would change the preparation in the
   model!), the phase is carried into the frame data.
2. **Inner products of `ψ ± ζφ`** (section A.1, with `ψ = ψ 0`, `φ = ψ 1`): using only
   `〈ψ‖ψ〉 = 〈φ‖φ〉 = 1`, `ζ〈ψ‖φ〉 = r`, `conj ζ · ζ = 1`:
   - `‖ψ + ζφ‖² = 2 + 2r`, `‖ψ − ζφ‖² = 2 − 2r` (`sum_norm_sq_add/sub`),
   - `(ψ + ζφ)†(ψ − ζφ) = 0` (orthogonal),
   - `(ψ + ζφ)†ψ = 1 + r`, `(ψ + ζφ)†φ = conj ζ (1 + r)`,
     `(ψ − ζφ)†ψ = 1 − r`, `(ψ − ζφ)†φ = −conj ζ (1 − r)`.
   Each is a `simp` expansion of the dot product followed by `linear_combination`.
3. **`r < 1`** (`lt_one_of_pure_ne`): if `r ≥ 1` then `‖ψ − ζφ‖² = 2 − 2r ≤ 0`, so `ψ = ζφ`
   pointwise, so `MState.pure ψ = MState.pure φ` (`MState.pure_eq_pure_iff`), contradiction.
   This is the only place the hypothesis "distinct quantum states" is used in the quantum half.
4. **Normalise.** `e 0 = Ket.normalize (ψ + ζφ)`, `e 1 = Ket.normalize (ψ − ζφ)` (both vectors
   are nonzero since their squared norms `2 ± 2r` are positive). Dividing the inner products by
   `√(2 ± 2r)` and simplifying `a / √(2a) = √(a/2)` gives
   `c = √((1 + r)/2)`, `s = √((1 − r)/2)`, `phase = ![1, conj ζ]` and the table
   `〈e 0‖ψ 0〉 = c`, `〈e 0‖ψ 1〉 = conj ζ · c`, `〈e 1‖ψ 0〉 = s`, `〈e 1‖ψ 1〉 = −conj ζ · s`
   (`dot_normalize_add_left/right`, `dot_normalize_sub_left/right`).
5. `s > 0 ⇔ r < 1`; `s ≤ c ⇔ r ≥ 0`; `c² + s² = 1` by arithmetic. All packaged as
   `QubitFrame.ofPhase`.

(In the paper's notation `r = |⟨ψ₀|ψ₁⟩| = cos θ`, `c = cos(θ/2)`, `s = sin(θ/2)`.)

### 7.2 Signs, Walsh characters, the number of copies, the phases

File: `QuantumInfo/Foundations/PBR/Phases.lean` — pure mathematics, imports only Mathlib.

**Signs and Walsh characters (§A).** `sign j k = -1` if `j = k = 1`, else `1` (i.e.
`(-1)^{jk}`), with `sign_comm`, `sign_mul_self`, `conj_sign` (real), `norm_sign`, and
`sum_sign_mul_sign : ∑ k, sign a k · sign b k = if a = b then 2 else 0`.
`walsh x z = ∏ i, sign (x i) (z i)` on `Fin n → Fin 2`, with the analogous symmetry, square-one,
reality and unit-norm lemmas, and the key **orthogonality**

`sum_walsh_mul_walsh : ∑ z, walsh x z · walsh y z = if x = y then 2ⁿ else 0`.

Proof: the sum over `z` of a product over `i` is the product over `i` of sums
(`Fintype.prod_sum`): `∏ i, ∑ k, sign (x i) k · sign (y i) k`; each factor is `2` or `0`, and
some factor is `0` unless `x = y`.

**Number of copies (§B).** `exists_two_mul_pow_le (hc : 0 < c) (hs : 0 < s) :
∃ n, 2 cⁿ ≤ (c + s)ⁿ`. Proof: Bernoulli `(1 + t)ⁿ ≥ 1 + n t` with `t = s/c` and `n ≥ c/s`, so
`(1 + s/c)ⁿ ≥ 2`; multiply by `cⁿ`. This is the paper's condition `2^{1/n} − 1 ≤ tan(θ/2)`.

**Choosing the angle (§C.1).** `exists_norm_pow_sub_pow_eq (hs : 0 ≤ s) (hsc : s ≤ c)
(hn : 2cⁿ ≤ (c+s)ⁿ) : ∃ α, ‖(c + e^{iα} s)ⁿ − cⁿ‖ = cⁿ`. Proof: the function
`f α = ‖(c + e^{iα}s)ⁿ − cⁿ‖` is continuous on `[0, π]` (`fun_prop`); `f 0 = (c+s)ⁿ − cⁿ ≥ cⁿ`
by `hn`; `f π = |(c − s)ⁿ − cⁿ| = cⁿ − (c−s)ⁿ ≤ cⁿ` because `0 ≤ c − s ≤ c`; the intermediate
value theorem (`intermediate_value_Icc'`) gives `α` with `f α = cⁿ`.

**The phases (§C.2–C.3).** With that `α`, `e := e^{iα}` and `w := (c + e s)ⁿ − cⁿ`, define

- `ω 0 = −w / cⁿ` (unit modulus, because `‖w‖ = cⁿ`),
- `ω z = ∏ i, ![1, e] (z i)` for `z ≠ 0` (i.e. `e^{iα · (number of ones in z)}`, unit modulus).

Then (`sum_phases_mul_amp`) `∑ z, ω z · ∏ i ![c, s] (z i) = 0`. Proof: for `z ≠ 0` the term is
`∏ i ![c, e s] (z i)`; for `z = 0` it is `−w = cⁿ − (c + es)ⁿ = ∏ i ![c, es](0) − (c + es)ⁿ`. So
the whole sum is `∑ z ∏ i ![c, es] (z i) − (c + es)ⁿ = (c + es)ⁿ − (c + es)ⁿ = 0`, using
`∑ z ∏ i f (z i) = (∑ k f k)ⁿ` (`Fintype.sum_pow`). Packaged as `exists_phases`.

**Rescaled Walsh vectors (§D).** `sum_conj_inv_sqrt_mul_walsh`: the `2ⁿ` vectors
`x ↦ (√2ⁿ)⁻¹ · walsh x z` (indexed by `z`) are orthonormal — immediate from Walsh orthogonality
and reality. `sum_norm_sq_inv_sqrt_mul`: `2ⁿ` unit scalars scaled by `(√2ⁿ)⁻¹` have total
squared norm `1`. Two small arithmetic helpers compute `((√2ⁿ)⁻¹)² = (2ⁿ)⁻¹`.

### 7.3 The measurement kets and their inner products

File: `QuantumInfo/Foundations/PBR/Measurement.lean`. Fix a frame `F : QubitFrame ψ` and unit
phases `ω` (`hω : ∀ z, ‖ω z‖ = 1`).

**Product frame (§A).** `F.frameKet z = Ket.piProd fun i => F.e (z i)` (`= E z`).

- `dot_frameKet_frameKet : 〈E z‖E z'〉 = if z = z' then 1 else 0` — from
  `Braket.dot_piProd` (bra-ket of tensor products is the product of bra-kets) and the frame's
  orthonormality.
- `dot_frameKet_piProd : 〈E z‖Ψ x〉 = (∏ i, phase (x i)) · walsh z x · ∏ i, ![c, s] (z i)` —
  `dot_piProd` plus the frame table `dot_e_state`, regrouped.
- `sum_norm_sq_dot_frameKet_piProd : ∑ z, ‖〈E z‖Ψ y〉‖² = 1` — product of the per-copy
  identities `∑ j ‖〈e j‖ψ b〉‖² = 1` (`Fintype.prod_sum` again).

**Measurement kets (§B.1).**

```lean
def measurementKet (ω) (hω) (x : Fin n → Fin 2) : Ket (Fin n → d) where
  vec k := ∑ z, ((√(2^n))⁻¹ * conj (ω z) * walsh x z) * F.frameKet z k
```

Its normalisation `∑ k ‖b x k‖² = 1` is Parseval for the orthonormal `E z`
(`Braket.sum_norm_sq_sum_mul_of_orthonormal`) applied to coefficients of modulus `(√2ⁿ)⁻¹`
(`sum_norm_sq_inv_sqrt_mul`). Then:

- `dot_measurementKet : 〈b x‖φ〉 = ∑ z, (√2ⁿ)⁻¹ · ω z · walsh x z · 〈E z‖φ〉` (conjugating the
  coefficients: `conj (conj ω) = ω`, Walsh characters are real).

**Orthonormality (§B.2).** `dot_frameKet_measurementKet : 〈E z‖b y〉 = (√2ⁿ)⁻¹ conj(ω z) walsh y z`
and then `dot_measurementKet_measurementKet : 〈b x‖b y〉 = if x = y then 1 else 0`:
`∑ z 2^{-n} |ω z|² walsh x z walsh y z = 2^{-n} · (2ⁿ or 0)`.

**The two key identities (§B.3).**

- `dot_measurementKet_piProd_self (hsum : ∑ z, ω z ∏ i ![c, s] (z i) = 0) :
  〈b x‖Ψ x〉 = 0`. Computation:
  `〈b x‖Ψ x〉 = ∑ z (√2ⁿ)⁻¹ ω z walsh x z · (∏ phase (x i)) walsh z x A z`
  `= (√2ⁿ)⁻¹ (∏ phase (x i)) ∑ z ω z A z = 0`, since `walsh x z · walsh z x = 1` (symmetry and
  square-one). Note the dependence on `x` has disappeared — that is the whole trick.
- `sum_norm_sq_dot_measurementKet : ∑ x, ‖〈b x‖Ψ y〉‖² = 1` for **every** `y`. Rewrite
  `〈b x‖Ψ y〉 = ∑ z (ω z 〈E z‖Ψ y〉) · ((√2ⁿ)⁻¹ walsh x z)` and apply Parseval for the
  orthonormal rescaled Walsh vectors (§7.2 D): the sum becomes `∑ z ‖ω z 〈E z‖Ψ y〉‖² =
  ∑ z ‖〈E z‖Ψ y〉‖² = 1`. Physically: every product state lies in the span of the `b x`, so the
  complement outcome never fires on product states.

### 7.4 Turning orthonormal kets into a POVM

File: `QuantumInfo/Measurements/POVM.lean` (new section at the end) and two helpers in
`QuantumInfo/States/Mixed/MState.lean`.

```lean
noncomputable def POVM.ofOrthonormal (b : X → Ket d)
    (hb : ∀ x y, 〈b x‖b y〉 = if x = y then 1 else 0) : POVM (Option X) d
```

- outcome `some x` ↦ `(MState.pure (b x)).M = |b x⟩⟨b x|` (PSD as a density matrix);
- outcome `none` ↦ `1 − ∑ x |b x⟩⟨b x|`;
- normalisation: `Fintype.sum_option` + `sub_add_cancel`.

PSD of the `none` operator (`one_sub_sum_pure_nonneg_of_orthonormal`): `P = ∑ x |b x⟩⟨b x|` is
idempotent because `|b x⟩⟨b x| · |b y⟩⟨b y| = δ_{xy} |b x⟩⟨b x|`
(`MState.pure_mul_pure_of_orthonormal`, via `Matrix.vecMulVec_mul_vecMulVec`), so `1 − P` is a
self-adjoint idempotent, hence PSD (`IsStarProjection.nonneg` from Mathlib).

Born probabilities on a pure state `ψ`:

- `measure_ofOrthonormal_some : (… (some x) : ℝ) = ‖〈b x‖ψ〉‖²` — the HermitianMat inner product
  of two pure states is `‖〈b x‖ψ〉‖²` (`MState.val_inner`, `MState.pure_inner`);
- `measure_ofOrthonormal_none : (… none : ℝ) = 1 − ∑ x ‖〈b x‖ψ〉‖²` — from the probabilities
  summing to one.

### 7.5 `exists_povm`: assembling the measurement

1. `exists_qubitFrame` gives a frame `F` (uses `MState.pure (ψ 0) ≠ MState.pure (ψ 1)`).
2. `exists_two_mul_pow_le F.c_pos F.s_pos` gives `n` with `2 cⁿ ≤ (c + s)ⁿ`.
3. `exists_phases F.c_pos F.s_pos.le F.s_le_c hn` gives unit `ω` with `∑ z ω z A z = 0`.
4. `E := POVM.ofOrthonormal (F.measurementKet ω hω) (dot_measurementKet_measurementKet)`, with
   outcome type `Option (Fin n → Fin 2)`.
5. Outcome `none`: witness `x = 0` (any `x` works); probability
   `1 − ∑ x ‖〈b x‖Ψ 0〉‖² = 1 − 1 = 0`.
6. Outcome `some x`: witness `x` itself; probability `‖〈b x‖Ψ x〉‖² = 0`.
7. `Prob` equality from real equality by `Subtype.ext`.

## 8. General lemmas added to existing files

These are not PBR-specific and were placed where AGENTS.md says they belong.

| Lemma | File | What it says | Used in |
|---|---|---|---|
| `Braket.dot_piProd` | Braket.lean | `〈⊗ψ‖⊗φ〉 = ∏ 〈ψ i‖φ i〉` | frame-ket inner products |
| `Braket.dot_eq_star_dotProduct` | Braket.lean | `〈ψ‖φ〉 = star ψ ⬝ᵥ φ` (corollary of `dot_eq_dotProduct`) | QubitFrame `simp` |
| `Braket.ofReal_sum_norm_sq_eq_star_dotProduct` | Braket.lean | `∑ ‖v x‖² = star v ⬝ᵥ v` in `ℂ` | QubitFrame norms |
| `Braket.exists_ne_zero_of_sum_norm_sq_ne_zero` | Braket.lean | nonzero norm ⇒ nonzero entry (for `Ket.normalize`) | QubitFrame |
| `Braket.dot_normalize_left`, `dot_normalize_normalize` | Braket.lean | bra-kets of `Ket.normalize` vectors | QubitFrame |
| `Braket.sum_norm_sq_sum_mul_of_orthonormal` | Braket.lean | Parseval: `∑ ‖∑ a β a v a‖² = ∑ ‖β a‖²` for orthonormal `v` | measurement kets |
| `MState.pure_mul_pure_of_orthonormal`, `sum_pure_mul_sum_pure_of_orthonormal` | MState.lean | projector algebra of an orthonormal family | `POVM.ofOrthonormal` |
| `POVM.ofOrthonormal`, `one_sub_sum_pure_nonneg_of_orthonormal`, `measure_ofOrthonormal_some/none` | POVM.lean | §7.4 | `exists_povm` |
| `MeasureTheory.Measure.pi_mono` | ForMathlib/MeasureTheory/Pi.lean | product measures are monotone | classical half |

## 9. How this relates to the PBR paper

- **Scope.** The paper first treats `|0⟩, |+⟩` with a 2-copy measurement, then the general case.
  Only the general case is formalised; the `|0⟩, |+⟩` case is the instance `n = 2`,
  `r = 1/√2` (and `exists_two_mul_pow_le` can pick some `n` for it).
- **Choice of `n`.** Paper: `2^{1/n} − 1 ≤ tan(θ/2)`. Here: `2 cⁿ ≤ (c + s)ⁿ` with
  `c = cos(θ/2)`, `s = sin(θ/2)` — the same inequality.
- **The measurement.** As I understand the paper's general construction (a phase rotation on
  each copy, an extra phase on the all-zeros component, then a Hadamard-type transform before a
  computational-basis measurement), its basis vectors have the form `b x` above with
  `ω z = e^{iα|z|}` for `z ≠ 0` and a separate phase on `z = 0` — which is exactly the `ω` built
  in `exists_phases`. The Lean code works with the resulting basis vectors directly rather than
  with the gate sequence. **Please check this correspondence against the paper yourself**; the
  formal result does not depend on it (the measurement is constructed and verified from
  scratch), only the attribution does.
- **Arbitrary dimension.** The paper's states live in any Hilbert space; here `d` is any finite
  type. The `2ⁿ` measurement kets span only part of the `n`-copy space when `d > 2`, which is
  why the POVM has the extra `none` outcome (the paper can treat the complement implicitly).
- **The classical step** is made rigorous via common sub-measures (§5.3).
- **Preparation independence** is stated in its general form (§3.3), not the Cartesian-product
  form; the paper's argument only needs the general form.

## 10. Edge cases and how they are handled

- **Orthogonal states** (`〈ψ‖φ〉 = 0`): `arg 0 = 0`, `ζ = 1`, `r = 0`, `c = s = 1/√2`. All
  hypotheses use `s ≤ c` and `0 ≤ s` (never strict), so this case goes through; `n = 1` already
  satisfies `2c ≤ 2c`. Tested in the scratch tests (`exists_phases` with `c = s`, and
  `exists_qubitFrame` on `![Ket.basis 0, Ket.basis 1]`).
- **Phase-equivalent kets**: excluded by the hypothesis `MState.pure ψ ≠ MState.pure φ`, which is
  turned into `r < 1` (§7.1 step 3). The theorem says nothing about phase-equivalent kets, as it
  should.
- **`n = 0`** in the classical lemma: no `n ≠ 0` assumption is needed; `pow_eq_zero_iff'`
  handles it (at `n = 0` the hypotheses are contradictory anyway). In the actual proof `n ≥ 1`.
- **`d` with one element**: every two kets are phase-equivalent, so the theorem is vacuously
  true there — correct, since there is only one pure state.
- **Measurability of the pulled-back response functions**: needs `ι n` measurable — that is
  why measurability is part of `PreparationIndependent`.

## 11. Review checklist

Statement fidelity (most important):

- [ ] `OntologicalModel` fields match your understanding of a Harrigan–Spekkens model (§3.1),
      including the Born rule coercion `ENNReal.ofReal (E.measure (MState.pure ψ) x)`.
- [ ] `IsPsiOntic` is the notion you want (mutual singularity, distinctness up to phase).
- [ ] `PreparationIndependent` says what PBR assume (§3.3) and you are happy with the
      generalisation away from the Cartesian product.
- [ ] Nothing assumed is stronger than PBR need: the `n`-copy models must be full ontological
      models of `n` copies (Born rule for all POVMs and all `n`-copy kets). If you would rather
      only require the response functions of the single PBR measurement, that would be a further
      (easy) generalisation — the proof only uses `resp`, `measurable_resp`, `sum_resp` for one
      POVM and `lintegral_resp` on product kets.

Proof structure (the kernel checks correctness; these are for understanding):

- [ ] §5 classical half; §6 glue; §7 quantum half; §8 general lemmas.
- [ ] The scratch non-vacuity test (Beltrametti–Bugajski) convinces you the structure is
      consistent. There is **no** Lean example of a model satisfying `PreparationIndependent`
      (open follow-up).

Presentation / AGENTS.md:

- [ ] Module docs of the five new files read well; only the headline is a `theorem` (listed in
      `Theorems.txt`); every definition and structure field has a docstring.
- [ ] References in `docs/references.bib` (`Pusey:2011de`, `Harrigan:2007wfc`) — you must verify
      them yourself (AI-POLICY §2.1). I used pages 475–478 for PBR; InspireHEP lists 476.

## 12. Re-checking it yourself

From the repo root, in PowerShell (Lean is not on PATH by default):

```powershell
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build QuantumInfo.Foundations.PBR.Theorem
```

Then a scratch file

```lean
import QuantumInfo.Foundations.PBR.Theorem
#check @OntologicalModel.PreparationIndependent.isPsiOntic
#print axioms OntologicalModel.PreparationIndependent.isPsiOntic
```

run with `lake env lean <file>` should print the statement and
`[propext, Classical.choice, Quot.sound]`. The scratch tests used during development
(`Task1.lean`–`Task8.lean`, `R1.lean`, including the Beltrametti–Bugajski model) are in this
session's scratchpad under `pbr-tests\`; the full build and lint results are in
`docs/superpowers/pbr-summary.md`.
