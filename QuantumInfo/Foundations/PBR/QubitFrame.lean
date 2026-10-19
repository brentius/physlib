/-
Copyright (c) 2026 brent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: brent
-/
module

public import QuantumInfo.Foundations.PBR.Phases
public import QuantumInfo.States.Mixed.MState

/-!
# The qubit frame of two pure states

An orthonormal frame of the span of two non-phase-equivalent pure states.

## i. Overview

Let `ψ 0` and `ψ 1` be pure states which are not equal up to a global phase. Write
`γ = 〈ψ 0‖ψ 1〉`, `r = ‖γ‖ < 1` and `ζ = exp (-i arg γ)`, so that `ζ γ = r`. The kets
`e 0 ∝ ψ 0 + ζ ψ 1` and `e 1 ∝ ψ 0 - ζ ψ 1` are orthonormal, and with `c = √((1 + r) / 2)`,
`s = √((1 - r) / 2)` one has `〈e j‖ψ b〉 = phase b * (-1) ^ (j b) * ![c, s] j` where
`phase = ![1, conj ζ]`. This is the qubit frame used to build the measurement in the
Pusey–Barrett–Rudolph (PBR) theorem.

## ii. Key results

- `PBR.QubitFrame` : the qubit frame of a pair of pure states.
- `PBR.QubitFrame.sum_norm_sq_dot_e_state` : each state lies in the span of the frame.
- `PBR.exists_qubitFrame` : two non-phase-equivalent pure states have a qubit frame.

## iii. Table of contents

- A. The vectors `ψ ± ζ φ`
  - A.1. Dot products
  - A.2. Norms
  - A.3. Bra-kets with the normalized vectors
- B. The qubit frame
- C. Existence of the qubit frame
  - C.1. Construction from an aligning phase
  - C.2. The aligning phase

## iv. References

- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]

-/

@[expose] public section

noncomputable section

open Braket

namespace PBR

variable {d : Type*} [Fintype d]

section Vectors

/-!
## A. The vectors `ψ ± ζ φ`

Throughout, `ζ` is a unit complex number aligning `〈ψ‖φ〉` with the real axis: `ζ 〈ψ‖φ〉 = r`.

### A.1. Dot products

-/

variable (ψ φ : Ket d) {ζ : ℂ} {r : ℝ}

/-- A unit complex number `ζ` satisfies `star ζ * ζ = 1`. -/
private lemma star_mul_self_of_norm_eq_one (hζ : ‖ζ‖ = 1) : star ζ * ζ = 1 := by
  rw [← starRingEnd_apply, Complex.conj_mul', hζ]; simp

/-- The conjugate of the alignment `ζ 〈ψ‖φ〉 = r`. -/
lemma star_mul_star_dot (hr : ζ * 〈ψ‖φ〉 = r) : star ζ * star 〈ψ‖φ〉 = r := by
  have h := congrArg (starRingEnd ℂ) hr
  rw [map_mul, Complex.conj_ofReal] at h
  simpa using h

/-- `(ψ + ζ φ)† (ψ + ζ φ) = 2 + 2 r`. -/
lemma star_add_dotProduct_add (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r) :
    star (ψ.vec + ζ • φ.vec) ⬝ᵥ (ψ.vec + ζ • φ.vec) = 2 + 2 * r := by
  have h1 := star_mul_self_of_norm_eq_one hζ
  have h2 := star_mul_star_dot ψ φ hr
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, ← dot_eq_star_dotProduct, dot_self_eq_one,
    dot_swap_conj ψ φ, starRingEnd_apply]
  linear_combination hr + h2 + h1

/-- `(ψ - ζ φ)† (ψ - ζ φ) = 2 - 2 r`. -/
lemma star_sub_dotProduct_sub (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r) :
    star (ψ.vec - ζ • φ.vec) ⬝ᵥ (ψ.vec - ζ • φ.vec) = 2 - 2 * r := by
  have h1 := star_mul_self_of_norm_eq_one hζ
  have h2 := star_mul_star_dot ψ φ hr
  simp only [star_sub, star_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, ← dot_eq_star_dotProduct, dot_self_eq_one,
    dot_swap_conj ψ φ, starRingEnd_apply]
  linear_combination -hr - h2 + h1

/-- `(ψ + ζ φ)† (ψ - ζ φ) = 0`. -/
lemma star_add_dotProduct_sub (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r) :
    star (ψ.vec + ζ • φ.vec) ⬝ᵥ (ψ.vec - ζ • φ.vec) = 0 := by
  have h1 := star_mul_self_of_norm_eq_one hζ
  have h2 := star_mul_star_dot ψ φ hr
  simp only [star_add, star_smul, add_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, ← dot_eq_star_dotProduct, dot_self_eq_one,
    dot_swap_conj ψ φ, starRingEnd_apply]
  linear_combination -hr + h2 - h1

/-- `(ψ - ζ φ)† (ψ + ζ φ) = 0`. -/
lemma star_sub_dotProduct_add (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r) :
    star (ψ.vec - ζ • φ.vec) ⬝ᵥ (ψ.vec + ζ • φ.vec) = 0 := by
  have h1 := star_mul_self_of_norm_eq_one hζ
  have h2 := star_mul_star_dot ψ φ hr
  simp only [star_sub, star_smul, sub_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, ← dot_eq_star_dotProduct, dot_self_eq_one,
    dot_swap_conj ψ φ, starRingEnd_apply]
  linear_combination hr - h2 - h1

/-- `(ψ + ζ φ)† ψ = 1 + r`. -/
lemma star_add_dotProduct_left (hr : ζ * 〈ψ‖φ〉 = r) :
    star (ψ.vec + ζ • φ.vec) ⬝ᵥ ψ.vec = 1 + r := by
  have h2 := star_mul_star_dot ψ φ hr
  simp only [star_add, star_smul, add_dotProduct, smul_dotProduct, smul_eq_mul,
    ← dot_eq_star_dotProduct, dot_self_eq_one, dot_swap_conj ψ φ, starRingEnd_apply]
  linear_combination h2

/-- `(ψ + ζ φ)† φ = conj ζ (1 + r)`. -/
lemma star_add_dotProduct_right (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r) :
    star (ψ.vec + ζ • φ.vec) ⬝ᵥ φ.vec = star ζ * (1 + r) := by
  have h1 := star_mul_self_of_norm_eq_one hζ
  simp only [star_add, star_smul, add_dotProduct, smul_dotProduct, smul_eq_mul,
    ← dot_eq_star_dotProduct, dot_self_eq_one]
  linear_combination (-〈ψ‖φ〉) * h1 + star ζ * hr

/-- `(ψ - ζ φ)† ψ = 1 - r`. -/
lemma star_sub_dotProduct_left (hr : ζ * 〈ψ‖φ〉 = r) :
    star (ψ.vec - ζ • φ.vec) ⬝ᵥ ψ.vec = 1 - r := by
  have h2 := star_mul_star_dot ψ φ hr
  simp only [star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul,
    ← dot_eq_star_dotProduct, dot_self_eq_one, dot_swap_conj ψ φ, starRingEnd_apply]
  linear_combination -h2

/-- `(ψ - ζ φ)† φ = -conj ζ (1 - r)`. -/
lemma star_sub_dotProduct_right (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r) :
    star (ψ.vec - ζ • φ.vec) ⬝ᵥ φ.vec = -(star ζ * (1 - r)) := by
  have h1 := star_mul_self_of_norm_eq_one hζ
  simp only [star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul,
    ← dot_eq_star_dotProduct, dot_self_eq_one]
  linear_combination (-〈ψ‖φ〉) * h1 + star ζ * hr

/-!
### A.2. Norms

-/

/-- The squared norm of `ψ + ζ φ` is `2 + 2 r`. -/
lemma sum_norm_sq_add (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r) :
    ∑ x, ‖(ψ.vec + ζ • φ.vec) x‖ ^ 2 = 2 + 2 * r := by
  have h := (ofReal_sum_norm_sq_eq_star_dotProduct _).trans
    (star_add_dotProduct_add ψ φ hζ hr)
  exact_mod_cast h

/-- The squared norm of `ψ - ζ φ` is `2 - 2 r`. -/
lemma sum_norm_sq_sub (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r) :
    ∑ x, ‖(ψ.vec - ζ • φ.vec) x‖ ^ 2 = 2 - 2 * r := by
  have h := (ofReal_sum_norm_sq_eq_star_dotProduct _).trans
    (star_sub_dotProduct_sub ψ φ hζ hr)
  exact_mod_cast h

/-!
### A.3. Bra-kets with the normalized vectors

-/

/-- For `0 ≤ a`, `a / √(2 a) = √(a / 2)`. -/
private lemma div_sqrt_two_mul {a : ℝ} (ha : 0 ≤ a) : a / √(2 * a) = √(a / 2) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  have h2 : 0 < √(2 * a) := Real.sqrt_pos.mpr (by linarith)
  rw [div_eq_iff h2.ne', ← Real.sqrt_mul (by linarith),
    show a / 2 * (2 * a) = a ^ 2 by ring, Real.sqrt_sq ha.le]

/-- If the squared norm of a vector is `2 a`, then `0 ≤ a`. -/
private lemma nonneg_of_sum_norm_sq_eq_two_mul {v : d → ℂ} {a : ℝ}
    (h : ∑ x, ‖v x‖ ^ 2 = 2 * a) : 0 ≤ a := by
  have := Finset.sum_nonneg fun x (_ : x ∈ Finset.univ) => sq_nonneg ‖v x‖
  linarith

/-- `〈e 0‖ψ〉 = c` for `e 0 ∝ ψ + ζ φ` and `c = √((1 + r) / 2)`. -/
lemma dot_normalize_add_left (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r)
    (h : ∃ x, (ψ.vec + ζ • φ.vec) x ≠ 0) :
    〈Ket.normalize (ψ.vec + ζ • φ.vec) h‖ψ〉 = √((1 + r) / 2) := by
  have hs : ∑ x, ‖(ψ.vec + ζ • φ.vec) x‖ ^ 2 = 2 * (1 + r) := by
    rw [sum_norm_sq_add ψ φ hζ hr]; ring
  rw [dot_normalize_left, star_add_dotProduct_left ψ φ hr, hs,
    ← div_sqrt_two_mul (nonneg_of_sum_norm_sq_eq_two_mul hs)]
  push_cast
  ring

/-- `〈e 0‖φ〉 = conj ζ * c` for `e 0 ∝ ψ + ζ φ` and `c = √((1 + r) / 2)`. -/
lemma dot_normalize_add_right (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r)
    (h : ∃ x, (ψ.vec + ζ • φ.vec) x ≠ 0) :
    〈Ket.normalize (ψ.vec + ζ • φ.vec) h‖φ〉 = star ζ * √((1 + r) / 2) := by
  have hs : ∑ x, ‖(ψ.vec + ζ • φ.vec) x‖ ^ 2 = 2 * (1 + r) := by
    rw [sum_norm_sq_add ψ φ hζ hr]; ring
  rw [dot_normalize_left, star_add_dotProduct_right ψ φ hζ hr, hs,
    ← div_sqrt_two_mul (nonneg_of_sum_norm_sq_eq_two_mul hs)]
  push_cast
  ring

/-- `〈e 1‖ψ〉 = s` for `e 1 ∝ ψ - ζ φ` and `s = √((1 - r) / 2)`. -/
lemma dot_normalize_sub_left (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r)
    (h : ∃ x, (ψ.vec - ζ • φ.vec) x ≠ 0) :
    〈Ket.normalize (ψ.vec - ζ • φ.vec) h‖ψ〉 = √((1 - r) / 2) := by
  have hs : ∑ x, ‖(ψ.vec - ζ • φ.vec) x‖ ^ 2 = 2 * (1 - r) := by
    rw [sum_norm_sq_sub ψ φ hζ hr]; ring
  rw [dot_normalize_left, star_sub_dotProduct_left ψ φ hr, hs,
    ← div_sqrt_two_mul (nonneg_of_sum_norm_sq_eq_two_mul hs)]
  push_cast
  ring

/-- `〈e 1‖φ〉 = -conj ζ * s` for `e 1 ∝ ψ - ζ φ` and `s = √((1 - r) / 2)`. -/
lemma dot_normalize_sub_right (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r)
    (h : ∃ x, (ψ.vec - ζ • φ.vec) x ≠ 0) :
    〈Ket.normalize (ψ.vec - ζ • φ.vec) h‖φ〉 = -(star ζ * √((1 - r) / 2)) := by
  have hs : ∑ x, ‖(ψ.vec - ζ • φ.vec) x‖ ^ 2 = 2 * (1 - r) := by
    rw [sum_norm_sq_sub ψ φ hζ hr]; ring
  rw [dot_normalize_left, star_sub_dotProduct_right ψ φ hζ hr, hs,
    ← div_sqrt_two_mul (nonneg_of_sum_norm_sq_eq_two_mul hs)]
  push_cast
  ring

/-- The kets `e 0 ∝ ψ + ζ φ` and `e 1 ∝ ψ - ζ φ` are orthogonal. -/
lemma dot_normalize_add_sub (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r)
    (h : ∃ x, (ψ.vec + ζ • φ.vec) x ≠ 0) (h' : ∃ x, (ψ.vec - ζ • φ.vec) x ≠ 0) :
    〈Ket.normalize (ψ.vec + ζ • φ.vec) h‖Ket.normalize (ψ.vec - ζ • φ.vec) h'〉 = 0 := by
  rw [dot_normalize_normalize, star_add_dotProduct_sub ψ φ hζ hr, zero_div, zero_div]

/-- The kets `e 1 ∝ ψ - ζ φ` and `e 0 ∝ ψ + ζ φ` are orthogonal. -/
lemma dot_normalize_sub_add (hζ : ‖ζ‖ = 1) (hr : ζ * 〈ψ‖φ〉 = r)
    (h : ∃ x, (ψ.vec - ζ • φ.vec) x ≠ 0) (h' : ∃ x, (ψ.vec + ζ • φ.vec) x ≠ 0) :
    〈Ket.normalize (ψ.vec - ζ • φ.vec) h‖Ket.normalize (ψ.vec + ζ • φ.vec) h'〉 = 0 := by
  rw [dot_normalize_normalize, star_sub_dotProduct_add ψ φ hζ hr, zero_div, zero_div]

end Vectors

/-!
## B. The qubit frame

-/

/-- A qubit frame of two pure states `ψ 0`, `ψ 1`: orthonormal kets `e 0`, `e 1` and reals
`c ≥ s > 0` with `c ^ 2 + s ^ 2 = 1` such that `〈e j‖ψ b〉 = phase b * (-1) ^ (j b) * ![c, s] j`
for unit phases `phase b`. -/
structure QubitFrame (ψ : Fin 2 → Ket d) where
  /-- The orthonormal frame kets. -/
  e : Fin 2 → Ket d
  /-- The amplitude of `e 0` in the states; for the frame built by `exists_qubitFrame` it is
  `√((1 + ‖〈ψ 0‖ψ 1〉‖) / 2)`. -/
  c : ℝ
  /-- The amplitude of `e 1` in the states; for the frame built by `exists_qubitFrame` it is
  `√((1 - ‖〈ψ 0‖ψ 1〉‖) / 2)`. -/
  s : ℝ
  /-- The global phases of the two states in the frame. -/
  phase : Fin 2 → ℂ
  /-- The smaller amplitude is positive. -/
  s_pos : 0 < s
  /-- The amplitude `s` is at most `c`. -/
  s_le_c : s ≤ c
  /-- The amplitudes are normalized. -/
  sq_add_sq : c ^ 2 + s ^ 2 = 1
  /-- The phases have unit norm. -/
  norm_phase (b : Fin 2) : ‖phase b‖ = 1
  /-- The frame kets are orthonormal. -/
  dot_e_e (j k : Fin 2) : 〈e j‖e k〉 = if j = k then 1 else 0
  /-- The components of the states in the frame. -/
  dot_e_state (j b : Fin 2) : 〈e j‖ψ b〉 = phase b * sign j b * ![(c : ℂ), (s : ℂ)] j

namespace QubitFrame

variable {ψ : Fin 2 → Ket d}

/-- The larger amplitude is positive. -/
lemma c_pos (F : QubitFrame ψ) : 0 < F.c := F.s_pos.trans_le F.s_le_c

/-- Each state `ψ b` lies in the span of the frame. -/
lemma sum_norm_sq_dot_e_state (F : QubitFrame ψ) (b : Fin 2) :
    ∑ j, ‖〈F.e j‖ψ b〉‖ ^ 2 = 1 := by
  simp only [Fin.sum_univ_two, F.dot_e_state, norm_mul, F.norm_phase, norm_sign, one_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  exact F.sq_add_sq

end QubitFrame

/-!
## C. Existence of the qubit frame

### C.1. Construction from an aligning phase

-/

/-- The qubit frame of `ψ 0`, `ψ 1` built from a unit `ζ` with `ζ 〈ψ 0‖ψ 1〉 = r < 1`:
`e 0 ∝ ψ 0 + ζ ψ 1`, `e 1 ∝ ψ 0 - ζ ψ 1`, `c = √((1 + r) / 2)`, `s = √((1 - r) / 2)` and
`phase = ![1, conj ζ]`. -/
def QubitFrame.ofPhase (ψ : Fin 2 → Ket d) {ζ : ℂ} {r : ℝ} (hζ : ‖ζ‖ = 1)
    (hr : ζ * 〈ψ 0‖ψ 1〉 = r) (hr0 : 0 ≤ r) (hr1 : r < 1) : QubitFrame ψ where
  e := ![Ket.normalize ((ψ 0).vec + ζ • (ψ 1).vec) (exists_ne_zero_of_sum_norm_sq_ne_zero
      (by rw [sum_norm_sq_add _ _ hζ hr]; linarith)),
    Ket.normalize ((ψ 0).vec - ζ • (ψ 1).vec) (exists_ne_zero_of_sum_norm_sq_ne_zero
      (by rw [sum_norm_sq_sub _ _ hζ hr]; linarith))]
  c := √((1 + r) / 2)
  s := √((1 - r) / 2)
  phase := ![1, star ζ]
  s_pos := Real.sqrt_pos.mpr (by linarith)
  s_le_c := Real.sqrt_le_sqrt (by linarith)
  sq_add_sq := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    ring
  norm_phase b := by fin_cases b <;> simp [hζ]
  dot_e_e j k := by
    fin_cases j <;> fin_cases k
    · simp
    · simp [dot_normalize_add_sub _ _ hζ hr]
    · simp [dot_normalize_sub_add _ _ hζ hr]
    · simp
  dot_e_state j b := by
    fin_cases j <;> fin_cases b
    · simp [sign, dot_normalize_add_left _ _ hζ hr]
    · simp [sign, dot_normalize_add_right _ _ hζ hr]
    · simp [sign, dot_normalize_sub_left _ _ hζ hr]
    · simp [sign, dot_normalize_sub_right _ _ hζ hr]

/-!
### C.2. The aligning phase

-/

/-- The unit `exp (-i arg γ)` rotates `γ` onto the nonnegative real axis. -/
lemma exp_neg_arg_mul_self (γ : ℂ) :
    Complex.exp (↑(-γ.arg) * Complex.I) * γ = ‖γ‖ := by
  calc Complex.exp (↑(-γ.arg) * Complex.I) * γ =
      Complex.exp (↑(-γ.arg) * Complex.I) * (‖γ‖ * Complex.exp (γ.arg * Complex.I)) := by
        rw [Complex.norm_mul_exp_arg_mul_I]
    _ = ‖γ‖ := by
        rw [mul_left_comm, ← Complex.exp_add]
        simp

/-- If `ψ` and `φ` are not equal up to a global phase and `ζ 〈ψ‖φ〉 = r` for a unit `ζ`,
then `r < 1`. -/
lemma lt_one_of_pure_ne [DecidableEq d] (ψ φ : Ket d) {ζ : ℂ} {r : ℝ} (hζ : ‖ζ‖ = 1)
    (hr : ζ * 〈ψ‖φ〉 = r) (h : MState.pure ψ ≠ MState.pure φ) : r < 1 := by
  by_contra! hle
  have hs := sum_norm_sq_sub ψ φ hζ hr
  have h0 : ∑ x, ‖(ψ.vec - ζ • φ.vec) x‖ ^ 2 = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg fun x _ => sq_nonneg _)
  rw [Fintype.sum_eq_zero_iff_of_nonneg fun x => sq_nonneg _] at h0
  refine h ((MState.pure_eq_pure_iff ψ φ).mpr ⟨ζ, hζ, funext fun x => ?_⟩)
  have hx := congrFun h0 x
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    norm_eq_zero, Pi.sub_apply, sub_eq_zero] at hx
  exact hx

/-- Two pure states which are not equal up to a global phase have a qubit frame. -/
lemma exists_qubitFrame [DecidableEq d] (ψ : Fin 2 → Ket d)
    (h : MState.pure (ψ 0) ≠ MState.pure (ψ 1)) : Nonempty (QubitFrame ψ) :=
  ⟨QubitFrame.ofPhase ψ (Complex.norm_exp_ofReal_mul_I _)
    (exp_neg_arg_mul_self 〈ψ 0‖ψ 1〉) (norm_nonneg _)
    (lt_one_of_pure_ne (ψ 0) (ψ 1) (Complex.norm_exp_ofReal_mul_I _)
      (exp_neg_arg_mul_self 〈ψ 0‖ψ 1〉) h)⟩

end PBR
