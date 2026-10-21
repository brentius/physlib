/-
Copyright (c) 2026 brent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: brent
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
public import PhyslibAlpha.QuantumMechanics.Foundations.PBR.Phases

/-!
# The qubit frame of two unit vectors

An orthonormal frame of the span of two unit vectors which are not equal up to a global phase.

## i. Overview

Let `ψ 0` and `ψ 1` be unit vectors of `𝓗[d]` with `‖⟪ψ 0, ψ 1⟫_ℂ‖ < 1`, that is, which are
not equal up to a global phase. Write `γ = ⟪ψ 0, ψ 1⟫_ℂ`, `r = ‖γ‖ < 1` and
`ζ = exp (-i arg γ)`, so that `ζ γ = r`. The vectors `e 0 ∝ ψ 0 + ζ ψ 1` and
`e 1 ∝ ψ 0 - ζ ψ 1` are orthonormal, and with `c = √((1 + r) / 2)` and `s = √((1 - r) / 2)`
one has `⟪e j, ψ b⟫_ℂ = phase b * (-1) ^ (j * b) * ![c, s] j` where `phase = ![1, conj ζ]`.
This is the qubit frame used to build the measurement in the Pusey–Barrett–Rudolph (PBR)
theorem.

## ii. Key results

- `PBR.QubitFrame` : the qubit frame of a pair of unit vectors.
- `PBR.QubitFrame.sum_norm_sq_inner_e_state` : Parseval's identity for each `ψ b` in the frame.
- `PBR.exists_qubitFrame` : two unit vectors which are not equal up to a global phase have a
  qubit frame.

## iii. Table of contents

- A. The vectors `ψ ± ζ φ`
  - A.1. Inner products
  - A.2. Inner products with the normalized vectors
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

namespace QuantumMechanics.PBR

open InnerProductSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

section Vectors

/-!
## A. The vectors `ψ ± ζ φ`

Throughout, `ψ` and `φ` are unit vectors and `ζ` is a unit complex number aligning
`⟪ψ, φ⟫_ℂ` with the real axis: `ζ * ⟪ψ, φ⟫_ℂ = r`.

### A.1. Inner products

-/

variable {ψ φ : 𝓗[d]} {ζ : ℂ} {r : ℝ}

/-- A unit complex number `ζ` satisfies `conj ζ * ζ = 1`. -/
private lemma conj_mul_self_of_norm_eq_one (hζ : ‖ζ‖ = 1) : starRingEnd ℂ ζ * ζ = 1 := by
  rw [Complex.conj_mul', hζ]
  simp

/-- The conjugate of the alignment `ζ * ⟪ψ, φ⟫_ℂ = r`. -/
lemma conj_mul_inner_swap (hr : ζ * ⟪ψ, φ⟫_ℂ = r) : starRingEnd ℂ ζ * ⟪φ, ψ⟫_ℂ = r := by
  rw [← inner_conj_symm, ← map_mul, hr, Complex.conj_ofReal]

/-- `⟪ψ + ζ φ, ψ⟫_ℂ = 1 + r`. -/
lemma inner_add_smul_fst (hψ : ‖ψ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ⟪ψ + ζ • φ, ψ⟫_ℂ = 1 + r := by
  rw [inner_add_left, inner_smul_left, inner_self_eq_one_of_norm_eq_one hψ,
    conj_mul_inner_swap hr]

/-- `⟪ψ + ζ φ, φ⟫_ℂ = conj ζ * (1 + r)`. -/
lemma inner_add_smul_snd (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ⟪ψ + ζ • φ, φ⟫_ℂ = starRingEnd ℂ ζ * (1 + r) := by
  rw [inner_add_left, inner_smul_left, inner_self_eq_one_of_norm_eq_one hφ, ← hr]
  linear_combination (-⟪ψ, φ⟫_ℂ) * conj_mul_self_of_norm_eq_one hζ

/-- `⟪ψ - ζ φ, ψ⟫_ℂ = 1 - r`. -/
lemma inner_sub_smul_fst (hψ : ‖ψ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ⟪ψ - ζ • φ, ψ⟫_ℂ = 1 - r := by
  rw [inner_sub_left, inner_smul_left, inner_self_eq_one_of_norm_eq_one hψ,
    conj_mul_inner_swap hr]

/-- `⟪ψ - ζ φ, φ⟫_ℂ = -(conj ζ * (1 - r))`. -/
lemma inner_sub_smul_snd (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) :
    ⟪ψ - ζ • φ, φ⟫_ℂ = -(starRingEnd ℂ ζ * (1 - r)) := by
  rw [inner_sub_left, inner_smul_left, inner_self_eq_one_of_norm_eq_one hφ, ← hr]
  linear_combination (-⟪ψ, φ⟫_ℂ) * conj_mul_self_of_norm_eq_one hζ

/-- The vectors `ψ + ζ φ` and `ψ - ζ φ` are orthogonal. -/
lemma inner_add_smul_sub_smul (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) : ⟪ψ + ζ • φ, ψ - ζ • φ⟫_ℂ = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_add_smul_fst hψ hr, inner_add_smul_snd hφ hζ hr]
  linear_combination (-(1 + (r : ℂ))) * conj_mul_self_of_norm_eq_one hζ

/-- The vectors `ψ - ζ φ` and `ψ + ζ φ` are orthogonal. -/
lemma inner_sub_smul_add_smul (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) : ⟪ψ - ζ • φ, ψ + ζ • φ⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_add_smul_sub_smul hψ hφ hζ hr, map_zero]

/-- The squared norm of `ψ + ζ φ` is `2 * (1 + r)`. -/
lemma norm_add_smul_sq (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) : ‖ψ + ζ • φ‖ ^ 2 = 2 * (1 + r) := by
  have h : ⟪ψ + ζ • φ, ψ + ζ • φ⟫_ℂ = 2 * (1 + r) := by
    rw [inner_add_right, inner_smul_right, inner_add_smul_fst hψ hr,
      inner_add_smul_snd hφ hζ hr]
    linear_combination (1 + (r : ℂ)) * conj_mul_self_of_norm_eq_one hζ
  rw [inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by push_cast; exact h)

/-- The squared norm of `ψ - ζ φ` is `2 * (1 - r)`. -/
lemma norm_sub_smul_sq (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) : ‖ψ - ζ • φ‖ ^ 2 = 2 * (1 - r) := by
  have h : ⟪ψ - ζ • φ, ψ - ζ • φ⟫_ℂ = 2 * (1 - r) := by
    rw [inner_sub_right, inner_smul_right, inner_sub_smul_fst hψ hr,
      inner_sub_smul_snd hφ hζ hr]
    linear_combination (1 - (r : ℂ)) * conj_mul_self_of_norm_eq_one hζ
  rw [inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by push_cast; exact h)

/-!
### A.2. Inner products with the normalized vectors

-/

/-- For `0 ≤ a`, `(√(2 * a))⁻¹ * a = √(a / 2)`. -/
private lemma inv_sqrt_two_mul_mul {a : ℝ} (ha : 0 ≤ a) : (√(2 * a))⁻¹ * a = √(a / 2) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  have h2 : 0 < √(2 * a) := Real.sqrt_pos.mpr (by linarith)
  rw [inv_mul_eq_div, div_eq_iff h2.ne', ← Real.sqrt_mul (by linarith),
    show a / 2 * (2 * a) = a ^ 2 by ring, Real.sqrt_sq ha.le]

/-- Rescaling a vector `u` with `‖u‖ ^ 2 = t > 0` by `(√t)⁻¹` gives a unit vector. -/
private lemma norm_inv_sqrt_smul {u : 𝓗[d]} {t : ℝ} (hu : ‖u‖ ^ 2 = t) (ht : 0 < t) :
    ‖(((√t)⁻¹ : ℝ) : ℂ) • u‖ = 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← hu,
    Real.sqrt_sq (norm_nonneg u), inv_mul_cancel₀]
  rintro h
  rw [h] at hu
  linarith

/-- The inner product of real rescalings of two vectors. -/
private lemma inner_ofReal_smul_ofReal_smul (a b : ℝ) (u v : 𝓗[d]) :
    ⟪(a : ℂ) • u, (b : ℂ) • v⟫_ℂ = a * b * ⟪u, v⟫_ℂ := by
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, mul_assoc]

/-- `⟪e 0, ψ⟫_ℂ = c` for `e 0 ∝ ψ + ζ φ` and `c = √((1 + r) / 2)`. -/
lemma inner_inv_sqrt_smul_add_smul_fst (hψ : ‖ψ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) (hr0 : 0 ≤ r) :
    ⟪(((√(2 * (1 + r)))⁻¹ : ℝ) : ℂ) • (ψ + ζ • φ), ψ⟫_ℂ = √((1 + r) / 2) := by
  rw [inner_smul_left, Complex.conj_ofReal, inner_add_smul_fst hψ hr,
    ← inv_sqrt_two_mul_mul (by linarith)]
  push_cast
  ring

/-- `⟪e 0, φ⟫_ℂ = conj ζ * c` for `e 0 ∝ ψ + ζ φ` and `c = √((1 + r) / 2)`. -/
lemma inner_inv_sqrt_smul_add_smul_snd (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) (hr0 : 0 ≤ r) :
    ⟪(((√(2 * (1 + r)))⁻¹ : ℝ) : ℂ) • (ψ + ζ • φ), φ⟫_ℂ =
      starRingEnd ℂ ζ * √((1 + r) / 2) := by
  rw [inner_smul_left, Complex.conj_ofReal, inner_add_smul_snd hφ hζ hr,
    ← inv_sqrt_two_mul_mul (by linarith)]
  push_cast
  ring

/-- `⟪e 1, ψ⟫_ℂ = s` for `e 1 ∝ ψ - ζ φ` and `s = √((1 - r) / 2)`. -/
lemma inner_inv_sqrt_smul_sub_smul_fst (hψ : ‖ψ‖ = 1) (hr : ζ * ⟪ψ, φ⟫_ℂ = r) (hr1 : r ≤ 1) :
    ⟪(((√(2 * (1 - r)))⁻¹ : ℝ) : ℂ) • (ψ - ζ • φ), ψ⟫_ℂ = √((1 - r) / 2) := by
  rw [inner_smul_left, Complex.conj_ofReal, inner_sub_smul_fst hψ hr,
    ← inv_sqrt_two_mul_mul (by linarith)]
  push_cast
  ring

/-- `⟪e 1, φ⟫_ℂ = -(conj ζ * s)` for `e 1 ∝ ψ - ζ φ` and `s = √((1 - r) / 2)`. -/
lemma inner_inv_sqrt_smul_sub_smul_snd (hφ : ‖φ‖ = 1) (hζ : ‖ζ‖ = 1)
    (hr : ζ * ⟪ψ, φ⟫_ℂ = r) (hr1 : r ≤ 1) :
    ⟪(((√(2 * (1 - r)))⁻¹ : ℝ) : ℂ) • (ψ - ζ • φ), φ⟫_ℂ =
      -(starRingEnd ℂ ζ * √((1 - r) / 2)) := by
  rw [inner_smul_left, Complex.conj_ofReal, inner_sub_smul_snd hφ hζ hr,
    ← inv_sqrt_two_mul_mul (by linarith)]
  push_cast
  ring

end Vectors

/-!
## B. The qubit frame

-/

/-- A qubit frame of two unit vectors `ψ 0`, `ψ 1`: orthonormal vectors `e 0`, `e 1` and reals
`c ≥ s > 0` with `c ^ 2 + s ^ 2 = 1` such that
`⟪e j, ψ b⟫_ℂ = phase b * (-1) ^ (j * b) * ![c, s] j` for unit phases `phase b`. -/
structure QubitFrame (ψ : Fin 2 → 𝓗[d]) where
  /-- The orthonormal frame vectors. -/
  e : Fin 2 → 𝓗[d]
  /-- The amplitude of `e 0` in the vectors; for the frame built by `exists_qubitFrame` it is
  `√((1 + ‖⟪ψ 0, ψ 1⟫_ℂ‖) / 2)`. -/
  c : ℝ
  /-- The amplitude of `e 1` in the vectors; for the frame built by `exists_qubitFrame` it is
  `√((1 - ‖⟪ψ 0, ψ 1⟫_ℂ‖) / 2)`. -/
  s : ℝ
  /-- The global phases of the two vectors in the frame. -/
  phase : Fin 2 → ℂ
  /-- The smaller amplitude is positive. -/
  s_pos : 0 < s
  /-- The amplitude `s` is at most `c`. -/
  s_le_c : s ≤ c
  /-- The amplitudes are normalized. -/
  sq_add_sq : c ^ 2 + s ^ 2 = 1
  /-- The phases have unit norm. -/
  norm_phase (b : Fin 2) : ‖phase b‖ = 1
  /-- The frame vectors are orthonormal. -/
  orthonormal_e : Orthonormal ℂ e
  /-- The components of the vectors in the frame. -/
  inner_e_state (j b : Fin 2) : ⟪e j, ψ b⟫_ℂ = phase b * sign j b * ![(c : ℂ), (s : ℂ)] j

namespace QubitFrame

variable {ψ : Fin 2 → 𝓗[d]}

/-- The larger amplitude is positive. -/
lemma c_pos (F : QubitFrame ψ) : 0 < F.c := F.s_pos.trans_le F.s_le_c

/-- Parseval's identity: the components of the unit vector `ψ b` in the frame have total squared
norm one, so `ψ b` lies in the span of the frame. -/
lemma sum_norm_sq_inner_e_state (F : QubitFrame ψ) (b : Fin 2) :
    ∑ j, ‖⟪F.e j, ψ b⟫_ℂ‖ ^ 2 = 1 := by
  simp only [Fin.sum_univ_two, F.inner_e_state, norm_mul, F.norm_phase, norm_sign, one_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact F.sq_add_sq

end QubitFrame

/-!
## C. Existence of the qubit frame

### C.1. Construction from an aligning phase

-/

/-- The qubit frame of unit vectors `ψ 0`, `ψ 1` built from a unit `ζ` with
`ζ * ⟪ψ 0, ψ 1⟫_ℂ = r < 1`: `e 0 ∝ ψ 0 + ζ ψ 1`, `e 1 ∝ ψ 0 - ζ ψ 1`, `c = √((1 + r) / 2)`,
`s = √((1 - r) / 2)` and `phase = ![1, conj ζ]`. -/
def QubitFrame.ofPhase (ψ : Fin 2 → 𝓗[d]) (hψ : ∀ b, ‖ψ b‖ = 1) {ζ : ℂ} {r : ℝ}
    (hζ : ‖ζ‖ = 1) (hr : ζ * ⟪ψ 0, ψ 1⟫_ℂ = r) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    QubitFrame ψ where
  e := ![(((√(2 * (1 + r)))⁻¹ : ℝ) : ℂ) • (ψ 0 + ζ • ψ 1),
    (((√(2 * (1 - r)))⁻¹ : ℝ) : ℂ) • (ψ 0 - ζ • ψ 1)]
  c := √((1 + r) / 2)
  s := √((1 - r) / 2)
  phase := ![1, star ζ]
  s_pos := Real.sqrt_pos.mpr (by linarith)
  s_le_c := Real.sqrt_le_sqrt (by linarith)
  sq_add_sq := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    ring
  norm_phase b := by fin_cases b <;> simp [hζ]
  orthonormal_e := by
    refine ⟨fun j => ?_, fun j k hjk => ?_⟩
    · fin_cases j
      · exact norm_inv_sqrt_smul (norm_add_smul_sq (hψ 0) (hψ 1) hζ hr) (by linarith)
      · exact norm_inv_sqrt_smul (norm_sub_smul_sq (hψ 0) (hψ 1) hζ hr) (by linarith)
    · fin_cases j <;> fin_cases k <;>
        simp only [ne_eq, not_true_eq_false, Fin.zero_eta, Fin.mk_one, Fin.isValue,
          Matrix.cons_val_zero, Matrix.cons_val_one] at hjk ⊢ <;>
        rw [inner_ofReal_smul_ofReal_smul]
      · rw [inner_add_smul_sub_smul (hψ 0) (hψ 1) hζ hr, mul_zero]
      · rw [inner_sub_smul_add_smul (hψ 0) (hψ 1) hζ hr, mul_zero]
  inner_e_state j b := by
    fin_cases j <;> fin_cases b <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one]
    · rw [inner_inv_sqrt_smul_add_smul_fst (hψ 0) hr hr0]
      simp [sign]
    · rw [inner_inv_sqrt_smul_add_smul_snd (hψ 1) hζ hr hr0]
      simp [sign]
    · rw [inner_inv_sqrt_smul_sub_smul_fst (hψ 0) hr hr1.le]
      simp [sign]
    · rw [inner_inv_sqrt_smul_sub_smul_snd (hψ 1) hζ hr hr1.le]
      simp [sign]

/-!
### C.2. The aligning phase

-/

/-- The unit `exp (-i arg γ)` rotates `γ` onto the nonnegative real axis. -/
private lemma exp_neg_arg_mul_self (γ : ℂ) :
    Complex.exp (↑(-γ.arg) * Complex.I) * γ = ‖γ‖ := by
  calc Complex.exp (↑(-γ.arg) * Complex.I) * γ =
      Complex.exp (↑(-γ.arg) * Complex.I) * (‖γ‖ * Complex.exp (γ.arg * Complex.I)) := by
        rw [Complex.norm_mul_exp_arg_mul_I]
    _ = ‖γ‖ := by
        rw [mul_left_comm, ← Complex.exp_add]
        simp

/-- Two unit vectors which are not equal up to a global phase, that is with
`‖⟪ψ 0, ψ 1⟫_ℂ‖ < 1`, have a qubit frame. -/
lemma exists_qubitFrame (ψ : Fin 2 → 𝓗[d]) (hψ : ∀ b, ‖ψ b‖ = 1)
    (h : ‖⟪ψ 0, ψ 1⟫_ℂ‖ < 1) : Nonempty (QubitFrame ψ) :=
  ⟨QubitFrame.ofPhase ψ hψ (Complex.norm_exp_ofReal_mul_I _)
    (exp_neg_arg_mul_self ⟪ψ 0, ψ 1⟫_ℂ) (norm_nonneg _) h⟩

end QuantumMechanics.PBR
