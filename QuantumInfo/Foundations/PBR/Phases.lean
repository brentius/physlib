/-
Copyright (c) 2026 brent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: brent
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Walsh signs and the phases of the PBR measurement

Signs and Walsh characters on `Fin n → Fin 2`, and the choice of the copy number and phases.

## i. Overview

The entangled measurement in the Pusey–Barrett–Rudolph (PBR) theorem is built from the signs
`(-1)^{jk}` on `Fin 2`, the Walsh characters `∏ i, (-1)^{x_i z_i}` on `Fin n → Fin 2`, and a
family of unit-modulus phases `ω z`. This file contains the purely mathematical input: the
orthogonality of Walsh characters, the choice of a number of copies `n` with
`2 cⁿ ≤ (c + s)ⁿ` (via Bernoulli's inequality), and the choice of phases with
`∑ z, ω z * ∏ i, ![c, s] (z i) = 0` (via the intermediate value theorem). In the PBR proof the
latter makes every outcome of the measurement orthogonal to one product state. Finally, the
rescaled Walsh vectors `x ↦ (√(2 ^ n))⁻¹ * walsh x z` are orthonormal.

## ii. Key results

- `PBR.sum_walsh_mul_walsh` : orthogonality of the Walsh characters.
- `PBR.exists_two_mul_pow_le` : the choice of the number of copies.
- `PBR.exists_phases` : the choice of the unit-modulus phases.
- `PBR.sum_conj_inv_sqrt_mul_walsh` : the rescaled Walsh vectors are orthonormal.

## iii. Table of contents

- A. Signs and Walsh characters
  - A.1. Signs on `Fin 2`
  - A.2. Walsh characters
- B. Choosing the number of copies
- C. Choosing the phases
  - C.1. Choosing the angle
  - C.2. Products of amplitudes
  - C.3. The phases
- D. Rescaled Walsh vectors

## iv. References

- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]

-/

@[expose] public section

noncomputable section

namespace PBR

/-!
## A. Signs and Walsh characters

### A.1. Signs on `Fin 2`

-/

/-- The sign `(-1) ^ (j * k)` for `j k : Fin 2`, as a complex number. -/
def sign (j k : Fin 2) : ℂ := if j = 1 ∧ k = 1 then -1 else 1

/-- The sign `(-1) ^ (j * k)` is symmetric in `j` and `k`. -/
lemma sign_comm (j k : Fin 2) : sign j k = sign k j := by
  unfold sign
  by_cases hj : j = 1 <;> by_cases hk : k = 1 <;> simp [hj, hk]

/-- A sign squares to one. -/
lemma sign_mul_self (j k : Fin 2) : sign j k * sign j k = 1 := by
  unfold sign
  split_ifs <;> norm_num

/-- A sign is real: it equals its complex conjugate. -/
lemma conj_sign (j k : Fin 2) : starRingEnd ℂ (sign j k) = sign j k := by
  unfold sign
  split_ifs <;> simp

/-- A sign has unit norm. -/
lemma norm_sign (j k : Fin 2) : ‖sign j k‖ = 1 := by
  unfold sign
  split_ifs <;> simp

/-- Orthogonality of the signs on `Fin 2`. -/
lemma sum_sign_mul_sign (a b : Fin 2) :
    ∑ k, sign a k * sign b k = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [sign, Fin.sum_univ_two]

/-!
### A.2. Walsh characters

-/

/-- The Walsh character `∏ i, (-1) ^ (x i * z i)` on `Fin n → Fin 2`. -/
def walsh {n : ℕ} (x z : Fin n → Fin 2) : ℂ := ∏ i, sign (x i) (z i)

/-- The Walsh character `walsh x z` is symmetric in `x` and `z`. -/
lemma walsh_comm {n : ℕ} (x z : Fin n → Fin 2) : walsh x z = walsh z x := by
  unfold walsh
  exact Finset.prod_congr rfl fun i _ => sign_comm _ _

/-- A Walsh character squares to one. -/
lemma walsh_mul_self {n : ℕ} (x z : Fin n → Fin 2) : walsh x z * walsh x z = 1 := by
  unfold walsh
  rw [← Finset.prod_mul_distrib]
  simp only [sign_mul_self, Finset.prod_const_one]

/-- A Walsh character is real: it equals its complex conjugate. -/
lemma conj_walsh {n : ℕ} (x z : Fin n → Fin 2) : starRingEnd ℂ (walsh x z) = walsh x z := by
  unfold walsh
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => conj_sign _ _

/-- A Walsh character has unit norm. -/
lemma norm_walsh {n : ℕ} (x z : Fin n → Fin 2) : ‖walsh x z‖ = 1 := by
  simp [walsh, norm_sign]

/-- Orthogonality of the Walsh characters. -/
lemma sum_walsh_mul_walsh {n : ℕ} (x y : Fin n → Fin 2) :
    ∑ z, walsh x z * walsh y z = if x = y then 2 ^ n else 0 := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  have key : ∑ z : Fin n → Fin 2, ∏ i, sign (x i) (z i) * sign (y i) (z i) =
      ∏ i, ∑ k, sign (x i) k * sign (y i) k :=
    (Fintype.prod_sum fun i k => sign (x i) k * sign (y i) k).symm
  rw [key]
  simp only [sum_sign_mul_sign]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-!
## B. Choosing the number of copies

-/

/-- For `0 < c` and `0 < s`, enough copies give `2 cⁿ ≤ (c + s)ⁿ` (Bernoulli's inequality). -/
lemma exists_two_mul_pow_le {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∃ n : ℕ, 2 * c ^ n ≤ (c + s) ^ n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (c / s)
  refine ⟨n, ?_⟩
  rw [div_le_iff₀ hs] at hn
  have ht : 1 ≤ (n : ℝ) * (s / c) := by
    rw [mul_div_assoc', le_div_iff₀ hc, one_mul]
    exact hn
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ s / c by have := div_pos hs hc; linarith) n
  have h2 := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ (1 + s / c) ^ n by linarith)
    (pow_pos hc n).le
  calc 2 * c ^ n ≤ (1 + s / c) ^ n * c ^ n := h2
    _ = (c + s) ^ n := by rw [← mul_pow, add_mul, one_mul, div_mul_cancel₀ s hc.ne']

/-!
## C. Choosing the phases

### C.1. Choosing the angle

-/

/-- The value of `‖(c + e^{iα} s)ⁿ - cⁿ‖` at `α = 0`. -/
private lemma norm_pow_sub_pow_at_zero (c s : ℝ) (n : ℕ) :
    ‖((c : ℂ) + Complex.exp ((0 : ℝ) * Complex.I) * s) ^ n - (c : ℂ) ^ n‖ =
      |(c + s) ^ n - c ^ n| := by
  have h : ((c : ℂ) + Complex.exp ((0 : ℝ) * Complex.I) * s) ^ n - (c : ℂ) ^ n =
      (((c + s) ^ n - c ^ n : ℝ) : ℂ) := by
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    push_cast
    ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-- The value of `‖(c + e^{iα} s)ⁿ - cⁿ‖` at `α = π`. -/
private lemma norm_pow_sub_pow_at_pi (c s : ℝ) (n : ℕ) :
    ‖((c : ℂ) + Complex.exp (Real.pi * Complex.I) * s) ^ n - (c : ℂ) ^ n‖ =
      |(c - s) ^ n - c ^ n| := by
  have h : ((c : ℂ) + Complex.exp (Real.pi * Complex.I) * s) ^ n - (c : ℂ) ^ n =
      (((c - s) ^ n - c ^ n : ℝ) : ℂ) := by
    rw [Complex.exp_pi_mul_I]
    push_cast
    ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-- If `0 ≤ s ≤ c` and `2 cⁿ ≤ (c + s)ⁿ`, some angle `α` gives
`‖(c + e^{iα} s)ⁿ - cⁿ‖ = cⁿ` (intermediate value theorem on `[0, π]`). -/
lemma exists_norm_pow_sub_pow_eq {c s : ℝ} {n : ℕ} (hs : 0 ≤ s) (hsc : s ≤ c)
    (hn : 2 * c ^ n ≤ (c + s) ^ n) :
    ∃ α : ℝ, ‖((c : ℂ) + Complex.exp (α * Complex.I) * s) ^ n - (c : ℂ) ^ n‖ = c ^ n := by
  have hc : 0 ≤ c := hs.trans hsc
  have hf : ContinuousOn
      (fun α : ℝ => ‖((c : ℂ) + Complex.exp (α * Complex.I) * s) ^ n - (c : ℂ) ^ n‖)
      (Set.Icc 0 Real.pi) := by
    fun_prop
  have h0 : c ^ n ≤
      ‖((c : ℂ) + Complex.exp ((0 : ℝ) * Complex.I) * s) ^ n - (c : ℂ) ^ n‖ := by
    rw [norm_pow_sub_pow_at_zero]
    exact (by linarith : c ^ n ≤ (c + s) ^ n - c ^ n).trans (le_abs_self _)
  have hπ : ‖((c : ℂ) + Complex.exp (Real.pi * Complex.I) * s) ^ n - (c : ℂ) ^ n‖ ≤
      c ^ n := by
    rw [norm_pow_sub_pow_at_pi, abs_le]
    have h1 : (c - s) ^ n ≤ c ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h2 : 0 ≤ (c - s) ^ n := pow_nonneg (by linarith) n
    have h3 : 0 ≤ c ^ n := pow_nonneg hc n
    constructor <;> linarith
  obtain ⟨α, -, hα⟩ := intermediate_value_Icc' Real.pi_pos.le hf ⟨hπ, h0⟩
  exact ⟨α, hα⟩

/-!
### C.2. Products of amplitudes

-/

/-- Multiplying the phase product `∏ i, ![1, e] (z i)` into the amplitude product. -/
lemma prod_phase_mul_prod_amp {n : ℕ} (e c s : ℂ) (z : Fin n → Fin 2) :
    (∏ i, ![1, e] (z i)) * ∏ i, ![c, s] (z i) = ∏ i, ![c, e * s] (z i) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize z i = k
  fin_cases k <;> simp

/-- The phase product `∏ i, ![1, e] (z i)` has unit norm when `e` does. -/
lemma norm_prod_phase {n : ℕ} {e : ℂ} (he : ‖e‖ = 1) (z : Fin n → Fin 2) :
    ‖∏ i, ![1, e] (z i)‖ = 1 := by
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  generalize z i = k
  fin_cases k <;> simp [he]

/-!
### C.3. The phases

-/

/-- The phases `ω 0 = -((c + e s)ⁿ - cⁿ) / cⁿ` and `ω z = ∏ i, ![1, e] (z i)` for `z ≠ 0`
cancel the amplitude products. -/
lemma sum_phases_mul_amp {n : ℕ} (c s e : ℂ) (hc : c ^ n ≠ 0) :
    ∑ z : Fin n → Fin 2, (if z = 0 then -(((c + e * s) ^ n - c ^ n) / c ^ n)
      else ∏ i, ![1, e] (z i)) * ∏ i, ![c, s] (z i) = 0 := by
  have key : ∀ z : Fin n → Fin 2, (if z = 0 then -(((c + e * s) ^ n - c ^ n) / c ^ n)
      else ∏ i, ![1, e] (z i)) * ∏ i, ![c, s] (z i) =
      ∏ i, ![c, e * s] (z i) - if z = 0 then (c + e * s) ^ n else 0 := by
    intro z
    split_ifs with h
    · subst h
      have hA : ∏ i : Fin n, ![c, s] ((0 : Fin n → Fin 2) i) = c ^ n := by simp
      have hF : ∏ i : Fin n, ![c, e * s] ((0 : Fin n → Fin 2) i) = c ^ n := by simp
      rw [hA, hF, neg_mul, div_mul_cancel₀ _ hc]
      ring
    · rw [prod_phase_mul_prod_amp, sub_zero]
  rw [Finset.sum_congr rfl fun z _ => key z, Finset.sum_sub_distrib, ← Fintype.sum_pow,
    Fin.sum_univ_two]
  simp

/-- Unit-modulus phases `ω z` with `∑ z, ω z * ∏ i, ![c, s] (z i) = 0`, for `0 ≤ s ≤ c`,
`0 < c` and `2 cⁿ ≤ (c + s)ⁿ`. -/
lemma exists_phases {c s : ℝ} {n : ℕ} (hc : 0 < c) (hs : 0 ≤ s) (hsc : s ≤ c)
    (hn : 2 * c ^ n ≤ (c + s) ^ n) :
    ∃ ω : (Fin n → Fin 2) → ℂ,
      (∀ z, ‖ω z‖ = 1) ∧ ∑ z, ω z * ∏ i, ![(c : ℂ), (s : ℂ)] (z i) = 0 := by
  obtain ⟨α, hα⟩ := exists_norm_pow_sub_pow_eq hs hsc hn
  have hcn : (c : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hc.ne')
  refine ⟨fun z => if z = 0 then
      -((((c : ℂ) + Complex.exp (α * Complex.I) * s) ^ n - (c : ℂ) ^ n) / (c : ℂ) ^ n)
      else ∏ i, ![1, Complex.exp (α * Complex.I)] (z i),
    fun z => ?_, sum_phases_mul_amp _ _ _ hcn⟩
  dsimp only
  split_ifs
  · rw [norm_neg, norm_div, hα, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc.le,
      div_self (pow_ne_zero _ hc.ne')]
  · exact norm_prod_phase (Complex.norm_exp_ofReal_mul_I α) z

/-!
## D. Rescaled Walsh vectors

-/

/-- The square of `(√(2 ^ n))⁻¹`, as a complex number, is `(2 ^ n)⁻¹`. -/
lemma ofReal_inv_sqrt_two_pow_sq (n : ℕ) :
    (((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) ^ 2 = ((2 : ℂ) ^ n)⁻¹ := by
  rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by positivity)]
  push_cast
  rfl

/-- `(√(2 ^ n))⁻¹ ^ 2 * (if p then 2 ^ n else 0) = if p then 1 else 0`. -/
lemma ofReal_inv_sqrt_two_pow_sq_mul_ite (n : ℕ) (p : Prop) [Decidable p] :
    (((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) ^ 2 * (if p then (2 : ℂ) ^ n else 0) =
      if p then 1 else 0 := by
  rw [ofReal_inv_sqrt_two_pow_sq]
  split_ifs
  · exact inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)
  · exact mul_zero _

/-- The rescaled Walsh vectors `x ↦ (√(2 ^ n))⁻¹ * walsh x z` are orthonormal. -/
lemma sum_conj_inv_sqrt_mul_walsh (n : ℕ) (z z' : Fin n → Fin 2) :
    ∑ x : Fin n → Fin 2, starRingEnd ℂ ((Real.sqrt (2 ^ n))⁻¹ * walsh x z) *
      ((Real.sqrt (2 ^ n))⁻¹ * walsh x z') = if z = z' then 1 else 0 := by
  simp only [map_mul, Complex.conj_ofReal, conj_walsh]
  calc _ = ∑ x : Fin n → Fin 2,
        (((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) ^ 2 * (walsh z x * walsh z' x) :=
        Finset.sum_congr rfl fun x _ => by rw [walsh_comm x z, walsh_comm x z']; ring
    _ = _ := by rw [← Finset.mul_sum, sum_walsh_mul_walsh, ofReal_inv_sqrt_two_pow_sq_mul_ite]

/-- A family of `2 ^ n` unit complex scalars `a z`, each rescaled by `(√(2 ^ n))⁻¹`, has total
squared norm one. -/
lemma sum_norm_sq_inv_sqrt_mul {n : ℕ} {a : (Fin n → Fin 2) → ℂ} (ha : ∀ z, ‖a z‖ = 1) :
    ∑ z, ‖(Real.sqrt (2 ^ n))⁻¹ * a z‖ ^ 2 = 1 := by
  simp only [norm_mul, ha, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 ^ n), Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

end PBR
