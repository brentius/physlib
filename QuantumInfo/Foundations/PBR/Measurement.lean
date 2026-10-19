/-
Copyright (c) 2026 brent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: brent
-/
module

public import QuantumInfo.Foundations.PBR.QubitFrame
public import QuantumInfo.Measurements.POVM

/-!
# The PBR measurement

The entangled measurement on `n` copies used in the Pusey–Barrett–Rudolph (PBR) theorem.

## i. Overview

Let `F` be a qubit frame of two pure states `ψ 0`, `ψ 1`, with frame kets `e 0`, `e 1` and
amplitudes `c`, `s`, and let `ω z` be unit phases indexed by `z : Fin n → Fin 2`. The product
frame kets `E z = e (z 0) ⊗ ⋯ ⊗ e (z (n - 1))` are orthonormal, and so are the measurement kets
`b x = 2^{-n/2} ∑ z, conj (ω z) * walsh x z * E z`. If `∑ z, ω z * ∏ i, ![c, s] (z i) = 0`, then
`b x` is orthogonal to the product state `Ψ x = ψ (x 0) ⊗ ⋯ ⊗ ψ (x (n - 1))`. Moreover every
product state `Ψ y` lies in the span of the kets `b x`. Completing the kets `b x` to a POVM
gives a measurement on `n` copies every outcome of which has probability zero on some product
state `Ψ x`.

## ii. Key results

- `PBR.QubitFrame.measurementKet` : the measurement kets `b x`.
- `PBR.QubitFrame.dot_measurementKet_measurementKet` : the measurement kets are orthonormal.
- `PBR.QubitFrame.dot_measurementKet_piProd_self` : `b x` is orthogonal to `Ψ x`.
- `PBR.QubitFrame.sum_norm_sq_dot_measurementKet` : `∑ x, ‖〈b x‖Ψ y〉‖ ^ 2 = 1`.
- `PBR.exists_povm` : the PBR measurement.

## iii. Table of contents

- A. The product frame kets
- B. The measurement kets
  - B.1. Definition
  - B.2. Orthonormality
  - B.3. Bra-kets with product states
- C. The PBR measurement

## iv. References

- M. F. Pusey, J. Barrett and T. Rudolph, *On the reality of the quantum state*,
  Nature Phys. 8, 475–478 (2012), arXiv:1111.3328. [ref: Pusey:2011de]

-/

@[expose] public section

noncomputable section

open Braket

namespace PBR

/-!
## A. The product frame kets

-/

namespace QubitFrame

variable {d : Type*} [Fintype d] {ψ : Fin 2 → Ket d} {n : ℕ}

/-- The product frame ket `E z = e (z 0) ⊗ ⋯ ⊗ e (z (n - 1))` on `n` copies. -/
def frameKet (F : QubitFrame ψ) (z : Fin n → Fin 2) : Ket (Fin n → d) :=
  Ket.piProd fun i => F.e (z i)

variable (F : QubitFrame ψ)

/-- The product frame kets are orthonormal. -/
lemma dot_frameKet_frameKet (z z' : Fin n → Fin 2) :
    〈F.frameKet z‖F.frameKet z'〉 = if z = z' then 1 else 0 := by
  simp [frameKet, dot_piProd, F.dot_e_e, Finset.prod_boole, funext_iff]

/-- The components of a product state in the product frame. -/
lemma dot_frameKet_piProd (z x : Fin n → Fin 2) :
    〈F.frameKet z‖Ket.piProd fun i => ψ (x i)〉 =
      (∏ i, F.phase (x i)) * walsh z x * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i) := by
  simp only [frameKet, dot_piProd, F.dot_e_state, Finset.prod_mul_distrib, walsh]

/-- Each product state lies in the span of the product frame. -/
lemma sum_norm_sq_dot_frameKet_piProd (y : Fin n → Fin 2) :
    ∑ z : Fin n → Fin 2, ‖〈F.frameKet z‖Ket.piProd fun i => ψ (y i)〉‖ ^ 2 = 1 := by
  simp only [frameKet, dot_piProd, norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i j => ‖〈F.e j‖ψ (y i)〉‖ ^ 2)]
  exact Finset.prod_eq_one fun i _ => F.sum_norm_sq_dot_e_state (y i)

/-!
## B. The measurement kets

### B.1. Definition

-/

/-- The PBR measurement ket `b x = (√(2 ^ n))⁻¹ ∑ z, conj (ω z) * walsh x z * E z` for unit
phases `ω`. -/
def measurementKet (ω : (Fin n → Fin 2) → ℂ) (hω : ∀ z, ‖ω z‖ = 1) (x : Fin n → Fin 2) :
    Ket (Fin n → d) where
  vec k := ∑ z, ((Real.sqrt (2 ^ n))⁻¹ * starRingEnd ℂ (ω z) * walsh x z) * F.frameKet z k
  normalized' := by
    refine (sum_norm_sq_sum_mul_of_orthonormal (fun z k => F.frameKet z k)
      (fun a b => F.dot_frameKet_frameKet a b) _).trans ?_
    simp only [mul_assoc]
    exact sum_norm_sq_inv_sqrt_mul fun z => by
      rw [norm_mul, Complex.norm_conj, hω, norm_walsh, one_mul]

variable {ω : (Fin n → Fin 2) → ℂ} {hω : ∀ z, ‖ω z‖ = 1}

/-- The entries of a measurement ket. -/
lemma measurementKet_apply (x : Fin n → Fin 2) (k : Fin n → d) :
    F.measurementKet ω hω x k =
      ∑ z, ((Real.sqrt (2 ^ n))⁻¹ * starRingEnd ℂ (ω z) * walsh x z) * F.frameKet z k :=
  rfl

/-- The bra of a measurement ket is the corresponding combination of frame bras. -/
lemma dot_measurementKet (x : Fin n → Fin 2) (φ : Ket (Fin n → d)) :
    〈F.measurementKet ω hω x‖φ〉 =
      ∑ z, (Real.sqrt (2 ^ n))⁻¹ * ω z * walsh x z * 〈F.frameKet z‖φ〉 := by
  simp only [Braket.dot, Bra.eq_conj, measurementKet_apply, map_sum, map_mul,
    Complex.conj_ofReal, Complex.conj_conj, conj_walsh, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun k _ => by ring

/-!
### B.2. Orthonormality

-/

/-- The components of a measurement ket in the product frame. -/
lemma dot_frameKet_measurementKet (z y : Fin n → Fin 2) :
    〈F.frameKet z‖F.measurementKet ω hω y〉 =
      (Real.sqrt (2 ^ n))⁻¹ * starRingEnd ℂ (ω z) * walsh y z := by
  rw [dot_swap_conj, dot_measurementKet]
  simp [F.dot_frameKet_frameKet, conj_walsh]

/-- The PBR measurement kets are orthonormal. -/
lemma dot_measurementKet_measurementKet (x y : Fin n → Fin 2) :
    〈F.measurementKet ω hω x‖F.measurementKet ω hω y〉 = if x = y then 1 else 0 := by
  have hω' : ∀ z, ω z * starRingEnd ℂ (ω z) = 1 := fun z => by
    rw [Complex.mul_conj', hω]
    simp
  rw [dot_measurementKet]
  simp_rw [dot_frameKet_measurementKet]
  calc _ = ∑ z, (((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) ^ 2 * (walsh x z * walsh y z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        linear_combination
          ((((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) ^ 2 * walsh x z * walsh y z) * hω' z
    _ = _ := by rw [← Finset.mul_sum, sum_walsh_mul_walsh, ofReal_inv_sqrt_two_pow_sq_mul_ite]

/-!
### B.3. Bra-kets with product states

-/

/-- If `∑ z, ω z * ∏ i, ![c, s] (z i) = 0`, the measurement ket `b x` is orthogonal to the
product state `Ψ x = ψ (x 0) ⊗ ⋯ ⊗ ψ (x (n - 1))`. -/
lemma dot_measurementKet_piProd_self
    (hsum : ∑ z, ω z * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i) = 0) (x : Fin n → Fin 2) :
    〈F.measurementKet ω hω x‖Ket.piProd fun i => ψ (x i)〉 = 0 := by
  rw [dot_measurementKet]
  simp_rw [dot_frameKet_piProd]
  calc _ = ∑ z, ((Real.sqrt (2 ^ n))⁻¹ * ∏ i, F.phase (x i)) *
        (ω z * ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [walsh_comm z x]
        linear_combination ((((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) * (∏ i, F.phase (x i)) * ω z *
          ∏ i, ![(F.c : ℂ), (F.s : ℂ)] (z i)) * walsh_mul_self x z
    _ = 0 := by rw [← Finset.mul_sum, hsum, mul_zero]

/-- Parseval's identity for the PBR measurement: every product state
`Ψ y = ψ (y 0) ⊗ ⋯ ⊗ ψ (y (n - 1))` lies in the span of the measurement kets. -/
lemma sum_norm_sq_dot_measurementKet (y : Fin n → Fin 2) :
    ∑ x, ‖〈F.measurementKet ω hω x‖Ket.piProd fun i => ψ (y i)〉‖ ^ 2 = 1 := by
  simp_rw [dot_measurementKet]
  calc _ = ∑ x, ‖∑ z : Fin n → Fin 2, (ω z * 〈F.frameKet z‖Ket.piProd fun i => ψ (y i)〉) *
        ((Real.sqrt (2 ^ n))⁻¹ * walsh x z)‖ ^ 2 :=
        Finset.sum_congr rfl fun x _ =>
          congrArg (‖·‖ ^ 2) (Finset.sum_congr rfl fun z _ => by ring)
    _ = ∑ z : Fin n → Fin 2, ‖ω z * 〈F.frameKet z‖Ket.piProd fun i => ψ (y i)〉‖ ^ 2 :=
        sum_norm_sq_sum_mul_of_orthonormal (fun z x => (Real.sqrt (2 ^ n))⁻¹ * walsh x z)
          (sum_conj_inv_sqrt_mul_walsh n) _
    _ = 1 := by
        simp_rw [norm_mul, hω, one_mul]
        exact F.sum_norm_sq_dot_frameKet_piProd y

end QubitFrame

/-!
## C. The PBR measurement

-/

/-- The PBR measurement: for two pure states which are not equal up to a global phase there is
a number of copies `n` and a POVM on `n` copies every outcome of which has probability zero on
some product state `ψ (x 0) ⊗ ⋯ ⊗ ψ (x (n - 1))`. -/
lemma exists_povm {d : Type*} [Fintype d] [DecidableEq d] (ψ : Fin 2 → Ket d)
    (h : MState.pure (ψ 0) ≠ MState.pure (ψ 1)) :
    ∃ (n : ℕ) (E : POVM (Option (Fin n → Fin 2)) (Fin n → d)), ∀ o, ∃ x : Fin n → Fin 2,
      E.measure (MState.pure (Ket.piProd fun i => ψ (x i))) o = 0 := by
  obtain ⟨F⟩ := exists_qubitFrame ψ h
  obtain ⟨n, hn⟩ := exists_two_mul_pow_le F.c_pos F.s_pos
  obtain ⟨ω, hω, hsum⟩ := exists_phases F.c_pos F.s_pos.le F.s_le_c hn
  have hb := F.dot_measurementKet_measurementKet (ω := ω) (hω := hω)
  refine ⟨n, POVM.ofOrthonormal (F.measurementKet ω hω) hb, ?_⟩
  rintro (_ | x)
  · -- the outcome `none` has probability `1 - 1` on every product state
    refine ⟨0, Subtype.ext ?_⟩
    rw [POVM.measure_ofOrthonormal_none, F.sum_norm_sq_dot_measurementKet, sub_self]
    rfl
  · -- the outcome `some x` has probability zero on `Ψ x`
    refine ⟨x, Subtype.ext ?_⟩
    rw [POVM.measure_ofOrthonormal_some, F.dot_measurementKet_piProd_self hsum, norm_zero,
      zero_pow two_ne_zero]
    rfl

end PBR
