import ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModes
import ArithmeticHodge.Analysis.ShiftedLegendreFiniteEnergyGap
import ArithmeticHodge.Analysis.UnitIntervalIntegralBridge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open MeasureTheory Polynomial
open scoped unitInterval

namespace ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModeL2

noncomputable section

open ShiftedLegendreCenteredLowModes
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine

/-!
# The centered degree-one shifted-Legendre mode in `L²`

This file records the exact normalization and affine first-moment formula
for the single degree-one mode used in the endpoint Schur block.  Every
constant is obtained from symbolic integration and the exact affine
Jacobian.
-/

private theorem eval_shiftedLegendreReal_one (t : ℝ) :
    (shiftedLegendreReal 1).eval t = 1 - 2 * t := by
  calc
    (shiftedLegendreReal 1).eval t =
        (shiftedLegendreReal 1).eval (((2 * t - 1) + 1) / 2) := by
      congr 1
      ring
    _ = (centeredShiftedLegendreReal 1).eval (2 * t - 1) :=
      (eval_centeredShiftedLegendreReal 1 (2 * t - 1)).symm
    _ = -(2 * t - 1) := eval_centeredShiftedLegendreReal_one _
    _ = 1 - 2 * t := by ring

/-- The unnormalized degree-one shifted-Legendre mode has exact squared
`L²([0,1])` norm `1/3`. -/
theorem norm_sq_shiftedLegendreL2_one :
    ‖shiftedLegendreL2 1‖ ^ 2 = (1 / 3 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
      (polynomialToContinuous (shiftedLegendreReal 1)))
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
      (polynomialToContinuous (shiftedLegendreReal 1))) = (1 / 3 : ℝ)
  have hinner := MeasureTheory.ContinuousMap.inner_toLp
    (𝕜 := ℝ) (volume : Measure unitInterval)
    (polynomialToContinuous (shiftedLegendreReal 1))
    (polynomialToContinuous (shiftedLegendreReal 1))
  calc
    _ = ∫ t : unitInterval,
        (polynomialToContinuous (shiftedLegendreReal 1)) t *
          starRingEnd ℝ
            ((polynomialToContinuous (shiftedLegendreReal 1)) t) := hinner
    _ = ∫ t : unitInterval,
        (shiftedLegendreReal 1).eval (t : ℝ) *
          (shiftedLegendreReal 1).eval (t : ℝ) := by
      rfl
    _ = ∫ t : ℝ in 0..1,
        (shiftedLegendreReal 1).eval t *
          (shiftedLegendreReal 1).eval t :=
      integral_unitInterval_eq_intervalIntegral
        (fun t : ℝ ↦
          (shiftedLegendreReal 1).eval t *
            (shiftedLegendreReal 1).eval t)
    _ = ∫ t : ℝ in 0..1, (1 - 2 * t) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change (shiftedLegendreReal 1).eval t *
        (shiftedLegendreReal 1).eval t = (1 - 2 * t) ^ 2
      rw [eval_shiftedLegendreReal_one]
      ring
    _ = ∫ t : ℝ in 0..1, (4 * t ^ 2 - 4 * t + 1) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      ring
    _ = (1 / 3 : ℝ) := by
      rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 1)
          (Continuous.intervalIntegrable (by fun_prop) 0 1),
        intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) 0 1)
          (Continuous.intervalIntegrable (by fun_prop) 0 1),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        integral_pow,
        integral_id]
      norm_num

/-- The degree-one normalization denominator is strictly positive. -/
theorem norm_shiftedLegendreL2_one_pos :
    0 < ‖shiftedLegendreL2 1‖ := by
  exact norm_pos_iff.mpr (shiftedLegendreL2_ne_zero 1)

@[simp]
theorem norm_shiftedLegendreL2_one_ne_zero :
    ‖shiftedLegendreL2 1‖ ≠ 0 :=
  ne_of_gt norm_shiftedLegendreL2_one_pos

/-- Squaring the inverse normalization contributes the exact Schur factor
`3`. -/
theorem inv_norm_shiftedLegendreL2_one_sq :
    ‖shiftedLegendreL2 1‖⁻¹ ^ 2 = (3 : ℝ) := by
  rw [inv_pow, norm_sq_shiftedLegendreL2_one]
  norm_num

private theorem shiftedLegendreHilbertBasis_repr_one_eq_unitIntegral
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval)) :
    shiftedLegendreHilbertBasis.repr (hf.toLp f) 1 =
      ‖shiftedLegendreL2 1‖⁻¹ *
        ∫ t : unitInterval, f t * (1 - 2 * (t : ℝ)) := by
  rw [shiftedLegendreHilbertBasis.repr_apply_apply,
    shiftedLegendreHilbertBasis_apply, normalizedShiftedLegendreL2,
    real_inner_smul_left, real_inner_comm, shiftedLegendreL2,
    ← integral_mul_polynomial_eq_inner f hf]
  apply congrArg (fun z : ℝ ↦ ‖shiftedLegendreL2 1‖⁻¹ * z)
  apply integral_congr_ae
  filter_upwards [] with t
  rw [eval_shiftedLegendreReal_one]

private theorem integral_centeredPullback_mul_degreeOne :
    ∀ w : ℝ → ℝ,
      (∫ t : unitInterval,
        centeredPullback w (t : ℝ) * (1 - 2 * (t : ℝ))) =
        -(1 / 2 : ℝ) * ∫ x : ℝ in -1..1, x * w x := by
  intro w
  calc
    _ = ∫ t : ℝ in 0..1,
        centeredPullback w t * (1 - 2 * t) :=
      integral_unitInterval_eq_intervalIntegral _
    _ = ∫ t : ℝ in 0..1,
        (fun x : ℝ ↦ -(x * w x)) (2 * t - 1) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      simp only [centeredPullback]
      ring
    _ = (1 / 2 : ℝ) *
        ∫ x : ℝ in -1..1, -(x * w x) :=
      integral_comp_two_mul_sub_one (fun x : ℝ ↦ -(x * w x))
    _ = -(1 / 2 : ℝ) *
        ∫ x : ℝ in -1..1, x * w x := by
      rw [intervalIntegral.integral_neg]
      ring

/-- The normalized degree-one Hilbert coefficient of the affine pullback is
the centered first moment with the exact sign, Jacobian, and inverse norm. -/
theorem shiftedLegendreHilbertBasis_repr_centeredPullback_one_eq
    (w : ℝ → ℝ)
    (hw : MemLp
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))
      2 (volume : Measure unitInterval)) :
    shiftedLegendreHilbertBasis.repr
        (hw.toLp (fun t : unitInterval ↦
          centeredPullback w (t : ℝ))) 1 =
      -(1 / 2 : ℝ) * ‖shiftedLegendreL2 1‖⁻¹ *
        ∫ x : ℝ in -1..1, x * w x := by
  rw [shiftedLegendreHilbertBasis_repr_one_eq_unitIntegral,
    integral_centeredPullback_mul_degreeOne]
  ring

/-- Squaring the degree-one coefficient gives the exact centered
first-moment contribution `3/4`, ready for the scalar Schur block. -/
theorem shiftedLegendreHilbertBasis_repr_centeredPullback_one_sq
    (w : ℝ → ℝ)
    (hw : MemLp
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))
      2 (volume : Measure unitInterval)) :
    (shiftedLegendreHilbertBasis.repr
        (hw.toLp (fun t : unitInterval ↦
          centeredPullback w (t : ℝ))) 1) ^ 2 =
      (3 / 4 : ℝ) *
        (∫ x : ℝ in -1..1, x * w x) ^ 2 := by
  rw [shiftedLegendreHilbertBasis_repr_centeredPullback_one_eq w hw]
  calc
    (-(1 / 2 : ℝ) * ‖shiftedLegendreL2 1‖⁻¹ *
        ∫ x : ℝ in -1..1, x * w x) ^ 2 =
      (1 / 4 : ℝ) * ‖shiftedLegendreL2 1‖⁻¹ ^ 2 *
        (∫ x : ℝ in -1..1, x * w x) ^ 2 := by
      ring
    _ = _ := by
      rw [inv_norm_shiftedLegendreL2_one_sq]
      ring

end

end ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModeL2
