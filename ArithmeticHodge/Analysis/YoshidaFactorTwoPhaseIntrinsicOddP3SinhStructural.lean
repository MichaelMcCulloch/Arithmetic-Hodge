import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveRankStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP3SinhStructural

noncomputable section

open UnitIntervalLogEnergyAffine
open ShiftedLegendreOrthogonality
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseLegendreFourFiveRankStructural
open YoshidaFactorTwoPhaseSymmetricCoercivity

/-!
# A positive Rodrigues model for the third odd endpoint moment

The `P₃` sinh moment is transported once to `[0,1]` and Rodrigues'
identity moves all three polynomial derivatives onto the exponential.
Every factor in the resulting integral is nonnegative.  This records the
sign needed by the sheared odd endpoint without evaluating the moment.
-/

private theorem centeredP3_affine (t : ℝ) :
    centeredP3 (2 * t - 1) = -(shiftedLegendreReal 3).eval t := by
  norm_num [centeredP3, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose]
  ring

private theorem integral_exp_mul_shiftedLegendreReal_three
    (lambda : ℝ) :
    (∫ t : ℝ in 0..1,
      Real.exp (2 * lambda * t) * (shiftedLegendreReal 3).eval t) =
      (-2 * lambda) ^ 3 / 6 *
        ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (t ^ 3 * (1 - t) ^ 3) := by
  have h := factorial_mul_integral_exp_shiftedLegendreReal 3 lambda
  have hbase (t : ℝ) :
      (shiftedLegendreRodriguesBase 3).eval t =
        t ^ 3 * (1 - t) ^ 3 := by
    simp [shiftedLegendreRodriguesBase]
  simp_rw [hbase] at h
  norm_num at h
  calc
    _ = (1 / 6 : ℝ) *
        (6 * ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (shiftedLegendreReal 3).eval t) := by
      ring
    _ = (1 / 6 : ℝ) *
        ((-2 * lambda) ^ 3 *
          ∫ t : ℝ in 0..1,
            Real.exp (2 * lambda * t) * (t ^ 3 * (1 - t) ^ 3)) := by
      rw [show -(2 * lambda) = -2 * lambda by ring] at h
      rw [h]
    _ = _ := by ring

private theorem centeredSinhMoment_centeredP3_eq_exp (lambda : ℝ) :
    centeredSinhMoment centeredP3 lambda =
      ∫ x : ℝ in -1..1, Real.exp (lambda * x) * centeredP3 x := by
  have hodd : Function.Odd centeredP3 := by
    intro x
    unfold centeredP3
    ring
  have hzero := centeredCoshMoment_eq_zero_of_odd hodd lambda
  unfold centeredSinhMoment
  calc
    _ = (∫ x : ℝ in -1..1,
          Real.cosh (lambda * x) * centeredP3 x) +
        ∫ x : ℝ in -1..1,
          Real.sinh (lambda * x) * centeredP3 x := by
      rw [show (∫ x : ℝ in -1..1,
          Real.cosh (lambda * x) * centeredP3 x) = 0 by exact hzero]
      ring
    _ = ∫ x : ℝ in -1..1,
        (Real.cosh (lambda * x) * centeredP3 x +
          Real.sinh (lambda * x) * centeredP3 x) := by
      rw [intervalIntegral.integral_add]
      · exact Continuous.intervalIntegrable
          ((Real.continuous_cosh.comp (by fun_prop)).mul
            (by unfold centeredP3; fun_prop)) (-1) 1
      · exact Continuous.intervalIntegrable
          ((Real.continuous_sinh.comp (by fun_prop)).mul
            (by unfold centeredP3; fun_prop)) (-1) 1
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _
      change Real.cosh (lambda * x) * centeredP3 x +
        Real.sinh (lambda * x) * centeredP3 x =
          Real.exp (lambda * x) * centeredP3 x
      rw [← add_mul, Real.cosh_add_sinh]

/-- Exact positive Rodrigues representation of the `P₃` sinh moment. -/
theorem centeredSinhMoment_centeredP3_rodrigues (lambda : ℝ) :
    centeredSinhMoment centeredP3 lambda =
      2 * Real.exp (-lambda) * ((2 * lambda) ^ 3 / 6) *
        ∫ t : ℝ in 0..1,
          Real.exp (2 * lambda * t) * (t ^ 3 * (1 - t) ^ 3) := by
  rw [centeredSinhMoment_centeredP3_eq_exp]
  have htransport := integral_comp_two_mul_sub_one
    (fun x : ℝ ↦ Real.exp (lambda * x) * centeredP3 x)
  have hunit :
      (∫ t : ℝ in 0..1,
          Real.exp (lambda * (2 * t - 1)) * centeredP3 (2 * t - 1)) =
        -Real.exp (-lambda) *
          ∫ t : ℝ in 0..1,
            Real.exp (2 * lambda * t) * (shiftedLegendreReal 3).eval t := by
    rw [show (fun t : ℝ ↦
        Real.exp (lambda * (2 * t - 1)) * centeredP3 (2 * t - 1)) =
      fun t ↦ -Real.exp (-lambda) *
        (Real.exp (2 * lambda * t) * (shiftedLegendreReal 3).eval t) by
      funext t
      rw [centeredP3_affine]
      rw [show lambda * (2 * t - 1) = -lambda + 2 * lambda * t by ring,
        Real.exp_add]
      ring,
      intervalIntegral.integral_const_mul]
  rw [hunit, integral_exp_mul_shiftedLegendreReal_three] at htransport
  linarith

/-- The third odd endpoint sinh moment is nonnegative, structurally. -/
theorem oddCleanSinhMoment3_nonneg : 0 ≤ oddCleanSinhMoment3 := by
  have hmoment :
      oddCleanSinhMoment3 = centeredSinhMoment centeredP3
        (yoshidaEndpointA / 2) := by
    unfold oddCleanSinhMoment3 yoshidaEndpointSinhMoment centeredSinhMoment
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hmoment, centeredSinhMoment_centeredP3_rodrigues]
  have hI : 0 ≤ ∫ t : ℝ in 0..1,
      Real.exp (2 * (yoshidaEndpointA / 2) * t) *
        (t ^ 3 * (1 - t) ^ 3) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    positivity
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (div_nonneg
        (pow_nonneg (mul_nonneg (by norm_num)
          (div_nonneg yoshidaEndpointA_pos.le (by norm_num))) 3)
        (by norm_num)))
    hI

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP3SinhStructural
