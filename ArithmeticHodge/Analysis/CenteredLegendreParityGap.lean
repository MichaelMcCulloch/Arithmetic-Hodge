import ArithmeticHodge.Analysis.ShiftedLegendreParityGap
import ArithmeticHodge.Analysis.UnitIntervalIntegralBridge

set_option autoImplicit false

open MeasureTheory
open scoped unitInterval

namespace ArithmeticHodge.Analysis.CenteredLegendreParityGap

open ShiftedLegendreCenteredParity
open ShiftedLegendreL2Basis
open ShiftedLegendreParityGap
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection

noncomputable section

/-!
# Centered parity-sector logarithmic gaps

The exact unit-interval parity gaps transport to raw logarithmic energy on
`[-1,1]`.  The affine Jacobians turn the even-sector constant `3` into `6`
and the odd-sector constant `11/3` into `22/3`.
-/

/-- A centered even mean-zero function has raw logarithmic gap `6`. -/
theorem six_mul_integral_sq_le_centeredRawLogEnergy_of_even
    (w : ℝ → ℝ)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hw : Function.Even w)
    (hmean : (∫ x : ℝ in -1..1, w x) = 0) :
    6 * (∫ x : ℝ in -1..1, w x ^ 2) ≤ centeredRawLogEnergy w := by
  have hunitMean :
      (∫ t : unitInterval, centeredPullback w (t : ℝ)) = 0 := by
    calc
      _ = ∫ t : ℝ in 0..1, centeredPullback w t :=
        integral_unitInterval_eq_intervalIntegral (centeredPullback w)
      _ = (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x :=
        integral_comp_two_mul_sub_one w
      _ = 0 := by rw [hmean, mul_zero]
  have hunit :=
    three_mul_integral_sq_le_unitIntervalLogEnergy_of_symm_even
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) hf henergy
      (centeredPullback_symm_of_even w hw) hunitMean
  rw [integral_unitInterval_centeredPullback_sq,
    unitIntervalLogEnergy_centeredPullback w henergy] at hunit
  linarith

/-- A centered odd function whose degree-one shifted-Legendre coefficient
vanishes has raw logarithmic gap `22/3`. -/
theorem twenty_two_div_three_mul_integral_sq_le_centeredRawLogEnergy_of_odd
    (w : ℝ → ℝ)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hw : Function.Odd w)
    (hone : shiftedLegendreHilbertBasis.repr
      (hf.toLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) 1 = 0) :
    (22 / 3 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w := by
  have hunit :=
    eleven_div_three_mul_integral_sq_le_unitIntervalLogEnergy_of_symm_odd
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) hf henergy
      (centeredPullback_symm_of_odd w hw) hone
  rw [integral_unitInterval_centeredPullback_sq,
    unitIntervalLogEnergy_centeredPullback w henergy] at hunit
  linarith

end

end ArithmeticHodge.Analysis.CenteredLegendreParityGap
