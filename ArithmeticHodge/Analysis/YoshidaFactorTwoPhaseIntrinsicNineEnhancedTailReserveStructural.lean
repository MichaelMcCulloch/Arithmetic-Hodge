import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineEnhancedTailReserveStructural

noncomputable section

open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineQuantitative
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicResidual

/-!
# The full cutoff-nine survivor reserve

The earlier `P6/P7/P8` estimate uses only a deliberately small residual
reserve.  At a genuine ninth moment gap, the tail phase retains much more:
the full even endpoint-potential half and a stronger even energy share.  After
subtracting the `14/15` allocation and clearing the scalar `1/15`, the exact
remaining reserve is the expression below.
-/

/-- Residual budget available to the coupled cutoff-nine survivor after the
sharp `P6/P7/P8` allocation and the factor-fifteen scaled completion. -/
def factorTwoIntrinsicNineSurvivorResidualReserve
    (eR oR : ℝ → ℝ) : ℝ :=
  (47 / 500 : ℝ) * factorTwoIntrinsicEnergy eR +
    (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR +
    (15 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy eR +
    (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy oR

theorem factorTwoIntrinsicNineSurvivorResidualReserve_nonneg
    (eR oR : ℝ → ℝ) :
    0 ≤ factorTwoIntrinsicNineSurvivorResidualReserve eR oR := by
  unfold factorTwoIntrinsicNineSurvivorResidualReserve
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num) (factorTwoIntrinsicEnergy_nonneg eR))
        (mul_nonneg (by norm_num) (factorTwoIntrinsicEnergy_nonneg oR)))
      (mul_nonneg (by norm_num)
        (factorTwoIntrinsicPotentialEnergy_nonneg eR)))
    (mul_nonneg (by norm_num)
      (factorTwoIntrinsicPotentialEnergy_nonneg oR))

/-- The actual tail complement contains `1/15` of the survivor reserve.
This is the strengthened tail inequality consumed by the direct `9 + 1`
scaled-range completion. -/
theorem factorTwoIntrinsicNineSurvivorResidualReserve_le_fifteen_mul_balancedTail
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 9)
    (hoGap : centeredLegendreMomentsVanishBelow oR 9)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicNineSurvivorResidualReserve eR oR ≤
      15 * (factorTwoEndpointChannelPhase eR oR a b -
        (14 / 15 : ℝ) * factorTwoIntrinsicNineResidualReserve eR oR) := by
  have he0 := centeredEvenP0Coefficient_eq_zero_of_momentsVanishBelow
    eR (by norm_num) heGap
  have htail := factorTwoEndpointChannelPhase_quantitative_of_nine_nine_residual
    eR oR heRc hoRc heRe hoRo he0 heLocal hoLocal
      heGap hoGap a b hab
  unfold factorTwoIntrinsicNineSurvivorResidualReserve
    factorTwoIntrinsicNineResidualReserve
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineEnhancedTailReserveStructural
