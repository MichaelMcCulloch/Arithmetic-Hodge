import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaEndpointOddSharpMassLoss

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenSharpScalar

open YoshidaConstantBounds
open YoshidaEndpointOddSharpMassLoss

noncomputable section

/-- A structural four-decimal upper bound for the complete even scalar loss.
This retains the separately proved Euler, `log π`, `log log 2`, and `log 2`
series bounds instead of collapsing them to the coarse `7/5`. -/
theorem yoshidaEndpointEvenSharpMassLoss_lt_six_thousand_eight_hundred_thirty_three_div_five_thousand :
    yoshidaEndpointEvenSharpMassLoss < (6833 / 5000 : ℝ) := by
  have hgamma := strict_euler_gamma_bounds.2
  have hpi := strict_log_pi_bounds.2
  have hloglog := strict_log_log_two_bounds.2
  have htwo := strict_log_two_bounds.2
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : Real.log (Real.pi * Real.log 2) =
      Real.log Real.pi + Real.log (Real.log 2) := by
    rw [Real.log_mul Real.pi_ne_zero hlogTwoPos.ne']
  unfold yoshidaEndpointEvenSharpMassLoss
  rw [hprod]
  linarith

/-- The corrected harmonic approximation at index `99` gives a fifth-decimal
Euler upper bound while remaining a single fixed analytic series estimate. -/
theorem eulerMascheroniConstant_lt_twenty_eight_thousand_eight_hundred_sixty_one_div_fifty_thousand :
    Real.eulerMascheroniConstant < (28861 / 50000 : ℝ) := by
  have hupper := eulerGamma_le_gammaUpperApprox 99
  have hlog := strict_log_one_hundred_bounds.1
  apply lt_of_le_of_lt hupper
  simp only [gammaUpperApprox, gammaLowerApprox]
  norm_num [harmonic, Finset.sum_range_succ] at ⊢
  linarith

/-- A direct short logarithm-series bound for the product `π log 2`. -/
theorem log_pi_mul_log_two_lt_seven_thousand_seven_hundred_eighty_three_div_ten_thousand :
    Real.log (Real.pi * Real.log 2) < (7783 / 10000 : ℝ) := by
  let R : ℝ := (3141593 / 1000000 : ℝ) * (6932 / 10000 : ℝ)
  have hpi := Real.pi_lt_d6
  norm_num at hpi
  have htwo := strict_log_two_bounds.2
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : Real.pi * Real.log 2 < R := by
    dsimp only [R]
    exact mul_lt_mul hpi htwo.le hlogTwoPos (by norm_num)
  have hRpos : 0 < R := by
    dsimp only [R]
    norm_num
  have hlogR : Real.log R < (7783 / 10000 : ℝ) := by
    have h := Real.log_div_le_sum_range_add
      (x := (2944380669 / 7944380669 : ℝ))
      (by norm_num) (by norm_num) 6
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  exact (Real.strictMonoOn_log (mul_pos Real.pi_pos hlogTwoPos)
    hRpos hprod).trans hlogR

/-- Sharpened scalar loss used by the small-margin fixed even low block. -/
theorem yoshidaEndpointEvenSharpMassLoss_lt_eight_hundred_fifty_four_div_six_hundred_twenty_five :
    yoshidaEndpointEvenSharpMassLoss < (854 / 625 : ℝ) := by
  have hgamma :=
    eulerMascheroniConstant_lt_twenty_eight_thousand_eight_hundred_sixty_one_div_fifty_thousand
  have hlog :=
    log_pi_mul_log_two_lt_seven_thousand_seven_hundred_eighty_three_div_ten_thousand
  have htwo := strict_log_two_bounds.2
  unfold yoshidaEndpointEvenSharpMassLoss
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenSharpScalar
