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

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenSharpScalar
