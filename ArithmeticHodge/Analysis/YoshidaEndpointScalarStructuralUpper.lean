import ArithmeticHodge.Analysis.YoshidaEulerGammaStructuralFine
import ArithmeticHodge.Analysis.YoshidaEndpointCleanQuadratic
import ArithmeticHodge.Analysis.YoshidaEndpointEvenSharpScalar

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointScalarStructuralUpper

open YoshidaEndpointEvenSharpScalar
open YoshidaEndpointOddCleanPositive
open YoshidaEulerGammaStructuralFine

noncomputable section

/-!
# Short structural upper bound for the endpoint scalar loss

The Euler term uses only the corrected fourth harmonic approximation and the
fixed `log 2` series.  The product logarithm uses a fixed universal atanh
series.  No long harmonic normalization or finite certificate is involved.
-/

theorem yoshidaEndpointScalarMassLoss_lt_338887_div_250000 :
    yoshidaEndpointScalarMassLoss < (338887 / 250000 : ℝ) := by
  have hgamma := eulerGamma_lt_577248_div_million
  have hlog :=
    log_pi_mul_log_two_lt_seven_thousand_seven_hundred_eighty_three_div_ten_thousand
  unfold yoshidaEndpointScalarMassLoss
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointScalarStructuralUpper
