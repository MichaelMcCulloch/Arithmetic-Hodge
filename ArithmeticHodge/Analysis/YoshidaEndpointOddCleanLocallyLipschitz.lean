import ArithmeticHodge.Analysis.YoshidaEndpointOddCleanLipschitz
import ArithmeticHodge.Analysis.YoshidaEndpointPullbackLipschitz

set_option autoImplicit false

open Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddCleanLocallyLipschitz

open YoshidaEndpointOddCleanLipschitz
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPullbackLipschitz

noncomputable section

/-- Local smoothness on the centered compact interval is enough for the
complete clean odd endpoint inequality. -/
theorem yoshidaEndpointOddCleanQuadratic_nonneg_of_locallyLipschitzOn
    (w : ℝ → ℝ) (hwcont : Continuous w) (hwodd : Function.Odd w)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w) :
    0 ≤ yoshidaEndpointOddCleanQuadratic w := by
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback w hlocal
  exact yoshidaEndpointOddCleanQuadratic_nonneg_of_lipschitzWith
    w hwcont hwodd hLip

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddCleanLocallyLipschitz
