import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenSineMomentOneEnclosure

open YoshidaEvenMomentTargets
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

/-!
# Certified enclosure for the first even sine moment

The existing analytic Cauchy-series enclosure becomes narrow enough for the
`10⁻⁵` even target after 1,536 exact head terms.  The remaining infinite tail
is still bounded analytically by `cauchyTailInterval`.
-/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem sineSeriesInterval_1536_sub_evenTarget_one :
    IsSubinterval (sineSeriesInterval 1 1536)
      (yoshidaEvenSineTargets 1) := by
  decide +kernel

/-- The actual first sine moment inhabits its production even target box. -/
theorem yoshidaEvenSineTarget_one_contains :
    (yoshidaEvenSineTargets 1).Contains (yoshidaSineMoment 1) := by
  exact contains_of_subinterval sineSeriesInterval_1536_sub_evenTarget_one
    (sineSeriesInterval_contains (by norm_num) (by norm_num))

end ArithmeticHodge.Analysis.YoshidaEvenSineMomentOneEnclosure
