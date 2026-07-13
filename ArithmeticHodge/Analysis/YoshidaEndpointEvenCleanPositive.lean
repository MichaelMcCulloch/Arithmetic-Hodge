import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedAssembly
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeFinal

set_option autoImplicit false

open Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenCleanPositive

open YoshidaEndpointEvenProjectedAssembly
open YoshidaEndpointEvenProjectedRemainderEnvelopeFinal
open YoshidaEndpointOddCleanPositive

noncomputable section

/-!
# Structural positivity of the complete clean even endpoint form

The fixed projected representer matrix is positive definite, so the weighted
Schur argument applies uniformly to every continuous, even, locally Lipschitz
profile.  This theorem has no remaining analytic or finite-dimensional
premise.
-/

/-- The clean endpoint quadratic is nonnegative on the complete continuous
even form domain. -/
theorem yoshidaEndpointOddCleanQuadratic_nonneg_of_even_of_locallyLipschitzOn
    (w : ℝ → ℝ) (hw : Continuous w) (hweven : Function.Even w)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w) :
    0 ≤ yoshidaEndpointOddCleanQuadratic w := by
  exact yoshidaEndpointOddCleanQuadratic_nonneg_of_even_of_projectedDual
    w hw hweven hlocal fixedProjectedWeightedDual_le_exactLowGram

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenCleanPositive
