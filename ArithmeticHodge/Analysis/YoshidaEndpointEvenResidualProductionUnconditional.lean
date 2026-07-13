import ArithmeticHodge.Analysis.YoshidaEndpointEvenCleanPositive
import ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProductionPositive

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProductionUnconditional

open ArithmeticHodge.Analysis
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointEvenCleanPositive
open YoshidaEndpointEvenResidualProductionPositive
open YoshidaEndpointHyperbolicBound
open YoshidaPointwiseParityCore
open YoshidaSectionSixAnalytic

noncomputable section

/-!
# Unconditional production positivity of the even boundary residual

The complete clean-even theorem discharges the only premise of the previously
proved zero-trace production bridge.
-/

/-- Every real zero-trace residual of a pointwise-even periodic source has
nonnegative actual production diagonal. -/
theorem clippedCriticalFormValue_evenBoundaryResidual_nonneg
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0) :
    0 ≤ clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
      (evenBoundaryResidual f : YoshidaClippedSmooth yoshidaEndpointA) := by
  exact clippedCriticalFormValue_evenBoundaryResidual_nonneg_of_cleanEven
    yoshidaEndpointOddCleanQuadratic_nonneg_of_even_of_locallyLipschitzOn
    f hf_real

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProductionUnconditional
