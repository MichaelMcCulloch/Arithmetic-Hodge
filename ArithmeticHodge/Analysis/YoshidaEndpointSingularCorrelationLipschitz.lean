import ArithmeticHodge.Analysis.YoshidaEndpointBoundaryTailFold
import ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelation
import ArithmeticHodge.Analysis.YoshidaEndpointTriangleFoldLipschitz

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelationLipschitz

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaEndpointBoundaryTailFold
open YoshidaEndpointPotentialBound
open YoshidaEndpointSingularCorrelation
open YoshidaEndpointTriangleFoldLipschitz

noncomputable section

/-- Exact singular endpoint correlation identity on the locally Lipschitz
source domain. -/
theorem integral_correlation_defect_div_eq_centered_energy_add_potential_of_locallyLipschitzOn
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w) :
    (∫ t : ℝ in 0..2,
      (centeredEndpointCorrelation w 0 - centeredEndpointCorrelation w t) / t) =
      centeredRawLogEnergy w / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) +
        Real.log 2 * (∫ x : ℝ in -1..1, w x ^ 2) := by
  exact integral_correlation_defect_div_eq_centered_energy_add_potential
    w hwcont
      (intervalIntegrable_centeredPositiveDistanceEnergy_div_of_locallyLipschitzOn
        w hlocal)
      (intervalIntegrable_centeredEndpointBoundaryTail_div w hwcont)
      (half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
        w hlocal)
      (half_integral_centeredEndpointBoundaryTail_div_eq w hwcont)

end

end ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelationLipschitz
