import ArithmeticHodge.Analysis.YoshidaEndpointBoundaryTailFold
import ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelation

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointSingularBoundaryAssembled

open YoshidaEndpointBoundaryTailFold
open YoshidaEndpointPotentialBound
open YoshidaEndpointSingularCorrelation

noncomputable section

/-- After the endpoint-tail Fubini theorem, the only remaining part of the
singular correlation is the positive-distance logarithmic energy. -/
theorem integral_correlation_defect_div_eq_half_energy_add_potential
    (w : ℝ → ℝ) (hw : Continuous w)
    (henergy : IntervalIntegrable
      (fun t : ℝ ↦ centeredPositiveDistanceEnergy w t / t) volume 0 2) :
    (∫ t : ℝ in 0..2,
      (CenteredEndpointCorrelation.centeredEndpointCorrelation w 0 -
        CenteredEndpointCorrelation.centeredEndpointCorrelation w t) / t) =
      (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2, centeredPositiveDistanceEnergy w t / t) +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) +
        Real.log 2 * (∫ x : ℝ in -1..1, w x ^ 2) := by
  rw [integral_correlation_defect_div_eq_energy_add_boundary w hw henergy
    (intervalIntegrable_centeredEndpointBoundaryTail_div w hw)]
  rw [half_integral_centeredEndpointBoundaryTail_div_eq w hw]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointSingularBoundaryAssembled
