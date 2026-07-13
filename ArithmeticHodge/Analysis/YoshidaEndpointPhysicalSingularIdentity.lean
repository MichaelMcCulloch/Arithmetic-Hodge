import ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound
import ArithmeticHodge.Analysis.YoshidaEndpointPhysicalSingularScaling
import ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelationLipschitz

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPhysicalSingularIdentity

open UnitIntervalLogEnergyAffine
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPhysicalSingularScaling
open YoshidaEndpointPotentialBound
open YoshidaEndpointScaledCorrelation
open YoshidaEndpointSingularCorrelationLipschitz

noncomputable section

/-- Exact physical-coordinate singular correlation at Yoshida's endpoint
scale. -/
theorem integral_physical_correlation_defect_div_eq_clean_singular
    (f : ℝ → ℝ) (hf : Continuous f)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1)
      (centeredRescale yoshidaEndpointA f)) :
    (∫ u : ℝ in 0..2 * yoshidaEndpointA,
      (realEndpointCorrelation yoshidaEndpointA f 0 -
        realEndpointCorrelation yoshidaEndpointA f u) / u) =
      yoshidaEndpointA *
        (centeredRawLogEnergy (centeredRescale yoshidaEndpointA f) / 4 +
          (∫ x : ℝ in -1..1,
            yoshidaEndpointPotential x *
              centeredRescale yoshidaEndpointA f x ^ 2) +
          Real.log 2 *
            (∫ x : ℝ in -1..1,
              centeredRescale yoshidaEndpointA f x ^ 2)) := by
  rw [integral_realEndpointCorrelation_defect_div yoshidaEndpointA_pos f]
  rw [integral_correlation_defect_div_eq_centered_energy_add_potential_of_locallyLipschitzOn
    (centeredRescale yoshidaEndpointA f) (by
      unfold centeredRescale
      fun_prop) hlocal]

end

end ArithmeticHodge.Analysis.YoshidaEndpointPhysicalSingularIdentity
