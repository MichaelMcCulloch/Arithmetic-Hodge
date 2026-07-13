import ArithmeticHodge.Analysis.YoshidaEndpointOddCleanLocallyLipschitz
import ArithmeticHodge.Analysis.YoshidaEndpointPhysicalRealQuadratic
import ArithmeticHodge.Analysis.YoshidaPointwiseOddRealImag

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddPhysicalPositive

open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanLocallyLipschitz
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPhysicalRealQuadratic
open YoshidaEndpointScaledCorrelation
open YoshidaPointwiseOddPeriodicCore
open YoshidaPointwiseOddRealImag

noncomputable section

/-- The exact physical endpoint quadratic is nonnegative on the real
coefficient of every structural odd periodic source profile. -/
theorem yoshidaEndpointPhysicalRealQuadratic_realProfile_nonneg
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA) :
    0 ≤ yoshidaEndpointPhysicalRealQuadratic
      (pointwiseOddPeriodicCoreRealProfile f) := by
  let g : ℝ → ℝ := pointwiseOddPeriodicCoreRealProfile f
  have hgcont : Continuous g :=
    continuous_pointwiseOddPeriodicCoreRealProfile yoshidaEndpointA_pos f
  have hgodd : Function.Odd g :=
    pointwiseOddPeriodicCoreRealProfile_odd f
  have hlocal : LocallyLipschitzOn (Icc (-1) 1)
      (centeredRescale yoshidaEndpointA g) := by
    simpa only [centeredRescale] using
      locallyLipschitzOn_centered_pointwiseOddPeriodicCoreRealProfile
        yoshidaEndpointA_pos f
  have hwodd : Function.Odd (centeredRescale yoshidaEndpointA g) := by
    intro x
    unfold centeredRescale
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring,
      hgodd]
  rw [yoshidaEndpointPhysicalRealQuadratic_eq_clean g hgcont hlocal]
  exact mul_nonneg yoshidaEndpointA_pos.le
    (yoshidaEndpointOddCleanQuadratic_nonneg_of_locallyLipschitzOn
      (centeredRescale yoshidaEndpointA g)
      (hgcont.comp (continuous_const.mul continuous_id))
      hwodd hlocal)

/-- The same structural physical positivity holds for the imaginary
coefficient profile. -/
theorem yoshidaEndpointPhysicalRealQuadratic_imagProfile_nonneg
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA) :
    0 ≤ yoshidaEndpointPhysicalRealQuadratic
      (pointwiseOddPeriodicCoreImagProfile f) := by
  let g : ℝ → ℝ := pointwiseOddPeriodicCoreImagProfile f
  have hgcont : Continuous g :=
    continuous_pointwiseOddPeriodicCoreImagProfile yoshidaEndpointA_pos f
  have hgodd : Function.Odd g :=
    pointwiseOddPeriodicCoreImagProfile_odd f
  have hlocal : LocallyLipschitzOn (Icc (-1) 1)
      (centeredRescale yoshidaEndpointA g) := by
    simpa only [centeredRescale] using
      locallyLipschitzOn_centered_pointwiseOddPeriodicCoreImagProfile
        yoshidaEndpointA_pos f
  have hwodd : Function.Odd (centeredRescale yoshidaEndpointA g) := by
    intro x
    unfold centeredRescale
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring,
      hgodd]
  rw [yoshidaEndpointPhysicalRealQuadratic_eq_clean g hgcont hlocal]
  exact mul_nonneg yoshidaEndpointA_pos.le
    (yoshidaEndpointOddCleanQuadratic_nonneg_of_locallyLipschitzOn
      (centeredRescale yoshidaEndpointA g)
      (hgcont.comp (continuous_const.mul continuous_id))
      hwodd hlocal)

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddPhysicalPositive
