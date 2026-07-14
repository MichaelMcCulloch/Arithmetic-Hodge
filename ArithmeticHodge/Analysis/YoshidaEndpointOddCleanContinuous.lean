import ArithmeticHodge.Analysis.YoshidaEndpointOddCleanPositive
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable

set_option autoImplicit false

open MeasureTheory

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddCleanContinuous

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialIntegrable

noncomputable section

/-- Continuity already supplies the endpoint-potential integrability needed
by the clean odd endpoint theorem. -/
theorem yoshidaEndpointOddCleanQuadratic_nonneg_of_continuous
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w) :
    0 ≤ yoshidaEndpointOddCleanQuadratic w := by
  exact yoshidaEndpointOddCleanQuadratic_nonneg w hwcont hf henergy hwodd
    (intervalIntegrable_endpointPotential_mul_sq w hwcont)

/-- Continuous form-domain specialization of the rational odd coercive
reserve. -/
theorem one_hundredth_energy_le_yoshidaEndpointOddCleanQuadratic_of_continuous
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w) :
    (1 / 100 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      yoshidaEndpointOddCleanQuadratic w := by
  exact one_hundredth_energy_le_yoshidaEndpointOddCleanQuadratic
    w hwcont hf henergy hwodd
      (intervalIntegrable_endpointPotential_mul_sq w hwcont)

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddCleanContinuous
