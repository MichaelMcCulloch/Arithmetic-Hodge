import ArithmeticHodge.Analysis.YoshidaEndpointOddSharpMassLoss
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddCoercivity

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddCorePositive

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialOddCoercivity

noncomputable section

def yoshidaEndpointOddCoreQuadratic (w : ℝ → ℝ) : ℝ :=
  centeredRawLogEnergy w / 4 +
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) -
    yoshidaEndpointOddSharpMassLoss * (∫ x : ℝ in -1..1, w x ^ 2)

theorem yoshidaEndpointOddCoreQuadratic_nonneg
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w)
    (hpotential : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * w x ^ 2) volume (-1) 1) :
    0 ≤ yoshidaEndpointOddCoreQuadratic w := by
  have hcoercive :=
    seven_fifths_mul_integral_sq_le_logEnergy_div_four_add_endpointPotential
      w hwcont hf henergy hwodd hpotential
  have hmass : 0 ≤ ∫ x : ℝ in -1..1, w x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    exact sq_nonneg _
  have hloss :
      yoshidaEndpointOddSharpMassLoss * (∫ x : ℝ in -1..1, w x ^ 2) ≤
        (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) :=
    mul_le_mul_of_nonneg_right
      (le_of_lt yoshidaEndpointOddSharpMassLoss_lt_seven_fifths) hmass
  unfold yoshidaEndpointOddCoreQuadratic
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddCorePositive
