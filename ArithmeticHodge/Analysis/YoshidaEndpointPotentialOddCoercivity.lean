import ArithmeticHodge.Analysis.YoshidaEndpointOcticOddCoercivity

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddCoercivity

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointOcticOddCoercivity
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialBound

noncomputable section

theorem seven_fifths_mul_integral_sq_le_logEnergy_div_four_add_endpointPotential
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w)
    (hpotential : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * w x ^ 2) volume (-1) 1) :
    (7 / 5 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w / 4 +
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
  have hocticInt : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointOctic x * w x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointOctic
    fun_prop
  have hmono :
      (∫ x : ℝ in -1..1, yoshidaEndpointOctic x * w x ^ 2) ≤
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (-1 : ℝ) ≤ 1) hocticInt hpotential
    intro x hx
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply octic_le_endpointPotential
    rw [abs_lt]
    exact hx
  have hoctic :=
    seven_fifths_mul_integral_sq_le_logEnergy_div_four_add_octic
      w hwcont hf henergy hwodd
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialOddCoercivity
