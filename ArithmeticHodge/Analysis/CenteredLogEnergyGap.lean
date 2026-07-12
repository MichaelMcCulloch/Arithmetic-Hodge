import ArithmeticHodge.Analysis.ShiftedLegendreFiniteEnergyGap
import ArithmeticHodge.Analysis.UnitIntervalIntegralBridge

set_option autoImplicit false

open MeasureTheory
open scoped unitInterval

namespace ArithmeticHodge.Analysis.CenteredLogEnergyGap

open ShiftedLegendreFiniteEnergyGap
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection

noncomputable section

/-!
# The centered finite-energy logarithmic gap

The complete shifted-Legendre gap on `[0,1]`, the exact subtype-integral
bridge, and the affine Jacobian identities combine to give the centered raw
gap on `[-1,1]`.  No finite truncation remains in the theorem.
-/

/-- Every real centered pullback with finite logarithmic energy and zero mean
satisfies the sharp centered raw logarithmic gap. -/
theorem four_mul_integral_sq_le_centeredRawLogEnergy
    (w : ℝ → ℝ)
    (hf : MemLp
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hmean : (∫ x : ℝ in -1..1, w x) = 0) :
    4 * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w := by
  have hmeanUnit :
      (∫ t : unitInterval, centeredPullback w (t : ℝ)) = 0 := by
    calc
      _ = ∫ t : ℝ in 0..1, centeredPullback w t :=
        integral_unitInterval_eq_intervalIntegral (centeredPullback w)
      _ = (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x :=
        integral_comp_two_mul_sub_one w
      _ = 0 := by rw [hmean, mul_zero]
  have hunit :
      2 * (∫ t : unitInterval,
        centeredPullback w (t : ℝ) ^ 2) ≤
      unitIntervalLogEnergy
        (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) :=
    two_mul_integral_sq_le_unitIntervalLogEnergy
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))
      hf henergy hmeanUnit
  exact four_mul_centered_normSq_le_of_unitIntervalLogEnergy_gap
    w henergy hunit

end

end ArithmeticHodge.Analysis.CenteredLogEnergyGap
