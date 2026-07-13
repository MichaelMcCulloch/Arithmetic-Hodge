import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.CenteredEndpointCorrelation

noncomputable section

/-- One-sided autocorrelation of a real function on the centered interval.
For `0 ≤ t ≤ 2`, the overlap is `[-1, 1-t]`. -/
def centeredEndpointCorrelation (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ in -1..1 - t, w (t + x) * w x

theorem centeredEndpointCorrelation_zero (w : ℝ → ℝ) :
    centeredEndpointCorrelation w 0 = ∫ x : ℝ in -1..1, w x ^ 2 := by
  unfold centeredEndpointCorrelation
  simp only [zero_add, sub_zero]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

end


end ArithmeticHodge.Analysis.CenteredEndpointCorrelation
