import ArithmeticHodge.Analysis.YoshidaEndpointScaledCorrelation

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointPhysicalSingularScaling

open CenteredEndpointCorrelation
open YoshidaEndpointScaledCorrelation

noncomputable section

/-- The renormalized singular correlation defect acquires one factor under
the physical-to-centered endpoint dilation. -/
theorem integral_realEndpointCorrelation_defect_div
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    (∫ u : ℝ in 0..2 * a,
      (realEndpointCorrelation a f 0 - realEndpointCorrelation a f u) / u) =
      a * ∫ t : ℝ in 0..2,
        (centeredEndpointCorrelation (centeredRescale a f) 0 -
          centeredEndpointCorrelation (centeredRescale a f) t) / t := by
  let G : ℝ → ℝ := fun u ↦
    (realEndpointCorrelation a f 0 - realEndpointCorrelation a f u) / u
  have hsubst :
      a • (∫ t : ℝ in 0..2, G (a * t)) =
        ∫ u : ℝ in a * 0..a * 2, G u := by
    exact intervalIntegral.smul_integral_comp_mul_left G a
  have hpoint (t : ℝ) :
      G (a * t) =
        (centeredEndpointCorrelation (centeredRescale a f) 0 -
          centeredEndpointCorrelation (centeredRescale a f) t) / t := by
    dsimp only [G]
    rw [realEndpointCorrelation_mul ha f t]
    have hzero := realEndpointCorrelation_mul ha f 0
    simp only [mul_zero] at hzero
    rw [hzero]
    by_cases ht : t = 0
    · simp [ht]
    · field_simp [ha.ne', ht]
  calc
    (∫ u : ℝ in 0..2 * a,
        (realEndpointCorrelation a f 0 - realEndpointCorrelation a f u) / u) =
        ∫ u : ℝ in 0..2 * a, G u := rfl
    _ = a * ∫ t : ℝ in 0..2, G (a * t) := by
      simpa only [mul_zero, smul_eq_mul, mul_comm] using hsubst.symm
    _ = a * ∫ t : ℝ in 0..2,
        (centeredEndpointCorrelation (centeredRescale a f) 0 -
          centeredEndpointCorrelation (centeredRescale a f) t) / t := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _ht
      exact hpoint t

end

end ArithmeticHodge.Analysis.YoshidaEndpointPhysicalSingularScaling
