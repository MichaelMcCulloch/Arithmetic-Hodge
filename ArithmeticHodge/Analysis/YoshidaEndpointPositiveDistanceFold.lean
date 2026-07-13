import ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelation

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPositiveDistanceFold

open UnitIntervalLogEnergyAffine
open YoshidaEndpointSingularCorrelation

noncomputable section

/-!
# Positive-distance triangular fold

The variables `(t,x)` parameterize the upper half of the centered square by
`(y,x)=(x+t,x)`.  This file reduces the desired fold to that single
measure-theoretic triangular interchange.
-/

/-- The symmetric logarithmic difference kernel on the centered square. -/
def centeredLogDifferenceKernel (w : ℝ → ℝ) (y x : ℝ) : ℝ :=
  (w y - w x) ^ 2 / |y - x|

/-- The upper-triangle energy written in positive-distance coordinates. -/
def centeredPositiveTriangleEnergy (w : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    ∫ x : ℝ in -1..1 - t, centeredLogDifferenceKernel w (x + t) x

/-- At nonnegative distance, the overlap quotient is exactly the centered
logarithmic kernel in triangular coordinates. -/
theorem positiveDistanceEnergy_div_eq_triangle_section
    (w : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    centeredPositiveDistanceEnergy w t / t =
      ∫ x : ℝ in -1..1 - t, centeredLogDifferenceKernel w (x + t) x := by
  unfold centeredPositiveDistanceEnergy centeredLogDifferenceKernel
  rw [div_eq_inv_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  change t⁻¹ * (w (t + x) - w x) ^ 2 =
    (w (x + t) - w x) ^ 2 / |(x + t) - x|
  rw [show |(x + t) - x| = t by
    rw [show (x + t) - x = t by ring, abs_of_nonneg ht]]
  rw [div_eq_inv_mul]
  rw [add_comm x t]

/-- The outer positive-distance integral is exactly the triangular-coordinate
integral; no interchange of the two integration variables is used here. -/
theorem integral_positiveDistanceEnergy_div_eq_triangle
    (w : ℝ → ℝ) :
    (∫ t : ℝ in 0..2, centeredPositiveDistanceEnergy w t / t) =
      centeredPositiveTriangleEnergy w := by
  unfold centeredPositiveTriangleEnergy
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  exact positiveDistanceEnergy_div_eq_triangle_section w ht'.1

/-- The single remaining Tonelli/Fubini statement: positive-distance
coordinates cover exactly one half of the symmetric centered square. -/
def PositiveDistanceTriangleInterchange (w : ℝ → ℝ) : Prop :=
  centeredPositiveTriangleEnergy w = centeredRawLogEnergy w / 2

/-- Once the triangular interchange is available, the desired factor `1/4`
is purely algebraic. -/
theorem half_integral_positiveDistanceEnergy_eq_centeredRaw_of_interchange
    (w : ℝ → ℝ) (hinterchange : PositiveDistanceTriangleInterchange w) :
    (1 / 2 : ℝ) *
        (∫ t : ℝ in 0..2, centeredPositiveDistanceEnergy w t / t) =
      centeredRawLogEnergy w / 4 := by
  rw [integral_positiveDistanceEnergy_div_eq_triangle]
  unfold PositiveDistanceTriangleInterchange at hinterchange
  rw [hinterchange]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointPositiveDistanceFold
