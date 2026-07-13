import ArithmeticHodge.Analysis.CenteredEndpointCorrelation
import ArithmeticHodge.Analysis.UnitIntervalLogEnergyAffine
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelation

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaEndpointPotentialBound

noncomputable section

/-!
# Structural endpoint singular correlation identity

The one-sided correlation defect splits into the positive-distance half of
the logarithmic difference energy and two endpoint tails.  This is the
algebraic first step in the correlation representation of the clean endpoint
quadratic.
-/

/-- Exact overlap-square and endpoint-tail decomposition at a fixed positive
distance. -/
theorem centeredEndpointCorrelation_zero_sub_eq_overlap_add_tails
    (w : ℝ → ℝ) (hw : Continuous w) (t : ℝ) :
    centeredEndpointCorrelation w 0 - centeredEndpointCorrelation w t =
      (1 / 2 : ℝ) *
          (∫ x : ℝ in -1..1 - t, (w (t + x) - w x) ^ 2) +
        (1 / 2 : ℝ) *
          ((∫ x : ℝ in 1 - t..1, w x ^ 2) +
            ∫ x : ℝ in -1..-1 + t, w x ^ 2) := by
  have hwSq : Continuous (fun x : ℝ ↦ w x ^ 2) := hw.pow 2
  have hshift :
      (∫ x : ℝ in -1..1 - t, w (t + x) ^ 2) =
        ∫ x : ℝ in -1 + t..1, w x ^ 2 := by
    convert intervalIntegral.integral_comp_add_left
      (a := (-1 : ℝ)) (b := 1 - t) (fun y : ℝ ↦ w y ^ 2) t using 1
    all_goals ring_nf
  have hleft :
      (∫ x : ℝ in -1..-1 + t, w x ^ 2) +
          ∫ x : ℝ in -1..1 - t, w (t + x) ^ 2 =
        ∫ x : ℝ in -1..1, w x ^ 2 := by
    rw [hshift]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hwSq.intervalIntegrable (-1) (-1 + t))
      (hwSq.intervalIntegrable (-1 + t) 1)
  have hright :
      (∫ x : ℝ in -1..1 - t, w x ^ 2) +
          ∫ x : ℝ in 1 - t..1, w x ^ 2 =
        ∫ x : ℝ in -1..1, w x ^ 2 := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (hwSq.intervalIntegrable (-1) (1 - t))
      (hwSq.intervalIntegrable (1 - t) 1)
  have hsquare :
      (∫ x : ℝ in -1..1 - t, (w (t + x) - w x) ^ 2) =
        (∫ x : ℝ in -1..1 - t, w (t + x) ^ 2) +
          (∫ x : ℝ in -1..1 - t, w x ^ 2) -
          2 * (∫ x : ℝ in -1..1 - t, w (t + x) * w x) := by
    have hwShiftSq : Continuous (fun x : ℝ ↦ w (t + x) ^ 2) := by
      fun_prop
    have hwCross : Continuous (fun x : ℝ ↦ w (t + x) * w x) := by
      fun_prop
    calc
      (∫ x : ℝ in -1..1 - t, (w (t + x) - w x) ^ 2) =
          ∫ x : ℝ in -1..1 - t,
            (w (t + x) ^ 2 + w x ^ 2) -
              2 * (w (t + x) * w x) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = (∫ x : ℝ in -1..1 - t,
            w (t + x) ^ 2 + w x ^ 2) -
          ∫ x : ℝ in -1..1 - t, 2 * (w (t + x) * w x) := by
        exact intervalIntegral.integral_sub
          ((hwShiftSq.add hwSq).intervalIntegrable (-1) (1 - t))
          ((hwCross.const_mul 2).intervalIntegrable (-1) (1 - t))
      _ = ((∫ x : ℝ in -1..1 - t, w (t + x) ^ 2) +
            ∫ x : ℝ in -1..1 - t, w x ^ 2) -
          2 * (∫ x : ℝ in -1..1 - t, w (t + x) * w x) := by
        rw [intervalIntegral.integral_add
            (hwShiftSq.intervalIntegrable (-1) (1 - t))
            (hwSq.intervalIntegrable (-1) (1 - t)),
          intervalIntegral.integral_const_mul]
  rw [centeredEndpointCorrelation_zero]
  unfold centeredEndpointCorrelation
  rw [hsquare]
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelation
