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

/-- Positive-distance overlap contribution before the outer singular
integration. -/
def centeredPositiveDistanceEnergy (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ in -1..1 - t, (w (t + x) - w x) ^ 2

/-- The two endpoint tails left outside the overlap at distance `t`. -/
def centeredEndpointBoundaryTail (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ x : ℝ in 1 - t..1, w x ^ 2) +
    ∫ x : ℝ in -1..-1 + t, w x ^ 2

/-- Integrating the fixed-distance identity reduces the singular correlation
to the positive-distance energy and the boundary-tail integral. -/
theorem integral_correlation_defect_div_eq_energy_add_boundary
    (w : ℝ → ℝ) (hw : Continuous w)
    (henergy : IntervalIntegrable
      (fun t : ℝ ↦ centeredPositiveDistanceEnergy w t / t) volume 0 2)
    (hboundary : IntervalIntegrable
      (fun t : ℝ ↦ centeredEndpointBoundaryTail w t / t) volume 0 2) :
    (∫ t : ℝ in 0..2,
      (centeredEndpointCorrelation w 0 - centeredEndpointCorrelation w t) / t) =
      (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2, centeredPositiveDistanceEnergy w t / t) +
        (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2, centeredEndpointBoundaryTail w t / t) := by
  have hpoint (t : ℝ) :
      (centeredEndpointCorrelation w 0 - centeredEndpointCorrelation w t) / t =
        (1 / 2 : ℝ) * (centeredPositiveDistanceEnergy w t / t) +
          (1 / 2 : ℝ) * (centeredEndpointBoundaryTail w t / t) := by
    rw [centeredEndpointCorrelation_zero_sub_eq_overlap_add_tails w hw t]
    unfold centeredPositiveDistanceEnergy centeredEndpointBoundaryTail
    ring
  calc
    _ = ∫ t : ℝ in 0..2,
        ((1 / 2 : ℝ) * (centeredPositiveDistanceEnergy w t / t) +
          (1 / 2 : ℝ) * (centeredEndpointBoundaryTail w t / t)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      exact hpoint t
    _ = (∫ t : ℝ in 0..2,
          (1 / 2 : ℝ) * (centeredPositiveDistanceEnergy w t / t)) +
        ∫ t : ℝ in 0..2,
          (1 / 2 : ℝ) * (centeredEndpointBoundaryTail w t / t) := by
      exact intervalIntegral.integral_add
        (henergy.const_mul (1 / 2 : ℝ))
        (hboundary.const_mul (1 / 2 : ℝ))
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- The desired singular-correlation identity follows exactly from the
positive-distance fold and the boundary-tail Fubini identity.  The two
hypotheses isolate the remaining analytic interchange statements without
introducing a spectral expansion or cutoff. -/
theorem integral_correlation_defect_div_eq_centered_energy_add_potential
    (w : ℝ → ℝ) (hw : Continuous w)
    (henergy : IntervalIntegrable
      (fun t : ℝ ↦ centeredPositiveDistanceEnergy w t / t) volume 0 2)
    (hboundary : IntervalIntegrable
      (fun t : ℝ ↦ centeredEndpointBoundaryTail w t / t) volume 0 2)
    (hpositiveFold :
      (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2, centeredPositiveDistanceEnergy w t / t) =
        centeredRawLogEnergy w / 4)
    (hboundaryFold :
      (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2, centeredEndpointBoundaryTail w t / t) =
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, w x ^ 2)) :
    (∫ t : ℝ in 0..2,
      (centeredEndpointCorrelation w 0 - centeredEndpointCorrelation w t) / t) =
      centeredRawLogEnergy w / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) +
        Real.log 2 * (∫ x : ℝ in -1..1, w x ^ 2) := by
  rw [integral_correlation_defect_div_eq_energy_add_boundary
    w hw henergy hboundary, hpositiveFold, hboundaryFold]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelation
