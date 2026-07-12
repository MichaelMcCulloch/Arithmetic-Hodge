import ArithmeticHodge.Analysis.UnitIntervalLogEnergyAffine
import ArithmeticHodge.Analysis.UnitIntervalLogEnergyProjection
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open MeasureTheory Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.UnitIntervalIntegralBridge

noncomputable section

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection

/-!
# Unit-interval subtype and interval-integral bridges

The `L²` form domain uses the canonical unit-interval subtype, while affine
transport is most direct for nested interval integrals on `ℝ`.  These lemmas
prove that the two representations agree exactly.
-/

/-- Integrating a real function over the canonical unit-interval subtype is
the same as its oriented integral from `0` to `1`. -/
theorem integral_unitInterval_eq_intervalIntegral (g : ℝ → ℝ) :
    (∫ x : unitInterval, g (x : ℝ)) =
      ∫ x : ℝ in 0..1, g x := by
  calc
    _ = ∫ x : ℝ in Set.Icc 0 1, g x :=
      unitInterval.measurePreserving_coe.integral_comp
        unitInterval.measurableEmbedding_coe g
    _ = _ := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- An integrable product-subtype integral is the corresponding nested
unit-interval integral. -/
theorem integral_unitInterval_prod_eq_intervalIntegral_integral
    (G : ℝ → ℝ → ℝ)
    (hG : Integrable (fun z : unitInterval × unitInterval ↦
      G (z.1 : ℝ) (z.2 : ℝ))) :
    (∫ z : unitInterval × unitInterval,
      G (z.1 : ℝ) (z.2 : ℝ)) =
      ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, G x y := by
  calc
    _ = ∫ x : unitInterval, ∫ y : unitInterval,
        G (x : ℝ) (y : ℝ) := MeasureTheory.integral_prod _ hG
    _ = ∫ x : unitInterval, ∫ y : ℝ in 0..1,
        G (x : ℝ) y := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact integral_unitInterval_eq_intervalIntegral
        (fun y ↦ G (x : ℝ) y)
    _ = _ := integral_unitInterval_eq_intervalIntegral
      (fun x ↦ ∫ y : ℝ in 0..1, G x y)

/-- The subtype half-energy of a centered affine pullback is exactly one
quarter of the centered raw nested energy. -/
theorem unitIntervalLogEnergy_centeredPullback
    (w : ℝ → ℝ)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ)))) :
    unitIntervalLogEnergy
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) =
        (1 / 4 : ℝ) * centeredRawLogEnergy w := by
  have hbridge := integral_unitInterval_prod_eq_intervalIntegral_integral
    (fun s t ↦
      (centeredPullback w s - centeredPullback w t) ^ 2 / |s - t|)
    (by
      simpa only [unitIntervalRawLogEnergyIntegrand] using henergy)
  unfold unitIntervalLogEnergy unitIntervalRawLogEnergyIntegrand
  rw [hbridge, rawLogEnergy_centeredPullback]
  ring

/-- The subtype squared mass of the centered pullback has Jacobian `1/2`. -/
theorem integral_unitInterval_centeredPullback_sq
    (w : ℝ → ℝ) :
    (∫ t : unitInterval, centeredPullback w (t : ℝ) ^ 2) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2 := by
  calc
    _ = ∫ t : ℝ in 0..1, centeredPullback w t ^ 2 :=
      integral_unitInterval_eq_intervalIntegral
        (fun t ↦ centeredPullback w t ^ 2)
    _ = _ := normSq_centeredPullback w

/-- A subtype unit-interval half-energy gap transports exactly to the
centered raw logarithmic gap. -/
theorem four_mul_centered_normSq_le_of_unitIntervalLogEnergy_gap
    (w : ℝ → ℝ)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hunit :
      2 * (∫ t : unitInterval,
        centeredPullback w (t : ℝ) ^ 2) ≤
      unitIntervalLogEnergy
        (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) :
    4 * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w := by
  rw [integral_unitInterval_centeredPullback_sq,
    unitIntervalLogEnergy_centeredPullback w henergy] at hunit
  linarith

end

end ArithmeticHodge.Analysis.UnitIntervalIntegralBridge
