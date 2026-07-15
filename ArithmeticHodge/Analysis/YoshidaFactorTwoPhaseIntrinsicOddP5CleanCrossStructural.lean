import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveRankStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseLegendreFourFiveStructural

/-!
# Structural clean `P1/P3`--`P5` crosses

The singular potential part is evaluated exactly from four even logarithmic
moments.  Its logarithmic terms cancel by Legendre orthogonality.  The
remaining regular and hyperbolic crosses are treated by global analytic
envelopes below; no interval subdivision or finite certificate is used.
-/

/-- Exact potential part of the clean `P1`--`P5` cross. -/
theorem integral_endpointPotential_mul_centeredP1_mul_P5 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP1 x *
        factorTwoCenteredP5 x) = (1 / 14 : ℝ) := by
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)).congr
    intro x _hx
    ring
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)).congr
    intro x _hx
    ring
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredP1 x * factorTwoCenteredP5 x) =
      fun x ↦ (63 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) -
        (70 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) +
        (15 / 8 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
    funext x
    unfold centeredP1 factorTwoCenteredP5
    ring,
    intervalIntegral.integral_add
      ((h6.const_mul (63 / 8 : ℝ)).sub (h4.const_mul (70 / 8 : ℝ)))
      (h2.const_mul (15 / 8 : ℝ)),
    intervalIntegral.integral_sub
      (h6.const_mul (63 / 8 : ℝ)) (h4.const_mul (70 / 8 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq]
  ring

/-- Exact potential part of the clean `P3`--`P5` cross. -/
theorem integral_endpointPotential_mul_centeredP3_mul_P5 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredP3 x *
        factorTwoCenteredP5 x) = (1 / 9 : ℝ) := by
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)).congr
    intro x _hx
    ring
  have h6 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)).congr
    intro x _hx
    ring
  have h8 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 8) volume (-1) 1 := by
    apply (intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 4) (continuous_id.pow 4)).congr
    intro x _hx
    ring
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredP3 x * factorTwoCenteredP5 x) =
      fun x ↦ (315 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 8) -
        (539 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) +
        (285 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
        (45 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) by
    funext x
    unfold centeredP3 factorTwoCenteredP5
    ring,
    intervalIntegral.integral_sub
      (((h8.const_mul (315 / 16 : ℝ)).sub
        (h6.const_mul (539 / 16 : ℝ))).add
          (h4.const_mul (285 / 16 : ℝ)))
      (h2.const_mul (45 / 16 : ℝ)),
    intervalIntegral.integral_add
      ((h8.const_mul (315 / 16 : ℝ)).sub
        (h6.const_mul (539 / 16 : ℝ)))
      (h4.const_mul (285 / 16 : ℝ)),
    intervalIntegral.integral_sub
      (h8.const_mul (315 / 16 : ℝ)) (h6.const_mul (539 / 16 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_eight,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
