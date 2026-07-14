import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointEvenStructuralReduction
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural correlations for the intrinsic `P4` mode

The three correlations below are exact overlap polynomials.  They are shared
by the two signed endpoint arguments.  Their proofs are ordinary polynomial
integration; no rank cutoff, quadrature, or sampled certificate is used.
-/

/-- Symmetric overlap correlation between `P0` and `P4`. -/
def factorTwoIntrinsicP4Correlation04 (t : ℝ) : ℝ :=
  -t * (t - 2) * (t - 1) * (7 * t ^ 2 - 14 * t + 4) / 8

/-- Symmetric overlap correlation between `P2` and `P4`. -/
def factorTwoIntrinsicP4Correlation24 (t : ℝ) : ℝ :=
  -t * (t - 2) *
    (t ^ 5 + 2 * t ^ 4 - 6 * t ^ 3 - 12 * t ^ 2 + 24 * t - 8) / 16

/-- Autocorrelation of `P4`. -/
def factorTwoIntrinsicP4Correlation44 (t : ℝ) : ℝ :=
  -(t - 2) *
    (35 * t ^ 8 + 70 * t ^ 7 - 220 * t ^ 6 - 440 * t ^ 5 +
      416 * t ^ 4 + 832 * t ^ 3 - 256 * t ^ 2 - 512 * t + 128) / 1152

private theorem integral_polynomial_nine
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 +
            (a₈ * x ^ 8 + a₉ * x ^ 9))))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 +
        a₉ * (r ^ 10 - l ^ 10) / 10 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem factorTwoCenteredCorrelationBilinear_p0_p4 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredEvenP0 factorTwoCenteredP4 t =
      factorTwoIntrinsicP4Correlation04 t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredEvenP0 factorTwoCenteredP4
  simp only [one_mul, mul_one]
  rw [show (fun x : ℝ ↦ (35 * x ^ 4 - 30 * x ^ 2 + 3) / 8) =
      fun x ↦ (3 / 8 : ℝ) * x ^ 0 + (0 * x ^ 1 +
        ((-15 / 4 : ℝ) * x ^ 2 + (0 * x ^ 3 +
          ((35 / 8 : ℝ) * x ^ 4 + (0 * x ^ 5 +
            (0 * x ^ 6 + (0 * x ^ 7 + (0 * x ^ 8 + 0 * x ^ 9)))))))) by
      funext x
      ring,
    integral_polynomial_nine]
  rw [show (fun x : ℝ ↦
      (35 * (t + x) ^ 4 - 30 * (t + x) ^ 2 + 3) / 8) =
      fun x ↦ ((3 / 8 : ℝ) - 15 * t ^ 2 / 4 + 35 * t ^ 4 / 8) * x ^ 0 +
        (((-15 * t / 2 + 35 * t ^ 3 / 2 : ℝ)) * x ^ 1 +
          (((-15 / 4 : ℝ) + 105 * t ^ 2 / 4) * x ^ 2 +
            ((35 * t / 2 : ℝ) * x ^ 3 +
              ((35 / 8 : ℝ) * x ^ 4 + (0 * x ^ 5 +
                (0 * x ^ 6 + (0 * x ^ 7 + (0 * x ^ 8 + 0 * x ^ 9)))))))) by
      funext x
      ring,
    integral_polynomial_nine]
  unfold factorTwoIntrinsicP4Correlation04
  ring

theorem factorTwoCenteredCorrelationBilinear_p2_p4 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredEvenP2 factorTwoCenteredP4 t =
      factorTwoIntrinsicP4Correlation24 t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredEvenP2 factorTwoCenteredP4
  rw [show (fun x : ℝ ↦
      ((3 * (t + x) ^ 2 - 1) / 2) *
        ((35 * x ^ 4 - 30 * x ^ 2 + 3) / 8)) =
      fun x ↦ ((-3 / 16 : ℝ) + 9 * t ^ 2 / 16) * x ^ 0 +
        ((9 * t / 8 : ℝ) * x ^ 1 +
          (((39 / 16 : ℝ) - 45 * t ^ 2 / 8) * x ^ 2 +
            ((-45 * t / 4 : ℝ) * x ^ 3 +
              (((-125 / 16 : ℝ) + 105 * t ^ 2 / 16) * x ^ 4 +
                ((105 * t / 8 : ℝ) * x ^ 5 +
                  ((105 / 16 : ℝ) * x ^ 6 +
                    (0 * x ^ 7 + (0 * x ^ 8 + 0 * x ^ 9)))))))) by
      funext x
      ring,
    integral_polynomial_nine]
  rw [show (fun x : ℝ ↦
      ((35 * (t + x) ^ 4 - 30 * (t + x) ^ 2 + 3) / 8) *
        ((3 * x ^ 2 - 1) / 2)) =
      fun x ↦ ((-3 / 16 : ℝ) + 15 * t ^ 2 / 8 - 35 * t ^ 4 / 16) * x ^ 0 +
        ((15 * t / 4 - 35 * t ^ 3 / 4 : ℝ) * x ^ 1 +
          (((39 / 16 : ℝ) - 75 * t ^ 2 / 4 + 105 * t ^ 4 / 16) * x ^ 2 +
            ((-20 * t + 105 * t ^ 3 / 4 : ℝ) * x ^ 3 +
              (((-125 / 16 : ℝ) + 315 * t ^ 2 / 8) * x ^ 4 +
                ((105 * t / 4 : ℝ) * x ^ 5 +
                  ((105 / 16 : ℝ) * x ^ 6 +
                    (0 * x ^ 7 + (0 * x ^ 8 + 0 * x ^ 9)))))))) by
      funext x
      ring,
    integral_polynomial_nine]
  unfold factorTwoIntrinsicP4Correlation24
  ring

theorem centeredEndpointCorrelation_p4 (t : ℝ) :
    centeredEndpointCorrelation factorTwoCenteredP4 t =
      factorTwoIntrinsicP4Correlation44 t := by
  unfold CenteredEndpointCorrelation.centeredEndpointCorrelation
    factorTwoCenteredP4
  rw [show (fun x : ℝ ↦
      ((35 * (t + x) ^ 4 - 30 * (t + x) ^ 2 + 3) / 8) *
        ((35 * x ^ 4 - 30 * x ^ 2 + 3) / 8)) =
      fun x ↦ ((9 / 64 : ℝ) - 45 * t ^ 2 / 32 + 105 * t ^ 4 / 64) * x ^ 0 +
        ((-45 * t / 16 + 105 * t ^ 3 / 16 : ℝ) * x ^ 1 +
          (((-45 / 16 : ℝ) + 765 * t ^ 2 / 32 - 525 * t ^ 4 / 32) * x ^ 2 +
            ((555 * t / 16 - 525 * t ^ 3 / 8 : ℝ) * x ^ 3 +
              (((555 / 32 : ℝ) - 3675 * t ^ 2 / 32 + 1225 * t ^ 4 / 64) * x ^ 4 +
                ((-1575 * t / 16 + 1225 * t ^ 3 / 16 : ℝ) * x ^ 5 +
                  (((-525 / 16 : ℝ) + 3675 * t ^ 2 / 32) * x ^ 6 +
                    ((1225 * t / 16 : ℝ) * x ^ 7 +
                      ((1225 / 64 : ℝ) * x ^ 8 + 0 * x ^ 9)))))))) by
      funext x
      ring,
    integral_polynomial_nine]
  unfold factorTwoIntrinsicP4Correlation44
  ring

theorem continuous_factorTwoIntrinsicP4Correlation04 :
    Continuous factorTwoIntrinsicP4Correlation04 := by
  unfold factorTwoIntrinsicP4Correlation04
  fun_prop

theorem continuous_factorTwoIntrinsicP4Correlation24 :
    Continuous factorTwoIntrinsicP4Correlation24 := by
  unfold factorTwoIntrinsicP4Correlation24
  fun_prop

theorem continuous_factorTwoIntrinsicP4Correlation44 :
    Continuous factorTwoIntrinsicP4Correlation44 := by
  unfold factorTwoIntrinsicP4Correlation44
  fun_prop

/-! ## Orthogonal correlation moments -/

theorem factorTwoIntrinsicP4Correlation04_moments :
    (∫ t : ℝ in 0..2, factorTwoIntrinsicP4Correlation04 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * factorTwoIntrinsicP4Correlation04 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * factorTwoIntrinsicP4Correlation04 t) =
        16 / 315 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * factorTwoIntrinsicP4Correlation04 t) =
        32 / 99 := by
  constructor
  · unfold factorTwoIntrinsicP4Correlation04
    ring_nf
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    repeat rw [intervalIntegral.integral_mul_const]
    repeat rw [integral_pow]
    rw [show (fun x : ℝ ↦ -x) = fun x ↦ (-1 : ℝ) * x ^ 1 by
      funext x
      ring, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  · constructor
    · unfold factorTwoIntrinsicP4Correlation04
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · constructor
      · unfold factorTwoIntrinsicP4Correlation04
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num
      · unfold factorTwoIntrinsicP4Correlation04
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num

theorem factorTwoIntrinsicP4Correlation24_moments :
    (∫ t : ℝ in 0..2, factorTwoIntrinsicP4Correlation24 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * factorTwoIntrinsicP4Correlation24 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * factorTwoIntrinsicP4Correlation24 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * factorTwoIntrinsicP4Correlation24 t) =
        32 / 315 := by
  constructor
  · unfold factorTwoIntrinsicP4Correlation24
    ring_nf
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    repeat rw [intervalIntegral.integral_mul_const]
    repeat rw [integral_pow]
    rw [show (fun x : ℝ ↦ -x) = fun x ↦ (-1 : ℝ) * x ^ 1 by
      funext x
      ring, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  · constructor
    · unfold factorTwoIntrinsicP4Correlation24
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · constructor
      · unfold factorTwoIntrinsicP4Correlation24
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num
      · unfold factorTwoIntrinsicP4Correlation24
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num

theorem factorTwoIntrinsicP4Correlation44_moments :
    (∫ t : ℝ in 0..2, factorTwoIntrinsicP4Correlation44 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * factorTwoIntrinsicP4Correlation44 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * factorTwoIntrinsicP4Correlation44 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * factorTwoIntrinsicP4Correlation44 t) = 0 := by
  constructor
  · unfold factorTwoIntrinsicP4Correlation44
    ring_nf
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    repeat rw [intervalIntegral.integral_mul_const]
    repeat rw [integral_pow]
    rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2),
      intervalIntegral.integral_const,
      show (fun x : ℝ ↦ x) = fun x ↦ (1 : ℝ) * x ^ 1 by
        funext x
        ring,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  · constructor
    · unfold factorTwoIntrinsicP4Correlation44
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · constructor
      · unfold factorTwoIntrinsicP4Correlation44
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num
      · unfold factorTwoIntrinsicP4Correlation44
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
