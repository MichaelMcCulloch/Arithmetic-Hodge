import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural

noncomputable section

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseLegendreFourFiveStructural

/-!
# Exact odd low-to-`P5` correlations

These identities are obtained by integrating the two symmetric overlap
polynomials exactly.  They are independent of every analytic kernel bound.
-/

/-- Exact symmetric overlap correlation between `P1` and `P5`. -/
def oddP5Correlation15 (t : ℝ) : ℝ :=
  -t + 7 * t ^ 2 - 15 * t ^ 3 + (105 / 8 : ℝ) * t ^ 4 -
    (35 / 8 : ℝ) * t ^ 5 + (3 / 16 : ℝ) * t ^ 7

/-- Exact symmetric overlap correlation between `P3` and `P5`. -/
def oddP5Correlation35 (t : ℝ) : ℝ :=
  -t + (9 / 2 : ℝ) * t ^ 2 - 5 * t ^ 3 +
    (15 / 8 : ℝ) * t ^ 5 - (7 / 16 : ℝ) * t ^ 7 +
    (5 / 128 : ℝ) * t ^ 9

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

theorem factorTwoCenteredCorrelationBilinear_p1_p5 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP1 factorTwoCenteredP5 t =
      oddP5Correlation15 t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredP1 factorTwoCenteredP5
  rw [show (fun x : ℝ ↦ (t + x) *
      ((63 * x ^ 5 - 70 * x ^ 3 + 15 * x) / 8)) =
      fun x ↦ 0 * x ^ 0 + ((15 * t / 8 : ℝ) * x ^ 1 +
        ((15 / 8 : ℝ) * x ^ 2 + ((-35 * t / 4 : ℝ) * x ^ 3 +
          ((-35 / 4 : ℝ) * x ^ 4 + ((63 * t / 8 : ℝ) * x ^ 5 +
            ((63 / 8 : ℝ) * x ^ 6 + (0 * x ^ 7 +
              (0 * x ^ 8 + 0 * x ^ 9)))))))) by
      funext x
      ring,
    integral_polynomial_nine]
  rw [show (fun x : ℝ ↦
      ((63 * (t + x) ^ 5 - 70 * (t + x) ^ 3 + 15 * (t + x)) / 8) * x) =
      fun x ↦ 0 * x ^ 0 +
        ((15 * t / 8 - 35 * t ^ 3 / 4 + 63 * t ^ 5 / 8 : ℝ) * x ^ 1 +
          ((15 / 8 - 105 * t ^ 2 / 4 + 315 * t ^ 4 / 8 : ℝ) * x ^ 2 +
            ((-105 * t / 4 + 315 * t ^ 3 / 4 : ℝ) * x ^ 3 +
              ((-35 / 4 + 315 * t ^ 2 / 4 : ℝ) * x ^ 4 +
                ((315 * t / 8 : ℝ) * x ^ 5 +
                  ((63 / 8 : ℝ) * x ^ 6 + (0 * x ^ 7 +
                    (0 * x ^ 8 + 0 * x ^ 9)))))))) by
      funext x
      ring,
    integral_polynomial_nine]
  unfold oddP5Correlation15
  ring

theorem factorTwoCenteredCorrelationBilinear_p3_p5 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP3 factorTwoCenteredP5 t =
      oddP5Correlation35 t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredP3 factorTwoCenteredP5
  rw [show (fun x : ℝ ↦ ((5 * (t + x) ^ 3 - 3 * (t + x)) / 2) *
      ((63 * x ^ 5 - 70 * x ^ 3 + 15 * x) / 8)) =
      fun x ↦ 0 * x ^ 0 +
        ((-45 * t / 16 + 75 * t ^ 3 / 16 : ℝ) * x ^ 1 +
          ((-45 / 16 + 225 * t ^ 2 / 16 : ℝ) * x ^ 2 +
            ((435 * t / 16 - 175 * t ^ 3 / 8 : ℝ) * x ^ 3 +
              ((285 / 16 - 525 * t ^ 2 / 8 : ℝ) * x ^ 4 +
                ((-1239 * t / 16 + 315 * t ^ 3 / 16 : ℝ) * x ^ 5 +
                  ((-539 / 16 + 945 * t ^ 2 / 16 : ℝ) * x ^ 6 +
                    ((945 * t / 16 : ℝ) * x ^ 7 +
                      ((315 / 16 : ℝ) * x ^ 8 + 0 * x ^ 9)))))))) by
      funext x
      ring,
    integral_polynomial_nine]
  rw [show (fun x : ℝ ↦
      ((63 * (t + x) ^ 5 - 70 * (t + x) ^ 3 + 15 * (t + x)) / 8) *
        ((5 * x ^ 3 - 3 * x) / 2)) =
      fun x ↦ 0 * x ^ 0 +
        ((-45 * t / 16 + 105 * t ^ 3 / 8 - 189 * t ^ 5 / 16 : ℝ) * x ^ 1 +
          ((-45 / 16 + 315 * t ^ 2 / 8 - 945 * t ^ 4 / 16 : ℝ) * x ^ 2 +
            ((705 * t / 16 - 140 * t ^ 3 + 315 * t ^ 5 / 16 : ℝ) * x ^ 3 +
              ((285 / 16 - 735 * t ^ 2 / 4 + 1575 * t ^ 4 / 16 : ℝ) * x ^ 4 +
                ((-1995 * t / 16 + 1575 * t ^ 3 / 8 : ℝ) * x ^ 5 +
                  ((-539 / 16 + 1575 * t ^ 2 / 8 : ℝ) * x ^ 6 +
                    ((1575 * t / 16 : ℝ) * x ^ 7 +
                      ((315 / 16 : ℝ) * x ^ 8 + 0 * x ^ 9)))))))) by
      funext x
      ring,
    integral_polynomial_nine]
  unfold oddP5Correlation35
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
