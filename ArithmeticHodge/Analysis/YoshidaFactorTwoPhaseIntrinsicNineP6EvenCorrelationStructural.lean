import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenCorrelationStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointEvenStructuralReduction
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

/-!
# Structural correlations for the intrinsic `P6` mode

The four correlations below are the exact overlap polynomials coupling `P6`
to the retained even modes `P0`, `P2`, `P4`, and `P6`.  Their proofs use only
exact polynomial integration; there is no sampling, quadrature, or numerical
certificate.
-/

/-- Symmetric overlap correlation between `P0` and `P6`. -/
def factorTwoIntrinsicP6Correlation06 (t : ℝ) : ℝ :=
  -t * (t - 2) * (t - 1) *
    (33 * t ^ 4 - 132 * t ^ 3 + 168 * t ^ 2 - 72 * t + 8) / 16

/-- Symmetric overlap correlation between `P2` and `P6`. -/
def factorTwoIntrinsicP6Correlation26 (t : ℝ) : ℝ :=
  -t * (t - 2) *
    (11 * t ^ 7 + 22 * t ^ 6 - 124 * t ^ 5 - 248 * t ^ 4 +
      1184 * t ^ 3 - 1328 * t ^ 2 + 544 * t - 64) / 128

/-- Symmetric overlap correlation between `P4` and `P6`. -/
def factorTwoIntrinsicP6Correlation46 (t : ℝ) : ℝ :=
  -t * (t - 2) *
    (7 * t ^ 9 + 14 * t ^ 8 - 62 * t ^ 7 - 124 * t ^ 6 +
      200 * t ^ 5 + 400 * t ^ 4 - 320 * t ^ 3 - 640 * t ^ 2 +
      640 * t - 128) / 256

/-- Autocorrelation of `P6`. -/
def factorTwoIntrinsicP6Correlation66 (t : ℝ) : ℝ :=
  -(t - 2) *
    (231 * t ^ 12 + 462 * t ^ 11 - 2352 * t ^ 10 - 4704 * t ^ 9 +
      8792 * t ^ 8 + 17584 * t ^ 7 - 14752 * t ^ 6 - 29504 * t ^ 5 +
      10880 * t ^ 4 + 21760 * t ^ 3 - 3072 * t ^ 2 - 6144 * t + 1024) /
    13312

private theorem integral_polynomial_twelve
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
        a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 + a₁₁ * x ^ 11 +
        a₁₂ * x ^ 12) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 +
        a₁₂ * (r ^ 13 - l ^ 13) / 13 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem factorTwoCenteredCorrelationBilinear_p0_p6 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredEvenP0 factorTwoCenteredP6 t =
      factorTwoIntrinsicP6Correlation06 t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation centeredEvenP0
  simp only [one_mul, mul_one]
  rw [show (fun x : ℝ ↦ factorTwoCenteredP6 x) =
      fun x ↦ (-5 / 16 : ℝ) * x ^ 0 + 0 * x ^ 1 +
        (105 / 16 : ℝ) * x ^ 2 + 0 * x ^ 3 +
        (-315 / 16 : ℝ) * x ^ 4 + 0 * x ^ 5 +
        (231 / 16 : ℝ) * x ^ 6 + 0 * x ^ 7 + 0 * x ^ 8 +
        0 * x ^ 9 + 0 * x ^ 10 + 0 * x ^ 11 + 0 * x ^ 12 by
      funext x
      rw [factorTwoCenteredP6_eq]
      ring,
    integral_polynomial_twelve]
  rw [show (fun x : ℝ ↦ factorTwoCenteredP6 (t + x)) =
      fun x ↦
        (231 * t ^ 6 / 16 - 315 * t ^ 4 / 16 + 105 * t ^ 2 / 16 - 5 / 16) *
            x ^ 0 +
        (693 * t ^ 5 / 8 - 315 * t ^ 3 / 4 + 105 * t / 8) * x ^ 1 +
        (3465 * t ^ 4 / 16 - 945 * t ^ 2 / 8 + 105 / 16) * x ^ 2 +
        (1155 * t ^ 3 / 4 - 315 * t / 4) * x ^ 3 +
        (3465 * t ^ 2 / 16 - 315 / 16) * x ^ 4 +
        (693 * t / 8) * x ^ 5 + (231 / 16 : ℝ) * x ^ 6 +
        0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 +
        0 * x ^ 11 + 0 * x ^ 12 by
      funext x
      rw [factorTwoCenteredP6_eq]
      ring,
    integral_polynomial_twelve]
  unfold factorTwoIntrinsicP6Correlation06
  ring

theorem factorTwoCenteredCorrelationBilinear_p2_p6 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredEvenP2 factorTwoCenteredP6 t =
      factorTwoIntrinsicP6Correlation26 t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation
  rw [show (fun x : ℝ ↦ centeredEvenP2 (t + x) * factorTwoCenteredP6 x) =
      fun x ↦
        (5 / 32 - 15 * t ^ 2 / 32 : ℝ) * x ^ 0 +
        (-15 * t / 16) * x ^ 1 +
        (315 * t ^ 2 / 32 - 15 / 4) * x ^ 2 +
        (315 * t / 16) * x ^ 3 +
        (315 / 16 - 945 * t ^ 2 / 32) * x ^ 4 +
        (-945 * t / 16) * x ^ 5 +
        (693 * t ^ 2 / 32 - 147 / 4) * x ^ 6 +
        (693 * t / 16) * x ^ 7 + (693 / 32 : ℝ) * x ^ 8 +
        0 * x ^ 9 + 0 * x ^ 10 + 0 * x ^ 11 + 0 * x ^ 12 by
      funext x
      unfold centeredEvenP2
      rw [factorTwoCenteredP6_eq]
      ring,
    integral_polynomial_twelve]
  rw [show (fun x : ℝ ↦ factorTwoCenteredP6 (t + x) * centeredEvenP2 x) =
      fun x ↦
        (-231 * t ^ 6 / 32 + 315 * t ^ 4 / 32 - 105 * t ^ 2 / 32 +
          5 / 32) * x ^ 0 +
        (-693 * t ^ 5 / 16 + 315 * t ^ 3 / 8 - 105 * t / 16) * x ^ 1 +
        (693 * t ^ 6 / 32 - 2205 * t ^ 4 / 16 + 2205 * t ^ 2 / 32 -
          15 / 4) * x ^ 2 +
        (2079 * t ^ 5 / 16 - 525 * t ^ 3 / 2 + 945 * t / 16) * x ^ 3 +
        (10395 * t ^ 4 / 32 - 9135 * t ^ 2 / 32 + 315 / 16) * x ^ 4 +
        (3465 * t ^ 3 / 8 - 2583 * t / 16) * x ^ 5 +
        (10395 * t ^ 2 / 32 - 147 / 4) * x ^ 6 +
        (2079 * t / 16) * x ^ 7 + (693 / 32 : ℝ) * x ^ 8 +
        0 * x ^ 9 + 0 * x ^ 10 + 0 * x ^ 11 + 0 * x ^ 12 by
      funext x
      unfold centeredEvenP2
      rw [factorTwoCenteredP6_eq]
      ring,
    integral_polynomial_twelve]
  unfold factorTwoIntrinsicP6Correlation26
  ring

theorem factorTwoCenteredCorrelationBilinear_p4_p6 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear factorTwoCenteredP4 factorTwoCenteredP6 t =
      factorTwoIntrinsicP6Correlation46 t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation
  rw [show (fun x : ℝ ↦ factorTwoCenteredP4 (t + x) * factorTwoCenteredP6 x) =
      fun x ↦
        (-175 * t ^ 4 / 128 + 75 * t ^ 2 / 64 - 15 / 128) * x ^ 0 +
        (-175 * t ^ 3 / 32 + 75 * t / 32) * x ^ 1 +
        (3675 * t ^ 4 / 128 - 525 * t ^ 2 / 16 + 465 / 128) * x ^ 2 +
        (3675 * t ^ 3 / 32 - 875 * t / 16) * x ^ 3 +
        (-11025 * t ^ 4 / 128 + 7875 * t ^ 2 / 32 - 2135 / 64) * x ^ 4 +
        (-11025 * t ^ 3 / 32 + 525 * t / 2) * x ^ 5 +
        (8085 * t ^ 4 / 128 - 9135 * t ^ 2 / 16 + 6909 / 64) * x ^ 6 +
        (8085 * t ^ 3 / 32 - 7245 * t / 16) * x ^ 7 +
        (24255 * t ^ 2 / 64 - 17955 / 128) * x ^ 8 +
        (8085 * t / 32) * x ^ 9 + (8085 / 128 : ℝ) * x ^ 10 +
        0 * x ^ 11 + 0 * x ^ 12 by
      funext x
      unfold factorTwoCenteredP4
      rw [factorTwoCenteredP6_eq]
      ring,
    integral_polynomial_twelve]
  rw [show (fun x : ℝ ↦ factorTwoCenteredP6 (t + x) * factorTwoCenteredP4 x) =
      fun x ↦
        (693 * t ^ 6 / 128 - 945 * t ^ 4 / 128 + 315 * t ^ 2 / 128 -
          15 / 128) * x ^ 0 +
        (2079 * t ^ 5 / 64 - 945 * t ^ 3 / 32 + 315 * t / 64) * x ^ 1 +
        (-3465 * t ^ 6 / 64 + 19845 * t ^ 4 / 128 - 2205 * t ^ 2 / 32 +
          465 / 128) * x ^ 2 +
        (-10395 * t ^ 5 / 32 + 12915 * t ^ 3 / 32 - 315 * t / 4) * x ^ 3 +
        (8085 * t ^ 6 / 128 - 114975 * t ^ 4 / 128 + 35385 * t ^ 2 / 64 -
          2135 / 64) * x ^ 4 +
        (24255 * t ^ 5 / 64 - 45675 * t ^ 3 / 32 + 12327 * t / 32) * x ^ 5 +
        (121275 * t ^ 4 / 128 - 42525 * t ^ 2 / 32 + 6909 / 64) * x ^ 6 +
        (40425 * t ^ 3 / 32 - 5355 * t / 8) * x ^ 7 +
        (121275 * t ^ 2 / 128 - 17955 / 128) * x ^ 8 +
        (24255 * t / 64) * x ^ 9 + (8085 / 128 : ℝ) * x ^ 10 +
        0 * x ^ 11 + 0 * x ^ 12 by
      funext x
      unfold factorTwoCenteredP4
      rw [factorTwoCenteredP6_eq]
      ring,
    integral_polynomial_twelve]
  unfold factorTwoIntrinsicP6Correlation46
  ring

theorem centeredEndpointCorrelation_p6 (t : ℝ) :
    centeredEndpointCorrelation factorTwoCenteredP6 t =
      factorTwoIntrinsicP6Correlation66 t := by
  unfold CenteredEndpointCorrelation.centeredEndpointCorrelation
  rw [show (fun x : ℝ ↦ factorTwoCenteredP6 (t + x) * factorTwoCenteredP6 x) =
      fun x ↦
        (-1155 * t ^ 6 / 256 + 1575 * t ^ 4 / 256 - 525 * t ^ 2 / 256 +
          25 / 256) * x ^ 0 +
        (-3465 * t ^ 5 / 128 + 1575 * t ^ 3 / 64 - 525 * t / 128) * x ^ 1 +
        (24255 * t ^ 6 / 256 - 1575 * t ^ 4 / 8 + 20475 * t ^ 2 / 256 -
          525 / 128) * x ^ 2 +
        (72765 * t ^ 5 / 128 - 19425 * t ^ 3 / 32 + 14175 * t / 128) * x ^ 3 +
        (-72765 * t ^ 6 / 256 + 231525 * t ^ 4 / 128 - 124425 * t ^ 2 / 128 +
          14175 / 256) * x ^ 4 +
        (-218295 * t ^ 5 / 128 + 55125 * t ^ 3 / 16 - 51345 * t / 64) * x ^ 5 +
        (53361 * t ^ 6 / 256 - 72765 * t ^ 4 / 16 + 491715 * t ^ 2 / 128 -
          17115 / 64) * x ^ 6 +
        (160083 * t ^ 5 / 128 - 218295 * t ^ 3 / 32 + 147735 * t / 64) * x ^ 7 +
        (800415 * t ^ 4 / 256 - 1528065 * t ^ 2 / 256 + 147735 / 256) * x ^ 8 +
        (266805 * t ^ 3 / 64 - 363825 * t / 128) * x ^ 9 +
        (800415 * t ^ 2 / 256 - 72765 / 128) * x ^ 10 +
        (160083 * t / 128) * x ^ 11 + (53361 / 256 : ℝ) * x ^ 12 by
      funext x
      rw [factorTwoCenteredP6_eq, factorTwoCenteredP6_eq]
      ring,
    integral_polynomial_twelve]
  unfold factorTwoIntrinsicP6Correlation66
  ring

theorem factorTwoCenteredCorrelationBilinear_p6_p6 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear factorTwoCenteredP6 factorTwoCenteredP6 t =
      factorTwoIntrinsicP6Correlation66 t := by
  rw [factorTwoCenteredCorrelationBilinear_self, centeredEndpointCorrelation_p6]

theorem continuous_factorTwoIntrinsicP6Correlation06 :
    Continuous factorTwoIntrinsicP6Correlation06 := by
  unfold factorTwoIntrinsicP6Correlation06
  fun_prop

theorem continuous_factorTwoIntrinsicP6Correlation26 :
    Continuous factorTwoIntrinsicP6Correlation26 := by
  unfold factorTwoIntrinsicP6Correlation26
  fun_prop

theorem continuous_factorTwoIntrinsicP6Correlation46 :
    Continuous factorTwoIntrinsicP6Correlation46 := by
  unfold factorTwoIntrinsicP6Correlation46
  fun_prop

theorem continuous_factorTwoIntrinsicP6Correlation66 :
    Continuous factorTwoIntrinsicP6Correlation66 := by
  unfold factorTwoIntrinsicP6Correlation66
  fun_prop

/-! ## Orthogonal correlation moments -/

theorem factorTwoIntrinsicP6Correlation06_moments :
    (∫ t : ℝ in 0..2, factorTwoIntrinsicP6Correlation06 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * factorTwoIntrinsicP6Correlation06 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * factorTwoIntrinsicP6Correlation06 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * factorTwoIntrinsicP6Correlation06 t) =
        32 / 3003 := by
  constructor
  · unfold factorTwoIntrinsicP6Correlation06
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
    · unfold factorTwoIntrinsicP6Correlation06
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · constructor
      · unfold factorTwoIntrinsicP6Correlation06
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num
      · unfold factorTwoIntrinsicP6Correlation06
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num

theorem factorTwoIntrinsicP6Correlation26_moments :
    (∫ t : ℝ in 0..2, factorTwoIntrinsicP6Correlation26 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * factorTwoIntrinsicP6Correlation26 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * factorTwoIntrinsicP6Correlation26 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * factorTwoIntrinsicP6Correlation26 t) = 0 := by
  constructor
  · unfold factorTwoIntrinsicP6Correlation26
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
    · unfold factorTwoIntrinsicP6Correlation26
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · constructor
      · unfold factorTwoIntrinsicP6Correlation26
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num
      · unfold factorTwoIntrinsicP6Correlation26
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num

theorem factorTwoIntrinsicP6Correlation46_moments :
    (∫ t : ℝ in 0..2, factorTwoIntrinsicP6Correlation46 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * factorTwoIntrinsicP6Correlation46 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * factorTwoIntrinsicP6Correlation46 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * factorTwoIntrinsicP6Correlation46 t) = 0 := by
  constructor
  · unfold factorTwoIntrinsicP6Correlation46
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
    · unfold factorTwoIntrinsicP6Correlation46
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · constructor
      · unfold factorTwoIntrinsicP6Correlation46
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num
      · unfold factorTwoIntrinsicP6Correlation46
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num

theorem factorTwoIntrinsicP6Correlation66_moments :
    (∫ t : ℝ in 0..2, factorTwoIntrinsicP6Correlation66 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * factorTwoIntrinsicP6Correlation66 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * factorTwoIntrinsicP6Correlation66 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * factorTwoIntrinsicP6Correlation66 t) = 0 := by
  constructor
  · unfold factorTwoIntrinsicP6Correlation66
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
    · unfold factorTwoIntrinsicP6Correlation66
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · constructor
      · unfold factorTwoIntrinsicP6Correlation66
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num
      · unfold factorTwoIntrinsicP6Correlation66
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenCorrelationStructural
