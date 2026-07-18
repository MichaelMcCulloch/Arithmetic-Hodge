import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP7EndpointUpperStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCenteredP9Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoStructuralConstantBounds

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP7P9CorrelationStructural

noncomputable section

open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoStructuralConstantBounds

/-!
# Structural `P7/P9` endpoint correlation

The first retained/omitted odd pair has an exact polynomial centered
correlation.  Its reflected Cauchy quotient is again a polynomial, while a
short displacement estimate from `7/6` fixes the sign of the retained
prime atom.  No sampled or floating-point inequality enters these results.
-/

def factorTwoP7P9Correlation (t : ℝ) : ℝ :=
  -t + (17 / 2 : ℝ) * t ^ 2 - 18 * t ^ 3 +
    (105 / 4 : ℝ) * t ^ 5 - (231 / 8 : ℝ) * t ^ 7 +
    (2475 / 128 : ℝ) * t ^ 9 - (1001 / 128 : ℝ) * t ^ 11 +
    (1911 / 1024 : ℝ) * t ^ 13 - (495 / 2048 : ℝ) * t ^ 15 +
    (429 / 32768 : ℝ) * t ^ 17

def factorTwoP7P9ReflectedQuotient (t : ℝ) : ℝ :=
  (-1 / 2 : ℝ) * t ^ 1 + 4 * t ^ 2 - 7 * t ^ 3 -
    (7 / 2 : ℝ) * t ^ 4 + (91 / 8 : ℝ) * t ^ 5 +
    (91 / 16 : ℝ) * t ^ 6 - (371 / 32 : ℝ) * t ^ 7 -
    (371 / 64 : ℝ) * t ^ 8 + (1733 / 256 : ℝ) * t ^ 9 +
    (1733 / 512 : ℝ) * t ^ 10 - (2271 / 1024 : ℝ) * t ^ 11 -
    (2271 / 2048 : ℝ) * t ^ 12 + (1551 / 4096 : ℝ) * t ^ 13 +
    (1551 / 8192 : ℝ) * t ^ 14 - (429 / 16384 : ℝ) * t ^ 15 -
    (429 / 32768 : ℝ) * t ^ 16

private theorem integral_polynomial_sixteen
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
        a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 + a₁₁ * x ^ 11 +
        a₁₂ * x ^ 12 + a₁₃ * x ^ 13 + a₁₄ * x ^ 14 +
        a₁₅ * x ^ 15 + a₁₆ * x ^ 16) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 +
        a₁₂ * (r ^ 13 - l ^ 13) / 13 +
        a₁₃ * (r ^ 14 - l ^ 14) / 14 +
        a₁₄ * (r ^ 15 - l ^ 15) / 15 +
        a₁₅ * (r ^ 16 - l ^ 16) / 16 +
        a₁₆ * (r ^ 17 - l ^ 17) / 17 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

set_option maxHeartbeats 800000 in
/-- Exact centered bilinear correlation of `P7` and `P9`. -/
theorem factorTwoCenteredCorrelationBilinear_P7_P9 (t : ℝ) :
    factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 t =
      factorTwoP7P9Correlation t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_swap_of_odd_odd
    odd_factorTwoCenteredP7 odd_factorTwoCenteredP9]
  ring_nf
  unfold factorTwoCenteredCrossCorrelation
  simp_rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  rw [show (fun x : ℝ ↦
      ((429 * (t + x) ^ 7 - 693 * (t + x) ^ 5 +
          315 * (t + x) ^ 3 - 35 * (t + x)) / 16) *
        ((12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
          4620 * x ^ 3 + 315 * x) / 128)) =
      fun x ↦
        0 * x ^ 0 +
        ((135135 / 2048 : ℝ) * t ^ 7 - (218295 / 2048 : ℝ) * t ^ 5 +
          (99225 / 2048 : ℝ) * t ^ 3 - (11025 / 2048 : ℝ) * t) * x ^ 1 +
        ((945945 / 2048 : ℝ) * t ^ 6 - (1091475 / 2048 : ℝ) * t ^ 4 +
          (297675 / 2048 : ℝ) * t ^ 2 - (11025 / 2048 : ℝ)) * x ^ 2 +
        (-(495495 / 512 : ℝ) * t ^ 7 + (6039495 / 2048 : ℝ) * t ^ 5 -
          (1819125 / 1024 : ℝ) * t ^ 3 + (459375 / 2048 : ℝ) * t) * x ^ 3 +
        (-(3468465 / 512 : ℝ) * t ^ 6 + (20738025 / 2048 : ℝ) * t ^ 4 -
          (3274425 / 1024 : ℝ) * t ^ 2 + (260925 / 2048 : ℝ)) * x ^ 4 +
        ((3864861 / 1024 : ℝ) * t ^ 7 - (27054027 / 1024 : ℝ) * t ^ 5 +
          (42421995 / 2048 : ℝ) * t ^ 3 - (6088005 / 2048 : ℝ) * t) * x ^ 5 +
        ((27054027 / 1024 : ℝ) * t ^ 6 - (65900835 / 1024 : ℝ) * t ^ 4 +
          (51881445 / 2048 : ℝ) * t ^ 2 - (2304225 / 2048 : ℝ)) * x ^ 6 +
        (-(2760615 / 512 : ℝ) * t ^ 7 + (90080991 / 1024 : ℝ) * t ^ 5 -
          (50585535 / 512 : ℝ) * t ^ 3 + (34882155 / 2048 : ℝ) * t) * x ^ 7 +
        (-(19324305 / 512 : ℝ) * t ^ 6 + (179864685 / 1024 : ℝ) * t ^ 4 -
          (47702655 / 512 : ℝ) * t ^ 2 + (9913365 / 2048 : ℝ)) * x ^ 8 +
        ((5214495 / 2048 : ℝ) * t ^ 7 - (240315075 / 2048 : ℝ) * t ^ 5 +
          (452747295 / 2048 : ℝ) * t ^ 3 - (101055955 / 2048 : ℝ) * t) * x ^ 9 +
        ((36501465 / 2048 : ℝ) * t ^ 6 - (428603175 / 2048 : ℝ) * t ^ 4 +
          (352188837 / 2048 : ℝ) * t ^ 2 - (23001979 / 2048 : ℝ)) * x ^ 10 +
        ((109504395 / 2048 : ℝ) * t ^ 5 - (235360125 / 1024 : ℝ) * t ^ 3 +
          (154783629 / 2048 : ℝ) * t) * x ^ 11 +
        ((182507325 / 2048 : ℝ) * t ^ 4 - (158062905 / 1024 : ℝ) * t ^ 2 +
          (29396367 / 2048 : ℝ)) * x ^ 12 +
        ((182507325 / 2048 : ℝ) * t ^ 3 - (119414295 / 2048 : ℝ) * t) * x ^ 13 +
        ((109504395 / 2048 : ℝ) * t ^ 2 - (19465875 / 2048 : ℝ)) * x ^ 14 +
        ((36501465 / 2048 : ℝ) * t) * x ^ 15 +
        (5214495 / 2048 : ℝ) * x ^ 16 by
      funext x
      ring,
    integral_polynomial_sixteen]
  unfold factorTwoP7P9Correlation
  ring

/-- The endpoint zero is exact, so the reflected quotient is polynomial. -/
theorem factorTwoP7P9Correlation_factor (t : ℝ) :
    factorTwoP7P9Correlation t =
      (2 - t) * factorTwoP7P9ReflectedQuotient t := by
  unfold factorTwoP7P9Correlation factorTwoP7P9ReflectedQuotient
  ring

theorem integral_factorTwoP7P9ReflectedQuotient :
    (∫ t : ℝ in 0..2, factorTwoP7P9ReflectedQuotient t) =
      -(41381 / 3063060 : ℝ) := by
  rw [show factorTwoP7P9ReflectedQuotient = fun t : ℝ ↦
      0 * t ^ 0 + (-1 / 2 : ℝ) * t ^ 1 + 4 * t ^ 2 +
        (-7) * t ^ 3 + (-7 / 2 : ℝ) * t ^ 4 +
        (91 / 8 : ℝ) * t ^ 5 + (91 / 16 : ℝ) * t ^ 6 +
        (-371 / 32 : ℝ) * t ^ 7 + (-371 / 64 : ℝ) * t ^ 8 +
        (1733 / 256 : ℝ) * t ^ 9 + (1733 / 512 : ℝ) * t ^ 10 +
        (-2271 / 1024 : ℝ) * t ^ 11 + (-2271 / 2048 : ℝ) * t ^ 12 +
        (1551 / 4096 : ℝ) * t ^ 13 + (1551 / 8192 : ℝ) * t ^ 14 +
        (-429 / 16384 : ℝ) * t ^ 15 + (-429 / 32768 : ℝ) * t ^ 16 by
      funext t
      unfold factorTwoP7P9ReflectedQuotient
      ring,
    integral_polynomial_sixteen]
  norm_num

theorem integral_factorTwoP7P9Correlation_div_two_sub :
    (∫ t : ℝ in 0..2, factorTwoP7P9Correlation t / (2 - t)) =
      -(41381 / 3063060 : ℝ) := by
  rw [show (∫ t : ℝ in 0..2,
      factorTwoP7P9Correlation t / (2 - t)) =
      ∫ t : ℝ in 0..2, factorTwoP7P9ReflectedQuotient t by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht
    intro _ht
    have hden : 2 - t ≠ 0 := sub_ne_zero.mpr ht.symm
    rw [factorTwoP7P9Correlation_factor]
    field_simp]
  exact integral_factorTwoP7P9ReflectedQuotient

/-- Exact reflected singular integral for the structural pair. -/
theorem integral_factorTwoCenteredCorrelationBilinear_P7_P9_div_two_sub :
    (∫ t : ℝ in 0..2,
        factorTwoCenteredCorrelationBilinear
          factorTwoCenteredP7 factorTwoCenteredP9 t / (2 - t)) =
      -(41381 / 3063060 : ℝ) := by
  rw [show (fun t : ℝ ↦
      factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 t / (2 - t)) =
      fun t ↦ factorTwoP7P9Correlation t / (2 - t) by
    funext t
    rw [factorTwoCenteredCorrelationBilinear_P7_P9]]
  exact integral_factorTwoP7P9Correlation_div_two_sub

theorem factorTwoP7P9_reflected_contribution_exact :
    -(1 / 2 : ℝ) *
        (∫ t : ℝ in 0..2, factorTwoP7P9Correlation t / (2 - t)) =
      41381 / 6126120 := by
  rw [integral_factorTwoP7P9Correlation_div_two_sub]
  norm_num

theorem factorTwoP7P9_reflected_contribution_gt_one_over_150 :
    (1 / 150 : ℝ) <
      -(1 / 2 : ℝ) *
        (∫ t : ℝ in 0..2,
          factorTwoP7P9Correlation t / (2 - t)) := by
  rw [factorTwoP7P9_reflected_contribution_exact]
  norm_num

private theorem factorTwoP7P9Correlation_shift_seven_sixths_le
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    factorTwoP7P9Correlation ((7 / 6 : ℝ) + d) -
        factorTwoP7P9Correlation (7 / 6 : ℝ) ≤ 200 * d ^ 2 := by
  have hpow (n : ℕ) (hn : 2 ≤ n) : d ^ n ≤ d ^ 2 := by
    calc
      d ^ n = d ^ 2 * d ^ (n - 2) := by
        rw [← pow_add, Nat.add_sub_of_le hn]
      _ ≤ d ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hd0 hd1) (sq_nonneg d)
      _ = d ^ 2 := by ring
  have h3 := hpow 3 (by omega)
  have h7 := hpow 7 (by omega)
  have h8 := hpow 8 (by omega)
  have h12 := hpow 12 (by omega)
  have h13 := hpow 13 (by omega)
  have h14 := hpow 14 (by omega)
  have h15 := hpow 15 (by omega)
  have h16 := hpow 16 (by omega)
  have h17 := hpow 17 (by omega)
  have hn4 : 0 ≤ d ^ 4 := pow_nonneg hd0 4
  have hn5 : 0 ≤ d ^ 5 := pow_nonneg hd0 5
  have hn6 : 0 ≤ d ^ 6 := pow_nonneg hd0 6
  have hn9 : 0 ≤ d ^ 9 := pow_nonneg hd0 9
  have hn10 : 0 ≤ d ^ 10 := pow_nonneg hd0 10
  have hn11 : 0 ≤ d ^ 11 := pow_nonneg hd0 11
  unfold factorTwoP7P9Correlation
  ring_nf
  nlinarith

/-- The exact prime lag lies in a sign-stable neighborhood of `7/6`. -/
theorem factorTwoP7P9Correlation_primeRatio_neg :
    factorTwoP7P9Correlation
        (YoshidaFactorTwoCenteredPhysical.factorTwoPrimeShift /
          YoshidaEndpointHyperbolicBound.yoshidaEndpointA) < 0 := by
  let tau : ℝ := YoshidaFactorTwoCenteredPhysical.factorTwoPrimeShift /
    YoshidaEndpointHyperbolicBound.yoshidaEndpointA
  let d : ℝ := tau - 7 / 6
  have htau := factorTwoPrimeLag_bounds
  have hd0 : 0 ≤ d := by
    dsimp only [d, tau]
    linarith [htau.1]
  have hdSmall : d < 1 / 300 := by
    dsimp only [d, tau]
    linarith [htau.2]
  have hd1 : d ≤ 1 := by linarith
  have hshift := factorTwoP7P9Correlation_shift_seven_sixths_le hd0 hd1
  have hcenter :
      factorTwoP7P9Correlation (7 / 6 : ℝ) < -(1 / 250 : ℝ) := by
    norm_num [factorTwoP7P9Correlation]
  have hdsq : d ^ 2 < (1 / 300 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hdSmall hd0 (by norm_num)
  change factorTwoP7P9Correlation tau < 0
  have htauEq : tau = (7 / 6 : ℝ) + d := by
    dsimp only [d]
    ring
  rw [htauEq]
  nlinarith

theorem factorTwoCenteredCorrelationBilinear_P7_P9_primeRatio_neg :
    factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP7 factorTwoCenteredP9
        (YoshidaFactorTwoCenteredPhysical.factorTwoPrimeShift /
          YoshidaEndpointHyperbolicBound.yoshidaEndpointA) < 0 := by
  rw [factorTwoCenteredCorrelationBilinear_P7_P9]
  exact factorTwoP7P9Correlation_primeRatio_neg

/-- The retained `p = 3` mixed atom has the favorable sign. -/
theorem factorTwoP7P9_prime_mixed_contribution_nonnegative :
    0 ≤ -(Real.log 3 / Real.sqrt 3) *
      factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP7 factorTwoCenteredP9
        (YoshidaFactorTwoCenteredPhysical.factorTwoPrimeShift /
          YoshidaEndpointHyperbolicBound.yoshidaEndpointA) := by
  have hcorr := factorTwoCenteredCorrelationBilinear_P7_P9_primeRatio_neg
  have hcoeff : 0 < Real.log 3 / Real.sqrt 3 := by
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP7P9CorrelationStructural
