import ArithmeticHodge.Analysis.RationalIntervalWidth
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
set_option maxRecDepth 100000

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaPositiveLogEnclosures

noncomputable section

open RatInterval

/-!
# Positive logarithm-ratio intervals

This module evaluates

`log ((1 + x) / (1 - x)) = 2 * atanh x`

on an exact rational interval contained in `[0, 1)`.  A finite odd-power
head is evaluated by interval arithmetic and the analytic tail is bounded at
the upper endpoint.  It is the reusable logarithm primitive needed by the
high-frequency scalar certificates.
-/

def intervalPow (I : RatInterval) : ℕ → RatInterval
  | 0 => pure 1
  | n + 1 => intervalPow I n * I

theorem intervalPow_contains
    {I : RatInterval} {x : ℝ} (hx : I.Contains x) (n : ℕ) :
    (intervalPow I n).Contains (x ^ n) := by
  induction n with
  | zero => simpa [intervalPow] using contains_pure (1 : ℚ)
  | succ n ih =>
      rw [pow_succ]
      exact contains_mul ih hx

def positiveLogRatioHeadInterval (I : RatInterval) : ℕ → RatInterval
  | 0 => pure 0
  | N + 1 => positiveLogRatioHeadInterval I N +
      pure 2 * intervalPow I (2 * N + 1) / pure (2 * N + 1)

theorem positiveLogRatioHeadInterval_contains
    {I : RatInterval} {x : ℝ} (hx : I.Contains x) (N : ℕ) :
    (positiveLogRatioHeadInterval I N).Contains
      (2 * ∑ i ∈ Finset.range N, x ^ (2 * i + 1) / (2 * i + 1)) := by
  induction N with
  | zero =>
      norm_num [positiveLogRatioHeadInterval, Contains, RatInterval.pure]
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add]
      have hpow := intervalPow_contains hx (2 * N + 1)
      have hnum := contains_mul (contains_pure 2) hpow
      have hterm := contains_div_of_pos
        (by
          change 0 < (2 * N + 1 : ℚ)
          positivity)
        hnum (contains_pure (2 * N + 1))
      exact contains_add ih (by
        convert hterm using 1
        push_cast
        ring)

def positiveLogRatioTailInterval (I : RatInterval) (N : ℕ) : RatInterval :=
  ⟨0, 2 * (I.upper ^ (2 * N + 1) / (1 - I.upper ^ 2))⟩

def positiveLogRatioInterval (I : RatInterval) (N : ℕ) : RatInterval :=
  positiveLogRatioHeadInterval I N + positiveLogRatioTailInterval I N

private theorem ratioTail_mono
    {x u : ℝ} (hx0 : 0 ≤ x) (hxu : x ≤ u) (hu1 : u < 1)
    (N : ℕ) :
    x ^ (2 * N + 1) / (1 - x ^ 2) ≤
      u ^ (2 * N + 1) / (1 - u ^ 2) := by
  have hu0 : 0 ≤ u := hx0.trans hxu
  have hpow : x ^ (2 * N + 1) ≤ u ^ (2 * N + 1) :=
    pow_le_pow_left₀ hx0 hxu _
  have hupow0 : 0 ≤ u ^ (2 * N + 1) := pow_nonneg hu0 _
  have hsq : x ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hx0 hxu 2
  have hden : 1 - u ^ 2 ≤ 1 - x ^ 2 := by linarith
  have hdu : 0 < 1 - u ^ 2 := by nlinarith
  exact div_le_div₀ hupow0 hpow hdu hden

theorem positiveLogRatioTailInterval_contains
    {I : RatInterval} {x : ℝ}
    (hI0 : 0 ≤ I.lower) (hI1 : I.upper < 1)
    (hx : I.Contains x) (N : ℕ) :
    (positiveLogRatioTailInterval I N).Contains
      (Real.log ((1 + x) / (1 - x)) -
        2 * ∑ i ∈ Finset.range N, x ^ (2 * i + 1) / (2 * i + 1)) := by
  have hlowR : (0 : ℝ) ≤ (I.lower : ℚ) := by exact_mod_cast hI0
  have hx0 : 0 ≤ x := hlowR.trans hx.1
  have hx1R : x < 1 := hx.2.trans_lt (by exact_mod_cast hI1)
  have hlo := Real.sum_range_le_log_div hx0 hx1R N
  have hup := Real.log_div_le_sum_range_add hx0 hx1R N
  have hrem0 : 0 ≤ Real.log ((1 + x) / (1 - x)) -
      2 * ∑ i ∈ Finset.range N, x ^ (2 * i + 1) / (2 * i + 1) := by
    linarith
  have hremX : Real.log ((1 + x) / (1 - x)) -
        2 * ∑ i ∈ Finset.range N, x ^ (2 * i + 1) / (2 * i + 1) ≤
      2 * (x ^ (2 * N + 1) / (1 - x ^ 2)) := by
    linarith
  have hmono := ratioTail_mono hx0 hx.2 (by exact_mod_cast hI1) N
  have hupper := hremX.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
  constructor
  · simpa [positiveLogRatioTailInterval, Contains] using hrem0
  · simpa only [positiveLogRatioTailInterval, Contains, Rat.cast_div,
      Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_one] using hupper

theorem positiveLogRatioInterval_contains
    {I : RatInterval} {x : ℝ}
    (hI0 : 0 ≤ I.lower) (hI1 : I.upper < 1)
    (hx : I.Contains x) (N : ℕ) :
    (positiveLogRatioInterval I N).Contains
      (Real.log ((1 + x) / (1 - x))) := by
  have hhead := positiveLogRatioHeadInterval_contains hx N
  have htail := positiveLogRatioTailInterval_contains hI0 hI1 hx N
  unfold positiveLogRatioInterval
  convert contains_add hhead htail using 1
  ring

end

end ArithmeticHodge.Analysis.YoshidaPositiveLogEnclosures
