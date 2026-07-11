import ArithmeticHodge.Analysis.DigammaTrapezoid
import ArithmeticHodge.Analysis.DigammaTrapezoidBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open ArithmeticHodge.Analysis.DigammaTrapezoid
open ArithmeticHodge.Analysis.DigammaTrapezoidBounds

namespace ArithmeticHodge.Analysis.DigammaNumericBounds

/-!
Kernel-checked rational enclosures for the two critical digamma values used in
Yoshida's Section 6 substitutions. Logarithms are certified with Mathlib's
atanh expansion and explicit remainder, not a floating-point oracle.
-/

theorem shiftedReciprocalPrimitive_quarter_twentyFive_lower :
    (3218925 / 1000000 : ℝ) ≤
      shiftedReciprocalPrimitive (1 / 4) 25 0 := by
  let z : ℝ := 1809 / 18193
  have hz0 : 0 ≤ z := by norm_num [z]
  have hz1 : z < 1 := by norm_num [z]
  have hseries := Real.sum_range_le_log_div hz0 hz1 3
  have hdecomp :
      shiftedReciprocalPrimitive (1 / 4) 25 0 =
        (9 / 2 : ℝ) * Real.log 2 +
          (1 / 2 : ℝ) * Real.log ((1 + z) / (1 - z)) := by
    unfold shiftedReciprocalPrimitive
    norm_num [z]
    rw [show (10001 / 16 : ℝ) = (2 : ℝ) ^ 9 * (10001 / 8192) by
      norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    ring
  rw [hdecomp]
  have hnumeric :
      (3218925 / 1000000 : ℝ) ≤
        (9 / 2 : ℝ) * 0.6931471803 +
          ∑ i ∈ Finset.range 3, z ^ (2 * i + 1) / (2 * i + 1) := by
    norm_num [z, Finset.sum_range_succ]
  nlinarith [Real.log_two_gt_d9]

theorem shiftedReciprocalPrimitive_quarter_twentyFive_upper :
    shiftedReciprocalPrimitive (1 / 4) 25 0 ≤
      (3218927 / 1000000 : ℝ) := by
  let z : ℝ := 1809 / 18193
  have hz0 : 0 ≤ z := by norm_num [z]
  have hz1 : z < 1 := by norm_num [z]
  have hseries := Real.log_div_le_sum_range_add hz0 hz1 3
  have hdecomp :
      shiftedReciprocalPrimitive (1 / 4) 25 0 =
        (9 / 2 : ℝ) * Real.log 2 +
          (1 / 2 : ℝ) * Real.log ((1 + z) / (1 - z)) := by
    unfold shiftedReciprocalPrimitive
    norm_num [z]
    rw [show (10001 / 16 : ℝ) = (2 : ℝ) ^ 9 * (10001 / 8192) by
      norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    ring
  rw [hdecomp]
  have hnumeric :
      (9 / 2 : ℝ) * 0.6931471808 +
          ((∑ i ∈ Finset.range 3, z ^ (2 * i + 1) / (2 * i + 1)) +
            z ^ (2 * 3 + 1) / (1 - z ^ 2)) ≤
        (3218927 / 1000000 : ℝ) := by
    norm_num [z, Finset.sum_range_succ]
  nlinarith [Real.log_two_lt_d9]

theorem shiftedReciprocalPrimitive_quarter_threeHundredFifty_lower :
    (5857933 / 1000000 : ℝ) ≤
      shiftedReciprocalPrimitive (1 / 4) 350 0 := by
  let z : ℝ := 911425 / 3008577
  have hz0 : 0 ≤ z := by norm_num [z]
  have hz1 : z < 1 := by norm_num [z]
  have hseries := Real.sum_range_le_log_div hz0 hz1 8
  have hdecomp :
      shiftedReciprocalPrimitive (1 / 4) 350 0 =
        (8 : ℝ) * Real.log 2 +
          (1 / 2 : ℝ) * Real.log ((1 + z) / (1 - z)) := by
    unfold shiftedReciprocalPrimitive
    norm_num [z]
    rw [show (1960001 / 16 : ℝ) =
        (2 : ℝ) ^ 16 * (1960001 / 1048576) by norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    ring
  rw [hdecomp]
  have hnumeric :
      (5857933 / 1000000 : ℝ) ≤
        (8 : ℝ) * 0.6931471803 +
          ∑ i ∈ Finset.range 8, z ^ (2 * i + 1) / (2 * i + 1) := by
    norm_num [z, Finset.sum_range_succ]
  nlinarith [Real.log_two_gt_d9]

theorem shiftedReciprocalPrimitive_quarter_threeHundredFifty_upper :
    shiftedReciprocalPrimitive (1 / 4) 350 0 ≤
      (5857934 / 1000000 : ℝ) := by
  let z : ℝ := 911425 / 3008577
  have hz0 : 0 ≤ z := by norm_num [z]
  have hz1 : z < 1 := by norm_num [z]
  have hseries := Real.log_div_le_sum_range_add hz0 hz1 8
  have hdecomp :
      shiftedReciprocalPrimitive (1 / 4) 350 0 =
        (8 : ℝ) * Real.log 2 +
          (1 / 2 : ℝ) * Real.log ((1 + z) / (1 - z)) := by
    unfold shiftedReciprocalPrimitive
    norm_num [z]
    rw [show (1960001 / 16 : ℝ) =
        (2 : ℝ) ^ 16 * (1960001 / 1048576) by norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
    ring
  rw [hdecomp]
  have hnumeric :
      (8 : ℝ) * 0.6931471808 +
          ((∑ i ∈ Finset.range 8, z ^ (2 * i + 1) / (2 * i + 1)) +
            z ^ (2 * 8 + 1) / (1 - z ^ 2)) ≤
        (5857934 / 1000000 : ℝ) := by
    norm_num [z, Finset.sum_range_succ]
  nlinarith [Real.log_two_lt_d9]

theorem digamma_quarter_vertical_re_fifty_lower :
    (1609 / 500 : ℝ) ≤
      (Complex.digamma ((1 / 4 : ℝ) +
        (50 / 2 : ℝ) * Complex.I)).re := by
  have herror := tsum_shiftedTrapezoidalError_upper_of_crossing
    (y := (25 : ℝ)) (by norm_num) 43 (by norm_num) (by norm_num)
  norm_num
  have hid := digamma_quarter_vertical_re_eq_primitive_sub_trapezoidalErrors
    (v := (50 : ℝ)) (by norm_num)
  norm_num at hid
  rw [hid]
  norm_num [shiftedReciprocalRealPart, reciprocalRealPart] at herror ⊢
  linarith [shiftedReciprocalPrimitive_quarter_twentyFive_lower]

theorem digamma_quarter_vertical_re_fifty_upper :
    (Complex.digamma ((1 / 4 : ℝ) +
        (50 / 2 : ℝ) * Complex.I)).re ≤
      (3219 / 1000 : ℝ) := by
  have herror := tsum_shiftedTrapezoidalError_lower_of_crossing
    (y := (25 : ℝ)) (by norm_num) 43 (by norm_num) (by norm_num)
  norm_num
  have hid := digamma_quarter_vertical_re_eq_primitive_sub_trapezoidalErrors
    (v := (50 : ℝ)) (by norm_num)
  norm_num at hid
  rw [hid]
  norm_num [shiftedReciprocalRealPart, reciprocalRealPart] at herror ⊢
  linarith [shiftedReciprocalPrimitive_quarter_twentyFive_upper]

theorem digamma_quarter_vertical_re_sevenHundred_lower :
    (5857 / 1000 : ℝ) ≤
      (Complex.digamma ((1 / 4 : ℝ) +
        (700 / 2 : ℝ) * Complex.I)).re := by
  have herror := tsum_shiftedTrapezoidalError_upper_of_crossing
    (y := (350 : ℝ)) (by norm_num) 605 (by norm_num) (by norm_num)
  norm_num
  have hid := digamma_quarter_vertical_re_eq_primitive_sub_trapezoidalErrors
    (v := (700 : ℝ)) (by norm_num)
  norm_num at hid
  rw [hid]
  norm_num [shiftedReciprocalRealPart, reciprocalRealPart] at herror ⊢
  linarith [shiftedReciprocalPrimitive_quarter_threeHundredFifty_lower]

theorem digamma_quarter_vertical_re_sevenHundred_upper :
    (Complex.digamma ((1 / 4 : ℝ) +
        (700 / 2 : ℝ) * Complex.I)).re ≤
      (2929 / 500 : ℝ) := by
  have herror := tsum_shiftedTrapezoidalError_lower_of_crossing
    (y := (350 : ℝ)) (by norm_num) 605 (by norm_num) (by norm_num)
  norm_num
  have hid := digamma_quarter_vertical_re_eq_primitive_sub_trapezoidalErrors
    (v := (700 : ℝ)) (by norm_num)
  norm_num at hid
  rw [hid]
  norm_num [shiftedReciprocalRealPart, reciprocalRealPart] at herror ⊢
  linarith [shiftedReciprocalPrimitive_quarter_threeHundredFifty_upper]

end ArithmeticHodge.Analysis.DigammaNumericBounds
