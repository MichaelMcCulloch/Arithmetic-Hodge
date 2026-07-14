import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaEndpointParameter
import ArithmeticHodge.Analysis.YoshidaFactorTwoCenteredPhysical

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoStructuralConstantBounds

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical

/-!
# Structural constant bounds for the factor-two endpoint

The intrinsic two-mode arguments only need coarse rational boxes for three
fixed constants.  The logarithmic bounds below come directly from the global
odd-power expansion of `log ((1+x)/(1-x))`; the square-root bounds are exact
algebra.  No interval subdivision or finite family of modes occurs here.
-/

/-- A public sharp enclosure of the retained-prime shift `log (3/2)`, proved
directly from the odd-power logarithm expansion. -/
theorem strict_log_three_halves_fine_bounds :
    (40546510810816 / 100000000000000 : ℝ) < Real.log (3 / 2) ∧
      Real.log (3 / 2) <
        (40546510810817 / 100000000000000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 10
  have hup := Real.log_div_le_sum_range_add
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hlo hup ⊢
  constructor <;> linarith

/-- The dimensionless `p = 3` lag is confined to a single short rational
interval. -/
theorem factorTwoPrimeLag_bounds :
    (11699 / 10000 : ℝ) <
        factorTwoPrimeShift / yoshidaEndpointA ∧
      factorTwoPrimeShift / yoshidaEndpointA < (117 / 100 : ℝ) := by
  have hlog := strict_log_two_fine_bounds
  have hshift := strict_log_three_halves_fine_bounds
  constructor
  · rw [lt_div_iff₀ yoshidaEndpointA_pos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    nlinarith [hlog.2, hshift.1]
  · rw [div_lt_iff₀ yoshidaEndpointA_pos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    nlinarith [hlog.1, hshift.2]

/-- Coarse but sign-useful bounds for the dyadic prime coefficient. -/
theorem factorTwoDyadicWeight_bounds :
    (49 / 100 : ℝ) < Real.log 2 / Real.sqrt 2 ∧
      Real.log 2 / Real.sqrt 2 < (491 / 1000 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtLower : (1414 / 1000 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hsqrtUpper : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2]
  have hlog := strict_log_two_bounds
  constructor
  · rw [lt_div_iff₀ hsqrtPos]
    nlinarith [hlog.1]
  · rw [div_lt_iff₀ hsqrtPos]
    nlinarith [hlog.2]

/-- Coarse structural bounds for the retained `p = 3` prime coefficient. -/
theorem factorTwoPrimeThreeWeight_bounds :
    (633 / 1000 : ℝ) < Real.log 3 / Real.sqrt 3 ∧
      Real.log 3 / Real.sqrt 3 < (127 / 200 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtLower : (1732 / 1000 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3]
  have hsqrtUpper : Real.sqrt 3 < (1733 / 1000 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 3]
  have hlog := strict_log_two_fine_bounds
  have hshift := strict_log_three_halves_fine_bounds
  have hlogThree : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  rw [hlogThree]
  constructor
  · rw [lt_div_iff₀ hsqrtPos]
    nlinarith [hlog.1, hshift.1]
  · rw [div_lt_iff₀ hsqrtPos]
    nlinarith [hlog.2, hshift.2]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoStructuralConstantBounds
