import ArithmeticHodge.Analysis.YoshidaConstantBounds

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddSharpMassLoss

open YoshidaConstantBounds

noncomputable section

/-!
# Sharp endpoint mass loss in the odd sector

The improved regular-kernel estimate replaces the old `log 2 / 4` loss by
`log 2 / 64`.  The scalar estimate below is analytic: it uses the monotone
Euler--Maclaurin correction from `YoshidaConstantBounds`, Archimedes' bound
`pi < 22/7`, and finite truncations of the universal logarithm series.
-/

/-- A four-term positive logarithm series at `x = 1/3`. -/
theorem six_hundred_ninety_three_div_thousand_lt_log_two :
    (693 / 1000 : ℝ) < Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- The matching logarithm remainder estimate gives a tight rational upper
bound without appealing to decimal evaluation. -/
theorem log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred :
    Real.log 2 < (1733 / 2500 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- A corrected harmonic approximation at the single index `4` already
places Euler's constant below `0.578`. -/
theorem eulerMascheroniConstant_lt_two_hundred_eighty_nine_div_five_hundred :
    Real.eulerMascheroniConstant < (289 / 500 : ℝ) := by
  have hgamma := eulerGamma_le_gammaUpperApprox 3
  have hlogTwo := six_hundred_ninety_three_div_thousand_lt_log_two
  have hlogFour : (2 : ℝ) * (693 / 1000) < Real.log 4 := by
    calc
      (2 : ℝ) * (693 / 1000) < 2 * Real.log 2 := by linarith
      _ = Real.log 4 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
        norm_num
  simp only [gammaUpperApprox, gammaLowerApprox] at hgamma
  norm_num [harmonic, Finset.sum_range_succ] at hgamma
  linarith

/-- Archimedes' `pi < 22/7` and the short logarithm bound control the
positive argument of the endpoint renormalization logarithm. -/
theorem pi_mul_log_two_lt_nineteen_thousand_sixty_three_div_eight_thousand_seven_hundred_fifty :
    Real.pi * Real.log 2 < (19063 / 8750 : ℝ) := by
  have hpi := Real.pi_lt_d4
  have hlogTwo :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred
  have hpiPos := Real.pi_pos
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- A short universal logarithm remainder estimate at the preceding rational
argument. -/
theorem log_nineteen_thousand_sixty_three_div_eight_thousand_seven_hundred_fifty_lt_seven_hundred_seventy_nine_div_thousand :
    Real.log (19063 / 8750 : ℝ) < (779 / 1000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (10313 / 27813 : ℝ))
    (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem log_pi_mul_log_two_lt_seven_hundred_seventy_nine_div_thousand :
    Real.log (Real.pi * Real.log 2) < (779 / 1000 : ℝ) := by
  have hprod :=
    pi_mul_log_two_lt_nineteen_thousand_sixty_three_div_eight_thousand_seven_hundred_fifty
  have hleft : 0 < Real.pi * Real.log 2 := by positivity
  have hright : (0 : ℝ) < 19063 / 8750 := by norm_num
  exact
    (Real.strictMonoOn_log hleft hright hprod).trans
      log_nineteen_thousand_sixty_three_div_eight_thousand_seven_hundred_fifty_lt_seven_hundred_seventy_nine_div_thousand

theorem inv_sqrt_two_lt_one_hundred_seventy_seven_div_two_hundred_fifty :
    1 / Real.sqrt 2 < (177 / 250 : ℝ) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rw [div_lt_iff₀ hsqrt]
  nlinarith [Real.sqrt_nonneg 2]

def yoshidaEndpointEvenSharpMassLoss : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.pi * Real.log 2) +
    Real.log 2 / 64

def yoshidaEndpointOddSharpMassLoss : ℝ :=
  yoshidaEndpointEvenSharpMassLoss + (1 / Real.sqrt 2 - Real.log 2)

theorem yoshidaEndpointOddSharpMassLoss_lt_seven_fifths :
    yoshidaEndpointOddSharpMassLoss < 7 / 5 := by
  have hgamma :=
    eulerMascheroniConstant_lt_two_hundred_eighty_nine_div_five_hundred
  have hlog :=
    log_pi_mul_log_two_lt_seven_hundred_seventy_nine_div_thousand
  have hsqrt :=
    inv_sqrt_two_lt_one_hundred_seventy_seven_div_two_hundred_fifty
  have htwo := six_hundred_ninety_three_div_thousand_lt_log_two
  unfold yoshidaEndpointOddSharpMassLoss yoshidaEndpointEvenSharpMassLoss
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddSharpMassLoss
