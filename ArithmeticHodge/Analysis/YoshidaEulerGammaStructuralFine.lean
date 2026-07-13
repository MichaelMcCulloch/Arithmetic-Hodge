import ArithmeticHodge.Analysis.YoshidaConstantBounds

set_option autoImplicit false

noncomputable section

namespace ArithmeticHodge.Analysis.YoshidaEulerGammaStructuralFine

open ArithmeticHodge.Analysis.YoshidaConstantBounds

/-!
# A small fixed-index Euler--Mascheroni enclosure

The corrected harmonic upper approximation at index three uses only the four
terms of `harmonic 4`.  Its logarithm is `log 4 = 2 * log 2`, so the analytic
odd-power enclosure for `log 2` gives the rational upper bound below without a
long harmonic normalization or a finite decision certificate.
-/

/-- The four-term corrected harmonic approximation, in closed form. -/
theorem gammaUpperApprox_three_eq :
    gammaUpperApprox 3 = 377 / 192 - 2 * Real.log 2 := by
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  simp only [gammaUpperApprox, gammaLowerApprox]
  norm_num [harmonic, Finset.sum_range_succ, hlog]
  ring

/-- A structural upper enclosure using four harmonic terms and the fixed
twelve-term analytic `atanh` enclosure for `log 2`. -/
theorem eulerGamma_lt_577248_div_million :
    Real.eulerMascheroniConstant < (577248 / 1000000 : ℝ) := by
  have hgamma := eulerGamma_le_gammaUpperApprox 3
  have hlog := strict_log_two_fine_bounds.1
  rw [gammaUpperApprox_three_eq] at hgamma
  norm_num at hlog ⊢
  linarith

end ArithmeticHodge.Analysis.YoshidaEulerGammaStructuralFine
