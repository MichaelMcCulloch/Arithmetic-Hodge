import ArithmeticHodge.Analysis.ZetaProduct
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open Complex Filter Topology Real ArithmeticHodge.Analysis

namespace ArithmeticHodge.Analysis

set_option autoImplicit false

/-- On the positive real axis, the first Dirichlet-series term gives
`1 ≤ Re ζ(k)`. -/
theorem one_le_riemannZeta_re_nat_scratch (k : ℕ) (hk : 1 < k) :
    1 ≤ (riemannZeta (k : ℂ)).re := by
  rw [zeta_nat_eq_tsum_of_gt_one hk]
  have hcast : (∑' n : ℕ, 1 / (n : ℂ) ^ k) =
      Complex.ofReal (∑' n : ℕ, 1 / (n : ℝ) ^ k) := by
    rw [Complex.ofReal_tsum]
    congr 1
    funext n
    push_cast
    norm_cast
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ k) :=
    summable_one_div_nat_pow.mpr hk
  rw [hcast]
  simp only [Complex.ofReal_re]
  simpa using hsum.sum_le_tsum {1} (fun n _ => by positivity)

/-- Exact real Gamma factor at the positive even integers. -/
theorem GammaR_two_mul_nat_scratch (n : ℕ) :
    Complex.Gammaℝ ((2 * (n + 1) : ℕ) : ℂ) =
      (((n.factorial : ℝ) / Real.pi ^ (n + 1) : ℝ) : ℂ) := by
  rw [Complex.Gammaℝ_def]
  have hhalf : (((2 * (n + 1) : ℕ) : ℂ) / 2) = (n + 1 : ℕ) := by
    push_cast
    ring
  have hneg : -(((2 * (n + 1) : ℕ) : ℂ)) / 2 = -((n + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [hhalf, hneg, Complex.cpow_neg, Complex.cpow_natCast]
  have hGamma : Complex.Gamma ((n + 1 : ℕ) : ℂ) = n.factorial := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.Gamma_nat_eq_factorial n
  rw [hGamma]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The Riemann xi function has a factorial lower bound on every positive
even integer.  This is the infinite-type growth input needed to rule out a
finite zero set. -/
theorem xi_even_factorial_re_lower_scratch (n : ℕ) :
    (n.factorial : ℝ) / Real.pi ^ (n + 1) ≤
      (xiFunction ((2 * (n + 1) : ℕ) : ℂ)).re := by
  let s : ℂ := ((2 * (n + 1) : ℕ) : ℂ)
  have hs_re : 1 < s.re := by
    dsimp [s]
    norm_num
    exact_mod_cast (show 1 < 2 * (n + 1) by omega)
  have hs_ne : s ≠ 0 := fun h => by
    rw [h] at hs_re
    norm_num at hs_re
  have hs_one : s ≠ 1 := fun h => by
    rw [h] at hs_re
    norm_num at hs_re
  have hGamma_ne : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs_re)
  have hcompleted : riemannZeta s * Complex.Gammaℝ s = completedRiemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs_ne, div_mul_cancel₀ _ hGamma_ne]
  have hGamma : Complex.Gammaℝ s =
      ((((n.factorial : ℝ) / Real.pi ^ (n + 1)) : ℝ) : ℂ) := by
    simpa [s] using GammaR_two_mul_nat_scratch n
  have hzeta : 1 ≤ (riemannZeta s).re := by
    simpa [s] using one_le_riemannZeta_re_nat_scratch (2 * (n + 1)) (by omega)
  have hquot_nonneg : 0 ≤ (n.factorial : ℝ) / Real.pi ^ (n + 1) := by positivity
  have hLambda : (n.factorial : ℝ) / Real.pi ^ (n + 1) ≤
      (completedRiemannZeta s).re := by
    rw [← hcompleted, hGamma]
    simp only [mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact le_mul_of_one_le_left hquot_nonneg hzeta
  have hxi := xiFunction_eq_mul_completedZeta s hs_ne hs_one
  have hxi_re : (xiFunction s).re =
      (1 / 2 : ℝ) * s.re * (s.re - 1) * (completedRiemannZeta s).re := by
    rw [hxi]
    let c : ℂ := (1 / 2 : ℂ) * s * (s - 1)
    have hc_im : c.im = 0 := by
      dsimp [c, s]
      norm_num
    have hc_re : c.re = (1 / 2 : ℝ) * s.re * (s.re - 1) := by
      dsimp [c, s]
      norm_num
    change (c * completedRiemannZeta s).re = _
    rw [mul_re, hc_im, zero_mul, sub_zero, hc_re]
  have hcoeff : 1 ≤ (1 / 2 : ℝ) * s.re * (s.re - 1) := by
    dsimp [s]
    norm_num
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hLambda_nonneg : 0 ≤ (completedRiemannZeta s).re :=
    hquot_nonneg.trans hLambda
  rw [show ((2 * (n + 1) : ℕ) : ℂ) = s from rfl, hxi_re]
  exact hLambda.trans (le_mul_of_one_le_left hLambda_nonneg hcoeff)

end ArithmeticHodge.Analysis

#print axioms ArithmeticHodge.Analysis.xi_even_factorial_re_lower_scratch
#print axioms ArithmeticHodge.Analysis.xi_even_factorial_re_lower
