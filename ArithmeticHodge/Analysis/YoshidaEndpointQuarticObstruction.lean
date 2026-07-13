import ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialBound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointQuarticObstruction

open YoshidaEndpointPotentialBound

noncomputable section

/-!
# Obstruction to the coarse endpoint quartic strategy

The degree-one odd mode receives logarithmic coefficient `1` and quartic
coefficient `57/140`.  Treating every remaining endpoint term only by its
global mass loss would therefore require the resulting coefficient to be
nonnegative.  A short analytic argument proves the opposite.  This rules out
that coarse lower-bound strategy without testing a growing family of modes;
it does not assert that the actual endpoint form is negative.
-/

/-- A two-term positive logarithm series gives the lower bound needed below.
-/
theorem fifty_six_div_eighty_one_le_log_two :
    (56 / 81 : ℝ) ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- A three-term logarithm remainder gives a convenient strict upper bound.
-/
theorem log_two_lt_one_hundred_thirty_nine_div_two_hundred :
    Real.log 2 < (139 / 200 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- A four-term positive logarithm series at `56/27`. -/
theorem three_thousand_six_hundred_forty_seven_div_five_thousand_lt_log_fifty_six_div_twenty_seven :
    (3647 / 5000 : ℝ) < Real.log (56 / 27) := by
  have h := Real.sum_range_le_log_div (x := (29 / 83 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem fifty_six_div_twenty_seven_lt_pi_mul_log_two :
    (56 / 27 : ℝ) < Real.pi * Real.log 2 := by
  nlinarith [Real.pi_gt_three, fifty_six_div_eighty_one_le_log_two]

theorem three_thousand_six_hundred_forty_seven_div_five_thousand_lt_log_pi_mul_log_two :
    (3647 / 5000 : ℝ) < Real.log (Real.pi * Real.log 2) := by
  have hpos : (0 : ℝ) < 56 / 27 := by norm_num
  have hprod : 0 < Real.pi * Real.log 2 := by positivity
  exact
    three_thousand_six_hundred_forty_seven_div_five_thousand_lt_log_fifty_six_div_twenty_seven.trans
      (Real.strictMonoOn_log hpos hprod
        fifty_six_div_twenty_seven_lt_pi_mul_log_two)

/-- A rational positive margin in the endpoint hyperbolic loss. -/
theorem one_div_two_hundred_lt_inv_sqrt_two_sub_log_two :
    (1 / 200 : ℝ) < 1 / Real.sqrt 2 - Real.log 2 := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hseven : (7 / 10 : ℝ) < 1 / Real.sqrt 2 := by
    rw [lt_div_iff₀ hsqrt]
    nlinarith [Real.sqrt_nonneg 2]
  linarith [log_two_lt_one_hundred_thirty_nine_div_two_hundred]

/-- The exact endpoint hyperbolic loss is strictly positive. -/
theorem log_two_lt_inv_sqrt_two :
    Real.log 2 < 1 / Real.sqrt 2 := by
  linarith [one_div_two_hundred_lt_inv_sqrt_two_sub_log_two]

/-- Mass loss in the even endpoint lower bound: Euler's constant, the
renormalization logarithm, and the regular-kernel Schur loss. -/
def yoshidaEndpointEvenMassLoss : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.pi * Real.log 2) +
    Real.log 2 / 4

/-- The odd sector additionally pays the exact negative hyperbolic rank-one
loss. -/
def yoshidaEndpointOddMassLoss : ℝ :=
  yoshidaEndpointEvenMassLoss + (1 / Real.sqrt 2 - Real.log 2)

/-- Structural antiderivative formula used for the low-mode moments. -/
theorem integral_pow_nat (n : ℕ) (a b : ℝ) :
    (∫ x : ℝ in a..b, x ^ n) =
      (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  let F : ℝ → ℝ := fun x ↦ x ^ (n + 1) / (n + 1)
  have hderiv (x : ℝ) : HasDerivAt F (x ^ n) x := by
    dsimp only [F]
    convert ((hasDerivAt_id x).pow (n + 1)).div_const (n + 1) using 1
    simp only [id_eq, Nat.cast_add, Nat.cast_one]
    field_simp
    rw [Nat.add_sub_cancel]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) a b)
  rw [hint]
  dsimp only [F]
  ring

theorem integral_sq_centered :
    (∫ x : ℝ in -1..1, x ^ 2) = 2 / 3 := by
  rw [integral_pow_nat]
  norm_num

/-- Exact quartic potential contribution of the centered degree-one mode.
-/
theorem integral_endpointQuartic_mul_sq :
    (∫ x : ℝ in -1..1, yoshidaEndpointQuartic x * x ^ 2) = 19 / 70 := by
  unfold yoshidaEndpointQuartic
  rw [show (fun x : ℝ ↦ (x ^ 2 / 2 + x ^ 4 / 4) * x ^ 2) =
      fun x ↦ x ^ 4 / 2 + x ^ 6 / 4 by
    funext x
    ring]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_div, intervalIntegral.integral_div]
    rw [integral_pow_nat, integral_pow_nat]
    norm_num
  · exact Continuous.intervalIntegrable (μ := volume)
      ((continuous_id.pow 4).div_const 2) (-1) 1
  · exact Continuous.intervalIntegrable (μ := volume)
      ((continuous_id.pow 6).div_const 4) (-1) 1

theorem endpointQuartic_degree_one_ratio :
    (∫ x : ℝ in -1..1, yoshidaEndpointQuartic x * x ^ 2) =
      (57 / 140 : ℝ) * ∫ x : ℝ in -1..1, x ^ 2 := by
  rw [integral_endpointQuartic_mul_sq, integral_sq_centered]
  norm_num

/-- Coefficient supplied to the degree-one mass by the logarithmic term plus
the quartic lower potential, after subtracting all global endpoint losses.
-/
def yoshidaEndpointOddQuarticLowCoefficient : ℝ :=
  1 + 57 / 140 - yoshidaEndpointOddMassLoss

/-- The precise scalar inequality required by the coarse degree-one lower
bound fails strictly. -/
theorem yoshidaEndpointOddQuarticLowCoefficient_neg :
    yoshidaEndpointOddQuarticLowCoefficient < 0 := by
  have hgamma : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  have hlogpi :=
    three_thousand_six_hundred_forty_seven_div_five_thousand_lt_log_pi_mul_log_two
  have hlogtwo := fifty_six_div_eighty_one_le_log_two
  have hloss := one_div_two_hundred_lt_inv_sqrt_two_sub_log_two
  unfold yoshidaEndpointOddQuarticLowCoefficient
    yoshidaEndpointOddMassLoss yoshidaEndpointEvenMassLoss
  linarith

theorem not_yoshidaEndpointOddQuarticLowCoefficient_nonneg :
    ¬0 ≤ yoshidaEndpointOddQuarticLowCoefficient :=
  not_le_of_gt yoshidaEndpointOddQuarticLowCoefficient_neg

end

end ArithmeticHodge.Analysis.YoshidaEndpointQuarticObstruction
