import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaConstantBounds

/-!
# Certified constants for Yoshida's diagonal moments

This module gives strict rational enclosures for the Euler--Mascheroni
constant, `log (log 2)`, and `log pi`.  The Euler enclosure is obtained from
monotone corrected harmonic approximations with an explicit `1 / (12 n^2)`
error term; logarithms are enclosed by finite odd-power series with exact
rational remainders.
-/

theorem strict_log_two_bounds :
    (6931 / 10000 : ℝ) < Real.log 2 ∧ Real.log 2 < (6932 / 10000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 5
  have hup := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hlo hup ⊢
  constructor <;> linarith

theorem strict_log_two_fine_bounds :
    (69314718055 / 100000000000 : ℝ) < Real.log 2 ∧
      Real.log 2 < (69314718057 / 100000000000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 12
  have hup := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at hlo hup ⊢
  constructor <;> linarith

theorem strict_log_thirtytwo_div_twentyfive_bounds :
    (2468600778 / 10000000000 : ℝ) < Real.log (32 / 25) ∧
      Real.log (32 / 25) < (2468600780 / 10000000000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (x := (7 / 57 : ℝ)) (by norm_num) (by norm_num) 6
  have hup := Real.log_div_le_sum_range_add (x := (7 / 57 : ℝ))
    (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hlo hup ⊢
  constructor <;> linarith

private theorem log_one_add_inv_upper {t : ℝ} (ht : 0 < t) :
    Real.log ((t + 1) / t) ≤ (2 * t + 1) / (2 * t * (t + 1)) := by
  have hx0 : 0 ≤ (1 / (2 * t + 1) : ℝ) := by positivity
  have hx1 : (1 / (2 * t + 1) : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have h := Real.log_div_le_sum_range_add (x := (1 / (2 * t + 1) : ℝ)) hx0 hx1 1
  norm_num [Finset.sum_range_succ] at h
  rw [show (1 + (2 * t + 1)⁻¹) / (1 - (2 * t + 1)⁻¹) =
      (t + 1) / t by field_simp; ring] at h
  have hbase : 1 < (2 * t + 1) ^ 2 := one_lt_pow₀ (by linarith) (by norm_num)
  have hden : 0 < 1 - ((2 * t + 1) ^ 2)⁻¹ :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ hbase)
  have hfour : 0 < 4 * t * (t + 1) := by positivity
  have htarget : 0 < t * 4 + t ^ 2 * 4 := by nlinarith [sq_nonneg t]
  have hpoly : 0 < (2 * t + 1) ^ 2 - 1 := by nlinarith [sq_nonneg t]
  have hid : (2 * t + 1)⁻¹ + ((2 * t + 1) ^ 3)⁻¹ /
        (1 - ((2 * t + 1) ^ 2)⁻¹) =
      (2 * t + 1) / (4 * t * (t + 1)) := by
    field_simp [ne_of_gt ht, ne_of_gt (by linarith : 0 < t + 1), ne_of_gt hden,
      ne_of_gt hfour]
    field_simp [ne_of_gt htarget, ne_of_gt hpoly]
    ring
  rw [hid] at h
  calc
    Real.log ((t + 1) / t) ≤ 2 * ((2 * t + 1) / (4 * t * (t + 1))) := by linarith
    _ = (2 * t + 1) / (2 * t * (t + 1)) := by
      field_simp [ne_of_gt ht, ne_of_gt (by linarith : 0 < t + 1)]
      norm_num

private theorem log_one_add_inv_lower {t : ℝ} (ht : 0 < t) :
    2 * (1 / (2 * t + 1) + (1 / (2 * t + 1)) ^ 3 / 3) ≤
      Real.log ((t + 1) / t) := by
  have hx0 : 0 ≤ (1 / (2 * t + 1) : ℝ) := by positivity
  have hx1 : (1 / (2 * t + 1) : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have h := Real.sum_range_le_log_div (x := (1 / (2 * t + 1) : ℝ)) hx0 hx1 2
  norm_num [Finset.sum_range_succ] at h
  rw [show (1 + (2 * t + 1)⁻¹) / (1 - (2 * t + 1)⁻¹) =
      (t + 1) / t by field_simp; ring] at h
  simp only [one_div, inv_pow] at ⊢
  linarith

noncomputable def gammaLowerApprox (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1))

noncomputable def gammaUpperApprox (n : ℕ) : ℝ :=
  gammaLowerApprox n + 1 / (12 * (n + 1) ^ 2)

private theorem gammaLowerApprox_step (n : ℕ) :
    gammaLowerApprox n ≤ gammaLowerApprox (n + 1) := by
  let t : ℝ := n + 1
  have ht : 0 < t := by
    dsimp [t]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hlog := log_one_add_inv_upper ht
  have hdiff : gammaLowerApprox (n + 1) - gammaLowerApprox n =
      (2 * t + 1) / (2 * t * (t + 1)) - Real.log ((t + 1) / t) := by
    simp only [gammaLowerApprox, harmonic_succ, Rat.cast_add, Rat.cast_inv,
      Rat.cast_natCast, Nat.cast_add, Nat.cast_one, t]
    rw [Real.log_div (by positivity) (by positivity)]
    field_simp
    ring
  apply sub_nonneg.mp
  rw [hdiff]
  linarith

private theorem corrected_log_increment_upper {t : ℝ} (ht : 0 < t) :
    (2 * t + 1) / (2 * t * (t + 1)) - Real.log ((t + 1) / t) ≤
      1 / (12 * t ^ 2) - 1 / (12 * (t + 1) ^ 2) := by
  have hlog := log_one_add_inv_lower ht
  calc
    (2 * t + 1) / (2 * t * (t + 1)) - Real.log ((t + 1) / t) ≤
        (2 * t + 1) / (2 * t * (t + 1)) -
          2 * (1 / (2 * t + 1) + (1 / (2 * t + 1)) ^ 3 / 3) := by linarith
    _ ≤ 1 / (12 * t ^ 2) - 1 / (12 * (t + 1) ^ 2) := by
      field_simp [ne_of_gt ht, ne_of_gt (by linarith : 0 < t + 1),
        ne_of_gt (by linarith : 0 < 2 * t + 1)]
      nlinarith [sq_nonneg t, sq_nonneg (t + 1)]

private theorem gammaUpperApprox_step (n : ℕ) :
    gammaUpperApprox (n + 1) ≤ gammaUpperApprox n := by
  let t : ℝ := n + 1
  have ht : 0 < t := by
    dsimp [t]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hinc := corrected_log_increment_upper ht
  have hdiff : gammaUpperApprox (n + 1) - gammaUpperApprox n =
      ((2 * t + 1) / (2 * t * (t + 1)) - Real.log ((t + 1) / t)) -
        (1 / (12 * t ^ 2) - 1 / (12 * (t + 1) ^ 2)) := by
    simp only [gammaUpperApprox, gammaLowerApprox, harmonic_succ, Rat.cast_add,
      Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one, t]
    rw [Real.log_div (by positivity) (by positivity)]
    field_simp
    ring
  apply sub_nonpos.mp
  rw [hdiff]
  linarith

private theorem tendsto_shift_nat : Filter.Tendsto (fun n : ℕ ↦ n + 1)
    Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [Filter.eventually_ge_atTop b] with n hn
  omega

theorem tendsto_gammaLowerApprox :
    Filter.Tendsto gammaLowerApprox Filter.atTop
      (nhds Real.eulerMascheroniConstant) := by
  have hmain : Filter.Tendsto
      (fun n : ℕ ↦ (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 1))
      Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      Real.tendsto_harmonic_sub_log.comp tendsto_shift_nat
  have hcast : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hn : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1)
      Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hcast.comp tendsto_shift_nat
  have hden : Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ) * ((n : ℝ) + 1))
      Filter.atTop Filter.atTop := hn.const_mul_atTop (by norm_num)
  have hcorr : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (2 * ((n : ℝ) + 1)))
      Filter.atTop (nhds 0) := hden.const_div_atTop 1
  simpa only [gammaLowerApprox, Nat.cast_add, Nat.cast_one, sub_zero] using hmain.sub hcorr

theorem tendsto_gammaUpperApprox :
    Filter.Tendsto gammaUpperApprox Filter.atTop
      (nhds Real.eulerMascheroniConstant) := by
  have hcast : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hn : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1)
      Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hcast.comp tendsto_shift_nat
  have hsq : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ 2)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun n ↦ ?_) hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [sq_nonneg ((n : ℝ) + 1)]
  have hden : Filter.Tendsto (fun n : ℕ ↦ (12 : ℝ) * (((n : ℝ) + 1) ^ 2))
      Filter.atTop Filter.atTop := hsq.const_mul_atTop (by norm_num)
  have hcorr : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) /
      (12 * (((n : ℝ) + 1) ^ 2))) Filter.atTop (nhds 0) := hden.const_div_atTop 1
  have hsum := tendsto_gammaLowerApprox.add hcorr
  simpa only [gammaUpperApprox, add_zero, Nat.cast_add, Nat.cast_one] using hsum

theorem gammaLowerApprox_le_eulerGamma (n : ℕ) :
    gammaLowerApprox n ≤ Real.eulerMascheroniConstant :=
  (monotone_nat_of_le_succ gammaLowerApprox_step).ge_of_tendsto
    tendsto_gammaLowerApprox n

theorem eulerGamma_le_gammaUpperApprox (n : ℕ) :
    Real.eulerMascheroniConstant ≤ gammaUpperApprox n :=
  (antitone_nat_of_succ_le gammaUpperApprox_step).le_of_tendsto
    tendsto_gammaUpperApprox n

theorem strict_log_one_hundred_bounds :
    (46051701858 / 10000000000 : ℝ) < Real.log 100 ∧
      Real.log 100 < (46051701862 / 10000000000 : ℝ) := by
  have htwo := strict_log_two_fine_bounds
  have hratio := strict_log_thirtytwo_div_twentyfive_bounds
  have hid : Real.log (100 : ℝ) = 7 * Real.log 2 - Real.log (32 / 25) := by
    calc
      Real.log (100 : ℝ) = Real.log (((2 : ℝ) ^ 7) / (32 / 25)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 7) - Real.log (32 / 25) := by
        rw [Real.log_div (by norm_num) (by norm_num)]
      _ = 7 * Real.log 2 - Real.log (32 / 25) := by rw [Real.log_pow]; norm_num
  rw [hid]
  constructor <;> linarith

theorem strict_euler_gamma_bounds :
    (5771 / 10000 : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (5773 / 10000 : ℝ) := by
  have hlower := gammaLowerApprox_le_eulerGamma 99
  have hupper := eulerGamma_le_gammaUpperApprox 99
  have hlog := strict_log_one_hundred_bounds
  constructor
  · apply lt_of_lt_of_le ?_ hlower
    simp only [gammaLowerApprox]
    norm_num [harmonic, Finset.sum_range_succ] at ⊢
    linarith [hlog.2]
  · apply lt_of_le_of_lt hupper
    simp only [gammaUpperApprox, gammaLowerApprox]
    norm_num [harmonic, Finset.sum_range_succ] at ⊢
    linarith [hlog.1]

private theorem log_ten_thousand_div_6931_upper :
    Real.log (10000 / 6931 : ℝ) < (3666 / 10000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (3069 / 16931 : ℝ))
    (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem log_ten_thousand_div_6932_lower :
    (3664 / 10000 : ℝ) < Real.log (10000 / 6932 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (3068 / 16932 : ℝ))
    (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem strict_log_log_two_bounds :
    (-3666 / 10000 : ℝ) < Real.log (Real.log 2) ∧
      Real.log (Real.log 2) < (-3664 / 10000 : ℝ) := by
  have htwo := strict_log_two_bounds
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlowerRat : (-3666 / 10000 : ℝ) < Real.log (6931 / 10000) := by
    rw [show (6931 / 10000 : ℝ) = (10000 / 6931)⁻¹ by norm_num, Real.log_inv]
    linarith [log_ten_thousand_div_6931_upper]
  have hupperRat : Real.log (6932 / 10000 : ℝ) < (-3664 / 10000 : ℝ) := by
    rw [show (6932 / 10000 : ℝ) = (10000 / 6932)⁻¹ by norm_num, Real.log_inv]
    linarith [log_ten_thousand_div_6932_lower]
  constructor
  · exact hlowerRat.trans (Real.log_lt_log (by norm_num) htwo.1)
  · exact (Real.log_lt_log hlog2pos htwo.2).trans hupperRat

private theorem log_3141592_million_lower :
    (11447 / 10000 : ℝ) < Real.log (3141592 / 1000000 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (267699 / 517699 : ℝ))
    (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem log_3141593_million_upper :
    Real.log (3141593 / 1000000 : ℝ) < (11448 / 10000 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (2141593 / 4141593 : ℝ))
    (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

theorem strict_log_pi_bounds :
    (11447 / 10000 : ℝ) < Real.log Real.pi ∧
      Real.log Real.pi < (11448 / 10000 : ℝ) := by
  constructor
  · have hpi := Real.pi_gt_d6
    have hlog := log_3141592_million_lower
    norm_num at hpi
    norm_num at hlog
    exact hlog.trans
      (Real.log_lt_log (by norm_num) hpi)
  · have hpi := Real.pi_lt_d6
    have hlog := log_3141593_million_upper
    norm_num at hpi
    norm_num at hlog
    norm_num at ⊢
    exact (Real.log_lt_log Real.pi_pos hpi).trans
      hlog

theorem yoshida_euler_gamma_bounds :
    (5771 / 10000 : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (5773 / 10000 : ℝ) := by
  exact strict_euler_gamma_bounds

theorem yoshida_log_log_two_bounds :
    (-3666 / 10000 : ℝ) < Real.log (Real.log 2) ∧
      Real.log (Real.log 2) < (-3664 / 10000 : ℝ) := by
  exact strict_log_log_two_bounds

theorem yoshida_log_pi_bounds :
    (11447 / 10000 : ℝ) < Real.log Real.pi ∧
      Real.log Real.pi < (11448 / 10000 : ℝ) := by
  exact strict_log_pi_bounds

end ArithmeticHodge.Analysis.YoshidaConstantBounds


