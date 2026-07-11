import ArithmeticHodge.Analysis.DigammaTrapezoid
import ArithmeticHodge.Analysis.TrapezoidalErrorBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.PSeries

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Set MeasureTheory intervalIntegral Filter
open ArithmeticHodge.Analysis.DigammaTrapezoid
open ArithmeticHodge.Analysis.TrapezoidalErrorBounds

namespace ArithmeticHodge.Analysis.DigammaTrapezoidBounds

/-!
Signed and quantitative bounds for the shifted trapezoidal-error series in the
real part of the critical-line digamma function.
-/

private theorem hasDerivAt_shiftedReciprocalRealPart
    {x y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (shiftedReciprocalRealPart x y)
      (reciprocalRealPartDeriv y (x + t)) t := by
  have hinner : HasDerivAt (fun s : ℝ ↦ x + s) 1 t := by
    simpa using (hasDerivAt_const t x).add (hasDerivAt_id t)
  simpa [shiftedReciprocalRealPart] using
    (hasDerivAt_reciprocalRealPart (u := x + t) hy).comp t hinner

private theorem hasDerivAt_shiftedReciprocalRealPartDeriv
    {x y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ reciprocalRealPartDeriv y (x + s))
      (reciprocalRealPartSecondDeriv y (x + t)) t := by
  have hinner : HasDerivAt (fun s : ℝ ↦ x + s) 1 t := by
    simpa using (hasDerivAt_const t x).add (hasDerivAt_id t)
  simpa using
    (hasDerivAt_reciprocalRealPartDeriv (u := x + t) hy).comp t hinner

private theorem shiftedReciprocalRealPart_contDiff_two
    {x y : ℝ} (hy : y ≠ 0) :
    ContDiff ℝ 2 (shiftedReciprocalRealPart x y) := by
  unfold shiftedReciprocalRealPart reciprocalRealPart
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · intro t
    have hden : 0 < (x + t) ^ 2 + y ^ 2 := by positivity
    exact hden.ne'

private theorem iteratedDeriv_two_shiftedReciprocalRealPart
    {x y t : ℝ} (hy : y ≠ 0) :
    iteratedDeriv 2 (shiftedReciprocalRealPart x y) t =
      reciprocalRealPartSecondDeriv y (x + t) := by
  have hfirst : deriv (shiftedReciprocalRealPart x y) =
      fun t ↦ reciprocalRealPartDeriv y (x + t) := by
    funext t
    exact (hasDerivAt_shiftedReciprocalRealPart
      (x := x) (y := y) (t := t) hy).deriv
  have hsecond : deriv (fun t ↦ reciprocalRealPartDeriv y (x + t)) =
      fun t ↦ reciprocalRealPartSecondDeriv y (x + t) := by
    funext t
    exact (hasDerivAt_shiftedReciprocalRealPartDeriv
      (x := x) (y := y) (t := t) hy).deriv
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ',
    show (1 : ℕ) = 0 + 1 by omega, iteratedDeriv_succ',
    iteratedDeriv_zero, hfirst, hsecond]

theorem shifted_unit_trapezoidal_error_le_global
    {x y : ℝ} (hy : 0 < y) (n : ℕ) :
    |shiftedTrapezoidalError x y n| ≤ 1 / (6 * y ^ 3) := by
  have hcont := shiftedReciprocalRealPart_contDiff_two (x := x) hy.ne'
  have hbound : ∀ t,
      |iteratedDerivWithin 2 (shiftedReciprocalRealPart x y)
          (Icc (n : ℝ) (n + 1)) t| ≤ 2 / y ^ 3 := by
    intro t
    by_cases ht : t ∈ Icc (n : ℝ) (n + 1)
    · rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (by norm_num : (n : ℝ) < n + 1))
        hcont.contDiffAt ht,
        iteratedDeriv_two_shiftedReciprocalRealPart hy.ne']
      exact abs_reciprocalRealPartSecondDeriv_le_two_div_cube_global hy
    · rw [iteratedDerivWithin_succ,
        derivWithin_zero_of_notMem_closure (by rwa [closure_Icc]), abs_zero]
      positivity
  have htrap := trapezoidal_error_le_of_c2
    (a := (n : ℝ)) (b := n + 1) hcont.contDiffOn
    (by simpa [uIcc_of_le (by norm_num : (n : ℝ) ≤ n + 1)] using hbound)
    (by norm_num : 0 < (1 : ℕ))
  norm_num [abs_of_nonneg] at htrap ⊢
  convert htrap using 1
  all_goals ring

theorem shiftedTrapezoidalError_nonpos_of_below_threshold
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (n : ℕ)
    (hupper : (x + (n + 1 : ℕ)) ^ 2 ≤ 3 * y ^ 2) :
    shiftedTrapezoidalError x y n ≤ 0 := by
  have hcont : Continuous (shiftedReciprocalRealPart x y) :=
    continuous_iff_continuousAt.mpr fun t ↦
      (hasDerivAt_shiftedReciprocalRealPart (x := x) (y := y)
        (t := t) hy.ne').continuousAt
  have hconc : ConcaveOn ℝ (Icc (n : ℝ) (n + 1))
      (shiftedReciprocalRealPart x y) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      hcont.continuousOn
    · intro t ht
      exact (hasDerivAt_shiftedReciprocalRealPart
        (x := x) (y := y) (t := t) hy.ne').hasDerivWithinAt
    · intro t ht
      exact (hasDerivAt_shiftedReciprocalRealPartDeriv
        (x := x) (y := y) (t := t) hy.ne').hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Icc (n : ℝ) (n + 1) := interior_subset ht
      have ht0 : 0 ≤ t := (Nat.cast_nonneg n).trans ht'.1
      have hu : 0 ≤ x + t := add_nonneg hx ht0
      have hend : 0 ≤ x + (n + 1 : ℕ) := by positivity
      have hut : x + t ≤ x + (n + 1 : ℕ) := by
        norm_num at ht' ⊢
        linarith
      have husq : (x + t) ^ 2 ≤ (x + (n + 1 : ℕ)) ^ 2 :=
        pow_le_pow_left₀ hu hut 2
      unfold reciprocalRealPartSecondDeriv
      have hdiff : (x + t) ^ 2 - 3 * y ^ 2 ≤ 0 := by
        linarith [husq.trans hupper]
      have hnum : 2 * (x + t) * ((x + t) ^ 2 - 3 * y ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hdiff
      exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
  exact trapezoidal_error_one_nonpos_of_concaveOn
    (by norm_num : (n : ℝ) ≤ n + 1)
    (hcont.intervalIntegrable _ _) hconc

theorem one_eighth_derivDiff_le_shiftedTrapezoidalError_of_below_threshold
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (n : ℕ)
    (hupper : (x + (n + 1 : ℕ)) ^ 2 ≤ 3 * y ^ 2) :
    (1 / 8 : ℝ) *
        (reciprocalRealPartDeriv y (x + (n + 1 : ℕ)) -
          reciprocalRealPartDeriv y (x + n)) ≤
      shiftedTrapezoidalError x y n := by
  let f : ℝ → ℝ := shiftedReciprocalRealPart x y
  let f' : ℝ → ℝ := fun t ↦ reciprocalRealPartDeriv y (x + t)
  let f'' : ℝ → ℝ := fun t ↦ reciprocalRealPartSecondDeriv y (x + t)
  have hf' : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    exact hasDerivAt_shiftedReciprocalRealPart (x := x) (y := y)
      (t := t) hy.ne'
  have hf'' : ∀ t, HasDerivAt f' (f'' t) t := by
    intro t
    exact hasDerivAt_shiftedReciprocalRealPartDeriv (x := x) (y := y)
      (t := t) hy.ne'
  have hf'_int : IntervalIntegrable f' volume (n : ℝ) (n + 1) :=
    Continuous.intervalIntegrable
      (continuous_iff_continuousAt.mpr fun t ↦ (hf'' t).continuousAt) _ _
  have hf''_cont : Continuous f'' := by
    dsimp [f'', reciprocalRealPartSecondDeriv]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t
      have hden : 0 < (x + t) ^ 2 + y ^ 2 := by positivity
      exact pow_ne_zero 3 hden.ne'
  have hf''_int : IntervalIntegrable f'' volume (n : ℝ) (n + 1) :=
    hf''_cont.intervalIntegrable _ _
  have hid := trapezoidal_error_one_eq_integral_secondDerivKernel
    hf' hf'' hf'_int hf''_int
  have hf''nonpos : ∀ t ∈ Icc (n : ℝ) (n + 1), f'' t ≤ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := (Nat.cast_nonneg n).trans ht.1
    have hu : 0 ≤ x + t := add_nonneg hx ht0
    have hut : x + t ≤ x + (n + 1 : ℕ) := by
      norm_num at ht ⊢
      linarith
    have husq : (x + t) ^ 2 ≤ (x + (n + 1 : ℕ)) ^ 2 :=
      pow_le_pow_left₀ hu hut 2
    dsimp [f'', reciprocalRealPartSecondDeriv]
    have hdiff : (x + t) ^ 2 - 3 * y ^ 2 ≤ 0 := by
      linarith [husq.trans hupper]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hdiff) (by positivity)
  have hkernel : ∀ t ∈ Icc (n : ℝ) (n + 1),
      (1 / 8 : ℝ) * f'' t ≤
        ((t - n) * (n + 1 - t) / 2) * f'' t := by
    intro t ht
    have hs0 : 0 ≤ t - (n : ℝ) := sub_nonneg.mpr ht.1
    have hs1 : t - (n : ℝ) ≤ 1 := by linarith [ht.2]
    have hweight : (t - (n : ℝ)) * ((n : ℝ) + 1 - t) / 2 ≤ 1 / 8 := by
      nlinarith [sq_nonneg (t - (n : ℝ) - 1 / 2)]
    exact mul_le_mul_of_nonpos_right hweight (hf''nonpos t ht)
  have hleftInt : IntervalIntegrable (fun t ↦ (1 / 8 : ℝ) * f'' t)
      volume (n : ℝ) (n + 1) := hf''_int.const_mul _
  have hrightInt : IntervalIntegrable
      (fun t ↦ ((t - n) * (n + 1 - t) / 2) * f'' t)
      volume (n : ℝ) (n + 1) :=
    hf''_int.continuousOn_mul (by fun_prop)
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (n : ℝ) ≤ n + 1) hleftInt hrightInt hkernel
  have hderivIntegral :
      (∫ t in (n : ℝ)..(n + 1), f'' t) = f' (n + 1) - f' n := by
    exact integral_eq_sub_of_hasDerivAt (fun t _ht ↦ hf'' t) hf''_int
  rw [intervalIntegral.integral_const_mul, hderivIntegral] at hmono
  rw [show shiftedTrapezoidalError x y n =
      trapezoidal_error f 1 n (n + 1) by rfl, hid]
  simpa [f'] using hmono

theorem one_eighth_derivDiff_le_sum_shiftedTrapezoidalError
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (M : ℕ)
    (hupper : (x + M) ^ 2 ≤ 3 * y ^ 2) :
    (1 / 8 : ℝ) *
        (reciprocalRealPartDeriv y (x + M) -
          reciprocalRealPartDeriv y x) ≤
      ∑ n ∈ Finset.range M, shiftedTrapezoidalError x y n := by
  let g : ℕ → ℝ := fun n ↦ reciprocalRealPartDeriv y (x + n)
  calc
    (1 / 8 : ℝ) *
          (reciprocalRealPartDeriv y (x + M) -
            reciprocalRealPartDeriv y x) =
        ∑ n ∈ Finset.range M, (1 / 8 : ℝ) *
          (reciprocalRealPartDeriv y (x + (n + 1 : ℕ)) -
            reciprocalRealPartDeriv y (x + n)) := by
              have htel : (1 / 8 : ℝ) * (g M - g 0) =
                  ∑ n ∈ Finset.range M, (1 / 8 : ℝ) * (g (n + 1) - g n) := by
                rw [← Finset.mul_sum, Finset.sum_range_sub]
              simpa [g, Nat.cast_add, Nat.cast_one] using htel
    _ ≤ ∑ n ∈ Finset.range M,
        shiftedTrapezoidalError x y n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnM : n + 1 ≤ M := Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
      have hnMR : ((n + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnM
      have hleft : 0 ≤ x + (n + 1 : ℕ) := by positivity
      have hright : x + (n + 1 : ℕ) ≤ x + M := by
        linarith
      have hsquare : (x + (n + 1 : ℕ)) ^ 2 ≤ (x + M) ^ 2 :=
        pow_le_pow_left₀ hleft hright 2
      exact one_eighth_derivDiff_le_shiftedTrapezoidalError_of_below_threshold
        hx hy n (hsquare.trans hupper)

theorem reciprocalRealPartDeriv_lower
    {y u : ℝ} (hy : 0 < y) :
    -(1 / (8 * y ^ 2)) ≤ reciprocalRealPartDeriv y u := by
  have hden : 0 < (u ^ 2 + y ^ 2) ^ 2 := by positivity
  have hy2 : 0 < 8 * y ^ 2 := by positivity
  unfold reciprocalRealPartDeriv
  rw [← neg_div]
  rw [div_le_div_iff₀ hy2 hden]
  nlinarith [sq_nonneg (u ^ 2 - 3 * y ^ 2)]

theorem neg_nine_div_sixty_four_sq_le_sum_shiftedTrapezoidalError
    {y : ℝ} (hy : 0 < y) (M : ℕ)
    (hupper : ((1 / 4 : ℝ) + M) ^ 2 ≤ 3 * y ^ 2) :
    -(9 / (64 * y ^ 2)) ≤
      ∑ n ∈ Finset.range M,
        shiftedTrapezoidalError (1 / 4) y n := by
  have hsum := one_eighth_derivDiff_le_sum_shiftedTrapezoidalError
    (x := (1 / 4 : ℝ)) (y := y) (by norm_num) hy M hupper
  have hderivM := reciprocalRealPartDeriv_lower (y := y)
    (u := (1 / 4 : ℝ) + M) hy
  have hderivZero : reciprocalRealPartDeriv y (1 / 4) ≤ 1 / y ^ 2 := by
    unfold reciprocalRealPartDeriv
    have hden : 0 < ((1 / 4 : ℝ) ^ 2 + y ^ 2) ^ 2 := by positivity
    have hy2 : 0 < y ^ 2 := by positivity
    rw [div_le_div_iff₀ hden hy2]
    nlinarith [sq_nonneg y,
      mul_nonneg (sq_nonneg y) (sq_nonneg ((1 / 4 : ℝ) ^ 2 + y ^ 2))]
  calc
    -(9 / (64 * y ^ 2)) ≤
        (1 / 8 : ℝ) *
          (reciprocalRealPartDeriv y ((1 / 4 : ℝ) + M) -
            reciprocalRealPartDeriv y (1 / 4)) := by
              have hy2 : 0 < y ^ 2 := by positivity
              rw [← neg_div]
              calc
                (-9 : ℝ) / (64 * y ^ 2) =
                    (1 / 8 : ℝ) *
                      (-(1 / (8 * y ^ 2)) - 1 / y ^ 2) := by field_simp; ring
                _ ≤ _ := by gcongr
    _ ≤ _ := hsum

theorem tsum_one_div_six_shifted_cube_le
    {c : ℝ} (hc : 1 < c) :
    (∑' n : ℕ, 1 / (6 * (c + n) ^ 3)) ≤
      1 / (12 * (c - 1) ^ 2) := by
  let a : ℕ → ℝ := fun n ↦ 1 / (c + n - 1) ^ 2
  have hctop : Tendsto (fun n : ℕ ↦ c + (n : ℝ) - 1) atTop atTop := by
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (c - 1)
        tendsto_natCast_atTop_atTop
  have ha0 : Tendsto a atTop (nhds 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hctop
    have hsquare := hinv.pow 2
    simpa [a, one_div, inv_pow] using hsquare
  have hdiffNonneg : ∀ n, 0 ≤ a n - a (n + 1) := by
    intro n
    have hu : 0 < c + (n : ℝ) - 1 := by
      nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have huv : c + (n : ℝ) - 1 ≤ c + (n + 1 : ℕ) - 1 := by
      push_cast
      linarith
    dsimp [a]
    rw [sub_nonneg]
    gcongr
  have hdiff : HasSum (fun n ↦ a n - a (n + 1)) (a 0) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hdiffNonneg]
    have hlim := (tendsto_const_nhds (x := a 0)).sub ha0
    simpa using hlim.congr' (by
      filter_upwards [] with N
      rw [← Finset.sum_sub_distrib, Finset.sum_range_sub'])
  have hmajor : HasSum
      (fun n ↦ (1 / 12 : ℝ) * (a n - a (n + 1)))
      ((1 / 12 : ℝ) * a 0) := hdiff.mul_left _
  have hpoint : ∀ n : ℕ,
      1 / (6 * (c + n) ^ 3) ≤
        (1 / 12 : ℝ) * (a n - a (n + 1)) := by
    intro n
    have hu : 1 < c + (n : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hu0 : 0 < c + (n : ℝ) := zero_lt_one.trans hu
    have hum : 0 < c + (n : ℝ) - 1 := sub_pos.mpr hu
    dsimp [a]
    push_cast
    rw [show c + ((n : ℝ) + 1) - 1 = c + n by ring]
    field_simp
    nlinarith [sq_nonneg (c + (n : ℝ) - 1)]
  have hcubicNonneg : ∀ n : ℕ, 0 ≤ 1 / (6 * (c + n) ^ 3) := by
    intro n
    positivity
  have hcubic : Summable (fun n : ℕ ↦ 1 / (6 * (c + n) ^ 3)) :=
    hmajor.summable.of_nonneg_of_le hcubicNonneg hpoint
  have hle := Summable.tsum_le_tsum hpoint hcubic hmajor.summable
  rw [hmajor.tsum_eq] at hle
  simpa [a, mul_comm] using hle

theorem summable_one_div_six_shifted_cube
    {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ ↦ 1 / (6 * (c + n) ^ 3)) := by
  have hbase : Summable (fun n : ℕ ↦ 1 / (6 * (n : ℝ) ^ 3)) := by
    have hp : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 3) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hp.mul_left (1 / 6 : ℝ)
  apply hbase.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn : (n : ℝ) ≤ c + n := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem tsum_shiftedTrapezoidalError_nat_add_le
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (M : ℕ)
    (hc : 1 < x + M) (hthreshold : 3 * y ^ 2 ≤ (x + M) ^ 2) :
    (∑' n : ℕ, shiftedTrapezoidalError x y (n + M)) ≤
      1 / (12 * (x + M - 1) ^ 2) := by
  have herr := summable_shiftedTrapezoidalError (x := x) (y := y)
    hx hy
  have herrTail : Summable (fun n : ℕ ↦
      shiftedTrapezoidalError x y (n + M)) :=
    (summable_nat_add_iff M).2 herr
  have hcubic := summable_one_div_six_shifted_cube
    (show 0 < x + M from zero_lt_one.trans hc)
  have hpoint : ∀ n : ℕ,
      shiftedTrapezoidalError x y (n + M) ≤
        1 / (6 * ((x + M) + n) ^ 3) := by
    intro n
    have hbase : 0 ≤ x + M := (zero_lt_one.trans hc).le
    have hmono : x + M ≤ x + (n + M : ℕ) := by
      push_cast
      linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hsquare : (x + M) ^ 2 ≤ (x + (n + M : ℕ)) ^ 2 :=
      pow_le_pow_left₀ hbase hmono 2
    have habs := shifted_unit_trapezoidal_error_le_of_threshold
      hx hy (n + M) (hthreshold.trans hsquare)
    exact (le_abs_self _).trans (by
      simpa [shiftedTrapezoidalError, Nat.cast_add, add_comm,
        add_left_comm, add_assoc] using habs)
  have hle := Summable.tsum_le_tsum hpoint herrTail hcubic
  exact hle.trans (tsum_one_div_six_shifted_cube_le hc)

theorem shiftedTrapezoidalError_nonneg_of_above_threshold
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (n : ℕ)
    (hlower : 3 * y ^ 2 ≤ (x + n) ^ 2) :
    0 ≤ shiftedTrapezoidalError x y n := by
  have hcont : Continuous (shiftedReciprocalRealPart x y) :=
    continuous_iff_continuousAt.mpr fun t ↦
      (hasDerivAt_shiftedReciprocalRealPart (x := x) (y := y)
        (t := t) hy.ne').continuousAt
  have hconv : ConvexOn ℝ (Icc (n : ℝ) (n + 1))
      (shiftedReciprocalRealPart x y) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      hcont.continuousOn
    · intro t ht
      exact (hasDerivAt_shiftedReciprocalRealPart
        (x := x) (y := y) (t := t) hy.ne').hasDerivWithinAt
    · intro t ht
      exact (hasDerivAt_shiftedReciprocalRealPartDeriv
        (x := x) (y := y) (t := t) hy.ne').hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Icc (n : ℝ) (n + 1) := interior_subset ht
      have hu0 : 0 ≤ x + (n : ℝ) := by positivity
      have hut : x + (n : ℝ) ≤ x + t := by linarith [ht'.1]
      have hu : 0 ≤ x + t := hu0.trans hut
      have husq : (x + (n : ℝ)) ^ 2 ≤ (x + t) ^ 2 :=
        pow_le_pow_left₀ hu0 hut 2
      unfold reciprocalRealPartSecondDeriv
      have hdiff : 0 ≤ (x + t) ^ 2 - 3 * y ^ 2 := by
        linarith [hlower.trans husq]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu) hdiff)
        (pow_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) 3)
  exact trapezoidal_error_one_nonneg_of_convexOn
    (by norm_num : (n : ℝ) ≤ n + 1)
    (hcont.intervalIntegrable _ _) hconv

theorem tsum_shiftedTrapezoidalError_lower_of_crossing
    {y : ℝ} (hy : 0 < y) (M : ℕ)
    (hbelow : ((1 / 4 : ℝ) + M) ^ 2 ≤ 3 * y ^ 2)
    (habove : 3 * y ^ 2 ≤ ((1 / 4 : ℝ) + (M + 1 : ℕ)) ^ 2) :
    -(9 / (64 * y ^ 2)) - 1 / (6 * y ^ 3) ≤
      ∑' n : ℕ, shiftedTrapezoidalError (1 / 4) y n := by
  let e : ℕ → ℝ := shiftedTrapezoidalError (1 / 4) y
  have he : Summable e := summable_shiftedTrapezoidalError (by norm_num) hy
  have hsplit := he.sum_add_tsum_nat_add (M + 1)
  have hhead := neg_nine_div_sixty_four_sq_le_sum_shiftedTrapezoidalError
    hy M hbelow
  have hcrossAbs := shifted_unit_trapezoidal_error_le_global
    (x := (1 / 4 : ℝ)) hy M
  have hcross : -(1 / (6 * y ^ 3)) ≤ e M :=
    neg_le_of_abs_le hcrossAbs
  have htailTerm : ∀ n : ℕ, 0 ≤ e (n + (M + 1)) := by
    intro n
    have hbase : 0 ≤ (1 / 4 : ℝ) + (M + 1 : ℕ) := by positivity
    have hmono : (1 / 4 : ℝ) + (M + 1 : ℕ) ≤
        (1 / 4 : ℝ) + (n + (M + 1) : ℕ) := by
      push_cast
      linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hsquare := pow_le_pow_left₀ hbase hmono 2
    exact shiftedTrapezoidalError_nonneg_of_above_threshold
      (by norm_num) hy (n + (M + 1)) (habove.trans hsquare)
  have htail : 0 ≤ ∑' n : ℕ, e (n + (M + 1)) := tsum_nonneg htailTerm
  rw [Finset.sum_range_succ] at hsplit
  linarith

theorem tsum_shiftedTrapezoidalError_upper_of_crossing
    {y : ℝ} (hy : 0 < y) (M : ℕ)
    (hbelow : ((1 / 4 : ℝ) + M) ^ 2 ≤ 3 * y ^ 2)
    (habove : 3 * y ^ 2 ≤ ((1 / 4 : ℝ) + (M + 1 : ℕ)) ^ 2) :
    (∑' n : ℕ, shiftedTrapezoidalError (1 / 4) y n) ≤
      1 / (6 * y ^ 3) +
        1 / (12 * ((1 / 4 : ℝ) + (M + 1 : ℕ) - 1) ^ 2) := by
  let e : ℕ → ℝ := shiftedTrapezoidalError (1 / 4) y
  have he : Summable e := summable_shiftedTrapezoidalError (by norm_num) hy
  have hsplit := he.sum_add_tsum_nat_add (M + 1)
  have hhead : ∑ n ∈ Finset.range M, e n ≤ 0 := by
    apply Finset.sum_nonpos
    intro n hn
    have hnM : n + 1 ≤ M := Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
    have hleft : 0 ≤ (1 / 4 : ℝ) + (n + 1 : ℕ) := by positivity
    have hright : (1 / 4 : ℝ) + (n + 1 : ℕ) ≤
        (1 / 4 : ℝ) + M := by
      have hnMR : ((n + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hnM
      linarith
    have hsquare := pow_le_pow_left₀ hleft hright 2
    exact shiftedTrapezoidalError_nonpos_of_below_threshold
      (by norm_num) hy n (hsquare.trans hbelow)
  have hcrossAbs := shifted_unit_trapezoidal_error_le_global
    (x := (1 / 4 : ℝ)) hy M
  have hcross : e M ≤ 1 / (6 * y ^ 3) :=
    (le_abs_self _).trans hcrossAbs
  have hMone : (1 : ℝ) ≤ (M + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  have hc : 1 < (1 / 4 : ℝ) + (M + 1 : ℕ) := by linarith
  have htail := tsum_shiftedTrapezoidalError_nat_add_le
    (x := (1 / 4 : ℝ)) (y := y) (by norm_num) hy (M + 1) hc habove
  rw [Finset.sum_range_succ] at hsplit
  linarith

end ArithmeticHodge.Analysis.DigammaTrapezoidBounds
