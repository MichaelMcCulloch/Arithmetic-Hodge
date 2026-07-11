import ArithmeticHodge.Analysis.MultiplicativeWeilDigamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Analysis.PSeries

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Set MeasureTheory intervalIntegral Filter

namespace ArithmeticHodge.Analysis.DigammaTrapezoid

def reciprocalRealPart (y u : ℝ) : ℝ :=
  u / (u ^ 2 + y ^ 2)

def reciprocalRealPartDeriv (y u : ℝ) : ℝ :=
  (y ^ 2 - u ^ 2) / (u ^ 2 + y ^ 2) ^ 2

def reciprocalRealPartSecondDeriv (y u : ℝ) : ℝ :=
  2 * u * (u ^ 2 - 3 * y ^ 2) / (u ^ 2 + y ^ 2) ^ 3

def shiftedReciprocalRealPart (x y t : ℝ) : ℝ :=
  reciprocalRealPart y (x + t)

def shiftedTrapezoidalError (x y : ℝ) (n : ℕ) : ℝ :=
  trapezoidal_error (shiftedReciprocalRealPart x y) 1 n (n + 1)

def shiftedReciprocalPrimitive (x y t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((x + t) ^ 2 + y ^ 2)

def quarterDigammaSeriesTerm (v : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹ -
    shiftedReciprocalRealPart (1 / 4) (v / 2) (n + 1)

def quarterDigammaPartialApprox (v : ℝ) (N : ℕ) : ℝ :=
  -Real.eulerMascheroniConstant -
    shiftedReciprocalRealPart (1 / 4) (v / 2) 0 +
      ∑ n ∈ Finset.range N, quarterDigammaSeriesTerm v n

theorem bombieriDigammaKernel_eq_shiftedReciprocalRealPart
    (k : ℕ) (v : ℝ) :
    MultiplicativeWeil.bombieriDigammaKernel k v =
      shiftedReciprocalRealPart (1 / 4) (v / 2) k := by
  unfold MultiplicativeWeil.bombieriDigammaKernel
    shiftedReciprocalRealPart reciprocalRealPart
  norm_num
  field_simp
  ring

private theorem one_div_quarter_vertical_add_nat_re
    (k : ℕ) (v : ℝ) :
    ((1 : ℂ) /
      ((1 / 4 : ℝ) + (v / 2) * Complex.I + k)).re =
        shiftedReciprocalRealPart (1 / 4) (v / 2) k := by
  rw [← bombieriDigammaKernel_eq_shiftedReciprocalRealPart]
  let z : ℂ := (1 / 4 : ℝ) + (v / 2) * Complex.I + k
  change ((1 : ℂ) / z).re = _
  have hre : z.re = 1 / 4 + k := by simp [z]
  have him : z.im = v / 2 := by simp [z]
  rw [Complex.div_re, Complex.normSq_apply, hre, him]
  unfold MultiplicativeWeil.bombieriDigammaKernel
  simp only [Complex.one_re, Complex.one_im, zero_mul]
  field_simp
  ring

theorem summable_quarterDigammaSeriesTerm (v : ℝ) :
    Summable (quarterDigammaSeriesTerm v) := by
  let z : ℂ := (1 / 4 : ℝ) + (v / 2) * Complex.I
  have hzre : 0 ≤ z.re := by simp [z]
  have hs := summable_digamma_partialFraction_of_nonneg_re z hzre
  have hre : Summable (fun n : ℕ ↦
      Complex.reCLM ((1 : ℂ) / (z + (n + 1 : ℕ)) -
        1 / (n + 1 : ℕ))) := by
    simpa only [Function.comp_apply] using
      hs.map Complex.reCLM Complex.reCLM.continuous
  have hkernel : Summable (fun n : ℕ ↦
      shiftedReciprocalRealPart (1 / 4) (v / 2) (n + 1) -
        ((n + 1 : ℕ) : ℝ)⁻¹) := by
    refine hre.congr ?_
    intro n
    change (((1 : ℂ) / (z + (n + 1 : ℕ)) -
      1 / (n + 1 : ℕ)).re) = _
    rw [Complex.sub_re]
    rw [show ((1 : ℂ) / (z + (n + 1 : ℕ))).re =
        shiftedReciprocalRealPart (1 / 4) (v / 2) (n + 1) by
      simpa only [z, Nat.cast_add, Nat.cast_one] using
        one_div_quarter_vertical_add_nat_re (n + 1) v]
    congr 1
    rw [show ((n + 1 : ℕ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) by
      norm_cast]
    rw [one_div, ← Complex.ofReal_inv]
    simp
    rw [Complex.normSq_apply]
    norm_num
  simpa only [quarterDigammaSeriesTerm, neg_sub] using hkernel.neg

theorem digamma_quarter_vertical_re_eq_trapezoid_series
    (v : ℝ) :
    (Complex.digamma ((1 / 4 : ℝ) +
        (v / 2) * Complex.I)).re =
      -Real.eulerMascheroniConstant -
        shiftedReciprocalRealPart (1 / 4) (v / 2) 0 +
          ∑' n : ℕ, quarterDigammaSeriesTerm v n := by
  rw [MultiplicativeWeil.digamma_quarter_vertical_re_eq]
  rw [bombieriDigammaKernel_eq_shiftedReciprocalRealPart]
  have htsum :
      (∑' n : ℕ,
        (MultiplicativeWeil.bombieriDigammaKernel (n + 1) v -
          ((n : ℝ) + 1)⁻¹)) =
        -∑' n : ℕ, quarterDigammaSeriesTerm v n := by
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    rw [bombieriDigammaKernel_eq_shiftedReciprocalRealPart]
    unfold quarterDigammaSeriesTerm
    push_cast
    ring
  rw [htsum]
  ring

theorem tendsto_quarterDigammaPartialApprox (v : ℝ) :
    Tendsto (quarterDigammaPartialApprox v) atTop
      (nhds (Complex.digamma ((1 / 4 : ℝ) +
        (v / 2) * Complex.I)).re) := by
  have hsum := (summable_quarterDigammaSeriesTerm v).hasSum.tendsto_sum_nat
  rw [digamma_quarter_vertical_re_eq_trapezoid_series]
  change Tendsto
    (fun N : ℕ ↦
      (-Real.eulerMascheroniConstant -
        shiftedReciprocalRealPart (1 / 4) (v / 2) 0) +
          ∑ n ∈ Finset.range N, quarterDigammaSeriesTerm v n)
    atTop
    (nhds ((-Real.eulerMascheroniConstant -
      shiftedReciprocalRealPart (1 / 4) (v / 2) 0) +
        ∑' n : ℕ, quarterDigammaSeriesTerm v n))
  exact tendsto_const_nhds.add hsum

theorem quarterDigammaPartialApprox_eq_harmonic_sub_sum
    (v : ℝ) (N : ℕ) :
    quarterDigammaPartialApprox v N =
      (harmonic N : ℝ) - Real.eulerMascheroniConstant -
        ∑ k ∈ Finset.range (N + 1),
          shiftedReciprocalRealPart (1 / 4) (v / 2) k := by
  rw [quarterDigammaPartialApprox, harmonic]
  push_cast
  simp only [quarterDigammaSeriesTerm]
  rw [Finset.sum_sub_distrib]
  have hshift :
      (∑ n ∈ Finset.range N,
          shiftedReciprocalRealPart (1 / 4) (v / 2) (n + 1)) =
        (∑ k ∈ Finset.range (N + 1),
          shiftedReciprocalRealPart (1 / 4) (v / 2) k) -
            shiftedReciprocalRealPart (1 / 4) (v / 2) 0 := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hshift]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem tendsto_shiftedReciprocalRealPart_nat
    (x y : ℝ) :
    Tendsto (fun N : ℕ ↦ shiftedReciprocalRealPart x y N)
      atTop (nhds 0) := by
  have hinv : Tendsto (fun N : ℕ ↦ ((N : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hx : Tendsto (fun N : ℕ ↦ 1 + x * (N : ℝ)⁻¹)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hy : Tendsto (fun N : ℕ ↦ y * (N : ℝ)⁻¹)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hinv
  have hden : Tendsto
      (fun N : ℕ ↦ (1 + x * (N : ℝ)⁻¹) ^ 2 +
        (y * (N : ℝ)⁻¹) ^ 2) atTop (nhds 1) := by
    simpa using (hx.pow 2).add (hy.pow 2)
  have hlim : Tendsto
      (fun N : ℕ ↦
        ((N : ℝ)⁻¹ * (1 + x * (N : ℝ)⁻¹)) /
          ((1 + x * (N : ℝ)⁻¹) ^ 2 +
            (y * (N : ℝ)⁻¹) ^ 2)) atTop (nhds 0) := by
    simpa using (hinv.mul hx).div hden (by norm_num : (1 : ℝ) ≠ 0)
  apply hlim.congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  unfold shiftedReciprocalRealPart reciprocalRealPart
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp
  ring

theorem tendsto_shiftedReciprocalPrimitive_sub_log_nat
    (x y : ℝ) :
    Tendsto (fun N : ℕ ↦
      shiftedReciprocalPrimitive x y N - Real.log N)
      atTop (nhds 0) := by
  have hinv : Tendsto (fun N : ℕ ↦ ((N : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hx : Tendsto (fun N : ℕ ↦ 1 + x * (N : ℝ)⁻¹)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hy : Tendsto (fun N : ℕ ↦ y * (N : ℝ)⁻¹)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hinv
  have hinside : Tendsto
      (fun N : ℕ ↦ (1 + x * (N : ℝ)⁻¹) ^ 2 +
        (y * (N : ℝ)⁻¹) ^ 2) atTop (nhds 1) := by
    simpa using (hx.pow 2).add (hy.pow 2)
  have hlog : Tendsto
      (fun N : ℕ ↦ Real.log
        ((1 + x * (N : ℝ)⁻¹) ^ 2 +
          (y * (N : ℝ)⁻¹) ^ 2)) atTop (nhds 0) := by
    simpa using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hinside
  have hlim : Tendsto
      (fun N : ℕ ↦ (1 / 2 : ℝ) * Real.log
        ((1 + x * (N : ℝ)⁻¹) ^ 2 +
          (y * (N : ℝ)⁻¹) ^ 2)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlog
  apply hlim.congr'
  have hxtop : Tendsto (fun N : ℕ ↦ x + (N : ℝ)) atTop atTop := by
    simpa [add_comm] using
      tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ne_atTop 0,
    hxtop.eventually (eventually_gt_atTop 0)] with N hN hxN
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have harg : 0 < (x + (N : ℝ)) ^ 2 + y ^ 2 := by positivity
  unfold shiftedReciprocalPrimitive
  symm
  calc
    (1 / 2 : ℝ) * Real.log ((x + (N : ℝ)) ^ 2 + y ^ 2) -
          Real.log (N : ℝ) =
        (1 / 2 : ℝ) *
          (Real.log ((x + (N : ℝ)) ^ 2 + y ^ 2) -
            Real.log ((N : ℝ) ^ 2)) := by
              rw [Real.log_pow]
              norm_num
              ring
    _ = (1 / 2 : ℝ) * Real.log
          (((x + (N : ℝ)) ^ 2 + y ^ 2) / (N : ℝ) ^ 2) := by
            rw [Real.log_div harg.ne' (pow_ne_zero 2 hNR)]
    _ = (1 / 2 : ℝ) * Real.log
          ((1 + x * (N : ℝ)⁻¹) ^ 2 +
            (y * (N : ℝ)⁻¹) ^ 2) := by
              congr 2
              field_simp
              ring

theorem tendsto_harmonic_sub_euler_sub_shiftedPrimitive
    (x y : ℝ) :
    Tendsto (fun N : ℕ ↦
      (harmonic N : ℝ) - Real.eulerMascheroniConstant -
        shiftedReciprocalPrimitive x y N) atTop (nhds 0) := by
  have hh : Tendsto (fun N : ℕ ↦
      (harmonic N : ℝ) - Real.log N -
        Real.eulerMascheroniConstant) atTop (nhds 0) := by
    simpa using Real.tendsto_harmonic_sub_log.sub
      (tendsto_const_nhds (x := Real.eulerMascheroniConstant))
  have hp := tendsto_shiftedReciprocalPrimitive_sub_log_nat x y
  have h := hh.sub hp
  convert h using 1
  · funext N
    ring
  · ring

theorem hasDerivAt_reciprocalRealPart
    {y u : ℝ} (hy : y ≠ 0) :
    HasDerivAt (reciprocalRealPart y) (reciprocalRealPartDeriv y u) u := by
  have hden : u ^ 2 + y ^ 2 ≠ 0 := by positivity
  convert (hasDerivAt_id u).div
    ((hasDerivAt_id u).pow 2 |>.add_const (y ^ 2)) hden using 1
  simp [reciprocalRealPartDeriv]
  field_simp
  ring

theorem hasDerivAt_reciprocalRealPartDeriv
    {y u : ℝ} (hy : y ≠ 0) :
    HasDerivAt (reciprocalRealPartDeriv y)
      (reciprocalRealPartSecondDeriv y u) u := by
  have hden : u ^ 2 + y ^ 2 ≠ 0 := by positivity
  convert
    (((hasDerivAt_const u (y ^ 2)).sub ((hasDerivAt_id u).pow 2)).div
      (((hasDerivAt_id u).pow 2 |>.add_const (y ^ 2)).pow 2)
      (pow_ne_zero 2 hden)) using 1
  simp [reciprocalRealPartSecondDeriv]
  field_simp
  ring

theorem hasDerivAt_shiftedReciprocalPrimitive
    {x y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (shiftedReciprocalPrimitive x y)
      (shiftedReciprocalRealPart x y t) t := by
  have hden : (x + t) ^ 2 + y ^ 2 ≠ 0 := by positivity
  have hinner : HasDerivAt (fun s : ℝ ↦ (x + s) ^ 2 + y ^ 2)
      (2 * (x + t)) t := by
    convert (((hasDerivAt_const t x).add (hasDerivAt_id t)).pow 2).add_const
      (y ^ 2) using 1
    all_goals simp
  have hlog := hinner.log hden
  convert hlog.const_mul (1 / 2 : ℝ) using 1
  unfold shiftedReciprocalRealPart reciprocalRealPart
  field_simp

theorem integral_shiftedReciprocalRealPart
    {x y a b : ℝ} (hy : y ≠ 0) :
    (∫ t in a..b, shiftedReciprocalRealPart x y t) =
      shiftedReciprocalPrimitive x y b -
        shiftedReciprocalPrimitive x y a := by
  apply integral_eq_sub_of_hasDerivAt
  · intro t _ht
    exact hasDerivAt_shiftedReciprocalPrimitive hy
  · have hcont : Continuous (shiftedReciprocalRealPart x y) := by
      unfold shiftedReciprocalRealPart reciprocalRealPart
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro t
        have : 0 < (x + t) ^ 2 + y ^ 2 := by positivity
        exact this.ne'
    exact hcont.intervalIntegrable a b

theorem shiftedTrapezoidalError_eq
    {x y : ℝ} (hy : y ≠ 0) (n : ℕ) :
    shiftedTrapezoidalError x y n =
      (shiftedReciprocalRealPart x y n +
          shiftedReciprocalRealPart x y (n + 1)) / 2 -
        (shiftedReciprocalPrimitive x y (n + 1) -
          shiftedReciprocalPrimitive x y n) := by
  rw [shiftedTrapezoidalError, trapezoidal_error,
    trapezoidal_integral_one,
    integral_shiftedReciprocalRealPart hy]
  norm_num
  ring

private theorem mul_abs_sq_sub_three_le (r : ℝ) (hr : 0 ≤ r) :
    r * |r ^ 2 - 3| ≤ (r ^ 2 + 1) ^ 3 := by
  by_cases hsmall : r ^ 2 ≤ 3
  · rw [abs_of_nonpos (sub_nonpos.mpr hsmall)]
    have hr3 : 0 ≤ r ^ 3 := by positivity
    have hsquare : 0 ≤ (2 * r - 1) ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (r ^ 2), sq_nonneg (r ^ 2 + 1)]
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hsmall))]
    have hrle : r ≤ r ^ 2 + 1 := by
      nlinarith [sq_nonneg (r - 1 / 2)]
    have hcube := pow_le_pow_left₀ hr hrle 3
    nlinarith [mul_nonneg hr (sub_nonneg.mpr (le_of_not_ge hsmall))]

private theorem scaled_second_derivative_polynomial
    {y u : ℝ} (hy : 0 < y) (hu : 0 ≤ u) :
    u * y ^ 3 * |u ^ 2 - 3 * y ^ 2| ≤
      (u ^ 2 + y ^ 2) ^ 3 := by
  let r : ℝ := u / y
  have hr : 0 ≤ r := div_nonneg hu hy.le
  have hdim := mul_abs_sq_sub_three_le r hr
  have hy2 : 0 < y ^ 2 := by positivity
  have hy6 : 0 < y ^ 6 := by positivity
  have hrSq : r ^ 2 - 3 = (u ^ 2 - 3 * y ^ 2) / y ^ 2 := by
    dsimp [r]
    field_simp
  rw [hrSq, abs_div, abs_of_pos hy2] at hdim
  have hscaled := mul_le_mul_of_nonneg_right hdim hy6.le
  dsimp [r] at hscaled
  field_simp at hscaled
  simpa [mul_comm] using hscaled

theorem abs_reciprocalRealPartSecondDeriv_le_two_div_cube
    {y u : ℝ} (hy : 0 < y) (hu : 0 ≤ u) :
    |reciprocalRealPartSecondDeriv y u| ≤ 2 / y ^ 3 := by
  have hden : 0 < u ^ 2 + y ^ 2 := by positivity
  have hy3 : 0 < y ^ 3 := by positivity
  rw [reciprocalRealPartSecondDeriv, abs_div,
    abs_of_pos (pow_pos hden 3), abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 * u)]
  rw [div_le_div_iff₀ (pow_pos hden 3) hy3]
  have hpoly := scaled_second_derivative_polynomial hy hu
  nlinarith

theorem abs_reciprocalRealPartSecondDeriv_le_two_div_cube_global
    {y u : ℝ} (hy : 0 < y) :
    |reciprocalRealPartSecondDeriv y u| ≤ 2 / y ^ 3 := by
  by_cases hu : 0 ≤ u
  · exact abs_reciprocalRealPartSecondDeriv_le_two_div_cube hy hu
  · have h := abs_reciprocalRealPartSecondDeriv_le_two_div_cube
      (y := y) (u := -u) hy (neg_nonneg.mpr (le_of_not_ge hu))
    have heq :
        reciprocalRealPartSecondDeriv y (-u) =
          -reciprocalRealPartSecondDeriv y u := by
      unfold reciprocalRealPartSecondDeriv
      ring
    rw [heq, abs_neg] at h
    exact h

theorem abs_reciprocalRealPartSecondDeriv_le_two_div_cube_of_threshold
    {y u : ℝ} (hu : 0 < u) (hthreshold : 3 * y ^ 2 ≤ u ^ 2) :
    |reciprocalRealPartSecondDeriv y u| ≤ 2 / u ^ 3 := by
  have hden : 0 < u ^ 2 + y ^ 2 := by positivity
  have hu3 : 0 < u ^ 3 := by positivity
  have hdiff : 0 ≤ u ^ 2 - 3 * y ^ 2 := sub_nonneg.mpr hthreshold
  rw [reciprocalRealPartSecondDeriv, abs_div,
    abs_of_pos (pow_pos hden 3), abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 * u), abs_of_nonneg hdiff]
  have hnum : 2 * u * (u ^ 2 - 3 * y ^ 2) ≤ 2 * u ^ 3 := by
    nlinarith [sq_nonneg y]
  have hdenPow : u ^ 6 ≤ (u ^ 2 + y ^ 2) ^ 3 := by
    nlinarith [sq_nonneg y, sq_nonneg (u ^ 2 + y ^ 2),
      mul_nonneg (sq_nonneg y) (sq_nonneg (u ^ 2 + y ^ 2))]
  calc
    2 * u * (u ^ 2 - 3 * y ^ 2) / (u ^ 2 + y ^ 2) ^ 3 ≤
        2 * u ^ 3 / (u ^ 2 + y ^ 2) ^ 3 := by
      exact div_le_div_of_nonneg_right hnum (pow_nonneg hden.le 3)
    _ ≤ 2 * u ^ 3 / u ^ 6 := by
      exact div_le_div_of_nonneg_left (by positivity)
        (by positivity) hdenPow
    _ = 2 / u ^ 3 := by field_simp

private theorem reciprocalRealPart_contDiff
    {y : ℝ} (hy : y ≠ 0) :
    ContDiff ℝ 2 (reciprocalRealPart y) := by
  unfold reciprocalRealPart
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · intro x
    have : 0 < x ^ 2 + y ^ 2 := by positivity
    exact this.ne'

private theorem iteratedDeriv_two_reciprocalRealPart
    {y u : ℝ} (hy : y ≠ 0) :
    iteratedDeriv 2 (reciprocalRealPart y) u =
      reciprocalRealPartSecondDeriv y u := by
  have hfirst :
      deriv (reciprocalRealPart y) = reciprocalRealPartDeriv y := by
    funext t
    exact (hasDerivAt_reciprocalRealPart (u := t) hy).deriv
  have hsecond :
      deriv (reciprocalRealPartDeriv y) =
        reciprocalRealPartSecondDeriv y := by
    funext t
    exact (hasDerivAt_reciprocalRealPartDeriv (u := t) hy).deriv
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ',
    show (1 : ℕ) = 0 + 1 by omega, iteratedDeriv_succ',
    iteratedDeriv_zero, hfirst, hsecond]

private theorem shiftedReciprocalRealPart_contDiff
    {x y : ℝ} (hy : y ≠ 0) :
    ContDiff ℝ 2 (shiftedReciprocalRealPart x y) := by
  have hbase := reciprocalRealPart_contDiff hy
  change ContDiff ℝ 2 (fun t ↦ reciprocalRealPart y (x + t))
  exact hbase.comp (contDiff_const.add contDiff_id)

private theorem iteratedDeriv_two_shiftedReciprocalRealPart
    {x y t : ℝ} (hy : y ≠ 0) :
    iteratedDeriv 2 (shiftedReciprocalRealPart x y) t =
      reciprocalRealPartSecondDeriv y (x + t) := by
  change iteratedDeriv 2 (fun z ↦ reciprocalRealPart y (x + z)) t = _
  rw [show iteratedDeriv 2 (fun z ↦ reciprocalRealPart y (x + z)) t =
      iteratedDeriv 2 (reciprocalRealPart y) (x + t) by
    exact congr_fun
      (iteratedDeriv_comp_const_add 2 (reciprocalRealPart y) x) t]
  exact iteratedDeriv_two_reciprocalRealPart hy

theorem unit_trapezoidal_error_le
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    |trapezoidal_error (reciprocalRealPart y) 1 n (n + 1)| ≤
      1 / (6 * y ^ 3) := by
  have hcont := reciprocalRealPart_contDiff hy.ne'
  have hbound : ∀ x,
      |iteratedDerivWithin 2 (reciprocalRealPart y)
          (Icc (n : ℝ) (n + 1)) x| ≤ 2 / y ^ 3 := by
    intro x
    by_cases hx : x ∈ Icc (n : ℝ) (n + 1)
    · rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (by norm_num : (n : ℝ) < n + 1))
        hcont.contDiffAt hx,
        iteratedDeriv_two_reciprocalRealPart hy.ne']
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

theorem shifted_unit_trapezoidal_error_le_of_threshold
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ)
    (hthreshold : 3 * y ^ 2 ≤ (x + n) ^ 2) :
    |trapezoidal_error (shiftedReciprocalRealPart x y)
        1 n (n + 1)| ≤ 1 / (6 * (x + n) ^ 3) := by
  have hcont := shiftedReciprocalRealPart_contDiff (x := x) hy.ne'
  have hxn : 0 < x + n := by positivity
  have hbound : ∀ t,
      |iteratedDerivWithin 2 (shiftedReciprocalRealPart x y)
          (Icc (n : ℝ) (n + 1)) t| ≤ 2 / (x + n) ^ 3 := by
    intro t
    by_cases ht : t ∈ Icc (n : ℝ) (n + 1)
    · rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (by norm_num : (n : ℝ) < n + 1))
        hcont.contDiffAt ht,
        iteratedDeriv_two_shiftedReciprocalRealPart hy.ne']
      have hnt : (n : ℝ) ≤ t := ht.1
      have hxnt : x + n ≤ x + t := by linarith
      have hxt : 0 < x + t := hxn.trans_le hxnt
      have hsq : (x + n) ^ 2 ≤ (x + t) ^ 2 := by
        exact pow_le_pow_left₀ hxn.le hxnt 2
      have hlocal :=
        abs_reciprocalRealPartSecondDeriv_le_two_div_cube_of_threshold
          hxt (hthreshold.trans hsq)
      exact hlocal.trans (by gcongr)
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

theorem sum_range_shiftedTrapezoidalError
    {x y : ℝ} (hy : y ≠ 0) (N : ℕ) :
    (∑ n ∈ Finset.range N, shiftedTrapezoidalError x y n) =
      trapezoidal_error (shiftedReciprocalRealPart x y) N 0 N := by
  cases N with
  | zero => simp [shiftedTrapezoidalError]
  | succ N =>
      have hcont :=
        (shiftedReciprocalRealPart_contDiff (x := x) hy).continuous
      have hint : IntervalIntegrable (shiftedReciprocalRealPart x y)
          volume 0 (0 + ((N + 1 : ℕ) : ℝ) * 1) :=
        hcont.intervalIntegrable _ _
      have hsum :
          (∑ i ∈ Finset.range (N + 1),
            trapezoidal_error (shiftedReciprocalRealPart x y) 1
              (0 + i * 1) (0 + (i + 1) * 1)) =
            trapezoidal_error (shiftedReciprocalRealPart x y) (N + 1)
              0 (0 + ((N + 1 : ℕ) : ℝ) * 1) :=
        sum_trapezoidal_error_adjacent_intervals
          (f := shiftedReciprocalRealPart x y)
          (a := 0) (h := 1) (N := N + 1)
          (Nat.succ_pos N) hint
      simpa [shiftedTrapezoidalError] using hsum

theorem trapezoidal_error_zero_nat_eq
    {x y : ℝ} (hy : y ≠ 0) {N : ℕ} (hN : 0 < N) :
    trapezoidal_error (shiftedReciprocalRealPart x y) N 0 N =
      (∑ k ∈ Finset.range (N + 1),
          shiftedReciprocalRealPart x y k) -
        (shiftedReciprocalRealPart x y 0 +
          shiftedReciprocalRealPart x y N) / 2 -
        (shiftedReciprocalPrimitive x y N -
          shiftedReciprocalPrimitive x y 0) := by
  rw [trapezoidal_error, trapezoidal_integral,
    integral_shiftedReciprocalRealPart hy]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show ((N : ℝ) - 0) / N = 1 by
    field_simp
    ring]
  simp only [zero_add, one_mul]
  have harg (k : ℕ) :
      ((k : ℝ) + 1) * ((N : ℝ) - 0) / N = (k + 1 : ℕ) := by
    push_cast
    field_simp
    ring
  simp_rw [harg]
  have hNsplit : N - 1 + 1 = N := by omega
  have hprefix :
      (∑ k ∈ Finset.range N,
          shiftedReciprocalRealPart x y k) =
        shiftedReciprocalRealPart x y 0 +
          ∑ k ∈ Finset.range (N - 1),
            shiftedReciprocalRealPart x y (k + 1) := by
    calc
      (∑ k ∈ Finset.range N,
          shiftedReciprocalRealPart x y k) =
          ∑ k ∈ Finset.range (N - 1 + 1),
            shiftedReciprocalRealPart x y k := by rw [hNsplit]
      _ = _ := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_add, Nat.cast_one]
        ring
  have hsum :
      (∑ k ∈ Finset.range (N + 1),
          shiftedReciprocalRealPart x y k) =
        shiftedReciprocalRealPart x y 0 +
          (∑ k ∈ Finset.range (N - 1),
            shiftedReciprocalRealPart x y (k + 1)) +
          shiftedReciprocalRealPart x y N := by
    rw [Finset.sum_range_succ, hprefix]
  rw [hsum]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem quarterDigammaPartialApprox_eq_trapezoidal_decomposition
    (v : ℝ) (hv : v ≠ 0) {N : ℕ} (hN : 0 < N) :
    quarterDigammaPartialApprox v N =
      ((harmonic N : ℝ) - Real.eulerMascheroniConstant -
          shiftedReciprocalPrimitive (1 / 4) (v / 2) N) +
        shiftedReciprocalPrimitive (1 / 4) (v / 2) 0 -
        (shiftedReciprocalRealPart (1 / 4) (v / 2) 0 +
          shiftedReciprocalRealPart (1 / 4) (v / 2) N) / 2 -
        ∑ n ∈ Finset.range N,
          shiftedTrapezoidalError (1 / 4) (v / 2) n := by
  rw [quarterDigammaPartialApprox_eq_harmonic_sub_sum]
  have hv2 : v / 2 ≠ 0 := div_ne_zero hv (by norm_num)
  rw [sum_range_shiftedTrapezoidalError hv2]
  rw [trapezoidal_error_zero_nat_eq hv2 hN]
  ring

theorem summable_shiftedTrapezoidalError
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Summable (shiftedTrapezoidalError x y) := by
  have hbase : Summable (fun n : ℕ ↦ 1 / (6 * (n : ℝ) ^ 3)) := by
    have hp : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 3) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hp.mul_left (1 / 6 : ℝ)
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (3 * y ^ 2))
  apply hbase.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnR : max 1 (3 * y ^ 2) ≤ (n : ℝ) :=
    hN.trans (by exact_mod_cast hn)
  have hnOne : (1 : ℝ) ≤ n := (le_max_left _ _).trans hnR
  have hnPos : (0 : ℝ) < n := zero_lt_one.trans_le hnOne
  have hnY : 3 * y ^ 2 ≤ (n : ℝ) := (le_max_right _ _).trans hnR
  have hnx : (n : ℝ) ≤ x + n := by linarith
  have hxnOne : 1 ≤ x + n := hnOne.trans hnx
  have hthreshold : 3 * y ^ 2 ≤ (x + n) ^ 2 := by
    have hlin : 3 * y ^ 2 ≤ x + n := hnY.trans hnx
    nlinarith [sq_nonneg (x + n - 1)]
  have herr := shifted_unit_trapezoidal_error_le_of_threshold
    hx hy n hthreshold
  rw [Real.norm_eq_abs]
  exact herr.trans (by
    have hxnPos : 0 < x + n := zero_lt_one.trans_le hxnOne
    gcongr)

theorem digamma_quarter_vertical_re_eq_primitive_sub_trapezoidalErrors
    {v : ℝ} (hv : 0 < v) :
    (Complex.digamma ((1 / 4 : ℝ) +
        (v / 2) * Complex.I)).re =
      shiftedReciprocalPrimitive (1 / 4) (v / 2) 0 -
        shiftedReciprocalRealPart (1 / 4) (v / 2) 0 / 2 -
        ∑' n : ℕ, shiftedTrapezoidalError (1 / 4) (v / 2) n := by
  have hmain := tendsto_quarterDigammaPartialApprox v
  have hzero := tendsto_harmonic_sub_euler_sub_shiftedPrimitive
    (1 / 4) (v / 2)
  have htail := tendsto_shiftedReciprocalRealPart_nat (1 / 4) (v / 2)
  have hendpoint : Tendsto (fun N : ℕ ↦
      (shiftedReciprocalRealPart (1 / 4) (v / 2) 0 +
        shiftedReciprocalRealPart (1 / 4) (v / 2) N) / 2)
      atTop (nhds (shiftedReciprocalRealPart (1 / 4) (v / 2) 0 / 2)) := by
    simpa using
      (tendsto_const_nhds.add htail).div_const (2 : ℝ)
  have herrSummable : Summable
      (shiftedTrapezoidalError (1 / 4) (v / 2)) :=
    summable_shiftedTrapezoidalError (by norm_num) (by positivity)
  have herr := herrSummable.hasSum.tendsto_sum_nat
  have hdecomp : Tendsto (fun N : ℕ ↦
      (((harmonic N : ℝ) - Real.eulerMascheroniConstant -
          shiftedReciprocalPrimitive (1 / 4) (v / 2) N) +
        shiftedReciprocalPrimitive (1 / 4) (v / 2) 0) -
        (shiftedReciprocalRealPart (1 / 4) (v / 2) 0 +
          shiftedReciprocalRealPart (1 / 4) (v / 2) N) / 2 -
        ∑ n ∈ Finset.range N,
          shiftedTrapezoidalError (1 / 4) (v / 2) n)
      atTop (nhds
        (shiftedReciprocalPrimitive (1 / 4) (v / 2) 0 -
          shiftedReciprocalRealPart (1 / 4) (v / 2) 0 / 2 -
          ∑' n : ℕ,
            shiftedTrapezoidalError (1 / 4) (v / 2) n)) := by
    convert (hzero.add tendsto_const_nhds).sub hendpoint |>.sub herr using 1
    all_goals ring
  have hagree : (fun N : ℕ ↦ quarterDigammaPartialApprox v N) =ᶠ[atTop]
      (fun N : ℕ ↦
        (((harmonic N : ℝ) - Real.eulerMascheroniConstant -
            shiftedReciprocalPrimitive (1 / 4) (v / 2) N) +
          shiftedReciprocalPrimitive (1 / 4) (v / 2) 0) -
          (shiftedReciprocalRealPart (1 / 4) (v / 2) 0 +
            shiftedReciprocalRealPart (1 / 4) (v / 2) N) / 2 -
          ∑ n ∈ Finset.range N,
            shiftedTrapezoidalError (1 / 4) (v / 2) n) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact quarterDigammaPartialApprox_eq_trapezoidal_decomposition
      v hv.ne' hN
  exact tendsto_nhds_unique hmain (hdecomp.congr' hagree.symm)
end ArithmeticHodge.Analysis.DigammaTrapezoid
