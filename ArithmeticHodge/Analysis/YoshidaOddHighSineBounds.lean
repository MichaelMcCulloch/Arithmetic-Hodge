import ArithmeticHodge.Analysis.YoshidaSineSeriesTail
import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaWeightedTailBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

set_option autoImplicit false

open Filter MeasureTheory Real Set
open scoped BigOperators Topology

namespace ArithmeticHodge.Analysis.YoshidaOddHighSineBounds

noncomputable section

open YoshidaCauchyTailBounds
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaSineSeriesTail
open YoshidaWeightedTailBounds
open YoshidaConstantBounds

/-!
# Uniform high Yoshida sine-moment bounds

This module proves the source-facing scalar window

`-79 / 50 ≤ yoshidaSineMoment n ≤ -31 / 20`

for every natural frequency `n ≥ 11`.  The proof starts from the exact
quarter-shifted Cauchy-series representation.  A trapezoidal decomposition
with split point `M = 2n` bounds the complete main-series remainder by
`7 / 5000`; rational estimates then control the polar and dyadic terms.

Scope caveat: this is only the uniform scalar input used by the odd low/high
coupling reduction.  It does not prove odd-tail coercivity, form boundedness,
the full restricted-support positivity statement, or the Riemann hypothesis.
-/

private def cauchyProfile (y t : ℝ) : ℝ :=
  y / ((1 / 4 + t) ^ 2 + y ^ 2)

private def cauchyProfileDeriv (y t : ℝ) : ℝ :=
  -2 * y * (1 / 4 + t) / (((1 / 4 + t) ^ 2 + y ^ 2) ^ 2)

private def cauchyProfileSecondDeriv (y t : ℝ) : ℝ :=
  2 * y * (3 * (1 / 4 + t) ^ 2 - y ^ 2) /
    (((1 / 4 + t) ^ 2 + y ^ 2) ^ 3)

private theorem hasDerivAt_cauchyProfile
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (cauchyProfile y) (cauchyProfileDeriv y t) t := by
  have hshift : HasDerivAt (fun u : ℝ ↦ 1 / 4 + u) 1 t := by
    convert (hasDerivAt_const t (1 / 4)).add (hasDerivAt_id t) using 1
    norm_num
  have hden : (1 / 4 + t) ^ 2 + y ^ 2 ≠ 0 := by positivity
  convert (hasDerivAt_const t y).div
    ((hshift.pow 2).add_const (y ^ 2)) hden using 1
  simp [cauchyProfileDeriv]
  field_simp

private theorem hasDerivAt_cauchyProfileDeriv
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (cauchyProfileDeriv y)
      (cauchyProfileSecondDeriv y t) t := by
  have hshift : HasDerivAt (fun u : ℝ ↦ 1 / 4 + u) 1 t := by
    convert (hasDerivAt_const t (1 / 4)).add (hasDerivAt_id t) using 1
    norm_num
  have hden : (1 / 4 + t) ^ 2 + y ^ 2 ≠ 0 := by positivity
  convert (((hasDerivAt_const t (-2 * y)).mul hshift).div
    (((hshift.pow 2).add_const (y ^ 2)).pow 2)
      (pow_ne_zero 2 hden)) using 1
  simp [cauchyProfileSecondDeriv]
  field_simp
  ring

private theorem cauchyProfile_contDiff_two
    {y : ℝ} (hy : y ≠ 0) : ContDiff ℝ 2 (cauchyProfile y) := by
  unfold cauchyProfile
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · intro t
    have : 0 < ((1 / 4 + t) ^ 2 + y ^ 2) := by positivity
    exact this.ne'

private theorem iteratedDeriv_two_cauchyProfile
    {y t : ℝ} (hy : y ≠ 0) :
    iteratedDeriv 2 (cauchyProfile y) t =
      cauchyProfileSecondDeriv y t := by
  have hfirst : deriv (cauchyProfile y) = cauchyProfileDeriv y := by
    funext u
    exact (hasDerivAt_cauchyProfile (t := u) hy).deriv
  have hsecond : deriv (cauchyProfileDeriv y) =
      cauchyProfileSecondDeriv y := by
    funext u
    exact (hasDerivAt_cauchyProfileDeriv (t := u) hy).deriv
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ',
    show (1 : ℕ) = 0 + 1 by omega, iteratedDeriv_succ',
    iteratedDeriv_zero, hfirst, hsecond]

private theorem abs_cauchyProfileSecondDeriv_le_global
    {y t : ℝ} (hy : 0 < y) :
    |cauchyProfileSecondDeriv y t| ≤ 2 / y ^ 3 := by
  let u : ℝ := 1 / 4 + t
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  have hden : 0 < u ^ 2 + y ^ 2 := by positivity
  have hpoly : y ^ 4 * |3 * u ^ 2 - y ^ 2| ≤
      (u ^ 2 + y ^ 2) ^ 3 := by
    rcases le_total (y ^ 2) (3 * u ^ 2) with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      rw [← sub_nonneg]
      have hid :
          (u ^ 2 + y ^ 2) ^ 3 - y ^ 4 * (3 * u ^ 2 - y ^ 2) =
            u ^ 6 + 3 * u ^ 4 * y ^ 2 + 2 * y ^ 6 := by ring
      rw [hid]
      positivity
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      rw [← sub_nonneg]
      have hid :
          (u ^ 2 + y ^ 2) ^ 3 - y ^ 4 * (y ^ 2 - 3 * u ^ 2) =
            u ^ 6 + 3 * u ^ 4 * y ^ 2 + 6 * u ^ 2 * y ^ 4 := by ring
      have hneg : -(3 * u ^ 2 - y ^ 2) = y ^ 2 - 3 * u ^ 2 := by ring
      rw [hneg]
      rw [hid]
      positivity
  unfold cauchyProfileSecondDeriv
  change |2 * y * (3 * u ^ 2 - y ^ 2) / (u ^ 2 + y ^ 2) ^ 3| ≤ _
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos hy, abs_of_pos (pow_pos hden 3)]
  rw [div_le_div_iff₀ (pow_pos hden 3) (pow_pos hy 3)]
  nlinarith [hpoly]

private theorem abs_cauchyProfileSecondDeriv_le_tail
    {y t : ℝ} (hy : 0 < y) (ht : 0 < 1 / 4 + t) :
    |cauchyProfileSecondDeriv y t| ≤
      6 * y / (1 / 4 + t) ^ 4 := by
  let u : ℝ := 1 / 4 + t
  have hu : 0 < u := ht
  have hden : 0 < u ^ 2 + y ^ 2 := by positivity
  have habs : |3 * u ^ 2 - y ^ 2| ≤ 3 * (u ^ 2 + y ^ 2) := by
    rcases le_total (y ^ 2) (3 * u ^ 2) with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      nlinarith [sq_nonneg y]
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      nlinarith [sq_nonneg u]
  have hdenSq : u ^ 4 ≤ (u ^ 2 + y ^ 2) ^ 2 := by
    nlinarith [sq_nonneg y, sq_nonneg (u ^ 2),
      mul_nonneg (sq_nonneg u) (sq_nonneg y)]
  unfold cauchyProfileSecondDeriv
  change |2 * y * (3 * u ^ 2 - y ^ 2) / (u ^ 2 + y ^ 2) ^ 3| ≤ _
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos hy, abs_of_pos (pow_pos hden 3)]
  calc
    2 * y * |3 * u ^ 2 - y ^ 2| / (u ^ 2 + y ^ 2) ^ 3 ≤
        2 * y * (3 * (u ^ 2 + y ^ 2)) /
          (u ^ 2 + y ^ 2) ^ 3 := by gcongr
    _ = 6 * y / (u ^ 2 + y ^ 2) ^ 2 := by field_simp; ring
    _ ≤ 6 * y / u ^ 4 := by
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hu 4) hdenSq

private def cauchyProfileError (y : ℝ) (k : ℕ) : ℝ :=
  trapezoidal_error (cauchyProfile y) 1 k (k + 1)

private theorem cauchyProfileError_le_global
    {y : ℝ} (hy : 0 < y) (k : ℕ) :
    |cauchyProfileError y k| ≤ 1 / (6 * y ^ 3) := by
  have hcont := cauchyProfile_contDiff_two hy.ne'
  have hbound : ∀ t,
      |iteratedDerivWithin 2 (cauchyProfile y)
        (Icc (k : ℝ) (k + 1)) t| ≤ 2 / y ^ 3 := by
    intro t
    by_cases ht : t ∈ Icc (k : ℝ) (k + 1)
    · rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (by norm_num : (k : ℝ) < k + 1))
        hcont.contDiffAt ht,
        iteratedDeriv_two_cauchyProfile hy.ne']
      exact abs_cauchyProfileSecondDeriv_le_global hy
    · rw [iteratedDerivWithin_succ,
        derivWithin_zero_of_notMem_closure (by rwa [closure_Icc]), abs_zero]
      positivity
  have htrap := trapezoidal_error_le_of_c2
    (a := (k : ℝ)) (b := k + 1) hcont.contDiffOn
    (by simpa [uIcc_of_le (by norm_num : (k : ℝ) ≤ k + 1)] using hbound)
    (by norm_num : 0 < (1 : ℕ))
  norm_num [cauchyProfileError, abs_of_nonneg] at htrap ⊢
  convert htrap using 1
  ring

private theorem cauchyProfileError_le_tail
    {y : ℝ} (hy : 0 < y) (k : ℕ) :
    |cauchyProfileError y k| ≤
      y / (2 * ((1 / 4 : ℝ) + k) ^ 4) := by
  have hcont := cauchyProfile_contDiff_two hy.ne'
  have hkpos : 0 < (1 / 4 : ℝ) + k := by positivity
  have hbound : ∀ t,
      |iteratedDerivWithin 2 (cauchyProfile y)
        (Icc (k : ℝ) (k + 1)) t| ≤
          6 * y / ((1 / 4 : ℝ) + k) ^ 4 := by
    intro t
    by_cases ht : t ∈ Icc (k : ℝ) (k + 1)
    · rw [iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc (by norm_num : (k : ℝ) < k + 1))
        hcont.contDiffAt ht,
        iteratedDeriv_two_cauchyProfile hy.ne']
      have hkt : (1 / 4 : ℝ) + k ≤ 1 / 4 + t := by
        norm_num at ht ⊢
        linarith [ht.1]
      have htpos : 0 < (1 / 4 : ℝ) + t := hkpos.trans_le hkt
      exact (abs_cauchyProfileSecondDeriv_le_tail hy htpos).trans
        (div_le_div_of_nonneg_left (by positivity) (pow_pos hkpos 4)
          (pow_le_pow_left₀ hkpos.le hkt 4))
    · rw [iteratedDerivWithin_succ,
        derivWithin_zero_of_notMem_closure (by rwa [closure_Icc]), abs_zero]
      positivity
  have htrap := trapezoidal_error_le_of_c2
    (a := (k : ℝ)) (b := k + 1) hcont.contDiffOn
    (by simpa [uIcc_of_le (by norm_num : (k : ℝ) ≤ k + 1)] using hbound)
    (by norm_num : 0 < (1 : ℕ))
  norm_num [cauchyProfileError, abs_of_nonneg] at htrap ⊢
  exact htrap.trans_eq (by
    field_simp [hkpos.ne']
    ring)

private theorem sum_range_cauchyProfileError
    {y : ℝ} (hy : y ≠ 0) (N : ℕ) :
    (∑ k ∈ Finset.range N, cauchyProfileError y k) =
      trapezoidal_error (cauchyProfile y) N 0 N := by
  cases N with
  | zero => simp [cauchyProfileError]
  | succ N =>
      have hcont := (cauchyProfile_contDiff_two hy).continuous
      have hint : IntervalIntegrable (cauchyProfile y)
          volume 0 (0 + ((N + 1 : ℕ) : ℝ) * 1) :=
        hcont.intervalIntegrable _ _
      have hsum := sum_trapezoidal_error_adjacent_intervals
        (f := cauchyProfile y) (a := 0) (h := 1) (N := N + 1)
        (Nat.succ_pos N) hint
      simpa [cauchyProfileError] using hsum

private def cauchyErrorMajor (y : ℝ) (M k : ℕ) : ℝ :=
  if k < M then 1 / (6 * y ^ 3) else y / (2 * (k : ℝ) ^ 4)

private theorem summable_cauchyErrorMajor
    {y : ℝ} (M : ℕ) : Summable (cauchyErrorMajor y M) := by
  have hp0 : Summable (fun k : ℕ ↦ 1 / ((k : ℝ) ^ 4)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have hp : Summable (fun k : ℕ ↦ y / (2 * (k : ℝ) ^ 4)) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hp0.mul_left (y / 2)
  apply hp.congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop M] with k hk
  simp [cauchyErrorMajor, not_lt.mpr hk]

private theorem cauchyErrorMajor_nonneg
    {y : ℝ} (hy : 0 < y) (M k : ℕ) :
    0 ≤ cauchyErrorMajor y M k := by
  unfold cauchyErrorMajor
  split_ifs <;> positivity

private theorem cauchyProfileError_le_major
    {y : ℝ} (hy : 0 < y) {M : ℕ} (hM : 0 < M) (k : ℕ) :
    |cauchyProfileError y k| ≤ cauchyErrorMajor y M k := by
  by_cases hk : k < M
  · simpa [cauchyErrorMajor, hk] using cauchyProfileError_le_global hy k
  · have hkM : M ≤ k := Nat.le_of_not_gt hk
    have hkpos : 0 < k := hM.trans_le hkM
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hden : (k : ℝ) ^ 4 ≤ ((1 / 4 : ℝ) + k) ^ 4 := by
      exact pow_le_pow_left₀ hkR.le (by linarith) 4
    simpa [cauchyErrorMajor, hk] using
      (cauchyProfileError_le_tail hy k).trans
        (div_le_div_of_nonneg_left hy.le (by positivity) (by nlinarith))

private theorem tsum_cauchyErrorMajor_le
    {y : ℝ} (hy : 0 < y) {M : ℕ} (hM : 1 < M) :
    (∑' k : ℕ, cauchyErrorMajor y M k) ≤
      M / (6 * y ^ 3) + y / (4 * (M - 1 : ℕ) ^ 2 * M) := by
  have hs := summable_cauchyErrorMajor (y := y) M
  have hsplit := hs.sum_add_tsum_nat_add M
  have hM0 : 0 < M := by omega
  have hKm1 : 0 < M - 1 := by omega
  have htail := invFourth_tail_le (M - 1) hKm1
  have hs4 := summable_invPow_tail (M - 1) 4 (by omega)
  have htail' :
      (∑' j : ℕ, y / (2 * ((M + j : ℕ) : ℝ) ^ 4)) ≤
        y / (4 * (M - 1 : ℕ) ^ 2 * M) := by
    have hmul := mul_le_mul_of_nonneg_left htail (show 0 ≤ y / 2 by positivity)
    rw [← hs4.tsum_mul_left (y / 2)] at hmul
    convert hmul using 1
    · apply tsum_congr
      intro j
      have hnat : M - 1 + j + 1 = M + j := by omega
      rw [hnat]
      ring
    · have hcast : (((M - 1 + 1 : ℕ) : ℝ)) = M := by
        norm_num [Nat.sub_add_cancel (by omega : 1 ≤ M)]
      rw [hcast]
      ring
  rw [← hsplit]
  calc
    (∑ k ∈ Finset.range M, cauchyErrorMajor y M k) +
        ∑' j : ℕ, cauchyErrorMajor y M (j + M) =
      M / (6 * y ^ 3) +
        ∑' j : ℕ, y / (2 * ((M + j : ℕ) : ℝ) ^ 4) := by
          congr 1
          · calc
              (∑ k ∈ Finset.range M, cauchyErrorMajor y M k) =
                  ∑ k ∈ Finset.range M, 1 / (6 * y ^ 3) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    rw [cauchyErrorMajor, if_pos (Finset.mem_range.mp hk)]
              _ = M / (6 * y ^ 3) := by simp; ring
          · apply tsum_congr
            intro j
            simp [cauchyErrorMajor, Nat.add_comm]
    _ ≤ _ := by gcongr

private theorem trapezoidal_error_cauchyProfile_le
    {y : ℝ} (hy : 0 < y) {M : ℕ} (hM : 1 < M) (N : ℕ) :
    |trapezoidal_error (cauchyProfile y) N 0 N| ≤
      M / (6 * y ^ 3) + y / (4 * (M - 1 : ℕ) ^ 2 * M) := by
  rw [← sum_range_cauchyProfileError hy.ne' N]
  calc
    |∑ k ∈ Finset.range N, cauchyProfileError y k| ≤
        ∑ k ∈ Finset.range N, |cauchyProfileError y k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, cauchyErrorMajor y M k := by
      exact Finset.sum_le_sum fun k _ ↦
        cauchyProfileError_le_major hy (by omega) k
    _ ≤ ∑' k : ℕ, cauchyErrorMajor y M k := by
      exact (summable_cauchyErrorMajor (y := y) M).sum_le_tsum
        (Finset.range N) (fun i _ ↦ cauchyErrorMajor_nonneg hy M i)
    _ ≤ _ := tsum_cauchyErrorMajor_le hy hM

private theorem trapezoidal_error_cauchyProfile_eq
    {y : ℝ} {N : ℕ} (hN : 0 < N) :
    trapezoidal_error (cauchyProfile y) N 0 N =
      (∑ k ∈ Finset.range (N + 1), cauchyProfile y k) -
        (cauchyProfile y 0 + cauchyProfile y N) / 2 -
        ∫ t in 0..N, cauchyProfile y t := by
  rw [trapezoidal_error, trapezoidal_integral]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show ((N : ℝ) - 0) / N = 1 by
    rw [sub_zero]
    exact div_self hNR]
  simp only [zero_add, one_mul]
  have harg (k : ℕ) :
      ((k : ℝ) + 1) * ((N : ℝ) - 0) / N = (k + 1 : ℕ) := by
    push_cast
    rw [sub_zero]
    field_simp
  simp_rw [harg]
  have hNsplit : N - 1 + 1 = N := by omega
  have hprefix :
      (∑ k ∈ Finset.range N, cauchyProfile y k) =
        cauchyProfile y 0 +
          ∑ k ∈ Finset.range (N - 1), cauchyProfile y (k + 1) := by
    calc
      (∑ k ∈ Finset.range N, cauchyProfile y k) =
          ∑ k ∈ Finset.range (N - 1 + 1), cauchyProfile y k := by
            rw [hNsplit]
      _ = _ := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_add, Nat.cast_one]
        ring
  have hsum :
      (∑ k ∈ Finset.range (N + 1), cauchyProfile y k) =
        cauchyProfile y 0 +
          (∑ k ∈ Finset.range (N - 1), cauchyProfile y (k + 1)) +
          cauchyProfile y N := by
    rw [Finset.sum_range_succ, hprefix]
  rw [hsum]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private def cauchyProfilePrimitive (y t : ℝ) : ℝ :=
  Real.arctan ((1 / 4 + t) / y)

private theorem hasDerivAt_cauchyProfilePrimitive
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (cauchyProfilePrimitive y)
      (cauchyProfile y t) t := by
  have hshift : HasDerivAt (fun u : ℝ ↦ 1 / 4 + u) 1 t := by
    convert (hasDerivAt_const t (1 / 4)).add (hasDerivAt_id t) using 1
    norm_num
  have hinner := hshift.div_const y
  have hatan := (Real.hasDerivAt_arctan ((1 / 4 + t) / y)).comp t hinner
  convert hatan using 1
  simp only [cauchyProfile]
  field_simp
  ring

private theorem integral_cauchyProfile
    {y a b : ℝ} (hy : y ≠ 0) :
    (∫ t in a..b, cauchyProfile y t) =
      cauchyProfilePrimitive y b - cauchyProfilePrimitive y a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _ht
    exact hasDerivAt_cauchyProfilePrimitive hy
  · exact (cauchyProfile_contDiff_two hy).continuous.intervalIntegrable _ _

private theorem tendsto_cauchyProfile_nat
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun N : ℕ ↦ cauchyProfile y N) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N ↦ by
      unfold cauchyProfile
      positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hden : (N : ℝ) ≤ (1 / 4 + (N : ℝ)) ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg (1 / 4 + (N : ℝ) - 1), sq_nonneg y]
    unfold cauchyProfile
    exact div_le_div_of_nonneg_left hy.le (by positivity) hden
  · exact tendsto_const_div_atTop_nhds_zero_nat y

private theorem tendsto_integral_cauchyProfile
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun N : ℕ ↦ ∫ t in 0..N, cauchyProfile y t) atTop
      (nhds (Real.pi / 2 - Real.arctan ((1 / 4) / y))) := by
  have hbase : Tendsto (fun N : ℕ ↦ (1 / 4 : ℝ) + N) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have harg : Tendsto (fun N : ℕ ↦ ((1 / 4 : ℝ) + N) / y)
      atTop atTop := hbase.atTop_div_const hy
  have hatan : Tendsto
      (fun N : ℕ ↦ Real.arctan (((1 / 4 : ℝ) + N) / y)) atTop
      (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg
  have hlim := hatan.sub
    (tendsto_const_nhds (x := Real.arctan ((1 / 4 : ℝ) / y)))
  convert hlim using 1
  funext N
  rw [integral_cauchyProfile hy.ne']
  simp [cauchyProfilePrimitive]

private theorem cauchyProfile_tsum_bounds
    {y : ℝ} (hy : 0 < y)
    (hs : Summable (fun k : ℕ ↦ cauchyProfile y k))
    {M : ℕ} (hM : 1 < M) :
    let I := Real.pi / 2 - Real.arctan ((1 / 4) / y)
    let E := M / (6 * y ^ 3) + y / (4 * (M - 1 : ℕ) ^ 2 * M)
    I + cauchyProfile y 0 / 2 - E ≤ ∑' k : ℕ, cauchyProfile y k ∧
      (∑' k : ℕ, cauchyProfile y k) ≤
        I + cauchyProfile y 0 / 2 + E := by
  dsimp only
  let I := Real.pi / 2 - Real.arctan ((1 / 4) / y)
  let E := M / (6 * y ^ 3) + y / (4 * (M - 1 : ℕ) ^ 2 * M)
  have hpartial : Tendsto
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1), cauchyProfile y k)
      atTop (nhds (∑' k : ℕ, cauchyProfile y k)) :=
    hs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hint := tendsto_integral_cauchyProfile hy
  have hlast := tendsto_cauchyProfile_nat hy
  have hendpoint : Tendsto
      (fun N : ℕ ↦ (cauchyProfile y 0 + cauchyProfile y N) / 2)
      atTop (nhds (cauchyProfile y 0 / 2)) := by
    convert (tendsto_const_nhds.add hlast).div_const 2 using 1
    ring
  have hlowerLim : Tendsto
      (fun N : ℕ ↦ (∫ t in 0..N, cauchyProfile y t) +
        (cauchyProfile y 0 + cauchyProfile y N) / 2 - E)
      atTop (nhds (I + cauchyProfile y 0 / 2 - E)) := by
    simpa only [I] using (hint.add hendpoint).sub (tendsto_const_nhds (x := E))
  have hupperLim : Tendsto
      (fun N : ℕ ↦ (∫ t in 0..N, cauchyProfile y t) +
        (cauchyProfile y 0 + cauchyProfile y N) / 2 + E)
      atTop (nhds (I + cauchyProfile y 0 / 2 + E)) := by
    simpa only [I] using (hint.add hendpoint).add (tendsto_const_nhds (x := E))
  have hbounds : ∀ᶠ N : ℕ in atTop,
      (∫ t in 0..N, cauchyProfile y t) +
          (cauchyProfile y 0 + cauchyProfile y N) / 2 - E ≤
        ∑ k ∈ Finset.range (N + 1), cauchyProfile y k ∧
      (∑ k ∈ Finset.range (N + 1), cauchyProfile y k) ≤
        (∫ t in 0..N, cauchyProfile y t) +
          (cauchyProfile y 0 + cauchyProfile y N) / 2 + E := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have herr := trapezoidal_error_cauchyProfile_le hy hM N
    have heq := trapezoidal_error_cauchyProfile_eq (y := y) hN
    rw [heq] at herr
    let d := (∑ k ∈ Finset.range (N + 1), cauchyProfile y k) -
        (cauchyProfile y 0 + cauchyProfile y N) / 2 -
        ∫ t in 0..N, cauchyProfile y t
    have hlo := neg_abs_le d
    have hhi := le_abs_self d
    constructor <;> dsimp only [E, d] at * <;> linarith
  exact ⟨le_of_tendsto_of_tendsto hlowerLim hpartial
      (hbounds.mono (fun _ h ↦ h.1)),
    le_of_tendsto_of_tendsto hpartial hupperLim
      (hbounds.mono (fun _ h ↦ h.2))⟩

private theorem yoshidaScaledFrequency_coarse_bounds
    (n : ℕ) :
    (9 / 2 : ℝ) * n ≤ yoshidaScaledFrequency n ∧
      yoshidaScaledFrequency n ≤ (23 / 5 : ℝ) * n := by
  have hlog := strict_log_two_bounds
  have hpiLower : (31415 / 10000 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d20
    norm_num at h ⊢
    linarith
  have hpiUpper : Real.pi < (31416 / 10000 : ℝ) := by
    have h := Real.pi_lt_d20
    norm_num at h ⊢
    linarith
  have hratioLower : (9 / 2 : ℝ) * yoshidaLength ≤ Real.pi := by
    rw [yoshidaLength]
    nlinarith [hlog.2, hpiLower]
  have hratioUpper : Real.pi ≤ (23 / 5 : ℝ) * yoshidaLength := by
    rw [yoshidaLength]
    nlinarith [hlog.1, hpiUpper]
  have hyEq : yoshidaScaledFrequency n = Real.pi * n / yoshidaLength := by
    rw [yoshidaScaledFrequency, yoshidaKappa]
    ring
  rw [hyEq]
  constructor
  · apply (le_div_iff₀ yoshidaLength_pos).2
    nlinarith [mul_le_mul_of_nonneg_right hratioLower (Nat.cast_nonneg n)]
  · apply (div_le_iff₀ yoshidaLength_pos).2
    nlinarith [mul_le_mul_of_nonneg_right hratioUpper (Nat.cast_nonneg n)]

private theorem high_trapezoidal_budget
    {n : ℕ} (hn : 11 ≤ n) :
    let y := yoshidaScaledFrequency n
    let M := 2 * n
    M / (6 * y ^ 3) + y / (4 * (M - 1 : ℕ) ^ 2 * M) ≤
      (7 / 5000 : ℝ) := by
  dsimp only
  let y := yoshidaScaledFrequency n
  let M := 2 * n
  have hb := yoshidaScaledFrequency_coarse_bounds n
  have hnR : (11 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hy : 0 < y := lt_of_lt_of_le (mul_pos (by norm_num) hn0) hb.1
  have hpow : ((9 / 2 : ℝ) * n) ^ 3 ≤ y ^ 3 :=
    pow_le_pow_left₀ (by positivity) hb.1 3
  have hcube : (121 : ℝ) * n ≤ n ^ 3 := by
    nlinarith [mul_nonneg hn0.le (sq_nonneg ((n : ℝ) - 11))]
  have hhead : (M : ℝ) / (6 * y ^ 3) ≤ 1 / 30000 := by
    apply (div_le_iff₀ (by positivity : 0 < 6 * y ^ 3)).2
    dsimp only [M]
    push_cast
    nlinarith [hpow, hcube]
  have hbase : (21 : ℝ) ≤ (M - 1 : ℕ) := by
    dsimp only [M]
    exact_mod_cast (show 21 ≤ 2 * n - 1 by omega)
  have hbaseSq : (441 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((M - 1 : ℕ) : ℝ) - 21)]
  have hMR : (0 : ℝ) < M := by
    dsimp only [M]
    positivity
  have hdenLower : (3528 : ℝ) * n ≤
      4 * ((M - 1 : ℕ) : ℝ) ^ 2 * M := by
    dsimp only [M] at hMR ⊢
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hbaseSq) hn0.le]
  have htail : y / (4 * ((M - 1 : ℕ) : ℝ) ^ 2 * M) ≤
      41 / 30000 := by
    apply (div_le_iff₀ (by positivity :
      0 < 4 * ((M - 1 : ℕ) : ℝ) ^ 2 * M)).2
    nlinarith [hb.2, hdenLower]
  dsimp only [y, M] at hhead htail ⊢
  nlinarith

private theorem arctan_lower_rational
    {z : ℝ} (hz : 0 ≤ z) : z / (1 + z ^ 2) ≤ Real.arctan z := by
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ 1 / (1 + z ^ 2))
      volume 0 z := Continuous.intervalIntegrable continuous_const _ _
  have hfun : IntervalIntegrable (fun t : ℝ ↦ (1 + t ^ 2)⁻¹)
      volume 0 z := Continuous.intervalIntegrable
        ((continuous_const.add (continuous_id.pow 2)).inv₀ fun t : ℝ ↦ by
          have : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
          exact this.ne') _ _
  have hpoint : ∀ t ∈ Icc (0 : ℝ) z,
      1 / (1 + z ^ 2) ≤ (1 + t ^ 2)⁻¹ := by
    intro t ht
    have hsq : t ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ ht.1 ht.2 2
    rw [one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  calc
    z / (1 + z ^ 2) = ∫ _t in 0..z, 1 / (1 + z ^ 2) := by
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      simp only [div_eq_mul_inv]
      simp
    _ ≤ ∫ t in 0..z, (1 + t ^ 2)⁻¹ :=
      intervalIntegral.integral_mono_on hz hconst hfun hpoint
    _ = Real.arctan z := by
      rw [integral_inv_one_add_sq, Real.arctan_zero, sub_zero]

private theorem arctan_upper_linear
    {z : ℝ} (hz : 0 ≤ z) : Real.arctan z ≤ z := by
  have hfun : IntervalIntegrable (fun t : ℝ ↦ (1 + t ^ 2)⁻¹)
      volume 0 z := Continuous.intervalIntegrable
        ((continuous_const.add (continuous_id.pow 2)).inv₀ fun t : ℝ ↦ by
          have : 0 < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
          exact this.ne') _ _
  have hone : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ))
      volume 0 z := Continuous.intervalIntegrable continuous_const _ _
  have hpoint : ∀ t ∈ Icc (0 : ℝ) z, (1 + t ^ 2)⁻¹ ≤ 1 := by
    intro t _ht
    rw [inv_le_one₀ (by positivity)]
    nlinarith [sq_nonneg t]
  calc
    Real.arctan z = ∫ t in 0..z, (1 + t ^ 2)⁻¹ := by
      rw [integral_inv_one_add_sq, Real.arctan_zero, sub_zero]
    _ ≤ ∫ _t in 0..z, (1 : ℝ) :=
      intervalIntegral.integral_mono_on hz hfun hone hpoint
    _ = z := by simp

private theorem cauchyProfile_zero_upper
    {y : ℝ} (hy : 0 < y) : cauchyProfile y 0 ≤ 1 / y := by
  unfold cauchyProfile
  norm_num
  rw [← one_div]
  rw [div_le_div_iff₀ (by positivity : 0 < (1 / 16 : ℝ) + y ^ 2) hy]
  nlinarith

private theorem cauchyProfile_zero_lower
    {y : ℝ} (hy : 2 ≤ y) :
    (49 / 50 : ℝ) / y ≤ cauchyProfile y 0 := by
  have hy0 : 0 < y := by linarith
  unfold cauchyProfile
  norm_num
  rw [div_le_div_iff₀ hy0 (by positivity : 0 < (1 / 16 : ℝ) + y ^ 2)]
  nlinarith [sq_nonneg (y - 2)]

private theorem arctan_quarter_div_y_lower
    {y : ℝ} (hy : 0 < y) :
    cauchyProfile y 0 / 4 ≤ Real.arctan ((1 / 4 : ℝ) / y) := by
  have hz : 0 ≤ (1 / 4 : ℝ) / y := by positivity
  have h := arctan_lower_rational hz
  apply h.trans'
  unfold cauchyProfile
  norm_num
  field_simp [hy.ne']
  norm_num
  exact le_of_eq (by ring)

private theorem arctan_quarter_div_y_upper
    {y : ℝ} (hy : 0 < y) :
    Real.arctan ((1 / 4 : ℝ) / y) ≤ 1 / (4 * y) := by
  have h := arctan_upper_linear (show 0 ≤ (1 / 4 : ℝ) / y by positivity)
  convert h using 1
  field_simp [hy.ne']

private theorem sqrt_two_coefficient_bounds :
    (-1 / 8 : ℝ) ≤
        2 - Real.sqrt 2 - (Real.sqrt 2)⁻¹ ∧
      2 - Real.sqrt 2 - (Real.sqrt 2)⁻¹ ≤ 0 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslower : (24 / 17 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 24 / 17)]
  constructor
  · apply le_of_mul_le_mul_right _ hs
    field_simp [hs.ne']
    nlinarith
  · apply le_of_mul_le_mul_right _ hs
    field_simp [hs.ne']
    nlinarith [sq_nonneg (Real.sqrt 2 - 1)]

private theorem sinePolarValue_bounds
    {n : ℕ} (hn : n ≠ 0) :
    let y := yoshidaScaledFrequency n
    (-1 / (8 * y) ≤ sinePolarValue n ∧ sinePolarValue n ≤ 0) := by
  dsimp only
  let y := yoshidaScaledFrequency n
  let c := 2 - Real.sqrt 2 - (Real.sqrt 2)⁻¹
  have hy : 0 < y := yoshidaScaledFrequency_pos hn
  have hc : (-1 / 8 : ℝ) ≤ c ∧ c ≤ 0 :=
    sqrt_two_coefficient_bounds
  have hkappa : yoshidaKappa n = 2 * y := by
    dsimp only [y]
    rw [yoshidaScaledFrequency]
    ring
  have hvalue : sinePolarValue n =
      4 * y * c / ((1 / 4 : ℝ) + 4 * y ^ 2) := by
    rw [sinePolarValue, hkappa]
    dsimp only [c]
    field_simp
    ring
  have hden : 0 < (1 / 4 : ℝ) + 4 * y ^ 2 := by positivity
  rw [hvalue]
  constructor
  · change (-1 : ℝ) / (8 * y) ≤
      4 * y * c / ((1 / 4 : ℝ) + 4 * y ^ 2)
    rw [div_le_div_iff₀ (by positivity : 0 < 8 * y) hden]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc.1) (sq_nonneg y)]
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hc.2) hden.le

private theorem inv_sqrt_two_le_five_sevenths :
    (Real.sqrt 2)⁻¹ ≤ (5 / 7 : ℝ) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslower : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 7 / 5)]
  rw [inv_eq_one_div]
  rw [div_le_iff₀ hs]
  nlinarith

private theorem sineMainTerm_le_inv_frequency
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    sineMainTerm n k ≤ 1 / yoshidaScaledFrequency n := by
  have hy := yoshidaScaledFrequency_pos hn
  rw [sineMainTerm, cauchyTailTerm]
  rw [div_le_div_iff₀ (by positivity :
    0 < ((1 / 4 : ℝ) + k) ^ 2 + yoshidaScaledFrequency n ^ 2) hy]
  nlinarith [sq_nonneg ((1 / 4 : ℝ) + k)]

private theorem sineDyadicCorrection_le_geometric
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    sineDyadicCorrection n k ≤
      (5 / (7 * yoshidaScaledFrequency n) : ℝ) * (1 / 4 : ℝ) ^ k := by
  have hy := yoshidaScaledFrequency_pos hn
  have hmain0 := sineMainTerm_nonneg hn k
  have hmain := sineMainTerm_le_inv_frequency hn k
  have hsqrt0 : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
  rw [sineDyadicCorrection, div_eq_mul_inv, ← inv_pow]
  calc
    sineMainTerm n k * (Real.sqrt 2)⁻¹ * ((4 : ℝ)⁻¹) ^ k ≤
        (1 / yoshidaScaledFrequency n) * (5 / 7 : ℝ) *
          ((4 : ℝ)⁻¹) ^ k := by
      gcongr
      exact inv_sqrt_two_le_five_sevenths
    _ = (5 / (7 * yoshidaScaledFrequency n) : ℝ) *
          (1 / 4 : ℝ) ^ k := by ring

private theorem sineDyadicCorrection_tsum_le
    {n : ℕ} (hn : n ≠ 0) :
    (∑' k : ℕ, sineDyadicCorrection n k) ≤
      20 / (21 * yoshidaScaledFrequency n) := by
  let C : ℝ := 5 / (7 * yoshidaScaledFrequency n)
  have hgeom : Summable (fun k : ℕ ↦ C * (1 / 4 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  have hcorr := summable_sineDyadicCorrection hn
  have hle := hcorr.tsum_le_tsum
    (sineDyadicCorrection_le_geometric hn) hgeom
  calc
    (∑' k : ℕ, sineDyadicCorrection n k) ≤
        ∑' k : ℕ, C * (1 / 4 : ℝ) ^ k := hle
    _ = C * ((1 - (1 / 4 : ℝ))⁻¹) := by
      rw [tsum_mul_left,
        tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
    _ = 20 / (21 * yoshidaScaledFrequency n) := by
      dsimp only [C]
      field_simp [yoshidaScaledFrequency_pos hn |>.ne']
      ring

private theorem yoshidaSineMoment_eq_main_correction
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaSineMoment n = sinePolarValue n -
      (∑' k : ℕ, sineMainTerm n k) +
      ∑' k : ℕ, sineDyadicCorrection n k := by
  rw [yoshidaSineMoment_eq_explicitCauchySeries hn]
  have hmain := summable_sineMainTerm hn
  have hcorr := summable_sineDyadicCorrection hn
  have heq : (∑' k : ℕ, sineCauchyTerm n k) =
      (∑' k : ℕ, sineMainTerm n k) -
        ∑' k : ℕ, sineDyadicCorrection n k := by
    rw [← hmain.tsum_sub hcorr]
    apply tsum_congr
    exact sineCauchyTerm_eq_main_sub_correction n
  rw [heq]
  ring

theorem yoshida_high_sine_bounds
    (n : ℕ) (hn : 11 ≤ n) :
    (-79 / 50 : ℝ) ≤ yoshidaSineMoment n ∧
      yoshidaSineMoment n ≤ (-31 / 20 : ℝ) := by
  let y := yoshidaScaledFrequency n
  let M := 2 * n
  let E := M / (6 * y ^ 3) + y / (4 * (M - 1 : ℕ) ^ 2 * M)
  let A := ∑' k : ℕ, sineMainTerm n k
  let C := ∑' k : ℕ, sineDyadicCorrection n k
  have hn0 : n ≠ 0 := by omega
  have hy : 0 < y := yoshidaScaledFrequency_pos hn0
  have hyBounds := yoshidaScaledFrequency_coarse_bounds n
  have hnR : (11 : ℝ) ≤ n := by exact_mod_cast hn
  have hyLower : (99 / 2 : ℝ) ≤ y := by
    dsimp only [y]
    nlinarith [hyBounds.1]
  have hyTwo : (2 : ℝ) ≤ y := by linarith
  have hM : 1 < M := by
    dsimp only [M]
    omega
  have hmainEq : (fun k : ℕ ↦ sineMainTerm n k) =
      fun k : ℕ ↦ cauchyProfile y k := by
    funext k
    dsimp only [y]
    rfl
  have hmainSummable : Summable (fun k : ℕ ↦ cauchyProfile y k) := by
    rw [← hmainEq]
    exact summable_sineMainTerm hn0
  have hA := cauchyProfile_tsum_bounds hy hmainSummable hM
  rw [← hmainEq] at hA
  change (Real.pi / 2 - Real.arctan ((1 / 4 : ℝ) / y)) +
        cauchyProfile y 0 / 2 - E ≤ A ∧
      A ≤ (Real.pi / 2 - Real.arctan ((1 / 4 : ℝ) / y)) +
        cauchyProfile y 0 / 2 + E at hA
  have hE : E ≤ (7 / 5000 : ℝ) := by
    dsimp only [E, y, M]
    exact high_trapezoidal_budget hn
  have hPolar := sinePolarValue_bounds hn0
  change -1 / (8 * y) ≤ sinePolarValue n ∧ sinePolarValue n ≤ 0 at hPolar
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact tsum_nonneg (sineDyadicCorrection_nonneg hn0)
  have hC : C ≤ 20 / (21 * y) := by
    dsimp only [C, y]
    exact sineDyadicCorrection_tsum_le hn0
  have hthetaLower := arctan_quarter_div_y_lower hy
  have hthetaUpper := arctan_quarter_div_y_upper hy
  have hf0Upper := cauchyProfile_zero_upper hy
  have hf0Lower := cauchyProfile_zero_lower hyTwo
  have hpiUpper : Real.pi / 2 ≤ (3927 / 2500 : ℝ) := by
    have h := Real.pi_lt_d20
    norm_num at h ⊢
    linarith
  have hpiLower : (6283 / 4000 : ℝ) ≤ Real.pi / 2 := by
    have h := Real.pi_gt_d20
    norm_num at h ⊢
    linarith
  have hinvLowerBudget : 3 / (8 * y) ≤ (1 / 132 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < 8 * y)]
    nlinarith [hyLower]
  have hinvUpperBudget : 374 / (525 * y) ≤ (748 / 51975 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < 525 * y)]
    nlinarith [hyLower]
  rw [yoshidaSineMoment_eq_main_correction hn0]
  change (-79 / 50 : ℝ) ≤ sinePolarValue n - A + C ∧
    sinePolarValue n - A + C ≤ (-31 / 20 : ℝ)
  constructor
  · have hcoarse :
        -Real.pi / 2 - 3 / (8 * y) - E ≤
          sinePolarValue n - A + C := by
      calc
        -Real.pi / 2 - 3 / (8 * y) - E =
            -Real.pi / 2 - 1 / (8 * y) - 1 / (4 * y) - E := by
              field_simp [hy.ne']
              ring
        _ ≤ -Real.pi / 2 - 1 / (8 * y) -
            cauchyProfile y 0 / 4 - E := by linarith
        _ ≤ -Real.pi / 2 - 1 / (8 * y) +
            Real.arctan ((1 / 4 : ℝ) / y) -
            cauchyProfile y 0 / 2 - E := by linarith
        _ = (-1 / (8 * y)) -
            (Real.pi / 2 - Real.arctan ((1 / 4 : ℝ) / y) +
              cauchyProfile y 0 / 2 + E) + 0 := by ring
        _ ≤ sinePolarValue n - A + C := by
          exact add_le_add (add_le_add hPolar.1 (neg_le_neg hA.2)) hC0
    have hnumeric : (-79 / 50 : ℝ) ≤
        -Real.pi / 2 - 3 / (8 * y) - E := by
      nlinarith [show (3927 / 2500 : ℝ) + 1 / 132 + 7 / 5000 ≤
        79 / 50 by norm_num]
    exact hnumeric.trans hcoarse
  · have hcoarse : sinePolarValue n - A + C ≤
        -Real.pi / 2 + 374 / (525 * y) + E := by
      calc
        sinePolarValue n - A + C ≤
            -Real.pi / 2 + Real.arctan ((1 / 4 : ℝ) / y) -
              cauchyProfile y 0 / 2 + E + C := by
                have hordered := add_le_add
                  (add_le_add hPolar.2 (neg_le_neg hA.1)) (le_refl C)
                linarith [hordered]
        _ ≤ -Real.pi / 2 + 1 / (4 * y) -
              ((49 / 50 : ℝ) / y) / 2 + E + 20 / (21 * y) := by
            linarith
        _ = -Real.pi / 2 + 374 / (525 * y) + E := by
            field_simp [hy.ne']
            ring
    have hnumeric : -Real.pi / 2 + 374 / (525 * y) + E ≤
        (-31 / 20 : ℝ) := by
      nlinarith [show - (6283 / 4000 : ℝ) + 748 / 51975 + 7 / 5000 ≤
        -31 / 20 by norm_num]
    exact hcoarse.trans hnumeric

end

end ArithmeticHodge.Analysis.YoshidaOddHighSineBounds
