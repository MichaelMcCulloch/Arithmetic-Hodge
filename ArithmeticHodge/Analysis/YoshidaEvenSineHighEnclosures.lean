import ArithmeticHodge.Analysis.YoshidaEvenDigammaImagRemainder
import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets
import ArithmeticHodge.Analysis.YoshidaEvenSineMomentFiveEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenSineMomentFourEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenSineMomentOneEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenSineMomentThreeEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenSineMomentTwoEnclosure
import ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures

set_option autoImplicit false

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped BigOperators ComplexConjugate Topology

namespace ArithmeticHodge.Analysis.YoshidaEvenSineHighEnclosures

open ArithmeticHodge.Analysis
open RatInterval
open YoshidaCauchyTailBounds
open YoshidaEvenCouplingReduction
open YoshidaEvenDigammaImagRemainder
open YoshidaEvenIntervalCertificate
open YoshidaEvenMomentTargets
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures
open YoshidaSineCheckpointedHead
open YoshidaSineSeriesTail
open YoshidaWeightedTailBounds
open TrapezoidalErrorBounds
open YoshidaConstantBounds

private def cauchyProfile (y t : ℝ) : ℝ :=
  y / ((1 / 4 + t) ^ 2 + y ^ 2)

private def cauchyProfileDeriv (y t : ℝ) : ℝ :=
  -2 * y * (1 / 4 + t) / (((1 / 4 + t) ^ 2 + y ^ 2) ^ 2)

private def cauchyProfileSecondDeriv (y t : ℝ) : ℝ :=
  2 * y * (3 * (1 / 4 + t) ^ 2 - y ^ 2) /
    (((1 / 4 + t) ^ 2 + y ^ 2) ^ 3)

private def cauchyProfileThirdDeriv (y t : ℝ) : ℝ :=
  24 * y * (1 / 4 + t) * (y ^ 2 - (1 / 4 + t) ^ 2) /
    (((1 / 4 + t) ^ 2 + y ^ 2) ^ 4)

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

private theorem hasDerivAt_cauchyProfileSecondDeriv
    {y t : ℝ} (hy : y ≠ 0) :
    HasDerivAt (cauchyProfileSecondDeriv y)
      (cauchyProfileThirdDeriv y t) t := by
  have hshift : HasDerivAt (fun u : ℝ ↦ 1 / 4 + u) 1 t := by
    convert (hasDerivAt_const t (1 / 4)).add (hasDerivAt_id t) using 1
    norm_num
  have hden : (1 / 4 + t) ^ 2 + y ^ 2 ≠ 0 := by positivity
  convert ((((hasDerivAt_const t (2 * y)).mul
      (((hasDerivAt_const t 3).mul (hshift.pow 2)).sub_const (y ^ 2))).div
        (((hshift.pow 2).add_const (y ^ 2)).pow 3)
          (pow_ne_zero 3 hden))) using 1
  simp [cauchyProfileThirdDeriv]
  field_simp
  ring

private theorem cauchyProfile_contDiff_three
    {y : ℝ} (hy : y ≠ 0) : ContDiff ℝ 3 (cauchyProfile y) := by
  unfold cauchyProfile
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · intro t
    have : 0 < ((1 / 4 + t) ^ 2 + y ^ 2) := by positivity
    exact this.ne'

private def correctedTrapezoidKernel (a t : ℝ) : ℝ :=
  (t - a) ^ 2 / 4 - (t - a) ^ 3 / 6 - (t - a) / 12

private theorem hasDerivAt_correctedTrapezoidKernel (a t : ℝ) :
    HasDerivAt (correctedTrapezoidKernel a)
      (((t - a) * (a + 1 - t) / 2) - 1 / 12) t := by
  unfold correctedTrapezoidKernel
  convert ((((hasDerivAt_id t).sub_const a).pow 2).div_const 4).sub
    ((((hasDerivAt_id t).sub_const a).pow 3).div_const 6) |>.sub
      (((hasDerivAt_id t).sub_const a).div_const 12) using 1
  simp only [id_eq]
  ring

private theorem abs_correctedTrapezoidKernel_le
    {a t : ℝ} (ht : t ∈ Icc a (a + 1)) :
    |correctedTrapezoidKernel a t| ≤ 1 / 12 := by
  let x : ℝ := t - a
  have hx0 : 0 ≤ x := by dsimp [x]; linarith [ht.1]
  have hx1 : x ≤ 1 := by dsimp [x]; linarith [ht.2]
  have honeSub : 0 ≤ 1 - x := by linarith
  have honeSubLe : 1 - x ≤ 1 := by linarith
  have habs : |2 * x - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hfactor : correctedTrapezoidKernel a t =
      x * (1 - x) * (2 * x - 1) / 12 := by
    dsimp [correctedTrapezoidKernel, x]
    ring
  rw [hfactor, abs_div, abs_mul, abs_mul,
    abs_of_nonneg hx0, abs_of_nonneg honeSub, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 12)
  calc
    x * (1 - x) * |2 * x - 1| ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

private theorem corrected_trapezoidal_error_one_le
    {f f' f'' f''' : ℝ → ℝ} {a : ℝ}
    (hf' : ∀ t, HasDerivAt f (f' t) t)
    (hf'' : ∀ t, HasDerivAt f' (f'' t) t)
    (hf''' : ∀ t, HasDerivAt f'' (f''' t) t)
    (hf'''_int : IntervalIntegrable f''' volume a (a + 1)) :
    |trapezoidal_error f 1 a (a + 1) -
        (f' (a + 1) - f' a) / 12| ≤
      (1 / 12 : ℝ) * ∫ t in a..a + 1, |f''' t| := by
  let w : ℝ → ℝ := fun t ↦ (t - a) * (a + 1 - t) / 2
  let q : ℝ → ℝ := fun t ↦ w t - 1 / 12
  let Q : ℝ → ℝ := correctedTrapezoidKernel a
  have hf'_cont : Continuous f' :=
    continuous_iff_continuousAt.mpr fun t ↦ (hf'' t).continuousAt
  have hf''_cont : Continuous f'' :=
    continuous_iff_continuousAt.mpr fun t ↦ (hf''' t).continuousAt
  have hf'_int : IntervalIntegrable f' volume a (a + 1) :=
    hf'_cont.intervalIntegrable _ _
  have hf''_int : IntervalIntegrable f'' volume a (a + 1) :=
    hf''_cont.intervalIntegrable _ _
  have htrap := trapezoidal_error_one_eq_integral_secondDerivKernel
    hf' hf'' hf'_int hf''_int
  have hderiv : deriv f' = f'' := by
    funext t
    exact (hf'' t).deriv
  have hderivIntegral :
      (∫ t in a..a + 1, f'' t) = f' (a + 1) - f' a := by
    exact intervalIntegral.integral_deriv_eq_sub' f' hderiv
      (fun t _ht ↦ (hf'' t).differentiableAt) hf''_cont.continuousOn
  have hQderiv : ∀ t, HasDerivAt Q (q t) t := by
    intro t
    simpa only [Q, q, w] using hasDerivAt_correctedTrapezoidKernel a t
  have hQ_cont : Continuous Q :=
    continuous_iff_continuousAt.mpr fun t ↦ (hQderiv t).continuousAt
  have hq_int : IntervalIntegrable q volume a (a + 1) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := Q) (u' := q) (v := f'') (v' := f''')
    (a := a) (b := a + 1)
    (fun t _ht ↦ hQderiv t) (fun t _ht ↦ hf''' t) hq_int hf'''_int
  have hQleft : Q a = 0 := by simp [Q, correctedTrapezoidKernel]
  have hQright : Q (a + 1) = 0 := by
    simp [Q, correctedTrapezoidKernel]
    ring
  simp only [hQleft, hQright, zero_mul, sub_zero, zero_sub] at hparts
  have hwf_int : IntervalIntegrable (fun t ↦ w t * f'' t) volume a (a + 1) :=
    hf''_int.continuousOn_mul (by fun_prop)
  have hscaled_int : IntervalIntegrable
      (fun t ↦ (1 / 12 : ℝ) * f'' t) volume a (a + 1) :=
    hf''_int.const_mul (1 / 12 : ℝ)
  have hcorrected :
      trapezoidal_error f 1 a (a + 1) -
          (f' (a + 1) - f' a) / 12 =
        -(∫ t in a..a + 1, Q t * f''' t) := by
    rw [htrap]
    change (∫ t in a..a + 1, w t * f'' t) -
        (f' (a + 1) - f' a) / 12 = _
    have hscaled :
        (f' (a + 1) - f' a) / 12 =
          ∫ t in a..a + 1, (1 / 12 : ℝ) * f'' t := by
      rw [intervalIntegral.integral_const_mul, hderivIntegral]
      ring
    rw [hscaled, ← intervalIntegral.integral_sub hwf_int hscaled_int]
    rw [show (fun t ↦ w t * f'' t - (1 / 12 : ℝ) * f'' t) =
        fun t ↦ q t * f'' t by
      funext t
      dsimp only [q]
      ring]
    linarith [hparts]
  rw [hcorrected, abs_neg]
  calc
    |∫ t in a..a + 1, Q t * f''' t| ≤
        ∫ t in a..a + 1, |Q t * f''' t| :=
      intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ t in a..a + 1, (1 / 12 : ℝ) * |f''' t| := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (hf'''_int.continuousOn_mul hQ_cont.continuousOn).abs
      · exact hf'''_int.abs.const_mul (1 / 12 : ℝ)
      · intro t ht
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (abs_correctedTrapezoidKernel_le ht) (abs_nonneg (f''' t))
    _ = (1 / 12 : ℝ) * ∫ t in a..a + 1, |f''' t| := by
      rw [intervalIntegral.integral_const_mul]

private theorem continuous_cauchyProfileThirdDeriv
    {y : ℝ} (hy : y ≠ 0) : Continuous (cauchyProfileThirdDeriv y) := by
  unfold cauchyProfileThirdDeriv
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    have : 0 < (1 / 4 + t) ^ 2 + y ^ 2 := by positivity
    exact (pow_pos this 4).ne'

private theorem cauchyProfileThirdDeriv_nonneg_before
    {y t : ℝ} (hy : 0 < y) (ht0 : 0 ≤ t) (ht : t ≤ y - 1 / 4) :
    0 ≤ cauchyProfileThirdDeriv y t := by
  have hx0 : 0 ≤ (1 / 4 : ℝ) + t := by positivity
  have hxy : (1 / 4 : ℝ) + t ≤ y := by linarith
  have hsq : ((1 / 4 : ℝ) + t) ^ 2 ≤ y ^ 2 :=
    pow_le_pow_left₀ hx0 hxy 2
  have hdiff : 0 ≤ y ^ 2 - ((1 / 4 : ℝ) + t) ^ 2 := sub_nonneg.mpr hsq
  unfold cauchyProfileThirdDeriv
  exact div_nonneg (by positivity) (by positivity)

private theorem cauchyProfileThirdDeriv_nonpos_after
    {y t : ℝ} (hy : 0 < y) (ht : y - 1 / 4 ≤ t) :
    cauchyProfileThirdDeriv y t ≤ 0 := by
  have hxy : y ≤ (1 / 4 : ℝ) + t := by linarith
  have hx0 : 0 ≤ (1 / 4 : ℝ) + t := hy.le.trans hxy
  have hsq : y ^ 2 ≤ ((1 / 4 : ℝ) + t) ^ 2 :=
    pow_le_pow_left₀ hy.le hxy 2
  unfold cauchyProfileThirdDeriv
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hsq))
    (by positivity)

private theorem cauchyProfileSecondDeriv_nonneg_after
    {y t : ℝ} (hy : 0 < y) (ht : y - 1 / 4 ≤ t) :
    0 ≤ cauchyProfileSecondDeriv y t := by
  have hxy : y ≤ (1 / 4 : ℝ) + t := by linarith
  have hx0 : 0 ≤ (1 / 4 : ℝ) + t := hy.le.trans hxy
  have hsq : y ^ 2 ≤ ((1 / 4 : ℝ) + t) ^ 2 :=
    pow_le_pow_left₀ hy.le hxy 2
  unfold cauchyProfileSecondDeriv
  have : 0 ≤ 3 * ((1 / 4 : ℝ) + t) ^ 2 - y ^ 2 := by
    nlinarith [sq_nonneg ((1 / 4 : ℝ) + t)]
  positivity

private theorem cauchyProfileSecondDeriv_transition
    {y : ℝ} (hy : 0 < y) :
    cauchyProfileSecondDeriv y (y - 1 / 4) = 1 / (2 * y ^ 3) := by
  unfold cauchyProfileSecondDeriv
  field_simp [hy.ne']
  ring

private theorem cauchyProfileSecondDeriv_zero_lower
    {y : ℝ} (hy : 0 < y) :
    -(2 / y ^ 3) ≤ cauchyProfileSecondDeriv y 0 := by
  have hy3 : 0 < y ^ 3 := pow_pos hy 3
  have hden : 0 < (1 / 16 : ℝ) + y ^ 2 := by positivity
  rw [show -(2 / y ^ 3) = (-(2 : ℝ)) / y ^ 3 by ring]
  rw [div_le_iff₀ hy3]
  unfold cauchyProfileSecondDeriv
  norm_num
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hden 3)]
  have hidentity :
      (-(2 : ℝ)) * ((1 / 16 + y ^ 2) ^ 3) ≤
        (2 * y * (3 / 16 - y ^ 2)) * y ^ 3 := by
    rw [← sub_nonneg]
    ring_nf
    positivity
  exact hidentity

private theorem integral_abs_cauchyProfileThirdDeriv_le
    {y : ℝ} (hy : 1 ≤ y) (N : ℕ) :
    (∫ t in (0 : ℝ)..N, |cauchyProfileThirdDeriv y t|) ≤
      3 / y ^ 3 := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  let c : ℝ := y - 1 / 4
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hthirdCont := continuous_cauchyProfileThirdDeriv hy0.ne'
  have habsInt (u v : ℝ) : IntervalIntegrable
      (fun t ↦ |cauchyProfileThirdDeriv y t|) volume u v :=
    hthirdCont.abs.intervalIntegrable _ _
  have hthirdInt (u v : ℝ) : IntervalIntegrable
      (cauchyProfileThirdDeriv y) volume u v :=
    hthirdCont.intervalIntegrable _ _
  have hFTC (u v : ℝ) :
      (∫ t in u..v, cauchyProfileThirdDeriv y t) =
        cauchyProfileSecondDeriv y v - cauchyProfileSecondDeriv y u := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _ht
      exact hasDerivAt_cauchyProfileSecondDeriv hy0.ne'
    · exact hthirdInt u v
  have hcvalue : cauchyProfileSecondDeriv y c = 1 / (2 * y ^ 3) := by
    dsimp only [c]
    exact cauchyProfileSecondDeriv_transition hy0
  have hzero : -(2 / y ^ 3) ≤ cauchyProfileSecondDeriv y 0 :=
    cauchyProfileSecondDeriv_zero_lower hy0
  by_cases hNc : (N : ℝ) ≤ c
  · have habsEq :
        (∫ t in (0 : ℝ)..N, |cauchyProfileThirdDeriv y t|) =
          ∫ t in (0 : ℝ)..N, cauchyProfileThirdDeriv y t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (Nat.cast_nonneg N)] at ht
      change |cauchyProfileThirdDeriv y t| = _
      rw [abs_of_nonneg]
      exact cauchyProfileThirdDeriv_nonneg_before hy0 ht.1 (ht.2.trans hNc)
    rw [habsEq, hFTC]
    have hmono : cauchyProfileSecondDeriv y (N : ℝ) ≤
        cauchyProfileSecondDeriv y c := by
      have hnonneg : 0 ≤ ∫ t in (N : ℝ)..c, cauchyProfileThirdDeriv y t := by
        apply intervalIntegral.integral_nonneg (by exact hNc)
        intro t ht
        exact cauchyProfileThirdDeriv_nonneg_before hy0
          (by linarith [ht.1]) ht.2
      rw [hFTC] at hnonneg
      linarith
    rw [hcvalue] at hmono
    have hy3 : 0 < y ^ 3 := pow_pos hy0 3
    apply (le_div_iff₀ hy3).2
    have hzero' :
        -(2 : ℝ) ≤ cauchyProfileSecondDeriv y 0 * y ^ 3 := by
      have := mul_le_mul_of_nonneg_right hzero hy3.le
      convert this using 1
      field_simp [hy3.ne']
    have hmono' :
        cauchyProfileSecondDeriv y (N : ℝ) * y ^ 3 ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_right hmono hy3.le
      convert this using 1
      field_simp [hy3.ne']
    nlinarith
  · have hcN : c ≤ (N : ℝ) := le_of_not_ge hNc
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (habsInt 0 c) (habsInt c N)
    rw [← hsplit]
    have hfirst :
        (∫ t in (0 : ℝ)..c, |cauchyProfileThirdDeriv y t|) =
          ∫ t in (0 : ℝ)..c, cauchyProfileThirdDeriv y t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hc0] at ht
      change |cauchyProfileThirdDeriv y t| = _
      rw [abs_of_nonneg]
      exact cauchyProfileThirdDeriv_nonneg_before hy0 ht.1 ht.2
    have hsecond :
        (∫ t in c..N, |cauchyProfileThirdDeriv y t|) =
          -(∫ t in c..N, cauchyProfileThirdDeriv y t) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hcN] at ht
      change |cauchyProfileThirdDeriv y t| = _
      rw [abs_of_nonpos]
      exact cauchyProfileThirdDeriv_nonpos_after hy0 ht.1
    rw [hfirst, hsecond, hFTC, hFTC]
    have hNnonneg := cauchyProfileSecondDeriv_nonneg_after hy0 hcN
    rw [hcvalue]
    have hy3 : 0 < y ^ 3 := pow_pos hy0 3
    apply (le_div_iff₀ hy3).2
    have hzero' :
        -(2 : ℝ) ≤ cauchyProfileSecondDeriv y 0 * y ^ 3 := by
      have := mul_le_mul_of_nonneg_right hzero hy3.le
      convert this using 1
      field_simp [hy3.ne']
    calc
      (1 / (2 * y ^ 3) - cauchyProfileSecondDeriv y 0 +
          -(cauchyProfileSecondDeriv y (N : ℝ) - 1 / (2 * y ^ 3))) * y ^ 3 =
          1 - cauchyProfileSecondDeriv y 0 * y ^ 3 -
            cauchyProfileSecondDeriv y (N : ℝ) * y ^ 3 := by
        field_simp [hy3.ne']
        ring
      _ ≤ 3 := by
        nlinarith [mul_nonneg hNnonneg hy3.le]

private def cauchyProfileError (y : ℝ) (k : ℕ) : ℝ :=
  trapezoidal_error (cauchyProfile y) 1 k (k + 1)

private theorem sum_range_cauchyProfileError
    {y : ℝ} (hy : y ≠ 0) (N : ℕ) :
    (∑ k ∈ Finset.range N, cauchyProfileError y k) =
      trapezoidal_error (cauchyProfile y) N 0 N := by
  cases N with
  | zero => simp [cauchyProfileError]
  | succ N =>
      have hcont := (cauchyProfile_contDiff_three hy).continuous
      have hint : IntervalIntegrable (cauchyProfile y)
          volume 0 (0 + ((N + 1 : ℕ) : ℝ) * 1) :=
        hcont.intervalIntegrable _ _
      have hsum := sum_trapezoidal_error_adjacent_intervals
        (f := cauchyProfile y) (a := 0) (h := 1) (N := N + 1)
        (Nat.succ_pos N) hint
      simpa [cauchyProfileError] using hsum

private theorem corrected_cauchyProfileError_le
    {y : ℝ} (hy : 0 < y) (k : ℕ) :
    |cauchyProfileError y k -
        (cauchyProfileDeriv y (k + 1) - cauchyProfileDeriv y k) / 12| ≤
      (1 / 12 : ℝ) *
        ∫ t in (k : ℝ)..k + 1, |cauchyProfileThirdDeriv y t| := by
  unfold cauchyProfileError
  exact corrected_trapezoidal_error_one_le
    (fun t ↦ hasDerivAt_cauchyProfile (y := y) (t := t) hy.ne')
    (fun t ↦ hasDerivAt_cauchyProfileDeriv (y := y) (t := t) hy.ne')
    (fun t ↦ hasDerivAt_cauchyProfileSecondDeriv (y := y) (t := t) hy.ne')
    ((continuous_cauchyProfileThirdDeriv hy.ne').intervalIntegrable _ _)

private theorem corrected_cauchyProfileError_sum_le
    {y : ℝ} (hy : 1 ≤ y) (N : ℕ) :
    |(∑ k ∈ Finset.range N, cauchyProfileError y k) -
        (cauchyProfileDeriv y N - cauchyProfileDeriv y 0) / 12| ≤
      1 / (4 * y ^ 3) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have htel :
      (∑ k ∈ Finset.range N,
        (cauchyProfileDeriv y (k + 1) - cauchyProfileDeriv y k)) =
          cauchyProfileDeriv y N - cauchyProfileDeriv y 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      (Finset.sum_range_sub (fun k : ℕ ↦ cauchyProfileDeriv y (k : ℝ)) N)
  have hrewrite :
      (∑ k ∈ Finset.range N, cauchyProfileError y k) -
          (cauchyProfileDeriv y N - cauchyProfileDeriv y 0) / 12 =
        ∑ k ∈ Finset.range N,
          (cauchyProfileError y k -
            (cauchyProfileDeriv y (k + 1) - cauchyProfileDeriv y k) / 12) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, htel]
  rw [hrewrite]
  calc
    |∑ k ∈ Finset.range N,
        (cauchyProfileError y k -
          (cauchyProfileDeriv y (k + 1) - cauchyProfileDeriv y k) / 12)| ≤
        ∑ k ∈ Finset.range N,
          |cauchyProfileError y k -
            (cauchyProfileDeriv y (k + 1) - cauchyProfileDeriv y k) / 12| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, (1 / 12 : ℝ) *
          ∫ t in (k : ℝ)..k + 1, |cauchyProfileThirdDeriv y t| := by
      exact Finset.sum_le_sum fun k _hk ↦ corrected_cauchyProfileError_le hy0 k
    _ = (1 / 12 : ℝ) *
          ∫ t in (0 : ℝ)..N, |cauchyProfileThirdDeriv y t| := by
      rw [← Finset.mul_sum]
      congr 1
      have hsum := intervalIntegral.sum_integral_adjacent_intervals
        (f := fun t ↦ |cauchyProfileThirdDeriv y t|)
        (a := fun k : ℕ ↦ (k : ℝ)) (n := N) (μ := volume)
        (fun k _hk ↦
          (continuous_cauchyProfileThirdDeriv hy0.ne').abs.intervalIntegrable _ _)
      simpa using hsum
    _ ≤ (1 / 12 : ℝ) * (3 / y ^ 3) := by
      gcongr
      exact integral_abs_cauchyProfileThirdDeriv_le hy N
    _ = 1 / (4 * y ^ 3) := by ring

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
  · exact (cauchyProfile_contDiff_three hy).continuous.intervalIntegrable _ _

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

private theorem abs_cauchyProfileDeriv_le_inv
    {y : ℝ} (hy : 0 < y) {N : ℕ} (hN : 1 ≤ N) :
    |cauchyProfileDeriv y N| ≤ 2 * y / N := by
  let x : ℝ := (1 / 4 : ℝ) + N
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hxN : (N : ℝ) ≤ x := by dsimp [x]; linarith
  have hx1 : 1 ≤ x := hNR.trans hxN
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx1
  have hden : 0 < x ^ 2 + y ^ 2 := by positivity
  have hdenPow : (x ^ 2) ^ 2 ≤ (x ^ 2 + y ^ 2) ^ 2 := by
    exact pow_le_pow_left₀ (sq_nonneg x)
      (by nlinarith [sq_nonneg y]) 2
  have hxCube : (N : ℝ) ≤ x ^ 3 := by
    have hfactor : 0 ≤ x * (x - 1) * (x + 1) := by
      exact mul_nonneg (mul_nonneg hx0.le (sub_nonneg.mpr hx1)) (by linarith)
    have hxLeCube : x ≤ x ^ 3 := by nlinarith
    exact hxN.trans hxLeCube
  unfold cauchyProfileDeriv
  change |-2 * y * x / (x ^ 2 + y ^ 2) ^ 2| ≤ _
  rw [abs_div, abs_mul, abs_mul, abs_of_nonpos (by norm_num : (-(2 : ℝ)) ≤ 0),
    abs_of_pos hy, abs_of_pos hx0, abs_of_pos (pow_pos hden 2)]
  norm_num
  calc
    2 * y * x / (x ^ 2 + y ^ 2) ^ 2 ≤
        2 * y * x / (x ^ 2) ^ 2 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hdenPow
    _ = 2 * y / x ^ 3 := by field_simp [hx0.ne']
    _ ≤ 2 * y / N := by
      exact div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast (Nat.zero_lt_of_lt hN)) hxCube

private theorem tendsto_cauchyProfileDeriv_nat
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun N : ℕ ↦ cauchyProfileDeriv y N) atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N ↦ abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact abs_cauchyProfileDeriv_le_inv hy hN
  · exact tendsto_const_div_atTop_nhds_zero_nat (2 * y)

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

private theorem cauchyProfile_tsum_corrected_bound
    {y : ℝ} (hy : 1 ≤ y)
    (hs : Summable (fun k : ℕ ↦ cauchyProfile y k)) :
    |(∑' k : ℕ, cauchyProfile y k) -
        (Real.pi / 2 - Real.arctan ((1 / 4) / y)) -
        cauchyProfile y 0 / 2 + cauchyProfileDeriv y 0 / 12| ≤
      1 / (4 * y ^ 3) := by
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hpartial : Tendsto
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1), cauchyProfile y k)
      atTop (nhds (∑' k : ℕ, cauchyProfile y k)) :=
    hs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hlast := tendsto_cauchyProfile_nat hy0
  have hint := tendsto_integral_cauchyProfile hy0
  have hendpoint : Tendsto
      (fun N : ℕ ↦ (cauchyProfile y 0 + cauchyProfile y N) / 2)
      atTop (nhds (cauchyProfile y 0 / 2)) := by
    convert (tendsto_const_nhds.add hlast).div_const 2 using 1
    ring
  have hformulaLim : Tendsto
      (fun N : ℕ ↦
        (∑ k ∈ Finset.range (N + 1), cauchyProfile y k) -
          (cauchyProfile y 0 + cauchyProfile y N) / 2 -
          ∫ t in 0..N, cauchyProfile y t)
      atTop
      (nhds ((∑' k : ℕ, cauchyProfile y k) - cauchyProfile y 0 / 2 -
        (Real.pi / 2 - Real.arctan ((1 / 4) / y)))) :=
    (hpartial.sub hendpoint).sub hint
  have herrorLim : Tendsto
      (fun N : ℕ ↦ ∑ k ∈ Finset.range N, cauchyProfileError y k)
      atTop
      (nhds ((∑' k : ℕ, cauchyProfile y k) - cauchyProfile y 0 / 2 -
        (Real.pi / 2 - Real.arctan ((1 / 4) / y)))) := by
    apply hformulaLim.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [sum_range_cauchyProfileError hy0.ne',
      trapezoidal_error_cauchyProfile_eq hN]
  have hderiv := tendsto_cauchyProfileDeriv_nat hy0
  have hderivDiff : Tendsto
      (fun N : ℕ ↦
        (cauchyProfileDeriv y N - cauchyProfileDeriv y 0) / 12)
      atTop (nhds ((0 - cauchyProfileDeriv y 0) / 12)) :=
    (hderiv.sub tendsto_const_nhds).div_const 12
  have hlim := herrorLim.sub hderivDiff
  have hlim' : Tendsto
      (fun N : ℕ ↦
        (∑ k ∈ Finset.range N, cauchyProfileError y k) -
          (cauchyProfileDeriv y N - cauchyProfileDeriv y 0) / 12)
      atTop
      (nhds ((∑' k : ℕ, cauchyProfile y k) -
        (Real.pi / 2 - Real.arctan ((1 / 4) / y)) -
        cauchyProfile y 0 / 2 + cauchyProfileDeriv y 0 / 12)) := by
    convert hlim using 1
    all_goals ring
  exact le_of_tendsto' hlim'.abs fun N ↦
    corrected_cauchyProfileError_sum_le hy N

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

private theorem cauchyProfile_endpoint_correction_abs_le
    {y : ℝ} (hy : 1 ≤ y) :
    |-Real.arctan ((1 / 4) / y) + cauchyProfile y 0 / 2 - 1 / (4 * y)| ≤
      1 / (32 * y ^ 3) := by
  let z : ℝ := (1 / 4) / y
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    rw [div_le_iff₀ hy0]
    nlinarith
  have hlower := arctan_lower_rational hz0
  have hupper := arctan_upper_linear hz0
  have hprofile : cauchyProfile y 0 / 2 = 2 * z / (1 + z ^ 2) := by
    dsimp [cauchyProfile, z]
    field_simp [hy0.ne']
    ring
  have hinv : 1 / (4 * y) = z := by
    dsimp [z]
    ring
  rw [hprofile, hinv]
  let D : ℝ := -Real.arctan z + 2 * z / (1 + z ^ 2) - z
  have hden : 0 < 1 + z ^ 2 := by positivity
  have hDnonpos : D ≤ 0 := by
    have hcompare : 2 * z / (1 + z ^ 2) - z ≤
        z / (1 + z ^ 2) := by
      rw [sub_le_iff_le_add]
      apply (div_le_iff₀ hden).2
      field_simp [hden.ne']
      nlinarith [mul_nonneg hz0 (sq_nonneg z)]
    dsimp only [D]
    linarith
  have hDlower : -(2 * z ^ 3) ≤ D := by
    have hfrac : -(2 * z ^ 3) ≤ -2 * z + 2 * z / (1 + z ^ 2) := by
      rw [show -2 * z + 2 * z / (1 + z ^ 2) =
          -(2 * z ^ 3 / (1 + z ^ 2)) by
        field_simp [hden.ne']
        ring]
      have hfracLe : 2 * z ^ 3 / (1 + z ^ 2) ≤ 2 * z ^ 3 := by
        rw [div_le_iff₀ hden]
        nlinarith [mul_nonneg (show 0 ≤ 2 * z ^ 3 by positivity) (sq_nonneg z)]
      linarith
    dsimp only [D]
    linarith
  change |D| ≤ _
  rw [abs_of_nonpos hDnonpos]
  have hzIdentity : 2 * z ^ 3 = 1 / (32 * y ^ 3) := by
    dsimp [z]
    field_simp [hy0.ne']
    ring
  rw [← hzIdentity]
  linarith

private theorem abs_cauchyProfileDeriv_zero_le
    {y : ℝ} (hy : 0 < y) :
    |cauchyProfileDeriv y 0| ≤ 1 / (2 * y ^ 3) := by
  have hden : 0 < (1 / 16 : ℝ) + y ^ 2 := by positivity
  unfold cauchyProfileDeriv
  norm_num
  rw [abs_div, abs_neg, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hy,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4),
    abs_of_pos (pow_pos hden 2)]
  norm_num
  rw [show (y ^ 3)⁻¹ * (1 / 2 : ℝ) = 1 / (2 * y ^ 3) by ring]
  apply (div_le_div_iff₀ (pow_pos hden 2) (by positivity : 0 < 2 * y ^ 3)).2
  nlinarith [sq_nonneg y, sq_nonneg ((1 / 16 : ℝ) + y ^ 2)]


private theorem cauchyProfile_cubic_remainder
    {y : ℝ} (hy : 4 < y)
    (hs : Summable (fun k : ℕ ↦ cauchyProfile y k)) :
    |(∑' k : ℕ, cauchyProfile y k) -
        (Real.pi / 2 + 1 / (4 * y))| ≤
      31 / (96 * y ^ 3) := by
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  let A : ℝ := (∑' k : ℕ, cauchyProfile y k) -
    (Real.pi / 2 - Real.arctan ((1 / 4) / y)) -
    cauchyProfile y 0 / 2 + cauchyProfileDeriv y 0 / 12
  let D : ℝ := -Real.arctan ((1 / 4) / y) +
    cauchyProfile y 0 / 2 - 1 / (4 * y)
  have hA : |A| ≤ 1 / (4 * y ^ 3) := by
    dsimp only [A]
    exact cauchyProfile_tsum_corrected_bound hy1 hs
  have hD : |D| ≤ 1 / (32 * y ^ 3) := by
    dsimp only [D]
    exact cauchyProfile_endpoint_correction_abs_le hy1
  have hd := abs_cauchyProfileDeriv_zero_le hy0
  have hidentity :
      (∑' k : ℕ, cauchyProfile y k) -
          (Real.pi / 2 + 1 / (4 * y)) =
        A + D - cauchyProfileDeriv y 0 / 12 := by
    dsimp only [A, D]
    ring
  rw [hidentity]
  calc
    |A + D - cauchyProfileDeriv y 0 / 12| ≤
        |A| + |D| + |cauchyProfileDeriv y 0| / 12 := by
      have h := abs_sub (A + D) (cauchyProfileDeriv y 0 / 12)
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)] at h
      linarith [abs_add_le A D]
    _ ≤ 1 / (4 * y ^ 3) + 1 / (32 * y ^ 3) +
        (1 / (2 * y ^ 3)) / 12 := by gcongr
    _ = 31 / (96 * y ^ 3) := by ring

/-!
# Scalable enclosures for the high even sine moments

The first regression target is a cubic-strength enclosure for the imaginary
digamma sample.  It is stated before its implementation so the strict Lean
check supplies the red phase of the proof-development cycle.
-/

theorem yoshidaEvenDigammaImag_cubic_remainder
    (n : ℕ) (hn : 1 ≤ n) :
    |yoshidaEvenDigammaImag n -
        digammaAsymptoticMain yoshidaA n| ≤
      31 / (96 * evenDigammaY n ^ 3) := by
  let y : ℝ := evenDigammaY n
  have hn0 : n ≠ 0 := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := strict_log_two_bounds
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hyEq : y = Real.pi * (n : ℝ) / Real.log 2 := by
    dsimp only [y, evenDigammaY, yoshidaA]
    ring
  have hy4 : 4 < y := by
    rw [hyEq]
    apply (lt_div_iff₀ hlogPos).2
    nlinarith [hlog.2]
  have hfun : (fun k : ℕ ↦ evenDigammaCauchyTerm n k) =
      fun k : ℕ ↦ cauchyProfile y k := by
    funext k
    dsimp only [evenDigammaCauchyTerm, cauchyProfile, y]
    congr 2
    ring
  have hs : Summable (fun k : ℕ ↦ cauchyProfile y k) := by
    rw [← hfun]
    exact summable_evenDigammaCauchyTerm n
  have hsharp := cauchyProfile_cubic_remainder hy4 hs
  have hmain :
      digammaAsymptoticMain yoshidaA n =
        Real.pi / 2 + 1 / (4 * y) := by
    dsimp only [digammaAsymptoticMain, y, evenDigammaY]
    field_simp [hn0, YoshidaCoercivityNumerics.yoshidaA_pos.ne', Real.pi_ne_zero]
    ring
  rw [yoshidaEvenDigammaImag_eq_tsum, hfun, hmain]
  exact hsharp

theorem evenDigammaY_eq_yoshidaScaledFrequency (n : ℕ) :
    evenDigammaY n = yoshidaScaledFrequency n := by
  rw [evenDigammaY, yoshidaScaledFrequency, yoshidaKappa, yoshidaA,
    yoshidaLength]
  ring

/-- The sine moment is the polar term minus the imaginary digamma sample,
plus only the exponentially small endpoint correction. -/
theorem yoshidaSineMoment_eq_polar_sub_digamma_add_dyadic
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaSineMoment n = sinePolarValue n - yoshidaEvenDigammaImag n +
      ∑' k : ℕ, sineDyadicCorrection n k := by
  rw [yoshidaSineMoment_eq_explicitCauchySeries hn]
  have hmain := summable_sineMainTerm hn
  have hcorr := summable_sineDyadicCorrection hn
  have hsplit : (∑' k : ℕ, sineCauchyTerm n k) =
      (∑' k : ℕ, sineMainTerm n k) -
        ∑' k : ℕ, sineDyadicCorrection n k := by
    rw [← hmain.tsum_sub hcorr]
    apply tsum_congr
    exact sineCauchyTerm_eq_main_sub_correction n
  rw [hsplit, yoshidaEvenDigammaImag_eq_tsum]
  have hmainEq : (fun k : ℕ ↦ sineMainTerm n k) =
      evenDigammaCauchyTerm n := by
    funext k
    rw [sineMainTerm, cauchyTailTerm, evenDigammaCauchyTerm,
      evenDigammaY_eq_yoshidaScaledFrequency]
    congr 2
    ring
  rw [hmainEq]
  ring

private theorem sineMainTerm_le_inv_frequency
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    sineMainTerm n k ≤ 1 / yoshidaScaledFrequency n := by
  have hy := yoshidaScaledFrequency_pos hn
  rw [sineMainTerm, cauchyTailTerm]
  rw [div_le_div_iff₀ (by positivity :
    0 < ((1 / 4 : ℝ) + k) ^ 2 + yoshidaScaledFrequency n ^ 2) hy]
  nlinarith [sq_nonneg ((1 / 4 : ℝ) + k)]

private theorem sineDyadicCorrection_le_inv_geometric
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    sineDyadicCorrection n k ≤
      (1 / yoshidaScaledFrequency n) * (1 / 4 : ℝ) ^ k := by
  have hy := yoshidaScaledFrequency_pos hn
  have hmain0 := sineMainTerm_nonneg hn k
  have hmain := sineMainTerm_le_inv_frequency hn k
  have hsqrt : (Real.sqrt 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact Real.one_le_sqrt.mpr (by norm_num)
  rw [sineDyadicCorrection, div_eq_mul_inv, ← inv_pow]
  calc
    sineMainTerm n k * (Real.sqrt 2)⁻¹ * ((4 : ℝ)⁻¹) ^ k ≤
        (1 / yoshidaScaledFrequency n) * 1 * ((4 : ℝ)⁻¹) ^ k := by
      gcongr
    _ = (1 / yoshidaScaledFrequency n) * (1 / 4 : ℝ) ^ k := by
      ring

/-- The correction tail uses the high-frequency denominator rather than the
frequency-growing coarse bound used by the low-mode checkpoint layer. -/
theorem sineDyadicCorrection_tail_high_le
    {n K : ℕ} (hn : n ≠ 0) :
    (∑' j : ℕ, sineDyadicCorrection n (K + j)) ≤
      2 / (yoshidaScaledFrequency n * (4 : ℝ) ^ K) := by
  let C : ℝ := 1 / (yoshidaScaledFrequency n * (4 : ℝ) ^ K)
  have hy := yoshidaScaledFrequency_pos hn
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hgeom : Summable (fun j : ℕ ↦ C * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left C
  have hcorr : Summable
      (fun j : ℕ ↦ sineDyadicCorrection n (K + j)) := by
    simpa [Nat.add_comm] using
      (summable_nat_add_iff K).2 (summable_sineDyadicCorrection hn)
  have hpoint (j : ℕ) : sineDyadicCorrection n (K + j) ≤
      C * (1 / 4 : ℝ) ^ j := by
    have h := sineDyadicCorrection_le_inv_geometric hn (K + j)
    rw [pow_add] at h
    calc
      sineDyadicCorrection n (K + j) ≤
          (1 / yoshidaScaledFrequency n) *
            ((1 / 4 : ℝ) ^ K * (1 / 4 : ℝ) ^ j) := h
      _ = C * (1 / 4 : ℝ) ^ j := by
        dsimp only [C]
        field_simp [hy.ne']
        norm_num [div_pow]
  have hsum := hcorr.tsum_le_tsum hpoint hgeom
  calc
    (∑' j : ℕ, sineDyadicCorrection n (K + j)) ≤
        ∑' j : ℕ, C * (1 / 4 : ℝ) ^ j := hsum
    _ = C * ((1 - (1 / 4 : ℝ))⁻¹) := by
      rw [tsum_mul_left,
        tsum_geometric_of_norm_lt_one
          (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
    _ ≤ C * 2 := by
      gcongr
      norm_num
    _ = 2 / (yoshidaScaledFrequency n * (4 : ℝ) ^ K) := by
      dsimp only [C]
      ring

private theorem evenDigammaY_eq_yoshidaY (n : ℕ) :
    evenDigammaY n = yoshidaY n := by
  rw [evenDigammaY_eq_yoshidaScaledFrequency,
    yoshidaScaledFrequency_eq_y]

private theorem yoshidaYInterval_lower_pos
    {n : ℕ} (hn : n ≠ 0) :
    0 < (yoshidaYInterval n).lower := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  change 0 < piFineInterval.lower * n / logTwoFineInterval.upper
  unfold piFineInterval logTwoFineInterval
  positivity

/-- The elementary asymptotic main term, evaluated with outward rational
constant intervals. -/
def evenDigammaMainInterval (n : ℕ) : RatInterval :=
  piFineInterval / RatInterval.pure 2 +
    (yoshidaYInterval n)⁻¹ / RatInterval.pure 4

theorem evenDigammaMainInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (evenDigammaMainInterval n).Contains
      (digammaAsymptoticMain yoshidaA n) := by
  have hy := yoshidaYInterval_contains n
  have hyInv := contains_inv_of_pos (yoshidaYInterval_lower_pos hn) hy
  have hpiHalf := contains_div_of_pos
    (by norm_num [RatInterval.pure] :
      (0 : ℚ) < (RatInterval.pure 2).lower)
    piFineInterval_contains (contains_pure 2)
  have hyQuarter := contains_div_of_pos
    (by norm_num [RatInterval.pure] :
      (0 : ℚ) < (RatInterval.pure 4).lower)
    hyInv (contains_pure 4)
  have hinterval := contains_add hpiHalf hyQuarter
  have hmain :
      digammaAsymptoticMain yoshidaA n =
        Real.pi / 2 + (yoshidaY n)⁻¹ / 4 := by
    have hlogNe : Real.log 2 ≠ 0 :=
      (Real.log_pos (by norm_num)).ne'
    rw [digammaAsymptoticMain, yoshidaY, yoshidaA, yoshidaLength]
    field_simp [hn, Real.pi_ne_zero, hlogNe]
    ring
  rw [hmain]
  exact hinterval

/-- Exact rational upper bound for the cubic analytic remainder.  The lower
frequency endpoint is used because `y ↦ y⁻³` is decreasing. -/
def evenDigammaCubicRadius (n : ℕ) : ℚ :=
  31 / (96 * (yoshidaYInterval n).lower ^ 3)

def evenDigammaCubicInterval (n : ℕ) : RatInterval :=
  inflateInterval (evenDigammaCubicRadius n)
    (evenDigammaMainInterval n)

theorem evenDigammaCubicInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (evenDigammaCubicInterval n).Contains
      (yoshidaEvenDigammaImag n) := by
  have hmain := evenDigammaMainInterval_contains hn
  have hrem := yoshidaEvenDigammaImag_cubic_remainder n
    (Nat.one_le_iff_ne_zero.mpr hn)
  have hyI := yoshidaYInterval_contains n
  have hyEq := evenDigammaY_eq_yoshidaY n
  have hylQ := yoshidaYInterval_lower_pos hn
  have hyl : (0 : ℝ) < ((yoshidaYInterval n).lower : ℝ) := by
    exact_mod_cast hylQ
  have hy0 : 0 < yoshidaY n := hyl.trans_le hyI.1
  have hden :
      96 * (((yoshidaYInterval n).lower : ℚ) : ℝ) ^ 3 ≤
        96 * yoshidaY n ^ 3 := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hyl.le hyI.1 3) (by norm_num)
  have hradius :
      31 / (96 * evenDigammaY n ^ 3) ≤
        ((evenDigammaCubicRadius n : ℚ) : ℝ) := by
    rw [hyEq]
    norm_num only [evenDigammaCubicRadius, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_mul, Rat.cast_pow]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  exact inflateInterval_contains_of_abs_sub hmain (hrem.trans hradius)

/-- Outward rational interval for one exponentially weighted correction
summand. -/
def sineDyadicCorrectionInterval (n k : ℕ) : RatInterval :=
  (yoshidaYInterval n / cauchyDenomInterval n k) *
      sqrtTwoInterval⁻¹ / pure ((4 : ℚ) ^ k)

theorem sineDyadicCorrectionInterval_contains
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    (sineDyadicCorrectionInterval n k).Contains
      (sineDyadicCorrection n k) := by
  have hy := yoshidaYInterval_contains n
  have hyl := yoshidaYInterval_lower_pos hn
  have hx : (pure (quarterShiftQ k ^ 2)).Contains
      (((k : ℝ) + 1 / 4) ^ 2) := by
    norm_num [Contains, RatInterval.pure, quarterShiftQ]
  have hden : (cauchyDenomInterval n k).Contains
      (((k : ℝ) + 1 / 4) ^ 2 + yoshidaY n ^ 2) := by
    exact contains_add hx (contains_nonnegSquare hyl.le hy)
  have hmain := contains_div_of_pos
    (cauchyDenomInterval_lower_pos n k) hy hden
  have hsInv := contains_inv_of_pos (I := sqrtTwoInterval)
    (x := Real.sqrt 2) (by norm_num [sqrtTwoInterval])
      sqrtTwoInterval_contains
  have hpow : (pure ((4 : ℚ) ^ k)).Contains ((4 : ℝ) ^ k) := by
    simpa using contains_pure ((4 : ℚ) ^ k)
  have hinterval := contains_div_of_pos
    (by change 0 < (4 : ℚ) ^ k; positivity)
    (contains_mul hmain hsInv) hpow
  have hterm : sineDyadicCorrection n k =
      (yoshidaY n /
          (((k : ℝ) + 1 / 4) ^ 2 + yoshidaY n ^ 2) *
        (Real.sqrt 2)⁻¹) / (4 : ℝ) ^ k := by
    rw [sineDyadicCorrection, sineMainTerm, cauchyTailTerm,
      yoshidaScaledFrequency_eq_y]
    simp only [add_comm (1 / 4 : ℝ)]
  rw [hterm]
  exact hinterval

def sineDyadicCorrectionHeadInterval (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | K + 1 => sineDyadicCorrectionHeadInterval n K +
      sineDyadicCorrectionInterval n K

theorem sineDyadicCorrectionHeadInterval_contains
    {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (sineDyadicCorrectionHeadInterval n K).Contains
      (∑ k ∈ Finset.range K, sineDyadicCorrection n k) := by
  induction K with
  | zero =>
      norm_num [sineDyadicCorrectionHeadInterval, Contains,
        RatInterval.pure]
  | succ K ih =>
      rw [Finset.sum_range_succ]
      exact contains_add ih (sineDyadicCorrectionInterval_contains hn K)

/-- A high-frequency geometric tail box.  Unlike the original production
tail, its radius decays as `1 / (y * 4^K)`. -/
def sineDyadicCorrectionTailInterval (n K : ℕ) : RatInterval :=
  ⟨0, 2 / ((yoshidaYInterval n).lower * (4 : ℚ) ^ K)⟩

theorem sineDyadicCorrectionTailInterval_contains
    {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (sineDyadicCorrectionTailInterval n K).Contains
      (∑' j : ℕ, sineDyadicCorrection n (K + j)) := by
  have hlow : 0 ≤ ∑' j : ℕ, sineDyadicCorrection n (K + j) :=
    tsum_nonneg fun j ↦ sineDyadicCorrection_nonneg hn (K + j)
  have hsource := sineDyadicCorrection_tail_high_le (n := n) (K := K) hn
  have hyI := yoshidaYInterval_contains n
  have hylQ := yoshidaYInterval_lower_pos hn
  have hyl : (0 : ℝ) < ((yoshidaYInterval n).lower : ℝ) := by
    exact_mod_cast hylQ
  have hden :
      (((yoshidaYInterval n).lower : ℚ) : ℝ) * (4 : ℝ) ^ K ≤
        yoshidaScaledFrequency n * (4 : ℝ) ^ K := by
    rw [yoshidaScaledFrequency_eq_y]
    exact mul_le_mul_of_nonneg_right hyI.1 (by positivity)
  have hupper :
      (∑' j : ℕ, sineDyadicCorrection n (K + j)) ≤
        2 / ((((yoshidaYInterval n).lower : ℚ) : ℝ) *
          (4 : ℝ) ^ K) := by
    exact hsource.trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) hden)
  constructor
  · simpa [sineDyadicCorrectionTailInterval, Contains] using hlow
  · simpa only [sineDyadicCorrectionTailInterval, Contains,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_pow] using hupper

def sineDyadicCorrectionFullInterval (n K : ℕ) : RatInterval :=
  sineDyadicCorrectionHeadInterval n K +
    sineDyadicCorrectionTailInterval n K

theorem sineDyadicCorrectionFullInterval_contains
    {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (sineDyadicCorrectionFullInterval n K).Contains
      (∑' k : ℕ, sineDyadicCorrection n k) := by
  have hsplit := (summable_sineDyadicCorrection hn).sum_add_tsum_nat_add K
  rw [← hsplit]
  exact contains_add (sineDyadicCorrectionHeadInterval_contains hn K)
    (by simpa [Nat.add_comm] using
      sineDyadicCorrectionTailInterval_contains hn K)

/-- Scalable rational enclosure: a polar interval, the cubic digamma box,
and ten inexpensive dyadic correction terms. -/
def highSineSeriesInterval (n K : ℕ) : RatInterval :=
  sinePolarInterval n - evenDigammaCubicInterval n +
    sineDyadicCorrectionFullInterval n K

theorem highSineSeriesInterval_contains
    {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (highSineSeriesInterval n K).Contains (yoshidaSineMoment n) := by
  rw [yoshidaSineMoment_eq_polar_sub_digamma_add_dyadic hn]
  exact contains_add
    (contains_sub (sinePolarInterval_contains n)
      (evenDigammaCubicInterval_contains hn))
    (sineDyadicCorrectionFullInterval_contains hn K)

/-!
## Exceptional low modes

The cubic enclosure already closes most modes from ten onward.  Six lower
targets need tighter one-off enclosures.  Their exact Cauchy heads are split
into 256-term chunks and rounded outward to the `10⁻¹²` grid; the accelerated
analytic tail then completes each proof without constructing one enormous
rational expression.
-/

private def sixModeSineChunkBox : ℕ → RatInterval
  | 0 => ⟨1439424336309 / 1000000000000, 1439424336395 / 1000000000000⟩
  | 1 => ⟨52843266050 / 1000000000000, 52843266052 / 1000000000000⟩
  | 2 => ⟨17683804756 / 1000000000000, 17683804757 / 1000000000000⟩
  | 3 => ⟨8848751122 / 1000000000000, 8848751123 / 1000000000000⟩
  | 4 => ⟨5310645782 / 1000000000000, 5310645784 / 1000000000000⟩
  | 5 => ⟨3540827020 / 1000000000000, 3540827021 / 1000000000000⟩
  | 6 => ⟨2529298124 / 1000000000000, 2529298126 / 1000000000000⟩
  | 7 => ⟨1897025648 / 1000000000000, 1897025649 / 1000000000000⟩
  | 8 => ⟨1475485449 / 1000000000000, 1475485450 / 1000000000000⟩
  | 9 => ⟨1180396865 / 1000000000000, 1180396866 / 1000000000000⟩
  | 10 => ⟨965782374 / 1000000000000, 965782375 / 1000000000000⟩
  | _ => pure 0

private def sevenModeSineChunkBox : ℕ → RatInterval
  | 0 => ⟨1425560762035 / 1000000000000, 1425560762122 / 1000000000000⟩
  | 1 => ⟨61505303916 / 1000000000000, 61505303918 / 1000000000000⟩
  | 2 => ⟨20616346532 / 1000000000000, 20616346533 / 1000000000000⟩
  | 3 => ⟨10319942873 / 1000000000000, 10319942874 / 1000000000000⟩
  | 4 => ⟨6194470491 / 1000000000000, 6194470493 / 1000000000000⟩
  | 5 => ⟨4130397614 / 1000000000000, 4130397615 / 1000000000000⟩
  | 6 => ⟨2950559267 / 1000000000000, 2950559268 / 1000000000000⟩
  | 7 => ⟨2213034590 / 1000000000000, 2213034591 / 1000000000000⟩
  | 8 => ⟨1721301815 / 1000000000000, 1721301816 / 1000000000000⟩
  | 9 => ⟨1377067092 / 1000000000000, 1377067093 / 1000000000000⟩
  | 10 => ⟨1126704235 / 1000000000000, 1126704236 / 1000000000000⟩
  | _ => pure 0

private def eightModeSineChunkBox : ℕ → RatInterval
  | 0 => ⟨1410868875673 / 1000000000000, 1410868875759 / 1000000000000⟩
  | 1 => ⟨70101438801 / 1000000000000, 70101438804 / 1000000000000⟩
  | 2 => ⟨23542107968 / 1000000000000, 23542107970 / 1000000000000⟩
  | 3 => ⟨11789476698 / 1000000000000, 11789476699 / 1000000000000⟩
  | 4 => ⟨7077703850 / 1000000000000, 7077703851 / 1000000000000⟩
  | 5 => ⟨4719706626 / 1000000000000, 4719706628 / 1000000000000⟩
  | 6 => ⟨3371687317 / 1000000000000, 3371687318 / 1000000000000⟩
  | 7 => ⟨2528968796 / 1000000000000, 2528968797 / 1000000000000⟩
  | 8 => ⟨1967073023 / 1000000000000, 1967073024 / 1000000000000⟩
  | 9 => ⟨1573708441 / 1000000000000, 1573708442 / 1000000000000⟩
  | 10 => ⟨1287606777 / 1000000000000, 1287606778 / 1000000000000⟩
  | 11 => ⟨1073020987 / 1000000000000, 1073020988 / 1000000000000⟩
  | 12 => ⟨907949767 / 1000000000000, 907949768 / 1000000000000⟩
  | 13 => ⟨778247967 / 1000000000000, 778247968 / 1000000000000⟩
  | 14 => ⟨674484764 / 1000000000000, 674484765 / 1000000000000⟩
  | 15 => ⟨590176093 / 1000000000000, 590176094 / 1000000000000⟩
  | 16 => ⟨520744758 / 1000000000000, 520744759 / 1000000000000⟩
  | 17 => ⟨462884893 / 1000000000000, 462884894 / 1000000000000⟩
  | 18 => ⟨414160528 / 1000000000000, 414160529 / 1000000000000⟩
  | 19 => ⟨372744644 / 1000000000000, 372744645 / 1000000000000⟩
  | 20 => ⟨337245202 / 1000000000000, 337245203 / 1000000000000⟩
  | 21 => ⟨306586520 / 1000000000000, 306586521 / 1000000000000⟩
  | _ => pure 0

private def nineModeSineChunkBox : ℕ → RatInterval
  | 0 => ⟨1395659014573 / 1000000000000, 1395659014659 / 1000000000000⟩
  | 1 => ⟨78623025503 / 1000000000000, 78623025506 / 1000000000000⟩
  | 2 => ⟨26460142830 / 1000000000000, 26460142831 / 1000000000000⟩
  | 3 => ⟨13257118357 / 1000000000000, 13257118359 / 1000000000000⟩
  | 4 => ⟨7960261925 / 1000000000000, 7960261926 / 1000000000000⟩
  | 5 => ⟨5308716849 / 1000000000000, 5308716850 / 1000000000000⟩
  | 6 => ⟨3792663317 / 1000000000000, 3792663318 / 1000000000000⟩
  | 7 => ⟨2844817614 / 1000000000000, 2844817616 / 1000000000000⟩
  | 8 => ⟨2212792635 / 1000000000000, 2212792636 / 1000000000000⟩
  | 9 => ⟨1770316795 / 1000000000000, 1770316796 / 1000000000000⟩
  | 10 => ⟨1448487243 / 1000000000000, 1448487244 / 1000000000000⟩
  | _ => pure 0

private def elevenModeSineChunkBox : ℕ → RatInterval
  | 0 => ⟨1364380738032 / 1000000000000, 1364380738117 / 1000000000000⟩
  | 1 => ⟨95409466735 / 1000000000000, 95409466739 / 1000000000000⟩
  | 2 => ⟨32269293116 / 1000000000000, 32269293118 / 1000000000000⟩
  | 3 => ⟨16185793534 / 1000000000000, 16185793535 / 1000000000000⟩
  | 4 => ⟨9723017615 / 1000000000000, 9723017616 / 1000000000000⟩
  | 5 => ⟨6485692413 / 1000000000000, 6485692414 / 1000000000000⟩
  | 6 => ⟨4634083463 / 1000000000000, 4634083464 / 1000000000000⟩
  | 7 => ⟨3476216529 / 1000000000000, 3476216530 / 1000000000000⟩
  | 8 => ⟨2704051330 / 1000000000000, 2704051331 / 1000000000000⟩
  | 9 => ⟨2163418046 / 1000000000000, 2163418047 / 1000000000000⟩
  | 10 => ⟨1770170928 / 1000000000000, 1770170929 / 1000000000000⟩
  | 11 => ⟨1475203675 / 1000000000000, 1475203676 / 1000000000000⟩
  | 12 => ⟨1248287654 / 1000000000000, 1248287655 / 1000000000000⟩
  | 13 => ⟨1069985719 / 1000000000000, 1069985721 / 1000000000000⟩
  | 14 => ⟨927337526 / 1000000000000, 927337527 / 1000000000000⟩
  | 15 => ⟨811431635 / 1000000000000, 811431636 / 1000000000000⟩
  | 16 => ⟨715976953 / 1000000000000, 715976954 / 1000000000000⟩
  | 17 => ⟨636429527 / 1000000000000, 636429528 / 1000000000000⟩
  | 18 => ⟨569440947 / 1000000000000, 569440948 / 1000000000000⟩
  | 19 => ⟨512499767 / 1000000000000, 512499768 / 1000000000000⟩
  | 20 => ⟨463692411 / 1000000000000, 463692412 / 1000000000000⟩
  | 21 => ⟨421540150 / 1000000000000, 421540151 / 1000000000000⟩
  | 22 => ⟨384885680 / 1000000000000, 384885681 / 1000000000000⟩
  | 23 => ⟨352812775 / 1000000000000, 352812776 / 1000000000000⟩
  | 24 => ⟨324588437 / 1000000000000, 324588438 / 1000000000000⟩
  | 25 => ⟨299620617 / 1000000000000, 299620618 / 1000000000000⟩
  | 26 => ⟨277426895 / 1000000000000, 277426896 / 1000000000000⟩
  | 27 => ⟨257610992 / 1000000000000, 257610993 / 1000000000000⟩
  | 28 => ⟨239844949 / 1000000000000, 239844950 / 1000000000000⟩
  | 29 => ⟨223855463 / 1000000000000, 223855464 / 1000000000000⟩
  | _ => pure 0

private def thirteenModeSineChunkBox : ℕ → RatInterval
  | 0 => ⟨1332608977135 / 1000000000000, 1332608977219 / 1000000000000⟩
  | 1 => ⟨111801809137 / 1000000000000, 111801809142 / 1000000000000⟩
  | 2 => ⟨38036422709 / 1000000000000, 38036422711 / 1000000000000⟩
  | 3 => ⟨19104117475 / 1000000000000, 19104117476 / 1000000000000⟩
  | 4 => ⟨11482070946 / 1000000000000, 11482070948 / 1000000000000⟩
  | 5 => ⟨7661028048 / 1000000000000, 7661028050 / 1000000000000⟩
  | 6 => ⟨5474668573 / 1000000000000, 5474668574 / 1000000000000⟩
  | 7 => ⟨4107146330 / 1000000000000, 4107146332 / 1000000000000⟩
  | 8 => ⟨3195026484 / 1000000000000, 3195026485 / 1000000000000⟩
  | 9 => ⟨2556337941 / 1000000000000, 2556337942 / 1000000000000⟩
  | 10 => ⟨2091733263 / 1000000000000, 2091733264 / 1000000000000⟩
  | 11 => ⟨1743223351 / 1000000000000, 1743223352 / 1000000000000⟩
  | 12 => ⟨1475106485 / 1000000000000, 1475106486 / 1000000000000⟩
  | 13 => ⟨1264423865 / 1000000000000, 1264423866 / 1000000000000⟩
  | 14 => ⟨1095865713 / 1000000000000, 1095865714 / 1000000000000⟩
  | 15 => ⟨958904464 / 1000000000000, 958904465 / 1000000000000⟩
  | 16 => ⟨846107723 / 1000000000000, 846107724 / 1000000000000⟩
  | 17 => ⟨752106966 / 1000000000000, 752106967 / 1000000000000⟩
  | 18 => ⟨672946031 / 1000000000000, 672946032 / 1000000000000⟩
  | 19 => ⟨605657541 / 1000000000000, 605657542 / 1000000000000⟩
  | 20 => ⟨547980476 / 1000000000000, 547980477 / 1000000000000⟩
  | 21 => ⟨498167579 / 1000000000000, 498167580 / 1000000000000⟩
  | 22 => ⟨454851361 / 1000000000000, 454851362 / 1000000000000⟩
  | 23 => ⟨416949181 / 1000000000000, 416949182 / 1000000000000⟩
  | 24 => ⟨383594892 / 1000000000000, 383594893 / 1000000000000⟩
  | 25 => ⟨354088892 / 1000000000000, 354088893 / 1000000000000⟩
  | _ => pure 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem sixModeSineChunk_kernel_certificate
    {i : ℕ} (hi : i < 11) :
    IsSubinterval (scheduledSineCauchyChunkInterval 6 i)
      (sixModeSineChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem checkpointedSineSeries_sub_evenTarget_six :
    IsSubinterval
      (coarseAcceleratedSineSeriesInterval 6 11 sixModeSineChunkBox)
      (yoshidaEvenSineTargets 6) := by
  decide +kernel

theorem yoshidaEvenSineTarget_six_contains :
    (yoshidaEvenSineTargets 6).Contains (yoshidaSineMoment 6) := by
  exact contains_of_subinterval checkpointedSineSeries_sub_evenTarget_six
    (coarseAcceleratedSineSeriesInterval_contains
      (by norm_num) (by norm_num) sixModeSineChunkBox
      (fun _ hi ↦ sixModeSineChunk_kernel_certificate hi))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem sevenModeSineChunk_kernel_certificate
    {i : ℕ} (hi : i < 11) :
    IsSubinterval (scheduledSineCauchyChunkInterval 7 i)
      (sevenModeSineChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem checkpointedSineSeries_sub_evenTarget_seven :
    IsSubinterval
      (coarseAcceleratedSineSeriesInterval 7 11 sevenModeSineChunkBox)
      (yoshidaEvenSineTargets 7) := by
  decide +kernel

theorem yoshidaEvenSineTarget_seven_contains :
    (yoshidaEvenSineTargets 7).Contains (yoshidaSineMoment 7) := by
  exact contains_of_subinterval checkpointedSineSeries_sub_evenTarget_seven
    (coarseAcceleratedSineSeriesInterval_contains
      (by norm_num) (by norm_num) sevenModeSineChunkBox
      (fun _ hi ↦ sevenModeSineChunk_kernel_certificate hi))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem eightModeSineChunk_kernel_certificate
    {i : ℕ} (hi : i < 22) :
    IsSubinterval (scheduledSineCauchyChunkInterval 8 i)
      (eightModeSineChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem checkpointedSineSeries_sub_evenTarget_eight :
    IsSubinterval
      (coarseAcceleratedSineSeriesInterval 8 22 eightModeSineChunkBox)
      (yoshidaEvenSineTargets 8) := by
  decide +kernel

theorem yoshidaEvenSineTarget_eight_contains :
    (yoshidaEvenSineTargets 8).Contains (yoshidaSineMoment 8) := by
  exact contains_of_subinterval checkpointedSineSeries_sub_evenTarget_eight
    (coarseAcceleratedSineSeriesInterval_contains
      (by norm_num) (by norm_num) eightModeSineChunkBox
      (fun _ hi ↦ eightModeSineChunk_kernel_certificate hi))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem nineModeSineChunk_kernel_certificate
    {i : ℕ} (hi : i < 11) :
    IsSubinterval (scheduledSineCauchyChunkInterval 9 i)
      (nineModeSineChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem checkpointedSineSeries_sub_evenTarget_nine :
    IsSubinterval
      (coarseAcceleratedSineSeriesInterval 9 11 nineModeSineChunkBox)
      (yoshidaEvenSineTargets 9) := by
  decide +kernel

theorem yoshidaEvenSineTarget_nine_contains :
    (yoshidaEvenSineTargets 9).Contains (yoshidaSineMoment 9) := by
  exact contains_of_subinterval checkpointedSineSeries_sub_evenTarget_nine
    (coarseAcceleratedSineSeriesInterval_contains
      (by norm_num) (by norm_num) nineModeSineChunkBox
      (fun _ hi ↦ nineModeSineChunk_kernel_certificate hi))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem elevenModeSineChunk_kernel_certificate
    {i : ℕ} (hi : i < 30) :
    IsSubinterval (scheduledSineCauchyChunkInterval 11 i)
      (elevenModeSineChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem checkpointedSineSeries_sub_evenTarget_eleven :
    IsSubinterval
      (coarseAcceleratedSineSeriesInterval 11 30 elevenModeSineChunkBox)
      (yoshidaEvenSineTargets 11) := by
  decide +kernel

theorem yoshidaEvenSineTarget_eleven_contains :
    (yoshidaEvenSineTargets 11).Contains (yoshidaSineMoment 11) := by
  exact contains_of_subinterval checkpointedSineSeries_sub_evenTarget_eleven
    (coarseAcceleratedSineSeriesInterval_contains
      (by norm_num) (by norm_num) elevenModeSineChunkBox
      (fun _ hi ↦ elevenModeSineChunk_kernel_certificate hi))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem thirteenModeSineChunk_kernel_certificate
    {i : ℕ} (hi : i < 26) :
    IsSubinterval (scheduledSineCauchyChunkInterval 13 i)
      (thirteenModeSineChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem checkpointedSineSeries_sub_evenTarget_thirteen :
    IsSubinterval
      (coarseAcceleratedSineSeriesInterval 13 26 thirteenModeSineChunkBox)
      (yoshidaEvenSineTargets 13) := by
  decide +kernel

theorem yoshidaEvenSineTarget_thirteen_contains :
    (yoshidaEvenSineTargets 13).Contains (yoshidaSineMoment 13) := by
  exact contains_of_subinterval checkpointedSineSeries_sub_evenTarget_thirteen
    (coarseAcceleratedSineSeriesInterval_contains
      (by norm_num) (by norm_num) thirteenModeSineChunkBox
      (fun _ hi ↦ thirteenModeSineChunk_kernel_certificate hi))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem highSineSeriesInterval_ten_sub_evenTarget
    {n : ℕ} (hn : 18 ≤ n) (hn199 : n ≤ 199) :
    IsSubinterval (highSineSeriesInterval n 10)
      (yoshidaEvenSineTargets n) := by
  interval_cases n <;> decide +kernel

/-- Every canonical high-mode target from `S₁₈` through `S₁₉₉` contains
the actual analytic sine moment. -/
theorem yoshidaEvenHighSineTargets_contains
    (n : ℕ) (hn : 18 ≤ n) (hn199 : n ≤ 199) :
    (yoshidaEvenSineTargets n).Contains (yoshidaSineMoment n) := by
  exact contains_of_subinterval
    (highSineSeriesInterval_ten_sub_evenTarget hn hn199)
    (highSineSeriesInterval_contains (by omega) 10)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem highSineSeriesInterval_ten_sub_evenTarget_ten :
    IsSubinterval (highSineSeriesInterval 10 10)
      (yoshidaEvenSineTargets 10) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem highSineSeriesInterval_ten_sub_evenTarget_twelve :
    IsSubinterval (highSineSeriesInterval 12 10)
      (yoshidaEvenSineTargets 12) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem highSineSeriesInterval_ten_sub_evenTarget_fourteen :
    IsSubinterval (highSineSeriesInterval 14 10)
      (yoshidaEvenSineTargets 14) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem highSineSeriesInterval_ten_sub_evenTarget_fifteen :
    IsSubinterval (highSineSeriesInterval 15 10)
      (yoshidaEvenSineTargets 15) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem highSineSeriesInterval_ten_sub_evenTarget_sixteen :
    IsSubinterval (highSineSeriesInterval 16 10)
      (yoshidaEvenSineTargets 16) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem highSineSeriesInterval_ten_sub_evenTarget_seventeen :
    IsSubinterval (highSineSeriesInterval 17 10)
      (yoshidaEvenSineTargets 17) := by
  decide +kernel

private theorem yoshidaEvenSineTarget_ten_contains :
    (yoshidaEvenSineTargets 10).Contains (yoshidaSineMoment 10) := by
  exact contains_of_subinterval
    highSineSeriesInterval_ten_sub_evenTarget_ten
    (highSineSeriesInterval_contains (by norm_num) 10)

private theorem yoshidaEvenSineTarget_twelve_contains :
    (yoshidaEvenSineTargets 12).Contains (yoshidaSineMoment 12) := by
  exact contains_of_subinterval
    highSineSeriesInterval_ten_sub_evenTarget_twelve
    (highSineSeriesInterval_contains (by norm_num) 10)

private theorem yoshidaEvenSineTarget_fourteen_contains :
    (yoshidaEvenSineTargets 14).Contains (yoshidaSineMoment 14) := by
  exact contains_of_subinterval
    highSineSeriesInterval_ten_sub_evenTarget_fourteen
    (highSineSeriesInterval_contains (by norm_num) 10)

private theorem yoshidaEvenSineTarget_fifteen_contains :
    (yoshidaEvenSineTargets 15).Contains (yoshidaSineMoment 15) := by
  exact contains_of_subinterval
    highSineSeriesInterval_ten_sub_evenTarget_fifteen
    (highSineSeriesInterval_contains (by norm_num) 10)

private theorem yoshidaEvenSineTarget_sixteen_contains :
    (yoshidaEvenSineTargets 16).Contains (yoshidaSineMoment 16) := by
  exact contains_of_subinterval
    highSineSeriesInterval_ten_sub_evenTarget_sixteen
    (highSineSeriesInterval_contains (by norm_num) 10)

private theorem yoshidaEvenSineTarget_seventeen_contains :
    (yoshidaEvenSineTargets 17).Contains (yoshidaSineMoment 17) := by
  exact contains_of_subinterval
    highSineSeriesInterval_ten_sub_evenTarget_seventeen
    (highSineSeriesInterval_contains (by norm_num) 10)

/-- Complete analytic enclosure package for all canonical even sine targets
`S₁, …, S₁₉₉`. -/
theorem yoshidaEvenSineTargetEnclosures :
    YoshidaEvenSineTargetEnclosures := by
  intro n hn hn199
  by_cases hnHigh : 18 ≤ n
  · exact yoshidaEvenHighSineTargets_contains n hnHigh hn199
  have hn17 : n ≤ 17 := by omega
  interval_cases n
  · exact YoshidaEvenSineMomentOneEnclosure.yoshidaEvenSineTarget_one_contains
  · exact YoshidaEvenSineMomentTwoEnclosure.yoshidaEvenSineTarget_two_contains
  · exact YoshidaEvenSineMomentThreeEnclosure.yoshidaEvenSineTarget_three_contains
  · exact YoshidaEvenSineMomentFourEnclosure.yoshidaEvenSineTarget_four_contains
  · exact YoshidaEvenSineMomentFiveEnclosure.yoshidaEvenSineTarget_five_contains
  · exact yoshidaEvenSineTarget_six_contains
  · exact yoshidaEvenSineTarget_seven_contains
  · exact yoshidaEvenSineTarget_eight_contains
  · exact yoshidaEvenSineTarget_nine_contains
  · exact yoshidaEvenSineTarget_ten_contains
  · exact yoshidaEvenSineTarget_eleven_contains
  · exact yoshidaEvenSineTarget_twelve_contains
  · exact yoshidaEvenSineTarget_thirteen_contains
  · exact yoshidaEvenSineTarget_fourteen_contains
  · exact yoshidaEvenSineTarget_fifteen_contains
  · exact yoshidaEvenSineTarget_sixteen_contains
  · exact yoshidaEvenSineTarget_seventeen_contains

end ArithmeticHodge.Analysis.YoshidaEvenSineHighEnclosures
