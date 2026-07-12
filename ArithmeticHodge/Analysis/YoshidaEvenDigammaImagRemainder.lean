import ArithmeticHodge.Analysis.ComplexStirling
import ArithmeticHodge.Analysis.TrapezoidalErrorBounds
import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaEvenCouplingReduction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

set_option autoImplicit false

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped BigOperators ComplexConjugate Topology

namespace ArithmeticHodge.Analysis.YoshidaEvenDigammaImagRemainder

open ArithmeticHodge.Analysis
open TrapezoidalErrorBounds
open YoshidaConstantBounds
open YoshidaEvenCouplingReduction
open YoshidaWeightedTailBounds

/-!
# Imaginary digamma samples for the even coupling estimate

The source-facing imaginary samples are reduced to an exact positive Cauchy
series.  This is the concrete analytic object behind the remaining sharp
remainder in Yoshida's equation (5.11).
-/

def evenDigammaY (n : ℕ) : ℝ :=
  Real.pi * (n : ℝ) / (2 * yoshidaA)

def evenDigammaCauchyTerm (n k : ℕ) : ℝ :=
  evenDigammaY n /
    (((k : ℝ) + 1 / 4) ^ 2 + evenDigammaY n ^ 2)

private theorem inv_ofReal_add_mul_I_im (x y : ℝ) :
    (((x : ℂ) + (y : ℂ) * Complex.I)⁻¹).im =
      -y / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_im]
  simp [Complex.normSq_apply]
  ring

private theorem digammaPartialFractionTerm_im
    (n k : ℕ) :
    let s : ℂ := (1 / 4 : ℝ) + (evenDigammaY n : ℂ) * Complex.I
    ((1 : ℂ) / (s + (↑(k + 1 : ℕ) : ℂ)) -
      1 / (↑(k + 1 : ℕ) : ℂ)).im =
        -evenDigammaCauchyTerm n (k + 1) := by
  dsimp only
  rw [sub_im]
  have hreal : ((1 / (↑(k + 1 : ℕ) : ℂ)) : ℂ).im = 0 := by
    simp
  rw [hreal, sub_zero]
  rw [one_div]
  have hden :
      ((1 / 4 : ℝ) : ℂ) + (evenDigammaY n : ℂ) * Complex.I +
          (↑(k + 1 : ℕ) : ℂ) =
        ((((k + 1 : ℕ) : ℝ) + 1 / 4 : ℝ) : ℂ) +
          (evenDigammaY n : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hden]
  rw [inv_ofReal_add_mul_I_im]
  unfold evenDigammaCauchyTerm
  push_cast
  ring

theorem summable_evenDigammaCauchyTerm (n : ℕ) :
    Summable (evenDigammaCauchyTerm n) := by
  let s : ℂ := (1 / 4 : ℝ) + (evenDigammaY n : ℂ) * Complex.I
  have hsre : 0 ≤ s.re := by
    dsimp only [s]
    norm_num
  have hcomplex := summable_digamma_partialFraction_of_nonneg_re s hsre
  have him : Summable (fun k : ℕ ↦
      ((1 : ℂ) / (s + (↑(k + 1 : ℕ) : ℂ)) -
        1 / (↑(k + 1 : ℕ) : ℂ)).im) :=
    (Complex.hasSum_im hcomplex.hasSum).summable
  have hshift : Summable (fun k : ℕ ↦
      evenDigammaCauchyTerm n (k + 1)) := by
    apply him.neg.congr
    intro k
    rw [digammaPartialFractionTerm_im n k]
    simp
  exact (summable_nat_add_iff 1).mp hshift

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

private theorem cauchyProfile_sharp_remainder
    {y : ℝ} (hy : 4 < y)
    (hs : Summable (fun k : ℕ ↦ cauchyProfile y k)) :
    |(∑' k : ℕ, cauchyProfile y k) -
        (Real.pi / 2 + 1 / (4 * y))| ≤
      1 / (12 * y ^ 2) := by
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
    _ ≤ 1 / (12 * y ^ 2) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 96 * y ^ 3)
        (by positivity : 0 < 12 * y ^ 2)]
      nlinarith [sq_pos_of_pos hy0]

/-- Exact positive Cauchy-series formula for every actual imaginary digamma
sample, including the real-axis value at `n = 0`. -/
theorem yoshidaEvenDigammaImag_eq_tsum (n : ℕ) :
    yoshidaEvenDigammaImag n =
      ∑' k : ℕ, evenDigammaCauchyTerm n k := by
  let s : ℂ := (1 / 4 : ℝ) + (evenDigammaY n : ℂ) * Complex.I
  have hspos : 0 < s.re := by
    dsimp only [s]
    norm_num
  have hcomplex := summable_digamma_partialFraction_of_nonneg_re s hspos.le
  have him := Complex.im_tsum hcomplex
  have hsplit := (summable_evenDigammaCauchyTerm n).sum_add_tsum_nat_add 1
  unfold yoshidaEvenDigammaImag
  have hs_eq :
      ((1 / 4 : ℝ) : ℂ) +
          (Real.pi : ℂ) * ((n : ℝ) : ℂ) /
              (2 * (yoshidaA : ℂ)) * Complex.I = s := by
    dsimp [s, evenDigammaY]
    push_cast
    ring
  rw [hs_eq]
  rw [digamma_eq_tsum_of_pos_re s hspos]
  change
    (-(1 / s + Real.eulerMascheroniConstant +
      ∑' k : ℕ,
        ((1 : ℂ) / (s + (↑(k + 1 : ℕ) : ℂ)) -
          1 / (↑(k + 1 : ℕ) : ℂ)))).im = _
  rw [neg_im, add_im, add_im, him]
  have hgamma : (Real.eulerMascheroniConstant : ℂ).im = 0 := by simp
  rw [hgamma, add_zero]
  have hhead : (1 / s).im = -evenDigammaCauchyTerm n 0 := by
    rw [one_div]
    change s⁻¹.im = _
    dsimp only [s]
    rw [inv_ofReal_add_mul_I_im]
    unfold evenDigammaCauchyTerm
    norm_num
    ring
  rw [hhead]
  have htail :
      (∑' k : ℕ,
        ((1 : ℂ) / (s + (↑(k + 1 : ℕ) : ℂ)) -
          1 / (↑(k + 1 : ℕ) : ℂ)).im) =
        ∑' k : ℕ, -evenDigammaCauchyTerm n (k + 1) := by
    apply tsum_congr
    intro k
    exact digammaPartialFractionTerm_im n k
  rw [htail, tsum_neg]
  norm_num [Finset.sum_range_succ] at hsplit
  linarith

theorem yoshidaEvenDigammaImag_zero : yoshidaEvenDigammaImag 0 = 0 := by
  rw [yoshidaEvenDigammaImag_eq_tsum]
  simp [evenDigammaCauchyTerm, evenDigammaY]

/-- Yoshida's sharp imaginary-digamma estimate (5.11), including the
exceptional first positive mode with its unweakened `1/12` constant. -/
theorem sharpDigammaImagRemainder5_11 : SharpDigammaImagRemainder5_11 := by
  refine ⟨yoshidaEvenDigammaImag_zero, ?_⟩
  intro n hn
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
  have hsharp := cauchyProfile_sharp_remainder hy4 hs
  have hmain :
      digammaAsymptoticMain yoshidaA n =
        Real.pi / 2 + 1 / (4 * y) := by
    dsimp only [digammaAsymptoticMain, y, evenDigammaY]
    field_simp [hn0, YoshidaCoercivityNumerics.yoshidaA_pos.ne', Real.pi_ne_zero]
    ring
  have hrhs :
      (2 * yoshidaA) ^ 2 /
          (12 * Real.pi ^ 2 * (n : ℝ) ^ 2) =
        1 / (12 * y ^ 2) := by
    dsimp only [y, evenDigammaY]
    field_simp [hn0, YoshidaCoercivityNumerics.yoshidaA_pos.ne', Real.pi_ne_zero]
  rw [yoshidaEvenDigammaImag_eq_tsum, hfun, hmain, hrhs]
  exact hsharp

end ArithmeticHodge.Analysis.YoshidaEvenDigammaImagRemainder
