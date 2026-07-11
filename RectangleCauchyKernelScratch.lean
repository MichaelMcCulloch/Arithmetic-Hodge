import ArithmeticHodge.Analysis.Contour.CauchyGoursat
import ArithmeticHodge.Analysis.Contour.RectangleWinding
import Mathlib.Analysis.Complex.RemovableSingularity

open Complex MeasureTheory Set
open scoped Interval Real

namespace ArithmeticHodge.Analysis.Contour

private lemma rectIntegral_congr_on_sides
    {f g : ℂ → ℂ} {z w : ℂ}
    (hbottom : ∀ x ∈ uIcc z.re w.re,
      f ((x : ℂ) + (z.im : ℂ) * I) = g ((x : ℂ) + (z.im : ℂ) * I))
    (htop : ∀ x ∈ uIcc z.re w.re,
      f ((x : ℂ) + (w.im : ℂ) * I) = g ((x : ℂ) + (w.im : ℂ) * I))
    (hright : ∀ y ∈ uIcc z.im w.im,
      f ((w.re : ℂ) + (y : ℂ) * I) = g ((w.re : ℂ) + (y : ℂ) * I))
    (hleft : ∀ y ∈ uIcc z.im w.im,
      f ((z.re : ℂ) + (y : ℂ) * I) = g ((z.re : ℂ) + (y : ℂ) * I)) :
    rectIntegral f z w = rectIntegral g z w := by
  simp only [rectIntegral]
  rw [intervalIntegral.integral_congr hbottom,
    intervalIntegral.integral_congr htop,
    intervalIntegral.integral_congr hright,
    intervalIntegral.integral_congr hleft]

private lemma rectIntegral_add_of_intervalIntegrable
    {f g : ℂ → ℂ} {z w : ℂ}
    (hfb : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re)
    (hgb : IntervalIntegrable
      (fun x : ℝ => g ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re)
    (hft : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re)
    (hgt : IntervalIntegrable
      (fun x : ℝ => g ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re)
    (hfr : IntervalIntegrable
      (fun y : ℝ => f ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hgr : IntervalIntegrable
      (fun y : ℝ => g ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hfl : IntervalIntegrable
      (fun y : ℝ => f ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hgl : IntervalIntegrable
      (fun y : ℝ => g ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im) :
    rectIntegral (fun s => f s + g s) z w =
      rectIntegral f z w + rectIntegral g z w := by
  simp only [rectIntegral]
  rw [intervalIntegral.integral_add hfb hgb,
    intervalIntegral.integral_add hft hgt,
    intervalIntegral.integral_add hfr hgr,
    intervalIntegral.integral_add hfl hgl]
  simp only [smul_eq_mul]
  ring

private lemma rectIntegral_smul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectIntegral (fun s => c • f s) z w = c • rectIntegral f z w := by
  simp only [rectIntegral, intervalIntegral.integral_smul, smul_sub, smul_add, smul_smul]
  rw [mul_comm I c]

private lemma horizontal_pole_intervalIntegrable
    {a b c : ℝ} {rho C : ℂ} (hc : c ≠ rho.im) :
    IntervalIntegrable
      (fun x : ℝ => C * (((x : ℂ) + (c : ℂ) * I - rho)⁻¹))
      volume a b := by
  apply Continuous.intervalIntegrable
  refine continuous_const.mul ((by fun_prop : Continuous
    (fun x : ℝ => (x : ℂ) + (c : ℂ) * I - rho)).inv₀ ?_)
  intro x hzero
  have him : (((x : ℂ) + (c : ℂ) * I - rho)).im = 0 := by
    rw [hzero]
    rfl
  exact hc (sub_eq_zero.mp (by simpa using him))

private lemma vertical_pole_intervalIntegrable
    {a b r : ℝ} {rho C : ℂ} (hr : r ≠ rho.re) :
    IntervalIntegrable
      (fun y : ℝ => C * (((r : ℂ) + (y : ℂ) * I - rho)⁻¹))
      volume a b := by
  apply Continuous.intervalIntegrable
  refine continuous_const.mul ((by fun_prop : Continuous
    (fun y : ℝ => (r : ℂ) + (y : ℂ) * I - rho)).inv₀ ?_)
  intro y hzero
  have hre : (((r : ℂ) + (y : ℂ) * I - rho)).re = 0 := by
    rw [hzero]
    rfl
  exact hr (sub_eq_zero.mp (by simpa using hre))

theorem rectIntegral_cauchy_kernel_scratch
    {H : ℂ → ℂ} {z w rho : ℂ}
    (hH : ∀ s ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]), DifferentiableAt ℂ H s)
    (hre₀ : z.re < rho.re) (hre₁ : rho.re < w.re)
    (him₀ : z.im < rho.im) (him₁ : rho.im < w.im) :
    rectIntegral (fun s => H s * (s - rho)⁻¹) z w =
      2 * (Real.pi : ℂ) * I * H rho := by
  let R : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]
  let q : ℂ → ℂ := dslope H rho
  let p : ℂ → ℂ := fun s => H rho * (s - rho)⁻¹
  have hrew : z.re < w.re := hre₀.trans hre₁
  have himw : z.im < w.im := him₀.trans him₁
  have hR_nhds : R ∈ nhds rho := by
    rw [← mem_interior_iff_mem_nhds]
    simp [R, interior_reProdIm, uIcc_of_le hrew.le, uIcc_of_le himw.le,
      mem_reProdIm, hre₀, hre₁, him₀, him₁]
  have hH_on : DifferentiableOn ℂ H R := by
    intro s hs
    exact (hH s hs).differentiableWithinAt
  have hq_diff : DifferentiableOn ℂ q R := by
    exact (differentiableOn_dslope hR_nhds).mpr hH_on
  have hq_zero : rectIntegral q z w = 0 :=
    rectIntegral_eq_zero_of_differentiableOn hq_diff
  have hq_cont : ContinuousOn q R := hq_diff.continuousOn
  have hq_bottom : IntervalIntegrable
      (fun x : ℝ => q ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re := by
    refine (hq_cont.comp (by fun_prop) ?_).intervalIntegrable
    intro x hx
    change (x : ℂ) + (z.im : ℂ) * I ∈
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
    rw [mem_reProdIm]
    exact ⟨by simpa using hx, by
      have hzmem : z.im ∈ [[z.im, w.im]] := by
        rw [uIcc_of_le himw.le]
        exact ⟨le_rfl, himw.le⟩
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
        one_mul, mul_one, zero_add, add_zero] using hzmem⟩
  have hq_top : IntervalIntegrable
      (fun x : ℝ => q ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re := by
    refine (hq_cont.comp (by fun_prop) ?_).intervalIntegrable
    intro x hx
    change (x : ℂ) + (w.im : ℂ) * I ∈
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
    rw [mem_reProdIm]
    exact ⟨by simpa using hx, by
      have hwmem : w.im ∈ [[z.im, w.im]] := by
        rw [uIcc_of_le himw.le]
        exact ⟨himw.le, le_rfl⟩
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
        one_mul, mul_one, zero_add, add_zero] using hwmem⟩
  have hq_right : IntervalIntegrable
      (fun y : ℝ => q ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im := by
    refine (hq_cont.comp (by fun_prop) ?_).intervalIntegrable
    intro y hy
    change (w.re : ℂ) + (y : ℂ) * I ∈
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
    rw [mem_reProdIm]
    exact ⟨by
      have hwmem : w.re ∈ [[z.re, w.re]] := by
        rw [uIcc_of_le hrew.le]
        exact ⟨hrew.le, le_rfl⟩
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
        one_mul, mul_one, zero_add, add_zero, sub_zero] using hwmem,
      by simpa using hy⟩
  have hq_left : IntervalIntegrable
      (fun y : ℝ => q ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im := by
    refine (hq_cont.comp (by fun_prop) ?_).intervalIntegrable
    intro y hy
    change (z.re : ℂ) + (y : ℂ) * I ∈
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
    rw [mem_reProdIm]
    exact ⟨by
      have hzmem : z.re ∈ [[z.re, w.re]] := by
        rw [uIcc_of_le hrew.le]
        exact ⟨le_rfl, hrew.le⟩
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
        one_mul, mul_one, zero_add, add_zero, sub_zero] using hzmem,
      by simpa using hy⟩
  have hp_bottom : IntervalIntegrable
      (fun x : ℝ => p ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re := by
    simpa [p] using horizontal_pole_intervalIntegrable
      (a := z.re) (b := w.re) (c := z.im) (rho := rho) (C := H rho) him₀.ne
  have hp_top : IntervalIntegrable
      (fun x : ℝ => p ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re := by
    simpa [p] using horizontal_pole_intervalIntegrable
      (a := z.re) (b := w.re) (c := w.im) (rho := rho) (C := H rho) him₁.ne'
  have hp_right : IntervalIntegrable
      (fun y : ℝ => p ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im := by
    simpa [p] using vertical_pole_intervalIntegrable
      (a := z.im) (b := w.im) (r := w.re) (rho := rho) (C := H rho) hre₁.ne'
  have hp_left : IntervalIntegrable
      (fun y : ℝ => p ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im := by
    simpa [p] using vertical_pole_intervalIntegrable
      (a := z.im) (b := w.im) (r := z.re) (rho := rho) (C := H rho) hre₀.ne
  have hdecomp : ∀ {s : ℂ}, s ≠ rho →
      H s * (s - rho)⁻¹ = q s + p s := by
    intro s hs
    change H s * (s - rho)⁻¹ =
      dslope H rho s + H rho * (s - rho)⁻¹
    rw [dslope_of_ne H hs, slope_def_field]
    simp only [div_eq_mul_inv]
    ring
  have hboundary :
      rectIntegral (fun s => H s * (s - rho)⁻¹) z w =
        rectIntegral (fun s => q s + p s) z w := by
    apply rectIntegral_congr_on_sides
    · intro x hx
      apply hdecomp
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    · intro x hx
      apply hdecomp
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    · intro y hy
      apply hdecomp
      intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith
    · intro y hy
      apply hdecomp
      intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith
  have hadd : rectIntegral (fun s => q s + p s) z w =
      rectIntegral q z w + rectIntegral p z w :=
    rectIntegral_add_of_intervalIntegrable
      hq_bottom hp_bottom hq_top hp_top hq_right hp_right hq_left hp_left
  have hp_eq : rectIntegral p z w =
      H rho * (2 * (Real.pi : ℂ) * I) := by
    calc
      rectIntegral p z w =
          H rho * rectIntegral (fun s => (s - rho)⁻¹) z w := by
        simpa only [p, smul_eq_mul] using
          rectIntegral_smul (H rho) (fun s => (s - rho)⁻¹) z w
      _ = H rho * (2 * (Real.pi : ℂ) * I) := by
        rw [rectIntegral_sub_inv_of_mem_rectangle hre₀ hre₁ him₀ him₁]
  rw [hboundary, hadd, hq_zero, zero_add, hp_eq]
  ring

end ArithmeticHodge.Analysis.Contour

#print axioms ArithmeticHodge.Analysis.Contour.rectIntegral_cauchy_kernel_scratch
