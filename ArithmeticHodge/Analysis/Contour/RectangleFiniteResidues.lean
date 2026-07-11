import ArithmeticHodge.Analysis.Contour.RectangleCauchy
import ArithmeticHodge.Analysis.Contour.RectangleWinding

open Complex MeasureTheory Set
open scoped Interval Real

namespace ArithmeticHodge.Analysis.Contour

private lemma rectIntegral_finset_sum_of_intervalIntegrable
    {ι : Type*} {T : Finset ι} {f : ι → ℂ → ℂ} {z w : ℂ}
    (hbottom : ∀ i ∈ T, IntervalIntegrable
      (fun x : ℝ => f i ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re)
    (htop : ∀ i ∈ T, IntervalIntegrable
      (fun x : ℝ => f i ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re)
    (hright : ∀ i ∈ T, IntervalIntegrable
      (fun y : ℝ => f i ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hleft : ∀ i ∈ T, IntervalIntegrable
      (fun y : ℝ => f i ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im) :
    rectIntegral (fun s => ∑ i ∈ T, f i s) z w =
      ∑ i ∈ T, rectIntegral (f i) z w := by
  simp only [rectIntegral,
    intervalIntegral.integral_finset_sum hbottom,
    intervalIntegral.integral_finset_sum htop,
    intervalIntegral.integral_finset_sum hright,
    intervalIntegral.integral_finset_sum hleft,
    Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

private lemma rectIntegral_smul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectIntegral (fun s => c • f s) z w = c • rectIntegral f z w := by
  simp only [rectIntegral, intervalIntegral.integral_smul, smul_sub, smul_add, smul_smul]
  rw [mul_comm I c]

private lemma horizontal_weighted_cauchy_intervalIntegrable
    {H : ℂ → ℂ} {a b c : ℝ} {rho A : ℂ}
    (hH : ContinuousOn
      (fun x : ℝ => H ((x : ℂ) + (c : ℂ) * I)) (uIcc a b))
    (hc : c ≠ rho.im) :
    IntervalIntegrable
      (fun x : ℝ =>
        A * H ((x : ℂ) + (c : ℂ) * I) *
          (((x : ℂ) + (c : ℂ) * I - rho)⁻¹)) volume a b := by
  refine ((continuousOn_const.mul hH).mul (ContinuousOn.inv₀ (by fun_prop) ?_)).intervalIntegrable
  intro x hx hzero
  have him : (((x : ℂ) + (c : ℂ) * I - rho)).im = 0 := by
    rw [hzero]
    rfl
  exact hc (sub_eq_zero.mp (by simpa using him))

private lemma vertical_weighted_cauchy_intervalIntegrable
    {H : ℂ → ℂ} {a b r : ℝ} {rho A : ℂ}
    (hH : ContinuousOn
      (fun y : ℝ => H ((r : ℂ) + (y : ℂ) * I)) (uIcc a b))
    (hr : r ≠ rho.re) :
    IntervalIntegrable
      (fun y : ℝ =>
        A * H ((r : ℂ) + (y : ℂ) * I) *
          (((r : ℂ) + (y : ℂ) * I - rho)⁻¹)) volume a b := by
  refine ((continuousOn_const.mul hH).mul (ContinuousOn.inv₀ (by fun_prop) ?_)).intervalIntegrable
  intro y hy hzero
  have hre : (((r : ℂ) + (y : ℂ) * I - rho)).re = 0 := by
    rw [hzero]
    rfl
  exact hr (sub_eq_zero.mp (by simpa using hre))

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

private lemma rectangle_boundary_continuousOn
    {F : ℂ → ℂ} {z w : ℂ}
    (hrew : z.re < w.re) (himw : z.im < w.im)
    (hF : ContinuousOn F ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    ContinuousOn
        (fun x : ℝ => F ((x : ℂ) + (z.im : ℂ) * I)) (uIcc z.re w.re) ∧
      ContinuousOn
        (fun x : ℝ => F ((x : ℂ) + (w.im : ℂ) * I)) (uIcc z.re w.re) ∧
      ContinuousOn
        (fun y : ℝ => F ((w.re : ℂ) + (y : ℂ) * I)) (uIcc z.im w.im) ∧
      ContinuousOn
        (fun y : ℝ => F ((z.re : ℂ) + (y : ℂ) * I)) (uIcc z.im w.im) := by
  have hbottom : ContinuousOn
      (fun x : ℝ => F ((x : ℂ) + (z.im : ℂ) * I)) (uIcc z.re w.re) := by
    refine hF.comp (by fun_prop) ?_
    intro x hx
    rw [mem_reProdIm]
    exact ⟨by simpa using hx, by
      have hzmem : z.im ∈ [[z.im, w.im]] := by
        rw [uIcc_of_le himw.le]
        exact ⟨le_rfl, himw.le⟩
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
        one_mul, mul_one, zero_add, add_zero] using hzmem⟩
  have htop : ContinuousOn
      (fun x : ℝ => F ((x : ℂ) + (w.im : ℂ) * I)) (uIcc z.re w.re) := by
    refine hF.comp (by fun_prop) ?_
    intro x hx
    rw [mem_reProdIm]
    exact ⟨by simpa using hx, by
      have hwmem : w.im ∈ [[z.im, w.im]] := by
        rw [uIcc_of_le himw.le]
        exact ⟨himw.le, le_rfl⟩
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
        one_mul, mul_one, zero_add, add_zero] using hwmem⟩
  have hright : ContinuousOn
      (fun y : ℝ => F ((w.re : ℂ) + (y : ℂ) * I)) (uIcc z.im w.im) := by
    refine hF.comp (by fun_prop) ?_
    intro y hy
    rw [mem_reProdIm]
    exact ⟨by
      have hwmem : w.re ∈ [[z.re, w.re]] := by
        rw [uIcc_of_le hrew.le]
        exact ⟨hrew.le, le_rfl⟩
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
        one_mul, mul_one, zero_add, add_zero, sub_zero] using hwmem,
      by simpa using hy⟩
  have hleft : ContinuousOn
      (fun y : ℝ => F ((z.re : ℂ) + (y : ℂ) * I)) (uIcc z.im w.im) := by
    refine hF.comp (by fun_prop) ?_
    intro y hy
    rw [mem_reProdIm]
    exact ⟨by
      have hzmem : z.re ∈ [[z.re, w.re]] := by
        rw [uIcc_of_le hrew.le]
        exact ⟨le_rfl, hrew.le⟩
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
        one_mul, mul_one, zero_add, add_zero, sub_zero] using hzmem,
      by simpa using hy⟩
  exact ⟨hbottom, htop, hright, hleft⟩

/-- The rectangular contour integral of a finite sum of simple Cauchy kernels
is `2 * π * I` times the corresponding weighted sum of interior residues. -/
theorem rectIntegral_finite_simple_residues
    {H : ℂ → ℂ} {a : ℂ → ℂ} {S : Finset ℂ} {z w : ℂ}
    (hrew : z.re < w.re) (himw : z.im < w.im)
    (hH : ∀ s ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]), DifferentiableAt ℂ H s)
    (hS : ∀ rho ∈ S,
      z.re < rho.re ∧ rho.re < w.re ∧ z.im < rho.im ∧ rho.im < w.im) :
    rectIntegral
        (fun s => ∑ rho ∈ S, a rho * H s * (s - rho)⁻¹) z w =
      2 * (Real.pi : ℂ) * I * ∑ rho ∈ S, a rho * H rho := by
  let R : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]
  have hH_cont : ContinuousOn H R := by
    intro s hs
    exact (hH s hs).continuousAt.continuousWithinAt
  have hH_bottom : ContinuousOn
      (fun x : ℝ => H ((x : ℂ) + (z.im : ℂ) * I)) (uIcc z.re w.re) := by
    refine hH_cont.comp (by fun_prop) ?_
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
  have hH_top : ContinuousOn
      (fun x : ℝ => H ((x : ℂ) + (w.im : ℂ) * I)) (uIcc z.re w.re) := by
    refine hH_cont.comp (by fun_prop) ?_
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
  have hH_right : ContinuousOn
      (fun y : ℝ => H ((w.re : ℂ) + (y : ℂ) * I)) (uIcc z.im w.im) := by
    refine hH_cont.comp (by fun_prop) ?_
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
  have hH_left : ContinuousOn
      (fun y : ℝ => H ((z.re : ℂ) + (y : ℂ) * I)) (uIcc z.im w.im) := by
    refine hH_cont.comp (by fun_prop) ?_
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
  have hbottom : ∀ rho ∈ S, IntervalIntegrable
      (fun x : ℝ =>
        a rho * H ((x : ℂ) + (z.im : ℂ) * I) *
          (((x : ℂ) + (z.im : ℂ) * I - rho)⁻¹)) volume z.re w.re := by
    intro rho hrho
    exact horizontal_weighted_cauchy_intervalIntegrable hH_bottom (hS rho hrho).2.2.1.ne
  have htop : ∀ rho ∈ S, IntervalIntegrable
      (fun x : ℝ =>
        a rho * H ((x : ℂ) + (w.im : ℂ) * I) *
          (((x : ℂ) + (w.im : ℂ) * I - rho)⁻¹)) volume z.re w.re := by
    intro rho hrho
    exact horizontal_weighted_cauchy_intervalIntegrable hH_top (hS rho hrho).2.2.2.ne'
  have hright : ∀ rho ∈ S, IntervalIntegrable
      (fun y : ℝ =>
        a rho * H ((w.re : ℂ) + (y : ℂ) * I) *
          (((w.re : ℂ) + (y : ℂ) * I - rho)⁻¹)) volume z.im w.im := by
    intro rho hrho
    exact vertical_weighted_cauchy_intervalIntegrable hH_right (hS rho hrho).2.1.ne'
  have hleft : ∀ rho ∈ S, IntervalIntegrable
      (fun y : ℝ =>
        a rho * H ((z.re : ℂ) + (y : ℂ) * I) *
          (((z.re : ℂ) + (y : ℂ) * I - rho)⁻¹)) volume z.im w.im := by
    intro rho hrho
    exact vertical_weighted_cauchy_intervalIntegrable hH_left (hS rho hrho).1.ne
  have hone (rho : ℂ) (hrho : rho ∈ S) :
      rectIntegral (fun s => a rho * H s * (s - rho)⁻¹) z w =
        (2 * (Real.pi : ℂ) * I) * (a rho * H rho) := by
    calc
      rectIntegral (fun s => a rho * H s * (s - rho)⁻¹) z w =
          a rho * rectIntegral (fun s => H s * (s - rho)⁻¹) z w := by
        simpa only [smul_eq_mul, mul_assoc] using
          rectIntegral_smul (a rho) (fun s => H s * (s - rho)⁻¹) z w
      _ = a rho * (2 * (Real.pi : ℂ) * I * H rho) := by
        rw [rectIntegral_cauchy_kernel hH
          (hS rho hrho).1 (hS rho hrho).2.1
          (hS rho hrho).2.2.1 (hS rho hrho).2.2.2]
      _ = (2 * (Real.pi : ℂ) * I) * (a rho * H rho) := by ring
  rw [rectIntegral_finset_sum_of_intervalIntegrable
    (f := fun rho s => a rho * H s * (s - rho)⁻¹)
    hbottom htop hright hleft]
  calc
    ∑ rho ∈ S, rectIntegral (fun s => a rho * H s * (s - rho)⁻¹) z w =
        ∑ rho ∈ S, (2 * (Real.pi : ℂ) * I) * (a rho * H rho) := by
      exact Finset.sum_congr rfl (fun rho hrho => hone rho hrho)
    _ = 2 * (Real.pi : ℂ) * I * ∑ rho ∈ S, a rho * H rho := by
      rw [Finset.mul_sum]

/-- Adding a function differentiable on the closed rectangle does not change
the finite simple-residue formula for the rectangular contour integral. -/
theorem rectIntegral_finite_simple_residues_add_remainder
    {G H : ℂ → ℂ} {a : ℂ → ℂ} {S : Finset ℂ} {z w : ℂ}
    (hrew : z.re < w.re) (himw : z.im < w.im)
    (hG : ∀ s ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]), DifferentiableAt ℂ G s)
    (hH : ∀ s ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]), DifferentiableAt ℂ H s)
    (hS : ∀ rho ∈ S,
      z.re < rho.re ∧ rho.re < w.re ∧ z.im < rho.im ∧ rho.im < w.im) :
    rectIntegral
        (fun s => G s + ∑ rho ∈ S, a rho * H s * (s - rho)⁻¹) z w =
      2 * (Real.pi : ℂ) * I * ∑ rho ∈ S, a rho * H rho := by
  have hG_on : DifferentiableOn ℂ G ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    intro s hs
    exact (hG s hs).differentiableWithinAt
  have hG_zero : rectIntegral G z w = 0 :=
    rectIntegral_eq_zero_of_differentiableOn hG_on
  have hG_cont : ContinuousOn G ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
    hG_on.continuousOn
  obtain ⟨hG_bottom, hG_top, hG_right, hG_left⟩ :=
    rectangle_boundary_continuousOn hrew himw hG_cont
  have hH_cont : ContinuousOn H ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    intro s hs
    exact (hH s hs).continuousAt.continuousWithinAt
  obtain ⟨hH_bottom, hH_top, hH_right, hH_left⟩ :=
    rectangle_boundary_continuousOn hrew himw hH_cont
  have hsum_bottom : IntervalIntegrable
      (fun x : ℝ => ∑ rho ∈ S,
        a rho * H ((x : ℂ) + (z.im : ℂ) * I) *
          (((x : ℂ) + (z.im : ℂ) * I - rho)⁻¹)) volume z.re w.re := by
    have hraw := IntervalIntegrable.sum S (fun rho hrho =>
      horizontal_weighted_cauchy_intervalIntegrable
        (rho := rho) (A := a rho) hH_bottom (hS rho hrho).2.2.1.ne)
    refine hraw.congr ?_
    intro x hx
    simp only [Finset.sum_apply]
  have hsum_top : IntervalIntegrable
      (fun x : ℝ => ∑ rho ∈ S,
        a rho * H ((x : ℂ) + (w.im : ℂ) * I) *
          (((x : ℂ) + (w.im : ℂ) * I - rho)⁻¹)) volume z.re w.re := by
    have hraw := IntervalIntegrable.sum S (fun rho hrho =>
      horizontal_weighted_cauchy_intervalIntegrable
        (rho := rho) (A := a rho) hH_top (hS rho hrho).2.2.2.ne')
    refine hraw.congr ?_
    intro x hx
    simp only [Finset.sum_apply]
  have hsum_right : IntervalIntegrable
      (fun y : ℝ => ∑ rho ∈ S,
        a rho * H ((w.re : ℂ) + (y : ℂ) * I) *
          (((w.re : ℂ) + (y : ℂ) * I - rho)⁻¹)) volume z.im w.im := by
    have hraw := IntervalIntegrable.sum S (fun rho hrho =>
      vertical_weighted_cauchy_intervalIntegrable
        (rho := rho) (A := a rho) hH_right (hS rho hrho).2.1.ne')
    refine hraw.congr ?_
    intro y hy
    simp only [Finset.sum_apply]
  have hsum_left : IntervalIntegrable
      (fun y : ℝ => ∑ rho ∈ S,
        a rho * H ((z.re : ℂ) + (y : ℂ) * I) *
          (((z.re : ℂ) + (y : ℂ) * I - rho)⁻¹)) volume z.im w.im := by
    have hraw := IntervalIntegrable.sum S (fun rho hrho =>
      vertical_weighted_cauchy_intervalIntegrable
        (rho := rho) (A := a rho) hH_left (hS rho hrho).1.ne)
    refine hraw.congr ?_
    intro y hy
    simp only [Finset.sum_apply]
  have hadd := rectIntegral_add_of_intervalIntegrable
    (f := G) (g := fun s => ∑ rho ∈ S, a rho * H s * (s - rho)⁻¹)
    hG_bottom.intervalIntegrable hsum_bottom
    hG_top.intervalIntegrable hsum_top
    hG_right.intervalIntegrable hsum_right
    hG_left.intervalIntegrable hsum_left
  rw [hadd, hG_zero, zero_add,
    rectIntegral_finite_simple_residues hrew himw hH hS]

end ArithmeticHodge.Analysis.Contour
