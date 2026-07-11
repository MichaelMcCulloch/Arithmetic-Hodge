import ArithmeticHodge.Analysis.ResidueRectangle
import ArithmeticHodge.Analysis.Contour.ArgumentPrinciple
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open Complex MeasureTheory Set
open scoped Interval Real

namespace ArithmeticHodge.Analysis

private lemma horizontal_inv_integral_eq_log_sub
    {a b c : ℝ} {rho : ℂ} (hc : c ≠ rho.im) :
    (∫ x : ℝ in a..b, ((x : ℂ) + (c : ℂ) * I - rho)⁻¹) =
      log ((b : ℂ) + (c : ℂ) * I - rho) -
        log ((a : ℂ) + (c : ℂ) * I - rho) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hline : HasDerivAt
        (fun t : ℝ => (t : ℂ) + (c : ℂ) * I - rho) 1 x := by
      simpa [sub_eq_add_neg, add_assoc] using
        ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const
          ((c : ℂ) * I - rho))
    have hslit : (x : ℂ) + (c : ℂ) * I - rho ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      simpa using sub_ne_zero.mpr hc
    simpa [div_eq_mul_inv] using hline.clog_real hslit
  · refine (ContinuousOn.inv₀ (by fun_prop) ?_).intervalIntegrable
    intro x hx hzero
    have him : (((x : ℂ) + (c : ℂ) * I - rho)).im = 0 := by
      rw [hzero]
      rfl
    exact hc (sub_eq_zero.mp (by simpa using him))

private lemma vertical_inv_integral_mul_I_eq_log_sub_of_right
    {a b r : ℝ} {rho : ℂ} (hr : rho.re < r) :
    I * (∫ y : ℝ in a..b, ((r : ℂ) + (y : ℂ) * I - rho)⁻¹) =
      log ((r : ℂ) + (b : ℂ) * I - rho) -
        log ((r : ℂ) + (a : ℂ) * I - rho) := by
  calc
    I * (∫ y : ℝ in a..b, ((r : ℂ) + (y : ℂ) * I - rho)⁻¹) =
        ∫ y : ℝ in a..b, I * ((r : ℂ) + (y : ℂ) * I - rho)⁻¹ := by
          exact (intervalIntegral.integral_const_mul I _).symm
    _ = _ := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro y hy
        have hline : HasDerivAt
            (fun t : ℝ => (r : ℂ) + (t : ℂ) * I - rho) I y := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add
              ((r : ℂ) - rho)
        have hslit : (r : ℂ) + (y : ℂ) * I - rho ∈ Complex.slitPlane := by
          rw [Complex.mem_slitPlane_iff]
          left
          simpa using sub_pos.mpr hr
        simpa [div_eq_mul_inv] using hline.clog_real hslit
      · refine (ContinuousOn.inv₀ (by fun_prop) ?_).const_mul I |>.intervalIntegrable
        intro y hy hzero
        have hre : (((r : ℂ) + (y : ℂ) * I - rho)).re = 0 := by
          rw [hzero]
          rfl
        linarith [show r - rho.re = 0 by simpa using hre]

private lemma vertical_inv_integral_mul_I_eq_log_neg_sub_of_left
    {a b r : ℝ} {rho : ℂ} (hr : r < rho.re) :
    I * (∫ y : ℝ in a..b, ((r : ℂ) + (y : ℂ) * I - rho)⁻¹) =
      log (-((r : ℂ) + (b : ℂ) * I - rho)) -
        log (-((r : ℂ) + (a : ℂ) * I - rho)) := by
  calc
    I * (∫ y : ℝ in a..b, ((r : ℂ) + (y : ℂ) * I - rho)⁻¹) =
        ∫ y : ℝ in a..b, I * ((r : ℂ) + (y : ℂ) * I - rho)⁻¹ := by
          exact (intervalIntegral.integral_const_mul I _).symm
    _ = _ := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro y hy
        have hline : HasDerivAt
            (fun t : ℝ => (r : ℂ) + (t : ℂ) * I - rho) I y := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add
              ((r : ℂ) - rho)
        have hslit : -((r : ℂ) + (y : ℂ) * I - rho) ∈ Complex.slitPlane := by
          rw [Complex.mem_slitPlane_iff]
          left
          simpa using sub_pos.mpr hr
        convert hline.neg.clog_real hslit using 1
        simp only [Pi.neg_apply, div_eq_mul_inv, ← neg_inv]
        ring
      · refine (ContinuousOn.inv₀ (by fun_prop) ?_).const_mul I |>.intervalIntegrable
        intro y hy hzero
        have hre : (((r : ℂ) + (y : ℂ) * I - rho)).re = 0 := by
          rw [hzero]
          rfl
        linarith [show r - rho.re = 0 by simpa using hre]

private lemma log_sub_log_neg_eq_pi_mul_I_of_im_pos
    {x : ℂ} (hx : 0 < x.im) :
    log x - log (-x) = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx]

private lemma log_neg_sub_log_eq_pi_mul_I_of_im_neg
    {x : ℂ} (hx : x.im < 0) :
    log (-x) - log x = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hx]

theorem rectIntegral_sub_inv_of_mem_rectangle_scratch
    {z w ρ : ℂ}
    (hre₀ : z.re < ρ.re) (hre₁ : ρ.re < w.re)
    (him₀ : z.im < ρ.im) (him₁ : ρ.im < w.im) :
    rectIntegral (fun s => (s - ρ)⁻¹) z w =
      2 * (Real.pi : ℂ) * Complex.I := by
  have hbottom := horizontal_inv_integral_eq_log_sub
    (a := z.re) (b := w.re) (c := z.im) (rho := ρ) him₀.ne
  have htop := horizontal_inv_integral_eq_log_sub
    (a := z.re) (b := w.re) (c := w.im) (rho := ρ) him₁.ne'
  have hright := vertical_inv_integral_mul_I_eq_log_sub_of_right
    (a := z.im) (b := w.im) (r := w.re) (rho := ρ) hre₁
  have hleft := vertical_inv_integral_mul_I_eq_log_neg_sub_of_left
    (a := z.im) (b := w.im) (r := z.re) (rho := ρ) hre₀
  have hu_im : 0 < ((z.re : ℂ) + (w.im : ℂ) * I - ρ).im := by
    simpa using sub_pos.mpr him₁
  have hl_im : ((z.re : ℂ) + (z.im : ℂ) * I - ρ).im < 0 := by
    simpa using sub_neg.mpr him₀
  have hu := log_sub_log_neg_eq_pi_mul_I_of_im_pos hu_im
  have hl := log_neg_sub_log_eq_pi_mul_I_of_im_neg hl_im
  simp only [rectIntegral, smul_eq_mul]
  rw [hbottom, htop, hright, hleft]
  calc
    _ =
        (log ((z.re : ℂ) + (w.im : ℂ) * I - ρ) -
          log (-((z.re : ℂ) + (w.im : ℂ) * I - ρ))) +
        (log (-((z.re : ℂ) + (z.im : ℂ) * I - ρ)) -
          log ((z.re : ℂ) + (z.im : ℂ) * I - ρ)) := by ring
    _ = 2 * (Real.pi : ℂ) * I := by rw [hu, hl]; ring

end ArithmeticHodge.Analysis

#print axioms ArithmeticHodge.Analysis.rectIntegral_sub_inv_of_mem_rectangle_scratch
