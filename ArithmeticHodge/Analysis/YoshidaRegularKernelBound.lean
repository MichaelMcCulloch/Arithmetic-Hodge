import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaRegularKernelBound

noncomputable section

/-! A structural bound for the regular part of Yoshida's archimedean kernel. -/

/-- The removable extension at zero of
`exp (t / 2) / (2 * sinh t) - 1 / (2 * t)`. -/
def yoshidaRegularKernel (t : ℝ) : ℝ :=
  if t = 0 then 1 / 4
  else Real.exp (t / 2) / (2 * Real.sinh t) - 1 / (2 * t)

private def lowerAux (t : ℝ) : ℝ :=
  2 * t - Real.exp (t / 2) + Real.exp (-3 * t / 2)

private def lowerSlope (t : ℝ) : ℝ :=
  2 - Real.exp (t / 2) / 2 - 3 * Real.exp (-3 * t / 2) / 2

private def lowerCurvature (t : ℝ) : ℝ :=
  -Real.exp (t / 2) / 4 + 9 * Real.exp (-3 * t / 2) / 4

private def upperAux (t : ℝ) : ℝ :=
  (2 + t) * (Real.exp (t / 2) - Real.exp (-3 * t / 2)) - 4 * t

private def upperSlope (t : ℝ) : ℝ :=
  Real.exp (t / 2) - Real.exp (-3 * t / 2) +
    (2 + t) * (Real.exp (t / 2) / 2 + 3 * Real.exp (-3 * t / 2) / 2) - 4

private def upperCurvature (t : ℝ) : ℝ :=
  (6 + t) * Real.exp (t / 2) / 4 -
    (6 + 9 * t) * Real.exp (-3 * t / 2) / 4

private theorem exp_half_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.exp (x / 2)) (Real.exp (t / 2) / 2) t := by
  convert ((hasDerivAt_id t).div_const 2).exp using 1
  all_goals simp only [id_eq]
  all_goals ring_nf

private theorem exp_neg_three_half_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.exp (-3 * x / 2))
      (-3 * Real.exp (-3 * t / 2) / 2) t := by
  convert (((hasDerivAt_id t).const_mul (-3)).div_const 2).exp using 1
  all_goals simp only [id_eq]
  all_goals ring_nf

private theorem lowerAux_hasDerivAt (t : ℝ) :
    HasDerivAt lowerAux (lowerSlope t) t := by
  unfold lowerAux lowerSlope
  convert (((hasDerivAt_id t).const_mul 2).sub (exp_half_hasDerivAt t)).add
    (exp_neg_three_half_hasDerivAt t) using 1
  all_goals ring_nf

private theorem lowerSlope_hasDerivAt (t : ℝ) :
    HasDerivAt lowerSlope (lowerCurvature t) t := by
  unfold lowerSlope lowerCurvature
  convert (((hasDerivAt_const t 2).sub ((exp_half_hasDerivAt t).div_const 2)).sub
    ((exp_neg_three_half_hasDerivAt t).const_mul 3 |>.div_const 2)) using 1
  all_goals ring_nf

private theorem upperAux_hasDerivAt (t : ℝ) :
    HasDerivAt upperAux (upperSlope t) t := by
  unfold upperAux upperSlope
  convert (((hasDerivAt_const t 2).add (hasDerivAt_id t)).mul
    ((exp_half_hasDerivAt t).sub (exp_neg_three_half_hasDerivAt t))).sub
      ((hasDerivAt_id t).const_mul 4) using 1
  all_goals simp only [id_eq, Pi.add_apply, Pi.sub_apply]
  all_goals ring_nf

private theorem upperSlope_hasDerivAt (t : ℝ) :
    HasDerivAt upperSlope (upperCurvature t) t := by
  unfold upperSlope upperCurvature
  convert (((exp_half_hasDerivAt t).sub (exp_neg_three_half_hasDerivAt t)).add
    (((hasDerivAt_const t 2).add (hasDerivAt_id t)).mul
      (((exp_half_hasDerivAt t).div_const 2).add
        ((exp_neg_three_half_hasDerivAt t).const_mul 3 |>.div_const 2)))).sub
          (hasDerivAt_const t 4) using 1
  all_goals simp only [id_eq, Pi.add_apply]
  all_goals ring_nf

private theorem value_nonneg_of_hasDerivAt_nonneg
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf0 : f 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hf' : ∀ x, 0 ≤ x → x ≤ t → 0 ≤ f' x) : 0 ≤ f t := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun x ↦ (hf x).continuousAt
  have hmono : MonotoneOn f (Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hcont.continuousOn ?_ ?_
    · intro x _
      exact (hf x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hf x).deriv]
      exact hf' x (interior_subset hx).1 (interior_subset hx).2
  have := hmono (by exact ⟨le_rfl, ht⟩) (by exact ⟨ht, le_rfl⟩) ht
  simpa [hf0] using this

private theorem exp_half_eq_exp_two_mul_exp_neg_three_half (t : ℝ) :
    Real.exp (t / 2) = Real.exp (2 * t) * Real.exp (-3 * t / 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

private theorem lowerCurvature_nonneg
    {t : ℝ} (ht2 : t ≤ Real.log 2) :
    0 ≤ lowerCurvature t := by
  have hlog : Real.exp (2 * t) ≤ 4 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    apply Real.exp_le_exp.mpr
    rw [show Real.log 4 = 2 * Real.log 2 by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      ring]
    linarith
  have hfactor := Real.exp_pos (-3 * t / 2)
  have hrel := exp_half_eq_exp_two_mul_exp_neg_three_half t
  have hcomp : Real.exp (t / 2) ≤ 9 * Real.exp (-3 * t / 2) := by
    rw [hrel]
    nlinarith
  unfold lowerCurvature
  linarith

private theorem lowerAux_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ Real.log 2) :
    0 ≤ lowerAux t := by
  have hslope : 0 ≤ lowerSlope t := by
    apply value_nonneg_of_hasDerivAt_nonneg lowerSlope_hasDerivAt
    · norm_num [lowerSlope]
    · exact ht0
    · intro x _ hxt
      exact lowerCurvature_nonneg (hxt.trans ht2)
  apply value_nonneg_of_hasDerivAt_nonneg lowerAux_hasDerivAt
  · norm_num [lowerAux]
  · exact ht0
  · intro x hx0 hxt
    apply value_nonneg_of_hasDerivAt_nonneg lowerSlope_hasDerivAt
    · norm_num [lowerSlope]
    · exact hx0
    · intro y _ hyx
      exact lowerCurvature_nonneg ((hyx.trans hxt).trans ht2)

private theorem upperCurvature_nonneg {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ upperCurvature t := by
  have hexp : 1 + 2 * t ≤ Real.exp (2 * t) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * t)
  have hcoef : 0 ≤ 6 + t := by linarith
  have hpoly : 6 + 9 * t ≤ (6 + t) * Real.exp (2 * t) := by
    have := mul_le_mul_of_nonneg_left hexp hcoef
    nlinarith
  have hfactor := Real.exp_pos (-3 * t / 2)
  have hrel := exp_half_eq_exp_two_mul_exp_neg_three_half t
  unfold upperCurvature
  rw [hrel]
  nlinarith

private theorem upperAux_nonneg {t : ℝ} (ht0 : 0 ≤ t) : 0 ≤ upperAux t := by
  apply value_nonneg_of_hasDerivAt_nonneg upperAux_hasDerivAt
  · norm_num [upperAux]
  · exact ht0
  · intro x hx0 _
    apply value_nonneg_of_hasDerivAt_nonneg upperSlope_hasDerivAt
    · norm_num [upperSlope]
    · exact hx0
    · intro y hy0 _
      exact upperCurvature_nonneg hy0

private theorem sinh_eq_exp_difference (t : ℝ) :
    Real.sinh t = Real.exp (t / 2) *
      (Real.exp (t / 2) - Real.exp (-3 * t / 2)) / 2 := by
  rw [Real.sinh_eq]
  rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
  congr 1
  all_goals ring_nf

private theorem sinh_le_mul_exp_half
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ Real.log 2) :
    Real.sinh t ≤ t * Real.exp (t / 2) := by
  have haux := lowerAux_nonneg ht0 ht2
  have hexp := Real.exp_pos (t / 2)
  rw [sinh_eq_exp_difference]
  unfold lowerAux at haux
  nlinarith

private theorem two_mul_exp_half_le_two_add_mul_sinh {t : ℝ} (ht0 : 0 ≤ t) :
    2 * t * Real.exp (t / 2) ≤ (2 + t) * Real.sinh t := by
  have haux := upperAux_nonneg ht0
  have hexp := Real.exp_pos (t / 2)
  rw [sinh_eq_exp_difference]
  unfold upperAux at haux
  nlinarith

theorem yoshidaRegularKernel_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ Real.log 2) :
    0 ≤ yoshidaRegularKernel t := by
  by_cases ht : t = 0
  · simp [yoshidaRegularKernel, ht]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hsinh : 0 < Real.sinh t := Real.sinh_pos_iff.mpr htpos
    have hmain := sinh_le_mul_exp_half ht0 ht2
    rw [yoshidaRegularKernel, if_neg ht]
    rw [sub_nonneg, div_le_div_iff₀ (by positivity : 0 < 2 * t)
      (by positivity : 0 < 2 * Real.sinh t)]
    nlinarith

theorem yoshidaRegularKernel_le_quarter {t : ℝ} (ht0 : 0 ≤ t) :
    yoshidaRegularKernel t ≤ 1 / 4 := by
  by_cases ht : t = 0
  · simp [yoshidaRegularKernel, ht]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hsinh : 0 < Real.sinh t := Real.sinh_pos_iff.mpr htpos
    have hmain := two_mul_exp_half_le_two_add_mul_sinh ht0
    rw [yoshidaRegularKernel, if_neg ht]
    rw [sub_le_iff_le_add]
    rw [div_le_iff₀ (by positivity : 0 < 2 * Real.sinh t)]
    rw [add_mul]
    field_simp [ht] at hmain ⊢
    nlinarith

theorem yoshidaRegularKernel_mem_Icc
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ Real.log 2) :
    0 ≤ yoshidaRegularKernel t ∧ yoshidaRegularKernel t ≤ 1 / 4 :=
  ⟨yoshidaRegularKernel_nonneg ht0 ht2, yoshidaRegularKernel_le_quarter ht0⟩

end

end ArithmeticHodge.Analysis.YoshidaRegularKernelBound
