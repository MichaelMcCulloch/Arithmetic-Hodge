import ArithmeticHodge.Analysis.YoshidaClippedMomentBridge
import Mathlib.Analysis.Fourier.Convolution

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaOddModeRegularity

noncomputable section

open YoshidaClippedMomentBridge

/-!
# Global regularity of clipped odd modes

Unlike the individual clipped exponentials, their normalized odd difference
vanishes at both endpoints.  Its zero extension is therefore globally
continuous, compactly supported, and integrable.  These facts are the first
regularity inputs for extending the smooth spectral/distribution identity to
Yoshida's odd modes.
-/

theorem yoshidaClippedOddMode_apply_all
    {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    yoshidaClippedOddMode a n x =
      if x ∈ Set.Icc (-a) a then
        (((Real.sqrt a)⁻¹ *
          Real.sin (Real.pi * (n : ℝ) * x / a) : ℝ) : ℂ)
      else 0 := by
  by_cases hx : x ∈ Set.Icc (-a) a
  · rw [if_pos hx, yoshidaClippedOddMode_apply_of_mem ha n hx]
  · rw [if_neg hx, yoshidaClippedSmooth_eq_zero_outside _ hx]

theorem yoshidaClippedOddMode_left_endpoint
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaClippedOddMode a n (-a) = 0 := by
  rw [yoshidaClippedOddMode_apply_of_mem ha n (by constructor <;> linarith)]
  norm_cast
  have ha0 : a ≠ 0 := ha.ne'
  rw [show Real.pi * (n : ℝ) * -a / a = -((n : ℝ) * Real.pi) by
    field_simp]
  rw [Real.sin_neg, Real.sin_nat_mul_pi]
  simp

theorem yoshidaClippedOddMode_right_endpoint
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    yoshidaClippedOddMode a n a = 0 := by
  rw [yoshidaClippedOddMode_apply_of_mem ha n (by constructor <;> linarith)]
  norm_cast
  have ha0 : a ≠ 0 := ha.ne'
  rw [show Real.pi * (n : ℝ) * a / a = (n : ℝ) * Real.pi by
    field_simp]
  rw [Real.sin_nat_mul_pi]
  simp

theorem continuous_yoshidaClippedOddMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Continuous (yoshidaClippedOddMode a n : ℝ → ℂ) := by
  classical
  rw [show (yoshidaClippedOddMode a n : ℝ → ℂ) =
      fun x ↦ if x ∈ Set.Icc (-a) a then
        (((Real.sqrt a)⁻¹ *
          Real.sin (Real.pi * (n : ℝ) * x / a) : ℝ) : ℂ)
      else 0 by
    funext x
    exact yoshidaClippedOddMode_apply_all ha n x]
  apply continuous_if
  · intro x hx
    change x ∈ frontier (Set.Icc (-a) a) at hx
    rw [frontier_Icc (by linarith : -a ≤ a)] at hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      norm_cast
      rw [show Real.pi * (n : ℝ) * -a / a = -((n : ℝ) * Real.pi) by
        field_simp [ha.ne']]
      simp [Real.sin_nat_mul_pi]
    · subst x
      norm_cast
      rw [show Real.pi * (n : ℝ) * a / a = (n : ℝ) * Real.pi by
        field_simp [ha.ne']]
      simp [Real.sin_nat_mul_pi]
  · exact (by fun_prop : Continuous (fun x : ℝ ↦
      (((Real.sqrt a)⁻¹ *
        Real.sin (Real.pi * (n : ℝ) * x / a) : ℝ) : ℂ))).continuousOn
  · exact continuous_const.continuousOn

theorem hasCompactSupport_yoshidaClippedOddMode
    {a : ℝ} (n : ℕ) :
    HasCompactSupport (yoshidaClippedOddMode a n : ℝ → ℂ) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_contra hmem
  exact hx (yoshidaClippedSmooth_eq_zero_outside _ hmem)

theorem integrable_yoshidaClippedOddMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (yoshidaClippedOddMode a n : ℝ → ℂ) :=
  (continuous_yoshidaClippedOddMode ha n).integrable_of_hasCompactSupport
    (hasCompactSupport_yoshidaClippedOddMode n)

end

end ArithmeticHodge.Analysis.YoshidaOddModeRegularity
