/-
  Logarithmic support and Plancherel identities for Bombieri tests.

  Multiplicative support in a positive interval becomes additive support in
  the reversed logarithmic interval.  On the critical Mellin line, the
  corresponding weighted logarithmic pullback also preserves the normalized
  squared norm through Fourier Plancherel.
-/

import ArithmeticHodge.Analysis.MultiplicativeWeilMellinFourier

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap FourierTransform

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- A positive multiplicative support interval pulls back to the reversed
logarithmic interval on the additive real line. -/
theorem logarithmicPullbackSchwartz_eq_zero_outside
    (g : BombieriTest) {a b u : ℝ} (ha : 0 < a)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hu : u ∉ Set.Icc (-Real.log b) (-Real.log a)) :
    g.logarithmicPullbackSchwartz (1 / 2) u = 0 := by
  rw [BombieriTest.logarithmicPullbackSchwartz_apply]
  unfold BombieriTest.logarithmicPullback
  rw [mul_eq_zero]
  right
  by_contra hne
  have hx : Real.exp (-u) ∈ Set.Icc a b :=
    hsupport (subset_tsupport g (Function.mem_support.mpr hne))
  apply hu
  constructor
  · have hlog : Real.log (Real.exp (-u)) ≤ Real.log b :=
      Real.log_le_log (Real.exp_pos (-u)) hx.2
    rw [Real.log_exp] at hlog
    linarith
  · have hlog : Real.log a ≤ Real.log (Real.exp (-u)) :=
      Real.log_le_log ha hx.1
    rw [Real.log_exp] at hlog
    linarith

/-- Mellin Plancherel on the critical line, expressed as the squared norm of
the weighted logarithmic pullback. -/
theorem mellin_critical_normSq_integral_eq_logPullback_normSq
    (g : BombieriTest) :
    ((1 / (2 * Real.pi)) * ∫ v : ℝ,
      Complex.normSq
        (mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I))) =
      ∫ u : ℝ, Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u) := by
  simp_rw [bombieriMellin_vertical_eq_fourier, Complex.normSq_eq_norm_sq]
  have hscale := MeasureTheory.Measure.integral_comp_div
    (fun ξ : ℝ ↦
      ‖FourierTransform.fourier
        (g.logarithmicPullbackSchwartz (1 / 2)) ξ‖ ^ 2)
    (2 * Real.pi)
  rw [hscale, abs_of_pos (by positivity)]
  rw [SchwartzMap.integral_norm_sq_fourier]
  simp only [smul_eq_mul]
  field_simp

end


end ArithmeticHodge.Analysis.MultiplicativeWeil
