import ArithmeticHodge.Analysis.MultiplicativeWeilDilationCrossFormula

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Exact scalar two-bump cross formula

The mixed autocorrelation is complex-linear in its first slot and
conjugate-linear in its second slot.  Combined with normalized dilation, this
gives the exact real-space symbol for a two-bump family.
-/

theorem bombieriDirectedCorrelation_smul_left
    (c : ℂ) (f g : BombieriTest) (x : ℝ) :
    bombieriDirectedCorrelation (c • f) g x =
      c * bombieriDirectedCorrelation f g x := by
  unfold bombieriDirectedCorrelation
  calc
    (∫ y : ℝ in Set.Ioi 0,
        (c • f) (x * y) * starRingEnd ℂ (g y)) =
        ∫ y : ℝ in Set.Ioi 0,
          c * (f (x * y) * starRingEnd ℂ (g y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      change c * f (x * y) * starRingEnd ℂ (g y) =
        c * (f (x * y) * starRingEnd ℂ (g y))
      ring
    _ = c * ∫ y : ℝ in Set.Ioi 0,
        f (x * y) * starRingEnd ℂ (g y) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0)) _ _

theorem bombieriDirectedCorrelation_smul_right
    (c : ℂ) (f g : BombieriTest) (x : ℝ) :
    bombieriDirectedCorrelation f (c • g) x =
      starRingEnd ℂ c * bombieriDirectedCorrelation f g x := by
  unfold bombieriDirectedCorrelation
  calc
    (∫ y : ℝ in Set.Ioi 0,
        f (x * y) * starRingEnd ℂ ((c • g) y)) =
        ∫ y : ℝ in Set.Ioi 0,
          starRingEnd ℂ c *
            (f (x * y) * starRingEnd ℂ (g y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      change f (x * y) * starRingEnd ℂ (c * g y) =
        starRingEnd ℂ c *
          (f (x * y) * starRingEnd ℂ (g y))
      have hconj : starRingEnd ℂ (c * g y) =
          starRingEnd ℂ c * starRingEnd ℂ (g y) :=
        map_mul (starRingEnd ℂ) _ _
      rw [hconj]
      ring
    _ = starRingEnd ℂ c * ∫ y : ℝ in Set.Ioi 0,
        f (x * y) * starRingEnd ℂ (g y) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0)) _ _

/-- Exact support-free mixed autocorrelation of a test and a scalar multiple
of its normalized dilation. -/
theorem bombieriQuadraticCrossTest_smul_normalizedDilation
    (g : BombieriTest) (c : ℂ) (lambda : ℝ)
    (hlambda : 0 < lambda) (x : ℝ) :
    bombieriQuadraticCrossTest g
        (c • normalizedDilation lambda hlambda g) x =
      starRingEnd ℂ c /
          ((Real.sqrt lambda : ℝ) : ℂ) *
            bombieriQuadraticTest g (lambda⁻¹ * x) +
        c * ((Real.sqrt lambda : ℝ) : ℂ) *
          bombieriQuadraticTest g (lambda * x) := by
  rw [bombieriQuadraticCrossTest_apply,
    bombieriDirectedCorrelation_smul_right,
    bombieriDirectedCorrelation_smul_left,
    bombieriDirectedCorrelation_normalizedDilation_left]
  have hright :=
    sqrt_mul_bombieriDirectedCorrelation_normalizedDilation_right
      g lambda hlambda x
  have hsqrt : ((Real.sqrt lambda : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hlambda).ne'
  apply (mul_left_cancel₀ hsqrt)
  calc
    ((Real.sqrt lambda : ℝ) : ℂ) *
          (starRingEnd ℂ c *
              bombieriDirectedCorrelation g
                (normalizedDilation lambda hlambda g) x +
            c * (((Real.sqrt lambda : ℝ) : ℂ) *
              bombieriQuadraticTest g (lambda * x))) =
        starRingEnd ℂ c *
            (((Real.sqrt lambda : ℝ) : ℂ) *
              bombieriDirectedCorrelation g
                (normalizedDilation lambda hlambda g) x) +
          ((Real.sqrt lambda : ℝ) : ℂ) *
            (c * (((Real.sqrt lambda : ℝ) : ℂ) *
              bombieriQuadraticTest g (lambda * x))) := by
      ring
    _ = starRingEnd ℂ c *
            bombieriQuadraticTest g (lambda⁻¹ * x) +
          ((Real.sqrt lambda : ℝ) : ℂ) *
            (c * (((Real.sqrt lambda : ℝ) : ℂ) *
              bombieriQuadraticTest g (lambda * x))) := by
      rw [hright]
    _ = ((Real.sqrt lambda : ℝ) : ℂ) *
        (starRingEnd ℂ c /
            ((Real.sqrt lambda : ℝ) : ℂ) *
              bombieriQuadraticTest g (lambda⁻¹ * x) +
          c * ((Real.sqrt lambda : ℝ) : ℂ) *
            bombieriQuadraticTest g (lambda * x)) := by
      field_simp [hsqrt]

/-- Factor-two specialization, with the inverse lag written as `x / 2`. -/
theorem bombieriQuadraticCrossTest_smul_dilation_two
    (g : BombieriTest) (c : ℂ) (x : ℝ) :
    bombieriQuadraticCrossTest g
        (c • normalizedDilation 2 (by norm_num) g) x =
      starRingEnd ℂ c /
          ((Real.sqrt 2 : ℝ) : ℂ) *
            bombieriQuadraticTest g (x / 2) +
        c * ((Real.sqrt 2 : ℝ) : ℂ) *
          bombieriQuadraticTest g (2 * x) := by
  rw [bombieriQuadraticCrossTest_smul_normalizedDilation]
  congr 3
  field_simp

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
