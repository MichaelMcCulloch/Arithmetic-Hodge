import ArithmeticHodge.Analysis.MultiplicativeWeilPrimeDilationKernelPositive

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Exact cross formula for normalized multiplicative dilations

These identities reduce the two-bump mixed autocorrelation to two rescaled
values of the original quadratic test.  They are the analytic input for the
exact two-dimensional Bombieri Gram reduction.
-/

/-- The directed correlation with the dilation in the first slot requires no
change of variables. -/
theorem bombieriDirectedCorrelation_normalizedDilation_left
    (g : BombieriTest) (lambda : ℝ) (hlambda : 0 < lambda) (x : ℝ) :
    bombieriDirectedCorrelation
        (normalizedDilation lambda hlambda g) g x =
      ((Real.sqrt lambda : ℝ) : ℂ) *
        bombieriQuadraticTest g (lambda * x) := by
  rw [bombieriQuadraticTest_apply]
  unfold bombieriDirectedCorrelation autocorrelation
  calc
    (∫ y : ℝ in Set.Ioi 0,
        normalizedDilation lambda hlambda g (x * y) *
          starRingEnd ℂ (g y)) =
        ∫ y : ℝ in Set.Ioi 0,
          ((Real.sqrt lambda : ℝ) : ℂ) *
            (g ((lambda * x) * y) * starRingEnd ℂ (g y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      change normalizedDilation lambda hlambda g (x * y) *
          starRingEnd ℂ (g y) =
        ((Real.sqrt lambda : ℝ) : ℂ) *
          (g ((lambda * x) * y) * starRingEnd ℂ (g y))
      rw [normalizedDilation_apply]
      rw [show lambda * (x * y) = (lambda * x) * y by ring]
      ring
    _ = ((Real.sqrt lambda : ℝ) : ℂ) *
        ∫ y : ℝ in Set.Ioi 0,
          g ((lambda * x) * y) * starRingEnd ℂ (g y) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0)) _ _

/-- After multiplying by `sqrt(lambda)`, the directed correlation with the
dilation in the second slot is the original autocorrelation at `x/lambda`. -/
theorem sqrt_mul_bombieriDirectedCorrelation_normalizedDilation_right
    (g : BombieriTest) (lambda : ℝ) (hlambda : 0 < lambda) (x : ℝ) :
    ((Real.sqrt lambda : ℝ) : ℂ) *
        bombieriDirectedCorrelation g
          (normalizedDilation lambda hlambda g) x =
      bombieriQuadraticTest g (lambda⁻¹ * x) := by
  rw [bombieriQuadraticTest_apply]
  let F : ℝ → ℂ := fun y ↦
    g ((lambda⁻¹ * x) * y) * starRingEnd ℂ (g y)
  have hscale := integral_comp_mul_right_Ioi F 0 hlambda
  have hscale' :
      (∫ y : ℝ in Set.Ioi 0, F (y * lambda)) =
        (((lambda⁻¹ : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0, F y) := by
    simpa only [zero_mul, Complex.real_smul] using hscale
  unfold bombieriDirectedCorrelation autocorrelation
  calc
    ((Real.sqrt lambda : ℝ) : ℂ) *
        ∫ y : ℝ in Set.Ioi 0,
          g (x * y) *
            starRingEnd ℂ (normalizedDilation lambda hlambda g y) =
        ((Real.sqrt lambda : ℝ) : ℂ) *
          (((Real.sqrt lambda : ℝ) : ℂ) *
            ∫ y : ℝ in Set.Ioi 0, F (y * lambda)) := by
      congr 1
      calc
        (∫ y : ℝ in Set.Ioi 0,
            g (x * y) *
              starRingEnd ℂ (normalizedDilation lambda hlambda g y)) =
            ∫ y : ℝ in Set.Ioi 0,
              ((Real.sqrt lambda : ℝ) : ℂ) * F (y * lambda) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _hy
          change g (x * y) *
              starRingEnd ℂ (normalizedDilation lambda hlambda g y) =
            ((Real.sqrt lambda : ℝ) : ℂ) * F (y * lambda)
          rw [normalizedDilation_apply]
          have hconj :
              starRingEnd ℂ
                  (((Real.sqrt lambda : ℝ) : ℂ) * g (lambda * y)) =
                ((Real.sqrt lambda : ℝ) : ℂ) *
                  starRingEnd ℂ (g (lambda * y)) := by
            calc
              starRingEnd ℂ
                    (((Real.sqrt lambda : ℝ) : ℂ) * g (lambda * y)) =
                  starRingEnd ℂ ((Real.sqrt lambda : ℝ) : ℂ) *
                    starRingEnd ℂ (g (lambda * y)) :=
                map_mul (starRingEnd ℂ) _ _
              _ = ((Real.sqrt lambda : ℝ) : ℂ) *
                    starRingEnd ℂ (g (lambda * y)) := by
                rw [Complex.conj_ofReal]
          rw [hconj]
          dsimp only [F]
          have harg : (lambda⁻¹ * x) * (y * lambda) = x * y := by
            field_simp [hlambda.ne']
          rw [harg]
          ring
        _ = ((Real.sqrt lambda : ℝ) : ℂ) *
            ∫ y : ℝ in Set.Ioi 0, F (y * lambda) := by
          exact MeasureTheory.integral_const_mul
            (μ := volume.restrict (Set.Ioi 0)) _ _
    _ = (lambda : ℂ) *
        ∫ y : ℝ in Set.Ioi 0, F (y * lambda) := by
      rw [← mul_assoc]
      congr 1
      norm_cast
      simpa [pow_two] using Real.sq_sqrt hlambda.le
    _ = (lambda : ℂ) *
        (((lambda⁻¹ : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0, F y) := by
      rw [hscale']
    _ = ∫ y : ℝ in Set.Ioi 0, F y := by
      rw [Complex.ofReal_inv]
      field_simp [hlambda.ne']
    _ = ∫ y : ℝ in Set.Ioi 0,
        g ((lambda⁻¹ * x) * y) * starRingEnd ℂ (g y) := by
      rfl

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
