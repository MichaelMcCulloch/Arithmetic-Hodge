import ArithmeticHodge.Analysis.MultiplicativeWeilTwoBumpDeterminant

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap FourierTransform

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Mellin action of normalized multiplicative dilation

The critical translation used by the two-bump reduction is the zero-weight
case of an exact identity on every logarithmic Mellin line.
-/

theorem normalizedDilation_logarithmicPullbackSchwartz
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest)
    (sigma u : ℝ) :
    (normalizedDilation lambda hlambda g).logarithmicPullbackSchwartz
        sigma u =
      ((Real.sqrt lambda * Real.exp (-sigma * Real.log lambda) : ℝ) : ℂ) *
        g.logarithmicPullbackSchwartz sigma (u - Real.log lambda) := by
  rw [BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullbackSchwartz_apply]
  unfold BombieriTest.logarithmicPullback
  rw [normalizedDilation_apply]
  have hargument :
      lambda * Real.exp (-u) =
        Real.exp (-(u - Real.log lambda)) := by
    rw [show -(u - Real.log lambda) = Real.log lambda + -u by ring,
      Real.exp_add, Real.exp_log hlambda]
  rw [hargument]
  have hweight :
      Real.exp (-sigma * u) * Real.sqrt lambda =
        (Real.sqrt lambda * Real.exp (-sigma * Real.log lambda)) *
          Real.exp (-sigma * (u - Real.log lambda)) := by
    rw [mul_assoc, ← Real.exp_add]
    rw [show -sigma * Real.log lambda +
        -sigma * (u - Real.log lambda) = -sigma * u by ring]
    ring
  rw [← mul_assoc, ← Complex.ofReal_mul, hweight]
  push_cast
  ring

/-- On a vertical Mellin line, normalized dilation is multiplication by its
real weight and the Fourier phase of the logarithmic translation. -/
theorem mellin_normalizedDilation_vertical
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest)
    (sigma t : ℝ) :
    mellin (normalizedDilation lambda hlambda g : ℝ → ℂ)
        (sigma + t * Complex.I) =
      ((Real.sqrt lambda * Real.exp (-sigma * Real.log lambda) : ℝ) : ℂ) *
        (Real.fourierChar
          ((-Real.log lambda) * (t / (2 * Real.pi))) : ℂ) *
        mellin (g : ℝ → ℂ) (sigma + t * Complex.I) := by
  rw [bombieriMellin_vertical_eq_fourier,
    bombieriMellin_vertical_eq_fourier]
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  let F : ℝ → ℂ :=
    g.logarithmicPullbackSchwartz sigma
  let alpha : ℂ :=
    ((Real.sqrt lambda * Real.exp (-sigma * Real.log lambda) : ℝ) : ℂ)
  have hpull :
      ((normalizedDilation lambda hlambda g).logarithmicPullbackSchwartz
          sigma : ℝ → ℂ) =
        alpha • (F ∘ fun u : ℝ ↦ u + (-Real.log lambda)) := by
    funext u
    change (normalizedDilation lambda hlambda g).logarithmicPullbackSchwartz
        sigma u = alpha * F (u + (-Real.log lambda))
    rw [normalizedDilation_logarithmicPullbackSchwartz]
    dsimp only [alpha, F, Function.comp_apply]
    rw [show u + -Real.log lambda = u - Real.log lambda by ring]
  rw [hpull]
  have hsmul := Fourier.fourierIntegral_const_smul
    Real.fourierChar volume
      (F ∘ fun u : ℝ ↦ u + (-Real.log lambda)) alpha
  have hsmulValue := congrFun hsmul (t / (2 * Real.pi))
  simp only [Pi.smul_apply, smul_eq_mul] at hsmulValue
  have hbridge (H : ℝ → ℂ) (xi : ℝ) :
      𝓕 H xi =
        Fourier.fourierIntegral Real.fourierChar volume H xi := by
    rw [Real.fourier_eq, Fourier.fourierIntegral_def]
    apply integral_congr_ae
    filter_upwards [] with u
    congr 1
    apply congrArg Real.fourierChar
    change -(xi * u) = -(u * xi)
    ring
  have htranslate := Fourier.fourierIntegral_comp_add_right
    Real.fourierChar volume F (-Real.log lambda)
  have hvalue := congrFun htranslate (t / (2 * Real.pi))
  rw [hbridge
      (alpha • (F ∘ fun u : ℝ ↦ u + -Real.log lambda))
      (t / (2 * Real.pi)),
    hsmulValue, hvalue,
    hbridge F (t / (2 * Real.pi))]
  simp only [Circle.smul_def, smul_eq_mul]
  dsimp only [alpha]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
