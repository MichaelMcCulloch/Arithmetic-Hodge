import ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationSmoothStructural
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationDerivativeStructural

noncomputable section

open MultiplicativeWeil

local instance : ContinuousSMul ℝ ℂ :=
  continuousSMul_of_algebraMap ℝ ℂ Complex.continuous_ofReal

/-- Differentiation of the directed correlation under its physical
`y`-integral. Compact support of the right input supplies a single integrable
dominating function. -/
theorem bombieriDirectedCorrelation_hasDerivAt_integral
    (f h : BombieriTest) (x : ℝ) :
    HasDerivAt (bombieriDirectedCorrelation f h)
      (∫ y : ℝ in Set.Ioi 0,
        ((y : ℂ) * deriv f (x * y)) * starRingEnd ℂ (h y)) x := by
  let F : ℝ → ℝ → ℂ := fun z y ↦
    f (z * y) * starRingEnd ℂ (h y)
  let F' : ℝ → ℝ → ℂ := fun z y ↦
    ((y : ℂ) * deriv f (z * y)) * starRingEnd ℂ (h y)
  have hfderiv_cont : Continuous (deriv f) :=
    f.contDiff.continuous_deriv (by simp)
  have hfderiv_compact : HasCompactSupport (deriv f) :=
    f.hasCompactSupport.deriv
  obtain ⟨C, hC⟩ :=
    hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
  let bound : ℝ → ℝ := fun y ↦ |y| * C * ‖h y‖
  have hF_meas : ∀ᶠ z in nhds x,
      AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards with z
    exact (show Continuous (F z) by
      dsimp only [F]
      fun_prop).aestronglyMeasurable
  have hF_int : Integrable (F x) (volume.restrict (Set.Ioi 0)) := by
    have hcont : Continuous (F x) := by
      dsimp only [F]
      fun_prop
    have hhcompact : HasCompactSupport
        (fun y : ℝ ↦ starRingEnd ℂ (h y)) :=
      h.hasCompactSupport.comp_left (by simp)
    have hcompact : HasCompactSupport (F x) := by
      simpa only [F, Pi.mul_apply] using
        hhcompact.mul_left (f := fun y : ℝ ↦ f (x * y))
    exact (hcont.integrable_of_hasCompactSupport hcompact).integrableOn
  have hF'_meas :
      AEStronglyMeasurable (F' x) (volume.restrict (Set.Ioi 0)) := by
    exact (show Continuous (F' x) by
      dsimp only [F']
      fun_prop).aestronglyMeasurable
  have h_bound : ∀ᵐ y : ℝ ∂(volume.restrict (Set.Ioi 0)),
      ∀ z ∈ (Set.univ : Set ℝ), ‖F' z y‖ ≤ bound y := by
    filter_upwards with y
    intro z _hz
    dsimp only [F', bound]
    calc
      ‖((y : ℂ) * deriv f (z * y)) * starRingEnd ℂ (h y)‖ =
          |y| * ‖deriv f (z * y)‖ * ‖h y‖ := by
            simp only [norm_mul, norm_real, Real.norm_eq_abs,
              Complex.norm_conj]
      _ ≤ |y| * C * ‖h y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hC (z * y)) (abs_nonneg y))
          (norm_nonneg (h y))
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) := by
    have hcont : Continuous bound := by
      dsimp only [bound]
      fun_prop
    have hcompact : HasCompactSupport bound := by
      exact h.hasCompactSupport.norm.mul_left
        (f := fun y : ℝ ↦ |y| * C)
    exact (hcont.integrable_of_hasCompactSupport hcompact).integrableOn
  have h_diff : ∀ᵐ y : ℝ ∂(volume.restrict (Set.Ioi 0)),
      ∀ z ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun w ↦ F w y) (F' z y) z := by
    filter_upwards with y
    intro z _hz
    have hf_at : HasDerivAt f (deriv f (z * y)) (z * y) :=
      (f.contDiff.differentiable (by simp) (z * y)).hasDerivAt
    have harg : HasDerivAt (fun w : ℝ ↦ w * y) y z :=
      hasDerivAt_mul_const y
    have hcomp := hf_at.hasFDerivAt.comp z harg.hasFDerivAt
    have hcomp' := hcomp.hasDerivAt
    simpa only [F, F', Function.comp_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      Complex.real_smul] using
        hcomp'.mul_const (starRingEnd ℂ (h y))
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound)
    (x₀ := x) (s := Set.univ) (μ := volume.restrict (Set.Ioi 0))
    Filter.univ_mem hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa only [F, F', bombieriDirectedCorrelation] using H.2

/-- Product rule for a Bombieri test cut out of a common parent by a smooth
real weight. -/
theorem deriv_eq_of_eq_realWeight_mul
    (f g : BombieriTest) (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ∞ eta)
    (hf : ∀ z : ℝ, f z = (eta z : ℂ) * g z) (z : ℝ) :
    deriv f z =
      ((deriv eta z : ℝ) : ℂ) * g z + (eta z : ℂ) * deriv g z := by
  have heta_real : HasDerivAt eta (deriv eta z) z :=
    (heta.differentiable (by simp) z).hasDerivAt
  have heta_complex : HasDerivAt (fun w : ℝ ↦ (eta w : ℂ))
      ((deriv eta z : ℝ) : ℂ) z :=
    heta_real.ofReal_comp
  have hg : HasDerivAt g (deriv g z) z :=
    (g.contDiff.differentiable (by simp) z).hasDerivAt
  have hprod := heta_complex.mul hg
  calc
    deriv f z = deriv (fun w : ℝ ↦ (eta w : ℂ) * g w) z := by
      congr 1
      exact funext hf
    _ = ((deriv eta z : ℝ) : ℂ) * g z +
        (eta z : ℂ) * deriv g z :=
      hprod.deriv

/-- Explicit coherent-weight specialization. The derivative separates into
the derivative of the left partition weight and the derivative of the common
Bombieri parent; the right weight is fixed with respect to `x`. -/
theorem bombieriDirectedCorrelation_hasDerivAt_coherentWeights
    (f h g : BombieriTest) (eta theta : ℝ → ℝ)
    (heta : ContDiff ℝ ∞ eta) (_htheta : ContDiff ℝ ∞ theta)
    (hf : ∀ z : ℝ, f z = (eta z : ℂ) * g z)
    (hh : ∀ z : ℝ, h z = (theta z : ℂ) * g z)
    (x : ℝ) :
    HasDerivAt (bombieriDirectedCorrelation f h)
      (∫ y : ℝ in Set.Ioi 0,
        (((y * deriv eta (x * y) * theta y : ℝ) : ℂ) *
            (g (x * y) * starRingEnd ℂ (g y)) +
          ((y * eta (x * y) * theta y : ℝ) : ℂ) *
            (deriv g (x * y) * starRingEnd ℂ (g y)))) x := by
  have H := bombieriDirectedCorrelation_hasDerivAt_integral f h x
  convert H using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  dsimp only
  have hstar :
      starRingEnd ℂ ((theta y : ℂ) * g y) =
        (theta y : ℂ) * starRingEnd ℂ (g y) := by
    rw [map_mul, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  rw [deriv_eq_of_eq_realWeight_mul f g eta heta hf (x * y), hh y,
    hstar]
  push_cast
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationDerivativeStructural
