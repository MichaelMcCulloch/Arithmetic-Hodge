import ArithmeticHodge.Analysis.YoshidaClippedCriticalForm
import ArithmeticHodge.Analysis.MultiplicativeWeilDigamma

/-!
# Parity orthogonality for Yoshida's clipped critical form

Reflection preserves Bombieri's real critical kernel.  Consequently the
critical samples of odd functions are odd in the spectral variable, while
those of even functions are even.  The polar terms cancel in the same way,
so the clipped local critical form has no odd/even cross term.
-/

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis

noncomputable section

/-- Bombieri's critical kernel is even in its real spectral variable. -/
theorem bombieriLocalCriticalKernel_neg (v : ℝ) :
    MultiplicativeWeil.bombieriLocalCriticalKernel (-v) =
      MultiplicativeWeil.bombieriLocalCriticalKernel v := by
  rw [MultiplicativeWeil.bombieriLocalCriticalKernel,
    MultiplicativeWeil.bombieriLocalCriticalKernel,
    MultiplicativeWeil.digamma_quarter_vertical_re_eq,
    MultiplicativeWeil.digamma_quarter_vertical_re_eq]
  simp [MultiplicativeWeil.bombieriDigammaKernel]

/-- Reflection makes the centered Laplace transform of an odd function odd. -/
theorem yoshidaCenteredLaplaceLinear_odd_neg
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (z : ℂ) :
    yoshidaCenteredLaplaceLinear a ha (-z) f =
      -yoshidaCenteredLaplaceLinear a ha z f := by
  rw [yoshidaCenteredLaplaceLinear_apply,
    yoshidaCenteredLaplaceLinear_apply]
  have h :
      (∫ x : ℝ in -a..a,
        Complex.exp (-(z * ((-x : ℝ) : ℂ))) * f (-x)) =
      ∫ x : ℝ in -a..a,
        Complex.exp (-(z * (x : ℂ))) * f x := by
    simpa only [Function.comp_apply, neg_neg] using
      intervalIntegral.integral_comp_neg
        (a := -a) (b := a)
        (fun x : ℝ ↦ Complex.exp (-(z * (x : ℂ))) * f x)
  calc
    (∫ x : ℝ in -a..a,
        Complex.exp (-((-z) * (x : ℂ))) * f x) =
      ∫ x : ℝ in -a..a,
        -(Complex.exp (-(z * ((-x : ℝ) : ℂ))) * f (-x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      change Complex.exp (-((-z) * (x : ℂ))) * f x =
        -(Complex.exp (-(z * ((-x : ℝ) : ℂ))) * f (-x))
      rw [hodd x]
      push_cast
      ring_nf
    _ = -(∫ x : ℝ in -a..a,
        Complex.exp (-(z * ((-x : ℝ) : ℂ))) * f (-x)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ x : ℝ in -a..a,
        Complex.exp (-(z * (x : ℂ))) * f x) := by rw [h]

/-- Reflection makes the centered Laplace transform of an even function even. -/
theorem yoshidaCenteredLaplaceLinear_even_neg
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (heven : ∀ x : ℝ, f (-x) = f x) (z : ℂ) :
    yoshidaCenteredLaplaceLinear a ha (-z) f =
      yoshidaCenteredLaplaceLinear a ha z f := by
  rw [yoshidaCenteredLaplaceLinear_apply,
    yoshidaCenteredLaplaceLinear_apply]
  have h :
      (∫ x : ℝ in -a..a,
        Complex.exp (-(z * ((-x : ℝ) : ℂ))) * f (-x)) =
      ∫ x : ℝ in -a..a,
        Complex.exp (-(z * (x : ℂ))) * f x := by
    simpa only [Function.comp_apply, neg_neg] using
      intervalIntegral.integral_comp_neg
        (a := -a) (b := a)
        (fun x : ℝ ↦ Complex.exp (-(z * (x : ℂ))) * f x)
  calc
    (∫ x : ℝ in -a..a,
        Complex.exp (-((-z) * (x : ℂ))) * f x) =
      ∫ x : ℝ in -a..a,
        Complex.exp (-(z * ((-x : ℝ) : ℂ))) * f (-x) := by
      apply intervalIntegral.integral_congr
      intro x _
      change Complex.exp (-((-z) * (x : ℂ))) * f x =
        Complex.exp (-(z * ((-x : ℝ) : ℂ))) * f (-x)
      rw [heven x]
      push_cast
      congr 2
      ring
    _ = _ := h

theorem yoshidaPositivePolar_odd_eq_neg_negative
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hodd : ∀ x : ℝ, f (-x) = -f x) :
    yoshidaPositivePolarLinear a ha f =
      -yoshidaNegativePolarLinear a ha f := by
  change yoshidaCenteredLaplaceLinear a ha (1 / 2 : ℂ) f =
    -yoshidaCenteredLaplaceLinear a ha (-1 / 2 : ℂ) f
  have h :=
    yoshidaCenteredLaplaceLinear_odd_neg ha f hodd (1 / 2 : ℂ)
  rw [show -(1 / 2 : ℂ) = (-1 / 2 : ℂ) by ring] at h
  rw [h]
  simp

theorem yoshidaPositivePolar_even_eq_negative
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    yoshidaPositivePolarLinear a ha f =
      yoshidaNegativePolarLinear a ha f := by
  change yoshidaCenteredLaplaceLinear a ha (1 / 2 : ℂ) f =
    yoshidaCenteredLaplaceLinear a ha (-1 / 2 : ℂ) f
  have h :=
    yoshidaCenteredLaplaceLinear_even_neg ha f heven (1 / 2 : ℂ)
  rw [show -(1 / 2 : ℂ) = (-1 / 2 : ℂ) by ring] at h
  exact h.symm

theorem yoshidaCriticalSample_odd_neg
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (v : ℝ) :
    yoshidaCriticalSampleLinear a ha (-v) f =
      -yoshidaCriticalSampleLinear a ha v f := by
  change yoshidaCenteredLaplaceLinear a ha (((-v : ℝ) : ℂ) * Complex.I) f =
    -yoshidaCenteredLaplaceLinear a ha ((v : ℂ) * Complex.I) f
  rw [show (((-v : ℝ) : ℂ) * Complex.I) =
    -((v : ℂ) * Complex.I) by push_cast; ring]
  exact yoshidaCenteredLaplaceLinear_odd_neg
    ha f hodd ((v : ℂ) * Complex.I)

theorem yoshidaCriticalSample_even_neg
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (heven : ∀ x : ℝ, f (-x) = f x) (v : ℝ) :
    yoshidaCriticalSampleLinear a ha (-v) f =
      yoshidaCriticalSampleLinear a ha v f := by
  change yoshidaCenteredLaplaceLinear a ha (((-v : ℝ) : ℂ) * Complex.I) f =
    yoshidaCenteredLaplaceLinear a ha ((v : ℂ) * Complex.I) f
  rw [show (((-v : ℝ) : ℂ) * Complex.I) =
    -((v : ℂ) * Complex.I) by push_cast; ring]
  exact yoshidaCenteredLaplaceLinear_even_neg
    ha f heven ((v : ℂ) * Complex.I)

/-- The odd/even critical cross integrand is odd in the spectral variable. -/
theorem yoshidaClippedCriticalCrossIntegrand_odd_even_neg
    {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a)
    (hodd : ∀ x : ℝ, f (-x) = -f x)
    (heven : ∀ x : ℝ, g (-x) = g x) (v : ℝ) :
    yoshidaClippedCriticalCrossIntegrand a ha f g (-v) =
      -yoshidaClippedCriticalCrossIntegrand a ha f g v := by
  rw [yoshidaClippedCriticalCrossIntegrand,
    yoshidaClippedCriticalCrossIntegrand,
    bombieriLocalCriticalKernel_neg,
    yoshidaCriticalSample_odd_neg ha f hodd,
    yoshidaCriticalSample_even_neg ha g heven]
  simp

/-- The spectral part of the odd/even cross term vanishes. -/
theorem integral_yoshidaClippedCriticalCrossIntegrand_odd_even_eq_zero
    {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a)
    (hodd : ∀ x : ℝ, f (-x) = -f x)
    (heven : ∀ x : ℝ, g (-x) = g x) :
    (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f g v) = 0 := by
  let F : ℝ → ℂ := yoshidaClippedCriticalCrossIntegrand a ha f g
  have hmeasure : (∫ v : ℝ, F (-v)) = ∫ v : ℝ, F v := by
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (MeasurableEquiv.neg ℝ).measurableEmbedding F
  have hneg : (∫ v : ℝ, F (-v)) = -(∫ v : ℝ, F v) := by
    calc
      (∫ v : ℝ, F (-v)) = ∫ v : ℝ, -F v := by
        apply integral_congr_ae
        filter_upwards [] with v
        exact yoshidaClippedCriticalCrossIntegrand_odd_even_neg
          ha f g hodd heven v
      _ = -(∫ v : ℝ, F v) := integral_neg F
  have hself : (∫ v : ℝ, F v) = -(∫ v : ℝ, F v) :=
    hmeasure.symm.trans hneg
  exact neg_eq_self.mp hself.symm

/-- The clipped local critical pairing has no odd/even cross term. -/
theorem yoshidaClippedLocalCriticalPairing_odd_even_eq_zero
    {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a)
    (hodd : ∀ x : ℝ, f (-x) = -f x)
    (heven : ∀ x : ℝ, g (-x) = g x) :
    yoshidaClippedLocalCriticalPairing a ha f g = 0 := by
  rw [yoshidaClippedLocalCriticalPairing,
    yoshidaPositivePolar_odd_eq_neg_negative ha f hodd,
    yoshidaPositivePolar_even_eq_negative ha g heven,
    integral_yoshidaClippedCriticalCrossIntegrand_odd_even_eq_zero
      ha f g hodd heven]
  simp

/-- The reversed even/odd cross term also vanishes. -/
theorem yoshidaClippedLocalCriticalPairing_even_odd_eq_zero
    {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hodd : ∀ x : ℝ, g (-x) = -g x) :
    yoshidaClippedLocalCriticalPairing a ha f g = 0 := by
  have hzero := yoshidaClippedLocalCriticalPairing_odd_even_eq_zero
    ha g f hodd heven
  have hconj := yoshidaClippedLocalCriticalPairing_conj ha f g
  rw [hzero] at hconj
  simpa using hconj.symm

theorem yoshidaClippedLocalCriticalForm_odd_even_eq_zero
    {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a)
    (hodd : ∀ x : ℝ, f (-x) = -f x)
    (heven : ∀ x : ℝ, g (-x) = g x) :
    yoshidaClippedLocalCriticalForm a ha f g = 0 := by
  exact yoshidaClippedLocalCriticalPairing_odd_even_eq_zero ha f g hodd heven

theorem yoshidaClippedLocalCriticalForm_even_odd_eq_zero
    {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hodd : ∀ x : ℝ, g (-x) = -g x) :
    yoshidaClippedLocalCriticalForm a ha f g = 0 := by
  exact yoshidaClippedLocalCriticalPairing_even_odd_eq_zero ha f g heven hodd

end

end ArithmeticHodge.Analysis
