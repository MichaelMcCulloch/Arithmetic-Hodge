import ArithmeticHodge.Analysis.YoshidaClippedRealImag
import ArithmeticHodge.Analysis.YoshidaClippedParityOrthogonality

set_option autoImplicit false

open Complex MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaClippedRealImagEnergySplit

open ArithmeticHodge.Analysis
open YoshidaClippedRealImag

noncomputable section

private theorem yoshidaCenteredLaplace_eq_star_of_pointwise_star_fixed
    {a : ℝ} (ha : 0 < a) (z : ℂ) (u : YoshidaClippedSmooth a)
    (hu : ∀ x : ℝ, star (u x) = u x) :
    yoshidaCenteredLaplaceLinear a ha z u =
      star (yoshidaCenteredLaplaceLinear a ha (star z) u) := by
  rw [yoshidaCenteredLaplaceLinear_apply,
    yoshidaCenteredLaplaceLinear_apply]
  have hint : IntervalIntegrable
      (fun x : ℝ ↦ Complex.exp (-(star z * (x : ℂ))) * u x)
      volume (-a) a := by
    have hw : Continuous (fun x : ℝ ↦
        Complex.exp (-(star z * (x : ℂ)))) := by
      fun_prop
    exact (hw.continuousOn.mul u.property.1.continuousOn)
      |>.intervalIntegrable_of_Icc (by linarith)
  change (∫ x : ℝ in -a..a,
      Complex.exp (-(z * (x : ℂ))) * u x) =
    Complex.conjCLE (∫ x : ℝ in -a..a,
      Complex.exp (-(star z * (x : ℂ))) * u x)
  calc
    (∫ x : ℝ in -a..a,
        Complex.exp (-(z * (x : ℂ))) * u x) =
        ∫ x : ℝ in -a..a,
          Complex.conjCLE
            (Complex.exp (-(star z * (x : ℂ))) * u x) := by
      apply intervalIntegral.integral_congr
      intro x _
      change Complex.exp (-(z * (x : ℂ))) * u x =
        Complex.conjCLE
          (Complex.exp (-(star z * (x : ℂ))) * u x)
      rw [Complex.conjCLE_apply, map_mul, ← Complex.exp_conj]
      simp only [map_neg, map_mul, starRingEnd_apply, star_star,
        hu]
      rw [show star (x : ℂ) = (x : ℂ) by simp]
    _ = Complex.conjCLE (∫ x : ℝ in -a..a,
        Complex.exp (-(star z * (x : ℂ))) * u x) :=
      Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint

private theorem yoshidaPositivePolar_star_fixed_of_pointwise_star_fixed
    {a : ℝ} (ha : 0 < a) (u : YoshidaClippedSmooth a)
    (hu : ∀ x : ℝ, star (u x) = u x) :
    star (yoshidaPositivePolarLinear a ha u) =
      yoshidaPositivePolarLinear a ha u := by
  unfold yoshidaPositivePolarLinear
  have h := yoshidaCenteredLaplace_eq_star_of_pointwise_star_fixed
    ha (1 / 2 : ℂ) u hu
  simpa using h.symm

private theorem yoshidaNegativePolar_star_fixed_of_pointwise_star_fixed
    {a : ℝ} (ha : 0 < a) (u : YoshidaClippedSmooth a)
    (hu : ∀ x : ℝ, star (u x) = u x) :
    star (yoshidaNegativePolarLinear a ha u) =
      yoshidaNegativePolarLinear a ha u := by
  unfold yoshidaNegativePolarLinear
  have h := yoshidaCenteredLaplace_eq_star_of_pointwise_star_fixed
    ha (-1 / 2 : ℂ) u hu
  simpa using h.symm

private theorem yoshidaCriticalSample_neg_eq_star_of_pointwise_star_fixed
    {a : ℝ} (ha : 0 < a) (u : YoshidaClippedSmooth a)
    (hu : ∀ x : ℝ, star (u x) = u x) (v : ℝ) :
    yoshidaCriticalSampleLinear a ha (-v) u =
      star (yoshidaCriticalSampleLinear a ha v u) := by
  unfold yoshidaCriticalSampleLinear
  have h := yoshidaCenteredLaplace_eq_star_of_pointwise_star_fixed
    ha (((-v : ℝ) : ℂ) * Complex.I) u hu
  convert h using 1
  all_goals simp [star_mul]
  rw [mul_comm (v : ℂ) Complex.I]

private theorem integral_cross_star_fixed_of_pointwise_star_fixed
    {a : ℝ} (ha : 0 < a) (u v : YoshidaClippedSmooth a)
    (hu : ∀ x : ℝ, star (u x) = u x)
    (hv : ∀ x : ℝ, star (v x) = v x) :
    star (∫ t : ℝ,
      yoshidaClippedCriticalCrossIntegrand a ha u v t) =
      ∫ t : ℝ,
        yoshidaClippedCriticalCrossIntegrand a ha u v t := by
  let F : ℝ → ℂ := yoshidaClippedCriticalCrossIntegrand a ha u v
  have hneg : ∀ t : ℝ, F (-t) = star (F t) := by
    intro t
    dsimp only [F]
    rw [yoshidaClippedCriticalCrossIntegrand,
      yoshidaClippedCriticalCrossIntegrand,
      bombieriLocalCriticalKernel_neg,
      yoshidaCriticalSample_neg_eq_star_of_pointwise_star_fixed ha u hu,
      yoshidaCriticalSample_neg_eq_star_of_pointwise_star_fixed ha v hv]
    simp only [star_mul, star_star, star_bombieriLocalCriticalKernel]
    ring
  have hmeasure : (∫ t : ℝ, F (-t)) = ∫ t : ℝ, F t :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (MeasurableEquiv.neg ℝ).measurableEmbedding F
  have hstar : (∫ t : ℝ, F (-t)) =
      star (∫ t : ℝ, F t) := by
    calc
      (∫ t : ℝ, F (-t)) = ∫ t : ℝ, star (F t) := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hneg t
      _ = star (∫ t : ℝ, F t) := integral_conj (f := F)
  exact hstar.symm.trans hmeasure

private theorem yoshidaClippedLocalCriticalForm_cross_star_fixed
    {a : ℝ} (ha : 0 < a) (u v : YoshidaClippedSmooth a)
    (hu : ∀ x : ℝ, star (u x) = u x)
    (hv : ∀ x : ℝ, star (v x) = v x) :
    star (yoshidaClippedLocalCriticalForm a ha u v) =
      yoshidaClippedLocalCriticalForm a ha u v := by
  rw [yoshidaClippedLocalCriticalForm_apply]
  simp only [yoshidaClippedLocalCriticalPairing, star_add, star_mul,
    yoshidaPositivePolar_star_fixed_of_pointwise_star_fixed ha u hu,
    yoshidaNegativePolar_star_fixed_of_pointwise_star_fixed ha u hu,
    yoshidaPositivePolar_star_fixed_of_pointwise_star_fixed ha v hv,
    yoshidaNegativePolar_star_fixed_of_pointwise_star_fixed ha v hv,
    integral_cross_star_fixed_of_pointwise_star_fixed ha u v hu hv]
  simp
  ring

/-- The real diagonal of the production form splits into its pointwise real
and imaginary components. -/
theorem yoshidaClippedLocalCriticalForm_real_add_imag_re
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    (yoshidaClippedLocalCriticalForm a ha f f).re =
      (yoshidaClippedLocalCriticalForm a ha
        (clippedRealPart f) (clippedRealPart f)).re +
      (yoshidaClippedLocalCriticalForm a ha
        (clippedImagPart f) (clippedImagPart f)).re := by
  let u : YoshidaClippedSmooth a := clippedRealPart f
  let v : YoshidaClippedSmooth a := clippedImagPart f
  have hu : ∀ x : ℝ, star (u x) = u x := by
    intro x
    simp [u]
  have hv : ∀ x : ℝ, star (v x) = v x := by
    intro x
    simp [v]
  have hcross : star (yoshidaClippedLocalCriticalForm a ha u v) =
      yoshidaClippedLocalCriticalForm a ha u v :=
    yoshidaClippedLocalCriticalForm_cross_star_fixed ha u v hu hv
  have hswap : yoshidaClippedLocalCriticalForm a ha u v =
      yoshidaClippedLocalCriticalForm a ha v u := by
    have hherm := yoshidaClippedLocalCriticalForm_conj_apply ha v u
    rw [hcross] at hherm
    exact hherm
  have hIleft (w : YoshidaClippedSmooth a) :
      yoshidaClippedLocalCriticalForm a ha (Complex.I • v) w =
        -Complex.I * yoshidaClippedLocalCriticalForm a ha v w := by
    calc
      yoshidaClippedLocalCriticalForm a ha (Complex.I • v) w =
          star Complex.I * yoshidaClippedLocalCriticalForm a ha v w := by
        simpa only [smul_eq_mul] using
          (LinearMap.map_smulₛₗ₂ (yoshidaClippedLocalCriticalForm a ha)
            Complex.I v w)
      _ = -Complex.I * yoshidaClippedLocalCriticalForm a ha v w := by
        rw [Complex.star_def, Complex.conj_I]
  have hrec : u + Complex.I • v = f := by
    simpa only [u, v] using clippedRealPart_add_I_smul_imagPart f
  change (yoshidaClippedLocalCriticalForm a ha f f).re =
    (yoshidaClippedLocalCriticalForm a ha u u).re +
      (yoshidaClippedLocalCriticalForm a ha v v).re
  rw [← hrec]
  simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul]
  rw [hIleft u, hIleft v]
  rw [hswap]
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  rw [Complex.add_re]

end

end ArithmeticHodge.Analysis.YoshidaClippedRealImagEnergySplit
