import ArithmeticHodge.Analysis.YoshidaEndpointClippedArchBridge
import ArithmeticHodge.Analysis.YoshidaClippedEndpointContinuous
import ArithmeticHodge.Analysis.YoshidaEndpointPhysicalSingularScaling
import ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelationLipschitz

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaGeneralEndpointPhysicalRealQuadraticStructural

noncomputable section

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaEndpointClippedArchBridge
open YoshidaClippedEndpointContinuous
open YoshidaEndpointPolarScaling
open YoshidaEndpointPotentialBound
open YoshidaEndpointPhysicalSingularScaling
open YoshidaEndpointScaledCorrelation
open YoshidaEndpointSingularCorrelationLipschitz
open YoshidaRegularKernelBound
open YoshidaSectionSixAnalytic

/-!
# The clipped physical quadratic at an arbitrary halfwidth

This module keeps the physical halfwidth symbolic.  It exposes the exact
centered real-space diagonal needed by the four-cell profile at
`a = 5 * log 2 / 8`; no positivity claim is inserted into the identity.
-/

/-- A real clipped profile has the expected raw physical polar product at
every positive halfwidth. -/
theorem clippedPolarEnergy_eq_physical_polar_product
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hf_real : ∀ y ∈ Icc (-a) a, f y = ((f y).re : ℂ)) :
    clippedPolarEnergy a ha f =
      2 *
        (∫ y : ℝ in -a..a, Real.exp (-y / 2) * (f y).re) *
        (∫ y : ℝ in -a..a, Real.exp (y / 2) * (f y).re) := by
  have hpos :
      yoshidaPositivePolarLinear a ha f =
        ((∫ y : ℝ in -a..a,
          Real.exp (-y / 2) * (f y).re : ℝ) : ℂ) := by
    rw [yoshidaPositivePolarLinear, yoshidaCenteredLaplaceLinear_apply,
      ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Icc (-a) a := by
      simpa only [uIcc_of_le (by linarith : -a ≤ a)] using hy
    change Complex.exp (-((1 / 2 : ℂ) * (y : ℂ))) * f y =
      ((Real.exp (-y / 2) * (f y).re : ℝ) : ℂ)
    rw [hf_real y hyIcc]
    rw [show -((1 / 2 : ℂ) * (y : ℂ)) = ((-y / 2 : ℝ) : ℂ) by
      push_cast
      ring,
      ← Complex.ofReal_exp]
    push_cast
    rfl
  have hneg :
      yoshidaNegativePolarLinear a ha f =
        ((∫ y : ℝ in -a..a,
          Real.exp (y / 2) * (f y).re : ℝ) : ℂ) := by
    rw [yoshidaNegativePolarLinear, yoshidaCenteredLaplaceLinear_apply,
      ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Icc (-a) a := by
      simpa only [uIcc_of_le (by linarith : -a ≤ a)] using hy
    change Complex.exp (-((-1 / 2 : ℂ) * (y : ℂ))) * f y =
      ((Real.exp (y / 2) * (f y).re : ℝ) : ℂ)
    rw [hf_real y hyIcc]
    rw [show -((-1 / 2 : ℂ) * (y : ℂ)) = ((y / 2 : ℝ) : ℂ) by
      push_cast
      ring,
      ← Complex.ofReal_exp]
    push_cast
    rfl
  unfold clippedPolarEnergy
  rw [hpos, hneg]
  simp [RCLike.star_def]
  ring

/-- The normalized real-space diagonal at halfwidth `a`.  The singular
correlation supplies the raw logarithmic energy and endpoint potential; the
remaining terms are the exact regular-kernel, scalar, and polar pieces. -/
def centeredClippedPhysicalQuadratic (a : ℝ) (w : ℝ → ℝ) : ℝ :=
  centeredRawLogEnergy w / 4 +
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) -
    (Real.log (2 * a) + Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in -1..1, w x ^ 2) -
    2 * a * (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (a * t) * centeredEndpointCorrelation w t) +
    2 * a *
      (∫ x : ℝ in -1..1, Real.exp (-a * x / 2) * w x) *
      (∫ x : ℝ in -1..1, Real.exp (a * x / 2) * w x)

/-- Exact physical-to-centered identity for the complete archimedean and
polar real-space expression at every positive halfwidth. -/
theorem clippedArchCorrelation_add_polar_eq_centered
    {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) (hg : Continuous g)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) (centeredRescale a g))
    (hdefect : IntervalIntegrable (fun u ↦
      (realEndpointCorrelation a g 0 - realEndpointCorrelation a g u) / u)
      volume 0 (2 * a))
    (hregularInt : IntervalIntegrable (fun u ↦
      yoshidaRegularKernel u * realEndpointCorrelation a g u)
      volume 0 (2 * a)) :
    clippedArchCorrelation a g +
        2 *
          (∫ y : ℝ in -a..a, Real.exp (-y / 2) * g y) *
          (∫ y : ℝ in -a..a, Real.exp (y / 2) * g y) =
      a * centeredClippedPhysicalQuadratic a (centeredRescale a g) := by
  let w : ℝ → ℝ := centeredRescale a g
  have hw : Continuous w := by
    exact hg.comp (continuous_const.mul continuous_id)
  have hsing := integral_realEndpointCorrelation_defect_div ha g
  have hsingCentered :=
    integral_correlation_defect_div_eq_centered_energy_add_potential_of_locallyLipschitzOn
      w hw hlocal
  rw [hsingCentered] at hsing
  have hregularScale := integral_weight_mul_realEndpointCorrelation
    ha g yoshidaRegularKernel
  have hmass : realEndpointCorrelation a g 0 =
      a * ∫ x : ℝ in -1..1, w x ^ 2 := by
    have hzero := realEndpointCorrelation_mul ha g 0
    simp only [mul_zero] at hzero
    rw [hzero, centeredEndpointCorrelation_zero]
  have hback (y : ℝ) : w (y / a) = g y := by
    dsimp only [w, centeredRescale]
    rw [mul_div_cancel₀ y ha.ne']
  have hneg :
      (∫ y : ℝ in -a..a, Real.exp (-y / 2) * g y) =
        a * ∫ x : ℝ in -1..1, Real.exp (-a * x / 2) * w x := by
    calc
      (∫ y : ℝ in -a..a, Real.exp (-y / 2) * g y) =
          ∫ y : ℝ in -a..a,
            Real.exp ((-1 / 2 : ℝ) * y) * w (y / a) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        change Real.exp (-y / 2) * g y =
          Real.exp ((-1 / 2 : ℝ) * y) * w (y / a)
        rw [hback]
        congr 2
        ring
      _ = a * ∫ x : ℝ in -1..1,
          Real.exp ((-1 / 2 : ℝ) * (a * x)) * w x :=
        integral_exp_mul_rescale ha.ne' w
      _ = a * ∫ x : ℝ in -1..1,
          Real.exp (-a * x / 2) * w x := by
        apply congrArg (fun z : ℝ ↦ a * z)
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
  have hpos :
      (∫ y : ℝ in -a..a, Real.exp (y / 2) * g y) =
        a * ∫ x : ℝ in -1..1, Real.exp (a * x / 2) * w x := by
    calc
      (∫ y : ℝ in -a..a, Real.exp (y / 2) * g y) =
          ∫ y : ℝ in -a..a,
            Real.exp ((1 / 2 : ℝ) * y) * w (y / a) := by
        apply intervalIntegral.integral_congr
        intro y _hy
        change Real.exp (y / 2) * g y =
          Real.exp ((1 / 2 : ℝ) * y) * w (y / a)
        rw [hback]
        congr 2
        ring
      _ = a * ∫ x : ℝ in -1..1,
          Real.exp ((1 / 2 : ℝ) * (a * x)) * w x :=
        integral_exp_mul_rescale ha.ne' w
      _ = a * ∫ x : ℝ in -1..1,
          Real.exp (a * x / 2) * w x := by
        apply congrArg (fun z : ℝ ↦ a * z)
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
  have htwice : IntervalIntegrable (fun u ↦
      2 * yoshidaRegularKernel u * realEndpointCorrelation a g u)
      volume 0 (2 * a) := by
    apply (hregularInt.const_mul 2).congr
    intro u _hu
    ring
  have hsplit :
      (∫ u : ℝ in 0..2 * a,
        (realEndpointCorrelation a g 0 - realEndpointCorrelation a g u) / u -
          2 * yoshidaRegularKernel u * realEndpointCorrelation a g u) =
      (∫ u : ℝ in 0..2 * a,
        (realEndpointCorrelation a g 0 - realEndpointCorrelation a g u) / u) -
        2 * (∫ u : ℝ in 0..2 * a,
          yoshidaRegularKernel u * realEndpointCorrelation a g u) := by
    rw [intervalIntegral.integral_sub hdefect htwice]
    rw [show (fun u : ℝ ↦
        2 * yoshidaRegularKernel u * realEndpointCorrelation a g u) =
      fun u ↦ 2 * (yoshidaRegularKernel u * realEndpointCorrelation a g u) by
        funext u
        ring,
      intervalIntegral.integral_const_mul]
  unfold clippedArchCorrelation centeredClippedPhysicalQuadratic
  dsimp only
  rw [hsplit, hsing, hregularScale, hmass, hneg, hpos]
  ring

/-- For a real clipped production profile with zero endpoint traces, the
complete critical form is exactly its normalized physical quadratic. -/
theorem clippedCriticalFormValue_eq_centeredClippedPhysicalQuadratic_of_endpoints_zero
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hf_real : ∀ x ∈ Icc (-a) a, f x = ((f x).re : ℂ))
    (hneg : f (-a) = 0) (hpos : f a = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1)
      (centeredRescale a (fun x ↦ (f x).re))) :
    clippedCriticalFormValue a ha f =
      a * centeredClippedPhysicalQuadratic a
        (centeredRescale a (fun x ↦ (f x).re)) := by
  let g : ℝ → ℝ := fun x ↦ (f x).re
  have hfcont : Continuous (f : ℝ → ℂ) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero ha f hneg hpos
  have hg : Continuous g := Complex.continuous_re.comp hfcont
  obtain ⟨hdefect, hregular⟩ :=
    clippedArchCorrelation_terms_intervalIntegrable_of_endpoints_zero
      ha f hf_real hneg hpos
  have harch :=
    clippedArchEnergy_eq_clippedArchCorrelation_of_endpoints_zero
      ha f hf_real hneg hpos
  have hpolar := clippedPolarEnergy_eq_physical_polar_product ha f hf_real
  have hphysical := clippedArchCorrelation_add_polar_eq_centered
    ha g hg hlocal hdefect hregular
  rw [clippedCriticalFormValue_eq_polar_add_arch ha f, hpolar, harch]
  dsimp only [g] at hphysical ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaGeneralEndpointPhysicalRealQuadraticStructural
