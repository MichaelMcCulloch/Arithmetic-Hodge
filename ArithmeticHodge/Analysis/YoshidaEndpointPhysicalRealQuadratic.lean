import ArithmeticHodge.Analysis.YoshidaEndpointCleanQuadratic
import ArithmeticHodge.Analysis.YoshidaEndpointPhysicalRegularScaling
import ArithmeticHodge.Analysis.YoshidaEndpointPhysicalSingularIdentity
import ArithmeticHodge.Analysis.YoshidaEndpointPolarScaling
import ArithmeticHodge.Analysis.YoshidaEndpointScalarCancellation

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPhysicalRealQuadratic

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPhysicalRegularScaling
open YoshidaEndpointPhysicalSingularIdentity
open YoshidaEndpointPolarScaling
open YoshidaEndpointPotentialBound
open YoshidaEndpointScalarCancellation
open YoshidaEndpointScaledCorrelation
open YoshidaRegularKernelBound

noncomputable section

/-- The real physical-coordinate endpoint expression obtained from the
renormalized correlation formula before centering. -/
def yoshidaEndpointPhysicalRealQuadratic (f : ℝ → ℝ) : ℝ :=
  (∫ u : ℝ in 0..2 * yoshidaEndpointA,
    (realEndpointCorrelation yoshidaEndpointA f 0 -
      realEndpointCorrelation yoshidaEndpointA f u) / u) -
  2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
    yoshidaRegularKernel u * realEndpointCorrelation yoshidaEndpointA f u) -
  (Real.log (2 * yoshidaEndpointA) + Real.eulerMascheroniConstant +
      Real.log 2 + Real.log Real.pi) *
    realEndpointCorrelation yoshidaEndpointA f 0 +
  2 *
    (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
      Real.exp (-y / 2) * f y) *
    (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
      Real.exp (y / 2) * f y)

/-- The physical real-space endpoint expression is exactly `a` times the
clean centered quadratic. -/
theorem yoshidaEndpointPhysicalRealQuadratic_eq_clean
    (f : ℝ → ℝ) (hf : Continuous f)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1)
      (centeredRescale yoshidaEndpointA f)) :
    yoshidaEndpointPhysicalRealQuadratic f =
      yoshidaEndpointA * yoshidaEndpointOddCleanQuadratic
        (centeredRescale yoshidaEndpointA f) := by
  let w : ℝ → ℝ := centeredRescale yoshidaEndpointA f
  have hw : Continuous w := by
    change Continuous (fun x : ℝ ↦ f (yoshidaEndpointA * x))
    exact hf.comp (continuous_const.mul continuous_id)
  have hsing := integral_physical_correlation_defect_div_eq_clean_singular
    f hf hlocal
  have hregular :=
    two_mul_integral_regularKernel_mul_realEndpointCorrelation_eq f hf
  have hmass : realEndpointCorrelation yoshidaEndpointA f 0 =
      yoshidaEndpointA * ∫ x : ℝ in -1..1, w x ^ 2 := by
    have hzero := realEndpointCorrelation_mul yoshidaEndpointA_pos f 0
    simp only [mul_zero] at hzero
    rw [hzero, centeredEndpointCorrelation_zero]
  have hback (y : ℝ) : w (y / yoshidaEndpointA) = f y := by
    dsimp only [w, centeredRescale]
    rw [mul_div_cancel₀ y yoshidaEndpointA_pos.ne']
  have hneg :
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (-y / 2) * f y) =
      ∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (-y / 2) * w (y / yoshidaEndpointA) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    change Real.exp (-y / 2) * f y =
      Real.exp (-y / 2) * w (y / yoshidaEndpointA)
    rw [hback]
  have hpos :
      (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (y / 2) * f y) =
      ∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
        Real.exp (y / 2) * w (y / yoshidaEndpointA) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    change Real.exp (y / 2) * f y =
      Real.exp (y / 2) * w (y / yoshidaEndpointA)
    rw [hback]
  have hpolar :
      2 *
          (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
            Real.exp (-y / 2) * f y) *
          (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
            Real.exp (y / 2) * f y) =
        yoshidaEndpointA * yoshidaEndpointHyperbolicQuadratic
          (fun x ↦ (w x : ℂ)) := by
    rw [hneg, hpos]
    exact two_mul_rescaledPolarMoments_eq_endpointHyperbolicQuadratic w hw
  have htwoA : 2 * yoshidaEndpointA = Real.log 2 := by
    unfold yoshidaEndpointA
    ring
  have hscalar := endpoint_scalar_cancellation
  unfold yoshidaEndpointPhysicalRealQuadratic
  rw [hsing, hregular, hmass, hpolar, htwoA]
  dsimp only [w] at hscalar ⊢
  unfold yoshidaEndpointOddCleanQuadratic
  dsimp only
  unfold yoshidaEndpointScalarMassLoss
  unfold yoshidaEndpointScalarMassLoss at hscalar
  linear_combination yoshidaEndpointA *
    (∫ x : ℝ in -1..1, centeredRescale yoshidaEndpointA f x ^ 2) * hscalar

end

end ArithmeticHodge.Analysis.YoshidaEndpointPhysicalRealQuadratic
