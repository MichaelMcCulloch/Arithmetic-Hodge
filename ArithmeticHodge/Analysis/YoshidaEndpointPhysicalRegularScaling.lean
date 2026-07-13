import ArithmeticHodge.Analysis.YoshidaEndpointRegularCorrelation
import ArithmeticHodge.Analysis.YoshidaEndpointScaledCorrelation

set_option autoImplicit false

open Complex MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointPhysicalRegularScaling

open YoshidaEndpointHyperbolicBound
open YoshidaEndpointRegularCorrelation
open YoshidaEndpointScaledCorrelation
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

noncomputable section

/-- The regular-kernel quadratic form in centered coordinates is exactly the
weighted physical autocorrelation after dilation to the Yoshida endpoint. -/
theorem two_mul_integral_regularKernel_mul_realEndpointCorrelation_eq
    (f : ℝ → ℝ) (hf : Continuous f) :
    2 * ∫ u : ℝ in 0..2 * yoshidaEndpointA,
        yoshidaRegularKernel u * realEndpointCorrelation yoshidaEndpointA f u =
      yoshidaEndpointA ^ 2 *
        (yoshidaEndpointRegularQuadratic
          (fun x ↦ (centeredRescale yoshidaEndpointA f x : ℂ))).re := by
  have hw : Continuous (centeredRescale yoshidaEndpointA f) := by
    unfold centeredRescale
    fun_prop
  rw [integral_weight_mul_realEndpointCorrelation yoshidaEndpointA_pos f
    yoshidaRegularKernel]
  rw [re_yoshidaEndpointRegularQuadratic_eq_correlation _ hw]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointPhysicalRegularScaling
