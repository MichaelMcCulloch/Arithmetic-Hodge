import ArithmeticHodge.Analysis.YoshidaClippedEndpointContinuous
import ArithmeticHodge.Analysis.YoshidaClippedPeriodicCore
import ArithmeticHodge.Analysis.YoshidaEndpointClippedPolarBridge

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointZeroTracePolarPhysical

open ArithmeticHodge.Analysis
open YoshidaClippedEndpointContinuous
open YoshidaEndpointClippedPolarBridge
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPolarScaling
open YoshidaSectionSixAnalytic

noncomputable section

/-- On a real periodic profile with zero endpoint traces, the production
polar energy is its raw physical-coordinate polar product. -/
theorem clippedPolarEnergy_eq_physical_polar_product_of_endpoints_zero
    (f : YoshidaClippedPeriodicCore yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0)
    (hneg : (f : YoshidaClippedSmooth yoshidaEndpointA)
      (-yoshidaEndpointA) = 0)
    (hpos : (f : YoshidaClippedSmooth yoshidaEndpointA)
      yoshidaEndpointA = 0) :
    (let g : ℝ → ℝ := fun x ↦
      ((f : YoshidaClippedSmooth yoshidaEndpointA) x).re
    clippedPolarEnergy yoshidaEndpointA yoshidaEndpointA_pos
        (f : YoshidaClippedSmooth yoshidaEndpointA) =
      2 *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * g y) *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * g y)) := by
  let fs : YoshidaClippedSmooth yoshidaEndpointA := f
  let g : ℝ → ℝ := fun x ↦ (fs x).re
  let w : ℝ → ℝ := fun x ↦ g (yoshidaEndpointA * x)
  have hfs : Continuous (fs : ℝ → ℂ) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero
      yoshidaEndpointA_pos fs hneg hpos
  have hg : Continuous g := Complex.continuous_re.comp hfs
  have hw : Continuous w := hg.comp (continuous_const.mul continuous_id)
  have hreal : ∀ y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      fs y = ((fs y).re : ℂ) := by
    intro y _hy
    apply Complex.ext
    · rfl
    · simpa [fs] using hf_real y
  have hclipped := clippedPolarEnergy_eq_endpointHyperbolicQuadratic fs hreal
  have hscaled :=
    two_mul_rescaledPolarMoments_eq_endpointHyperbolicQuadratic w hw
  have hback (y : ℝ) : w (y / yoshidaEndpointA) = g y := by
    dsimp only [w]
    rw [mul_div_cancel₀ y yoshidaEndpointA_pos.ne']
  simp_rw [hback] at hscaled
  calc
    clippedPolarEnergy yoshidaEndpointA yoshidaEndpointA_pos fs =
        yoshidaEndpointA *
          yoshidaEndpointHyperbolicQuadratic
            (fun x ↦ ((fs (yoshidaEndpointA * x)).re : ℂ)) := hclipped
    _ = yoshidaEndpointA *
          yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) := by
      rfl
    _ = 2 *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * g y) *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * g y) := hscaled.symm
    _ = _ := rfl

end

end ArithmeticHodge.Analysis.YoshidaEndpointZeroTracePolarPhysical
