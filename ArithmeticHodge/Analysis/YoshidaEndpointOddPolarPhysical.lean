import ArithmeticHodge.Analysis.YoshidaEndpointClippedPolarBridge
import ArithmeticHodge.Analysis.YoshidaPointwiseOddRealImag

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddPolarPhysical

open YoshidaEndpointClippedPolarBridge
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPolarScaling
open YoshidaPointwiseOddPeriodicCore
open YoshidaPointwiseOddRealImag
open YoshidaSectionSixAnalytic

noncomputable section

/-- On a real-valued structural odd periodic profile, the production polar
energy is the raw physical-coordinate polar product. -/
theorem clippedPolarEnergy_eq_physical_polar_product
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0) :
    clippedPolarEnergy yoshidaEndpointA yoshidaEndpointA_pos
        (f.1 : YoshidaClippedSmooth yoshidaEndpointA) =
      2 *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * pointwiseOddPeriodicCoreRealProfile f y) *
        (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * pointwiseOddPeriodicCoreRealProfile f y) := by
  let g : ℝ → ℝ := pointwiseOddPeriodicCoreRealProfile f
  let w : ℝ → ℝ := fun x ↦ g (yoshidaEndpointA * x)
  have hg : Continuous g :=
    continuous_pointwiseOddPeriodicCoreRealProfile yoshidaEndpointA_pos f
  have hw : Continuous w := hg.comp (continuous_const.mul continuous_id)
  have hreal : ∀ y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      ((f.1 : YoshidaClippedSmooth yoshidaEndpointA) y) =
        ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
          YoshidaClippedSmooth yoshidaEndpointA) y).re : ℂ) := by
    intro y _hy
    apply Complex.ext
    · rfl
    · simpa using hf_real y
  have hclipped := clippedPolarEnergy_eq_endpointHyperbolicQuadratic
    (f.1 : YoshidaClippedSmooth yoshidaEndpointA) hreal
  have hscaled :=
    two_mul_rescaledPolarMoments_eq_endpointHyperbolicQuadratic w hw
  have hback (y : ℝ) : w (y / yoshidaEndpointA) = g y := by
    dsimp only [w]
    rw [mul_div_cancel₀ y yoshidaEndpointA_pos.ne']
  simp_rw [hback] at hscaled
  calc
    clippedPolarEnergy yoshidaEndpointA yoshidaEndpointA_pos
        (f.1 : YoshidaClippedSmooth yoshidaEndpointA) =
        yoshidaEndpointA *
          yoshidaEndpointHyperbolicQuadratic
            (fun x ↦ (((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
              YoshidaClippedSmooth yoshidaEndpointA)
                (yoshidaEndpointA * x)).re) := hclipped
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

end ArithmeticHodge.Analysis.YoshidaEndpointOddPolarPhysical
