import ArithmeticHodge.Analysis.YoshidaClippedRealImagEnergySplit
import ArithmeticHodge.Analysis.YoshidaEndpointClippedArchBridge
import ArithmeticHodge.Analysis.YoshidaEndpointOddPhysicalPositive
import ArithmeticHodge.Analysis.YoshidaEndpointOddPolarPhysical

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddProductionPositive

open ArithmeticHodge.Analysis
open YoshidaClippedRealImag
open YoshidaClippedRealImagEnergySplit
open YoshidaEndpointClippedArchBridge
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddPhysicalPositive
open YoshidaEndpointOddPolarPhysical
open YoshidaEndpointPhysicalRealQuadratic
open YoshidaPointwiseOddPeriodicCore
open YoshidaPointwiseOddRealImag
open YoshidaSectionSixAnalytic

noncomputable section

/-- On a real-valued structural odd source profile, the actual production
diagonal is exactly the physical endpoint quadratic. -/
theorem yoshidaClippedLocalCriticalForm_re_eq_physicalRealQuadratic
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0) :
    (yoshidaClippedLocalCriticalForm yoshidaEndpointA yoshidaEndpointA_pos
      (f.1 : YoshidaClippedSmooth yoshidaEndpointA)
      (f.1 : YoshidaClippedSmooth yoshidaEndpointA)).re =
      yoshidaEndpointPhysicalRealQuadratic
        (pointwiseOddPeriodicCoreRealProfile f) := by
  let fs : YoshidaClippedSmooth yoshidaEndpointA :=
    (f.1 : YoshidaClippedSmooth yoshidaEndpointA)
  have hdecomp := clippedCriticalFormValue_eq_polar_add_arch
    yoshidaEndpointA_pos fs
  have hpolar := clippedPolarEnergy_eq_physical_polar_product f hf_real
  have hbridge := clippedArchEnergy_add_polar_eq_physicalRealQuadratic
    f.1 (fun x _hx ↦ hf_real x) f.property
  unfold clippedCriticalFormValue at hdecomp
  dsimp only at hbridge
  have hbridge' :
      clippedArchEnergy yoshidaEndpointA yoshidaEndpointA_pos fs +
        2 *
          (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
            Real.exp (-y / 2) * pointwiseOddPeriodicCoreRealProfile f y) *
          (∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
            Real.exp (y / 2) * pointwiseOddPeriodicCoreRealProfile f y) =
        yoshidaEndpointPhysicalRealQuadratic
          (pointwiseOddPeriodicCoreRealProfile f) := by
    simpa only [fs, pointwiseOddPeriodicCoreRealProfile] using hbridge
  change (yoshidaClippedLocalCriticalForm yoshidaEndpointA
      yoshidaEndpointA_pos fs fs).re = _
  rw [hdecomp, hpolar]
  linarith

/-- The actual complex odd production diagonal is exactly the sum of the two
physical real endpoint quadratics. -/
theorem yoshidaClippedLocalCriticalForm_re_eq_real_add_imag_physical
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA) :
    (yoshidaClippedLocalCriticalForm yoshidaEndpointA yoshidaEndpointA_pos
      (f.1 : YoshidaClippedSmooth yoshidaEndpointA)
      (f.1 : YoshidaClippedSmooth yoshidaEndpointA)).re =
      yoshidaEndpointPhysicalRealQuadratic
          (pointwiseOddPeriodicCoreRealProfile f) +
        yoshidaEndpointPhysicalRealQuadratic
          (pointwiseOddPeriodicCoreImagProfile f) := by
  let fr := pointwiseOddPeriodicCoreRealPart f
  let fi := pointwiseOddPeriodicCoreImagPart f
  have hr := yoshidaClippedLocalCriticalForm_re_eq_physicalRealQuadratic
    fr (by
      intro x
      dsimp only [fr]
      exact pointwiseOddPeriodicCoreRealPart_im_zero f)
  have hi := yoshidaClippedLocalCriticalForm_re_eq_physicalRealQuadratic
    fi (by
      intro x
      dsimp only [fi]
      exact pointwiseOddPeriodicCoreImagPart_im_zero f)
  have hr' :
      (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos
        (clippedRealPart (f.1 : YoshidaClippedSmooth yoshidaEndpointA))
        (clippedRealPart (f.1 : YoshidaClippedSmooth yoshidaEndpointA))).re =
      yoshidaEndpointPhysicalRealQuadratic
        (pointwiseOddPeriodicCoreRealProfile f) := by
    simpa only [fr, pointwiseOddPeriodicCoreRealPart,
      periodicCoreRealPart, pointwiseOddPeriodicCoreRealProfile] using hr
  have hi' :
      (yoshidaClippedLocalCriticalForm yoshidaEndpointA
        yoshidaEndpointA_pos
        (clippedImagPart (f.1 : YoshidaClippedSmooth yoshidaEndpointA))
        (clippedImagPart (f.1 : YoshidaClippedSmooth yoshidaEndpointA))).re =
      yoshidaEndpointPhysicalRealQuadratic
        (pointwiseOddPeriodicCoreImagProfile f) := by
    simpa only [fi, pointwiseOddPeriodicCoreImagPart,
      periodicCoreImagPart, pointwiseOddPeriodicCoreRealProfile,
      pointwiseOddPeriodicCoreImagProfile] using hi
  rw [yoshidaClippedLocalCriticalForm_real_add_imag_re
    yoshidaEndpointA_pos (f.1 : YoshidaClippedSmooth yoshidaEndpointA),
    hr', hi']

/-- Structural nonnegativity of the actual production clipped form on every
pointwise-odd periodic source vector. -/
theorem yoshidaClippedLocalCriticalForm_re_nonneg
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule yoshidaEndpointA) :
    0 ≤ (yoshidaClippedLocalCriticalForm yoshidaEndpointA
      yoshidaEndpointA_pos
      (f.1 : YoshidaClippedSmooth yoshidaEndpointA)
      (f.1 : YoshidaClippedSmooth yoshidaEndpointA)).re := by
  rw [yoshidaClippedLocalCriticalForm_re_eq_real_add_imag_physical f]
  exact add_nonneg
    (yoshidaEndpointPhysicalRealQuadratic_realProfile_nonneg f)
    (yoshidaEndpointPhysicalRealQuadratic_imagProfile_nonneg f)

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddProductionPositive
