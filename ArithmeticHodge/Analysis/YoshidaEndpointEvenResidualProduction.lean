import ArithmeticHodge.Analysis.YoshidaEndpointClippedArchBridge
import ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryResidual
import ArithmeticHodge.Analysis.YoshidaEndpointZeroTracePolarPhysical

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProduction

open ArithmeticHodge.Analysis
open YoshidaEndpointClippedArchBridge
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPhysicalRealQuadratic
open YoshidaEndpointZeroTracePolarPhysical
open YoshidaPointwiseParityCore
open YoshidaSectionSixAnalytic

noncomputable section

/-- The actual production diagonal of the zero-trace residual of a real even
periodic source is exactly its physical endpoint quadratic. -/
theorem clippedCriticalFormValue_evenBoundaryResidual_eq_physical
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0) :
    (let r : YoshidaClippedPeriodicCore yoshidaEndpointA :=
      evenBoundaryResidual f
    let g : ℝ → ℝ := fun x ↦
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re
    clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
        (r : YoshidaClippedSmooth yoshidaEndpointA) =
      yoshidaEndpointPhysicalRealQuadratic g) := by
  let r : YoshidaClippedPeriodicCore yoshidaEndpointA :=
    evenBoundaryResidual f
  let g : ℝ → ℝ := fun x ↦
    ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re
  change clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
      (r : YoshidaClippedSmooth yoshidaEndpointA) =
    yoshidaEndpointPhysicalRealQuadratic g
  have hends :
      ((r : YoshidaClippedSmooth yoshidaEndpointA) (-yoshidaEndpointA) = 0) ∧
      ((r : YoshidaClippedSmooth yoshidaEndpointA) yoshidaEndpointA = 0) := by
    simpa only [r] using
      evenBoundaryResidual_endpoints_zero yoshidaEndpointA_pos f
  have hreal (x : ℝ) :
      ((r : YoshidaClippedSmooth yoshidaEndpointA) x).im = 0 := by
    simpa only [r] using evenBoundaryResidual_im_zero f hf_real x
  have hpolar :=
    clippedPolarEnergy_eq_physical_polar_product_of_endpoints_zero
      r hreal hends.1 hends.2
  have hbridge :=
    clippedArchEnergy_add_polar_eq_physicalRealQuadratic_of_endpoints_zero
      r (fun x _hx ↦ hreal x) hends.1 hends.2
  rw [clippedCriticalFormValue_eq_polar_add_arch, hpolar]
  dsimp only at hbridge ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProduction
