import ArithmeticHodge.Analysis.YoshidaEndpointClippedArchBridge
import ArithmeticHodge.Analysis.YoshidaEndpointEvenBoundaryResidual
import ArithmeticHodge.Analysis.YoshidaEndpointZeroTracePolarPhysical

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProduction

open ArithmeticHodge.Analysis
open YoshidaClippedEndpointContinuous
open YoshidaEndpointClippedArchBridge
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPhysicalRealQuadratic
open YoshidaEndpointScaledCorrelation
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

/-- The same production diagonal is the endpoint scale times the generic
clean centered quadratic of the residual profile. -/
theorem clippedCriticalFormValue_evenBoundaryResidual_eq_clean
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
      yoshidaEndpointA * yoshidaEndpointOddCleanQuadratic
        (centeredRescale yoshidaEndpointA g)) := by
  let r : YoshidaClippedPeriodicCore yoshidaEndpointA :=
    evenBoundaryResidual f
  let g : ℝ → ℝ := fun x ↦
    ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re
  change clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
      (r : YoshidaClippedSmooth yoshidaEndpointA) =
    yoshidaEndpointA * yoshidaEndpointOddCleanQuadratic
      (centeredRescale yoshidaEndpointA g)
  have hends :
      ((r : YoshidaClippedSmooth yoshidaEndpointA) (-yoshidaEndpointA) = 0) ∧
      ((r : YoshidaClippedSmooth yoshidaEndpointA) yoshidaEndpointA = 0) := by
    simpa only [r] using
      evenBoundaryResidual_endpoints_zero yoshidaEndpointA_pos f
  have hrcont : Continuous
      ((r : YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero
      yoshidaEndpointA_pos _ hends.1 hends.2
  have hgcont : Continuous g := Complex.continuous_re.comp hrcont
  have hprofile : ContDiffOn ℝ 1 g
      (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    exact Complex.reCLM.contDiff.comp_contDiffOn
      ((r : YoshidaClippedSmooth yoshidaEndpointA).property.1.of_le (by simp))
  have hscale : ContDiffOn ℝ 1
      (fun x : ℝ ↦ yoshidaEndpointA * x) (Icc (-1) 1) := by
    fun_prop
  have hmaps : MapsTo (fun x : ℝ ↦ yoshidaEndpointA * x)
      (Icc (-1) 1) (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    intro x hx
    constructor <;> nlinarith [hx.1, hx.2, yoshidaEndpointA_pos]
  have hlocal : LocallyLipschitzOn (Icc (-1) 1)
      (centeredRescale yoshidaEndpointA g) := by
    have hcomp := hprofile.comp hscale hmaps
    simpa only [centeredRescale, Function.comp_apply] using
      hcomp.locallyLipschitzOn (convex_Icc (-1) 1)
  rw [clippedCriticalFormValue_evenBoundaryResidual_eq_physical f hf_real]
  exact yoshidaEndpointPhysicalRealQuadratic_eq_clean g hgcont hlocal

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProduction
