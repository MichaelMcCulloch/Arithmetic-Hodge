import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousTailStructural

set_option autoImplicit false

open scoped ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousCleanPolarizationStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointEvenBoundaryProductionBridge
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaPointwiseParityCore
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Clean polarization for boundary-continuous even representatives

The full even production diagonal already equals the endpoint clean quadratic
of its boundary-continuous representative.  Applying that diagonal identity
to two profiles and their sum, then polarizing the Hermitian clipped critical
form, identifies the corresponding clean cross term exactly.
-/

private theorem clippedCriticalFormValue_add
    (r s : YoshidaClippedSmooth yoshidaA) :
    clippedCriticalFormValue yoshidaA yoshidaA_pos (r + s) =
      clippedCriticalFormValue yoshidaA yoshidaA_pos r +
        2 * (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos r s).re +
      clippedCriticalFormValue yoshidaA yoshidaA_pos s := by
  have hcross :
      (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos s r).re =
        (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos r s).re := by
    have h := yoshidaClippedLocalCriticalForm_conj_apply
      yoshidaA_pos r s
    have hre := congrArg Complex.re h
    simpa only [starRingEnd_apply, Complex.conj_re] using hre
  unfold clippedCriticalFormValue
  simp only [map_add, LinearMap.add_apply, Complex.add_re]
  rw [hcross]
  ring

private theorem boundaryContinuousEvenProfile_add
    (f g : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA) :
    boundaryContinuousEvenProfile (f + g) =
      boundaryContinuousEvenProfile f + boundaryContinuousEvenProfile g := by
  funext x
  unfold boundaryContinuousEvenProfile evenBoundaryResidual
    evenBoundaryConstantPart centeredRescale
  simp only [Submodule.coe_add, Pi.add_apply, Complex.add_re, Complex.add_im,
    Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, Complex.sub_re, Complex.mul_re]
  ring

/-- For pointwise-real even periodic profiles, the clean polarization of
their boundary-continuous representatives is exactly the real clipped
critical pairing divided by Yoshida's endpoint scale. -/
theorem factorTwoCenteredCleanPolarization_boundaryContinuous_eq_clippedCriticalForm_re_div
    (f g : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaA)
    (hfReal : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0))
    (hgReal : ∀ x : ℝ,
      ((((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0)) :
    factorTwoCenteredCleanPolarization
        (boundaryContinuousEvenProfile f)
        (boundaryContinuousEvenProfile g) =
      (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        ((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)
        ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA)).re / yoshidaA := by
  let u : ℝ → ℝ := boundaryContinuousEvenProfile f
  let v : ℝ → ℝ := boundaryContinuousEvenProfile g
  have hfgReal : ∀ x : ℝ,
      (((((f + g).1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0) := by
    intro x
    simp only [Submodule.coe_add, Pi.add_apply, Complex.add_im,
      hfReal x, hgReal x, add_zero]
  have haddProfile : boundaryContinuousEvenProfile (f + g) = u + v := by
    simpa only [u, v] using boundaryContinuousEvenProfile_add f g
  have hfBridge := clippedCriticalFormValue_even_eq_clean_add_boundary
    f hfReal
  have hgBridge := clippedCriticalFormValue_even_eq_clean_add_boundary
    g hgReal
  have hfgBridge := clippedCriticalFormValue_even_eq_clean_add_boundary
    (f + g) hfgReal
  have hfBridge' :
      clippedCriticalFormValue yoshidaA yoshidaA_pos
          ((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) =
        yoshidaA * yoshidaEndpointOddCleanQuadratic u := by
    simpa only [u, YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using hfBridge
  have hgBridge' :
      clippedCriticalFormValue yoshidaA yoshidaA_pos
          ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) =
        yoshidaA * yoshidaEndpointOddCleanQuadratic v := by
    simpa only [v, YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using hgBridge
  have hfgBridge' :
      clippedCriticalFormValue yoshidaA yoshidaA_pos
          (((f + g).1 : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) =
        yoshidaA * yoshidaEndpointOddCleanQuadratic (u + v) := by
    rw [← haddProfile]
    simpa only [YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using hfgBridge
  have hadd := clippedCriticalFormValue_add
    ((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA)
    ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
      YoshidaClippedSmooth yoshidaA)
  have hcoeAdd :
      ((f.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) +
        ((g.1 : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) =
      (((f + g).1 : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) := rfl
  rw [hcoeAdd, hfBridge', hgBridge', hfgBridge'] at hadd
  dsimp only [u, v] at hadd
  unfold factorTwoCenteredCleanPolarization
  field_simp [yoshidaA_pos.ne']
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousCleanPolarizationStructural
