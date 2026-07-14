import ArithmeticHodge.Analysis.YoshidaCoercivityNumerics
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointClean
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile

set_option autoImplicit false

open scoped ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCleanPolarizationCritical

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseFullProfile
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Clean polarization as a clipped critical cross term

The mixed clean term needs no separate singular-integral bilinearity proof.
It follows by applying the endpoint clean bridge to `r`, `s`, and `r + s`,
then expanding the diagonal of the Hermitian sesquilinear critical form.
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

/-- For pointwise-real periodic profiles with zero endpoint traces, the
endpoint clean polarization is exactly the real clipped critical pairing,
divided by Yoshida's endpoint scale. -/
theorem factorTwoCenteredCleanPolarization_eq_clippedCriticalForm_re_div
    (r s : YoshidaClippedPeriodicCore yoshidaA)
    (hrReal : ∀ x : ℝ,
      ((r : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hsReal : ∀ x : ℝ,
      ((s : YoshidaClippedSmooth yoshidaA) x).im = 0)
    (hrNeg : (r : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hrPos : (r : YoshidaClippedSmooth yoshidaA) yoshidaA = 0)
    (hsNeg : (s : YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0)
    (hsPos : (s : YoshidaClippedSmooth yoshidaA) yoshidaA = 0) :
    factorTwoCenteredCleanPolarization
        (centeredRescale yoshidaA (fun x ↦
          ((r : YoshidaClippedSmooth yoshidaA) x).re))
        (centeredRescale yoshidaA (fun x ↦
          ((s : YoshidaClippedSmooth yoshidaA) x).re)) =
      (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (r : YoshidaClippedSmooth yoshidaA)
        (s : YoshidaClippedSmooth yoshidaA)).re / yoshidaA := by
  let u : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((r : YoshidaClippedSmooth yoshidaA) x).re)
  let v : ℝ → ℝ := centeredRescale yoshidaA (fun x ↦
    ((s : YoshidaClippedSmooth yoshidaA) x).re)
  have hrsReal : ∀ x : ℝ,
      (((r + s : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) x).im = 0 := by
    intro x
    simp only [Submodule.coe_add, Pi.add_apply, Complex.add_im,
      hrReal x, hsReal x, add_zero]
  have hrsNeg :
      ((r + s : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) (-yoshidaA) = 0 := by
    simp only [Submodule.coe_add, Pi.add_apply, hrNeg, hsNeg, add_zero]
  have hrsPos :
      ((r + s : YoshidaClippedPeriodicCore yoshidaA) :
        YoshidaClippedSmooth yoshidaA) yoshidaA = 0 := by
    simp only [Submodule.coe_add, Pi.add_apply, hrPos, hsPos, add_zero]
  have haddProfile :
      centeredRescale yoshidaA (fun x ↦
        (((r + s : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) x).re) = u + v := by
    funext x
    rfl
  have hrBridge :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      r hrReal hrNeg hrPos
  have hsBridge :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      s hsReal hsNeg hsPos
  have hrsBridge :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      (r + s) hrsReal hrsNeg hrsPos
  have hrBridge' :
      clippedCriticalFormValue yoshidaA yoshidaA_pos
          (r : YoshidaClippedSmooth yoshidaA) =
        yoshidaA * yoshidaEndpointOddCleanQuadratic u := by
    simpa only [u, YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using hrBridge
  have hsBridge' :
      clippedCriticalFormValue yoshidaA yoshidaA_pos
          (s : YoshidaClippedSmooth yoshidaA) =
        yoshidaA * yoshidaEndpointOddCleanQuadratic v := by
    simpa only [v, YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using hsBridge
  have hrsBridge' :
      clippedCriticalFormValue yoshidaA yoshidaA_pos
          ((r + s : YoshidaClippedPeriodicCore yoshidaA) :
            YoshidaClippedSmooth yoshidaA) =
        yoshidaA * yoshidaEndpointOddCleanQuadratic (u + v) := by
    rw [← haddProfile]
    simpa only [YoshidaEndpointHyperbolicBound.yoshidaEndpointA,
      YoshidaWeightedTailBounds.yoshidaA] using hrsBridge
  have hadd := clippedCriticalFormValue_add
    (r : YoshidaClippedSmooth yoshidaA)
    (s : YoshidaClippedSmooth yoshidaA)
  have hcoeAdd :
      (r : YoshidaClippedSmooth yoshidaA) +
          (s : YoshidaClippedSmooth yoshidaA) =
        ((r + s : YoshidaClippedPeriodicCore yoshidaA) :
          YoshidaClippedSmooth yoshidaA) := rfl
  rw [hcoeAdd, hrBridge', hsBridge', hrsBridge'] at hadd
  dsimp only [u, v] at hadd
  unfold factorTwoCenteredCleanPolarization
  field_simp [yoshidaA_pos.ne']
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCleanPolarizationCritical
