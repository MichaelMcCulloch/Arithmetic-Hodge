import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenCleanPolarizationBridge

noncomputable section

open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur

/-!
# Even low--tail clean polarization bridge

The existing exact low--tail expansion is restated as an identity for the
clean polarization used by the endpoint phase Schur decomposition.
-/

/-- Clean polarization of an intrinsic even `P₀/P₂` profile against a
zero-`P₂` tail is exactly the public clean bilinear form. -/
theorem factorTwoCenteredCleanPolarization_evenStructuralLow_tail_eq_bilinear
    (r : ℝ → ℝ) (hr : Continuous r)
    (htwo : centeredEvenP2Coefficient r = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (c d : ℝ) :
    factorTwoCenteredCleanPolarization
        (factorTwoEvenStructuralLowProfile c d) r =
      yoshidaEndpointEvenCleanBilinear
        (factorTwoEvenStructuralLowProfile c d) r := by
  have hlow : factorTwoEvenStructuralLowProfile c d =
      yoshidaEndpointEvenLowProfile c d := by
    funext x
    unfold factorTwoEvenStructuralLowProfile yoshidaEndpointEvenLowProfile
      centeredEvenP0
    ring
  have h := yoshidaEndpointOddCleanQuadratic_low_tail
    r hr htwo hlocal c d
  unfold factorTwoCenteredCleanPolarization
  rw [hlow]
  change
    (yoshidaEndpointOddCleanQuadratic
          (fun x ↦ yoshidaEndpointEvenLowProfile c d x + r x) -
        yoshidaEndpointOddCleanQuadratic (yoshidaEndpointEvenLowProfile c d) -
        yoshidaEndpointOddCleanQuadratic r) / 2 =
      yoshidaEndpointEvenCleanBilinear
        (yoshidaEndpointEvenLowProfile c d) r
  rw [h]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenCleanPolarizationBridge
