import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEndpointControlsStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01CoupledResidualPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep12ResidualPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStructuralPositive

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicEndpointControlsStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01CoupledResidualPositive
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01CauchyStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Positive
open YoshidaFactorTwoPhaseIntrinsicLowControlStep12ResidualPositive
open YoshidaFactorTwoPhaseIntrinsicLowControlStep12Structural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlsPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaEndpointOddResidualRegularity

/-!
# Structural positivity of the intrinsic four-mode phase block

The pointwise assembly below uses one coupled `2 x 2` Schur estimate for
Step01 and the structural Step12 and Step23 estimates.  It does not split
the phase disk into cases or enumerate modes.
-/

/-- A `23 / 5` determinant slope turns the rational coupled Schur estimate
into the exact Step01 Cauchy inequality. -/
theorem factorTwoIntrinsicStep01ExactCauchy_of_slope23Fifths
    (hslope : (23 / 5 : ℝ) ≤ factorTwoIntrinsicStep01Slope) :
    FactorTwoIntrinsicStep01ExactCauchy := by
  intro u v c d
  have hrational :=
    step01_rationalCauchy_of_alternatingSharpBounds
      factorTwoIntrinsicAlternatingSharpBounds u v c d
  have heven := step01EvenLower_le u v
  have hodd := step01OddBudgetLower_le hslope c d
  have hproduct :
      step01EvenLower u v * step01OddBudgetLower c d ≤
        factorTwoIntrinsicEvenPlusQuadratic u v *
          factorTwoIntrinsicStep01ExactOddBudget c d :=
    mul_le_mul heven hodd (step01OddBudgetLower_nonneg c d)
      ((step01EvenLower_nonneg u v).trans heven)
  exact hrational.trans hproduct

/-- The first Bernstein difference is nonnegative once the structural
determinant-slope reserve is supplied. -/
theorem factorTwoIntrinsicBoundaryControlStep01_nonneg_of_slope23Fifths
    (hslope : (23 / 5 : ℝ) ≤ factorTwoIntrinsicStep01Slope) :
    ∀ c d : ℝ, 0 ≤ factorTwoIntrinsicBoundaryControlStep01 c d := by
  exact (factorTwoIntrinsicBoundaryControlStep01_nonneg_iff_exactCauchy
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.1
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.2).mpr
      (factorTwoIntrinsicStep01ExactCauchy_of_slope23Fifths hslope)

/-- Conditional structural closure of all four intrinsic Bernstein controls. -/
theorem factorTwoIntrinsicBoundaryControls_nonneg_of_slope23Fifths
    (hslope : (23 / 5 : ℝ) ≤ factorTwoIntrinsicStep01Slope) :
    ∀ c d : ℝ,
      0 ≤ factorTwoIntrinsicBoundaryControl0 c d ∧
        0 ≤ factorTwoIntrinsicBoundaryControl1 c d ∧
        0 ≤ factorTwoIntrinsicBoundaryControl2 c d ∧
        0 ≤ factorTwoIntrinsicBoundaryControl3 c d := by
  intro c d
  exact factorTwoIntrinsicBoundaryControls_nonneg_of_steps c d
    (factorTwoIntrinsicBoundaryControl0_nonneg_structural c d)
    (factorTwoIntrinsicBoundaryControlStep01_nonneg_of_slope23Fifths
      hslope c d)
    (factorTwoIntrinsicBoundaryControlStep12_nonneg_of_reducedResidual
      c d (step12ReducedResidual_nonneg c d))
    (factorTwoIntrinsicBoundaryControlStep23_nonneg_structural c d)

/-- Conditional pointwise Bernstein assembly of the intrinsic phase disk. -/
theorem factorTwoEndpointChannelPhase_intrinsicLow_nonneg_of_slope23Fifths
    (hslope : (23 / 5 : ℝ) ≤ factorTwoIntrinsicStep01Slope)
    (c0 c2 c1 c3 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2)
      (factorTwoOddStructuralLowProfile c1 c3) a b := by
  have hcontrols :=
    factorTwoIntrinsicBoundaryControls_nonneg_of_slope23Fifths
      hslope c1 c3
  exact factorTwoEndpointChannelPhase_intrinsicLow_nonneg_of_controls
    c0 c2 c1 c3 a b hab
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.1
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.2
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.1
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.2
    hcontrols.1 hcontrols.2.1 hcontrols.2.2.1 hcontrols.2.2.2

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStructuralPositive
