import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlsPositive

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEndpointControlsStructuralPositive

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlsPositive
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural endpoint controls for the intrinsic phase block

The signed even and odd endpoint theorems discharge the two endpoint
Bernstein controls.  Only the two interior controls (or an alternative static
split) remain for the intrinsic four-mode disk.
-/

theorem factorTwoIntrinsicOdd_plus_quadratic_nonneg (c d : ℝ) :
    0 ≤ factorTwoIntrinsicOddPhaseQuadratic 1 c d := by
  rcases oddStructuralLow_endpoint_gates with
    ⟨h11, hdet, _hminus11, _hminusDet⟩
  by_cases hne : c ≠ 0 ∨ d ≠ 0
  · exact (real_twoByTwo_quadratic_pos
      (factorTwoIntrinsicOddPhaseLow11 1)
      (factorTwoIntrinsicOddPhaseLow13 1)
      (factorTwoIntrinsicOddPhaseLow33 1)
      c d h11 hdet hne).le
  · have hz : c = 0 ∧ d = 0 := by
      simpa only [not_or, not_not] using hne
    rcases hz with ⟨rfl, rfl⟩
    simp [factorTwoIntrinsicOddPhaseQuadratic]

theorem factorTwoIntrinsicOdd_minus_quadratic_nonneg (c d : ℝ) :
    0 ≤ factorTwoIntrinsicOddPhaseQuadratic (-1) c d := by
  rcases oddStructuralLow_endpoint_gates with
    ⟨_hplus11, _hplusDet, h11, hdet⟩
  by_cases hne : c ≠ 0 ∨ d ≠ 0
  · exact (real_twoByTwo_quadratic_pos
      (factorTwoIntrinsicOddPhaseLow11 (-1))
      (factorTwoIntrinsicOddPhaseLow13 (-1))
      (factorTwoIntrinsicOddPhaseLow33 (-1))
      c d h11 hdet hne).le
  · have hz : c = 0 ∧ d = 0 := by
      simpa only [not_or, not_not] using hne
    rcases hz with ⟨rfl, rfl⟩
    simp [factorTwoIntrinsicOddPhaseQuadratic]

/-- The positive-endpoint Bernstein control is nonnegative for every odd
coefficient pair. -/
theorem factorTwoIntrinsicBoundaryControl0_nonneg_structural (c d : ℝ) :
    0 ≤ factorTwoIntrinsicBoundaryControl0 c d := by
  exact factorTwoIntrinsicBoundaryControl0_nonneg_of_endpoint c d
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.2.le
    (factorTwoIntrinsicOdd_plus_quadratic_nonneg c d)

/-- The negative-endpoint Bernstein control is nonnegative for every odd
coefficient pair. -/
theorem factorTwoIntrinsicBoundaryControl3_nonneg_structural (c d : ℝ) :
    0 ≤ factorTwoIntrinsicBoundaryControl3 c d := by
  exact factorTwoIntrinsicBoundaryControl3_nonneg_of_endpoint c d
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.2.le
    (factorTwoIntrinsicOdd_minus_quadratic_nonneg c d)

theorem factorTwoIntrinsicBoundaryControl0_psd_structural :
    IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControl0 :=
  factorTwoIntrinsicBoundaryControl0_nonneg_iff.mp
    factorTwoIntrinsicBoundaryControl0_nonneg_structural

theorem factorTwoIntrinsicBoundaryControl3_psd_structural :
    IntrinsicBinaryQuadraticPSD factorTwoIntrinsicBoundaryControl3 :=
  factorTwoIntrinsicBoundaryControl3_nonneg_iff.mp
    factorTwoIntrinsicBoundaryControl3_nonneg_structural

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEndpointControlsStructuralPositive
