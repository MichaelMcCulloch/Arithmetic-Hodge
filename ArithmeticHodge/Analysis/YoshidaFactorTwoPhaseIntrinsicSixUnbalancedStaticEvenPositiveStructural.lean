import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# Positivity of the even blocks in the unbalanced endpoint split

The rational transfer changes only the alternating block.  Consequently the
two even `P0/P2/P4` blocks are exactly the endpoint matrices whose two low
Sylvester gates and full determinants were already proved structurally.
-/

private theorem ePlusDet_eq_P024 :
    factorTwoIntrinsicSixUnbalancedEPlusDet =
      factorTwoIntrinsicP024Determinant 1 := by
  unfold factorTwoIntrinsicSixUnbalancedEPlusDet
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    factorTwoIntrinsicP024Determinant
  rfl

private theorem eMinusDet_eq_P024 :
    factorTwoIntrinsicSixUnbalancedEMinusDet =
      factorTwoIntrinsicP024Determinant (-1) := by
  unfold factorTwoIntrinsicSixUnbalancedEMinusDet
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
    factorTwoIntrinsicP024Determinant
  rfl

/-- The positive-endpoint even block has all three strict Sylvester gates. -/
theorem factorTwoIntrinsicSixUnbalancedEPlus_positive :
    FactorTwoIntrinsicSixUnbalancedEPlusPositive := by
  rcases factorTwoIntrinsicEven_plus_endpoint_structural_gates with
    ⟨h00, hminor⟩
  constructor
  · simpa [factorTwoIntrinsicSixUnbalancedEPlus00] using h00
  constructor
  · simpa [leadingMinorTwo, factorTwoIntrinsicEvenPhaseDet,
      factorTwoIntrinsicSixUnbalancedEPlus00,
      factorTwoIntrinsicSixUnbalancedEPlus02,
      factorTwoIntrinsicSixUnbalancedEPlus22] using hminor
  · rw [ePlusDet_eq_P024,
      ← factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant]
    exact factorTwoIntrinsicSixP4SchurLeading_plus_pos

/-- The negative-endpoint even block has all three strict Sylvester gates. -/
theorem factorTwoIntrinsicSixUnbalancedEMinus_positive :
    FactorTwoIntrinsicSixUnbalancedEMinusPositive := by
  rcases factorTwoIntrinsicEven_minus_endpoint_kernel_gates with
    ⟨h00, hminor⟩
  constructor
  · simpa [factorTwoIntrinsicSixUnbalancedEMinus00] using h00
  constructor
  · simpa [leadingMinorTwo, factorTwoIntrinsicEvenPhaseDet,
      factorTwoIntrinsicSixUnbalancedEMinus00,
      factorTwoIntrinsicSixUnbalancedEMinus02,
      factorTwoIntrinsicSixUnbalancedEMinus22] using hminor
  · rw [eMinusDet_eq_P024,
      ← factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant]
    exact factorTwoIntrinsicSixP4SchurLeading_minus_pos

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
