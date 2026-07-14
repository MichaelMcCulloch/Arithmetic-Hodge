import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointReduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointReduction

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4LeadingStructuralClosure

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur

/-!
# Structural closure of the phase-dependent `P₄` leading pivot

The positive endpoint contributes one column-Schur gate; the negative
endpoint contributes one growing-row dual gate.  Convexity of the actual
`P₀/P₂/P₄` pencil then propagates strict positivity to the entire
closed phase disk.
-/

/-- The exact positive-endpoint column gate. -/
def factorTwoIntrinsicP024PlusColumnGate : Prop :=
  factorTwoIntrinsicSixP4PlusLower22 *
          factorTwoIntrinsicSixP4PlusLower04 ^ 2 -
        2 * factorTwoIntrinsicSixP4PlusLower02 *
          factorTwoIntrinsicSixP4PlusLower04 *
          factorTwoIntrinsicSixP4PlusLower24 +
        factorTwoIntrinsicSixP4PlusLower00 *
          factorTwoIntrinsicSixP4PlusLower24 ^ 2 <
      leadingMinorTwo
          factorTwoIntrinsicSixP4PlusLower00
          factorTwoIntrinsicSixP4PlusLower02
          factorTwoIntrinsicSixP4PlusLower22 *
        factorTwoIntrinsicSixP4PlusLower44

/-- The two endpoint inequalities imply positivity of the sequential `P₄`
leading coefficient at every point of the phase disk. -/
theorem factorTwoIntrinsicSixP4SchurLeading_pos_of_structural_endpoint_gates
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hPlus : factorTwoIntrinsicP024PlusColumnGate)
    (hMinus : factorTwoIntrinsicP024MinusDualGate) :
    0 < factorTwoIntrinsicSixP4SchurLeading a := by
  apply factorTwoIntrinsicSixP4SchurLeading_pos_of_endpoint_gates a b hab
  · exact factorTwoIntrinsicSixP4SchurLeading_one_pos_of_plus_lower_schur
      hPlus
  · exact factorTwoIntrinsicSixP4SchurLeading_minus_pos_of_dualGate
      hMinus

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4LeadingStructuralClosure
