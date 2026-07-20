import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural

noncomputable section

open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural

/-!
# Unconditional finite bridge for the odd `P₁₁+` defect

The coefficient/function identification is now proved exactly, so the finite
corrected reserve is no longer an input.  The only remaining hypothesis in
the odd defect closure is the coupled weighted-dual selector inequality.
-/

/-- The exact five-mode coefficient/function bridge, with no hypothesis. -/
theorem fourCellOddFiveModeCoreExpressionBridge :
    FourCellOddFiveModeCoreExpressionBridge := by
  intro c d e f g
  exact fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression c d e f g

/-- The retained `P₃/P₅/P₇/P₉` corrected reserve is unconditionally
nonnegative. -/
theorem fourCellOddP11FiniteCorrectedReserve_nonnegative :
    FourCellOddP11FiniteCorrectedReserveNonnegative :=
  fourCellOddP11FiniteCorrectedReserve_nonnegative_of_bridge
    fourCellOddFiveModeCoreExpressionBridge

/-- The concrete coupled weighted-dual selector is now the sole input needed
for the actual universal corrected Riesz defect. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_concreteWeightedDual
    (hdual : FourCellOddP11CoupledWeightedDualCertificate) :
    FourCellOddP11CoupledRieszDefectNonnegative :=
  fourCellOddP11CoupledRieszDefectNonnegative_of_weightedDual
    fourCellOddP11FiniteCorrectedReserve_nonnegative hdual

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural
