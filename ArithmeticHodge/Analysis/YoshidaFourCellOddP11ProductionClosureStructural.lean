import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalCoupledClosureStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11ProductionClosureStructural

noncomputable section

open YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddStripCapacityAssemblyStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Production handoff for the odd four-cell weighted dual

The coupled weighted-dual certificate is transported through the corrected
`P₁`/tail determinant, the `P₁`-orthogonal extension, and the exact odd-strip
base decomposition.  Thus the named weighted dual is the only remaining
analytic premise in the odd four-cell production branch.
-/

/-- The concrete weighted-dual certificate proves the actual odd four-cell
lower operator for every smooth odd profile. -/
theorem fourCellOddStripCapacityLowerOperator_nonnegative_of_concreteWeightedDual
    (hdual : FourCellOddP11CoupledWeightedDualCertificate)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    0 ≤ fourCellOddStripCapacityLowerOperator w := by
  have hdefect : FourCellOddP11CoupledRieszDefectNonnegative :=
    fourCellOddP11CoupledRieszDefectNonnegative_of_concreteWeightedDual hdual
  have hcoupled : FourCellOddP1FiveModeP11CoupledTailBound :=
    fourCellOddP1FiveModeP11CoupledTailBound_of_correctedDefect hdefect
  have horthogonal : FourCellOddP1OrthogonalFormDualBound :=
    fourCellOddP1OrthogonalFormDualBound_of_fiveModeP11CoupledTail hcoupled
  have hcore : 0 ≤ fourCellOddCoreLocalQuadratic w :=
    fourCellOddCoreLocalQuadratic_nonneg_of_P1OrthogonalFormDual
      horthogonal w hw hodd
  apply fourCellOddStripCapacityLowerOperator_nonneg_of_base_ge_blended
    w hw.continuous
  rw [← sub_nonneg]
  rw [fourCellOddStripCapacityBase_sub_blended_eq_core_add_localWidthDefect
    w hw hodd]
  simpa only [fourCellOddCoreLocalQuadratic] using hcore

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11ProductionClosureStructural
