import ArithmeticHodge.Analysis.YoshidaFourCellOddP11WeightedDualSelectorStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalCoupledClosureStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11ProductionClosureStructural

noncomputable section

open YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP11WeightedDualSelectorStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddStripCapacityAssemblyStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Production handoff for the odd four-cell weighted dual

The exact corrected `P₁`/tail determinant is transported through the
`P₁`-orthogonal extension and the odd-strip base decomposition.  Weighted-dual
and selector certificates remain sufficient ways to prove that determinant,
but the production handoff itself does not require either strengthening.
-/

/-- The exact corrected `P₁`/`P₁₁+` determinant is itself sufficient for the
actual odd four-cell lower operator.  This is the correlation-preserving
frontier before any stronger weighted-dual or selector estimate is imposed. -/
theorem fourCellOddStripCapacityLowerOperator_nonnegative_of_correctedDefect
    (hdefect : FourCellOddP11CoupledRieszDefectNonnegative)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    0 ≤ fourCellOddStripCapacityLowerOperator w := by
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

/-- The concrete weighted-dual certificate proves the actual odd four-cell
lower operator for every smooth odd profile. -/
theorem fourCellOddStripCapacityLowerOperator_nonnegative_of_concreteWeightedDual
    (hdual : FourCellOddP11CoupledWeightedDualCertificate)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    0 ≤ fourCellOddStripCapacityLowerOperator w := by
  have hdefect : FourCellOddP11CoupledRieszDefectNonnegative :=
    fourCellOddP11CoupledRieszDefectNonnegative_of_concreteWeightedDual hdual
  exact fourCellOddStripCapacityLowerOperator_nonnegative_of_correctedDefect
    hdefect w hw hodd

/-- The weaker correlation-preserving selector Loewner condition feeds the
same production chain directly; the obsolete independent `D₀` allocation is
not needed. -/
theorem fourCellOddStripCapacityLowerOperator_nonnegative_of_selectorLoewner
    (hselector : FourCellOddP11CoupledSelectorLoewnerCertificate)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    0 ≤ fourCellOddStripCapacityLowerOperator w := by
  have hdefect : FourCellOddP11CoupledRieszDefectNonnegative :=
    fourCellOddP11CoupledRieszDefectNonnegative_of_selectorLoewner hselector
  exact fourCellOddStripCapacityLowerOperator_nonnegative_of_correctedDefect
    hdefect w hw hodd

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11ProductionClosureStructural
