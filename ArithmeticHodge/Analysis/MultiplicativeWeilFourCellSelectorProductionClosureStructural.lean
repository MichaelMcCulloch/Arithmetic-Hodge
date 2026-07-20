import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellCapacityAssemblyStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ProductionClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11WeightedDualSelectorStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellSelectorProductionClosureStructural

noncomputable section

open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilFourCellCapacityAssemblyStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11ProductionClosureStructural
open YoshidaFourCellOddP11WeightedDualSelectorStructural
open YoshidaFourCellOddStripCapacityAssemblyStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural

/-!
# Four-cell production from the exact odd corrected determinant

The exact correlation-preserving odd `P11+` corrected determinant feeds the
actual four-cell production theorem directly.  Stronger selector certificates
remain available as sufficient interfaces, but are not part of the sharp
length-four frontier.
-/

/-- The still-missing endpoint-zero even parity bracket, isolated from the
now-sharpened odd selector condition. -/
def FourCellEvenEndpointZeroExactCapacity : Prop :=
  ∀ w : ℝ → ℝ, ContDiff ℝ 1 w → Function.Even w →
    w (-1) = 0 ∧ w 1 = 0 →
      0 ≤ centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w

/-- The even endpoint-zero capacity theorem and the exact odd corrected
determinant imply production positivity at length four. -/
theorem realFiniteBlockProductionNonnegativeAtLength_four_of_evenCapacity_and_oddCorrectedDefect
    (heven : FourCellEvenEndpointZeroExactCapacity)
    (hodd : FourCellOddP11CoupledRieszDefectNonnegative) :
    RealFiniteBlockProductionNonnegativeAtLength 4 := by
  intro parent hparent k
  exact
    bombieriRealQuadraticValue_fourBlock_nonnegative_of_endpointZeroExactParityCapacity
      heven
      (by
        intro w hw hwOdd _hendpoints
        exact fourCellBracket_nonnegative_of_oddStripCapacity
          w hw hwOdd
            (fourCellOddStripCapacityLowerOperator_nonnegative_of_correctedDefect
              hodd w hw hwOdd))
      parent hparent k 0

/-- The odd selector Loewner certificate and the exact even endpoint-zero
capacity theorem imply production positivity at length four. -/
theorem realFiniteBlockProductionNonnegativeAtLength_four_of_evenCapacity_and_oddSelector
    (heven : FourCellEvenEndpointZeroExactCapacity)
    (hodd : FourCellOddP11CoupledSelectorLoewnerCertificate) :
    RealFiniteBlockProductionNonnegativeAtLength 4 := by
  intro parent hparent k
  exact
    bombieriRealQuadraticValue_fourBlock_nonnegative_of_endpointZeroExactParityCapacity
      heven
      (by
        intro w hw hwOdd _hendpoints
        exact fourCellBracket_nonnegative_of_oddStripCapacity
          w hw hwOdd
            (fourCellOddStripCapacityLowerOperator_nonnegative_of_selectorLoewner
              hodd w hw hwOdd))
      parent hparent k 0

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellSelectorProductionClosureStructural
