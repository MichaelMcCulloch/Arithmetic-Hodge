import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellCapacityAssemblyStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenSchurResidualSelectorStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ProductionClosureStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11WeightedDualSelectorStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellSelectorProductionClosureStructural

noncomputable section

open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilFourCellCapacityAssemblyStructural
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenFiniteSevenTailAssemblyStructural
open YoshidaFourCellEvenSchurResidualSelectorStructural
open YoshidaFourCellEvenZeroCoshCoupledCoreStructural
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

/-- The canonical quotient-tail Loewner inequality supplies the complete
endpoint-zero even capacity family through the endpoint-preserving cosh
split.  The zero-cosh diagonal is already unconditional; only the canonical
endpoint-seed row is consumed here. -/
theorem fourCellEvenEndpointZeroExactCapacity_of_canonicalSchurResidualLoewner
    (hloewner : FourCellEvenCanonicalSchurResidualLoewner) :
    FourCellEvenEndpointZeroExactCapacity := by
  intro w hw heven hend
  have hbracket :=
    fourCell_evenBracket_nonnegative_of_endpointSeedUniversalSchur
      w hw heven hend
      (by
        intro v hvDiff hveven _hvend hzero
        exact
          thirtyThree_div_twenty_mass_le_canonicalCoupledCore_cutoffEight
            v hvDiff.continuous
            (hvDiff.contDiffOn.locallyLipschitzOn
              (convex_Icc (-1 : ℝ) 1))
            hveven hzero)
      (by
        intro v hvDiff hveven _hvend hzero
        have hrow :=
          fourCellEvenEndpointSeedRow_sq_le_seed_mul_polarFree_of_canonicalLoewner
            hloewner v hvDiff.continuous
              (hvDiff.contDiffOn.locallyLipschitzOn
                (convex_Icc (-1 : ℝ) 1))
              hveven hzero
        simpa only [fourCellEvenFiniteSevenSeedDiagonal] using hrow)
  simpa only [fourCellEvenExactBracket] using hbracket

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

/-- The sharp canonical even quotient and exact odd corrected determinant
are sufficient for production positivity at length four. -/
theorem realFiniteBlockProductionNonnegativeAtLength_four_of_evenCanonicalLoewner_and_oddCorrectedDefect
    (heven : FourCellEvenCanonicalSchurResidualLoewner)
    (hodd : FourCellOddP11CoupledRieszDefectNonnegative) :
    RealFiniteBlockProductionNonnegativeAtLength 4 :=
  realFiniteBlockProductionNonnegativeAtLength_four_of_evenCapacity_and_oddCorrectedDefect
    (fourCellEvenEndpointZeroExactCapacity_of_canonicalSchurResidualLoewner
      heven)
    hodd

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
