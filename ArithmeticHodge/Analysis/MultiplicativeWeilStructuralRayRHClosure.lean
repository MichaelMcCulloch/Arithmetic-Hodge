import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthCommonParentResidualStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthPositiveRayKernelStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualParentLocalizationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellSelectorProductionClosureStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
import ArithmeticHodge.Analysis.YoshidaFiveCellEndpointParitySchurClosureStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.MultiplicativeWeilStructuralRayRHClosure

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthCommonParentResidualStructural
open MultiplicativeWeilAllLengthPositiveRayKernelStructural
open MultiplicativeWeilAllLengthResidualParentLocalizationStructural
open MultiplicativeWeilFiveCellResidualFactorTwoStructural
open MultiplicativeWeilFourCellSelectorProductionClosureStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open YoshidaFiveCellEndpointParitySchurClosureStructural
open YoshidaFourCellOddP11WeightedDualSelectorStructural

/-!
# Exact structural-ray frontier for RH

This file packages the sharpened low-length and tail handoffs without hiding
any analytic premise.  Length four is one even endpoint-zero capacity family
plus the odd two-row selector Loewner certificate.  Length five is the pair of
intrinsic same-parity low-plus-tail ray families.  Every later length is the
positive ray of the actual common-parent residual pencil, restricted to
genuinely nonlocal parents in the exact surrounding lattice window;
ratio-two parents and remote parent support are already unconditional or
irrelevant.
-/

/-- The intrinsic five-cell parity rays imply production positivity at exact
length five. -/
theorem realFiniteBlockProductionNonnegativeAtLength_five_of_intrinsicParityRays
    (hfive : FiveCellEndpointAdaptedIntrinsicParityRayNonnegative) :
    RealFiniteBlockProductionNonnegativeAtLength 5 := by
  exact realFiveCellFactorTwoDomination_iff_productionNonnegative.mp
    (realFiveCellFactorTwoDomination_of_intrinsicParityRays hfive)

/-- The complete sharpened analytic frontier, with no remote-support,
ratio-two-support, lattice-position, or singular-pivot bookkeeping left
implicit. -/
def ArithmeticHodgeStructuralRayCertificate : Prop :=
  FourCellEvenEndpointZeroExactCapacity ∧
    FourCellOddP11CoupledSelectorLoewnerCertificate ∧
      FiveCellEndpointAdaptedIntrinsicParityRayNonnegative ∧
        ∀ n : ℕ, 6 ≤ n →
          RealFiniteBlockCommonParentResidualPositiveRayNonnegativeNormalizedOutsideRatioTwoAtLength
            n

/-- The structural-ray certificate implies RH.  The zero enumeration is an
already-proved existence theorem and is chosen internally, so no auxiliary
hypothesis remains at the terminal interface. -/
theorem riemannHypothesis_of_structuralRayCertificate
    (hcert : ArithmeticHodgeStructuralRayCertificate) :
    RiemannHypothesis := by
  let zeros : ZetaZeroEnumeration :=
    Classical.choice nonempty_zetaZeroEnumeration
  exact riemannHypothesis_of_four_five_and_tailPositiveRay
    zeros
    (realFiniteBlockProductionNonnegativeAtLength_four_of_evenCapacity_and_oddSelector
      hcert.1 hcert.2.1)
    (realFiniteBlockProductionNonnegativeAtLength_five_of_intrinsicParityRays
      hcert.2.2.1)
    (fun n hn ↦
      (realFiniteBlockCommonParentResidualPositiveRayNonnegative_iff_normalizedOutsideRatioTwo
        n (by omega)).2 (hcert.2.2.2 n hn))

end

end ArithmeticHodge.Analysis.MultiplicativeWeilStructuralRayRHClosure
