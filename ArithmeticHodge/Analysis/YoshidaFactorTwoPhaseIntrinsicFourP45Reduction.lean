import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveCoupledReduction

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45Reduction

noncomputable section

open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseArchRankDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicLowStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreFourFiveCoupledReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Schur reduction for the first six intrinsic modes

The intrinsic four-mode block and the `P₄/P₅` block are already treated
separately.  Their sum is therefore reduced to one exact mixed determinant;
no entrywise phase split is introduced here.
-/

/-- The exact mixed coordinate between the intrinsic four-mode block and the
rescaled `P₄/P₅` block. -/
def factorTwoIntrinsicFourP45Mixed
    (c0 c2 c1 c3 c4 c5 a b : ℝ) : ℝ :=
  factorTwoEndpointLowTailMixed
    (factorTwoEvenStructuralLowProfile c0 c2)
    (fun x ↦ c4 * factorTwoCenteredP4 x)
    (factorTwoOddStructuralLowProfile c1 c3)
    (fun x ↦ c5 * factorTwoCenteredP5 x) a b

/-- The first six intrinsic Legendre modes are phase-positive once their
single mixed Schur determinant and the two scalar `P₄/P₅` rank bounds hold. -/
theorem factorTwoEndpointChannelPhase_intrinsicFour_add_P45_nonneg_of_mixed_schur
    (hRank4 : factorTwoEvenRankEnergy factorTwoCenteredP4 ≤
      (3 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP4)
    (hRank5 : factorTwoOddRankEnergy factorTwoCenteredP5 ≤
      (3 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP5)
    (c0 c2 c1 c3 c4 c5 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hMixed :
      factorTwoIntrinsicFourP45Mixed c0 c2 c1 c3 c4 c5 a b ^ 2 ≤
        factorTwoEndpointChannelPhase
            (factorTwoEvenStructuralLowProfile c0 c2)
            (factorTwoOddStructuralLowProfile c1 c3) a b *
          factorTwoEndpointChannelPhase
            (fun x ↦ c4 * factorTwoCenteredP4 x)
            (fun x ↦ c5 * factorTwoCenteredP5 x) a b) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2 +
        fun x ↦ c4 * factorTwoCenteredP4 x)
      (factorTwoOddStructuralLowProfile c1 c3 +
        fun x ↦ c5 * factorTwoCenteredP5 x) a b := by
  apply factorTwoEndpointChannelPhase_nonneg_of_low_tail_schur
    (factorTwoEvenStructuralLowProfile c0 c2)
    (fun x ↦ c4 * factorTwoCenteredP4 x)
    (factorTwoOddStructuralLowProfile c1 c3)
    (fun x ↦ c5 * factorTwoCenteredP5 x)
    (continuous_factorTwoEvenStructuralLowProfile c0 c2)
    (continuous_const.mul continuous_factorTwoCenteredP4)
    (continuous_factorTwoOddStructuralLowProfile c1 c3)
    (continuous_const.mul continuous_factorTwoCenteredP5)
    a b
    (factorTwoEndpointChannelPhase_intrinsicLow_nonneg_structural
      c0 c2 c1 c3 a b hab)
    (factorTwoEndpointChannelPhase_P4_P5_nonneg_of_rank_bounds
      hRank4 hRank5 c4 c5 a b hab)
  simpa only [factorTwoIntrinsicFourP45Mixed] using hMixed

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45Reduction
