import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45Reduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveRankStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45StructuralReduction

noncomputable section

open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45Reduction
open YoshidaFactorTwoPhaseIntrinsicLowStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreFourFiveRankStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Rank-free Schur reduction for the first six intrinsic modes

The structural all-rank estimates discharge the two analytic hypotheses in
the original six-mode reduction.  Only the exact mixed Schur inequality
remains.
-/

/-- The first six intrinsic Legendre modes are phase-positive provided their
single mixed Schur inequality holds. -/
theorem factorTwoEndpointChannelPhase_intrinsicFour_add_P45_nonneg_of_mixed_schur_structural
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
        fun x ↦ c5 * factorTwoCenteredP5 x) a b :=
  factorTwoEndpointChannelPhase_intrinsicFour_add_P45_nonneg_of_mixed_schur
    factorTwoEvenRankEnergy_P4_le_three_twentieths
    factorTwoOddRankEnergy_P5_le_three_twentieths
    c0 c2 c1 c3 c4 c5 a b hab hMixed

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45StructuralReduction
