import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveCoupledReduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveRankStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructuralPositive

noncomputable section

open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLegendreFourFiveCoupledReduction
open YoshidaFactorTwoPhaseLegendreFourFiveRankStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural

/-!
# Structural positivity for the first middle Legendre pair

This theorem combines the uniform all-rank `P₄/P₅` estimates with the
coupled clean-reserve reduction.  No finite cutoff or rank enumeration remains
among its hypotheses.
-/

/-- Every independently rescaled `P₄/P₅` pair has nonnegative factor-two
endpoint phase throughout the closed phase disk. -/
theorem factorTwoEndpointChannelPhase_P4_P5_nonneg
    (c d a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (fun x ↦ c * factorTwoCenteredP4 x)
      (fun x ↦ d * factorTwoCenteredP5 x) a b :=
  factorTwoEndpointChannelPhase_P4_P5_nonneg_of_rank_bounds
    factorTwoEvenRankEnergy_P4_le_three_twentieths
    factorTwoOddRankEnergy_P5_le_three_twentieths
    c d a b hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructuralPositive
