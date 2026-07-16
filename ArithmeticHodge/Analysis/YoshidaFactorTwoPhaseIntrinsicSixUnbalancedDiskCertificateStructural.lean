import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusNonnegativeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskCertificateStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusNonnegativeStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Unconditional intrinsic six-mode phase disk

The two structural endpoint certificates are inserted into the exact
square-root interpolation of the unbalanced split.  The transferred
bilinear terms cancel before interpolation, so the conclusion covers the
entire closed phase disk, including `(-1, 0)`.
-/

theorem factorTwoEndpointChannelPhase_intrinsicSix_nonnegative
    (c0 c2 c4 c1 c3 c5 a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4)
      (factorTwoIntrinsicSixOddTail c1 c3 c5) a b :=
  factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_unbalanced_static
    factorTwoIntrinsicSixUnbalancedStaticPlusNonnegative
    factorTwoIntrinsicSixUnbalancedStaticMinusNonnegative
    c0 c2 c4 c1 c3 c5 a b hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskCertificateStructural
