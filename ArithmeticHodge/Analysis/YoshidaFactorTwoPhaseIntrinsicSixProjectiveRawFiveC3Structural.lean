import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3CleanRStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3CleanXStructural

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural

noncomputable section

open Polynomial
open CenteredOddOneThreeEnergy
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural positivity of the third raw five-mode coefficient

This coefficient is the endpoint reversal of the second convolution layer.
The proof keeps that reversal at the level of the even adjugate pencil and
the odd endpoint pencil; it does not enumerate values of the projective
parameter.
-/

/-- The third mixed coefficient of the raw five-mode determinant is
nonnegative. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_three_nonneg :
    0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 3 := by
  rw [coefficient_three_eq_correlated]
  let A := cleanStrong
  let X := cleanSkew
  let R := cleanCrossSum
  let C := cleanWeak
  let D := cleanCrossDifference
  let F := cleanP4
  let a := perturbStrong
  let x := perturbSkew
  let r := perturbCrossSum
  let c := perturbWeak
  let d := perturbCrossDifference
  let f := perturbP4
  let su := u0 + u2
  let du := u0 - u2
  let sv := v0 + v2
  let dv := v0 - v2
  let q11 := yoshidaEndpointOddLowGram11
  let q13 := yoshidaEndpointOddLowGram13
  let q33 := yoshidaEndpointOddLowGram33
  let h11 := factorTwoCenteredSymmetricPerturbation centeredP1
  let h13 := factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3
  let h33 := factorTwoCenteredSymmetricPerturbation centeredP3
  change 0 ≤ correlatedCoefficientThree
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33
  have hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
    simpa only [A, X, R, C, D, F, a, x, r, c, d, f, su, du, sv, dv,
      q11, q13, q33, h11, h13, h33] using actual_correlated_box
  have hterminal : 0 ≤
      tailOddFace corner_a corner_x corner_r cornerU4 cornerV4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 := by
    unfold tailOddFace
    exact ((by norm_num : (0 : ℝ) < 15 / 1000000).trans
      correlated_corner_gt_fifteen_millionths).le
  have htail := correlated_tail_five_lower a x r u4 v4
    hbox.a_mem.1 hbox.a_mem.2 hbox.x_mem.1 hbox.x_mem.2
    hbox.r_mem.1 hbox.r_mem.2 hbox.u4_mem.1 hbox.u4_mem.2
    hbox.v4_mem.1 hbox.v4_mem.2
  have hodd := correlated_odd_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hdvStep := correlated_alternating_unfix_dv
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsvStep := correlated_alternating_unfix_sv
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hduStep := correlated_alternating_unfix_du
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsuStep := correlated_alternating_unfix_su
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hfStep := correlated_even_unfix_f
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hdStep := correlated_even_unfix_d
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hcStep := correlated_even_unfix_c
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hFStep := correlated_clean_unfix_F
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hDStep := correlated_clean_unfix_D
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hCStep := correlated_clean_unfix_C
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hRStep := correlated_clean_unfix_R
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hXStep := correlated_clean_unfix_X
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hAStep := correlated_A_lower_endpoint
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  calc
    0 ≤ tailOddFace corner_a corner_x corner_r cornerU4 cornerV4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 := hterminal
    _ ≤ tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 := htail
    _ ≤ tailOddFace a x r u4 v4 q11 q13 q33 h11 h13 h33 := hodd
    _ = alternatingFace a x r cornerSu cornerDu u4 cornerSv cornerDv v4
        q11 q13 q33 h11 h13 h33 := rfl
    _ ≤ alternatingFace a x r cornerSu cornerDu u4 cornerSv dv v4
        q11 q13 q33 h11 h13 h33 := hdvStep
    _ ≤ alternatingFace a x r cornerSu cornerDu u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := hsvStep
    _ ≤ alternatingFace a x r cornerSu du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := hduStep
    _ ≤ alternatingFace a x r su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := hsuStep
    _ = perturbFFace a x r corner_f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := rfl
    _ ≤ perturbFFace a x r f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := hfStep
    _ = perturbDFace a x r corner_d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := rfl
    _ ≤ perturbDFace a x r d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := hdStep
    _ = perturbCFace a x r corner_c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := rfl
    _ ≤ perturbCFace a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := hcStep
    _ = correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := rfl
    _ ≤ correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := hFStep
    _ ≤ correlatedCoefficientThree
        cornerA cornerX cornerR cornerC D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := hDStep
    _ ≤ correlatedCoefficientThree
        cornerA cornerX cornerR C D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := hCStep
    _ ≤ correlatedCoefficientThree
        cornerA cornerX R C D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := hRStep
    _ ≤ correlatedCoefficientThree
        cornerA X R C D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := hXStep
    _ ≤ correlatedCoefficientThree
        A X R C D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := hAStep

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural
