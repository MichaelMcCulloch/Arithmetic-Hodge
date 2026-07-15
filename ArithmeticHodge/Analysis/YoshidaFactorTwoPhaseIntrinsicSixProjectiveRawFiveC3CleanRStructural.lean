import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3CleanRSlopesQStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3CleanRSlopesEvenStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3CleanRSlopesAlternatingStructural

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

set_option maxHeartbeats 5000000 in
private theorem cleanRSecant_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    cleanRSecant R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤ (-4 / 100000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hRL hRU hCL hCU hDL hDU hFL hFU haL haU hxL hxU hrL hrU hcL hcU hdL hdU hfL hfU hsuL hsuU hduL hduU hu4L hu4U hsvL hsvU hdvL hdvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  have hq13Slope := cleanRSlopeQ13_lower A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hq11Slope := cleanRSlopeQ11_upper A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hDSlope := cleanRSlopeD_upper A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hCSlope := cleanRSlopeC_upper A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hq33Slope := cleanRSlopeQ33_upper A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hh11Slope := cleanRSlopeH11_upper A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hu4Slope := cleanRSlopeU4_lower A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hdvSlope := cleanRSlopeDv_lower A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hh13Slope := cleanRSlopeH13_lower A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hq13Step : (q13 - cornerQ13) * cleanRSlopeQ13
      R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num [cornerQ13] at ⊢; linarith)
      (by linarith only [hq13Slope])
  have hq11Step : (q11 - cornerQ11) * cleanRSlopeQ11
      R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num [cornerQ11] at ⊢; linarith)
      (by linarith only [hq11Slope])
  have hDStep : (D - 42817 / 1000000) * cleanRSlopeD
      R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith only [hDSlope])
  have hCStep : (C - cornerC) * cleanRSlopeC
      R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num [cornerC] at ⊢; linarith)
      (by linarith only [hCSlope])
  have hq33Step : (q33 - cornerQ33) * cleanRSlopeQ33
      R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num [cornerQ33] at ⊢; linarith)
      (by linarith only [hq33Slope])
  have hh11Step : (h11 - cornerH11) * cleanRSlopeH11
      R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num [cornerH11] at ⊢; linarith)
      (by linarith only [hh11Slope])
  have hu4Step : (u4 - cornerU4) * cleanRSlopeU4
      R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num [cornerU4] at ⊢; linarith)
      (by linarith only [hu4Slope])
  have hdvStep : (dv - cornerDv) * cleanRSlopeDv
      R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num [cornerDv] at ⊢; linarith)
      (by linarith only [hdvSlope])
  have hh13Step : (h13 - cornerH13) * cleanRSlopeH13
      R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num [cornerH13] at ⊢; linarith)
      (by linarith only [hh13Slope])
  have hcorner := cleanRSecant_corner_upper A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have htel := cleanRSecant_telescope R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33
  have hsteps := add_nonpos
    (add_nonpos
      (add_nonpos
        (add_nonpos
          (add_nonpos
            (add_nonpos
              (add_nonpos
                (add_nonpos hq13Step hq11Step)
                hDStep)
              hCStep)
            hq33Step)
          hh11Step)
        hu4Step)
      hdvStep)
    hh13Step
  calc
    cleanRSecant R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤
      cleanRSecant R cornerC (42817 / 1000000) F a x r c d f
        su du cornerU4 sv cornerDv v4
          cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 h33 := by
        rw [← sub_nonpos, htel]
        exact hsteps
    _ ≤ (-4 / 100000 : ℝ) := hcorner

set_option maxHeartbeats 3000000 in
theorem correlated_clean_unfix_R
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    correlatedCoefficientThree
        cornerA cornerX cornerR C D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤
      correlatedCoefficientThree
        cornerA cornerX R C D F
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
  let g : ℝ → ℝ := fun z ↦ correlatedCoefficientThree
    cornerA cornerX z C D F
    a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33
  have hslope := cleanRSecant_upper A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hsecCap : quadraticSecant g R cornerR ≤ (-4 / 100000 : ℝ) := by
    simpa only [g, cleanRSecant] using hslope
  have hsec : quadraticSecant g R cornerR ≤ (0 : ℝ) :=
    hsecCap.trans (by norm_num)
  have hid : g R - g cornerR =
      (R - cornerR) * quadraticSecant g R cornerR := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_upper_endpoint g R cornerR
    (by simpa only [cornerR] using hbox.R_mem.2) hsec hid

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural
