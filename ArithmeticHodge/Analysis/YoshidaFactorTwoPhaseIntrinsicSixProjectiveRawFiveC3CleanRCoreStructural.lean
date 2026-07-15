import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3CleanFDCStructural

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

def cleanRSecant
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ correlatedCoefficientThree
      cornerA cornerX z C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33)
    R cornerR

def cleanRSlopeQ13
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ cleanRSecant R C D F a x r c d f
      su du u4 sv dv v4 q11 z q33 h11 h13 h33)
    q13 cornerQ13

def cleanRSlopeQ11
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ cleanRSecant R C D F a x r c d f
      su du u4 sv dv v4 z cornerQ13 q33 h11 h13 h33)
    q11 cornerQ11

def cleanRSlopeD
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ cleanRSecant R C z F a x r c d f
      su du u4 sv dv v4 cornerQ11 cornerQ13 q33 h11 h13 h33)
    D (42817 / 1000000)

def cleanRSlopeC
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ cleanRSecant R z (42817 / 1000000) F a x r c d f
      su du u4 sv dv v4 cornerQ11 cornerQ13 q33 h11 h13 h33)
    C cornerC

def cleanRSlopeQ33
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ cleanRSecant R cornerC (42817 / 1000000) F a x r c d f
      su du u4 sv dv v4 cornerQ11 cornerQ13 z h11 h13 h33)
    q33 cornerQ33

def cleanRSlopeH11
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ cleanRSecant R cornerC (42817 / 1000000) F a x r c d f
      su du u4 sv dv v4 cornerQ11 cornerQ13 cornerQ33 z h13 h33)
    h11 cornerH11

def cleanRSlopeU4
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ cleanRSecant R cornerC (42817 / 1000000) F a x r c d f
      su du z sv dv v4 cornerQ11 cornerQ13 cornerQ33 cornerH11 h13 h33)
    u4 cornerU4

def cleanRSlopeDv
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ cleanRSecant R cornerC (42817 / 1000000) F a x r c d f
      su du cornerU4 sv z v4 cornerQ11 cornerQ13 cornerQ33
        cornerH11 h13 h33)
    dv cornerDv

def cleanRSlopeH13
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ cleanRSecant R cornerC (42817 / 1000000) F a x r c d f
      su du cornerU4 sv cornerDv v4 cornerQ11 cornerQ13 cornerQ33
        cornerH11 z h33)
    h13 cornerH13

set_option maxHeartbeats 5000000 in
theorem cleanRSecant_telescope
    (R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    cleanRSecant R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 -
      cleanRSecant R cornerC (42817 / 1000000) F a x r c d f
        su du cornerU4 sv cornerDv v4
          cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 h33 =
      (q13 - cornerQ13) * cleanRSlopeQ13 R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 +
      (q11 - cornerQ11) * cleanRSlopeQ11 R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 +
      (D - 42817 / 1000000) * cleanRSlopeD R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 +
      (C - cornerC) * cleanRSlopeC R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 +
      (q33 - cornerQ33) * cleanRSlopeQ33 R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 +
      (h11 - cornerH11) * cleanRSlopeH11 R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 +
      (u4 - cornerU4) * cleanRSlopeU4 R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 +
      (dv - cornerDv) * cleanRSlopeDv R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 +
      (h13 - cornerH13) * cleanRSlopeH13 R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
  unfold cleanRSlopeQ13 cleanRSlopeQ11 cleanRSlopeD cleanRSlopeC
    cleanRSlopeQ33 cleanRSlopeH11 cleanRSlopeU4 cleanRSlopeDv
    cleanRSlopeH13 cleanRSecant quadraticSecant correlatedCoefficientThree
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
    alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural
