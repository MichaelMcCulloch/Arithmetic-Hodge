import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP3SinhStructural
import ArithmeticHodge.Analysis.YoshidaEndpointOddOneThreeRawPolarization
import ArithmeticHodge.Analysis.YoshidaDiagonalFineBase
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCarleman

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural

noncomputable section

open MeasureTheory Real Set
open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointRegularCorrelation
open YoshidaConstantBounds
open YoshidaDiagonalFineBase
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicOddP3SinhStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddLowEndpointPositive
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaFactorTwoStructuralConstantBounds
open YoshidaRegularKernelBound
open YoshidaRegularKernelSchur

/-!
# The correlated negative-endpoint odd `P5` completion profile

The final positive static determinant does not need independent boxes for the
six entries of its odd `P1/P3/P5` block.  Its border column is the single
profile

`r = -(10319/4800) P1 + (15/8) P3 + P5`.

The definitions below form the three required endpoint quantities and their
correlation polynomials before any estimate is taken.  This is the
cancellation-preserving input for the final bordered Schur estimate.
-/

def plusP5OddCompletionProfile (x : ℝ) : ℝ :=
  (-10319 / 4800 : ℝ) * centeredP1 x +
    (15 / 8 : ℝ) * centeredP3 x + factorTwoCenteredP5 x

def plusP5OddBorderProfile (x : ℝ) : ℝ :=
  (-359 / 360 : ℝ) * centeredP1 x + centeredP3 x

theorem plusP5OddCompletionProfile_polynomial (x : ℝ) :
    plusP5OddCompletionProfile x =
      (63 / 8 : ℝ) * x ^ 5 - (65 / 16 : ℝ) * x ^ 3 -
        (14819 / 4800 : ℝ) * x := by
  unfold plusP5OddCompletionProfile centeredP1 centeredP3
    factorTwoCenteredP5
  ring

theorem plusP5OddBorderProfile_polynomial (x : ℝ) :
    plusP5OddBorderProfile x =
      (5 / 2 : ℝ) * x ^ 3 - (899 / 360 : ℝ) * x := by
  unfold plusP5OddBorderProfile centeredP1 centeredP3
  ring

theorem continuous_plusP5OddCompletionProfile :
    Continuous plusP5OddCompletionProfile := by
  unfold plusP5OddCompletionProfile centeredP1 centeredP3
    factorTwoCenteredP5
  fun_prop

theorem continuous_plusP5OddBorderProfile :
    Continuous plusP5OddBorderProfile := by
  unfold plusP5OddBorderProfile centeredP1 centeredP3
  fun_prop

def plusP5OddB1 : ℝ :=
  (-10319 / 4800 : ℝ) * factorTwoIntrinsicSixUnbalancedOMinus11 +
    (15 / 8 : ℝ) * factorTwoIntrinsicSixUnbalancedOMinus13 +
    factorTwoIntrinsicSixUnbalancedOMinus15

def plusP5OddB4 : ℝ :=
  (3704521 / 1728000 : ℝ) * factorTwoIntrinsicSixUnbalancedOMinus11 -
    (9647 / 2400 : ℝ) * factorTwoIntrinsicSixUnbalancedOMinus13 +
    (15 / 8 : ℝ) * factorTwoIntrinsicSixUnbalancedOMinus33 -
    (359 / 360 : ℝ) * factorTwoIntrinsicSixUnbalancedOMinus15 +
    factorTwoIntrinsicSixUnbalancedOMinus35

def plusP5OddQ : ℝ :=
  (106481761 / 23040000 : ℝ) *
      factorTwoIntrinsicSixUnbalancedOMinus11 -
    (10319 / 1280 : ℝ) * factorTwoIntrinsicSixUnbalancedOMinus13 +
    (225 / 64 : ℝ) * factorTwoIntrinsicSixUnbalancedOMinus33 -
    (10319 / 2400 : ℝ) * factorTwoIntrinsicSixUnbalancedOMinus15 +
    (15 / 4 : ℝ) * factorTwoIntrinsicSixUnbalancedOMinus35 +
    factorTwoIntrinsicSixUnbalancedOMinus55

def plusP5OddB1Correlation (t : ℝ) : ℝ :=
  (-10319 / 4800 : ℝ) * oddStructuralCorrelation11 t +
    (15 / 8 : ℝ) * oddStructuralCorrelation13 t +
    oddP5Correlation15 t

def plusP5OddB4Correlation (t : ℝ) : ℝ :=
  (3704521 / 1728000 : ℝ) * oddStructuralCorrelation11 t -
    (9647 / 2400 : ℝ) * oddStructuralCorrelation13 t +
    (15 / 8 : ℝ) * oddStructuralCorrelation33 t -
    (359 / 360 : ℝ) * oddP5Correlation15 t + oddP5Correlation35 t

def plusP5OddQCorrelation (t : ℝ) : ℝ :=
  (106481761 / 23040000 : ℝ) * oddStructuralCorrelation11 t -
    (10319 / 1280 : ℝ) * oddStructuralCorrelation13 t +
    (225 / 64 : ℝ) * oddStructuralCorrelation33 t -
    (10319 / 2400 : ℝ) * oddP5Correlation15 t +
    (15 / 4 : ℝ) * oddP5Correlation35 t + oddP5Correlation55 t

theorem plusP5OddB1Correlation_polynomial (t : ℝ) :
    plusP5OddB1Correlation t =
      (-10319 / 7200 : ℝ) - (3481 / 4800 : ℝ) * t +
        (187 / 16 : ℝ) * t ^ 2 - (523319 / 28800 : ℝ) * t ^ 3 +
        (105 / 8 : ℝ) * t ^ 4 - (265 / 64 : ℝ) * t ^ 5 +
        (3 / 16 : ℝ) * t ^ 7 := by
  unfold plusP5OddB1Correlation oddStructuralCorrelation11
    oddStructuralCorrelation13 oddP5Correlation15
  ring

theorem plusP5OddB4Correlation_polynomial (t : ℝ) :
    plusP5OddB4Correlation t =
      (35651647 / 18144000 : ℝ) - (3481 / 1728000 : ℝ) * t -
        (7217 / 576 : ℝ) * t ^ 2 +
        (188905081 / 10368000 : ℝ) * t ^ 3 -
        (2513 / 192 : ℝ) * t ^ 4 +
        (289859 / 57600 : ℝ) * t ^ 5 -
        (1817 / 3360 : ℝ) * t ^ 7 + (5 / 128 : ℝ) * t ^ 9 := by
  unfold plusP5OddB4Correlation oddStructuralCorrelation11
    oddStructuralCorrelation13 oddStructuralCorrelation33 oddP5Correlation15
    oddP5Correlation35
  ring

theorem plusP5OddQCorrelation_polynomial (t : ℝ) :
    plusP5OddQCorrelation t =
      (11355935597 / 2661120000 : ℝ) -
        (12117361 / 23040000 : ℝ) * t -
        (1281653 / 38400 : ℝ) * t ^ 2 +
        (8933375761 / 138240000 : ℝ) * t ^ 3 -
        (72233 / 1280 : ℝ) * t ^ 4 +
        (641767 / 30720 : ℝ) * t ^ 5 -
        (186341 / 179200 : ℝ) * t ^ 7 -
        (65 / 512 : ℝ) * t ^ 9 + (63 / 2816 : ℝ) * t ^ 11 := by
  unfold plusP5OddQCorrelation oddStructuralCorrelation11
    oddStructuralCorrelation13 oddStructuralCorrelation33 oddP5Correlation15
    oddP5Correlation35 oddP5Correlation55
  ring

theorem continuous_plusP5OddB1Correlation :
    Continuous plusP5OddB1Correlation := by
  unfold plusP5OddB1Correlation oddStructuralCorrelation11
    oddStructuralCorrelation13 oddP5Correlation15
  fun_prop

theorem continuous_plusP5OddB4Correlation :
    Continuous plusP5OddB4Correlation := by
  unfold plusP5OddB4Correlation oddStructuralCorrelation11
    oddStructuralCorrelation13 oddStructuralCorrelation33 oddP5Correlation15
    oddP5Correlation35
  fun_prop

theorem continuous_plusP5OddQCorrelation :
    Continuous plusP5OddQCorrelation := by
  unfold plusP5OddQCorrelation oddStructuralCorrelation11
    oddStructuralCorrelation13 oddStructuralCorrelation33 oddP5Correlation15
    oddP5Correlation35 oddP5Correlation55
  fun_prop

/-! ## Exact profile-correlation bridges -/

private theorem factorTwoCenteredCorrelationBilinear_add_left_profile
    (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear (u + v) w t =
      factorTwoCenteredCorrelationBilinear u w t +
        factorTwoCenteredCorrelationBilinear v w t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_add_left u v w hu hv hw t,
    factorTwoCenteredCrossCorrelation_add_right w u v hw hu hv t]
  ring

private theorem factorTwoCenteredCorrelationBilinear_add_right_profile
    (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hw : Continuous w) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear u (v + w) t =
      factorTwoCenteredCorrelationBilinear u v t +
        factorTwoCenteredCorrelationBilinear u w t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_add_right u v w hu hv hw t,
    factorTwoCenteredCrossCorrelation_add_left v w u hv hw hu t]
  ring

private theorem factorTwoCenteredCorrelationBilinear_smul_left_profile
    (c : ℝ) (u v : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear (c • u) v t =
      c * factorTwoCenteredCorrelationBilinear u v t := by
  simpa using
    factorTwoCenteredCorrelationBilinear_smul_smul c 1 u v t

private theorem factorTwoCenteredCorrelationBilinear_smul_right_profile
    (c : ℝ) (u v : ℝ → ℝ) (t : ℝ) :
    factorTwoCenteredCorrelationBilinear u (c • v) t =
      c * factorTwoCenteredCorrelationBilinear u v t := by
  simpa using
    factorTwoCenteredCorrelationBilinear_smul_smul 1 c u v t

private theorem plusP5OddCompletionProfile_eq_smul_add :
    plusP5OddCompletionProfile =
      (-10319 / 4800 : ℝ) • centeredP1 +
        (15 / 8 : ℝ) • centeredP3 + factorTwoCenteredP5 := by
  funext x
  simp only [plusP5OddCompletionProfile, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

private theorem plusP5OddBorderProfile_eq_smul_add :
    plusP5OddBorderProfile =
      (-359 / 360 : ℝ) • centeredP1 + centeredP3 := by
  funext x
  simp only [plusP5OddBorderProfile, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem factorTwoCenteredCorrelationBilinear_p1_plusP5OddCompletionProfile
    (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP1
        plusP5OddCompletionProfile t =
      plusP5OddB1Correlation t := by
  have h1 : Continuous centeredP1 := by unfold centeredP1; fun_prop
  have h3 : Continuous centeredP3 := by unfold centeredP3; fun_prop
  have h5 : Continuous factorTwoCenteredP5 :=
    continuous_factorTwoCenteredP5
  rw [plusP5OddCompletionProfile_eq_smul_add,
    factorTwoCenteredCorrelationBilinear_add_right_profile centeredP1
      ((-10319 / 4800 : ℝ) • centeredP1 +
        (15 / 8 : ℝ) • centeredP3) factorTwoCenteredP5 h1
      ((h1.const_smul (-10319 / 4800 : ℝ)).add
        (h3.const_smul (15 / 8 : ℝ))) h5 t,
    factorTwoCenteredCorrelationBilinear_add_right_profile centeredP1
      ((-10319 / 4800 : ℝ) • centeredP1)
      ((15 / 8 : ℝ) • centeredP3) h1
      (h1.const_smul (-10319 / 4800 : ℝ))
      (h3.const_smul (15 / 8 : ℝ)) t,
    factorTwoCenteredCorrelationBilinear_smul_right_profile,
    factorTwoCenteredCorrelationBilinear_smul_right_profile,
    factorTwoCenteredCorrelationBilinear_p1_p1,
    factorTwoCenteredCorrelationBilinear_p1_p3,
    factorTwoCenteredCorrelationBilinear_p1_p5]
  unfold plusP5OddB1Correlation oddStructuralCorrelation11
    oddStructuralCorrelation13
  ring

private theorem factorTwoCenteredCorrelationBilinear_p3_plusP5OddCompletionProfile
    (t : ℝ) :
    factorTwoCenteredCorrelationBilinear centeredP3
        plusP5OddCompletionProfile t =
      (-10319 / 4800 : ℝ) * oddStructuralCorrelation13 t +
        (15 / 8 : ℝ) * oddStructuralCorrelation33 t +
        oddP5Correlation35 t := by
  have h1 : Continuous centeredP1 := by unfold centeredP1; fun_prop
  have h3 : Continuous centeredP3 := by unfold centeredP3; fun_prop
  have h5 : Continuous factorTwoCenteredP5 :=
    continuous_factorTwoCenteredP5
  rw [plusP5OddCompletionProfile_eq_smul_add,
    factorTwoCenteredCorrelationBilinear_add_right_profile centeredP3
      ((-10319 / 4800 : ℝ) • centeredP1 +
        (15 / 8 : ℝ) • centeredP3) factorTwoCenteredP5 h3
      ((h1.const_smul (-10319 / 4800 : ℝ)).add
        (h3.const_smul (15 / 8 : ℝ))) h5 t,
    factorTwoCenteredCorrelationBilinear_add_right_profile centeredP3
      ((-10319 / 4800 : ℝ) • centeredP1)
      ((15 / 8 : ℝ) • centeredP3) h3
      (h1.const_smul (-10319 / 4800 : ℝ))
      (h3.const_smul (15 / 8 : ℝ)) t,
    factorTwoCenteredCorrelationBilinear_smul_right_profile,
    factorTwoCenteredCorrelationBilinear_smul_right_profile,
    factorTwoCenteredCorrelationBilinear_comm centeredP3 centeredP1,
    factorTwoCenteredCorrelationBilinear_p1_p3,
    factorTwoCenteredCorrelationBilinear_p3_p3,
    factorTwoCenteredCorrelationBilinear_p3_p5]
  unfold oddStructuralCorrelation13 oddStructuralCorrelation33
  ring

theorem factorTwoCenteredCorrelationBilinear_plusP5OddProfiles
    (t : ℝ) :
    factorTwoCenteredCorrelationBilinear plusP5OddBorderProfile
        plusP5OddCompletionProfile t =
      plusP5OddB4Correlation t := by
  have h1 : Continuous centeredP1 := by unfold centeredP1; fun_prop
  have h3 : Continuous centeredP3 := by unfold centeredP3; fun_prop
  have hr : Continuous plusP5OddCompletionProfile :=
    continuous_plusP5OddCompletionProfile
  rw [plusP5OddBorderProfile_eq_smul_add,
    factorTwoCenteredCorrelationBilinear_add_left_profile
      ((-359 / 360 : ℝ) • centeredP1) centeredP3
      plusP5OddCompletionProfile (h1.const_smul (-359 / 360 : ℝ)) h3 hr t,
    factorTwoCenteredCorrelationBilinear_smul_left_profile,
    factorTwoCenteredCorrelationBilinear_p1_plusP5OddCompletionProfile,
    factorTwoCenteredCorrelationBilinear_p3_plusP5OddCompletionProfile]
  unfold plusP5OddB1Correlation plusP5OddB4Correlation
  ring

theorem centeredEndpointCorrelation_plusP5OddCompletionProfile
    (t : ℝ) :
    centeredEndpointCorrelation plusP5OddCompletionProfile t =
      plusP5OddQCorrelation t := by
  let q : ℝ → ℝ := factorTwoOddStructuralLowProfile
    (-10319 / 4800) (15 / 8)
  have hq : Continuous q := by
    dsimp only [q]
    exact continuous_factorTwoOddStructuralLowProfile _ _
  have h5 : Continuous factorTwoCenteredP5 :=
    continuous_factorTwoCenteredP5
  have hprofile :
      plusP5OddCompletionProfile = q + factorTwoCenteredP5 := by
    funext x
    dsimp only [q]
    unfold plusP5OddCompletionProfile factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply]
  have hqprofile :
      q = (-10319 / 4800 : ℝ) • centeredP1 +
        (15 / 8 : ℝ) • centeredP3 := by
    funext x
    dsimp only [q]
    unfold factorTwoOddStructuralLowProfile
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hprofile, centeredEndpointCorrelation_add q factorTwoCenteredP5 hq h5 t,
    centeredEndpointCorrelation_oddStructuralProfile,
    hqprofile,
    factorTwoCenteredCorrelationBilinear_add_left_profile
      ((-10319 / 4800 : ℝ) • centeredP1)
      ((15 / 8 : ℝ) • centeredP3) factorTwoCenteredP5
      ((by unfold centeredP1; fun_prop : Continuous centeredP1).const_smul
        (-10319 / 4800 : ℝ))
      ((by unfold centeredP3; fun_prop : Continuous centeredP3).const_smul
        (15 / 8 : ℝ)) h5 t,
    factorTwoCenteredCorrelationBilinear_smul_left_profile,
    factorTwoCenteredCorrelationBilinear_smul_left_profile,
    factorTwoCenteredCorrelationBilinear_p1_p5,
    factorTwoCenteredCorrelationBilinear_p3_p5,
    centeredEndpointCorrelation_p5]
  unfold plusP5OddQCorrelation
  ring

/-! ## Linearity of the single pole-free profile error -/

private theorem poleFreeAnalyticError_add_profile
    (C D : ℝ → ℝ) (hC : Continuous C) (hD : Continuous D) :
    poleFreeAnalyticError (C + D) =
      poleFreeAnalyticError C + poleFreeAnalyticError D := by
  have hCI := intervalIntegrable_poleFreeAnalyticError C hC
  have hDI := intervalIntegrable_poleFreeAnalyticError D hD
  unfold poleFreeAnalyticError
  rw [show (fun t : ℝ ↦
      (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) *
        (C + D) t) =
      fun t ↦
        (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t +
          (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * D t by
    funext t
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add hCI hDI]

private theorem poleFreeAnalyticError_const_mul_profile
    (c : ℝ) (C : ℝ → ℝ) :
    poleFreeAnalyticError (fun t ↦ c * C t) =
      c * poleFreeAnalyticError C := by
  unfold poleFreeAnalyticError
  rw [show (fun t : ℝ ↦
      (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) *
        (c * C t)) =
      fun t ↦ c *
        ((oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]

theorem poleFreeAnalyticError_plusP5OddB1Correlation_eq :
    poleFreeAnalyticError plusP5OddB1Correlation =
      (-10319 / 4800 : ℝ) *
          poleFreeAnalyticError oddStructuralCorrelation11 +
        (15 / 8 : ℝ) *
          poleFreeAnalyticError oddStructuralCorrelation13 +
        poleFreeAnalyticError oddP5Correlation15 := by
  let C11 : ℝ → ℝ := fun t ↦
    (-10319 / 4800 : ℝ) * oddStructuralCorrelation11 t
  let C13 : ℝ → ℝ := fun t ↦
    (15 / 8 : ℝ) * oddStructuralCorrelation13 t
  have h11 : Continuous oddStructuralCorrelation11 := by
    unfold oddStructuralCorrelation11
    fun_prop
  have h13 : Continuous oddStructuralCorrelation13 := by
    unfold oddStructuralCorrelation13
    fun_prop
  have h15 : Continuous oddP5Correlation15 := by
    unfold oddP5Correlation15
    fun_prop
  have hC11 : Continuous C11 := by
    dsimp only [C11]
    exact continuous_const.mul h11
  have hC13 : Continuous C13 := by
    dsimp only [C13]
    exact continuous_const.mul h13
  have hprofile : plusP5OddB1Correlation = C11 + C13 + oddP5Correlation15 := by
    funext t
    dsimp only [C11, C13]
    simp only [Pi.add_apply]
    unfold plusP5OddB1Correlation
    ring
  rw [hprofile,
    poleFreeAnalyticError_add_profile (C11 + C13) oddP5Correlation15
      (hC11.add hC13) h15,
    poleFreeAnalyticError_add_profile C11 C13 hC11 hC13]
  dsimp only [C11, C13]
  rw [poleFreeAnalyticError_const_mul_profile,
    poleFreeAnalyticError_const_mul_profile]

theorem poleFreeAnalyticError_plusP5OddB4Correlation_eq :
    poleFreeAnalyticError plusP5OddB4Correlation =
      (3704521 / 1728000 : ℝ) *
          poleFreeAnalyticError oddStructuralCorrelation11 -
        (9647 / 2400 : ℝ) *
          poleFreeAnalyticError oddStructuralCorrelation13 +
        (15 / 8 : ℝ) *
          poleFreeAnalyticError oddStructuralCorrelation33 -
        (359 / 360 : ℝ) * poleFreeAnalyticError oddP5Correlation15 +
        poleFreeAnalyticError oddP5Correlation35 := by
  let C11 : ℝ → ℝ := fun t ↦
    (3704521 / 1728000 : ℝ) * oddStructuralCorrelation11 t
  let C13 : ℝ → ℝ := fun t ↦
    (-9647 / 2400 : ℝ) * oddStructuralCorrelation13 t
  let C33 : ℝ → ℝ := fun t ↦
    (15 / 8 : ℝ) * oddStructuralCorrelation33 t
  let C15 : ℝ → ℝ := fun t ↦
    (-359 / 360 : ℝ) * oddP5Correlation15 t
  have h11 : Continuous oddStructuralCorrelation11 := by
    unfold oddStructuralCorrelation11
    fun_prop
  have h13 : Continuous oddStructuralCorrelation13 := by
    unfold oddStructuralCorrelation13
    fun_prop
  have h33 : Continuous oddStructuralCorrelation33 := by
    unfold oddStructuralCorrelation33
    fun_prop
  have h15 : Continuous oddP5Correlation15 := by
    unfold oddP5Correlation15
    fun_prop
  have h35 : Continuous oddP5Correlation35 := by
    unfold oddP5Correlation35
    fun_prop
  have hC11 : Continuous C11 := by
    dsimp only [C11]
    exact continuous_const.mul h11
  have hC13 : Continuous C13 := by
    dsimp only [C13]
    exact continuous_const.mul h13
  have hC33 : Continuous C33 := by
    dsimp only [C33]
    exact continuous_const.mul h33
  have hC15 : Continuous C15 := by
    dsimp only [C15]
    exact continuous_const.mul h15
  have hprofile :
      plusP5OddB4Correlation = C11 + C13 + C33 + C15 + oddP5Correlation35 := by
    funext t
    dsimp only [C11, C13, C33, C15]
    simp only [Pi.add_apply]
    unfold plusP5OddB4Correlation
    ring
  rw [hprofile,
    poleFreeAnalyticError_add_profile (C11 + C13 + C33 + C15)
      oddP5Correlation35 (((hC11.add hC13).add hC33).add hC15) h35,
    poleFreeAnalyticError_add_profile (C11 + C13 + C33) C15
      ((hC11.add hC13).add hC33) hC15,
    poleFreeAnalyticError_add_profile (C11 + C13) C33
      (hC11.add hC13) hC33,
    poleFreeAnalyticError_add_profile C11 C13 hC11 hC13]
  dsimp only [C11, C13, C33, C15]
  repeat rw [poleFreeAnalyticError_const_mul_profile]
  ring

theorem poleFreeAnalyticError_plusP5OddQCorrelation_eq :
    poleFreeAnalyticError plusP5OddQCorrelation =
      (106481761 / 23040000 : ℝ) *
          poleFreeAnalyticError oddStructuralCorrelation11 -
        (10319 / 1280 : ℝ) *
          poleFreeAnalyticError oddStructuralCorrelation13 +
        (225 / 64 : ℝ) *
          poleFreeAnalyticError oddStructuralCorrelation33 -
        (10319 / 2400 : ℝ) * poleFreeAnalyticError oddP5Correlation15 +
        (15 / 4 : ℝ) * poleFreeAnalyticError oddP5Correlation35 +
        poleFreeAnalyticError oddP5Correlation55 := by
  let C11 : ℝ → ℝ := fun t ↦
    (106481761 / 23040000 : ℝ) * oddStructuralCorrelation11 t
  let C13 : ℝ → ℝ := fun t ↦
    (-10319 / 1280 : ℝ) * oddStructuralCorrelation13 t
  let C33 : ℝ → ℝ := fun t ↦
    (225 / 64 : ℝ) * oddStructuralCorrelation33 t
  let C15 : ℝ → ℝ := fun t ↦
    (-10319 / 2400 : ℝ) * oddP5Correlation15 t
  let C35 : ℝ → ℝ := fun t ↦
    (15 / 4 : ℝ) * oddP5Correlation35 t
  have h11 : Continuous oddStructuralCorrelation11 := by
    unfold oddStructuralCorrelation11
    fun_prop
  have h13 : Continuous oddStructuralCorrelation13 := by
    unfold oddStructuralCorrelation13
    fun_prop
  have h33 : Continuous oddStructuralCorrelation33 := by
    unfold oddStructuralCorrelation33
    fun_prop
  have h15 : Continuous oddP5Correlation15 := by
    unfold oddP5Correlation15
    fun_prop
  have h35 : Continuous oddP5Correlation35 := by
    unfold oddP5Correlation35
    fun_prop
  have h55 : Continuous oddP5Correlation55 :=
    continuous_oddP5Correlation55
  have hC11 : Continuous C11 := by
    dsimp only [C11]
    exact continuous_const.mul h11
  have hC13 : Continuous C13 := by
    dsimp only [C13]
    exact continuous_const.mul h13
  have hC33 : Continuous C33 := by
    dsimp only [C33]
    exact continuous_const.mul h33
  have hC15 : Continuous C15 := by
    dsimp only [C15]
    exact continuous_const.mul h15
  have hC35 : Continuous C35 := by
    dsimp only [C35]
    exact continuous_const.mul h35
  have hprofile :
      plusP5OddQCorrelation =
        C11 + C13 + C33 + C15 + C35 + oddP5Correlation55 := by
    funext t
    dsimp only [C11, C13, C33, C15, C35]
    simp only [Pi.add_apply]
    unfold plusP5OddQCorrelation
    ring
  rw [hprofile,
    poleFreeAnalyticError_add_profile (C11 + C13 + C33 + C15 + C35)
      oddP5Correlation55
      ((((hC11.add hC13).add hC33).add hC15).add hC35) h55,
    poleFreeAnalyticError_add_profile (C11 + C13 + C33 + C15) C35
      (((hC11.add hC13).add hC33).add hC15) hC35,
    poleFreeAnalyticError_add_profile (C11 + C13 + C33) C15
      ((hC11.add hC13).add hC33) hC15,
    poleFreeAnalyticError_add_profile (C11 + C13) C33
      (hC11.add hC13) hC33,
    poleFreeAnalyticError_add_profile C11 C13 hC11 hC13]
  dsimp only [C11, C13, C33, C15, C35]
  repeat rw [poleFreeAnalyticError_const_mul_profile]
  ring

/-! ## Exact negative-endpoint B1 profile assembly -/

private theorem oddStructuralRegularError11_sharp_expansion :
    oddStructuralRegularError oddStructuralCorrelation11 =
      poleFreeAnalyticError oddStructuralCorrelation11 + oddPolynomialMoment11 := by
  have h := evenStructuralRegularError_eq_analytic_add_polynomial
    oddStructuralCorrelation11 (by unfold oddStructuralCorrelation11; fun_prop)
  rw [integral_polynomialDifference_mul_oddCorrelations.1] at h
  simpa [evenStructuralRegularError, oddStructuralRegularError] using h

private theorem oddStructuralRegularError13_sharp_expansion :
    oddStructuralRegularError oddStructuralCorrelation13 =
      poleFreeAnalyticError oddStructuralCorrelation13 + oddPolynomialMoment13 := by
  have h := evenStructuralRegularError_eq_analytic_add_polynomial
    oddStructuralCorrelation13 (by unfold oddStructuralCorrelation13; fun_prop)
  rw [integral_polynomialDifference_mul_oddCorrelations.2.1] at h
  simpa [evenStructuralRegularError, oddStructuralRegularError] using h

def plusP5OddCompletionSinhMoment : ℝ :=
  (-10319 / 4800 : ℝ) * oddCleanSinhMoment1 +
    (15 / 8 : ℝ) * oddCleanSinhMoment3 + oddP5CleanSinhMoment

def plusP5OddB1CleanEnvelope : ℝ :=
  (-10319 / 4800 : ℝ) *
      oddCleanRegularEnvelopeError oddStructuralCorrelation11 +
    (15 / 8 : ℝ) *
      oddCleanRegularEnvelopeError oddStructuralCorrelation13 +
    oddP5CleanRegularEnvelopeError15

def plusP5OddB1Base : ℝ :=
  (-10319 / 4800 : ℝ) *
      ((14 / 9 : ℝ) - (2 / 3 : ℝ) *
        (Real.log 2 + yoshidaEndpointScalarMassLoss)) +
    (15 / 8 : ℝ) * (1 / 5 : ℝ) + (1 / 14 : ℝ) -
    yoshidaEndpointA *
      ((-10319 / 4800 : ℝ) * oddCleanRegularPolynomialGram11 +
        (15 / 8 : ℝ) * oddCleanRegularPolynomialGram13 +
        oddP5CleanRegularPolynomial15) -
    ((-10319 / 4800 : ℝ) *
        (oddPolynomialMoment11 - 4 / 375 +
          (2 / 3 - (2 / 3 : ℝ) * Real.log 2) -
          (Real.log 2 / Real.sqrt 2) * (2 / 3)) +
      (15 / 8 : ℝ) *
        (oddPolynomialMoment13 + (7 - 10 * Real.log 2)) +
      (oddP5PolynomialMoment15 + (165 - 238 * Real.log 2)) -
      (Real.log 3 / Real.sqrt 3) * plusP5OddB1Correlation
        (factorTwoPrimeShift / yoshidaEndpointA))

theorem plusP5OddB1_eq_structuralProfile :
    plusP5OddB1 =
      plusP5OddB1Base -
        yoshidaEndpointA * plusP5OddB1CleanEnvelope -
        2 * yoshidaEndpointA * oddCleanSinhMoment1 *
          plusP5OddCompletionSinhMoment -
        poleFreeAnalyticError plusP5OddB1Correlation := by
  rw [poleFreeAnalyticError_plusP5OddB1Correlation_eq]
  unfold plusP5OddB1 plusP5OddB1Base plusP5OddB1CleanEnvelope
    plusP5OddCompletionSinhMoment
    factorTwoIntrinsicSixUnbalancedOMinus11
    factorTwoIntrinsicSixUnbalancedOMinus13
    factorTwoIntrinsicSixUnbalancedOMinus15
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicFourP45Cross15
  rw [yoshidaEndpointOddLowGram11_structural_eq,
    yoshidaEndpointOddLowGram13_structural_eq,
    cleanBilinear_p1_p5_eq,
    factorTwoCenteredSymmetricPerturbation_p1_structural_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_structural_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p1_p5_structural_eq,
    oddStructuralRegularError11_sharp_expansion,
    oddStructuralRegularError13_sharp_expansion]
  unfold plusP5OddB1Correlation
  ring

/-! ## Global Bernstein bounds for the three complete correlations -/

theorem abs_plusP5OddB1Correlation_le_two
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |plusP5OddB1Correlation t| ≤ 2 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  rw [abs_le]
  constructor
  · have h : 0 ≤ (2 : ℝ) + plusP5OddB1Correlation t := by
      rw [show (2 : ℝ) + plusP5OddB1Correlation t =
          (4081 / 7200 : ℝ) * (1 - x) ^ 7 +
            (4531 / 1800 : ℝ) * x * (1 - x) ^ 6 +
            (119881 / 2400 : ℝ) * x ^ 2 * (1 - x) ^ 5 +
            (77819 / 900 : ℝ) * x ^ 3 * (1 - x) ^ 4 +
            (625423 / 7200 : ℝ) * x ^ 4 * (1 - x) ^ 3 +
            (49769 / 600 : ℝ) * x ^ 5 * (1 - x) ^ 2 +
            (30119 / 2400 : ℝ) * x ^ 6 * (1 - x) +
            2 * x ^ 7 by
        rw [plusP5OddB1Correlation_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith
  · have h : 0 ≤ (2 : ℝ) - plusP5OddB1Correlation t := by
      rw [show (2 : ℝ) - plusP5OddB1Correlation t =
          (24719 / 7200 : ℝ) * (1 - x) ^ 7 +
            (45869 / 1800 : ℝ) * x * (1 - x) ^ 6 +
            (81719 / 2400 : ℝ) * x ^ 2 * (1 - x) ^ 5 +
            (48181 / 900 : ℝ) * x ^ 3 * (1 - x) ^ 4 +
            (382577 / 7200 : ℝ) * x ^ 4 * (1 - x) ^ 3 +
            (631 / 600 : ℝ) * x ^ 5 * (1 - x) ^ 2 +
            (37081 / 2400 : ℝ) * x ^ 6 * (1 - x) +
            2 * x ^ 7 by
        rw [plusP5OddB1Correlation_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith

theorem abs_plusP5OddB4Correlation_le_two
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |plusP5OddB4Correlation t| ≤ 2 := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  rw [abs_le]
  constructor
  · have h : 0 ≤ (2 : ℝ) + plusP5OddB4Correlation t := by
      rw [show (2 : ℝ) + plusP5OddB4Correlation t =
          (71939647 / 18144000 : ℝ) * (1 - x) ^ 9 +
            (107897287 / 3024000 : ℝ) * x * (1 - x) ^ 8 +
            (139991707 / 1512000 : ℝ) * x ^ 2 * (1 - x) ^ 7 +
            (165725761 / 1296000 : ℝ) * x ^ 3 * (1 - x) ^ 6 +
            (9678527 / 86400 : ℝ) * x ^ 4 * (1 - x) ^ 5 +
            (6554557 / 144000 : ℝ) * x ^ 5 * (1 - x) ^ 4 +
            (28423009 / 648000 : ℝ) * x ^ 6 * (1 - x) ^ 3 +
            (3809173 / 48000 : ℝ) * x ^ 7 * (1 - x) ^ 2 +
            (15548519 / 864000 : ℝ) * x ^ 8 * (1 - x) +
            2 * x ^ 9 by
        rw [plusP5OddB4Correlation_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith
  · have h : 0 ≤ (2 : ℝ) - plusP5OddB4Correlation t := by
      rw [show (2 : ℝ) - plusP5OddB4Correlation t =
          (636353 / 18144000 : ℝ) * (1 - x) ^ 9 +
            (966713 / 3024000 : ℝ) * x * (1 - x) ^ 8 +
            (77736293 / 1512000 : ℝ) * x ^ 2 * (1 - x) ^ 7 +
            (269730239 / 1296000 : ℝ) * x ^ 3 * (1 - x) ^ 6 +
            (33867073 / 86400 : ℝ) * x ^ 4 * (1 - x) ^ 5 +
            (66021443 / 144000 : ℝ) * x ^ 5 * (1 - x) ^ 4 +
            (189304991 / 648000 : ℝ) * x ^ 6 * (1 - x) ^ 3 +
            (3102827 / 48000 : ℝ) * x ^ 7 * (1 - x) ^ 2 +
            (15555481 / 864000 : ℝ) * x ^ 8 * (1 - x) +
            2 * x ^ 9 by
        rw [plusP5OddB4Correlation_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith

theorem abs_plusP5OddQCorrelation_le_forty_three_tenths
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |plusP5OddQCorrelation t| ≤ (43 / 10 : ℝ) := by
  let x : ℝ := t / 2
  have hx0 : 0 ≤ x := by dsimp only [x]; linarith
  have hx1 : 0 ≤ 1 - x := by dsimp only [x]; linarith
  rw [abs_le]
  constructor
  · have h : 0 ≤ (43 / 10 : ℝ) + plusP5OddQCorrelation t := by
      rw [show (43 / 10 : ℝ) + plusP5OddQCorrelation t =
          (22798751597 / 2661120000 : ℝ) * (1 - x) ^ 11 +
            (2818035877 / 30240000 : ℝ) * x * (1 - x) ^ 10 +
            (3166058263 / 9676800 : ℝ) * x ^ 2 * (1 - x) ^ 9 +
            (1288427563 / 1890000 : ℝ) * x ^ 3 * (1 - x) ^ 8 +
            (136408344911 / 120960000 : ℝ) * x ^ 4 * (1 - x) ^ 7 +
            (2907922973 / 2160000 : ℝ) * x ^ 5 * (1 - x) ^ 6 +
            (15067982549 / 17280000 : ℝ) * x ^ 6 * (1 - x) ^ 5 +
            (14345411 / 54000 : ℝ) * x ^ 7 * (1 - x) ^ 4 +
            (8967873037 / 34560000 : ℝ) * x ^ 8 * (1 - x) ^ 3 +
            (426084689 / 1440000 : ℝ) * x ^ 9 * (1 - x) ^ 2 +
            (532778639 / 11520000 : ℝ) * x ^ 10 * (1 - x) +
            (43 / 10 : ℝ) * x ^ 11 by
        rw [plusP5OddQCorrelation_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith

  · have h : 0 ≤ (43 / 10 : ℝ) - plusP5OddQCorrelation t := by
      rw [show (43 / 10 : ℝ) - plusP5OddQCorrelation t =
          (86880403 / 2661120000 : ℝ) * (1 - x) ^ 11 +
            (42668123 / 30240000 : ℝ) * x * (1 - x) ^ 10 +
            (1411068137 / 9676800 : ℝ) * x ^ 2 * (1 - x) ^ 9 +
            (1393482437 / 1890000 : ℝ) * x ^ 3 * (1 - x) ^ 8 +
            (206876135089 / 120960000 : ℝ) * x ^ 4 * (1 - x) ^ 7 +
            (5674189027 / 2160000 : ℝ) * x ^ 5 * (1 - x) ^ 6 +
            (53588913451 / 17280000 : ℝ) * x ^ 6 * (1 - x) ^ 5 +
            (138906589 / 54000 : ℝ) * x ^ 7 * (1 - x) ^ 4 +
            (40072766963 / 34560000 : ℝ) * x ^ 8 * (1 - x) ^ 3 +
            (255035311 / 1440000 : ℝ) * x ^ 9 * (1 - x) ^ 2 +
            (557013361 / 11520000 : ℝ) * x ^ 10 * (1 - x) +
            (43 / 10 : ℝ) * x ^ 11 by
        rw [plusP5OddQCorrelation_polynomial]
        dsimp only [x]
        ring]
      positivity
    linarith

/-! ## One pole-free analytic error per complete profile -/

private theorem abs_poleFreeAnalyticError_lt_of_uniform_bound
    (C : ℝ → ℝ) (hC : Continuous C) (M : ℝ) (hM : 0 < M)
    (hbound : ∀ t, 0 ≤ t → t ≤ 2 → |C t| ≤ M) :
    |poleFreeAnalyticError C| < M / 10000 := by
  have hbase :=
    abs_poleFreeAnalyticError_le_integratedPoleFreeWeight C hC
  have hmono :
      (∫ t : ℝ in 0..2, integratedPoleFreeWeight t * |C t|) ≤
        ∫ t : ℝ in 0..2, integratedPoleFreeWeight t * M := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_integratedPoleFreeWeight.mul hC.abs).intervalIntegrable 0 2)
      ((continuous_integratedPoleFreeWeight.mul continuous_const).intervalIntegrable
        0 2)
    intro t ht
    exact mul_le_mul_of_nonneg_left (hbound t ht.1 ht.2)
      (integratedPoleFreeWeight_nonneg ht)
  have hfactor :
      (∫ t : ℝ in 0..2, integratedPoleFreeWeight t * M) =
        M * (∫ t : ℝ in 0..2, integratedPoleFreeWeight t) := by
    rw [show (fun t : ℝ ↦ integratedPoleFreeWeight t * M) =
        fun t ↦ M * integratedPoleFreeWeight t by
      funext t
      ring,
      intervalIntegral.integral_const_mul]
  have hscaled :
      M * (∫ t : ℝ in 0..2, integratedPoleFreeWeight t) <
        M * (1 / 10000 : ℝ) :=
    mul_lt_mul_of_pos_left integratedPoleFreeWeight_integral_lt hM
  calc
    |poleFreeAnalyticError C| ≤
        ∫ t : ℝ in 0..2, integratedPoleFreeWeight t * |C t| := hbase
    _ ≤ ∫ t : ℝ in 0..2, integratedPoleFreeWeight t * M := hmono
    _ = M * (∫ t : ℝ in 0..2, integratedPoleFreeWeight t) := hfactor
    _ < M * (1 / 10000 : ℝ) := hscaled
    _ = M / 10000 := by ring

theorem abs_poleFreeAnalyticError_plusP5OddB1Correlation_lt :
    |poleFreeAnalyticError plusP5OddB1Correlation| < (1 / 5000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_lt_of_uniform_bound
    plusP5OddB1Correlation continuous_plusP5OddB1Correlation 2 (by norm_num)
      (fun t ht0 ht2 ↦ abs_plusP5OddB1Correlation_le_two ht0 ht2)
  norm_num at h ⊢
  exact h

theorem abs_poleFreeAnalyticError_plusP5OddB4Correlation_lt :
    |poleFreeAnalyticError plusP5OddB4Correlation| < (1 / 5000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_lt_of_uniform_bound
    plusP5OddB4Correlation continuous_plusP5OddB4Correlation 2 (by norm_num)
      (fun t ht0 ht2 ↦ abs_plusP5OddB4Correlation_le_two ht0 ht2)
  norm_num at h ⊢
  exact h

theorem abs_poleFreeAnalyticError_plusP5OddQCorrelation_lt :
    |poleFreeAnalyticError plusP5OddQCorrelation| <
      (43 / 100000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_lt_of_uniform_bound
    plusP5OddQCorrelation continuous_plusP5OddQCorrelation (43 / 10)
      (by norm_num)
      (fun t ht0 ht2 ↦
        abs_plusP5OddQCorrelation_le_forty_three_tenths ht0 ht2)
  norm_num at h ⊢
  exact h

/-! ## Structural rational box for the first correlated border coordinate -/

private theorem plusP5_log_pi_mul_log_two_bounds :
    (7782169 / 10000000 : ℝ) < Real.log (Real.pi * Real.log 2) ∧
      Real.log (Real.pi * Real.log 2) < (7782170 / 10000000 : ℝ) := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprodLower :
      (21775860 / 10000000 : ℝ) < Real.pi * Real.log 2 := by
    calc
      (21775860 / 10000000 : ℝ) <
          (3.14159265358979323846 : ℝ) *
            (69314718055 / 100000000000 : ℝ) := by norm_num
      _ < Real.pi * (69314718055 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_right Real.pi_gt_d20 (by norm_num)
      _ < Real.pi * Real.log 2 :=
        mul_lt_mul_of_pos_left strict_log_two_fine_bounds.1 Real.pi_pos
  have hprodUpper :
      Real.pi * Real.log 2 < (21775861 / 10000000 : ℝ) := by
    calc
      Real.pi * Real.log 2 <
          (3.14159265358979323847 : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right Real.pi_lt_d20 hlogTwoPos
      _ < (3.14159265358979323847 : ℝ) *
          (69314718057 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_left strict_log_two_fine_bounds.2 (by norm_num)
      _ < (21775861 / 10000000 : ℝ) := by norm_num
  have hseriesLower := Real.sum_range_le_log_div
    (x := (588793 / 1588793 : ℝ)) (by norm_num) (by norm_num) 10
  have hlogLower :
      (7782169 / 10000000 : ℝ) <
        Real.log (21775860 / 10000000 : ℝ) := by
    norm_num [Finset.sum_range_succ] at hseriesLower ⊢
    linarith
  have hseriesUpper := Real.log_div_le_sum_range_add
    (x := (11775861 / 31775861 : ℝ)) (by norm_num) (by norm_num) 10
  have hlogUpper :
      Real.log (21775861 / 10000000 : ℝ) <
        (7782170 / 10000000 : ℝ) := by
    norm_num [Finset.sum_range_succ] at hseriesUpper ⊢
    linarith
  constructor
  · exact hlogLower.trans
      (Real.strictMonoOn_log (by norm_num)
        (mul_pos Real.pi_pos hlogTwoPos) hprodLower)
  · exact (Real.strictMonoOn_log (mul_pos Real.pi_pos hlogTwoPos)
      (by norm_num) hprodUpper).trans hlogUpper

theorem plusP5_scalarMassLoss_fine_bounds :
    (13554324 / 10000000 : ℝ) < yoshidaEndpointScalarMassLoss ∧
      yoshidaEndpointScalarMassLoss < (13554329 / 10000000 : ℝ) := by
  have hgamma := fineGammaInterval_contains
  have hgammaLower : (5772155 / 10000000 : ℝ) ≤
      Real.eulerMascheroniConstant := by
    norm_num [fineGammaInterval, RatInterval.Contains] at hgamma ⊢
    exact hgamma.1
  have hgammaUpper : Real.eulerMascheroniConstant ≤
      (5772159 / 10000000 : ℝ) := by
    norm_num [fineGammaInterval, RatInterval.Contains] at hgamma ⊢
    exact hgamma.2
  unfold yoshidaEndpointScalarMassLoss
  constructor <;> linarith [plusP5_log_pi_mul_log_two_bounds.1,
    plusP5_log_pi_mul_log_two_bounds.2]

private theorem plusP5_endpointA_pow_fine_bounds (n : ℕ) (hn : n ≠ 0) :
    (69314718055 / 200000000000 : ℝ) ^ n < yoshidaEndpointA ^ n ∧
      yoshidaEndpointA ^ n <
        (69314718057 / 200000000000 : ℝ) ^ n := by
  have hA :
      (69314718055 / 200000000000 : ℝ) < yoshidaEndpointA ∧
        yoshidaEndpointA < (69314718057 / 200000000000 : ℝ) := by
    unfold yoshidaEndpointA
    constructor <;> linarith [strict_log_two_fine_bounds.1,
      strict_log_two_fine_bounds.2]
  constructor
  · exact pow_lt_pow_left₀ hA.1 (by norm_num) hn
  · exact pow_lt_pow_left₀ hA.2 yoshidaEndpointA_pos.le hn

private theorem plusP5OddB1_cleanPolynomialContribution_bounds :
    (5445 / 1000000 : ℝ) <
        -yoshidaEndpointA *
          ((-10319 / 4800 : ℝ) * oddCleanRegularPolynomialGram11 +
            (15 / 8 : ℝ) * oddCleanRegularPolynomialGram13 +
            oddP5CleanRegularPolynomial15) ∧
      -yoshidaEndpointA *
          ((-10319 / 4800 : ℝ) * oddCleanRegularPolynomialGram11 +
            (15 / 8 : ℝ) * oddCleanRegularPolynomialGram13 +
            oddP5CleanRegularPolynomial15) < (5447 / 1000000 : ℝ) := by
  have h2 := plusP5_endpointA_pow_fine_bounds 2 (by norm_num)
  have h3 := plusP5_endpointA_pow_fine_bounds 3 (by norm_num)
  have h4 := plusP5_endpointA_pow_fine_bounds 4 (by norm_num)
  have h5 := plusP5_endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := plusP5_endpointA_pow_fine_bounds 6 (by norm_num)
  have h7 := plusP5_endpointA_pow_fine_bounds 7 (by norm_num)
  unfold oddCleanRegularPolynomialGram11 oddCleanRegularPolynomialGram13
    oddP5CleanRegularPolynomial15
  ring_nf
  constructor <;> nlinarith

private theorem plusP5_log_two_div_sqrt_two_fine_bounds :
    (12253 / 25000 : ℝ) < Real.log 2 / Real.sqrt 2 ∧
      Real.log 2 / Real.sqrt 2 < (49014 / 100000 : ℝ) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  constructor
  · exact log_two_div_sqrt_two_kernel_lower
  · rw [div_lt_iff₀ hspos]
    nlinarith [strict_log_two_fine_bounds.2, sqrt_two_kernel_bounds.1]

private theorem plusP5OddB1Correlation_prime_bounds :
    (69408 / 100000 : ℝ) <
        plusP5OddB1Correlation
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      plusP5OddB1Correlation
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (69411 / 100000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 116992 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hy0 : 0 < y := by
    dsimp only [y, tau]
    linarith [htau.1]
  have hyU : y < (1 / 100000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (2 : ℕ) ≠ 0)
  have hy3 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (3 : ℕ) ≠ 0)
  have hy4 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (4 : ℕ) ≠ 0)
  have hy5 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (5 : ℕ) ≠ 0)
  have hy6 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (6 : ℕ) ≠ 0)
  have hy7 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (7 : ℕ) ≠ 0)
  have htauy : tau = 116992 / 100000 + y := by
    dsimp only [y]
    ring
  dsimp only [tau] at htauy ⊢
  rw [htauy, plusP5OddB1Correlation_polynomial]
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7,
    sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6,
    pow_nonneg hy0.le 7]

private theorem plusP5OddB1PrimeProduct_bounds :
    (44023 / 100000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          plusP5OddB1Correlation
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          plusP5OddB1Correlation
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (11007 / 25000 : ℝ) := by
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hcorr := plusP5OddB1Correlation_prime_bounds
  have hbeta0 : 0 < Real.log 3 / Real.sqrt 3 := by
    linarith [hbeta.1]
  have hcorr0 : 0 < plusP5OddB1Correlation
      (factorTwoPrimeShift / yoshidaEndpointA) := by
    linarith [hcorr.1]
  constructor
  · calc
      (44023 / 100000 : ℝ) <
          (63427 / 100000 : ℝ) * (69408 / 100000 : ℝ) := by
        norm_num
      _ < (Real.log 3 / Real.sqrt 3) * (69408 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
      _ < (Real.log 3 / Real.sqrt 3) *
          plusP5OddB1Correlation
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_left hcorr.1 hbeta0
  · calc
      (Real.log 3 / Real.sqrt 3) *
          plusP5OddB1Correlation
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (6343 / 10000 : ℝ) *
            plusP5OddB1Correlation
              (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_right hbeta.2 hcorr0
      _ < (6343 / 10000 : ℝ) * (69411 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_left hcorr.2 (by norm_num)
      _ < (11007 / 25000 : ℝ) := by norm_num

private theorem plusP5OddB1Base_bounds :
    (3891 / 100000 : ℝ) < plusP5OddB1Base ∧
      plusP5OddB1Base < (391 / 10000 : ℝ) := by
  have hmass := plusP5_scalarMassLoss_fine_bounds
  have hclean := plusP5OddB1_cleanPolynomialContribution_bounds
  have halpha := plusP5_log_two_div_sqrt_two_fine_bounds
  have hprime := plusP5OddB1PrimeProduct_bounds
  have hm := oddPolynomialMoment_bounds
  have hm15 := oddP5PolynomialMoment_bounds
  have hlog := strict_log_two_fine_bounds
  unfold plusP5OddB1Base
  constructor <;> nlinarith [hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1,
    hm15.1, hm15.2.1]

private theorem abs_plusP5OddB1CleanEnvelope_lt :
    |plusP5OddB1CleanEnvelope| < (1 / 125000 : ℝ) := by
  have h11 := abs_le.mp abs_oddCleanRegularEnvelopeError11_le
  have h13 := abs_lt.mp abs_oddCleanRegularEnvelopeError13_lt
  have h15 := abs_lt.mp abs_oddP5CleanRegularEnvelopeError15_lt
  unfold plusP5OddB1CleanEnvelope
  rw [abs_lt]
  constructor <;> nlinarith [h11.1, h11.2, h13.1, h13.2, h15.1, h15.2]

private theorem abs_plusP5OddB1CleanEnvelope_scaled_lt :
    |yoshidaEndpointA * plusP5OddB1CleanEnvelope| <
      (1 / 250000 : ℝ) := by
  have hA : yoshidaEndpointA < (7 / 20 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  rw [abs_mul, abs_of_nonneg yoshidaEndpointA_pos.le]
  calc
    yoshidaEndpointA * |plusP5OddB1CleanEnvelope| ≤
        (7 / 20 : ℝ) * |plusP5OddB1CleanEnvelope| :=
      mul_le_mul_of_nonneg_right hA.le (abs_nonneg _)
    _ < (7 / 20 : ℝ) * (1 / 125000 : ℝ) :=
      mul_lt_mul_of_pos_left abs_plusP5OddB1CleanEnvelope_lt (by norm_num)
    _ < (1 / 250000 : ℝ) := by norm_num

private theorem plusP5OddB1HyperbolicMain_bounds :
    (10003 / 500000 : ℝ) <
        2 * yoshidaEndpointA * (10319 / 4800 : ℝ) *
          oddCleanSinhMoment1 ^ 2 ∧
      2 * yoshidaEndpointA * (10319 / 4800 : ℝ) *
          oddCleanSinhMoment1 ^ 2 < (2001 / 100000 : ℝ) := by
  have hA := plusP5_endpointA_pow_fine_bounds 1 (by norm_num)
  have hAlo : (69314718055 / 200000000000 : ℝ) < yoshidaEndpointA := by
    simpa using hA.1
  have hAhi : yoshidaEndpointA <
      (69314718057 / 200000000000 : ℝ) := by
    simpa using hA.2
  have hmLower := oddCleanSinhMoment1_gt
  have hmSqLower :
      (11587142 / 100000000 : ℝ) ^ 2 < oddCleanSinhMoment1 ^ 2 := by
    nlinarith [sq_nonneg
      (oddCleanSinhMoment1 - (11587142 / 100000000 : ℝ))]
  have hmSqUpper := oddCleanSinhMoment1_sq_lt
  have hA0 := yoshidaEndpointA_pos
  rw [show 2 * yoshidaEndpointA * (10319 / 4800 : ℝ) *
      oddCleanSinhMoment1 ^ 2 =
        yoshidaEndpointA * (10319 / 2400 : ℝ) *
          oddCleanSinhMoment1 ^ 2 by ring]
  constructor
  · calc
      (10003 / 500000 : ℝ) <
          (69314718055 / 200000000000 : ℝ) *
            (10319 / 2400 : ℝ) *
              (11587142 / 100000000 : ℝ) ^ 2 := by norm_num
      _ < yoshidaEndpointA * (10319 / 2400 : ℝ) *
          (11587142 / 100000000 : ℝ) ^ 2 := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hAlo (by norm_num)) (by norm_num)
      _ < yoshidaEndpointA * (10319 / 2400 : ℝ) *
          oddCleanSinhMoment1 ^ 2 := by
        exact mul_lt_mul_of_pos_left hmSqLower
          (mul_pos hA0 (by norm_num))
  · calc
      yoshidaEndpointA * (10319 / 2400 : ℝ) *
          oddCleanSinhMoment1 ^ 2 ≤
          (69314718057 / 200000000000 : ℝ) *
            (10319 / 2400 : ℝ) * oddCleanSinhMoment1 ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hAhi.le (by norm_num))
          (sq_nonneg _)
      _ < (69314718057 / 200000000000 : ℝ) *
          (10319 / 2400 : ℝ) * (134263 / 10000000 : ℝ) := by
        exact mul_lt_mul_of_pos_left hmSqUpper (by norm_num)
      _ < (2001 / 100000 : ℝ) := by norm_num

private theorem abs_plusP5OddB1HyperbolicCross13_lt :
    |2 * yoshidaEndpointA * (15 / 8 : ℝ) *
        (oddCleanSinhMoment1 * oddCleanSinhMoment3)| <
      (1 / 30000 : ℝ) := by
  have hA := plusP5_endpointA_pow_fine_bounds 1 (by norm_num)
  have hAhi : yoshidaEndpointA <
      (69314718057 / 200000000000 : ℝ) := by
    simpa using hA.2
  have hcross := abs_oddCleanSinhMoment1_mul_moment3_lt
  rw [show |2 * yoshidaEndpointA * (15 / 8 : ℝ) *
      (oddCleanSinhMoment1 * oddCleanSinhMoment3)| =
        (15 / 4 : ℝ) * yoshidaEndpointA *
          |oddCleanSinhMoment1 * oddCleanSinhMoment3| by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg yoshidaEndpointA_pos.le,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 8)]
    ring]
  calc
    (15 / 4 : ℝ) * yoshidaEndpointA *
        |oddCleanSinhMoment1 * oddCleanSinhMoment3| ≤
        (15 / 4 : ℝ) * (69314718057 / 200000000000 : ℝ) *
          |oddCleanSinhMoment1 * oddCleanSinhMoment3| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAhi.le (by norm_num)) (abs_nonneg _)
    _ < (15 / 4 : ℝ) * (69314718057 / 200000000000 : ℝ) *
        (1 / 39000 : ℝ) := by
      exact mul_lt_mul_of_pos_left hcross (by norm_num)
    _ < (1 / 30000 : ℝ) := by norm_num

private theorem plusP5OddB1Hyperbolic_bounds :
    (1997 / 100000 : ℝ) <
        -2 * yoshidaEndpointA * oddCleanSinhMoment1 *
          plusP5OddCompletionSinhMoment ∧
      -2 * yoshidaEndpointA * oddCleanSinhMoment1 *
          plusP5OddCompletionSinhMoment < (2005 / 100000 : ℝ) := by
  have hmain := plusP5OddB1HyperbolicMain_bounds
  have h13 := abs_lt.mp abs_plusP5OddB1HyperbolicCross13_lt
  have h15 := abs_lt.mp abs_oddP5_hyperbolicCross15_lt
  rw [show -2 * yoshidaEndpointA * oddCleanSinhMoment1 *
      plusP5OddCompletionSinhMoment =
        2 * yoshidaEndpointA * (10319 / 4800 : ℝ) *
            oddCleanSinhMoment1 ^ 2 -
          2 * yoshidaEndpointA * (15 / 8 : ℝ) *
            (oddCleanSinhMoment1 * oddCleanSinhMoment3) -
          2 * yoshidaEndpointA * oddCleanSinhMoment1 *
            oddP5CleanSinhMoment by
    unfold plusP5OddCompletionSinhMoment
    ring]
  constructor <;> nlinarith [hmain.1, hmain.2, h13.1, h13.2,
    h15.1, h15.2]

theorem plusP5OddB1_bounds :
    (1173 / 20000 : ℝ) < plusP5OddB1 ∧
      plusP5OddB1 < (297 / 5000 : ℝ) := by
  have hbase := plusP5OddB1Base_bounds
  have henv := abs_lt.mp abs_plusP5OddB1CleanEnvelope_scaled_lt
  have hhyper := plusP5OddB1Hyperbolic_bounds
  have herr := abs_lt.mp
    abs_poleFreeAnalyticError_plusP5OddB1Correlation_lt
  rw [plusP5OddB1_eq_structuralProfile]
  constructor <;> nlinarith [hbase.1, hbase.2, henv.1, henv.2,
    hhyper.1, hhyper.2, herr.1, herr.2]

/-! ## Exact negative-endpoint B4 profile assembly -/

private theorem oddStructuralRegularError33_sharp_expansion :
    oddStructuralRegularError oddStructuralCorrelation33 =
      poleFreeAnalyticError oddStructuralCorrelation33 + oddPolynomialMoment33 := by
  have h := evenStructuralRegularError_eq_analytic_add_polynomial
    oddStructuralCorrelation33 (by unfold oddStructuralCorrelation33; fun_prop)
  rw [integral_polynomialDifference_mul_oddCorrelations.2.2] at h
  simpa [evenStructuralRegularError, oddStructuralRegularError] using h

def plusP5OddBorderSinhMoment : ℝ :=
  (-359 / 360 : ℝ) * oddCleanSinhMoment1 + oddCleanSinhMoment3

def plusP5OddB4CleanEnvelope : ℝ :=
  (3704521 / 1728000 : ℝ) *
      oddCleanRegularEnvelopeError oddStructuralCorrelation11 -
    (9647 / 2400 : ℝ) *
      oddCleanRegularEnvelopeError oddStructuralCorrelation13 +
    (15 / 8 : ℝ) *
      oddCleanRegularEnvelopeError oddStructuralCorrelation33 -
    (359 / 360 : ℝ) * oddP5CleanRegularEnvelopeError15 +
    oddP5CleanRegularEnvelopeError35

def plusP5OddB4Base : ℝ :=
  (3704521 / 1728000 : ℝ) *
      ((14 / 9 : ℝ) - (2 / 3 : ℝ) *
        (Real.log 2 + yoshidaEndpointScalarMassLoss)) -
    (9647 / 2400 : ℝ) * (1 / 5 : ℝ) +
    (15 / 8 : ℝ) *
      ((674 / 735 : ℝ) - (2 / 7 : ℝ) *
        (Real.log 2 + yoshidaEndpointScalarMassLoss)) -
    (359 / 360 : ℝ) * (1 / 14 : ℝ) + (1 / 9 : ℝ) -
    yoshidaEndpointA *
      ((3704521 / 1728000 : ℝ) * oddCleanRegularPolynomialGram11 -
        (9647 / 2400 : ℝ) * oddCleanRegularPolynomialGram13 +
        (15 / 8 : ℝ) * oddCleanRegularPolynomialGram33 -
        (359 / 360 : ℝ) * oddP5CleanRegularPolynomial15 +
        oddP5CleanRegularPolynomial35) -
    ((3704521 / 1728000 : ℝ) *
        (oddPolynomialMoment11 - 4 / 375 +
          (2 / 3 - (2 / 3 : ℝ) * Real.log 2) -
          (Real.log 2 / Real.sqrt 2) * (2 / 3)) -
      (9647 / 2400 : ℝ) *
        (oddPolynomialMoment13 + (7 - 10 * Real.log 2)) +
      (15 / 8 : ℝ) *
        (oddPolynomialMoment33 +
          (5 / 21 - (2 / 7 : ℝ) * Real.log 2) -
          (Real.log 2 / Real.sqrt 2) * (2 / 7)) -
      (359 / 360 : ℝ) *
        (oddP5PolynomialMoment15 + (165 - 238 * Real.log 2)) +
      (oddP5PolynomialMoment35 + (25 / 2 - 18 * Real.log 2)) -
      (Real.log 3 / Real.sqrt 3) * plusP5OddB4Correlation
        (factorTwoPrimeShift / yoshidaEndpointA))

theorem plusP5OddB4_eq_structuralProfile :
    plusP5OddB4 =
      plusP5OddB4Base -
        yoshidaEndpointA * plusP5OddB4CleanEnvelope -
        2 * yoshidaEndpointA * plusP5OddBorderSinhMoment *
          plusP5OddCompletionSinhMoment -
        poleFreeAnalyticError plusP5OddB4Correlation := by
  rw [poleFreeAnalyticError_plusP5OddB4Correlation_eq]
  unfold plusP5OddB4 plusP5OddB4Base plusP5OddB4CleanEnvelope
    plusP5OddBorderSinhMoment plusP5OddCompletionSinhMoment
    factorTwoIntrinsicSixUnbalancedOMinus11
    factorTwoIntrinsicSixUnbalancedOMinus13
    factorTwoIntrinsicSixUnbalancedOMinus15
    factorTwoIntrinsicSixUnbalancedOMinus33
    factorTwoIntrinsicSixUnbalancedOMinus35
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33 factorTwoIntrinsicFourP45Cross15
    factorTwoIntrinsicFourP45Cross35
  rw [yoshidaEndpointOddLowGram11_structural_eq,
    yoshidaEndpointOddLowGram13_structural_eq,
    yoshidaEndpointOddLowGram33_structural_eq,
    cleanBilinear_p1_p5_eq, cleanBilinear_p3_p5_eq,
    factorTwoCenteredSymmetricPerturbation_p1_structural_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_structural_eq,
    factorTwoCenteredSymmetricPerturbation_p3_structural_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p1_p5_structural_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p3_p5_structural_eq,
    oddStructuralRegularError11_sharp_expansion,
    oddStructuralRegularError13_sharp_expansion,
    oddStructuralRegularError33_sharp_expansion]
  unfold plusP5OddB4Correlation
  ring

private theorem plusP5OddB4_cleanPolynomialContribution_bounds :
    (-5753 / 1000000 : ℝ) <
        -yoshidaEndpointA *
          ((3704521 / 1728000 : ℝ) * oddCleanRegularPolynomialGram11 -
            (9647 / 2400 : ℝ) * oddCleanRegularPolynomialGram13 +
            (15 / 8 : ℝ) * oddCleanRegularPolynomialGram33 -
            (359 / 360 : ℝ) * oddP5CleanRegularPolynomial15 +
            oddP5CleanRegularPolynomial35) ∧
      -yoshidaEndpointA *
          ((3704521 / 1728000 : ℝ) * oddCleanRegularPolynomialGram11 -
            (9647 / 2400 : ℝ) * oddCleanRegularPolynomialGram13 +
            (15 / 8 : ℝ) * oddCleanRegularPolynomialGram33 -
            (359 / 360 : ℝ) * oddP5CleanRegularPolynomial15 +
            oddP5CleanRegularPolynomial35) < (-5752 / 1000000 : ℝ) := by
  have h2 := plusP5_endpointA_pow_fine_bounds 2 (by norm_num)
  have h3 := plusP5_endpointA_pow_fine_bounds 3 (by norm_num)
  have h4 := plusP5_endpointA_pow_fine_bounds 4 (by norm_num)
  have h5 := plusP5_endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := plusP5_endpointA_pow_fine_bounds 6 (by norm_num)
  have h7 := plusP5_endpointA_pow_fine_bounds 7 (by norm_num)
  unfold oddCleanRegularPolynomialGram11 oddCleanRegularPolynomialGram13
    oddCleanRegularPolynomialGram33 oddP5CleanRegularPolynomial15
    oddP5CleanRegularPolynomial35
  ring_nf
  constructor <;> nlinarith

private theorem plusP5OddB4Correlation_prime_bounds :
    (-96366 / 100000 : ℝ) <
        plusP5OddB4Correlation
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      plusP5OddB4Correlation
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (-96365 / 100000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 116992 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hy0 : 0 < y := by
    dsimp only [y, tau]
    linarith [htau.1]
  have hyU : y < (1 / 100000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (2 : ℕ) ≠ 0)
  have hy3 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (3 : ℕ) ≠ 0)
  have hy4 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (4 : ℕ) ≠ 0)
  have hy5 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (5 : ℕ) ≠ 0)
  have hy6 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (6 : ℕ) ≠ 0)
  have hy7 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (7 : ℕ) ≠ 0)
  have hy8 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (8 : ℕ) ≠ 0)
  have hy9 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (9 : ℕ) ≠ 0)
  have htauy : tau = 116992 / 100000 + y := by
    dsimp only [y]
    ring
  dsimp only [tau] at htauy ⊢
  rw [htauy, plusP5OddB4Correlation_polynomial]
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8, hy9,
    sq_nonneg y, pow_nonneg hy0.le 3, pow_nonneg hy0.le 4,
    pow_nonneg hy0.le 5, pow_nonneg hy0.le 6,
    pow_nonneg hy0.le 7, pow_nonneg hy0.le 8,
    pow_nonneg hy0.le 9]

private theorem plusP5OddB4PrimeProduct_bounds :
    (-61125 / 100000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          plusP5OddB4Correlation
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          plusP5OddB4Correlation
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (-61121 / 100000 : ℝ) := by
  have hbeta := log_three_div_sqrt_three_kernel_bounds
  have hcorr := plusP5OddB4Correlation_prime_bounds
  have hnegcorr :
      (96365 / 100000 : ℝ) <
          -plusP5OddB4Correlation
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
        -plusP5OddB4Correlation
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (96366 / 100000 : ℝ) := by
    constructor <;> linarith [hcorr.1, hcorr.2]
  have hbeta0 : 0 < Real.log 3 / Real.sqrt 3 := by
    linarith [hbeta.1]
  have hnegcorr0 : 0 < -plusP5OddB4Correlation
      (factorTwoPrimeShift / yoshidaEndpointA) := by
    linarith [hnegcorr.1]
  have hpositiveProduct :
      (61121 / 100000 : ℝ) <
          (Real.log 3 / Real.sqrt 3) *
            (-plusP5OddB4Correlation
              (factorTwoPrimeShift / yoshidaEndpointA)) ∧
        (Real.log 3 / Real.sqrt 3) *
            (-plusP5OddB4Correlation
              (factorTwoPrimeShift / yoshidaEndpointA)) <
          (61125 / 100000 : ℝ) := by
    constructor
    · calc
        (61121 / 100000 : ℝ) <
            (63427 / 100000 : ℝ) * (96365 / 100000 : ℝ) := by
          norm_num
        _ < (Real.log 3 / Real.sqrt 3) * (96365 / 100000 : ℝ) :=
          mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
        _ < (Real.log 3 / Real.sqrt 3) *
            (-plusP5OddB4Correlation
              (factorTwoPrimeShift / yoshidaEndpointA)) :=
          mul_lt_mul_of_pos_left hnegcorr.1 hbeta0
    · calc
        (Real.log 3 / Real.sqrt 3) *
            (-plusP5OddB4Correlation
              (factorTwoPrimeShift / yoshidaEndpointA)) <
            (6343 / 10000 : ℝ) *
              (-plusP5OddB4Correlation
                (factorTwoPrimeShift / yoshidaEndpointA)) :=
          mul_lt_mul_of_pos_right hbeta.2 hnegcorr0
        _ < (6343 / 10000 : ℝ) * (96366 / 100000 : ℝ) :=
          mul_lt_mul_of_pos_left hnegcorr.2 (by norm_num)
        _ < (61125 / 100000 : ℝ) := by norm_num
  constructor <;> nlinarith [hpositiveProduct.1, hpositiveProduct.2]

private theorem plusP5OddB4Base_bounds :
    (40308 / 100000 : ℝ) < plusP5OddB4Base ∧
      plusP5OddB4Base < (4032 / 10000 : ℝ) := by
  have hmass := plusP5_scalarMassLoss_fine_bounds
  have hclean := plusP5OddB4_cleanPolynomialContribution_bounds
  have halpha := plusP5_log_two_div_sqrt_two_fine_bounds
  have hprime := plusP5OddB4PrimeProduct_bounds
  have hm := oddPolynomialMoment_bounds
  have hm15 := oddP5PolynomialMoment_bounds
  have hlog := strict_log_two_fine_bounds
  unfold plusP5OddB4Base
  constructor <;> nlinarith [hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1,
    hm.2.2.2.2.1, hm.2.2.2.2.2, hm15.1, hm15.2.1,
    oddP5PolynomialMoment_bounds.2.2]

private theorem abs_plusP5OddB4CleanEnvelope_lt :
    |plusP5OddB4CleanEnvelope| < (3 / 250000 : ℝ) := by
  have h11 := abs_le.mp abs_oddCleanRegularEnvelopeError11_le
  have h13 := abs_lt.mp abs_oddCleanRegularEnvelopeError13_lt
  have h33 := abs_le.mp abs_oddCleanRegularEnvelopeError33_le
  have h15 := abs_lt.mp abs_oddP5CleanRegularEnvelopeError15_lt
  have h35 := abs_lt.mp abs_oddP5CleanRegularEnvelopeError35_lt
  unfold plusP5OddB4CleanEnvelope
  rw [abs_lt]
  constructor <;> nlinarith [h11.1, h11.2, h13.1, h13.2,
    h33.1, h33.2, h15.1, h15.2, h35.1, h35.2]

private theorem abs_plusP5OddB4CleanEnvelope_scaled_lt :
    |yoshidaEndpointA * plusP5OddB4CleanEnvelope| <
      (1 / 200000 : ℝ) := by
  have hA : yoshidaEndpointA < (7 / 20 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  rw [abs_mul, abs_of_nonneg yoshidaEndpointA_pos.le]
  calc
    yoshidaEndpointA * |plusP5OddB4CleanEnvelope| ≤
        (7 / 20 : ℝ) * |plusP5OddB4CleanEnvelope| :=
      mul_le_mul_of_nonneg_right hA.le (abs_nonneg _)
    _ < (7 / 20 : ℝ) * (3 / 250000 : ℝ) :=
      mul_lt_mul_of_pos_left abs_plusP5OddB4CleanEnvelope_lt (by norm_num)
    _ < (1 / 200000 : ℝ) := by norm_num

private theorem plusP5OddB4HyperbolicMain_bounds :
    (1995 / 100000 : ℝ) <
        2 * yoshidaEndpointA * (3704521 / 1728000 : ℝ) *
          oddCleanSinhMoment1 ^ 2 ∧
      2 * yoshidaEndpointA * (3704521 / 1728000 : ℝ) *
          oddCleanSinhMoment1 ^ 2 < (3991 / 200000 : ℝ) := by
  have hA := plusP5_endpointA_pow_fine_bounds 1 (by norm_num)
  have hAlo : (69314718055 / 200000000000 : ℝ) < yoshidaEndpointA := by
    simpa using hA.1
  have hAhi : yoshidaEndpointA <
      (69314718057 / 200000000000 : ℝ) := by
    simpa using hA.2
  have hmLower := oddCleanSinhMoment1_gt
  have hmSqLower :
      (11587142 / 100000000 : ℝ) ^ 2 < oddCleanSinhMoment1 ^ 2 := by
    nlinarith [sq_nonneg
      (oddCleanSinhMoment1 - (11587142 / 100000000 : ℝ))]
  have hmSqUpper := oddCleanSinhMoment1_sq_lt
  have hA0 := yoshidaEndpointA_pos
  rw [show 2 * yoshidaEndpointA * (3704521 / 1728000 : ℝ) *
      oddCleanSinhMoment1 ^ 2 =
        yoshidaEndpointA * (3704521 / 864000 : ℝ) *
          oddCleanSinhMoment1 ^ 2 by ring]
  constructor
  · calc
      (1995 / 100000 : ℝ) <
          (69314718055 / 200000000000 : ℝ) *
            (3704521 / 864000 : ℝ) *
              (11587142 / 100000000 : ℝ) ^ 2 := by norm_num
      _ < yoshidaEndpointA * (3704521 / 864000 : ℝ) *
          (11587142 / 100000000 : ℝ) ^ 2 := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hAlo (by norm_num)) (by norm_num)
      _ < yoshidaEndpointA * (3704521 / 864000 : ℝ) *
          oddCleanSinhMoment1 ^ 2 := by
        exact mul_lt_mul_of_pos_left hmSqLower
          (mul_pos hA0 (by norm_num))
  · calc
      yoshidaEndpointA * (3704521 / 864000 : ℝ) *
          oddCleanSinhMoment1 ^ 2 ≤
          (69314718057 / 200000000000 : ℝ) *
            (3704521 / 864000 : ℝ) * oddCleanSinhMoment1 ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hAhi.le (by norm_num))
          (sq_nonneg _)
      _ < (69314718057 / 200000000000 : ℝ) *
          (3704521 / 864000 : ℝ) * (134263 / 10000000 : ℝ) := by
        exact mul_lt_mul_of_pos_left hmSqUpper (by norm_num)
      _ < (3991 / 200000 : ℝ) := by norm_num

private theorem abs_plusP5OddB4HyperbolicCross13_lt :
    |2 * yoshidaEndpointA * (-9647 / 2400 : ℝ) *
        (oddCleanSinhMoment1 * oddCleanSinhMoment3)| <
      (9 / 125000 : ℝ) := by
  have hA := plusP5_endpointA_pow_fine_bounds 1 (by norm_num)
  have hAhi : yoshidaEndpointA <
      (69314718057 / 200000000000 : ℝ) := by
    simpa using hA.2
  have hcross := abs_oddCleanSinhMoment1_mul_moment3_lt
  calc
    |2 * yoshidaEndpointA * (-9647 / 2400 : ℝ) *
        (oddCleanSinhMoment1 * oddCleanSinhMoment3)| =
        (9647 / 2400 : ℝ) *
          |2 * yoshidaEndpointA *
            (oddCleanSinhMoment1 * oddCleanSinhMoment3)| := by
      rw [show 2 * yoshidaEndpointA * (-9647 / 2400 : ℝ) *
          (oddCleanSinhMoment1 * oddCleanSinhMoment3) =
        (-9647 / 2400 : ℝ) *
          (2 * yoshidaEndpointA *
            (oddCleanSinhMoment1 * oddCleanSinhMoment3)) by ring,
        abs_mul]
      norm_num
    _ = (9647 / 1200 : ℝ) * yoshidaEndpointA *
          |oddCleanSinhMoment1 * oddCleanSinhMoment3| := by
      rw [abs_mul, abs_mul, abs_of_nonneg yoshidaEndpointA_pos.le]
      norm_num
      ring
    (9647 / 1200 : ℝ) * yoshidaEndpointA *
        |oddCleanSinhMoment1 * oddCleanSinhMoment3| ≤
        (9647 / 1200 : ℝ) *
          (69314718057 / 200000000000 : ℝ) *
          |oddCleanSinhMoment1 * oddCleanSinhMoment3| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAhi.le (by norm_num)) (abs_nonneg _)
    _ < (9647 / 1200 : ℝ) *
        (69314718057 / 200000000000 : ℝ) * (1 / 39000 : ℝ) := by
      exact mul_lt_mul_of_pos_left hcross (by norm_num)
    _ < (9 / 125000 : ℝ) := by norm_num

private theorem abs_plusP5OddB4HyperbolicSquare33_lt :
    |2 * yoshidaEndpointA * (15 / 8 : ℝ) *
        oddCleanSinhMoment3 ^ 2| < (1 / 10000000 : ℝ) := by
  have hA := plusP5_endpointA_pow_fine_bounds 1 (by norm_num)
  have hAhi : yoshidaEndpointA <
      (69314718057 / 200000000000 : ℝ) := by
    simpa using hA.2
  have hm3 := oddCleanSinhMoment3_sq_lt
  rw [abs_of_nonneg (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le) (by norm_num))
    (sq_nonneg _))]
  calc
    2 * yoshidaEndpointA * (15 / 8 : ℝ) * oddCleanSinhMoment3 ^ 2 ≤
        2 * (69314718057 / 200000000000 : ℝ) * (15 / 8 : ℝ) *
          oddCleanSinhMoment3 ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAhi.le (by norm_num)) (by norm_num))
        (sq_nonneg _)
    _ < 2 * (69314718057 / 200000000000 : ℝ) * (15 / 8 : ℝ) *
        (481 / 10000000000 : ℝ) := by
      exact mul_lt_mul_of_pos_left hm3 (by norm_num)
    _ < (1 / 10000000 : ℝ) := by norm_num

private theorem abs_plusP5OddB4HyperbolicCross15_lt :
    |2 * yoshidaEndpointA * (-359 / 360 : ℝ) *
        (oddCleanSinhMoment1 * oddP5CleanSinhMoment)| <
      (1 / 1000000 : ℝ) := by
  calc
    |2 * yoshidaEndpointA * (-359 / 360 : ℝ) *
        (oddCleanSinhMoment1 * oddP5CleanSinhMoment)| =
        (359 / 360 : ℝ) *
          |2 * yoshidaEndpointA * oddCleanSinhMoment1 *
            oddP5CleanSinhMoment| := by
      rw [show 2 * yoshidaEndpointA * (-359 / 360 : ℝ) *
          (oddCleanSinhMoment1 * oddP5CleanSinhMoment) =
        (-359 / 360 : ℝ) *
          (2 * yoshidaEndpointA * oddCleanSinhMoment1 *
            oddP5CleanSinhMoment) by ring,
        abs_mul]
      norm_num
    (359 / 360 : ℝ) *
        |2 * yoshidaEndpointA * oddCleanSinhMoment1 *
          oddP5CleanSinhMoment| <
        (359 / 360 : ℝ) * (1 / 1000000 : ℝ) :=
      mul_lt_mul_of_pos_left abs_oddP5_hyperbolicCross15_lt (by norm_num)
    _ < (1 / 1000000 : ℝ) := by norm_num

private theorem plusP5OddB4Hyperbolic_bounds :
    (-2003 / 100000 : ℝ) <
        -2 * yoshidaEndpointA * plusP5OddBorderSinhMoment *
          plusP5OddCompletionSinhMoment ∧
      -2 * yoshidaEndpointA * plusP5OddBorderSinhMoment *
          plusP5OddCompletionSinhMoment < (-1987 / 100000 : ℝ) := by
  have hmain := plusP5OddB4HyperbolicMain_bounds
  have h13 := abs_lt.mp abs_plusP5OddB4HyperbolicCross13_lt
  have h33 := abs_lt.mp abs_plusP5OddB4HyperbolicSquare33_lt
  have h15 := abs_lt.mp abs_plusP5OddB4HyperbolicCross15_lt
  have h35 := abs_lt.mp abs_oddP5_hyperbolicCross35_lt
  rw [show -2 * yoshidaEndpointA * plusP5OddBorderSinhMoment *
      plusP5OddCompletionSinhMoment =
        -(2 * yoshidaEndpointA * (3704521 / 1728000 : ℝ) *
            oddCleanSinhMoment1 ^ 2) -
          2 * yoshidaEndpointA * (-9647 / 2400 : ℝ) *
            (oddCleanSinhMoment1 * oddCleanSinhMoment3) -
          2 * yoshidaEndpointA * (15 / 8 : ℝ) *
            oddCleanSinhMoment3 ^ 2 -
          2 * yoshidaEndpointA * (-359 / 360 : ℝ) *
            (oddCleanSinhMoment1 * oddP5CleanSinhMoment) -
          2 * yoshidaEndpointA * oddCleanSinhMoment3 *
            oddP5CleanSinhMoment by
    unfold plusP5OddBorderSinhMoment plusP5OddCompletionSinhMoment
    ring]
  constructor <;> nlinarith [hmain.1, hmain.2, h13.1, h13.2,
    h33.1, h33.2, h15.1, h15.2, h35.1, h35.2]

theorem plusP5OddB4_bounds :
    (957 / 2500 : ℝ) < plusP5OddB4 ∧
      plusP5OddB4 < (959 / 2500 : ℝ) := by
  have hbase := plusP5OddB4Base_bounds
  have henv := abs_lt.mp abs_plusP5OddB4CleanEnvelope_scaled_lt
  have hhyper := plusP5OddB4Hyperbolic_bounds
  have herr := abs_lt.mp
    abs_poleFreeAnalyticError_plusP5OddB4Correlation_lt
  rw [plusP5OddB4_eq_structuralProfile]
  constructor <;> nlinarith [hbase.1, hbase.2, henv.1, henv.2,
    hhyper.1, hhyper.2, herr.1, herr.2]

/-! ## The whole correlated `P₁/P₃/P₅` square -/

/-- The exact sixth-order regular-kernel model of the single completed
profile.  It is formed before taking any estimate, so all mixed-mode
cancellation is retained. -/
def plusP5OddQCleanPolynomial : ℝ :=
  (17580370823 / 296524800000 : ℝ) * yoshidaEndpointA +
    (106481761 / 829440000 : ℝ) * yoshidaEndpointA ^ 2 -
    (9126616739 / 2737152000000 : ℝ) * yoshidaEndpointA ^ 3 -
    (559630327 / 23224320000 : ℝ) * yoshidaEndpointA ^ 4 +
    (5236079823901 / 32011868528640000 : ℝ) * yoshidaEndpointA ^ 5 +
    (2558186668753 / 536481792000000 : ℝ) * yoshidaEndpointA ^ 6

/-- The one signed global regular-kernel envelope of the completed profile. -/
def plusP5OddQCleanEnvelope : ℝ :=
  oddCleanRegularEnvelopeError plusP5OddQCorrelation

/-- The combined pole-free polynomial moment of the completed correlation. -/
def plusP5OddQPolynomialMoment : ℝ :=
  -(106481761 / 51840000 : ℝ) * polynomialD2 -
    (559630327 / 151200000 : ℝ) * polynomialD4 -
    (41937486373 / 5821200000 : ℝ) * polynomialD6

/-- The exact nonnegative logarithmic reserve left in the fifth mode. -/
def plusP5OddQRawReserve : ℝ :=
  centeredRawLogEnergy factorTwoCenteredP5 / 4 - 137 / 330

/-- All explicit contributions of the completed square, prior to the three
global analytic remainders. -/
def plusP5OddQAlgebraicBase : ℝ :=
  27837295643700157 / 38419920000000 -
    (9949613 / 9600 : ℝ) * Real.log 2 -
    (11355935597 / 2661120000 : ℝ) * yoshidaEndpointScalarMassLoss +
    (11355935597 / 2661120000 : ℝ) * (Real.log 2 / Real.sqrt 2) +
    (Real.log 3 / Real.sqrt 3) *
      plusP5OddQCorrelation (factorTwoPrimeShift / yoshidaEndpointA) -
    yoshidaEndpointA * plusP5OddQCleanPolynomial -
    plusP5OddQPolynomialMoment

/-- The diagonal `P5` contribution to the sixth-order regular model. -/
def oddP5CleanRegularPolynomial55 : ℝ :=
  yoshidaEndpointA / 7722 + yoshidaEndpointA ^ 3 / 1544400 +
    31 * yoshidaEndpointA ^ 5 / 2315673360

theorem integral_regularKernelPolynomial6_mul_oddP5Correlation55 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        oddP5Correlation55 t) = oddP5CleanRegularPolynomial55 := by
  unfold yoshidaRegularKernelPolynomial6 oddP5Correlation55
    oddP5CleanRegularPolynomial55
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow]
  rw [show (fun x : ℝ ↦ yoshidaEndpointA * x) =
      fun x ↦ yoshidaEndpointA * x ^ 1 by
    funext x
    ring,
    intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem measurable_yoshidaRegularKernel_q :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem intervalIntegrable_regularKernel_mul_q
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦ yoshidaRegularKernel (yoshidaEndpointA * t) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (yoshidaEndpointA * t) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 4 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact (measurable_yoshidaRegularKernel_q.comp
      (measurable_const.mul measurable_id)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have harg0 : 0 ≤ yoshidaEndpointA * t :=
      mul_nonneg yoshidaEndpointA_pos.le htIcc.1
    have harg2 : yoshidaEndpointA * t ≤ Real.log 2 := by
      unfold yoshidaEndpointA
      nlinarith [mul_le_mul_of_nonneg_left htIcc.2
        (by positivity : 0 ≤ Real.log 2 / 2)]
    have hK := yoshidaRegularKernel_mem_Icc harg0 harg2
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK.1]
    exact mul_le_mul_of_nonneg_right hK.2 (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

theorem re_yoshidaEndpointRegularQuadratic_p5_eq :
    (yoshidaEndpointRegularQuadratic
      (fun x ↦ (factorTwoCenteredP5 x : ℂ))).re =
      oddP5CleanRegularPolynomial55 +
        oddCleanRegularEnvelopeError oddP5Correlation55 := by
  rw [re_yoshidaEndpointRegularQuadratic_eq_correlation _
    continuous_factorTwoCenteredP5]
  simp_rw [centeredEndpointCorrelation_p5]
  have hactual := intervalIntegrable_regularKernel_mul_q oddP5Correlation55
    continuous_oddP5Correlation55
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
          oddP5Correlation55 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    · unfold yoshidaRegularKernelPolynomial6 oddP5Correlation55
      fun_prop
  have herr : IntervalIntegrable
      (fun t : ℝ ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
            oddP5Correlation55 t) volume 0 2 := by
    apply (hactual.sub hpoly).congr
    intro t _ht
    ring
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernel (yoshidaEndpointA * t) * oddP5Correlation55 t) =
      fun t ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
            oddP5Correlation55 t +
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
          oddP5Correlation55 t by
      funext t
      ring,
    intervalIntegral.integral_add herr hpoly]
  have hmodel := integral_regularKernelPolynomial6_mul_oddP5Correlation55
  unfold oddCleanRegularEnvelopeError
  nlinarith

private theorem yoshidaEndpointCoshMoment_p5_eq_zero :
    yoshidaEndpointCoshMoment factorTwoCenteredP5 = 0 := by
  have h := centeredCoshMoment_eq_zero_of_odd odd_factorTwoCenteredP5
    (yoshidaEndpointA / 2)
  rw [show yoshidaEndpointCoshMoment factorTwoCenteredP5 =
      centeredCoshMoment factorTwoCenteredP5 (yoshidaEndpointA / 2) by
    unfold centeredCoshMoment yoshidaEndpointCoshMoment
    apply intervalIntegral.integral_congr
    intro x _hx
    ring]
  exact h

theorem yoshidaEndpointOddCleanQuadratic_p5_eq :
    yoshidaEndpointOddCleanQuadratic factorTwoCenteredP5 =
      (25402 / 38115 : ℝ) -
        (2 / 11 : ℝ) * (Real.log 2 + yoshidaEndpointScalarMassLoss) +
        plusP5OddQRawReserve -
        yoshidaEndpointA *
          (oddP5CleanRegularPolynomial55 +
            oddCleanRegularEnvelopeError oddP5Correlation55) -
        2 * yoshidaEndpointA * oddP5CleanSinhMoment ^ 2 := by
  unfold yoshidaEndpointOddCleanQuadratic
  dsimp only
  rw [integral_endpointPotential_mul_factorTwoCenteredP5_sq,
    integral_factorTwoCenteredP5_sq,
    re_yoshidaEndpointRegularQuadratic_p5_eq,
    yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments,
    yoshidaEndpointCoshMoment_p5_eq_zero]
  unfold plusP5OddQRawReserve oddP5CleanSinhMoment
  ring

theorem integral_plusP5OddCompletionProfile_sq :
    (∫ x : ℝ in -1..1, plusP5OddCompletionProfile x ^ 2) =
      (11355935597 / 2661120000 : ℝ) := by
  calc
    (∫ x : ℝ in -1..1, plusP5OddCompletionProfile x ^ 2) =
        centeredEndpointCorrelation plusP5OddCompletionProfile 0 := by
      unfold centeredEndpointCorrelation
      simp only [sub_zero, zero_add]
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    _ = plusP5OddQCorrelation 0 :=
      centeredEndpointCorrelation_plusP5OddCompletionProfile 0
    _ = (11355935597 / 2661120000 : ℝ) := by
      norm_num [plusP5OddQCorrelation, oddStructuralCorrelation11,
        oddStructuralCorrelation13, oddStructuralCorrelation33,
        oddP5Correlation15, oddP5Correlation35, oddP5Correlation55]

theorem centeredRawLogEnergy_plusP5OddCompletionProfile_eq :
    centeredRawLogEnergy plusP5OddCompletionProfile =
      (8 / 3 : ℝ) * (-10319 / 4800 : ℝ) ^ 2 +
        (44 / 21 : ℝ) * (15 / 8 : ℝ) ^ 2 +
        centeredRawLogEnergy factorTwoCenteredP5 := by
  have h := centeredRawLogEnergy_one_three_add_tail_explicit
    factorTwoCenteredP5 locallyLipschitzOn_factorTwoCenteredP5
    factorTwoCenteredP5_intrinsic_coefficients_zero.1
    factorTwoCenteredP5_intrinsic_coefficients_zero.2
    (-10319 / 4800 : ℝ) (15 / 8 : ℝ)
  simpa only [plusP5OddCompletionProfile] using h

private theorem intervalIntegrable_regularEnvelope_mul_q
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t : ℝ ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t)
      volume 0 2 := by
  have hactual := intervalIntegrable_regularKernel_mul_q C hC
  have hpoly : IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) * C t)
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    · apply Continuous.mul
      · unfold yoshidaRegularKernelPolynomial6
        fun_prop
      · exact hC
  apply (hactual.sub hpoly).congr
  intro t _ht
  ring

private theorem oddCleanRegularEnvelopeError_add_q
    (C D : ℝ → ℝ) (hC : Continuous C) (hD : Continuous D) :
    oddCleanRegularEnvelopeError (C + D) =
      oddCleanRegularEnvelopeError C + oddCleanRegularEnvelopeError D := by
  have hCI := intervalIntegrable_regularEnvelope_mul_q C hC
  have hDI := intervalIntegrable_regularEnvelope_mul_q D hD
  unfold oddCleanRegularEnvelopeError
  rw [show (fun t : ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * t) -
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
          (C + D) t) =
      fun t ↦
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t +
        (yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * D t by
    funext t
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add hCI hDI]
  ring

private theorem oddCleanRegularEnvelopeError_const_mul_q
    (c : ℝ) (C : ℝ → ℝ) :
    oddCleanRegularEnvelopeError (fun t ↦ c * C t) =
      c * oddCleanRegularEnvelopeError C := by
  unfold oddCleanRegularEnvelopeError
  rw [show (fun t : ℝ ↦
      (yoshidaRegularKernel (yoshidaEndpointA * t) -
        yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) *
          (c * C t)) =
      fun t ↦ c *
        ((yoshidaRegularKernel (yoshidaEndpointA * t) -
          yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)) * C t) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  ring

theorem plusP5OddQCleanEnvelope_eq_entries :
    plusP5OddQCleanEnvelope =
      (106481761 / 23040000 : ℝ) *
          oddCleanRegularEnvelopeError oddStructuralCorrelation11 -
        (10319 / 1280 : ℝ) *
          oddCleanRegularEnvelopeError oddStructuralCorrelation13 +
        (225 / 64 : ℝ) *
          oddCleanRegularEnvelopeError oddStructuralCorrelation33 -
        (10319 / 2400 : ℝ) * oddP5CleanRegularEnvelopeError15 +
        (15 / 4 : ℝ) * oddP5CleanRegularEnvelopeError35 +
        oddCleanRegularEnvelopeError oddP5Correlation55 := by
  let C11 : ℝ → ℝ := fun t ↦
    (106481761 / 23040000 : ℝ) * oddStructuralCorrelation11 t
  let C13 : ℝ → ℝ := fun t ↦
    (-10319 / 1280 : ℝ) * oddStructuralCorrelation13 t
  let C33 : ℝ → ℝ := fun t ↦
    (225 / 64 : ℝ) * oddStructuralCorrelation33 t
  let C15 : ℝ → ℝ := fun t ↦
    (-10319 / 2400 : ℝ) * oddP5Correlation15 t
  let C35 : ℝ → ℝ := fun t ↦
    (15 / 4 : ℝ) * oddP5Correlation35 t
  have h11 : Continuous oddStructuralCorrelation11 := by
    unfold oddStructuralCorrelation11; fun_prop
  have h13 : Continuous oddStructuralCorrelation13 := by
    unfold oddStructuralCorrelation13; fun_prop
  have h33 : Continuous oddStructuralCorrelation33 := by
    unfold oddStructuralCorrelation33; fun_prop
  have h15 : Continuous oddP5Correlation15 := by
    unfold oddP5Correlation15; fun_prop
  have h35 : Continuous oddP5Correlation35 := by
    unfold oddP5Correlation35; fun_prop
  have hC11 : Continuous C11 := by
    dsimp only [C11]; exact continuous_const.mul h11
  have hC13 : Continuous C13 := by
    dsimp only [C13]; exact continuous_const.mul h13
  have hC33 : Continuous C33 := by
    dsimp only [C33]; exact continuous_const.mul h33
  have hC15 : Continuous C15 := by
    dsimp only [C15]; exact continuous_const.mul h15
  have hC35 : Continuous C35 := by
    dsimp only [C35]; exact continuous_const.mul h35
  have hprofile : plusP5OddQCorrelation =
      C11 + C13 + C33 + C15 + C35 + oddP5Correlation55 := by
    funext t
    dsimp only [C11, C13, C33, C15, C35]
    simp only [Pi.add_apply]
    unfold plusP5OddQCorrelation
    ring
  unfold plusP5OddQCleanEnvelope
  rw [hprofile,
    oddCleanRegularEnvelopeError_add_q (C11 + C13 + C33 + C15 + C35)
      oddP5Correlation55
      ((((hC11.add hC13).add hC33).add hC15).add hC35)
      continuous_oddP5Correlation55,
    oddCleanRegularEnvelopeError_add_q (C11 + C13 + C33 + C15) C35
      (((hC11.add hC13).add hC33).add hC15) hC35,
    oddCleanRegularEnvelopeError_add_q (C11 + C13 + C33) C15
      ((hC11.add hC13).add hC33) hC15,
    oddCleanRegularEnvelopeError_add_q (C11 + C13) C33
      (hC11.add hC13) hC33,
    oddCleanRegularEnvelopeError_add_q C11 C13 hC11 hC13]
  dsimp only [C11, C13, C33, C15, C35]
  repeat rw [oddCleanRegularEnvelopeError_const_mul_q]
  unfold oddP5CleanRegularEnvelopeError15 oddP5CleanRegularEnvelopeError35
  ring

theorem plusP5OddQCleanPolynomial_eq_entries :
    plusP5OddQCleanPolynomial =
      (106481761 / 23040000 : ℝ) * oddCleanRegularPolynomialGram11 -
        (10319 / 1280 : ℝ) * oddCleanRegularPolynomialGram13 +
        (225 / 64 : ℝ) * oddCleanRegularPolynomialGram33 -
        (10319 / 2400 : ℝ) * oddP5CleanRegularPolynomial15 +
        (15 / 4 : ℝ) * oddP5CleanRegularPolynomial35 +
        oddP5CleanRegularPolynomial55 := by
  unfold plusP5OddQCleanPolynomial oddCleanRegularPolynomialGram11
    oddCleanRegularPolynomialGram13 oddCleanRegularPolynomialGram33
    oddP5CleanRegularPolynomial15 oddP5CleanRegularPolynomial35
    oddP5CleanRegularPolynomial55
  ring

theorem plusP5OddQPolynomialMoment_eq_entries :
    plusP5OddQPolynomialMoment =
      (106481761 / 23040000 : ℝ) * oddPolynomialMoment11 -
        (10319 / 1280 : ℝ) * oddPolynomialMoment13 +
        (225 / 64 : ℝ) * oddPolynomialMoment33 -
        (10319 / 2400 : ℝ) * oddP5PolynomialMoment15 +
        (15 / 4 : ℝ) * oddP5PolynomialMoment35 := by
  unfold plusP5OddQPolynomialMoment oddPolynomialMoment11
    oddPolynomialMoment13 oddPolynomialMoment33 oddP5PolynomialMoment15
    oddP5PolynomialMoment35
  ring

/-- Exact whole-profile identity for the completed negative-endpoint square.
Only one regular envelope and one pole-free analytic remainder survive. -/
theorem plusP5OddQ_eq_structuralProfile :
    plusP5OddQ =
      plusP5OddQAlgebraicBase + plusP5OddQRawReserve -
        yoshidaEndpointA * plusP5OddQCleanEnvelope -
        2 * yoshidaEndpointA * plusP5OddCompletionSinhMoment ^ 2 -
        poleFreeAnalyticError plusP5OddQCorrelation := by
  rw [poleFreeAnalyticError_plusP5OddQCorrelation_eq,
    plusP5OddQCleanEnvelope_eq_entries]
  unfold plusP5OddQ plusP5OddQAlgebraicBase plusP5OddQRawReserve
    plusP5OddCompletionSinhMoment
    factorTwoIntrinsicSixUnbalancedOMinus11
    factorTwoIntrinsicSixUnbalancedOMinus13
    factorTwoIntrinsicSixUnbalancedOMinus15
    factorTwoIntrinsicSixUnbalancedOMinus33
    factorTwoIntrinsicSixUnbalancedOMinus35
    factorTwoIntrinsicSixUnbalancedOMinus55
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33 factorTwoIntrinsicFourP45Cross15
    factorTwoIntrinsicFourP45Cross35 factorTwoIntrinsicP5PhaseDiagonal
  rw [plusP5OddQCleanPolynomial_eq_entries,
    plusP5OddQPolynomialMoment_eq_entries]
  rw [yoshidaEndpointOddLowGram11_structural_eq,
    yoshidaEndpointOddLowGram13_structural_eq,
    yoshidaEndpointOddLowGram33_structural_eq,
    cleanBilinear_p1_p5_eq, cleanBilinear_p3_p5_eq,
    yoshidaEndpointOddCleanQuadratic_p5_eq,
    factorTwoCenteredSymmetricPerturbation_p1_structural_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p1_p3_structural_eq,
    factorTwoCenteredSymmetricPerturbation_p3_structural_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p1_p5_structural_eq,
    factorTwoCenteredSymmetricPerturbationBilinear_p3_p5_structural_eq,
    factorTwoCenteredSymmetricPerturbation_p5_structural_eq,
    oddStructuralRegularError11_sharp_expansion,
    oddStructuralRegularError13_sharp_expansion,
    oddStructuralRegularError33_sharp_expansion]
  unfold plusP5OddQCorrelation plusP5OddQRawReserve
  ring

/-! ## Global structural boxes for the completed square -/

private theorem plusP5OddQRawReserve_nonneg :
    0 ≤ plusP5OddQRawReserve := by
  have hraw := factorTwoCenteredP5_raw_reserve
  have henergy : factorTwoIntrinsicEnergy factorTwoCenteredP5 =
      (2 / 11 : ℝ) := by
    simpa [factorTwoIntrinsicEnergy] using integral_factorTwoCenteredP5_sq
  rw [henergy] at hraw
  unfold plusP5OddQRawReserve
  nlinarith

private theorem abs_plusP5OddQCleanEnvelope_scaled_lt :
    |yoshidaEndpointA * plusP5OddQCleanEnvelope| <
      (3 / 500000 : ℝ) := by
  have herr := abs_oddCleanRegularEnvelopeError_le plusP5OddQCorrelation
    continuous_plusP5OddQCorrelation
  have hL1 := integral_abs_centeredEndpointCorrelation_le_energy
    plusP5OddCompletionProfile continuous_plusP5OddCompletionProfile
  simp_rw [centeredEndpointCorrelation_plusP5OddCompletionProfile] at hL1
  rw [integral_plusP5OddCompletionProfile_sq] at hL1
  have henv : |plusP5OddQCleanEnvelope| ≤
      (11355935597 / 2661120000 : ℝ) / 250000 := by
    unfold plusP5OddQCleanEnvelope
    calc
      |oddCleanRegularEnvelopeError plusP5OddQCorrelation| ≤
          (1 / 250000 : ℝ) *
            (∫ t : ℝ in 0..2, |plusP5OddQCorrelation t|) := herr
      _ ≤ (1 / 250000 : ℝ) *
          (11355935597 / 2661120000 : ℝ) :=
        mul_le_mul_of_nonneg_left hL1 (by norm_num)
      _ = (11355935597 / 2661120000 : ℝ) / 250000 := by ring
  have hA := plusP5_endpointA_pow_fine_bounds 1 (by norm_num)
  have hAhi : yoshidaEndpointA <
      (69314718057 / 200000000000 : ℝ) := by
    simpa using hA.2
  rw [abs_mul, abs_of_pos yoshidaEndpointA_pos]
  calc
    yoshidaEndpointA * |plusP5OddQCleanEnvelope| ≤
        yoshidaEndpointA *
          ((11355935597 / 2661120000 : ℝ) / 250000) :=
      mul_le_mul_of_nonneg_left henv yoshidaEndpointA_pos.le
    _ < (69314718057 / 200000000000 : ℝ) *
          ((11355935597 / 2661120000 : ℝ) / 250000) :=
      mul_lt_mul_of_pos_right hAhi (by norm_num)
    _ < (3 / 500000 : ℝ) := by norm_num

private theorem abs_poleFreeAnalyticError_plusP5OddQCorrelation_ultra_lt :
    |poleFreeAnalyticError plusP5OddQCorrelation| <
      (427 / 1000000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_lt_of_uniform_bound
    plusP5OddQCorrelation continuous_plusP5OddQCorrelation
      (11355935597 / 2661120000 : ℝ) (by norm_num)
      (fun t ht0 ht2 ↦ by
        rw [← centeredEndpointCorrelation_plusP5OddCompletionProfile t]
        have hcorr := abs_centeredEndpointCorrelation_le_energy
          plusP5OddCompletionProfile continuous_plusP5OddCompletionProfile
          ht0 ht2
        rw [integral_plusP5OddCompletionProfile_sq] at hcorr
        exact hcorr)
  calc
    |poleFreeAnalyticError plusP5OddQCorrelation| <
        (11355935597 / 2661120000 : ℝ) / 10000 := h
    _ < (427 / 1000000 : ℝ) := by norm_num

private theorem sqrt_two_q_ultra_bounds :
    (14142135623 / 10000000000 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < (14142135624 / 10000000000 : ℝ) := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith

private theorem log_two_div_sqrt_two_q_ultra_bounds :
    (4901290717 / 10000000000 : ℝ) < Real.log 2 / Real.sqrt 2 ∧
      Real.log 2 / Real.sqrt 2 < (4901290718 / 10000000000 : ℝ) := by
  have hlog := strict_log_two_fine_bounds
  have hs := sqrt_two_q_ultra_bounds
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [lt_div_iff₀ hspos, div_lt_iff₀ hspos]
  constructor <;> nlinarith

private theorem log_three_div_sqrt_three_q_ultra_bounds :
    (6342841 / 10000000 : ℝ) < Real.log 3 / Real.sqrt 3 ∧
      Real.log 3 / Real.sqrt 3 < (6342842 / 10000000 : ℝ) := by
  have hlog2 := strict_log_two_fine_bounds
  have hlog32 := strict_log_three_halves_fine_bounds
  have hlog3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    calc
      Real.log 3 = Real.log (2 * (3 / 2 : ℝ)) := by norm_num
      _ = Real.log 2 + Real.log (3 / 2) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hsSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsLower : (17320508 / 10000000 : ℝ) < Real.sqrt 3 := by
    nlinarith
  have hsUpper : Real.sqrt 3 < (17320509 / 10000000 : ℝ) := by
    nlinarith
  rw [lt_div_iff₀ hspos, div_lt_iff₀ hspos, hlog3]
  constructor <;> nlinarith

private theorem factorTwoPrimeRatio_q_ultra_bounds :
    (11699250014 / 10000000000 : ℝ) <
        factorTwoPrimeShift / yoshidaEndpointA ∧
      factorTwoPrimeShift / yoshidaEndpointA <
        (11699250015 / 10000000000 : ℝ) := by
  have hlog := strict_log_two_fine_bounds
  have hshift := strict_log_three_halves_fine_bounds
  constructor
  · rw [lt_div_iff₀ yoshidaEndpointA_pos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    nlinarith
  · rw [div_lt_iff₀ yoshidaEndpointA_pos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    nlinarith

private theorem plusP5OddQPolynomialMoment_bounds :
    (24 / 1000000 : ℝ) < plusP5OddQPolynomialMoment ∧
      plusP5OddQPolynomialMoment < (52 / 1000000 : ℝ) := by
  rcases poleFree_coefficient_bounds with
    ⟨_h0l, _h0u, h2l, h2u, h4l, h4u, h6l, h6u⟩
  unfold plusP5OddQPolynomialMoment polynomialD2 polynomialD4 polynomialD6
  constructor <;> nlinarith

private theorem plusP5OddQCleanPolynomial_scaled_lt :
    yoshidaEndpointA * plusP5OddQCleanPolynomial <
      (12301 / 1000000 : ℝ) := by
  have h2 := plusP5_endpointA_pow_fine_bounds 2 (by norm_num)
  have h3 := plusP5_endpointA_pow_fine_bounds 3 (by norm_num)
  have h4 := plusP5_endpointA_pow_fine_bounds 4 (by norm_num)
  have h5 := plusP5_endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := plusP5_endpointA_pow_fine_bounds 6 (by norm_num)
  have h7 := plusP5_endpointA_pow_fine_bounds 7 (by norm_num)
  unfold plusP5OddQCleanPolynomial
  ring_nf
  nlinarith

private theorem plusP5OddQCorrelation_prime_ultra_bounds :
    (-1998827 / 1000000 : ℝ) <
        plusP5OddQCorrelation
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      plusP5OddQCorrelation
          (factorTwoPrimeShift / yoshidaEndpointA) <
        (-999413 / 500000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 11699250014 / 10000000000
  have htau := factorTwoPrimeRatio_q_ultra_bounds
  have hy0 : 0 < y := by
    dsimp only [y, tau]
    linarith [htau.1]
  have hyU : y < (1 / 10000000000 : ℝ) := by
    dsimp only [y, tau]
    linarith [htau.2]
  have hy2 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (2 : ℕ) ≠ 0)
  have hy3 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (3 : ℕ) ≠ 0)
  have hy4 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (4 : ℕ) ≠ 0)
  have hy5 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (5 : ℕ) ≠ 0)
  have hy6 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (6 : ℕ) ≠ 0)
  have hy7 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (7 : ℕ) ≠ 0)
  have hy8 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (8 : ℕ) ≠ 0)
  have hy9 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (9 : ℕ) ≠ 0)
  have hy10 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (10 : ℕ) ≠ 0)
  have hy11 := pow_lt_pow_left₀ hyU hy0.le (by norm_num : (11 : ℕ) ≠ 0)
  have htauy : tau = 11699250014 / 10000000000 + y := by
    dsimp only [y]
    ring
  dsimp only [tau] at htauy ⊢
  rw [htauy, plusP5OddQCorrelation_polynomial]
  ring_nf
  constructor <;> nlinarith [hy2, hy3, hy4, hy5, hy6, hy7, hy8,
    hy9, hy10, hy11, sq_nonneg y, pow_nonneg hy0.le 3,
    pow_nonneg hy0.le 4, pow_nonneg hy0.le 5, pow_nonneg hy0.le 6,
    pow_nonneg hy0.le 7, pow_nonneg hy0.le 8, pow_nonneg hy0.le 9,
    pow_nonneg hy0.le 10, pow_nonneg hy0.le 11]

private theorem plusP5OddQPrimeProduct_ultra_bounds :
    (-6339122 / 5000000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          plusP5OddQCorrelation
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
      (Real.log 3 / Real.sqrt 3) *
          plusP5OddQCorrelation
            (factorTwoPrimeShift / yoshidaEndpointA) <
        (-12678235 / 10000000 : ℝ) := by
  have hbeta := log_three_div_sqrt_three_q_ultra_bounds
  have hcorr := plusP5OddQCorrelation_prime_ultra_bounds
  have hnegcorr :
      (999413 / 500000 : ℝ) <
          -plusP5OddQCorrelation
            (factorTwoPrimeShift / yoshidaEndpointA) ∧
        -plusP5OddQCorrelation
            (factorTwoPrimeShift / yoshidaEndpointA) <
          (1998827 / 1000000 : ℝ) := by
    constructor <;> linarith [hcorr.1, hcorr.2]
  have hbeta0 : 0 < Real.log 3 / Real.sqrt 3 := by
    linarith [hbeta.1]
  have hnegcorr0 : 0 < -plusP5OddQCorrelation
      (factorTwoPrimeShift / yoshidaEndpointA) := by
    linarith [hnegcorr.1]
  have hpositive :
      (12678235 / 10000000 : ℝ) <
          (Real.log 3 / Real.sqrt 3) *
            (-plusP5OddQCorrelation
              (factorTwoPrimeShift / yoshidaEndpointA)) ∧
        (Real.log 3 / Real.sqrt 3) *
            (-plusP5OddQCorrelation
              (factorTwoPrimeShift / yoshidaEndpointA)) <
          (6339122 / 5000000 : ℝ) := by
    constructor
    · calc
        (12678235 / 10000000 : ℝ) <
            (6342841 / 10000000 : ℝ) *
              (999413 / 500000 : ℝ) := by norm_num
        _ < (Real.log 3 / Real.sqrt 3) *
            (999413 / 500000 : ℝ) :=
          mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
        _ < (Real.log 3 / Real.sqrt 3) *
            (-plusP5OddQCorrelation
              (factorTwoPrimeShift / yoshidaEndpointA)) :=
          mul_lt_mul_of_pos_left hnegcorr.1 hbeta0
    · calc
        (Real.log 3 / Real.sqrt 3) *
            (-plusP5OddQCorrelation
              (factorTwoPrimeShift / yoshidaEndpointA)) <
            (6342842 / 10000000 : ℝ) *
              (-plusP5OddQCorrelation
                (factorTwoPrimeShift / yoshidaEndpointA)) :=
          mul_lt_mul_of_pos_right hbeta.2 hnegcorr0
        _ < (6342842 / 10000000 : ℝ) *
            (1998827 / 1000000 : ℝ) :=
          mul_lt_mul_of_pos_left hnegcorr.2 (by norm_num)
        _ < (6339122 / 5000000 : ℝ) := by norm_num
  constructor <;> nlinarith [hpositive.1, hpositive.2]

private theorem plusP5OddQAlgebraicBase_gt :
    (59537 / 50000 : ℝ) < plusP5OddQAlgebraicBase := by
  have hmass := plusP5_scalarMassLoss_fine_bounds
  have halpha := log_two_div_sqrt_two_q_ultra_bounds
  have hprime := plusP5OddQPrimeProduct_ultra_bounds
  have hclean := plusP5OddQCleanPolynomial_scaled_lt
  have hmoment := plusP5OddQPolynomialMoment_bounds
  have hlog := strict_log_two_fine_bounds
  unfold plusP5OddQAlgebraicBase
  nlinarith

private theorem exp_weighted_p3_integral_lower :
    (1 / 140 : ℝ) ≤
      Real.exp (-yoshidaEndpointA / 2) *
        ∫ t : ℝ in 0..1,
          Real.exp (yoshidaEndpointA * t) *
            (t ^ 3 * (1 - t) ^ 3) := by
  have hpoly :
      (∫ t : ℝ in 0..1,
        (yoshidaEndpointA * t - yoshidaEndpointA / 2 + 1) *
          (t ^ 3 * (1 - t) ^ 3)) = (1 / 140 : ℝ) := by
    ring_nf
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
    repeat rw [intervalIntegral.integral_mul_const]
    repeat rw [intervalIntegral.integral_const_mul]
    repeat rw [integral_pow]
    norm_num
    ring
  have hexp :
      Real.exp (-yoshidaEndpointA / 2) *
          (∫ t : ℝ in 0..1,
            Real.exp (yoshidaEndpointA * t) *
              (t ^ 3 * (1 - t) ^ 3)) =
        ∫ t : ℝ in 0..1,
          Real.exp (yoshidaEndpointA * t - yoshidaEndpointA / 2) *
            (t ^ 3 * (1 - t) ^ 3) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    change Real.exp (-yoshidaEndpointA / 2) *
        (Real.exp (yoshidaEndpointA * t) *
          (t ^ 3 * (1 - t) ^ 3)) =
      Real.exp (yoshidaEndpointA * t - yoshidaEndpointA / 2) *
        (t ^ 3 * (1 - t) ^ 3)
    calc
      _ = (Real.exp (-yoshidaEndpointA / 2) *
          Real.exp (yoshidaEndpointA * t)) *
            (t ^ 3 * (1 - t) ^ 3) := by ring
      _ = Real.exp (yoshidaEndpointA * t - yoshidaEndpointA / 2) *
          (t ^ 3 * (1 - t) ^ 3) := by
        rw [← Real.exp_add]
        congr 2
        ring
  rw [← hpoly, hexp]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hweight : 0 ≤ t ^ 3 * (1 - t) ^ 3 := by positivity
  exact mul_le_mul_of_nonneg_right
    (Real.add_one_le_exp (yoshidaEndpointA * t - yoshidaEndpointA / 2))
    hweight

private theorem oddCleanSinhMoment3_gt_ninety_nine_millionths :
    (99 / 1000000 : ℝ) < oddCleanSinhMoment3 := by
  have hmoment : oddCleanSinhMoment3 =
      centeredSinhMoment centeredP3 (yoshidaEndpointA / 2) := by
    unfold oddCleanSinhMoment3 yoshidaEndpointSinhMoment centeredSinhMoment
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hrod := centeredSinhMoment_centeredP3_rodrigues
    (yoshidaEndpointA / 2)
  have hweighted := exp_weighted_p3_integral_lower
  have hA3 := plusP5_endpointA_pow_fine_bounds 3 (by norm_num)
  have hscale :
      yoshidaEndpointA ^ 3 * (1 / 140 : ℝ) ≤
        yoshidaEndpointA ^ 3 *
          (Real.exp (-yoshidaEndpointA / 2) *
            ∫ t : ℝ in 0..1,
              Real.exp (yoshidaEndpointA * t) *
                (t ^ 3 * (1 - t) ^ 3)) :=
    mul_le_mul_of_nonneg_left hweighted (pow_nonneg yoshidaEndpointA_pos.le 3)
  rw [hmoment, hrod]
  rw [show (∫ t : ℝ in 0..1,
      Real.exp (2 * (yoshidaEndpointA / 2) * t) *
        (t ^ 3 * (1 - t) ^ 3)) =
      ∫ t : ℝ in 0..1,
        Real.exp (yoshidaEndpointA * t) *
          (t ^ 3 * (1 - t) ^ 3) by
    apply intervalIntegral.integral_congr
    intro t _ht
    change Real.exp (2 * (yoshidaEndpointA / 2) * t) *
        (t ^ 3 * (1 - t) ^ 3) =
      Real.exp (yoshidaEndpointA * t) * (t ^ 3 * (1 - t) ^ 3)
    rw [show 2 * (yoshidaEndpointA / 2) * t = yoshidaEndpointA * t by ring]]
  calc
    (99 / 1000000 : ℝ) <
        (69314718055 / 200000000000 : ℝ) ^ 3 / 420 := by norm_num
    _ < yoshidaEndpointA ^ 3 / 420 :=
      div_lt_div_of_pos_right hA3.1 (by norm_num)
    _ ≤ 2 * Real.exp (-(yoshidaEndpointA / 2)) *
          ((2 * (yoshidaEndpointA / 2)) ^ 3 / 6) *
            ∫ t : ℝ in 0..1,
              Real.exp (yoshidaEndpointA * t) *
                (t ^ 3 * (1 - t) ^ 3) := by
      calc
        yoshidaEndpointA ^ 3 / 420 ≤
            yoshidaEndpointA ^ 3 / 3 *
              (Real.exp (-yoshidaEndpointA / 2) *
                ∫ t : ℝ in 0..1,
                  Real.exp (yoshidaEndpointA * t) *
                    (t ^ 3 * (1 - t) ^ 3)) := by
          nlinarith [hscale]
        _ = _ := by ring

private theorem plusP5OddQHyperbolic_bounds :
    0 ≤ 2 * yoshidaEndpointA * plusP5OddCompletionSinhMoment ^ 2 ∧
      2 * yoshidaEndpointA * plusP5OddCompletionSinhMoment ^ 2 <
        (537 / 12500 : ℝ) := by
  have hm1 := oddCleanSinhMoment1_gt
  have hm1sq := oddCleanSinhMoment1_sq_lt
  have hm1hi : oddCleanSinhMoment1 < (14484 / 125000 : ℝ) := by
    nlinarith
  have hm3lo := oddCleanSinhMoment3_gt_ninety_nine_millionths
  have hm3hi : oddCleanSinhMoment3 < (1 / 4000 : ℝ) := by
    exact lt_of_le_of_lt (le_abs_self oddCleanSinhMoment3)
      abs_oddCleanSinhMoment3_lt
  have hm5lo := oddP5CleanSinhMoment_nonneg
  have hm5hi := oddP5CleanSinhMoment_lt
  have hSlower : (-248916 / 1000000 : ℝ) <
      plusP5OddCompletionSinhMoment := by
    unfold plusP5OddCompletionSinhMoment
    nlinarith
  have hSneg : plusP5OddCompletionSinhMoment < 0 := by
    unfold plusP5OddCompletionSinhMoment
    nlinarith
  have hsq : plusP5OddCompletionSinhMoment ^ 2 <
      (248916 / 1000000 : ℝ) ^ 2 := by
    have hprod : 0 <
        ((248916 / 1000000 : ℝ) + plusP5OddCompletionSinhMoment) *
          ((248916 / 1000000 : ℝ) - plusP5OddCompletionSinhMoment) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  constructor
  · exact mul_nonneg
      (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le) (sq_nonneg _)
  · rw [show 2 * yoshidaEndpointA = Real.log 2 by
      unfold yoshidaEndpointA
      ring]
    calc
      Real.log 2 * plusP5OddCompletionSinhMoment ^ 2 <
          Real.log 2 * (248916 / 1000000 : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_left hsq (Real.log_pos (by norm_num))
      _ < (69314718057 / 100000000000 : ℝ) *
          (248916 / 1000000 : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right strict_log_two_fine_bounds.2 (by norm_num)
      _ < (537 / 12500 : ℝ) := by norm_num

/-- Structural lower bound for the complete correlated negative-endpoint
odd square.  Every analytic estimate is global on its full interval. -/
theorem plusP5OddQ_gt_11473_div_10000 :
    (11473 / 10000 : ℝ) < plusP5OddQ := by
  have hbase := plusP5OddQAlgebraicBase_gt
  have hraw := plusP5OddQRawReserve_nonneg
  have henv := abs_lt.mp abs_plusP5OddQCleanEnvelope_scaled_lt
  have hhyper := plusP5OddQHyperbolic_bounds
  have hpfe := abs_lt.mp
    abs_poleFreeAnalyticError_plusP5OddQCorrelation_ultra_lt
  rw [plusP5OddQ_eq_structuralProfile]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural
