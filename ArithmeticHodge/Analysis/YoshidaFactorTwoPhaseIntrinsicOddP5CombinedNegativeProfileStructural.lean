import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural

noncomputable section

open MeasureTheory Real Set
open CenteredEndpointCorrelation
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddLowEndpointPositive

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

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural
