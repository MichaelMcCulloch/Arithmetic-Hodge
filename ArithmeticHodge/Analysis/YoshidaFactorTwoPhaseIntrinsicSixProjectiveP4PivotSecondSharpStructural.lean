import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural

noncomputable section

open MeasureTheory Polynomial Real Set
open CenteredEndpointCorrelation
open YoshidaConstantBounds
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenProjectedRemainderEnvelopeCoefficients
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoEndpointClean
open ThreeByThreePositiveMixedDeterminant
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Sharp structural reserve for the second projective pivot coefficient

The proof works in exact sum/difference coordinates and retains the correlated
endpoint boxes.  It does not pass through a near-singular Loewner lower matrix.
-/

/-! ## Sharp clean weak-coordinate box -/

private theorem log_pi_lt_1144730_div_million :
    Real.log Real.pi < (1144730 / 1000000 : ℝ) := by
  have hseries := Real.log_div_le_sum_range_add
    (x := (2141593 / 4141593 : ℝ)) (by norm_num) (by norm_num) 16
  have hrat : Real.log (3141593 / 1000000 : ℝ) <
      (1144730 / 1000000 : ℝ) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    linarith
  have hpi := Real.pi_lt_d6
  norm_num at hpi
  exact (Real.log_lt_log Real.pi_pos hpi).trans hrat

private theorem log_log_two_lt_neg_3665_div_ten_thousand :
    Real.log (Real.log 2) < (-3665 / 10000 : ℝ) := by
  have hseries := Real.sum_range_le_log_div
    (x := (30685 / 169315 : ℝ)) (by norm_num) (by norm_num) 6
  have hrat : (3665 / 10000 : ℝ) <
      Real.log (100000 / 69315 : ℝ) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    linarith
  have htwo : Real.log 2 < (69315 / 100000 : ℝ) := by
    linarith [strict_log_two_fine_bounds.2]
  have htwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv : (100000 / 69315 : ℝ) < (Real.log 2)⁻¹ := by
    rw [show (Real.log 2)⁻¹ = 1 / Real.log 2 by ring,
      lt_div_iff₀ htwoPos]
    norm_num at htwo ⊢
    linarith
  have hlogInv : (3665 / 10000 : ℝ) < Real.log ((Real.log 2)⁻¹) :=
    hrat.trans (Real.log_lt_log (by norm_num) hinv)
  rw [Real.log_inv] at hlogInv
  linarith

private theorem scalarMassLoss_lt_27109_div_20000 :
    yoshidaEndpointScalarMassLoss < (27109 / 20000 : ℝ) := by
  have hgamma :=
    YoshidaEndpointEvenSharpScalar.eulerMascheroniConstant_lt_twenty_eight_thousand_eight_hundred_sixty_one_div_fifty_thousand
  have hpi := log_pi_lt_1144730_div_million
  have hloglog := log_log_two_lt_neg_3665_div_ten_thousand
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsplit : Real.log (Real.pi * Real.log 2) =
      Real.log Real.pi + Real.log (Real.log 2) := by
    rw [Real.log_mul Real.pi_ne_zero hlogTwoPos.ne']
  unfold yoshidaEndpointScalarMassLoss
  rw [hsplit]
  linarith

private theorem endpointA_fine_bounds_here :
    (69314718055 / 200000000000 : ℝ) < yoshidaEndpointA ∧
      yoshidaEndpointA < (69314718057 / 200000000000 : ℝ) := by
  unfold yoshidaEndpointA
  constructor <;> linarith [strict_log_two_fine_bounds.1,
    strict_log_two_fine_bounds.2]

private theorem regular00_scaled_upper_here :
    yoshidaEndpointA *
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x) <
      (69314718057 / 200000000000 : ℝ) * (97104 / 100000 : ℝ) := by
  have hR := intrinsicEven_regularGram00_lt
  exact (mul_lt_mul_of_pos_left hR yoshidaEndpointA_pos).trans
    (mul_lt_mul_of_pos_right endpointA_fine_bounds_here.2 (by norm_num))

private theorem regular02_scaled_bounds_here :
    (69314718055 / 200000000000 : ℝ) * (191 / 50000 : ℝ) <
        -yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
              centeredEvenP2 x) ∧
      -yoshidaEndpointA *
          (∫ x : ℝ in -1..1,
            yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
              centeredEvenP2 x) <
        (69314718057 / 200000000000 : ℝ) * (77 / 20000 : ℝ) := by
  have hR := intrinsicEven_regularGram02_bounds
  have hA := endpointA_fine_bounds_here
  have hneg : (191 / 50000 : ℝ) <
      -(∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
          centeredEvenP2 x) := by
    linarith [hR.2]
  have hnegU :
      -(∫ x : ℝ in -1..1,
        yoshidaEndpointEvenRegularRepresenter centeredEvenP0 x *
          centeredEvenP2 x) < (77 / 20000 : ℝ) := by
    linarith [hR.1]
  constructor
  · nlinarith [mul_lt_mul_of_pos_right hA.1 (by norm_num :
        (0 : ℝ) < 191 / 50000),
      mul_lt_mul_of_pos_left hneg yoshidaEndpointA_pos]
  · have hp := mul_lt_mul hA.2 hnegU.le (by
        norm_num at hR
        linarith) (by norm_num : (0 : ℝ) ≤ 69314718057 / 200000000000)
    nlinarith

private theorem regular22_scaled_upper_here :
    yoshidaEndpointA *
        (∫ x : ℝ in -1..1,
          yoshidaEndpointEvenRegularRepresenter centeredEvenP2 x *
            centeredEvenP2 x) <
      (69314718057 / 200000000000 : ℝ) * (58 / 100000 : ℝ) := by
  have hR := intrinsicEven_regularGram22_lt
  exact (mul_lt_mul_of_pos_left hR yoshidaEndpointA_pos).trans
    (mul_lt_mul_of_pos_right endpointA_fine_bounds_here.2 (by norm_num))

private theorem hyper00_lower_here :
    2 * (69314718055 / 200000000000 : ℝ) *
        (2010024476 / 1000000000 : ℝ) ^ 2 <
      2 * yoshidaEndpointA *
        yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 := by
  have hA := endpointA_fine_bounds_here.1
  have hC := coshMoment_p0_bounds.1
  have hCsq : (2010024476 / 1000000000 : ℝ) ^ 2 <
      yoshidaEndpointCoshMoment centeredEvenP0 ^ 2 :=
    pow_lt_pow_left₀ hC (by norm_num) (by norm_num)
  nlinarith [mul_lt_mul_of_pos_right hA (by positivity),
    mul_lt_mul_of_pos_left hCsq yoshidaEndpointA_pos]

private theorem hyper02_bounds_here :
    2 * (69314718055 / 200000000000 : ℝ) *
        (2010024476 / 1000000000 : ℝ) *
          (4012369 / 1000000000 : ℝ) <
      2 * yoshidaEndpointA *
        yoshidaEndpointCoshMoment centeredEvenP0 *
          yoshidaEndpointCoshMoment centeredEvenP2 ∧
    2 * yoshidaEndpointA *
        yoshidaEndpointCoshMoment centeredEvenP0 *
          yoshidaEndpointCoshMoment centeredEvenP2 <
      2 * (69314718057 / 200000000000 : ℝ) *
        (2010024478 / 1000000000 : ℝ) *
          (4012371 / 1000000000 : ℝ) := by
  have hA := endpointA_fine_bounds_here
  have h0 := coshMoment_p0_bounds
  have h2 := coshMoment_p2_bounds
  have h0pos : 0 < yoshidaEndpointCoshMoment centeredEvenP0 := by
    linarith [h0.1]
  have h2pos : 0 < yoshidaEndpointCoshMoment centeredEvenP2 := by
    linarith [h2.1]
  constructor
  · have hp := mul_lt_mul h0.1 h2.1.le (by norm_num) h0pos.le
    nlinarith [mul_lt_mul_of_pos_right hA.1 (by positivity),
      mul_lt_mul_of_pos_left hp yoshidaEndpointA_pos]
  · have hp := mul_lt_mul h0.2 h2.2.le h2pos (by norm_num)
    nlinarith [mul_lt_mul_of_pos_right hA.2 (mul_pos h0pos h2pos),
      mul_lt_mul_of_pos_left hp (by norm_num :
        (0 : ℝ) < 69314718057 / 200000000000)]

private theorem hyper22_lower_here :
    2 * (69314718055 / 200000000000 : ℝ) *
        (4012369 / 1000000000 : ℝ) ^ 2 <
      2 * yoshidaEndpointA *
        yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 := by
  have hA := endpointA_fine_bounds_here.1
  have hC := coshMoment_p2_bounds.1
  have hCsq : (4012369 / 1000000000 : ℝ) ^ 2 <
      yoshidaEndpointCoshMoment centeredEvenP2 ^ 2 :=
    pow_lt_pow_left₀ hC (by norm_num) (by norm_num)
  nlinarith [mul_lt_mul_of_pos_right hA (by positivity),
    mul_lt_mul_of_pos_left hCsq yoshidaEndpointA_pos]

private theorem clean_low_sharp_bounds :
    (36672 / 100000 : ℝ) < yoshidaEndpointEvenLowGram00 ∧
      (34024 / 100000 : ℝ) < yoshidaEndpointEvenLowGram02 ∧
      yoshidaEndpointEvenLowGram02 < (34026 / 100000 : ℝ) ∧
      (32703 / 100000 : ℝ) < yoshidaEndpointEvenLowGram22 := by
  have hS := scalarMassLoss_lt_27109_div_20000
  have hR00 := regular00_scaled_upper_here
  have hR02 := regular02_scaled_bounds_here
  have hR22 := regular22_scaled_upper_here
  have hH00 := hyper00_lower_here
  have hH02 := hyper02_bounds_here
  have hH22 := hyper22_lower_here
  have hlog := strict_log_two_fine_bounds.2
  constructor
  · rw [intrinsicEven_cleanGram00_expansion, integral_endpointPotential_one]
    norm_num at hS hR00 hH00 hlog ⊢
    linarith
  constructor
  · rw [intrinsicEven_cleanGram02_expansion,
      integral_endpointPotential_mul_centeredEvenP2]
    norm_num at hR02 hH02 ⊢
    linarith
  constructor
  · rw [intrinsicEven_cleanGram02_expansion,
      integral_endpointPotential_mul_centeredEvenP2]
    norm_num at hR02 hH02 ⊢
    linarith
  · rw [intrinsicEven_cleanGram22_expansion,
      integral_endpointPotential_mul_centeredEvenP2_sq]
    norm_num at hS hR22 hH22 hlog ⊢
    linarith

private theorem negative_weak_eq_midpoint_sub_profile_error :
    evenNegativePerturbation00 - 2 * evenNegativePerturbation02 +
        evenNegativePerturbation22 =
      step01Midpoint00 - 2 * step01Midpoint02 + step01Midpoint22 -
        poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile 1 (-1))) := by
  have hneg := evenNegativePerturbation_profile_eq 1 (-1)
  have hkernel := factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq
    1 (-1)
  have hreg := evenStructuralRegularError_profile_sharp_expansion 1 (-1)
  rw [hkernel] at hneg
  unfold step01Midpoint00 step01Midpoint02 step01Midpoint22
    evenNegativePerturbationTaylor00 evenNegativePerturbationTaylor02
    evenNegativePerturbationTaylor22
  norm_num at hneg hreg ⊢
  linarith

private theorem negative_strong_eq_midpoint_sub_profile_error :
    evenNegativePerturbation00 + 2 * evenNegativePerturbation02 +
        evenNegativePerturbation22 =
      step01Midpoint00 + 2 * step01Midpoint02 + step01Midpoint22 -
        poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile 1 1)) := by
  have hneg := evenNegativePerturbation_profile_eq 1 1
  have hkernel := factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq
    1 1
  have hreg := evenStructuralRegularError_profile_sharp_expansion 1 1
  rw [hkernel] at hneg
  unfold step01Midpoint00 step01Midpoint02 step01Midpoint22
    evenNegativePerturbationTaylor00 evenNegativePerturbationTaylor02
    evenNegativePerturbationTaylor22
  norm_num at hneg hreg ⊢
  linarith

private theorem abs_profile_error_strong_le :
    |poleFreeAnalyticError
        (centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile 1 1))| ≤ (9 / 10000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_profile_le 1 1
  norm_num at h ⊢
  exact h

private theorem abs_profile_error_weak_le :
    |poleFreeAnalyticError
        (centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile 1 (-1)))| ≤ (9 / 10000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_profile_le 1 (-1)
  norm_num at h ⊢
  exact h

private theorem abs_step01_error00_le_here :
    |step01AnalyticError00| ≤ (3 / 4000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_profile_le 1 0
  have hfun : centeredEndpointCorrelation
      (factorTwoEvenStructuralLowProfile 1 0) = evenStructuralCorrelation00 := by
    funext t
    rw [centeredEndpointCorrelation_evenStructuralProfile]
    norm_num
  rw [hfun] at h
  norm_num [step01AnalyticError00] at h ⊢
  exact h

private theorem abs_step01_error22_le_here :
    |step01AnalyticError22| ≤ (3 / 20000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_profile_le 0 1
  have hfun : centeredEndpointCorrelation
      (factorTwoEvenStructuralLowProfile 0 1) = evenStructuralCorrelation22 := by
    funext t
    rw [centeredEndpointCorrelation_evenStructuralProfile]
    norm_num
  rw [hfun] at h
  norm_num [step01AnalyticError22] at h ⊢
  exact h

/-! The exact clean midpoint and its negative perturbation in the aligned
`P₀ ± P₂` basis.  All twelve coordinates below are positive. -/

private def cleanStrong : ℝ :=
  yoshidaEndpointEvenLowGram00 + 2 * yoshidaEndpointEvenLowGram02 +
    yoshidaEndpointEvenLowGram22

private def cleanSkew : ℝ :=
  yoshidaEndpointEvenLowGram00 - yoshidaEndpointEvenLowGram22

private def cleanCrossSum : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
    yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4

private def cleanWeak : ℝ :=
  yoshidaEndpointEvenLowGram00 - 2 * yoshidaEndpointEvenLowGram02 +
    yoshidaEndpointEvenLowGram22

private def cleanCrossDifference : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
    yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4

private def cleanP4 : ℝ :=
  yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4

private def perturbStrong : ℝ :=
  evenNegativePerturbation00 + 2 * evenNegativePerturbation02 +
    evenNegativePerturbation22

private def perturbSkew : ℝ :=
  evenNegativePerturbation00 - evenNegativePerturbation22

private def perturbCrossSum : ℝ :=
  cleanCrossSum - factorTwoIntrinsicP4PlusCrossSum

private def perturbWeak : ℝ :=
  evenNegativePerturbation00 - 2 * evenNegativePerturbation02 +
    evenNegativePerturbation22

private def perturbCrossDifference : ℝ :=
  cleanCrossDifference - factorTwoIntrinsicP4PlusCrossDifference

private def perturbP4 : ℝ :=
  -factorTwoCenteredSymmetricPerturbation factorTwoCenteredP4

private theorem clean_aligned_bounds :
    (137423 / 100000 : ℝ) < cleanStrong ∧
      cleanStrong < (137442 / 100000 : ℝ) ∧
      (3962 / 100000 : ℝ) < cleanSkew ∧
      cleanSkew < (3977 / 100000 : ℝ) ∧
      (242817 / 1000000 : ℝ) < cleanCrossSum ∧
      cleanCrossSum < (242898 / 1000000 : ℝ) ∧
      (1323 / 100000 : ℝ) < cleanWeak ∧
      cleanWeak < (1342 / 100000 : ℝ) ∧
      (42817 / 1000000 : ℝ) < cleanCrossDifference ∧
      cleanCrossDifference < (42898 / 1000000 : ℝ) ∧
      (1571 / 5000 : ℝ) < cleanP4 := by
  have hs := clean_low_sharp_bounds
  have h00U := intrinsicEven_cleanGram00_lt_step01
  have h22U := intrinsicEven_cleanGram22_lt_step01
  have hsum :=
    factorTwoIntrinsicP4CleanCross_sum_sub_seventeen_seventieths_abs_lt
  have hdiff :=
    factorTwoIntrinsicP4CleanCross_difference_sub_three_seventieths_abs_lt
  have h44 := one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  rw [abs_lt] at hsum hdiff
  unfold cleanStrong cleanSkew cleanCrossSum cleanWeak
    cleanCrossDifference cleanP4
  norm_num at hs h00U h22U hsum hdiff h44 ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem perturb_aligned_bounds :
    (824479 / 1000000 : ℝ) < perturbStrong ∧
      perturbStrong < (826465 / 1000000 : ℝ) ∧
      (37851 / 1000000 : ℝ) < perturbSkew ∧
      perturbSkew < (39761 / 1000000 : ℝ) ∧
      (49817 / 1000000 : ℝ) < perturbCrossSum ∧
      perturbCrossSum < (57183 / 1000000 : ℝ) ∧
      (5179 / 1000000 : ℝ) < perturbWeak ∧
      perturbWeak < (7165 / 1000000 : ℝ) ∧
      (23317 / 1000000 : ℝ) < perturbCrossDifference ∧
      perturbCrossDifference < (27183 / 1000000 : ℝ) ∧
      (17 / 100 : ℝ) < perturbP4 ∧
      perturbP4 < (4416 / 25000 : ℝ) := by
  have hm00L := step01Midpoint00_gt
  have hm00U := step01Midpoint00_lt
  have hm02L := step01Midpoint02_gt
  have hm02U := step01Midpoint02_lt
  have hm22L := step01Midpoint22_gt
  have hm22U := step01Midpoint22_lt
  have heStrong := abs_le.mp abs_profile_error_strong_le
  have heWeak := abs_le.mp abs_profile_error_weak_le
  have he00 := abs_le.mp abs_step01_error00_le_here
  have he22 := abs_le.mp abs_step01_error22_le_here
  have hneg := step01_negativePerturbation_eq_midpoint_sub_error
  have hclean := clean_aligned_bounds
  have hpS := factorTwoIntrinsicP4PlusCrossSum_bounds
  have hpD := factorTwoIntrinsicP4PlusCrossDifference_bounds
  have hm := factorTwoIntrinsicP4MinusCross_sum_difference_bounds
  have hsumMid : factorTwoIntrinsicP4MinusCrossSum +
      factorTwoIntrinsicP4PlusCrossSum = 2 * cleanCrossSum := by
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4PlusCrossSum cleanCrossSum
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    ring
  have hdiffMid : factorTwoIntrinsicP4MinusCrossDifference +
      factorTwoIntrinsicP4PlusCrossDifference = 2 * cleanCrossDifference := by
    unfold factorTwoIntrinsicP4MinusCrossDifference
      factorTwoIntrinsicP4PlusCrossDifference cleanCrossDifference
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    ring
  have h44L := factorTwoIntrinsicP4Perturbation_lt_neg_seventeen_hundredths
  have h44U := factorTwoCenteredSymmetricPerturbation_p4_lower
  unfold perturbStrong perturbSkew perturbCrossSum perturbWeak
    perturbCrossDifference perturbP4
  rw [negative_strong_eq_midpoint_sub_profile_error,
    negative_weak_eq_midpoint_sub_profile_error]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · rw [hneg.1, hneg.2.2]
    linarith
  constructor
  · rw [hneg.1, hneg.2.2]
    linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-! ## Cancellation-preserving reserve polynomial -/

/-- The reverse mixed determinant after writing the negative endpoint as
`clean + perturbation` and the positive endpoint as `clean - perturbation`.
The two skew coordinates are stored with their positive signs. -/
private def alignedReserve
    (A X R C D F a y r c d f : ℝ) : ℝ :=
  let KF :=
    3 * (A * C - X ^ 2) + (C * a + A * c - 2 * X * y) -
      (a * c - y ^ 2)
  let Kf :=
    (A * C - X ^ 2) - (A * c + C * a - 2 * X * y) -
      3 * (a * c - y ^ 2)
  F * KF + f * Kf -
    (6 * X + 2 * y) * R * D - (3 * A + a) * D ^ 2 -
    (3 * C + c) * R ^ 2 - 2 * (X * D + R * C) * r -
    2 * (X * R + A * D) * d + (A + 3 * a) * d ^ 2 +
    (C + 3 * c) * r ^ 2 + 2 * (X + 3 * y) * r * d +
    2 * (y * d + r * c) * R + 2 * (y * r + a * d) * D

private theorem alignedReserve_eq_mixedDeterminantOne
    (A X R C D F a y r c d f : ℝ) :
    alignedReserve A X R C D F a y r c d f =
      mixedDeterminantOne
        (A + a) (-(X + y)) (R + r) (C + c) (D + d) (F + f)
        (A - a) (y - X) (R - r) (C - c) (D - d) (F - f) := by
  unfold alignedReserve mixedDeterminantOne
  ring

/-! ## Exact aligned-coordinate expansion -/

/-- Replacing the first two coordinates by `P₀ + P₂` and `P₂ - P₀`
multiplies every determinant coefficient by four.  This is the algebraic
normal form used below; in particular, the small low-block eigenvalue is an
explicit diagonal coordinate rather than the difference of two large terms. -/
private theorem four_mul_mixedDeterminantOne_eq_aligned
    (a b r c s f A B R C S F : ℝ) :
    4 * mixedDeterminantOne a b r c s f A B R C S F =
      mixedDeterminantOne
        (a + 2 * b + c) (c - a) (r + s)
        (a - 2 * b + c) (s - r) f
        (A + 2 * B + C) (C - A) (R + S)
        (A - 2 * B + C) (S - R) F := by
  unfold mixedDeterminantOne
  ring

/-- The two phase endpoints have the clean low Gram as their exact midpoint. -/
private theorem low_endpoint_midpoint_exact :
    factorTwoStructuralPhaseLow00 1 + factorTwoStructuralPhaseLow00 (-1) =
        2 * yoshidaEndpointEvenLowGram00 ∧
      factorTwoStructuralPhaseLow02 1 + factorTwoStructuralPhaseLow02 (-1) =
        2 * yoshidaEndpointEvenLowGram02 ∧
      factorTwoStructuralPhaseLow22 1 + factorTwoStructuralPhaseLow22 (-1) =
        2 * yoshidaEndpointEvenLowGram22 := by
  unfold factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22
  constructor
  · ring
  constructor <;> ring

/-- The same exact midpoint correlation holds for both `P₄` crosses and its
diagonal. -/
private theorem p4_endpoint_midpoint_exact :
    factorTwoIntrinsicFourP45Cross04 1 +
          factorTwoIntrinsicFourP45Cross04 (-1) =
        2 * yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 ∧
      factorTwoIntrinsicFourP45Cross24 1 +
          factorTwoIntrinsicFourP45Cross24 (-1) =
        2 * yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 ∧
      factorTwoIntrinsicSixP4Diagonal 1 +
          factorTwoIntrinsicSixP4Diagonal (-1) =
        2 * yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4 := by
  unfold factorTwoIntrinsicFourP45Cross04
    factorTwoIntrinsicFourP45Cross24 factorTwoIntrinsicSixP4Diagonal
    factorTwoEndpointPhaseDiagonal
  constructor
  · ring
  constructor <;> ring

/-- Exact reverse mixed coefficient in the aligned basis. -/
private theorem four_mul_pivotCoeff_two_eq_aligned :
    4 * pivotCoeff 2 =
      mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 (-1) +
          2 * factorTwoStructuralPhaseLow02 (-1) +
          factorTwoStructuralPhaseLow22 (-1))
        (factorTwoStructuralPhaseLow22 (-1) -
          factorTwoStructuralPhaseLow00 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1) +
          factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoStructuralPhaseLow00 (-1) -
          2 * factorTwoStructuralPhaseLow02 (-1) +
          factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1) -
          factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))
        (factorTwoStructuralPhaseLow00 1 +
          2 * factorTwoStructuralPhaseLow02 1 +
          factorTwoStructuralPhaseLow22 1)
        (factorTwoStructuralPhaseLow22 1 -
          factorTwoStructuralPhaseLow00 1)
        (factorTwoIntrinsicFourP45Cross04 1 +
          factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoStructuralPhaseLow00 1 -
          2 * factorTwoStructuralPhaseLow02 1 +
          factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1 -
          factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoIntrinsicSixP4Diagonal 1) := by
  rw [pivotCoeff_two_eq_exact_mixed]
  exact four_mul_mixedDeterminantOne_eq_aligned _ _ _ _ _ _ _ _ _ _ _ _

private theorem four_mul_pivotCoeff_two_eq_reserve :
    4 * pivotCoeff 2 =
      alignedReserve cleanStrong cleanSkew cleanCrossSum cleanWeak
        cleanCrossDifference cleanP4 perturbStrong perturbSkew
        perturbCrossSum perturbWeak perturbCrossDifference perturbP4 := by
  rw [four_mul_pivotCoeff_two_eq_aligned,
    alignedReserve_eq_mixedDeterminantOne]
  unfold cleanStrong cleanSkew cleanCrossSum cleanWeak cleanCrossDifference
    cleanP4 perturbStrong perturbSkew perturbCrossSum perturbWeak
    perturbCrossDifference perturbP4
    factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22 evenNegativePerturbation00
    evenNegativePerturbation02 evenNegativePerturbation22
    factorTwoIntrinsicP4PlusCrossSum factorTwoIntrinsicP4PlusCrossDifference
    factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    factorTwoIntrinsicSixP4Diagonal factorTwoEndpointPhaseDiagonal
  unfold cleanCrossSum cleanCrossDifference
  ring

private theorem positive_mul_bounds
    {u v lu ru lv rv : ℝ}
    (hlu0 : 0 ≤ lu) (hlv0 : 0 ≤ lv)
    (hlu : lu ≤ u) (hru : u ≤ ru)
    (hlv : lv ≤ v) (hrv : v ≤ rv) :
    lu * lv ≤ u * v ∧ u * v ≤ ru * rv := by
  have hu0 : 0 ≤ u := hlu0.trans hlu
  have hv0 : 0 ≤ v := hlv0.trans hlv
  constructor
  · calc
      lu * lv ≤ u * lv := mul_le_mul_of_nonneg_right hlu hlv0
      _ ≤ u * v := mul_le_mul_of_nonneg_left hlv hu0
  · calc
      u * v ≤ ru * v := mul_le_mul_of_nonneg_right hru hv0
      _ ≤ ru * rv := mul_le_mul_of_nonneg_left hrv (hu0.trans hru)

private theorem positive_sq_bounds
    {u lu ru : ℝ} (hlu0 : 0 ≤ lu) (hlu : lu ≤ u) (hru : u ≤ ru) :
    lu ^ 2 ≤ u ^ 2 ∧ u ^ 2 ≤ ru ^ 2 := by
  have hu0 : 0 ≤ u := hlu0.trans hlu
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlu) (add_nonneg hu0 hlu0)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hru)
      (add_nonneg (hu0.trans hru) hu0)]

private theorem alignedReserve_box_gt
    {A X R C D F a y r c d f : ℝ}
    (hA : (137423 / 100000 : ℝ) < A ∧ A < 137442 / 100000)
    (hX : (3962 / 100000 : ℝ) < X ∧ X < 3977 / 100000)
    (hR : (242817 / 1000000 : ℝ) < R ∧ R < 242898 / 1000000)
    (hC : (1323 / 100000 : ℝ) < C ∧ C < 1342 / 100000)
    (hD : (42817 / 1000000 : ℝ) < D ∧ D < 42898 / 1000000)
    (hF : (1571 / 5000 : ℝ) < F)
    (ha : (824479 / 1000000 : ℝ) < a ∧ a < 826465 / 1000000)
    (hy : (37851 / 1000000 : ℝ) < y ∧ y < 39761 / 1000000)
    (hr : (49817 / 1000000 : ℝ) < r ∧ r < 57183 / 1000000)
    (hc : (5179 / 1000000 : ℝ) < c ∧ c < 7165 / 1000000)
    (hd : (23317 / 1000000 : ℝ) < d ∧ d < 27183 / 1000000)
    (hf : (17 / 100 : ℝ) < f ∧ f < 4416 / 25000) :
    (16 / 5000 : ℝ) < alignedReserve A X R C D F a y r c d f := by
  have hySq := positive_sq_bounds (u := y)
    (lu := (37851 / 1000000 : ℝ)) (ru := 39761 / 1000000)
    (by norm_num) hy.1.le hy.2.le
  have hXsq := positive_sq_bounds (u := X)
    (lu := (3962 / 100000 : ℝ)) (ru := 3977 / 100000)
    (by norm_num) hX.1.le hX.2.le
  have hac := positive_mul_bounds (u := a) (v := c)
    (lu := (824479 / 1000000 : ℝ)) (ru := 826465 / 1000000)
    (lv := (5179 / 1000000 : ℝ)) (rv := 7165 / 1000000)
    (by norm_num) (by norm_num) ha.1.le ha.2.le hc.1.le hc.2.le
  have hCa := positive_mul_bounds (u := C) (v := a)
    (lu := (1323 / 100000 : ℝ)) (ru := 1342 / 100000)
    (lv := (824479 / 1000000 : ℝ)) (rv := 826465 / 1000000)
    (by norm_num) (by norm_num) hC.1.le hC.2.le ha.1.le ha.2.le
  have hXy := positive_mul_bounds (u := X) (v := y)
    (lu := (3962 / 100000 : ℝ)) (ru := 3977 / 100000)
    (lv := (37851 / 1000000 : ℝ)) (rv := 39761 / 1000000)
    (by norm_num) (by norm_num) hX.1.le hX.2.le hy.1.le hy.2.le
  have hAc := positive_mul_bounds (u := A) (v := c)
    (lu := (137423 / 100000 : ℝ)) (ru := 137442 / 100000)
    (lv := (5179 / 1000000 : ℝ)) (rv := 7165 / 1000000)
    (by norm_num) (by norm_num) hA.1.le hA.2.le hc.1.le hc.2.le
  have hAC := positive_mul_bounds (u := A) (v := C)
    (lu := (137423 / 100000 : ℝ)) (ru := 137442 / 100000)
    (lv := (1323 / 100000 : ℝ)) (rv := 1342 / 100000)
    (by norm_num) (by norm_num) hA.1.le hA.2.le hC.1.le hC.2.le
  have hdSq := positive_sq_bounds (u := d)
    (lu := (23317 / 1000000 : ℝ)) (ru := 27183 / 1000000)
    (by norm_num) hd.1.le hd.2.le
  have hDSq := positive_sq_bounds (u := D)
    (lu := (42817 / 1000000 : ℝ)) (ru := 42898 / 1000000)
    (by norm_num) hD.1.le hD.2.le
  have hrSq := positive_sq_bounds (u := r)
    (lu := (49817 / 1000000 : ℝ)) (ru := 57183 / 1000000)
    (by norm_num) hr.1.le hr.2.le
  have hRSq := positive_sq_bounds (u := R)
    (lu := (242817 / 1000000 : ℝ)) (ru := 242898 / 1000000)
    (by norm_num) hR.1.le hR.2.le
  have hDd := positive_mul_bounds (u := D) (v := d)
    (lu := (42817 / 1000000 : ℝ)) (ru := 42898 / 1000000)
    (lv := (23317 / 1000000 : ℝ)) (rv := 27183 / 1000000)
    (by norm_num) (by norm_num) hD.1.le hD.2.le hd.1.le hd.2.le
  have hDa := positive_mul_bounds (u := D) (v := a)
    (lu := (42817 / 1000000 : ℝ)) (ru := 42898 / 1000000)
    (lv := (824479 / 1000000 : ℝ)) (rv := 826465 / 1000000)
    (by norm_num) (by norm_num) hD.1.le hD.2.le ha.1.le ha.2.le
  have hrd := positive_mul_bounds (u := r) (v := d)
    (lu := (49817 / 1000000 : ℝ)) (ru := 57183 / 1000000)
    (lv := (23317 / 1000000 : ℝ)) (rv := 27183 / 1000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le hd.1.le hd.2.le
  have hDr := positive_mul_bounds (u := D) (v := r)
    (lu := (42817 / 1000000 : ℝ)) (ru := 42898 / 1000000)
    (lv := (49817 / 1000000 : ℝ)) (rv := 57183 / 1000000)
    (by norm_num) (by norm_num) hD.1.le hD.2.le hr.1.le hr.2.le
  have hRd := positive_mul_bounds (u := R) (v := d)
    (lu := (242817 / 1000000 : ℝ)) (ru := 242898 / 1000000)
    (lv := (23317 / 1000000 : ℝ)) (rv := 27183 / 1000000)
    (by norm_num) (by norm_num) hR.1.le hR.2.le hd.1.le hd.2.le
  have hRD := positive_mul_bounds (u := R) (v := D)
    (lu := (242817 / 1000000 : ℝ)) (ru := 242898 / 1000000)
    (lv := (42817 / 1000000 : ℝ)) (rv := 42898 / 1000000)
    (by norm_num) (by norm_num) hR.1.le hR.2.le hD.1.le hD.2.le
  have hrc := positive_mul_bounds (u := r) (v := c)
    (lu := (49817 / 1000000 : ℝ)) (ru := 57183 / 1000000)
    (lv := (5179 / 1000000 : ℝ)) (rv := 7165 / 1000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le hc.1.le hc.2.le
  have hyd := positive_mul_bounds (u := y) (v := d)
    (lu := (37851 / 1000000 : ℝ)) (ru := 39761 / 1000000)
    (lv := (23317 / 1000000 : ℝ)) (rv := 27183 / 1000000)
    (by norm_num) (by norm_num) hy.1.le hy.2.le hd.1.le hd.2.le
  have hDy := positive_mul_bounds (u := D) (v := y)
    (lu := (42817 / 1000000 : ℝ)) (ru := 42898 / 1000000)
    (lv := (37851 / 1000000 : ℝ)) (rv := 39761 / 1000000)
    (by norm_num) (by norm_num) hD.1.le hD.2.le hy.1.le hy.2.le
  have hCr := positive_mul_bounds (u := C) (v := r)
    (lu := (1323 / 100000 : ℝ)) (ru := 1342 / 100000)
    (lv := (49817 / 1000000 : ℝ)) (rv := 57183 / 1000000)
    (by norm_num) (by norm_num) hC.1.le hC.2.le hr.1.le hr.2.le
  have hXd := positive_mul_bounds (u := X) (v := d)
    (lu := (3962 / 100000 : ℝ)) (ru := 3977 / 100000)
    (lv := (23317 / 1000000 : ℝ)) (rv := 27183 / 1000000)
    (by norm_num) (by norm_num) hX.1.le hX.2.le hd.1.le hd.2.le
  have hXD := positive_mul_bounds (u := X) (v := D)
    (lu := (3962 / 100000 : ℝ)) (ru := 3977 / 100000)
    (lv := (42817 / 1000000 : ℝ)) (rv := 42898 / 1000000)
    (by norm_num) (by norm_num) hX.1.le hX.2.le hD.1.le hD.2.le
  have haf := positive_mul_bounds (u := a) (v := f)
    (lu := (824479 / 1000000 : ℝ)) (ru := 826465 / 1000000)
    (lv := (17 / 100 : ℝ)) (rv := 4416 / 25000)
    (by norm_num) (by norm_num) ha.1.le ha.2.le hf.1.le hf.2.le
  have hRr := positive_mul_bounds (u := R) (v := r)
    (lu := (242817 / 1000000 : ℝ)) (ru := 242898 / 1000000)
    (lv := (49817 / 1000000 : ℝ)) (rv := 57183 / 1000000)
    (by norm_num) (by norm_num) hR.1.le hR.2.le hr.1.le hr.2.le
  have hyr := positive_mul_bounds (u := y) (v := r)
    (lu := (37851 / 1000000 : ℝ)) (ru := 39761 / 1000000)
    (lv := (49817 / 1000000 : ℝ)) (rv := 57183 / 1000000)
    (by norm_num) (by norm_num) hy.1.le hy.2.le hr.1.le hr.2.le
  have had := positive_mul_bounds (u := a) (v := d)
    (lu := (824479 / 1000000 : ℝ)) (ru := 826465 / 1000000)
    (lv := (23317 / 1000000 : ℝ)) (rv := 27183 / 1000000)
    (by norm_num) (by norm_num) ha.1.le ha.2.le hd.1.le hd.2.le
  have hRy := positive_mul_bounds (u := R) (v := y)
    (lu := (242817 / 1000000 : ℝ)) (ru := 242898 / 1000000)
    (lv := (37851 / 1000000 : ℝ)) (rv := 39761 / 1000000)
    (by norm_num) (by norm_num) hR.1.le hR.2.le hy.1.le hy.2.le
  have hXr := positive_mul_bounds (u := X) (v := r)
    (lu := (3962 / 100000 : ℝ)) (ru := 3977 / 100000)
    (lv := (49817 / 1000000 : ℝ)) (rv := 57183 / 1000000)
    (by norm_num) (by norm_num) hX.1.le hX.2.le hr.1.le hr.2.le
  have hXR := positive_mul_bounds (u := X) (v := R)
    (lu := (3962 / 100000 : ℝ)) (ru := 3977 / 100000)
    (lv := (242817 / 1000000 : ℝ)) (rv := 242898 / 1000000)
    (by norm_num) (by norm_num) hX.1.le hX.2.le hR.1.le hR.2.le
  have hAd := positive_mul_bounds (u := A) (v := d)
    (lu := (137423 / 100000 : ℝ)) (ru := 137442 / 100000)
    (lv := (23317 / 1000000 : ℝ)) (rv := 27183 / 1000000)
    (by norm_num) (by norm_num) hA.1.le hA.2.le hd.1.le hd.2.le
  have hAD := positive_mul_bounds (u := A) (v := D)
    (lu := (137423 / 100000 : ℝ)) (ru := 137442 / 100000)
    (lv := (42817 / 1000000 : ℝ)) (rv := 42898 / 1000000)
    (by norm_num) (by norm_num) hA.1.le hA.2.le hD.1.le hD.2.le
  have hRc := positive_mul_bounds (u := R) (v := c)
    (lu := (242817 / 1000000 : ℝ)) (ru := 242898 / 1000000)
    (lv := (5179 / 1000000 : ℝ)) (rv := 7165 / 1000000)
    (by norm_num) (by norm_num) hR.1.le hR.2.le hc.1.le hc.2.le
  have hRC := positive_mul_bounds (u := R) (v := C)
    (lu := (242817 / 1000000 : ℝ)) (ru := 242898 / 1000000)
    (lv := (1323 / 100000 : ℝ)) (rv := 1342 / 100000)
    (by norm_num) (by norm_num) hR.1.le hR.2.le hC.1.le hC.2.le
  have hsF : 0 < y ^ 2 - a * c + C * a - 2 * X * y -
      3 * X ^ 2 + A * c + 3 * A * C := by
    nlinarith only [hySq.1, hac.2, hCa.1, hXy.2, hXsq.2,
      hAc.1, hAC.1]
  have hFstep :
      alignedReserve A X R C D (1571 / 5000) a y r c d f <
        alignedReserve A X R C D F a y r c d f := by
    have heq : alignedReserve A X R C D F a y r c d f -
          alignedReserve A X R C D (1571 / 5000) a y r c d f =
        (F - 1571 / 5000) *
          (y ^ 2 - a * c + C * a - 2 * X * y - 3 * X ^ 2 +
            A * c + 3 * A * C) := by
      unfold alignedReserve
      ring
    have hp := mul_pos (sub_pos.mpr hF) hsF
    linarith only [heq, hp]
  have hsf : 3 * y ^ 2 - 3 * a * c - C * a + 2 * X * y -
      X ^ 2 - A * c + A * C < 0 := by
    nlinarith only [hySq.2, hac.1, hCa.1, hXy.2, hXsq.1,
      hAc.1, hAC.2]
  have hfstep :
      alignedReserve A X R C D (1571 / 5000) a y r c d (4416 / 25000) <
        alignedReserve A X R C D (1571 / 5000) a y r c d f := by
    have heq : alignedReserve A X R C D (1571 / 5000) a y r c d f -
          alignedReserve A X R C D (1571 / 5000) a y r c d
            (4416 / 25000) =
        (f - 4416 / 25000) *
          (3 * y ^ 2 - 3 * a * c - C * a + 2 * X * y - X ^ 2 -
            A * c + A * C) := by
      unfold alignedReserve
      ring
    have hp := mul_pos_of_neg_of_neg (sub_neg.mpr hf.2) hsf
    linarith only [heq, hp]
  have hsA : 0 < d ^ 2 - c * (4416 / 25000) +
      (1571 / 5000) * c - 2 * D * d - 3 * D ^ 2 +
      C * (4416 / 25000) + 3 * C * (1571 / 5000) := by
    nlinarith only [hdSq.1, hc.1, hDd.2, hDSq.2, hC.1]
  have hAstep :
      alignedReserve (137423 / 100000) X R C D (1571 / 5000)
          a y r c d (4416 / 25000) <
        alignedReserve A X R C D (1571 / 5000)
          a y r c d (4416 / 25000) := by
    have heq :
        alignedReserve A X R C D (1571 / 5000) a y r c d (4416 / 25000) -
            alignedReserve (137423 / 100000) X R C D (1571 / 5000)
              a y r c d (4416 / 25000) =
          (A - 137423 / 100000) *
            (d ^ 2 - c * (4416 / 25000) + (1571 / 5000) * c -
              2 * D * d - 3 * D ^ 2 + C * (4416 / 25000) +
              3 * C * (1571 / 5000)) := by
      unfold alignedReserve
      ring
    have hp := mul_pos (sub_pos.mpr hA.1) hsA
    linarith only [heq, hp]
  have hsX :
      2 * r * d + 2 * y * (4416 / 25000) - 2 * (1571 / 5000) * y -
          2 * D * r - 2 * R * d - 6 * R * D -
          (X + 3977 / 100000) * (4416 / 25000) -
          3 * (X + 3977 / 100000) * (1571 / 5000) < 0 := by
    nlinarith only [hrd.2, hy.1, hy.2, hDr.1, hRd.1, hRD.1, hX.1]
  have hXstep :
      alignedReserve (137423 / 100000) (3977 / 100000) R C D
          (1571 / 5000) a y r c d (4416 / 25000) <
        alignedReserve (137423 / 100000) X R C D
          (1571 / 5000) a y r c d (4416 / 25000) := by
    have heq :
        alignedReserve (137423 / 100000) X R C D
              (1571 / 5000) a y r c d (4416 / 25000) -
            alignedReserve (137423 / 100000) (3977 / 100000) R C D
              (1571 / 5000) a y r c d (4416 / 25000) =
          (X - 3977 / 100000) *
            (2 * r * d + 2 * y * (4416 / 25000) -
              2 * (1571 / 5000) * y - 2 * D * r - 2 * R * d -
              6 * R * D - (X + 3977 / 100000) * (4416 / 25000) -
              3 * (X + 3977 / 100000) * (1571 / 5000)) := by
      unfold alignedReserve
      ring
    have hp := mul_pos_of_neg_of_neg (sub_neg.mpr hX.2) hsX
    linarith only [heq, hp]
  have hsR :
      2 * r * c + 2 * y * d - 2 * D * y - 2 * C * r -
          (R + 242898 / 1000000) * c -
          3 * (R + 242898 / 1000000) * C -
          2 * (3977 / 100000) * d - 6 * (3977 / 100000) * D < 0 := by
    nlinarith only [hrc.2, hyd.2, hDy.1, hCr.1, hR.1,
      hc.1, hC.1, hd.1, hD.1]
  have hRstep :
      alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) C D (1571 / 5000)
          a y r c d (4416 / 25000) <
        alignedReserve (137423 / 100000) (3977 / 100000)
          R C D (1571 / 5000) a y r c d (4416 / 25000) := by
    have heq :
        alignedReserve (137423 / 100000) (3977 / 100000) R C D
              (1571 / 5000) a y r c d (4416 / 25000) -
            alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) C D (1571 / 5000)
              a y r c d (4416 / 25000) =
          (R - 242898 / 1000000) *
            (2 * r * c + 2 * y * d - 2 * D * y - 2 * C * r -
              (R + 242898 / 1000000) * c -
              3 * (R + 242898 / 1000000) * C -
              2 * (3977 / 100000) * d - 6 * (3977 / 100000) * D) := by
      unfold alignedReserve
      ring
    have hp := mul_pos_of_neg_of_neg (sub_neg.mpr hR.2) hsR
    linarith only [heq, hp]
  have hsC : 0 < r ^ 2 - a * (4416 / 25000) +
      (1571 / 5000) * a - 2 * (242898 / 1000000) * r -
      3 * (242898 / 1000000) ^ 2 +
      (137423 / 100000) * (4416 / 25000) +
      3 * (137423 / 100000) * (1571 / 5000) := by
    nlinarith only [hrSq.1, ha.1, ha.2, hr.2]
  have hCstep :
      alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) D (1571 / 5000)
          a y r c d (4416 / 25000) <
        alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) C D (1571 / 5000)
          a y r c d (4416 / 25000) := by
    have heq :
        alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) C D (1571 / 5000)
              a y r c d (4416 / 25000) -
            alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) D (1571 / 5000)
              a y r c d (4416 / 25000) =
          (C - 1323 / 100000) *
            (r ^ 2 - a * (4416 / 25000) + (1571 / 5000) * a -
              2 * (242898 / 1000000) * r -
              3 * (242898 / 1000000) ^ 2 +
              (137423 / 100000) * (4416 / 25000) +
              3 * (137423 / 100000) * (1571 / 5000)) := by
      unfold alignedReserve
      ring
    have hp := mul_pos (sub_pos.mpr hC.1) hsC
    linarith only [heq, hp]
  have hsD :
      2 * y * r + 2 * a * d - (D + 42898 / 1000000) * a -
          2 * (242898 / 1000000) * y - 2 * (3977 / 100000) * r -
          6 * (3977 / 100000) * (242898 / 1000000) -
          2 * (137423 / 100000) * d -
          3 * (137423 / 100000) * (D + 42898 / 1000000) < 0 := by
    nlinarith only [hyr.2, had.2, hDa.1, ha.1, hy.1, hr.1, hd.1, hD.1]
  have hDstep :
      alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) a y r c d (4416 / 25000) <
        alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) D (1571 / 5000)
          a y r c d (4416 / 25000) := by
    have heq :
        alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) D (1571 / 5000)
              a y r c d (4416 / 25000) -
            alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) a y r c d (4416 / 25000) =
          (D - 42898 / 1000000) *
            (2 * y * r + 2 * a * d - (D + 42898 / 1000000) * a -
              2 * (242898 / 1000000) * y - 2 * (3977 / 100000) * r -
              6 * (3977 / 100000) * (242898 / 1000000) -
              2 * (137423 / 100000) * d -
              3 * (137423 / 100000) * (D + 42898 / 1000000)) := by
      unfold alignedReserve
      ring
    have hp := mul_pos_of_neg_of_neg (sub_neg.mpr hD.2) hsD
    linarith only [heq, hp]
  have hsy : 0 <
      6 * r * d + 3 * (y + 37851 / 1000000) * (4416 / 25000) +
        (1571 / 5000) * (y + 37851 / 1000000) +
        2 * (42898 / 1000000) * r + 2 * (242898 / 1000000) * d -
        2 * (242898 / 1000000) * (42898 / 1000000) +
        2 * (3977 / 100000) * (4416 / 25000) -
        2 * (3977 / 100000) * (1571 / 5000) := by
    nlinarith only [hrd.1, hy.1, hr.1, hd.1]
  have hystep :
      alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) a (37851 / 1000000) r c d (4416 / 25000) <
        alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) a y r c d (4416 / 25000) := by
    have heq :
        alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) a y r c d (4416 / 25000) -
            alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) a (37851 / 1000000) r c d (4416 / 25000) =
          (y - 37851 / 1000000) *
            (6 * r * d +
              3 * (y + 37851 / 1000000) * (4416 / 25000) +
              (1571 / 5000) * (y + 37851 / 1000000) +
              2 * (42898 / 1000000) * r +
              2 * (242898 / 1000000) * d -
              2 * (242898 / 1000000) * (42898 / 1000000) +
              2 * (3977 / 100000) * (4416 / 25000) -
              2 * (3977 / 100000) * (1571 / 5000)) := by
      unfold alignedReserve
      ring
    have hp := mul_pos (sub_pos.mpr hy.1) hsy
    linarith only [heq, hp]
  have hsr : 0 <
      3 * (r + 49817 / 1000000) * c +
        6 * (37851 / 1000000) * d +
        2 * (42898 / 1000000) * (37851 / 1000000) +
        (1323 / 100000) * (r + 49817 / 1000000) +
        2 * (242898 / 1000000) * c -
        2 * (242898 / 1000000) * (1323 / 100000) +
        2 * (3977 / 100000) * d -
        2 * (3977 / 100000) * (42898 / 1000000) := by
    nlinarith only [hrc.1, hc.1, hr.1, hd.1]
  have hrstep :
      alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
          c d (4416 / 25000) <
        alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) a (37851 / 1000000) r c d (4416 / 25000) := by
    have heq :
        alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) a (37851 / 1000000) r c d (4416 / 25000) -
            alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
              c d (4416 / 25000) =
          (r - 49817 / 1000000) *
            (3 * (r + 49817 / 1000000) * c +
              6 * (37851 / 1000000) * d +
              2 * (42898 / 1000000) * (37851 / 1000000) +
              (1323 / 100000) * (r + 49817 / 1000000) +
              2 * (242898 / 1000000) * c -
              2 * (242898 / 1000000) * (1323 / 100000) +
              2 * (3977 / 100000) * d -
              2 * (3977 / 100000) * (42898 / 1000000)) := by
      unfold alignedReserve
      ring
    have hp := mul_pos (sub_pos.mpr hr.1) hsr
    linarith only [heq, hp]
  have hsc :
      3 * (49817 / 1000000) ^ 2 -
          3 * a * (4416 / 25000) - (1571 / 5000) * a +
          2 * (242898 / 1000000) * (49817 / 1000000) -
          (242898 / 1000000) ^ 2 -
          (137423 / 100000) * (4416 / 25000) +
          (137423 / 100000) * (1571 / 5000) < 0 := by
    nlinarith only [ha.1]
  have hcstep :
      alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
          (7165 / 1000000) d (4416 / 25000) <
        alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
          c d (4416 / 25000) := by
    have heq :
        alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
              c d (4416 / 25000) -
            alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
              (7165 / 1000000) d (4416 / 25000) =
          (c - 7165 / 1000000) *
            (3 * (49817 / 1000000) ^ 2 -
              3 * a * (4416 / 25000) - (1571 / 5000) * a +
              2 * (242898 / 1000000) * (49817 / 1000000) -
              (242898 / 1000000) ^ 2 -
              (137423 / 100000) * (4416 / 25000) +
              (137423 / 100000) * (1571 / 5000)) := by
      unfold alignedReserve
      ring
    have hp := mul_pos_of_neg_of_neg (sub_neg.mpr hc.2) hsc
    linarith only [heq, hp]
  have hsd : 0 <
      6 * (37851 / 1000000) * (49817 / 1000000) +
        3 * a * (d + 23317 / 1000000) +
        2 * (42898 / 1000000) * a +
        2 * (242898 / 1000000) * (37851 / 1000000) +
        2 * (3977 / 100000) * (49817 / 1000000) -
        2 * (3977 / 100000) * (242898 / 1000000) +
        (137423 / 100000) * (d + 23317 / 1000000) -
        2 * (137423 / 100000) * (42898 / 1000000) := by
    nlinarith only [had.1, ha.1, hd.1]
  have hdstep :
      alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
          (7165 / 1000000) (23317 / 1000000) (4416 / 25000) <
        alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
          (7165 / 1000000) d (4416 / 25000) := by
    have heq :
        alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
              (7165 / 1000000) d (4416 / 25000) -
            alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
              (7165 / 1000000) (23317 / 1000000) (4416 / 25000) =
          (d - 23317 / 1000000) *
            (6 * (37851 / 1000000) * (49817 / 1000000) +
              3 * a * (d + 23317 / 1000000) +
              2 * (42898 / 1000000) * a +
              2 * (242898 / 1000000) * (37851 / 1000000) +
              2 * (3977 / 100000) * (49817 / 1000000) -
              2 * (3977 / 100000) * (242898 / 1000000) +
              (137423 / 100000) * (d + 23317 / 1000000) -
              2 * (137423 / 100000) * (42898 / 1000000)) := by
      unfold alignedReserve
      ring
    have hp := mul_pos (sub_pos.mpr hd.1) hsd
    linarith only [heq, hp]
  have hsa :
      3 * (23317 / 1000000 : ℝ) ^ 2 -
          3 * (7165 / 1000000) * (4416 / 25000) -
          (1571 / 5000) * (7165 / 1000000) +
          2 * (42898 / 1000000) * (23317 / 1000000) -
          (42898 / 1000000) ^ 2 -
          (1323 / 100000) * (4416 / 25000) +
          (1323 / 100000) * (1571 / 5000) < 0 := by
    norm_num
  have hastep :
      alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) (826465 / 1000000) (37851 / 1000000)
          (49817 / 1000000) (7165 / 1000000) (23317 / 1000000)
          (4416 / 25000) <
        alignedReserve (137423 / 100000) (3977 / 100000)
          (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
          (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
          (7165 / 1000000) (23317 / 1000000) (4416 / 25000) := by
    have heq :
        alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) a (37851 / 1000000) (49817 / 1000000)
              (7165 / 1000000) (23317 / 1000000) (4416 / 25000) -
            alignedReserve (137423 / 100000) (3977 / 100000)
              (242898 / 1000000) (1323 / 100000) (42898 / 1000000)
              (1571 / 5000) (826465 / 1000000) (37851 / 1000000)
              (49817 / 1000000) (7165 / 1000000) (23317 / 1000000)
              (4416 / 25000) =
          (a - 826465 / 1000000) *
            (3 * (23317 / 1000000) ^ 2 -
              3 * (7165 / 1000000) * (4416 / 25000) -
              (1571 / 5000) * (7165 / 1000000) +
              2 * (42898 / 1000000) * (23317 / 1000000) -
              (42898 / 1000000) ^ 2 -
              (1323 / 100000) * (4416 / 25000) +
              (1323 / 100000) * (1571 / 5000)) := by
      unfold alignedReserve
      ring
    have hp := mul_pos_of_neg_of_neg (sub_neg.mpr ha.2) hsa
    linarith only [heq, hp]
  have hcorner : (16 / 5000 : ℝ) <
      alignedReserve
        (137423 / 100000) (3977 / 100000) (242898 / 1000000)
        (1323 / 100000) (42898 / 1000000) (1571 / 5000)
        (826465 / 1000000) (37851 / 1000000) (49817 / 1000000)
        (7165 / 1000000) (23317 / 1000000) (4416 / 25000) := by
    norm_num [alignedReserve]
  linarith only [hcorner, hastep, hdstep, hcstep, hrstep, hystep,
    hDstep, hCstep, hRstep, hXstep, hAstep, hfstep, hFstep]

/-- A sharp direct structural reserve for the reverse mixed determinant. -/
theorem pivotCoeff_two_gt_four_div_five_thousand :
    (4 / 5000 : ℝ) < pivotCoeff 2 := by
  rcases clean_aligned_bounds with
    ⟨hAL, hAU, hXL, hXU, hRL, hRU, hCL, hCU, hDL, hDU, hF⟩
  rcases perturb_aligned_bounds with
    ⟨haL, haU, hyL, hyU, hrL, hrU, hcL, hcU, hdL, hdU, hfL, hfU⟩
  have hreserve := alignedReserve_box_gt
    ⟨hAL, hAU⟩ ⟨hXL, hXU⟩ ⟨hRL, hRU⟩ ⟨hCL, hCU⟩ ⟨hDL, hDU⟩ hF
    ⟨haL, haU⟩ ⟨hyL, hyU⟩ ⟨hrL, hrU⟩ ⟨hcL, hcU⟩ ⟨hdL, hdU⟩
    ⟨hfL, hfU⟩
  rw [← four_mul_pivotCoeff_two_eq_reserve] at hreserve
  nlinarith only [hreserve]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
