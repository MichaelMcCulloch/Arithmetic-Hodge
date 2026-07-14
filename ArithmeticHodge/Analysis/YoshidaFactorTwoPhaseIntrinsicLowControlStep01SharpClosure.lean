import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01CauchyStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01SharpClosure

noncomputable section

open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01CauchyStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Positive
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseLowSchur

/-!
# Sharp structural closure of intrinsic control Step01

The singular reflected branch has already been completed into the global
five-square integral.  This file closes the remaining determinant slope and
the coupled signed smooth remainder without phase subdivision, sampling,
mode enumeration, or a computational certificate.
-/

/-- The positive even endpoint and the negative perturbation are the two
matrices naturally occurring in the Step01 determinant derivative. -/
def step01EvenPositive00 : ℝ :=
  factorTwoStructuralPhaseLow00 1

def step01EvenPositive02 : ℝ :=
  factorTwoStructuralPhaseLow02 1

def step01EvenPositive22 : ℝ :=
  factorTwoStructuralPhaseLow22 1

/-- Exact mixed-determinant presentation of the division-free slope gap. -/
theorem factorTwoIntrinsicStep01_slopeGap_eq_mixedDet :
    factorTwoIntrinsicEvenDetCoefficient1 -
        2 * factorTwoIntrinsicEvenDetCoefficient0 =
      2 *
        (step01EvenPositive00 * evenNegativePerturbation22 +
          step01EvenPositive22 * evenNegativePerturbation00 -
          2 * step01EvenPositive02 * evenNegativePerturbation02 -
          (step01EvenPositive00 * step01EvenPositive22 -
            step01EvenPositive02 ^ 2)) := by
  unfold factorTwoIntrinsicEvenDetCoefficient0
    factorTwoIntrinsicEvenDetCoefficient1
    factorTwoIntrinsicEvenDirection00 factorTwoIntrinsicEvenDirection02
    factorTwoIntrinsicEvenDirection22
    step01EvenPositive00 step01EvenPositive02 step01EvenPositive22
    evenNegativePerturbation00 evenNegativePerturbation02
    evenNegativePerturbation22 factorTwoIntrinsicEvenPhaseDet
  ring

theorem factorTwoIntrinsicEvenDetCoefficient0_pos :
    0 < factorTwoIntrinsicEvenDetCoefficient0 := by
  unfold factorTwoIntrinsicEvenDetCoefficient0
  exact factorTwoIntrinsicEven_plus_endpoint_structural_gates.2

private theorem evenStructuralRegularError02_ge_neg_nine_div_five_thousand :
    (-9 / 5000 : ℝ) ≤
      evenStructuralRegularError evenStructuralCorrelation02 := by
  have hp := abs_evenStructuralRegularError_profile_le 1 2
  have hm := abs_evenStructuralRegularError_profile_le 1 (-2)
  rw [evenStructuralRegularError_profile_expansion] at hp hm
  rw [abs_le] at hp hm
  norm_num at hp hm ⊢
  nlinarith

private theorem evenNegativePerturbation02_lt_207_div_1000 :
    evenNegativePerturbation02 < (207 / 1000 : ℝ) := by
  have hb := evenStructuralKernelBase02_bounds.1
  have hr :=
    evenStructuralRegularError02_ge_neg_nine_div_five_thousand
  have heq := factorTwoCenteredSymmetricPerturbation_even_structural_eq.2.1
  have heq' :
      factorTwoCenteredSymmetricPerturbationBilinear
          centeredEvenP0 centeredEvenP2 =
        evenStructuralRegularError evenStructuralCorrelation02 +
          evenStructuralKernelBase02 := by
    rw [heq]
    unfold evenStructuralKernelBase02
    ring
  unfold evenNegativePerturbation02
  rw [heq']
  linarith

private theorem evenNegativePerturbation22_lt_19_div_100 :
    evenNegativePerturbation22 < (19 / 100 : ℝ) := by
  have herr := abs_evenStructuralRegularError_profile_le 0 1
  rw [evenStructuralRegularError_profile_expansion, abs_le] at herr
  have hb := evenStructuralKernelBase22_lower
  have heq := factorTwoCenteredSymmetricPerturbation_even_structural_eq.2.2
  have heq' :
      factorTwoCenteredSymmetricPerturbation centeredEvenP2 =
        evenStructuralRegularError evenStructuralCorrelation22 +
          evenStructuralKernelBase22 := by
    rw [heq]
    unfold evenStructuralKernelBase22
    ring
  unfold evenNegativePerturbation22
  rw [heq']
  norm_num at herr hb ⊢
  linarith

private theorem step01_evenNegativePerturbation00_lower :
    (453 / 2000 : ℝ) ≤ evenNegativePerturbation00 := by
  have h := evenNegativePerturbationSharp_quadratic_le 1 0
  rw [← evenNegativePerturbation_profile_eq] at h
  norm_num [evenNegativePerturbationSharp00,
    evenNegativePerturbationSharp02, evenNegativePerturbationSharp22] at h ⊢
  exact h

private theorem step01_evenNegativePerturbation22_lower :
    (47 / 250 : ℝ) ≤ evenNegativePerturbation22 := by
  have h := evenNegativePerturbationSharp_quadratic_le 0 1
  rw [← evenNegativePerturbation_profile_eq] at h
  norm_num [evenNegativePerturbationSharp00,
    evenNegativePerturbationSharp02, evenNegativePerturbationSharp22] at h ⊢
  exact h

/-- The determinant slope has a strict rational reserve.  All six matrix
entries remain in the mixed-determinant expression; only its monotonicity
on the proved structural intervals is used. -/
theorem factorTwoIntrinsicStep01_slopeGap_pos :
    0 < factorTwoIntrinsicEvenDetCoefficient1 -
      2 * factorTwoIntrinsicEvenDetCoefficient0 := by
  let a : ℝ := yoshidaEndpointEvenLowGram00
  let b : ℝ := yoshidaEndpointEvenLowGram02
  let d : ℝ := yoshidaEndpointEvenLowGram22
  let u : ℝ := evenNegativePerturbation00
  let v : ℝ := evenNegativePerturbation02
  let w : ℝ := evenNegativePerturbation22
  let margin : ℝ :=
    -(a * d - b ^ 2) + 2 * (a * w + d * u - 2 * b * v) -
      3 * (u * w - v ^ 2)
  have haL : (3665 / 10000 : ℝ) < a := by
    simpa only [a] using intrinsicEven_cleanGram00_gt
  have haU : a < (37 / 100 : ℝ) := by
    simpa only [a] using intrinsicEven_cleanGram00_lt_thirtyseven_hundredths
  have hbL : (3402 / 10000 : ℝ) < b := by
    simpa only [b] using intrinsicEven_cleanGram02_bounds.1
  have hbU : b < (3403 / 10000 : ℝ) := by
    simpa only [b] using intrinsicEven_cleanGram02_bounds.2
  have hdL : (3269 / 10000 : ℝ) < d := by
    simpa only [d] using intrinsicEven_cleanGram22_gt
  have huL : (453 / 2000 : ℝ) ≤ u := by
    simpa only [u] using step01_evenNegativePerturbation00_lower
  have hvU : v < (207 / 1000 : ℝ) := by
    simpa only [v] using evenNegativePerturbation02_lt_207_div_1000
  have hwL : (47 / 250 : ℝ) ≤ w := by
    simpa only [w] using step01_evenNegativePerturbation22_lower
  have hwU : w < (19 / 100 : ℝ) := by
    simpa only [w] using evenNegativePerturbation22_lt_19_div_100
  have hV :
      (-(a * d - b ^ 2) + 2 * (a * w + d * u - 2 * b * (207 / 1000)) -
          3 * (u * w - (207 / 1000 : ℝ) ^ 2)) < margin := by
    have hfactor : 0 <
        ((207 / 1000 : ℝ) - v) *
          (4 * b - 3 * (v + 207 / 1000)) := by
      apply mul_pos (sub_pos.mpr hvU)
      nlinarith
    dsimp only [margin]
    nlinarith
  have hB :
      (-(a * d - (3403 / 10000 : ℝ) ^ 2) +
          2 * (a * w + d * u - 2 * (3403 / 10000) * (207 / 1000)) -
          3 * (u * w - (207 / 1000 : ℝ) ^ 2)) <
        (-(a * d - b ^ 2) + 2 * (a * w + d * u - 2 * b * (207 / 1000)) -
          3 * (u * w - (207 / 1000 : ℝ) ^ 2)) := by
    have hfactor : 0 <
        ((3403 / 10000 : ℝ) - b) *
          (4 * (207 / 1000 : ℝ) - (b + 3403 / 10000)) := by
      apply mul_pos (sub_pos.mpr hbU)
      nlinarith
    nlinarith
  have hU :
      (-(a * d - (3403 / 10000 : ℝ) ^ 2) +
          2 * (a * w + d * (453 / 2000) -
            2 * (3403 / 10000) * (207 / 1000)) -
          3 * ((453 / 2000 : ℝ) * w - (207 / 1000) ^ 2)) ≤
        (-(a * d - (3403 / 10000 : ℝ) ^ 2) +
          2 * (a * w + d * u - 2 * (3403 / 10000) * (207 / 1000)) -
          3 * (u * w - (207 / 1000 : ℝ) ^ 2)) := by
    have hcoefficient : 0 < 2 * d - 3 * w := by
      nlinarith
    nlinarith
  have hW :
      (-(a * d - (3403 / 10000 : ℝ) ^ 2) +
          2 * (a * (47 / 250) + d * (453 / 2000) -
            2 * (3403 / 10000) * (207 / 1000)) -
          3 * ((453 / 2000 : ℝ) * (47 / 250) -
            (207 / 1000) ^ 2)) ≤
        (-(a * d - (3403 / 10000 : ℝ) ^ 2) +
          2 * (a * w + d * (453 / 2000) -
            2 * (3403 / 10000) * (207 / 1000)) -
          3 * ((453 / 2000 : ℝ) * w - (207 / 1000) ^ 2)) := by
    have hcoefficient : 0 < 2 * a - 3 * (453 / 2000 : ℝ) := by
      nlinarith
    nlinarith
  have hD :
      (-((a * (3269 / 10000)) - (3403 / 10000 : ℝ) ^ 2) +
          2 * (a * (47 / 250) + (3269 / 10000) * (453 / 2000) -
            2 * (3403 / 10000) * (207 / 1000)) -
          3 * ((453 / 2000 : ℝ) * (47 / 250) -
            (207 / 1000) ^ 2)) <
        (-(a * d - (3403 / 10000 : ℝ) ^ 2) +
          2 * (a * (47 / 250) + d * (453 / 2000) -
            2 * (3403 / 10000) * (207 / 1000)) -
          3 * ((453 / 2000 : ℝ) * (47 / 250) -
            (207 / 1000) ^ 2)) := by
    have hcoefficient : 0 < 2 * (453 / 2000 : ℝ) - a := by
      nlinarith
    nlinarith
  have hA :
      (-(((3665 / 10000 : ℝ) * (3269 / 10000)) -
            (3403 / 10000) ^ 2) +
          2 * ((3665 / 10000 : ℝ) * (47 / 250) +
            (3269 / 10000) * (453 / 2000) -
            2 * (3403 / 10000) * (207 / 1000)) -
          3 * ((453 / 2000 : ℝ) * (47 / 250) -
            (207 / 1000) ^ 2)) <
        (-((a * (3269 / 10000)) - (3403 / 10000 : ℝ) ^ 2) +
          2 * (a * (47 / 250) + (3269 / 10000) * (453 / 2000) -
            2 * (3403 / 10000) * (207 / 1000)) -
          3 * ((453 / 2000 : ℝ) * (47 / 250) -
            (207 / 1000) ^ 2)) := by
    have hcoefficient : 0 < 2 * (47 / 250 : ℝ) - 3269 / 10000 := by
      norm_num
    nlinarith
  have hrat : 0 <
      -(((3665 / 10000 : ℝ) * (3269 / 10000)) -
          (3403 / 10000) ^ 2) +
        2 * ((3665 / 10000 : ℝ) * (47 / 250) +
          (3269 / 10000) * (453 / 2000) -
          2 * (3403 / 10000) * (207 / 1000)) -
        3 * ((453 / 2000 : ℝ) * (47 / 250) -
          (207 / 1000) ^ 2) := by
    norm_num
  have hmargin : 0 < margin := by
    nlinarith [hV, hB, hU, hW, hD, hA, hrat]
  have hE00 : step01EvenPositive00 = a - u := by
    dsimp only [step01EvenPositive00, a, u]
    unfold factorTwoStructuralPhaseLow00 evenNegativePerturbation00
    ring
  have hE02 : step01EvenPositive02 = b - v := by
    dsimp only [step01EvenPositive02, b, v]
    unfold factorTwoStructuralPhaseLow02 evenNegativePerturbation02
    ring
  have hE22 : step01EvenPositive22 = d - w := by
    dsimp only [step01EvenPositive22, d, w]
    unfold factorTwoStructuralPhaseLow22 evenNegativePerturbation22
    ring
  rw [factorTwoIntrinsicStep01_slopeGap_eq_mixedDet]
  rw [hE00, hE02, hE22]
  dsimp only [margin, a, b, d, u, v, w] at hmargin
  nlinarith

theorem factorTwoIntrinsicStep01Slope_two_le :
    2 ≤ factorTwoIntrinsicStep01Slope := by
  rw [factorTwoIntrinsicStep01Slope_two_le_iff
    factorTwoIntrinsicEvenDetCoefficient0_pos]
  linarith [factorTwoIntrinsicStep01_slopeGap_pos]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01SharpClosure
