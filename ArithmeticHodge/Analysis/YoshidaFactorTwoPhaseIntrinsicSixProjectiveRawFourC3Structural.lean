import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC3Structural

noncomputable section

open MeasureTheory Real Set
open Polynomial
open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotMixedStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural positivity of the third raw four-mode coefficient

The coefficient adjacent to the negative endpoint is treated through its
exact mixed-endpoint scalar formula.  The three-dimensional mixed determinant
is positive by the endpoint Sylvester gates.  Consequently the only remaining
analytic input is the displayed fixed `P4/P1` boundary Schur inequality.  No
sampling of the projective half-line is used.
-/

/-- The linear coefficient of the negative odd endpoint is its strictly
positive endpoint diagonal. -/
theorem coefficientOdd11Polynomial_coeff_one_pos :
    0 < coefficientOdd11Polynomial.coeff 1 := by
  have h := oddStructuralLow_endpoint_gates.2.2.1
  rw [show coefficientOdd11Polynomial.coeff 1 =
      factorTwoIntrinsicOddPhaseLow11 (-1) by
    simp [coefficientOdd11Polynomial, endpointAffinePolynomial]]
  simpa [factorTwoIntrinsicOddPhaseLow11,
    YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11] using h

/-- The exact fixed boundary determinant left after removing the positive
mixed-determinant summand from `c3`. -/
def factorTwoIntrinsicSixProjectiveRawFourC3Boundary : ℝ :=
  pivotCoeff 3 * coefficientOdd11Polynomial.coeff 0 -
    p1AlternatingAdjugateCoeff 2

/-- Structural reduction of `c3`: the endpoint boundary Schur inequality is
the only additional input beyond the already-proved positive mixed
determinant. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_three_nonneg_of_boundary
    (hBoundary : 0 ≤ factorTwoIntrinsicSixProjectiveRawFourC3Boundary) :
    0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 3 := by
  have hMixed : 0 ≤
      pivotCoeff 2 * coefficientOdd11Polynomial.coeff 1 :=
    mul_nonneg pivotCoeff_two_pos.le
      coefficientOdd11Polynomial_coeff_one_pos.le
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  unfold factorTwoIntrinsicSixProjectiveRawFourC3Boundary at hBoundary
  linarith

/-! ## Exact negative-endpoint scalar block -/

private def e00m : ℝ := factorTwoStructuralPhaseLow00 (-1)
private def e02m : ℝ := factorTwoStructuralPhaseLow02 (-1)
private def e22m : ℝ := factorTwoStructuralPhaseLow22 (-1)
private def e04m : ℝ := factorTwoIntrinsicFourP45Cross04 (-1)
private def e24m : ℝ := factorTwoIntrinsicFourP45Cross24 (-1)
private def e44m : ℝ := factorTwoIntrinsicSixP4Diagonal (-1)

private def a01 : ℝ := factorTwoIntrinsicAlternating01
private def a21 : ℝ := factorTwoIntrinsicAlternating21
private def a41 : ℝ := factorTwoIntrinsicFourP45Cross41

private def evenDetMinus : ℝ :=
  symmetricDeterminant e00m e02m e04m e22m e24m e44m

private def alternatingAdjugateMinus : ℝ :=
  adjugateQuadratic e00m e02m e04m e22m e24m e44m a01 a21 a41

private theorem pivot_polynomial_expansion :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial =
      C (symmetricDeterminant
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)) +
      C (mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))) * X +
      C (mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)) * X ^ 2 +
      C evenDetMinus * X ^ 3 := by
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial evenDetMinus e00m e02m e22m e04m e24m e44m
    mixedDeterminantOne symmetricDeterminant
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

private theorem pivotCoeff_three_eq_evenDetMinus :
    pivotCoeff 3 = evenDetMinus := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 3 = _
  rw [pivot_polynomial_expansion]
  simp

private def alternatingAdjugatePlus : ℝ :=
  adjugateQuadratic
    (factorTwoStructuralPhaseLow00 1)
    (factorTwoStructuralPhaseLow02 1)
    (factorTwoIntrinsicFourP45Cross04 1)
    (factorTwoStructuralPhaseLow22 1)
    (factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicSixP4Diagonal 1) a01 a21 a41

private def alternatingAdjugateMixed : ℝ :=
  let e00p := factorTwoStructuralPhaseLow00 1
  let e02p := factorTwoStructuralPhaseLow02 1
  let e22p := factorTwoStructuralPhaseLow22 1
  let e04p := factorTwoIntrinsicFourP45Cross04 1
  let e24p := factorTwoIntrinsicFourP45Cross24 1
  let e44p := factorTwoIntrinsicSixP4Diagonal 1
  (e22m * e44p + e22p * e44m - 2 * e24p * e24m) * a01 ^ 2 +
    2 * (e04m * e24p + e04p * e24m - e02m * e44p - e02p * e44m) *
      a01 * a21 +
    2 * (e02m * e24p + e02p * e24m - e04m * e22p - e04p * e22m) *
      a01 * a41 +
    (e00m * e44p + e00p * e44m - 2 * e04p * e04m) * a21 ^ 2 +
    2 * (e02m * e04p + e02p * e04m - e00m * e24p - e00p * e24m) *
      a21 * a41 +
    (e00m * e22p + e00p * e22m - 2 * e02p * e02m) * a41 ^ 2

private theorem alternating_adjugate_polynomial_expansion :
    coefficientP1AlternatingAdjugatePolynomial =
      C alternatingAdjugatePlus + C alternatingAdjugateMixed * X +
        C alternatingAdjugateMinus * X ^ 2 := by
  unfold coefficientP1AlternatingAdjugatePolynomial
    coefficientLowDetPolynomial coefficientLow00Polynomial
    coefficientLow02Polynomial coefficientLow22Polynomial
    coefficientCross04Polynomial coefficientCross24Polynomial
    coefficientP4DiagonalPolynomial endpointAffinePolynomial
    alternatingAdjugatePlus alternatingAdjugateMixed
    alternatingAdjugateMinus e00m e02m e22m e04m e24m e44m
    a01 a21 a41 adjugateQuadratic
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

private theorem p1AlternatingAdjugateCoeff_two_eq :
    p1AlternatingAdjugateCoeff 2 = alternatingAdjugateMinus := by
  change coefficientP1AlternatingAdjugatePolynomial.coeff 2 = _
  rw [alternating_adjugate_polynomial_expansion]
  simp

/-! ## Structural endpoint boxes -/

private theorem abs_step01AnalyticError00_le :
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

private theorem abs_step01AnalyticError22_le :
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

private theorem integral_abs_evenStructuralCorrelation02 :
    (∫ t : ℝ in 0..2, |evenStructuralCorrelation02 t|) = (1 / 4 : ℝ) := by
  have hcont : Continuous evenStructuralCorrelation02 := by
    unfold evenStructuralCorrelation02
    fun_prop
  have hleft : ∀ t ∈ Icc (0 : ℝ) 1,
      evenStructuralCorrelation02 t ≤ 0 := by
    intro t ht
    unfold evenStructuralCorrelation02
    have h0 : 0 ≤ t := ht.1
    have h1 : t - 1 ≤ 0 := sub_nonpos.mpr ht.2
    have h2 : t - 2 ≤ 0 := by linarith
    have hp0 : t * (t - 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 h2
    have hp : 0 ≤ t * (t - 2) * (t - 1) :=
      mul_nonneg_of_nonpos_of_nonpos hp0 h1
    nlinarith
  have hright : ∀ t ∈ Icc (1 : ℝ) 2,
      0 ≤ evenStructuralCorrelation02 t := by
    intro t ht
    unfold evenStructuralCorrelation02
    have h0 : 0 ≤ t := by linarith [ht.1]
    have h1 : 0 ≤ t - 1 := sub_nonneg.mpr ht.1
    have h2 : t - 2 ≤ 0 := sub_nonpos.mpr ht.2
    have hp0 : t * (t - 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 h2
    have hp : t * (t - 2) * (t - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hp0 h1
    nlinarith
  have hI01 : IntervalIntegrable (fun t : ℝ ↦ |evenStructuralCorrelation02 t|)
      volume 0 1 := hcont.abs.intervalIntegrable 0 1
  have hI12 : IntervalIntegrable (fun t : ℝ ↦ |evenStructuralCorrelation02 t|)
      volume 1 2 := hcont.abs.intervalIntegrable 1 2
  rw [(intervalIntegral.integral_add_adjacent_intervals hI01 hI12).symm]
  have hleftEq :
      (∫ t : ℝ in 0..1, |evenStructuralCorrelation02 t|) =
        ∫ t : ℝ in 0..1, -evenStructuralCorrelation02 t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    change |evenStructuralCorrelation02 t| = -evenStructuralCorrelation02 t
    rw [abs_of_nonpos (hleft t ht)]
  have hrightEq :
      (∫ t : ℝ in 1..2, |evenStructuralCorrelation02 t|) =
        ∫ t : ℝ in 1..2, evenStructuralCorrelation02 t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
    change |evenStructuralCorrelation02 t| = evenStructuralCorrelation02 t
    rw [abs_of_nonneg (hright t ht)]
  rw [hleftEq, hrightEq]
  unfold evenStructuralCorrelation02
  ring_nf
  repeat' first
    | rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
  repeat' rw [intervalIntegral.integral_neg]
  repeat' rw [integral_id]
  norm_num

private theorem abs_step01AnalyticError02_le :
    |step01AnalyticError02| ≤ (3 / 32000 : ℝ) := by
  have h := abs_poleFreeAnalyticError_le evenStructuralCorrelation02
    (by unfold evenStructuralCorrelation02; fun_prop)
  rw [integral_abs_evenStructuralCorrelation02] at h
  norm_num [step01AnalyticError02] at h ⊢
  exact h

private theorem e00m_bounds :
    (11859 / 20000 : ℝ) ≤ e00m ∧ e00m < (5949 / 10000 : ℝ) := by
  have hlower := intrinsicStaticMinusEvenLower_le 1 0
  have hclean := intrinsicEven_cleanGram00_lt_step01
  have hmid := step01Midpoint00_lt
  have herr := abs_le.mp abs_step01AnalyticError00_le
  have hpert := step01_negativePerturbation_eq_midpoint_sub_error.1
  have heq : e00m = yoshidaEndpointEvenLowGram00 + evenNegativePerturbation00 := by
    unfold e00m factorTwoStructuralPhaseLow00 evenNegativePerturbation00
    ring
  constructor
  · unfold intrinsicStaticMinusEvenLower factorTwoIntrinsicStaticEvenQuadratic at hlower
    norm_num [intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22] at hlower
    simpa only [e00m] using hlower
  · rw [heq, hpert]
    norm_num at hclean hmid herr ⊢
    linarith

private theorem e02m_bounds :
    (2179649 / 4000000 : ℝ) < e02m ∧
      e02m < (2180951 / 4000000 : ℝ) := by
  have hclean := intrinsicEven_cleanGram02_bounds
  have hmidL := step01Midpoint02_gt
  have hmidU := step01Midpoint02_lt
  have herr' := abs_le.mp abs_step01AnalyticError02_le
  have hpert := step01_negativePerturbation_eq_midpoint_sub_error.2.1
  have heq : e02m = yoshidaEndpointEvenLowGram02 + evenNegativePerturbation02 := by
    unfold e02m factorTwoStructuralPhaseLow02 evenNegativePerturbation02
    ring
  rw [heq, hpert]
  norm_num at hclean hmidL hmidU herr' ⊢
  constructor <;> linarith

private theorem e22m_bounds :
    (10297 / 20000 : ℝ) ≤ e22m ∧
      e22m < (515777 / 1000000 : ℝ) := by
  have hlower := intrinsicStaticMinusEvenLower_le 0 1
  have hclean := intrinsicEven_cleanGram22_lt_step01
  have hmid := step01Midpoint22_lt
  have herr := abs_le.mp abs_step01AnalyticError22_le
  have hpert := step01_negativePerturbation_eq_midpoint_sub_error.2.2
  have heq : e22m = yoshidaEndpointEvenLowGram22 + evenNegativePerturbation22 := by
    unfold e22m factorTwoStructuralPhaseLow22 evenNegativePerturbation22
    ring
  constructor
  · unfold intrinsicStaticMinusEvenLower factorTwoIntrinsicStaticEvenQuadratic at hlower
    norm_num [intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22] at hlower
    simpa only [e22m] using hlower
  · rw [heq, hpert]
    norm_num at hclean hmid herr ⊢
    linarith

private theorem e44m_lower : (12 / 25 : ℝ) < e44m := by
  change (12 / 25 : ℝ) < factorTwoIntrinsicP4PhaseDiagonal (-1)
  simpa [factorTwoIntrinsicP4MinusDiagonalLower] using
    factorTwoIntrinsicP4MinusDiagonalLower_lt_phaseDiagonal

private def sMinus : ℝ := e04m + e24m
private def tMinus : ℝ := e24m - e04m
private def xAlternating : ℝ := a01 + a21
private def yAlternating : ℝ := a01 - a21

private theorem sMinus_bounds :
    (204844 / 700000 : ℝ) < sMinus ∧ sMinus < (3 / 10 : ℝ) := by
  let clean : ℝ :=
    yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
      yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4
  have hclean := factorTwoIntrinsicP4CleanCross_sum_sub_seventeen_seventieths_abs_lt
  rw [abs_lt] at hclean
  have hplus := factorTwoIntrinsicP4PlusCrossSum_bounds
  have hminus := factorTwoIntrinsicP4MinusCross_sum_difference_bounds
  have hid : sMinus + factorTwoIntrinsicP4PlusCrossSum = 2 * clean := by
    dsimp only [sMinus, e04m, e24m, clean]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    ring
  constructor
  · dsimp only [clean] at hclean hid
    nlinarith [hclean.1, hplus.2]
  · simpa only [sMinus] using hminus.2.1

private theorem tMinus_bounds :
    (46294 / 700000 : ℝ) < tMinus ∧ tMinus < (7 / 100 : ℝ) := by
  let clean : ℝ :=
    yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
      yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4
  have hclean :=
    factorTwoIntrinsicP4CleanCross_difference_sub_three_seventieths_abs_lt
  rw [abs_lt] at hclean
  have hplus := factorTwoIntrinsicP4PlusCrossDifference_bounds
  have hminus := factorTwoIntrinsicP4MinusCross_sum_difference_bounds
  have hid : tMinus + factorTwoIntrinsicP4PlusCrossDifference = 2 * clean := by
    dsimp only [tMinus, e04m, e24m, clean]
    unfold factorTwoIntrinsicP4PlusCrossDifference
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    ring
  constructor
  · dsimp only [clean] at hclean hid
    nlinarith [hclean.1, hplus.2]
  · simpa only [tMinus] using hminus.2.2.2

private theorem alternating_sum_difference_bounds :
    (56168 / 100000 : ℝ) < xAlternating ∧
      xAlternating < (56173 / 100000 : ℝ) ∧
      (1687 / 100000 : ℝ) < yAlternating ∧
      yAlternating < (1692 / 100000 : ℝ) := by
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨hxL, hxU, hyL, hyU, _⟩
  simpa only [xAlternating, yAlternating, a01, a21] using
    ⟨hxL, hxU, hyL, hyU⟩

/-! ## Correlated endpoint Schur coordinate -/

/-- The endpoint Schur excess in the sum/difference coordinates.  Keeping
`S,T` and `X,Y` paired is what preserves the cancellations in the endpoint
adjugate. -/
private def endpointSchurExcess
    (A B C S T X Y Z F : ℝ) : ℝ :=
  adjugateQuadratic A B ((S - T) / 2) C ((S + T) / 2) F
      ((X + Y) / 2) ((X - Y) / 2) Z -
    (19 / 100 : ℝ) *
      symmetricDeterminant A B ((S - T) / 2) C ((S + T) / 2) F

private theorem endpoint_schur_excess_eq :
    alternatingAdjugateMinus - (19 / 100 : ℝ) * evenDetMinus =
      endpointSchurExcess e00m e02m e22m sMinus tMinus
        xAlternating yAlternating a41 e44m := by
  unfold endpointSchurExcess alternatingAdjugateMinus evenDetMinus
    sMinus tMinus xAlternating yAlternating
  ring

private def aCenter : ℝ := 23757 / 40000
private def bCenter : ℝ := 21803 / 40000
private def cCenter : ℝ := 1030627 / 2000000
private def sCenter : ℝ := 103711 / 350000
private def tCenter : ℝ := 47647 / 700000
private def xCenter : ℝ := 112341 / 200000
private def yCenter : ℝ := 3379 / 200000
private def zCenter : ℝ := 57 / 400

private theorem positive_sq_bounds
    {u l r : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hur : u ≤ r) :
    l ^ 2 ≤ u ^ 2 ∧ u ^ 2 ≤ r ^ 2 := by
  have hu : 0 ≤ u := hl.trans hlu
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlu) (add_nonneg hu hl)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hur) (add_nonneg (hu.trans hur) hu)]

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

private theorem positive_mul3_bounds
    {u v w lu ru lv rv lw rw : ℝ}
    (hlu0 : 0 ≤ lu) (hlv0 : 0 ≤ lv) (hlw0 : 0 ≤ lw)
    (hlu : lu ≤ u) (hru : u ≤ ru)
    (hlv : lv ≤ v) (hrv : v ≤ rv)
    (hlw : lw ≤ w) (hrw : w ≤ rw) :
    lu * lv * lw ≤ u * v * w ∧ u * v * w ≤ ru * rv * rw := by
  have huv := positive_mul_bounds hlu0 hlv0 hlu hru hlv hrv
  have huv0 : 0 ≤ u * v :=
    mul_nonneg (hlu0.trans hlu) (hlv0.trans hlv)
  constructor
  · calc
      lu * lv * lw ≤ (u * v) * lw :=
        mul_le_mul_of_nonneg_right huv.1 hlw0
      _ ≤ u * v * w := mul_le_mul_of_nonneg_left hlw huv0
  · calc
      u * v * w ≤ (ru * rv) * w :=
        mul_le_mul_of_nonneg_right huv.2 (hlw0.trans hlw)
      _ ≤ ru * rv * rw :=
        mul_le_mul_of_nonneg_left hrw
          (mul_nonneg (hlu0.trans hlu |>.trans hru)
            (hlv0.trans hlv |>.trans hrv))

private theorem mul_le_budget_of_abs_le
    {u v r m : ℝ} (hr : 0 ≤ r)
    (hu : |u| ≤ r) (hv : |v| ≤ m) : u * v ≤ r * m := by
  calc
    u * v ≤ |u * v| := le_abs_self _
    _ = |u| * |v| := abs_mul u v
    _ ≤ r * m := mul_le_mul hu hv (abs_nonneg v) hr

private theorem endpoint_center_radii :
    |e00m - aCenter| ≤ (39 / 40000 : ℝ) ∧
      |e02m - bCenter| ≤ (651 / 4000000 : ℝ) ∧
      |e22m - cCenter| ≤ (927 / 2000000 : ℝ) ∧
      |sMinus - sCenter| ≤ (1289 / 350000 : ℝ) ∧
      |tMinus - tCenter| ≤ (1353 / 700000 : ℝ) ∧
      |xAlternating - xCenter| ≤ (1 / 40000 : ℝ) ∧
      |yAlternating - yCenter| ≤ (1 / 40000 : ℝ) ∧
      |a41 - zCenter| ≤ (3 / 2000 : ℝ) := by
  rcases e00m_bounds with ⟨hAL, hAU⟩
  rcases e02m_bounds with ⟨hBL, hBU⟩
  rcases e22m_bounds with ⟨hCL, hCU⟩
  rcases sMinus_bounds with ⟨hSL, hSU⟩
  rcases tMinus_bounds with ⟨hTL, hTU⟩
  rcases alternating_sum_difference_bounds with
    ⟨hXL, hXU, hYL, hYU⟩
  have hZ : (141 / 1000 : ℝ) < a41 ∧ a41 < (144 / 1000 : ℝ) := by
    simpa only [a41] using factorTwoIntrinsicFourP45Cross41_bounds
  rcases hZ with ⟨hZL, hZU⟩
  repeat' apply And.intro
  all_goals rw [abs_le]
  all_goals simp only [aCenter, bCenter, cCenter, sCenter, tCenter,
    xCenter, yCenter, zCenter]
  all_goals constructor <;> norm_num at * <;> linarith

private theorem endpoint_center_negative :
    endpointSchurExcess aCenter bCenter cCenter sCenter tCenter
      xCenter yCenter zCenter (12 / 25) < 0 := by
  norm_num [endpointSchurExcess, adjugateQuadratic,
    symmetricDeterminant, aCenter, bCenter, cCenter, sCenter, tCenter,
    xCenter, yCenter, zCenter]

/-- Slope of the Schur excess in the final diagonal.  Its sum/difference
form makes the decisive negative `2 × 2` determinant reserve explicit. -/
private def endpointSchurFSlope (A B C X Y : ℝ) : ℝ :=
  ((A + C - 2 * B) * X ^ 2 +
      (A + C + 2 * B) * Y ^ 2 +
      2 * (C - A) * X * Y -
      (76 / 100 : ℝ) * (A * C - B ^ 2)) / 4

private theorem endpoint_schur_F_difference
    (A B C S T X Y Z F F₀ : ℝ) :
    endpointSchurExcess A B C S T X Y Z F -
        endpointSchurExcess A B C S T X Y Z F₀ =
      (F - F₀) * endpointSchurFSlope A B C X Y := by
  unfold endpointSchurExcess endpointSchurFSlope
    adjugateQuadratic symmetricDeterminant
  ring

private theorem endpointSchurFSlope_neg :
    endpointSchurFSlope e00m e02m e22m
      xAlternating yAlternating < 0 := by
  rcases e00m_bounds with ⟨hAL, hAU⟩
  rcases e02m_bounds with ⟨hBL, hBU⟩
  rcases e22m_bounds with ⟨hCL, hCU⟩
  rcases alternating_sum_difference_bounds with
    ⟨hXL, hXU, hYL, hYU⟩
  have hA0 : 0 ≤ e00m := by linarith
  have hB0 : 0 ≤ e02m := by linarith
  have hC0 : 0 ≤ e22m := by linarith
  have hX0 : 0 ≤ xAlternating := by linarith
  have hY0 : 0 ≤ yAlternating := by linarith
  have hXsq : xAlternating ^ 2 ≤ (56173 / 100000 : ℝ) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hXU.le)
      (show 0 ≤ (56173 / 100000 : ℝ) + xAlternating by linarith)
    nlinarith
  have hYsq : yAlternating ^ 2 ≤ (1692 / 100000 : ℝ) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hYU.le)
      (show 0 ≤ (1692 / 100000 : ℝ) + yAlternating by linarith)
    nlinarith
  have hXY : (56168 / 100000 : ℝ) * (1687 / 100000 : ℝ) ≤
      xAlternating * yAlternating := by
    calc
      (56168 / 100000 : ℝ) * (1687 / 100000 : ℝ) ≤
          xAlternating * (1687 / 100000 : ℝ) :=
        mul_le_mul_of_nonneg_right hXL.le (by norm_num)
      _ ≤ xAlternating * yAlternating :=
        mul_le_mul_of_nonneg_left hYL.le hX0
  have hAC : (11859 / 20000 : ℝ) * (10297 / 20000 : ℝ) ≤
      e00m * e22m := by
    calc
      (11859 / 20000 : ℝ) * (10297 / 20000 : ℝ) ≤
          e00m * (10297 / 20000 : ℝ) :=
        mul_le_mul_of_nonneg_right hAL (by norm_num)
      _ ≤ e00m * e22m := mul_le_mul_of_nonneg_left hCL hA0
  have hBsq : e02m ^ 2 ≤ (2180951 / 4000000 : ℝ) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hBU.le)
      (show 0 ≤ (2180951 / 4000000 : ℝ) + e02m by linarith)
    nlinarith
  have hDelta :
      (11859 / 20000 : ℝ) * (10297 / 20000 : ℝ) -
          (2180951 / 4000000 : ℝ) ^ 2 ≤
        e00m * e22m - e02m ^ 2 := by
    linarith
  have hk₁L : 0 ≤ e00m + e22m - 2 * e02m := by
    nlinarith
  have hk₁U : e00m + e22m - 2 * e02m ≤
      (5949 / 10000 : ℝ) + (515777 / 1000000 : ℝ) -
        2 * (2179649 / 4000000 : ℝ) := by
    linarith
  have hk₂L : 0 ≤ e00m + e22m + 2 * e02m := by
    positivity
  have hk₂U : e00m + e22m + 2 * e02m ≤
      (5949 / 10000 : ℝ) + (515777 / 1000000 : ℝ) +
        2 * (2180951 / 4000000 : ℝ) := by
    linarith
  have hterm₁ :
      (e00m + e22m - 2 * e02m) * xAlternating ^ 2 ≤
        ((5949 / 10000 : ℝ) + (515777 / 1000000 : ℝ) -
          2 * (2179649 / 4000000 : ℝ)) *
            (56173 / 100000 : ℝ) ^ 2 :=
    mul_le_mul hk₁U hXsq (sq_nonneg xAlternating) (by norm_num)
  have hterm₂ :
      (e00m + e22m + 2 * e02m) * yAlternating ^ 2 ≤
        ((5949 / 10000 : ℝ) + (515777 / 1000000 : ℝ) +
          2 * (2180951 / 4000000 : ℝ)) *
            (1692 / 100000 : ℝ) ^ 2 :=
    mul_le_mul hk₂U hYsq (sq_nonneg yAlternating) (by norm_num)
  have hCA : e22m - e00m ≤
      (515777 / 1000000 : ℝ) - (11859 / 20000 : ℝ) := by
    linarith
  have hCAU : (515777 / 1000000 : ℝ) -
      (11859 / 20000 : ℝ) ≤ 0 := by norm_num
  have hcross₀ : (e22m - e00m) *
      (xAlternating * yAlternating) ≤
        ((515777 / 1000000 : ℝ) - (11859 / 20000 : ℝ)) *
          (xAlternating * yAlternating) :=
    mul_le_mul_of_nonneg_right hCA (mul_nonneg hX0 hY0)
  have hcross₁ :
      ((515777 / 1000000 : ℝ) - (11859 / 20000 : ℝ)) *
          (xAlternating * yAlternating) ≤
        ((515777 / 1000000 : ℝ) - (11859 / 20000 : ℝ)) *
          ((56168 / 100000 : ℝ) * (1687 / 100000 : ℝ)) :=
    mul_le_mul_of_nonpos_left hXY hCAU
  have hcross : 2 * (e22m - e00m) * xAlternating * yAlternating ≤
      2 * ((515777 / 1000000 : ℝ) - (11859 / 20000 : ℝ)) *
        (56168 / 100000 : ℝ) * (1687 / 100000 : ℝ) := by
    nlinarith
  have hnumeric :
      (((5949 / 10000 : ℝ) + (515777 / 1000000 : ℝ) -
          2 * (2179649 / 4000000 : ℝ)) *
            (56173 / 100000 : ℝ) ^ 2) +
        (((5949 / 10000 : ℝ) + (515777 / 1000000 : ℝ) +
          2 * (2180951 / 4000000 : ℝ)) *
            (1692 / 100000 : ℝ) ^ 2) +
        2 * ((515777 / 1000000 : ℝ) - (11859 / 20000 : ℝ)) *
          (56168 / 100000 : ℝ) * (1687 / 100000 : ℝ) -
        (76 / 100 : ℝ) *
          ((11859 / 20000 : ℝ) * (10297 / 20000 : ℝ) -
            (2180951 / 4000000 : ℝ) ^ 2) < 0 := by
    norm_num
  unfold endpointSchurFSlope
  nlinarith

private theorem endpoint_schur_excess_le_diagonal_floor :
    endpointSchurExcess e00m e02m e22m sMinus tMinus
        xAlternating yAlternating a41 e44m ≤
      endpointSchurExcess e00m e02m e22m sMinus tMinus
        xAlternating yAlternating a41 (12 / 25) := by
  have hF := e44m_lower
  have hslope := endpointSchurFSlope_neg
  rw [← sub_nonpos]
  rw [endpoint_schur_F_difference]
  exact (mul_nonpos_of_nonneg_of_nonpos (by linarith) hslope.le)

/-! ### Midpoint telescoping slopes -/

private def aSlope (C S T X Y Z : ℝ) : ℝ :=
  -(57 / 625 : ℝ) * C + (3 / 25 : ℝ) * X ^ 2 +
    (3 / 25 : ℝ) * Y ^ 2 + (19 / 400 : ℝ) * S ^ 2 +
    (19 / 400 : ℝ) * T ^ 2 + C * Z ^ 2 -
    (6 / 25 : ℝ) * X * Y + (19 / 200 : ℝ) * S * T +
    S * Y * Z / 2 + T * Y * Z / 2 - S * X * Z / 2 - T * X * Z / 2

private def bSlope (B S T X Y Z : ℝ) : ℝ :=
  (1242771 / 25000000 : ℝ) - (21803 / 40000 : ℝ) * Z ^ 2 -
    (19 / 200 : ℝ) * S ^ 2 - (6 / 25 : ℝ) * X ^ 2 +
    (6 / 25 : ℝ) * Y ^ 2 + (19 / 200 : ℝ) * T ^ 2 +
    (57 / 625 : ℝ) * B - B * Z ^ 2 + S * X * Z + T * Y * Z

private def cSlope (S T X Y Z : ℝ) : ℝ :=
  -(1354149 / 25000000 : ℝ) + (3 / 25 : ℝ) * X ^ 2 +
    (3 / 25 : ℝ) * Y ^ 2 + (19 / 400 : ℝ) * S ^ 2 +
    (19 / 400 : ℝ) * T ^ 2 + (23757 / 40000 : ℝ) * Z ^ 2 -
    (19 / 200 : ℝ) * S * T + (6 / 25 : ℝ) * X * Y +
    T * X * Z / 2 + T * Y * Z / 2 - S * X * Z / 2 - S * Y * Z / 2

private def sSlope (S T X Y Z : ℝ) : ℝ :=
  (75228122093 / 280000000000000 : ℝ) -
    (103711 / 1400000 : ℝ) * Y ^ 2 +
    (725363 / 800000000 : ℝ) * S +
    (2987237 / 400000000 : ℝ) * T -
    (38177 / 4000000 : ℝ) * X * Z - S * Y ^ 2 / 4 +
    (157223 / 4000000 : ℝ) * Y * Z - T * X * Y / 2

private def tSlope (T X Y Z : ℝ) : ℝ :=
  (5221419372689 / 560000000000000 : ℝ) -
    (47647 / 2800000 : ℝ) * X ^ 2 +
    (83576763 / 800000000 : ℝ) * T -
    (157223 / 4000000 : ℝ) * X * Z -
    (103711 / 700000 : ℝ) * X * Y - T * X ^ 2 / 4 +
    (4398777 / 4000000 : ℝ) * Y * Z

private def xSlope (X Y Z : ℝ) : ℝ :=
  (249327210291531 / 392000000000000000 : ℝ) -
    (14186230417 / 490000000000 : ℝ) * Y -
    (616398159 / 112000000000 : ℝ) * Z +
    (2219378591 / 1960000000000 : ℝ) * X

private def ySlope (Y Z : ℝ) : ℝ :=
  -(74565862190341 / 6125000000000000 : ℝ) +
    (9688001473 / 112000000000 : ℝ) * Z +
    (118568072279 / 490000000000 : ℝ) * Y

private def zSlope (Z : ℝ) : ℝ :=
  -(1985006890463 / 5600000000000000 : ℝ) +
    (716065189 / 80000000000 : ℝ) * Z

private theorem a_step_identity (A B C S T X Y Z : ℝ) :
    endpointSchurExcess A B C S T X Y Z (12 / 25) -
        endpointSchurExcess aCenter B C S T X Y Z (12 / 25) =
      (A - aCenter) * aSlope C S T X Y Z := by
  unfold endpointSchurExcess aSlope aCenter adjugateQuadratic
    symmetricDeterminant
  ring

private theorem b_step_identity (B C S T X Y Z : ℝ) :
    endpointSchurExcess aCenter B C S T X Y Z (12 / 25) -
        endpointSchurExcess aCenter bCenter C S T X Y Z (12 / 25) =
      (B - bCenter) * bSlope B S T X Y Z := by
  unfold endpointSchurExcess bSlope aCenter bCenter adjugateQuadratic
    symmetricDeterminant
  ring

private theorem c_step_identity (C S T X Y Z : ℝ) :
    endpointSchurExcess aCenter bCenter C S T X Y Z (12 / 25) -
        endpointSchurExcess aCenter bCenter cCenter S T X Y Z (12 / 25) =
      (C - cCenter) * cSlope S T X Y Z := by
  unfold endpointSchurExcess cSlope aCenter bCenter cCenter
    adjugateQuadratic symmetricDeterminant
  ring

private theorem s_step_identity (S T X Y Z : ℝ) :
    endpointSchurExcess aCenter bCenter cCenter S T X Y Z (12 / 25) -
        endpointSchurExcess aCenter bCenter cCenter sCenter T X Y Z (12 / 25) =
      (S - sCenter) * sSlope S T X Y Z := by
  unfold endpointSchurExcess sSlope aCenter bCenter cCenter sCenter
    adjugateQuadratic symmetricDeterminant
  ring

private theorem t_step_identity (T X Y Z : ℝ) :
    endpointSchurExcess aCenter bCenter cCenter sCenter T X Y Z (12 / 25) -
        endpointSchurExcess aCenter bCenter cCenter sCenter tCenter X Y Z
          (12 / 25) =
      (T - tCenter) * tSlope T X Y Z := by
  unfold endpointSchurExcess tSlope aCenter bCenter cCenter sCenter tCenter
    adjugateQuadratic symmetricDeterminant
  ring

private theorem x_step_identity (X Y Z : ℝ) :
    endpointSchurExcess aCenter bCenter cCenter sCenter tCenter X Y Z
        (12 / 25) -
      endpointSchurExcess aCenter bCenter cCenter sCenter tCenter xCenter Y Z
        (12 / 25) =
      (X - xCenter) * xSlope X Y Z := by
  unfold endpointSchurExcess xSlope aCenter bCenter cCenter sCenter tCenter
    xCenter adjugateQuadratic symmetricDeterminant
  ring

private theorem y_step_identity (Y Z : ℝ) :
    endpointSchurExcess aCenter bCenter cCenter sCenter tCenter xCenter Y Z
        (12 / 25) -
      endpointSchurExcess aCenter bCenter cCenter sCenter tCenter xCenter
        yCenter Z (12 / 25) =
      (Y - yCenter) * ySlope Y Z := by
  unfold endpointSchurExcess ySlope aCenter bCenter cCenter sCenter tCenter
    xCenter yCenter adjugateQuadratic symmetricDeterminant
  ring

private theorem z_step_identity (Z : ℝ) :
    endpointSchurExcess aCenter bCenter cCenter sCenter tCenter xCenter
        yCenter Z (12 / 25) -
      endpointSchurExcess aCenter bCenter cCenter sCenter tCenter xCenter
        yCenter zCenter (12 / 25) =
      (Z - zCenter) * zSlope Z := by
  unfold endpointSchurExcess zSlope aCenter bCenter cCenter sCenter tCenter
    xCenter yCenter zCenter adjugateQuadratic symmetricDeterminant
  ring

set_option maxHeartbeats 1200000 in
private theorem telescope_slope_bounds :
    |aSlope e22m sMinus tMinus xAlternating yAlternating a41| ≤
        (97 / 10000 : ℝ) ∧
      |bSlope e02m sMinus tMinus xAlternating yAlternating a41| ≤
        (19 / 1000 : ℝ) ∧
      |cSlope sMinus tMinus xAlternating yAlternating a41| ≤
        (98 / 10000 : ℝ) ∧
      |sSlope sMinus tMinus xAlternating yAlternating a41| ≤
        (5 / 100000 : ℝ) ∧
      |tSlope tMinus xAlternating yAlternating a41| ≤
        (43 / 10000 : ℝ) ∧
      |xSlope xAlternating yAlternating a41| ≤
        (11 / 1000000 : ℝ) ∧
      |ySlope yAlternating a41| ≤ (44 / 10000 : ℝ) ∧
      |zSlope a41| ≤ (1 / 1000 : ℝ) := by
  rcases e02m_bounds with ⟨hBL, hBU⟩
  rcases e22m_bounds with ⟨hCL, hCU⟩
  rcases sMinus_bounds with ⟨hSL, hSU⟩
  rcases tMinus_bounds with ⟨hTL, hTU⟩
  rcases alternating_sum_difference_bounds with
    ⟨hXL, hXU, hYL, hYU⟩
  have hZ : (141 / 1000 : ℝ) < a41 ∧ a41 < (144 / 1000 : ℝ) := by
    simpa only [a41] using factorTwoIntrinsicFourP45Cross41_bounds
  rcases hZ with ⟨hZL, hZU⟩
  have hS2 := positive_sq_bounds (by norm_num) hSL.le hSU.le
  have hT2 := positive_sq_bounds (by norm_num) hTL.le hTU.le
  have hX2 := positive_sq_bounds (by norm_num) hXL.le hXU.le
  have hY2 := positive_sq_bounds (by norm_num) hYL.le hYU.le
  have hZ2 := positive_sq_bounds (by norm_num) hZL.le hZU.le
  have hST := positive_mul_bounds (by norm_num) (by norm_num)
    hSL.le hSU.le hTL.le hTU.le
  have hXY := positive_mul_bounds (by norm_num) (by norm_num)
    hXL.le hXU.le hYL.le hYU.le
  have hXZ := positive_mul_bounds (by norm_num) (by norm_num)
    hXL.le hXU.le hZL.le hZU.le
  have hYZ := positive_mul_bounds (by norm_num) (by norm_num)
    hYL.le hYU.le hZL.le hZU.le
  have hSXZ := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hSL.le hSU.le hXL.le hXU.le hZL.le hZU.le
  have hSYZ := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hSL.le hSU.le hYL.le hYU.le hZL.le hZU.le
  have hTXZ := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hTL.le hTU.le hXL.le hXU.le hZL.le hZU.le
  have hTYZ := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hTL.le hTU.le hYL.le hYU.le hZL.le hZU.le
  have hTXY := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hTL.le hTU.le hXL.le hXU.le hYL.le hYU.le
  have hSY2 := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hSL.le hSU.le hYL.le hYU.le hYL.le hYU.le
  have hTX2 := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hTL.le hTU.le hXL.le hXU.le hXL.le hXU.le
  have hBZ2 := positive_mul3_bounds (by norm_num) (by norm_num) (by norm_num)
    hBL.le hBU.le hZL.le hZU.le hZL.le hZU.le
  constructor
  · rw [abs_le]
    constructor <;> unfold aSlope <;>
      nlinarith [hS2.1, hS2.2, hT2.1, hT2.2, hX2.1, hX2.2,
        hY2.1, hY2.2, hZ2.1, hZ2.2, hST.1, hST.2, hXY.1,
        hXY.2, hSXZ.1, hSXZ.2, hSYZ.1, hSYZ.2, hTXZ.1, hTXZ.2,
        hTYZ.1, hTYZ.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold bSlope <;>
      nlinarith [hS2.1, hS2.2, hT2.1, hT2.2, hX2.1, hX2.2,
        hY2.1, hY2.2, hZ2.1, hZ2.2, hBZ2.1, hBZ2.2,
        hSXZ.1, hSXZ.2, hTYZ.1, hTYZ.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold cSlope <;>
      nlinarith [hS2.1, hS2.2, hT2.1, hT2.2, hX2.1, hX2.2,
        hY2.1, hY2.2, hZ2.1, hZ2.2, hST.1, hST.2, hXY.1,
        hXY.2, hSXZ.1, hSXZ.2, hSYZ.1, hSYZ.2, hTXZ.1, hTXZ.2,
        hTYZ.1, hTYZ.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold sSlope <;>
      nlinarith [hY2.1, hY2.2, hXZ.1, hXZ.2, hYZ.1, hYZ.2,
        hSY2.1, hSY2.2, hTXY.1, hTXY.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold tSlope <;>
      nlinarith [hX2.1, hX2.2, hXZ.1, hXZ.2, hXY.1, hXY.2,
        hYZ.1, hYZ.2, hTX2.1, hTX2.2]
  constructor
  · rw [abs_le]
    constructor <;> unfold xSlope <;> nlinarith
  constructor
  · rw [abs_le]
    constructor <;> unfold ySlope <;> nlinarith
  · rw [abs_le]
    constructor <;> unfold zSlope <;> nlinarith

private theorem endpoint_schur_excess_at_floor_lt :
    endpointSchurExcess e00m e02m e22m sMinus tMinus
        xAlternating yAlternating a41 (12 / 25) <
      (157 / 5000000 : ℝ) := by
  rcases endpoint_center_radii with
    ⟨hRA, hRB, hRC, hRS, hRT, hRX, hRY, hRZ⟩
  rcases telescope_slope_bounds with
    ⟨hSA, hSB, hSC, hSS, hST, hSX, hSY, hSZ⟩
  have hAstep :
      endpointSchurExcess e00m e02m e22m sMinus tMinus
          xAlternating yAlternating a41 (12 / 25) -
        endpointSchurExcess aCenter e02m e22m sMinus tMinus
          xAlternating yAlternating a41 (12 / 25) ≤
        (39 / 40000 : ℝ) * (97 / 10000 : ℝ) := by
    rw [a_step_identity]
    exact mul_le_budget_of_abs_le (by norm_num) hRA hSA
  have hBstep :
      endpointSchurExcess aCenter e02m e22m sMinus tMinus
          xAlternating yAlternating a41 (12 / 25) -
        endpointSchurExcess aCenter bCenter e22m sMinus tMinus
          xAlternating yAlternating a41 (12 / 25) ≤
        (651 / 4000000 : ℝ) * (19 / 1000 : ℝ) := by
    rw [b_step_identity]
    exact mul_le_budget_of_abs_le (by norm_num) hRB hSB
  have hCstep :
      endpointSchurExcess aCenter bCenter e22m sMinus tMinus
          xAlternating yAlternating a41 (12 / 25) -
        endpointSchurExcess aCenter bCenter cCenter sMinus tMinus
          xAlternating yAlternating a41 (12 / 25) ≤
        (927 / 2000000 : ℝ) * (98 / 10000 : ℝ) := by
    rw [c_step_identity]
    exact mul_le_budget_of_abs_le (by norm_num) hRC hSC
  have hSstep :
      endpointSchurExcess aCenter bCenter cCenter sMinus tMinus
          xAlternating yAlternating a41 (12 / 25) -
        endpointSchurExcess aCenter bCenter cCenter sCenter tMinus
          xAlternating yAlternating a41 (12 / 25) ≤
        (1289 / 350000 : ℝ) * (5 / 100000 : ℝ) := by
    rw [s_step_identity]
    exact mul_le_budget_of_abs_le (by norm_num) hRS hSS
  have hTstep :
      endpointSchurExcess aCenter bCenter cCenter sCenter tMinus
          xAlternating yAlternating a41 (12 / 25) -
        endpointSchurExcess aCenter bCenter cCenter sCenter tCenter
          xAlternating yAlternating a41 (12 / 25) ≤
        (1353 / 700000 : ℝ) * (43 / 10000 : ℝ) := by
    rw [t_step_identity]
    exact mul_le_budget_of_abs_le (by norm_num) hRT hST
  have hXstep :
      endpointSchurExcess aCenter bCenter cCenter sCenter tCenter
          xAlternating yAlternating a41 (12 / 25) -
        endpointSchurExcess aCenter bCenter cCenter sCenter tCenter
          xCenter yAlternating a41 (12 / 25) ≤
        (1 / 40000 : ℝ) * (11 / 1000000 : ℝ) := by
    rw [x_step_identity]
    exact mul_le_budget_of_abs_le (by norm_num) hRX hSX
  have hYstep :
      endpointSchurExcess aCenter bCenter cCenter sCenter tCenter
          xCenter yAlternating a41 (12 / 25) -
        endpointSchurExcess aCenter bCenter cCenter sCenter tCenter
          xCenter yCenter a41 (12 / 25) ≤
        (1 / 40000 : ℝ) * (44 / 10000 : ℝ) := by
    rw [y_step_identity]
    exact mul_le_budget_of_abs_le (by norm_num) hRY hSY
  have hZstep :
      endpointSchurExcess aCenter bCenter cCenter sCenter tCenter
          xCenter yCenter a41 (12 / 25) -
        endpointSchurExcess aCenter bCenter cCenter sCenter tCenter
          xCenter yCenter zCenter (12 / 25) ≤
        (3 / 2000 : ℝ) * (1 / 1000 : ℝ) := by
    rw [z_step_identity]
    exact mul_le_budget_of_abs_le (by norm_num) hRZ hSZ
  have hbudget :
      (39 / 40000 : ℝ) * (97 / 10000 : ℝ) +
        (651 / 4000000 : ℝ) * (19 / 1000 : ℝ) +
        (927 / 2000000 : ℝ) * (98 / 10000 : ℝ) +
        (1289 / 350000 : ℝ) * (5 / 100000 : ℝ) +
        (1353 / 700000 : ℝ) * (43 / 10000 : ℝ) +
        (1 / 40000 : ℝ) * (11 / 1000000 : ℝ) +
        (1 / 40000 : ℝ) * (44 / 10000 : ℝ) +
        (3 / 2000 : ℝ) * (1 / 1000 : ℝ) <
          (157 / 5000000 : ℝ) := by
    norm_num
  linarith [endpoint_center_negative]

private theorem endpoint_schur_excess_lt :
    alternatingAdjugateMinus - (19 / 100 : ℝ) * evenDetMinus <
      (157 / 5000000 : ℝ) := by
  rw [endpoint_schur_excess_eq]
  exact lt_of_le_of_lt endpoint_schur_excess_le_diagonal_floor
    endpoint_schur_excess_at_floor_lt

/-! ## Odd reserves and unconditional closure -/

private theorem coefficientOdd11Polynomial_coeff_one_gt :
    (157 / 1000 : ℝ) < coefficientOdd11Polynomial.coeff 1 := by
  rw [show coefficientOdd11Polynomial.coeff 1 =
      factorTwoIntrinsicOddPhaseLow11 (-1) by
    simp [coefficientOdd11Polynomial, endpointAffinePolynomial]]
  have hclean := yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hpert := oddStructuralLow_perturbation_sharp_bounds.1.2
  unfold factorTwoIntrinsicOddPhaseLow11
  norm_num only [neg_mul, one_mul]
  nlinarith

private theorem coefficientOdd11Polynomial_coeff_zero_gt :
    (19 / 100 : ℝ) < coefficientOdd11Polynomial.coeff 0 := by
  rw [show coefficientOdd11Polynomial.coeff 0 =
      factorTwoIntrinsicOddPhaseLow11 1 by
    simp [coefficientOdd11Polynomial, endpointAffinePolynomial]]
  have hclean := yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hpert := oddStructuralLow_perturbation_sharp_bounds.1.1
  unfold factorTwoIntrinsicOddPhaseLow11
  norm_num only [one_mul]
  nlinarith

private theorem evenDetMinus_pos : 0 < evenDetMinus := by
  have h := factorTwoIntrinsicSixP4SchurLeading_minus_pos
  have heq : evenDetMinus = factorTwoIntrinsicSixP4SchurLeading (-1) := by
    have hdiag : factorTwoIntrinsicSixP4Diagonal (-1) =
        factorTwoIntrinsicP4PhaseDiagonal (-1) := by rfl
    unfold evenDetMinus e00m e02m e22m e04m e24m e44m
      factorTwoIntrinsicSixP4SchurLeading factorTwoIntrinsicSixLowDet
      factorTwoIntrinsicSixP4Low0 factorTwoIntrinsicSixP4Low2
      symmetricDeterminant
    rw [hdiag]
    ring
  rw [heq]
  exact h

/-- Unconditional structural positivity of the coefficient adjacent to the
negative endpoint. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_three_nonneg :
    0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 3 := by
  have hpivot := pivotCoeff_two_gt_one_div_five_thousand
  have hoddMinus := coefficientOdd11Polynomial_coeff_one_gt
  have hoddPlus := coefficientOdd11Polynomial_coeff_zero_gt
  have hmixed : (157 / 5000000 : ℝ) <
      pivotCoeff 2 * coefficientOdd11Polynomial.coeff 1 := by
    calc
      (157 / 5000000 : ℝ) =
          (157 / 1000 : ℝ) * (1 / 5000 : ℝ) := by norm_num
      _ < (157 / 1000 : ℝ) * pivotCoeff 2 :=
        mul_lt_mul_of_pos_left hpivot (by norm_num)
      _ < coefficientOdd11Polynomial.coeff 1 * pivotCoeff 2 :=
        mul_lt_mul_of_pos_right hoddMinus
          ((show (0 : ℝ) < 1 / 5000 by norm_num).trans hpivot)
      _ = pivotCoeff 2 * coefficientOdd11Polynomial.coeff 1 := by ring
  have hplus : (19 / 100 : ℝ) * evenDetMinus <
      evenDetMinus * coefficientOdd11Polynomial.coeff 0 := by
    calc
      (19 / 100 : ℝ) * evenDetMinus =
          evenDetMinus * (19 / 100 : ℝ) := by ring
      _ < evenDetMinus * coefficientOdd11Polynomial.coeff 0 :=
        mul_lt_mul_of_pos_left hoddPlus evenDetMinus_pos
  have hexcess := endpoint_schur_excess_lt
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  rw [pivotCoeff_three_eq_evenDetMinus, p1AlternatingAdjugateCoeff_two_eq]
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC3Structural
