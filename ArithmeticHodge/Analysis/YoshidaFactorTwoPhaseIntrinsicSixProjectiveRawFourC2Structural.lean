import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotMixedStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveRankStructural
import ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDeterminant

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural

noncomputable section

open Polynomial
open ThreeByThreeRankOneSchur
open MeasureTheory Real Set
open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotMixedStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotCombinedReserveStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaConstantBounds
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseSymmetricCarleman
open ShiftedLegendreL2Basis
open ShiftedLegendreLogEigen
open ShiftedLegendreLogKernel
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PrimeCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
open CenteredEndpointCorrelation
open YoshidaFactorTwoPhaseLegendreFourFiveRankStructural
open YoshidaDiagonalFineBase
open YoshidaRegularKernelSchur
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenFullPolarization
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass

/-!
# Structural positivity of the middle raw four-mode coefficient

This is the central mixed-endpoint coefficient of the raw
`P₀/P₂/P₄/P₁` determinant.  The proof keeps its exact scalar decomposition
and uses only analytic bounds proved elsewhere in the structural chain.
-/

private def e00p : ℝ := factorTwoStructuralPhaseLow00 1
private def e02p : ℝ := factorTwoStructuralPhaseLow02 1
private def e22p : ℝ := factorTwoStructuralPhaseLow22 1
private def e04p : ℝ := factorTwoIntrinsicFourP45Cross04 1
private def e24p : ℝ := factorTwoIntrinsicFourP45Cross24 1
private def e44p : ℝ := factorTwoIntrinsicSixP4Diagonal 1

private def e00m : ℝ := factorTwoStructuralPhaseLow00 (-1)
private def e02m : ℝ := factorTwoStructuralPhaseLow02 (-1)
private def e22m : ℝ := factorTwoStructuralPhaseLow22 (-1)
private def e04m : ℝ := factorTwoIntrinsicFourP45Cross04 (-1)
private def e24m : ℝ := factorTwoIntrinsicFourP45Cross24 (-1)
private def e44m : ℝ := factorTwoIntrinsicSixP4Diagonal (-1)

private def o11p : ℝ := factorTwoIntrinsicOddPhaseLow11 1
private def o11m : ℝ := factorTwoIntrinsicOddPhaseLow11 (-1)

private def a01 : ℝ := factorTwoIntrinsicAlternating01
private def a21 : ℝ := factorTwoIntrinsicAlternating21
private def a41 : ℝ := factorTwoIntrinsicFourP45Cross41

/-! ## Clean/perturbation polarization of the mixed adjugate -/

private def c00 : ℝ := yoshidaEndpointEvenLowGram00
private def c02 : ℝ := yoshidaEndpointEvenLowGram02
private def c22 : ℝ := yoshidaEndpointEvenLowGram22
private def c04 : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4
private def c24 : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4
private def c44 : ℝ :=
  yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4

private def n00 : ℝ :=
  -factorTwoCenteredSymmetricPerturbation centeredEvenP0
private def n02 : ℝ :=
  -factorTwoCenteredSymmetricPerturbationBilinear centeredEvenP0 centeredEvenP2
private def n22 : ℝ :=
  -factorTwoCenteredSymmetricPerturbation centeredEvenP2
private def n04 : ℝ :=
  -factorTwoCenteredSymmetricPerturbationBilinear
    centeredEvenP0 factorTwoCenteredP4
private def n24 : ℝ :=
  -factorTwoCenteredSymmetricPerturbationBilinear
    centeredEvenP2 factorTwoCenteredP4
private def n44 : ℝ :=
  -factorTwoCenteredSymmetricPerturbation factorTwoCenteredP4

private theorem o11m_gt : (157 / 1000 : ℝ) < o11m := by
  have hclean := yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hpert := oddStructuralLow_perturbation_sharp_bounds.1.2
  unfold o11m factorTwoIntrinsicOddPhaseLow11
  norm_num only [neg_mul, one_mul]
  nlinarith

private theorem o11p_gt : (19 / 100 : ℝ) < o11p := by
  have hclean := yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hpert := oddStructuralLow_perturbation_sharp_bounds.1.1
  unfold o11p factorTwoIntrinsicOddPhaseLow11
  norm_num only [one_mul]
  nlinarith

private def evenDetPlus : ℝ :=
  e00p * e22p * e44p + 2 * e02p * e04p * e24p -
    e00p * e24p ^ 2 - e22p * e04p ^ 2 - e44p * e02p ^ 2

private def evenDetMinus : ℝ :=
  e00m * e22m * e44m + 2 * e02m * e04m * e24m -
    e00m * e24m ^ 2 - e22m * e04m ^ 2 - e44m * e02m ^ 2

/-- Coefficient of `X` in `det (E₊ + X E₋)`. -/
private def evenMixedOne : ℝ :=
  e00m * e22p * e44p + e00p * e22m * e44p + e00p * e22p * e44m +
    2 * (e02m * e04p * e24p + e02p * e04m * e24p +
      e02p * e04p * e24m) -
    (e00m * e24p ^ 2 + 2 * e00p * e24p * e24m) -
    (e22m * e04p ^ 2 + 2 * e22p * e04p * e04m) -
    (e44m * e02p ^ 2 + 2 * e44p * e02p * e02m)

/-- Coefficient of `X²` in `det (E₊ + X E₋)`. -/
private def evenMixedTwo : ℝ :=
  e00p * e22m * e44m + e00m * e22p * e44m + e00m * e22m * e44p +
    2 * (e02p * e04m * e24m + e02m * e04p * e24m +
      e02m * e04m * e24p) -
    (e00p * e24m ^ 2 + 2 * e00m * e24p * e24m) -
    (e22p * e04m ^ 2 + 2 * e22m * e04p * e04m) -
    (e44p * e02m ^ 2 + 2 * e44m * e02p * e02m)

/-- Coefficient of `X` in the alternating adjugate energy. -/
private def alternatingAdjugateMixed : ℝ :=
  (e22m * e44p + e22p * e44m - 2 * e24p * e24m) * a01 ^ 2 +
    2 * (e04m * e24p + e04p * e24m - e02m * e44p - e02p * e44m) *
      a01 * a21 +
    2 * (e02m * e24p + e02p * e24m - e04m * e22p - e04p * e22m) *
      a01 * a41 +
    (e00m * e44p + e00p * e44m - 2 * e04p * e04m) * a21 ^ 2 +
    2 * (e02m * e04p + e02p * e04m - e00m * e24p - e00p * e24m) *
      a21 * a41 +
    (e00m * e22p + e00p * e22m - 2 * e02p * e02m) * a41 ^ 2

set_option maxHeartbeats 800000 in
private theorem alternatingAdjugateMixed_eq_clean_sub_perturbation :
    alternatingAdjugateMixed =
      2 * (adjugateQuadratic c00 c02 c04 c22 c24 c44 a01 a21 a41 -
        adjugateQuadratic n00 n02 n04 n22 n24 n44 a01 a21 a41) := by
  unfold alternatingAdjugateMixed adjugateQuadratic
    e00p e02p e22p e04p e24p e44p e00m e02m e22m e04m e24m e44m
    c00 c02 c22 c04 c24 c44 n00 n02 n22 n04 n24 n44
    factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22 factorTwoIntrinsicFourP45Cross04
    factorTwoIntrinsicFourP45Cross24 factorTwoIntrinsicSixP4Diagonal
    factorTwoEndpointPhaseDiagonal
  ring

/-! The adjugate is estimated in weak/strong sum-difference coordinates.
These coordinates retain the cancellations which disappear in six
independent entrywise estimates. -/

private def xAlt : ℝ := a01 + a21
private def yAlt : ℝ := a01 - a21

private def weakMass (u v w : ℝ) : ℝ := u + w - 2 * v
private def strongMass (u v w : ℝ) : ℝ := u + w + 2 * v
private def skewMass (u w : ℝ) : ℝ := w - u
private def crossSum (r s : ℝ) : ℝ := r + s
private def crossDiff (r s : ℝ) : ℝ := s - r

private def adjugateSumDifference
    (u v r w s d p q z : ℝ) : ℝ :=
  let α := weakMass u v w
  let γ := strongMass u v w
  let β := skewMass u w
  let S := crossSum r s
  let D := crossDiff r s
  ((d * α - D ^ 2) * p ^ 2 +
      (d * γ - S ^ 2) * q ^ 2 +
      2 * (d * β - S * D) * p * q +
      2 * (-α * S + β * D) * p * z +
      2 * (-β * S + γ * D) * q * z +
      4 * (u * w - v ^ 2) * z ^ 2) / 4

private theorem adjugateQuadratic_eq_sumDifference
    (u v r w s d p q z : ℝ) :
    adjugateQuadratic u v r w s d
        ((p + q) / 2) ((p - q) / 2) z =
      adjugateSumDifference u v r w s d p q z := by
  unfold adjugateQuadratic adjugateSumDifference weakMass strongMass
    skewMass crossSum crossDiff
  ring

private theorem alternatingAdjugateMixed_eq_sumDifference :
    alternatingAdjugateMixed =
      2 * (adjugateSumDifference c00 c02 c04 c22 c24 c44 xAlt yAlt a41 -
        adjugateSumDifference n00 n02 n04 n22 n24 n44 xAlt yAlt a41) := by
  rw [alternatingAdjugateMixed_eq_clean_sub_perturbation]
  rw [show a01 = (xAlt + yAlt) / 2 by unfold xAlt yAlt; ring,
    show a21 = (xAlt - yAlt) / 2 by unfold xAlt yAlt; ring,
    adjugateQuadratic_eq_sumDifference,
    adjugateQuadratic_eq_sumDifference]

/-! The numerator of `adjugateSumDifference`.  Keeping the weak `x²` and
`xz` terms paired is essential: their two large contributions have opposite
sign, while their sum is monotone on the structural coordinate box. -/

private def adjugateBracket
    (α γ β S D f x y z : ℝ) : ℝ :=
  (f * α - D ^ 2) * x ^ 2 +
    (f * γ - S ^ 2) * y ^ 2 +
    2 * (f * β - S * D) * x * y +
    2 * (-α * S + β * D) * x * z +
    2 * (-β * S + γ * D) * y * z +
    (α * γ - β ^ 2) * z ^ 2

private def weakXZBlock
    (α β S D f x z : ℝ) : ℝ :=
  (f * α - D ^ 2) * x ^ 2 +
    2 * (-α * S + β * D) * x * z

private theorem weakXZBlock_factorization
    (α β S D f x z : ℝ) :
    weakXZBlock α β S D f x z =
      α * x * (f * x - 2 * S * z) +
        D * x * (2 * β * z - D * x) := by
  unfold weakXZBlock
  ring

private theorem adjugateBracket_eq_weakXZ
    (α γ β S D f x y z : ℝ) :
    adjugateBracket α γ β S D f x y z =
      weakXZBlock α β S D f x z +
        (f * γ - S ^ 2) * y ^ 2 +
        2 * (f * β - S * D) * x * y +
        2 * (-β * S + γ * D) * y * z +
        (α * γ - β ^ 2) * z ^ 2 := by
  unfold adjugateBracket weakXZBlock
  ring

private theorem alternatingAdjugateMixed_eq_brackets :
    alternatingAdjugateMixed =
      (adjugateBracket
          (weakMass c00 c02 c22) (strongMass c00 c02 c22)
          (skewMass c00 c22) (crossSum c04 c24) (crossDiff c04 c24)
          c44 xAlt yAlt a41 -
        adjugateBracket
          (weakMass n00 n02 n22) (strongMass n00 n02 n22)
          (skewMass n00 n22) (crossSum n04 n24) (crossDiff n04 n24)
          n44 xAlt yAlt a41) / 2 := by
  rw [alternatingAdjugateMixed_eq_sumDifference]
  unfold adjugateSumDifference adjugateBracket weakMass strongMass skewMass
    crossSum crossDiff
  ring

/-! ## Structural coordinate boxes -/

private def cAlpha : ℝ := weakMass c00 c02 c22
private def cGamma : ℝ := strongMass c00 c02 c22
private def cBeta : ℝ := skewMass c00 c22
private def cS : ℝ := crossSum c04 c24
private def cD : ℝ := crossDiff c04 c24

private def nAlpha : ℝ := weakMass n00 n02 n22
private def nGamma : ℝ := strongMass n00 n02 n22
private def nBeta : ℝ := skewMass n00 n22
private def nS : ℝ := crossSum n04 n24
private def nD : ℝ := crossDiff n04 n24

private theorem cleanLowCoordinate_bounds :
    (128 / 10000 : ℝ) < cAlpha ∧ cAlpha < (135 / 10000 : ℝ) ∧
      (13738 / 10000 : ℝ) < cGamma ∧ cGamma < (13745 / 10000 : ℝ) ∧
      (-399 / 10000 : ℝ) < cBeta ∧ cBeta < (-394 / 10000 : ℝ) := by
  have h00L := intrinsicEven_cleanGram00_gt
  have h00U := intrinsicEven_cleanGram00_lt_step01
  have h02 := intrinsicEven_cleanGram02_bounds
  have h22L := intrinsicEven_cleanGram22_gt
  have h22U := intrinsicEven_cleanGram22_lt_step01
  unfold cAlpha cGamma cBeta weakMass strongMass skewMass c00 c02 c22
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem cleanCrossCoordinate_bounds :
    (17 / 70 - 1 / 25000 : ℝ) < cS ∧
      cS < (17 / 70 + 1 / 25000 : ℝ) ∧
      (3 / 70 - 1 / 25000 : ℝ) < cD ∧
      cD < (3 / 70 + 1 / 25000 : ℝ) := by
  have hS :=
    factorTwoIntrinsicP4CleanCross_sum_sub_seventeen_seventieths_abs_lt
  have hD :=
    factorTwoIntrinsicP4CleanCross_difference_sub_three_seventieths_abs_lt
  rw [abs_lt] at hS hD
  unfold cS cD crossSum crossDiff c04 c24
  constructor
  · linarith [hS.1]
  constructor
  · linarith [hS.2]
  constructor <;> linarith [hD.1, hD.2]

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

private def weakCorrelation (t : ℝ) : ℝ :=
  evenStructuralCorrelation00 t - 2 * evenStructuralCorrelation02 t +
    evenStructuralCorrelation22 t

private def strongCorrelation (t : ℝ) : ℝ :=
  evenStructuralCorrelation00 t + 2 * evenStructuralCorrelation02 t +
    evenStructuralCorrelation22 t

private theorem weakCorrelation_nonneg
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : 0 ≤ weakCorrelation t := by
  let u : ℝ := t / 2
  have hu0 : 0 ≤ u := by dsimp only [u]; linarith [ht.1]
  have hu1 : u ≤ 1 := by dsimp only [u]; linarith [ht.2]
  have h1u : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hfactor : weakCorrelation t =
      (12 / 5 : ℝ) * (1 - u) ^ 5 +
        12 * u * (1 - u) ^ 4 +
        12 * u ^ 2 * (1 - u) ^ 3 := by
    unfold weakCorrelation evenStructuralCorrelation00
      evenStructuralCorrelation02 evenStructuralCorrelation22
    dsimp only [u]
    ring
  rw [hfactor]
  exact add_nonneg
    (add_nonneg (mul_nonneg (by norm_num) (pow_nonneg h1u 5))
      (mul_nonneg (mul_nonneg (by norm_num) hu0) (pow_nonneg h1u 4)))
    (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg u))
      (pow_nonneg h1u 3))

private theorem strongCorrelation_nonneg
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : 0 ≤ strongCorrelation t := by
  let u : ℝ := t / 2
  have hu0 : 0 ≤ u := by dsimp only [u]; linarith [ht.1]
  have hu1 : u ≤ 1 := by dsimp only [u]; linarith [ht.2]
  have h1u : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hfactor : strongCorrelation t =
      (12 / 5 : ℝ) * (1 - u) ^ 5 +
        4 * u * (1 - u) ^ 4 +
        4 * u ^ 2 * (1 - u) ^ 3 +
        8 * u ^ 3 * (1 - u) ^ 2 +
        8 * u ^ 4 * (1 - u) := by
    unfold strongCorrelation evenStructuralCorrelation00
      evenStructuralCorrelation02 evenStructuralCorrelation22
    dsimp only [u]
    ring
  rw [hfactor]
  positivity

private theorem step01AnalyticError_pencil_eq (a b d : ℝ) :
    a * step01AnalyticError00 + b * step01AnalyticError02 +
        d * step01AnalyticError22 =
      poleFreeAnalyticError (fun t ↦
        a * evenStructuralCorrelation00 t +
          b * evenStructuralCorrelation02 t +
          d * evenStructuralCorrelation22 t) := by
  have h00 := intervalIntegrable_poleFreeAnalyticError
    evenStructuralCorrelation00 (by unfold evenStructuralCorrelation00; fun_prop)
  have h02 := intervalIntegrable_poleFreeAnalyticError
    evenStructuralCorrelation02 (by unfold evenStructuralCorrelation02; fun_prop)
  have h22 := intervalIntegrable_poleFreeAnalyticError
    evenStructuralCorrelation22 (by unfold evenStructuralCorrelation22; fun_prop)
  unfold step01AnalyticError00 step01AnalyticError02 step01AnalyticError22
    poleFreeAnalyticError
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (h00.const_mul a) (h02.const_mul b),
    ← intervalIntegral.integral_add ((h00.const_mul a).add (h02.const_mul b))
      (h22.const_mul d)]
  apply intervalIntegral.integral_congr
  intro t _ht
  ring

private theorem weakAnalyticError_nonpos :
    step01AnalyticError00 - 2 * step01AnalyticError02 +
        step01AnalyticError22 ≤ 0 := by
  have heq := step01AnalyticError_pencil_eq 1 (-2) 1
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 2,
      (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) *
          weakCorrelation t ≤ 0 := by
    intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg
      (poleFreeKernel_sub_polynomial_nonpos ht) (weakCorrelation_nonneg ht)
  rw [show (fun t : ℝ ↦
      (1 : ℝ) * evenStructuralCorrelation00 t +
        (-2) * evenStructuralCorrelation02 t +
        (1 : ℝ) * evenStructuralCorrelation22 t) = weakCorrelation by
    funext t
    unfold weakCorrelation
    ring] at heq
  have hnonpos : poleFreeAnalyticError weakCorrelation ≤ 0 := by
    unfold poleFreeAnalyticError
    have h := intervalIntegral.integral_nonneg (μ := volume)
      (a := (0 : ℝ)) (b := 2)
      (by norm_num) (fun t ht ↦ neg_nonneg.mpr (hpoint t ht))
    rw [intervalIntegral.integral_neg] at h
    linarith
  nlinarith

private theorem strongAnalyticError_nonpos :
    step01AnalyticError00 + 2 * step01AnalyticError02 +
        step01AnalyticError22 ≤ 0 := by
  have heq := step01AnalyticError_pencil_eq 1 2 1
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 2,
      (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) *
          strongCorrelation t ≤ 0 := by
    intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg
      (poleFreeKernel_sub_polynomial_nonpos ht) (strongCorrelation_nonneg ht)
  rw [show (fun t : ℝ ↦
      (1 : ℝ) * evenStructuralCorrelation00 t +
        2 * evenStructuralCorrelation02 t +
        (1 : ℝ) * evenStructuralCorrelation22 t) = strongCorrelation by
    funext t
    unfold strongCorrelation
    ring] at heq
  have hnonpos : poleFreeAnalyticError strongCorrelation ≤ 0 := by
    unfold poleFreeAnalyticError
    have h := intervalIntegral.integral_nonneg (μ := volume)
      (a := (0 : ℝ)) (b := 2)
      (by norm_num) (fun t ht ↦ neg_nonneg.mpr (hpoint t ht))
    rw [intervalIntegral.integral_neg] at h
    linarith
  nlinarith

private theorem negativeLowCoordinate_lower_bounds :
    (6079 / 1000000 : ℝ) < nAlpha ∧
      (825379 / 1000000 : ℝ) < nGamma ∧
      (-39761 / 1000000 : ℝ) < nBeta := by
  have hmid00L := step01Midpoint00_gt
  have hmid00U := step01Midpoint00_lt
  have hmid02L := step01Midpoint02_gt
  have hmid02U := step01Midpoint02_lt
  have hmid22L := step01Midpoint22_gt
  have hsplit := step01_negativePerturbation_eq_midpoint_sub_error
  have h00err := abs_le.mp abs_step01AnalyticError00_le
  have h22err := abs_le.mp abs_step01AnalyticError22_le
  have hn00 : n00 = evenNegativePerturbation00 := by rfl
  have hn02 : n02 = evenNegativePerturbation02 := by rfl
  have hn22 : n22 = evenNegativePerturbation22 := by rfl
  unfold nAlpha nGamma nBeta weakMass strongMass skewMass
  rw [hn00, hn02, hn22, hsplit.1, hsplit.2.1, hsplit.2.2]
  constructor
  · nlinarith [weakAnalyticError_nonpos]
  constructor
  · nlinarith [strongAnalyticError_nonpos]
  · nlinarith

private theorem abs_poleFreeAnalyticError_p4Sum_lt_local :
    |poleFreeAnalyticError factorTwoIntrinsicP4CorrelationSum| <
      (3 / 32000 : ℝ) := by
  have hcont : Continuous factorTwoIntrinsicP4CorrelationSum := by
    simpa only [factorTwoIntrinsicP4CorrelationSum] using
      continuous_factorTwoIntrinsicP4Correlation04.add
        continuous_factorTwoIntrinsicP4Correlation24
  have herr := abs_poleFreeAnalyticError_le
    factorTwoIntrinsicP4CorrelationSum hcont
  have hL1 := integral_abs_factorTwoIntrinsicP4CorrelationSum_lt
  nlinarith

private theorem abs_poleFreeAnalyticError_p4Difference_lt_local :
    |poleFreeAnalyticError factorTwoIntrinsicP4CorrelationDifference| <
      (3 / 100000 : ℝ) := by
  have hcont : Continuous factorTwoIntrinsicP4CorrelationDifference := by
    simpa only [factorTwoIntrinsicP4CorrelationDifference] using
      continuous_factorTwoIntrinsicP4Correlation24.sub
        continuous_factorTwoIntrinsicP4Correlation04
  have herr := abs_poleFreeAnalyticError_le
    factorTwoIntrinsicP4CorrelationDifference hcont
  have hL1 := integral_abs_factorTwoIntrinsicP4CorrelationDifference_lt
  nlinarith

private theorem poleFreeAnalyticError_add_local
    (C D : ℝ → ℝ) (hC : Continuous C) (hD : Continuous D) :
    poleFreeAnalyticError C + poleFreeAnalyticError D =
      poleFreeAnalyticError (C + D) := by
  have hCI := intervalIntegrable_poleFreeAnalyticError C hC
  have hDI := intervalIntegrable_poleFreeAnalyticError D hD
  unfold poleFreeAnalyticError
  rw [← intervalIntegral.integral_add hCI hDI]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [Pi.add_apply]
  ring

private theorem poleFreeAnalyticError_sub_local
    (C D : ℝ → ℝ) (hC : Continuous C) (hD : Continuous D) :
    poleFreeAnalyticError C - poleFreeAnalyticError D =
      poleFreeAnalyticError (C - D) := by
  have hCI := intervalIntegrable_poleFreeAnalyticError C hC
  have hDI := intervalIntegrable_poleFreeAnalyticError D hD
  unfold poleFreeAnalyticError
  rw [← intervalIntegral.integral_sub hCI hDI]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [Pi.sub_apply]
  ring

private def p4P6SumLocal : ℝ :=
  poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
    poleFreeCoeff6 yoshidaEndpointA * (32 / 99 + 32 / 315)

private def p4P6DifferenceLocal : ℝ :=
  -poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
    poleFreeCoeff6 yoshidaEndpointA * (32 / 315 - 32 / 99)

private theorem p4P6Local_bounds :
    0 ≤ p4P6SumLocal ∧ p4P6SumLocal < (3 / 1000000 : ℝ) ∧
      (-3 / 1000000 : ℝ) < p4P6DifferenceLocal ∧
      p4P6DifferenceLocal ≤ 0 := by
  rcases poleFree_coefficient_bounds with
    ⟨_h0l, _h0u, _h2l, _h2u, h4l, h4u, h6l, h6u⟩
  unfold p4P6SumLocal p4P6DifferenceLocal
  norm_num at h4l h4u h6l h6u ⊢
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem plusCrossSum_structural_eq_local :
    factorTwoIntrinsicP4PlusCrossSum =
      (yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
        yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4) +
      poleFreeAnalyticError factorTwoIntrinsicP4CorrelationSum +
      p4P6SumLocal + 72 - 104 * Real.log 2 -
      (Real.log 3 / Real.sqrt 3) * factorTwoIntrinsicP4CorrelationSum
        (factorTwoPrimeShift / yoshidaEndpointA) := by
  have herr :
      poleFreeAnalyticError factorTwoIntrinsicP4Correlation04 +
          poleFreeAnalyticError factorTwoIntrinsicP4Correlation24 =
        poleFreeAnalyticError factorTwoIntrinsicP4CorrelationSum := by
    simpa only [factorTwoIntrinsicP4CorrelationSum] using
      poleFreeAnalyticError_add_local factorTwoIntrinsicP4Correlation04
        factorTwoIntrinsicP4Correlation24
        continuous_factorTwoIntrinsicP4Correlation04
        continuous_factorTwoIntrinsicP4Correlation24
  rcases factorTwoIntrinsicP4_perturbation_structural_eq with
    ⟨h04, h24, _h44⟩
  unfold factorTwoIntrinsicP4PlusCrossSum
    factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
  rw [h04, h24]
  unfold factorTwoIntrinsicP4PerturbationBase04
    factorTwoIntrinsicP4PerturbationBase24 p4P6SumLocal
    factorTwoIntrinsicP4CorrelationSum
  unfold factorTwoIntrinsicP4CorrelationSum at herr
  linear_combination herr

private theorem plusCrossDifference_structural_eq_local :
    factorTwoIntrinsicP4PlusCrossDifference =
      (yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
        yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4) +
      poleFreeAnalyticError factorTwoIntrinsicP4CorrelationDifference +
      p4P6DifferenceLocal - (158 / 3 : ℝ) + 76 * Real.log 2 -
      (Real.log 3 / Real.sqrt 3) *
        factorTwoIntrinsicP4CorrelationDifference
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  have herr :
      poleFreeAnalyticError factorTwoIntrinsicP4Correlation24 -
          poleFreeAnalyticError factorTwoIntrinsicP4Correlation04 =
        poleFreeAnalyticError factorTwoIntrinsicP4CorrelationDifference := by
    simpa only [factorTwoIntrinsicP4CorrelationDifference] using
      poleFreeAnalyticError_sub_local factorTwoIntrinsicP4Correlation24
        factorTwoIntrinsicP4Correlation04
        continuous_factorTwoIntrinsicP4Correlation24
        continuous_factorTwoIntrinsicP4Correlation04
  rcases factorTwoIntrinsicP4_perturbation_structural_eq with
    ⟨h04, h24, _h44⟩
  unfold factorTwoIntrinsicP4PlusCrossDifference
    factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
  rw [h04, h24]
  unfold factorTwoIntrinsicP4PerturbationBase04
    factorTwoIntrinsicP4PerturbationBase24 p4P6DifferenceLocal
    factorTwoIntrinsicP4CorrelationDifference
  unfold factorTwoIntrinsicP4CorrelationDifference at herr
  linear_combination herr

private theorem plusCrossCoordinate_lower_bounds :
    (1924 / 10000 : ℝ) < factorTwoIntrinsicP4PlusCrossSum ∧
      (1925 / 100000 : ℝ) < factorTwoIntrinsicP4PlusCrossDifference := by
  constructor
  · let clean : ℝ :=
      yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
        yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4
    let err : ℝ := poleFreeAnalyticError factorTwoIntrinsicP4CorrelationSum
    let beta : ℝ := Real.log 3 / Real.sqrt 3
    let P : ℝ := -factorTwoIntrinsicP4CorrelationSum
      (factorTwoPrimeShift / yoshidaEndpointA)
    have heq := plusCrossSum_structural_eq_local
    have hclean :=
      factorTwoIntrinsicP4CleanCross_sum_sub_seventeen_seventieths_abs_lt
    have herr := abs_poleFreeAnalyticError_p4Sum_lt_local
    have hp6 := p4P6Local_bounds
    have hlog := strict_log_two_fine_bounds
    have hbeta := log_three_div_sqrt_three_kernel_bounds
    have hcorr := factorTwoIntrinsicP4PrimeCorrelation_sum_difference_bounds
    have hP : (29333 / 500000 : ℝ) < P := by
      dsimp only [P]
      linarith [hcorr.1]
    have hbeta0 : 0 < beta := by dsimp only [beta]; positivity
    have hprimeLower :
        (63427 / 100000 : ℝ) * (29333 / 500000 : ℝ) < beta * P := by
      calc
        (63427 / 100000 : ℝ) * (29333 / 500000 : ℝ) <
            beta * (29333 / 500000 : ℝ) :=
          mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
        _ < beta * P := mul_lt_mul_of_pos_left hP hbeta0
    rw [abs_lt] at hclean herr
    dsimp only [clean, err, beta, P] at heq hprimeLower ⊢
    nlinarith
  · let clean : ℝ :=
      yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
        yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4
    let err : ℝ :=
      poleFreeAnalyticError factorTwoIntrinsicP4CorrelationDifference
    let beta : ℝ := Real.log 3 / Real.sqrt 3
    let Q : ℝ := factorTwoIntrinsicP4CorrelationDifference
      (factorTwoPrimeShift / yoshidaEndpointA)
    have heq := plusCrossDifference_structural_eq_local
    have hclean :=
      factorTwoIntrinsicP4CleanCross_difference_sub_three_seventieths_abs_lt
    have herr := abs_poleFreeAnalyticError_p4Difference_lt_local
    have hp6 := p4P6Local_bounds
    have hlog := strict_log_two_fine_bounds
    have hbeta := log_three_div_sqrt_three_kernel_bounds
    have hcorr := factorTwoIntrinsicP4PrimeCorrelation_sum_difference_bounds
    have hQ : (56755 / 1000000 : ℝ) < Q := by
      dsimp only [Q]
      exact hcorr.2.2.1
    have hbeta0 : 0 < beta := by dsimp only [beta]; positivity
    have hprimeLower :
        (63427 / 100000 : ℝ) * (56755 / 1000000 : ℝ) < beta * Q := by
      calc
        (63427 / 100000 : ℝ) * (56755 / 1000000 : ℝ) <
            beta * (56755 / 1000000 : ℝ) :=
          mul_lt_mul_of_pos_right hbeta.1 (by norm_num)
        _ < beta * Q := mul_lt_mul_of_pos_left hQ hbeta0
    rw [abs_lt] at hclean herr
    dsimp only [clean, err, beta, Q] at heq hprimeLower ⊢
    nlinarith

/-- Public sharp lower boxes for the two aligned positive-endpoint `P₄`
cross coordinates. -/
theorem factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds :
    (1924 / 10000 : ℝ) < factorTwoIntrinsicP4PlusCrossSum ∧
      (1925 / 100000 : ℝ) < factorTwoIntrinsicP4PlusCrossDifference :=
  plusCrossCoordinate_lower_bounds

private theorem negativeCrossCoordinate_upper_bounds :
    nS < (17 / 70 + 1 / 25000 - 1924 / 10000 : ℝ) ∧
      nD < (3 / 70 + 1 / 25000 - 1925 / 100000 : ℝ) := by
  have hclean := cleanCrossCoordinate_bounds
  have hplus := plusCrossCoordinate_lower_bounds
  have hSeq : nS = cS - factorTwoIntrinsicP4PlusCrossSum := by
    unfold nS cS crossSum n04 n24 c04 c24
      factorTwoIntrinsicP4PlusCrossSum factorTwoIntrinsicFourP45Cross04
      factorTwoIntrinsicFourP45Cross24
    ring
  have hDeq : nD = cD - factorTwoIntrinsicP4PlusCrossDifference := by
    unfold nD cD crossDiff n04 n24 c04 c24
      factorTwoIntrinsicP4PlusCrossDifference factorTwoIntrinsicFourP45Cross04
      factorTwoIntrinsicFourP45Cross24
    ring
  constructor <;> nlinarith

private theorem abs_poleFreeAnalyticError_correlation44_le_local :
    |poleFreeAnalyticError factorTwoIntrinsicP4Correlation44| ≤
      (1 / 12000 : ℝ) := by
  have herr := abs_poleFreeAnalyticError_le
    factorTwoIntrinsicP4Correlation44
      continuous_factorTwoIntrinsicP4Correlation44
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
  simp_rw [centeredEndpointCorrelation_p4] at hcorr
  rw [integral_factorTwoCenteredP4_sq] at hcorr
  nlinarith

private theorem n44_gt : (17645 / 100000 : ℝ) < n44 := by
  let beta : ℝ := Real.log 3 / Real.sqrt 3
  let C : ℝ := factorTwoIntrinsicP4Correlation44
    (factorTwoPrimeShift / yoshidaEndpointA)
  have heq := factorTwoIntrinsicP4_perturbation_structural_eq.2.2
  have herr := abs_poleFreeAnalyticError_correlation44_le_local
  have herrUpper : poleFreeAnalyticError factorTwoIntrinsicP4Correlation44 ≤
      (1 / 12000 : ℝ) := (le_abs_self _).trans herr
  have hlog := strict_log_two_fine_bounds.1
  have halpha := log_two_div_sqrt_two_kernel_lower
  have hbeta := log_three_div_sqrt_three_kernel_bounds.1
  have hbeta0 : 0 < beta := by dsimp only [beta]; positivity
  have hC := factorTwoIntrinsicP4PrimeCorrelation44_bounds.1
  have hprime :
      (63427 / 100000 : ℝ) * (68143 / 1000000) < beta * C := by
    calc
      (63427 / 100000 : ℝ) * (68143 / 1000000) <
          beta * (68143 / 1000000) :=
        mul_lt_mul_of_pos_right hbeta (by norm_num)
      _ < beta * C := mul_lt_mul_of_pos_left hC hbeta0
  unfold n44
  rw [heq]
  unfold factorTwoIntrinsicP4PerturbationBase44
  dsimp only [beta, C] at hprime
  norm_num at hlog halpha herrUpper hprime ⊢
  nlinarith

/-! The clean `P4` upper box uses the shifted-Legendre log-kernel
eigenidentity.  This is an exact integral calculation, not quadrature. -/

private theorem shiftedLegendreReal_four_eval (t : ℝ) :
    (shiftedLegendreReal 4).eval t =
      1 - 20 * t + 90 * t ^ 2 - 140 * t ^ 3 + 70 * t ^ 4 := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose]
  ring

private theorem centeredPullback_p4 (t : ℝ) :
    centeredPullback factorTwoCenteredP4 t =
      (shiftedLegendreReal 4).eval t := by
  rw [shiftedLegendreReal_four_eval]
  unfold centeredPullback factorTwoCenteredP4
  ring

/-- Exact centered raw logarithmic energy of the intrinsic degree-four
Legendre mode. -/
theorem centeredRawLogEnergy_factorTwoCenteredP4 :
    centeredRawLogEnergy factorTwoCenteredP4 = (50 / 27 : ℝ) := by
  let p : ℝ[X] := shiftedLegendreReal 4
  let pfun : unitInterval → ℝ := fun t ↦ p.eval (t : ℝ)
  let qfun : unitInterval → ℝ := fun t ↦
    centeredPullback factorTwoCenteredP4 (t : ℝ)
  have hpEnergy : Integrable (unitIntervalRawLogEnergyIntegrand pfun) := by
    simpa only [pfun] using
      integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hqEnergy : Integrable (unitIntervalRawLogEnergyIntegrand qfun) := by
    apply hpEnergy.congr
    filter_upwards [] with z
    unfold unitIntervalRawLogEnergyIntegrand
    dsimp only [pfun, qfun, p]
    rw [centeredPullback_p4, centeredPullback_p4]
  have hqP : unitIntervalLogEnergy qfun = unitIntervalLogEnergy pfun := by
    unfold unitIntervalLogEnergy
    apply congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) * z)
    apply integral_congr_ae
    filter_upwards [] with z
    unfold unitIntervalRawLogEnergyIntegrand
    dsimp only [pfun, qfun, p]
    rw [centeredPullback_p4, centeredPullback_p4]
  have hpIdentity : unitIntervalLogEnergy pfun =
      ∫ t : unitInterval,
        p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ) := by
    unfold unitIntervalLogEnergy
    rw [show (∫ z, unitIntervalRawLogEnergyIntegrand pfun z) =
        2 * ∫ t : unitInterval,
          p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ) by
      simpa only [pfun] using
        integral_unitIntervalRawLogEnergyIntegrand_polynomial p]
    ring
  have hpEigen : (∫ t : unitInterval,
      p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ)) =
      (2 * (harmonic 4 : ℝ)) *
        ∫ t : unitInterval, p.eval (t : ℝ) * p.eval (t : ℝ) := by
    rw [show shiftedLogKernel p =
        Polynomial.C (2 * (harmonic 4 : ℝ)) * p by
      dsimp only [p]
      exact shiftedLogKernel_shiftedLegendreReal 4]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  have hbridge := unitIntervalLogEnergy_centeredPullback
    factorTwoCenteredP4 hqEnergy
  change unitIntervalLogEnergy qfun =
    (1 / 4 : ℝ) * centeredRawLogEnergy factorTwoCenteredP4 at hbridge
  have hmass :
      (∫ t : unitInterval, p.eval (t : ℝ) * p.eval (t : ℝ)) =
        (1 / 9 : ℝ) := by
    calc
      _ = ∫ t : ℝ in 0..1, p.eval t * p.eval t :=
        integral_unitInterval_eq_intervalIntegral
          (fun t : ℝ ↦ p.eval t * p.eval t)
      _ = (1 / 9 : ℝ) := by
        dsimp only [p]
        simp_rw [shiftedLegendreReal_four_eval]
        ring_nf
        repeat' first
          | rw [intervalIntegral.integral_add
              (Continuous.intervalIntegrable (by fun_prop) 0 1)
              (Continuous.intervalIntegrable (by fun_prop) 0 1)]
          | rw [intervalIntegral.integral_sub
              (Continuous.intervalIntegrable (by fun_prop) 0 1)
              (Continuous.intervalIntegrable (by fun_prop) 0 1)]
        norm_num
  rw [hqP, hpIdentity, hpEigen, hmass] at hbridge
  norm_num [harmonic] at hbridge ⊢
  linarith

private theorem log_pi_mul_log_two_gt_local :
    (778205 / 1000000 : ℝ) < Real.log (Real.pi * Real.log 2) := by
  have hprod : (108879 / 50000 : ℝ) < Real.pi * Real.log 2 := by
    calc
      (108879 / 50000 : ℝ) <
          (3.14159265358979323846 : ℝ) *
            (69314718055 / 100000000000 : ℝ) := by norm_num
      _ < Real.pi * (69314718055 / 100000000000 : ℝ) :=
        mul_lt_mul_of_pos_right Real.pi_gt_d20 (by norm_num)
      _ < Real.pi * Real.log 2 :=
        mul_lt_mul_of_pos_left strict_log_two_fine_bounds.1 Real.pi_pos
  have hseries := Real.sum_range_le_log_div
    (x := (58879 / 158879 : ℝ)) (by norm_num) (by norm_num) 10
  have hrat : (778205 / 1000000 : ℝ) <
      Real.log (108879 / 50000 : ℝ) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    linarith
  exact hrat.trans
    (Real.strictMonoOn_log (by norm_num)
      (mul_pos Real.pi_pos (Real.log_pos (by norm_num))) hprod)

private theorem scalarMassLoss_gt_local :
    (135542 / 100000 : ℝ) < yoshidaEndpointScalarMassLoss := by
  have hgamma := fineGammaInterval_contains
  have hgammaLower : (5772155 / 10000000 : ℝ) ≤
      Real.eulerMascheroniConstant := by
    norm_num [fineGammaInterval, RatInterval.Contains] at hgamma ⊢
    exact hgamma.1
  unfold yoshidaEndpointScalarMassLoss
  linarith [log_pi_mul_log_two_gt_local, hgammaLower]

private theorem regularQuadratic_p4_nonneg :
    0 ≤ (yoshidaEndpointRegularQuadratic
      (fun x ↦ (factorTwoCenteredP4 x : ℂ))).re := by
  let e : ℝ :=
    oddCleanRegularEnvelopeError factorTwoIntrinsicP4Correlation44
  have heq := re_yoshidaEndpointRegularQuadratic_p4_eq
  have herr0 := abs_oddCleanRegularEnvelopeError_le
    factorTwoIntrinsicP4Correlation44
      continuous_factorTwoIntrinsicP4Correlation44
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
  simp_rw [centeredEndpointCorrelation_p4] at hcorr
  rw [integral_factorTwoCenteredP4_sq] at hcorr
  have herr : |e| ≤ (1 / 1125000 : ℝ) := by
    dsimp only [e]
    nlinarith
  have heLower : -(1 / 1125000 : ℝ) ≤ e := neg_le_of_abs_le herr
  have hA := strict_log_two_fine_bounds.1
  dsimp only [e] at heq heLower
  unfold yoshidaEndpointA at heq
  norm_num at hA heLower heq ⊢
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 ≤ (Real.log 2 / 2) ^ 3 := by positivity
  have h5 : 0 ≤ (Real.log 2 / 2) ^ 5 := by positivity
  nlinarith

private theorem hyperbolicQuadratic_p4_lt :
    yoshidaEndpointHyperbolicQuadratic
        (fun x ↦ (factorTwoCenteredP4 x : ℂ)) < (3 / 1250 : ℝ) := by
  let M : ℝ := centeredCoshMoment factorTwoCenteredP4
    (yoshidaEndpointA / 2)
  have hw := exp_weighted_centeredCoshMoment_P4_sq_le_profile
    (yoshidaEndpointA / 2)
    (div_nonneg yoshidaEndpointA_pos.le (by norm_num))
  have hprofile := factorTwoP4RankProfile_le_max
    (yoshidaEndpointA / 2)
    (div_nonneg yoshidaEndpointA_pos.le (by norm_num))
  have hw' : Real.exp (-yoshidaEndpointA) * M ^ 2 ≤
      (16384 / 9765625 : ℝ) := by
    dsimp only [M]
    have hrewrite : -2 * (yoshidaEndpointA / 2) = -yoshidaEndpointA := by ring
    rw [hrewrite] at hw
    exact hw.trans hprofile
  have hexpA : Real.exp yoshidaEndpointA < 2 := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) by
      symm
      exact Real.exp_log (by norm_num)]
    apply Real.exp_lt_exp.mpr
    unfold yoshidaEndpointA
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hexpNeg : (1 / 2 : ℝ) < Real.exp (-yoshidaEndpointA) := by
    have hprod : Real.exp yoshidaEndpointA *
        Real.exp (-yoshidaEndpointA) = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hpos := Real.exp_pos (-yoshidaEndpointA)
    nlinarith
  have hM : M ^ 2 ≤ 2 * (16384 / 9765625 : ℝ) := by
    have hscaled : (1 / 2 : ℝ) * M ^ 2 ≤
        Real.exp (-yoshidaEndpointA) * M ^ 2 :=
      mul_le_mul_of_nonneg_right hexpNeg.le (sq_nonneg M)
    nlinarith
  have hA : yoshidaEndpointA < (347 / 1000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have hmoment : yoshidaEndpointCoshMoment factorTwoCenteredP4 = M := by
    unfold yoshidaEndpointCoshMoment
    dsimp only [M, centeredCoshMoment]
    apply intervalIntegral.integral_congr
    intro x _hx
    change Real.cosh (yoshidaEndpointA * x / 2) * factorTwoCenteredP4 x =
      Real.cosh (yoshidaEndpointA / 2 * x) * factorTwoCenteredP4 x
    rw [show yoshidaEndpointA * x / 2 =
      yoshidaEndpointA / 2 * x by ring]
  have hsinh := yoshidaEndpointSinhMoment_eq_zero_of_even
    factorTwoCenteredP4 even_factorTwoCenteredP4
  rw [yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments,
    hsinh, hmoment]
  norm_num
  have hA0 := yoshidaEndpointA_pos
  have hMsq0 := sq_nonneg M
  nlinarith

private theorem hyperbolicQuadratic_p4_lt_one_div_hundred_million :
    yoshidaEndpointHyperbolicQuadratic
        (fun x ↦ (factorTwoCenteredP4 x : ℂ)) <
      (1 / 100000000 : ℝ) := by
  let M : ℝ := centeredCoshMoment factorTwoCenteredP4
    (yoshidaEndpointA / 2)
  have hw := exp_weighted_centeredCoshMoment_P4_sq_le_profile
    (yoshidaEndpointA / 2)
    (div_nonneg yoshidaEndpointA_pos.le (by norm_num))
  have hAupper : yoshidaEndpointA < (347 / 1000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have harg : yoshidaEndpointA / 2 ∈ Icc (0 : ℝ) 8 := by
    constructor
    · exact div_nonneg yoshidaEndpointA_pos.le (by norm_num)
    · linarith
  have hcap : (347 / 2000 : ℝ) ∈ Icc (0 : ℝ) 8 := by
    norm_num
  have hmono :
      factorTwoP4RankProfile (yoshidaEndpointA / 2) ≤
        factorTwoP4RankProfile (347 / 2000 : ℝ) :=
    factorTwoP4RankProfile_monotoneOn harg hcap (by linarith)
  have hprofile :
      factorTwoP4RankProfile (yoshidaEndpointA / 2) <
        (1 / 2000000000 : ℝ) := by
    calc
      factorTwoP4RankProfile (yoshidaEndpointA / 2) ≤
          factorTwoP4RankProfile (347 / 2000 : ℝ) := hmono
      _ < (1 / 2000000000 : ℝ) := by
        norm_num [factorTwoP4RankProfile]
  have hw' :
      Real.exp (-yoshidaEndpointA) * M ^ 2 <
        (1 / 2000000000 : ℝ) := by
    dsimp only [M]
    have hrewrite : -2 * (yoshidaEndpointA / 2) = -yoshidaEndpointA := by
      ring
    rw [hrewrite] at hw
    exact hw.trans_lt hprofile
  have hexpA : Real.exp yoshidaEndpointA < 2 := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) by
      symm
      exact Real.exp_log (by norm_num)]
    apply Real.exp_lt_exp.mpr
    unfold yoshidaEndpointA
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hexpNeg : (1 / 2 : ℝ) < Real.exp (-yoshidaEndpointA) := by
    have hprod : Real.exp yoshidaEndpointA *
        Real.exp (-yoshidaEndpointA) = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hpos := Real.exp_pos (-yoshidaEndpointA)
    nlinarith
  have hM : M ^ 2 < (1 / 1000000000 : ℝ) := by
    have hscaled : (1 / 2 : ℝ) * M ^ 2 ≤
        Real.exp (-yoshidaEndpointA) * M ^ 2 :=
      mul_le_mul_of_nonneg_right hexpNeg.le (sq_nonneg M)
    nlinarith
  have hmoment : yoshidaEndpointCoshMoment factorTwoCenteredP4 = M := by
    unfold yoshidaEndpointCoshMoment
    dsimp only [M, centeredCoshMoment]
    apply intervalIntegral.integral_congr
    intro x _hx
    change Real.cosh (yoshidaEndpointA * x / 2) * factorTwoCenteredP4 x =
      Real.cosh (yoshidaEndpointA / 2 * x) * factorTwoCenteredP4 x
    rw [show yoshidaEndpointA * x / 2 =
      yoshidaEndpointA / 2 * x by ring]
  have hsinh := yoshidaEndpointSinhMoment_eq_zero_of_even
    factorTwoCenteredP4 even_factorTwoCenteredP4
  rw [yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments,
    hsinh, hmoment]
  norm_num
  have hA0 := yoshidaEndpointA_pos
  have hMsq0 := sq_nonneg M
  nlinarith

private theorem c44_lt : c44 < (8 / 25 : ℝ) := by
  have hmass := scalarMassLoss_gt_local
  have hreg := regularQuadratic_p4_nonneg
  have hregScaled : 0 ≤ yoshidaEndpointA *
      (yoshidaEndpointRegularQuadratic
        (fun x ↦ (factorTwoCenteredP4 x : ℂ))).re :=
    mul_nonneg yoshidaEndpointA_pos.le hreg
  have hhyper := hyperbolicQuadratic_p4_lt
  have hlog := strict_log_two_fine_bounds.1
  unfold c44 yoshidaEndpointOddCleanQuadratic
  rw [centeredRawLogEnergy_factorTwoCenteredP4,
    integral_endpointPotential_mul_factorTwoCenteredP4_sq,
    integral_factorTwoCenteredP4_sq]
  norm_num at hmass hregScaled hhyper hlog ⊢
  nlinarith

private theorem c44_lt_three_hundred_fifteen_thousandths :
    c44 < (315 / 1000 : ℝ) := by
  have hmass := scalarMassLoss_gt_local
  have hreg := regularQuadratic_p4_nonneg
  have hregScaled : 0 ≤ yoshidaEndpointA *
      (yoshidaEndpointRegularQuadratic
        (fun x ↦ (factorTwoCenteredP4 x : ℂ))).re :=
    mul_nonneg yoshidaEndpointA_pos.le hreg
  have hhyper := hyperbolicQuadratic_p4_lt_one_div_hundred_million
  have hlog := strict_log_two_fine_bounds.1
  unfold c44 yoshidaEndpointOddCleanQuadratic
  rw [centeredRawLogEnergy_factorTwoCenteredP4,
    integral_endpointPotential_mul_factorTwoCenteredP4_sq,
    integral_factorTwoCenteredP4_sq]
  norm_num at hmass hregScaled hhyper hlog ⊢
  nlinarith

/-- Public structural upper bound for the clean `P₄` diagonal. -/
theorem factorTwoP4_clean_diagonal_lt_eight_div_twenty_five :
    yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4 <
      (8 / 25 : ℝ) := by
  simpa only [c44] using c44_lt

/-- Tight clean `P₄` diagonal cap obtained by evaluating the structural
rank profile at the actual endpoint scale. -/
theorem factorTwoP4_clean_diagonal_lt_three_hundred_fifteen_thousandths :
    yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4 <
      (315 / 1000 : ℝ) := by
  simpa only [c44] using c44_lt_three_hundred_fifteen_thousandths

/-- Tight lower box for the positive quantity obtained by negating the
`P₄` symmetric perturbation. -/
theorem factorTwoP4_negative_perturbation_gt_one_seventy_six_forty_five :
    (17645 / 100000 : ℝ) <
      -factorTwoCenteredSymmetricPerturbation factorTwoCenteredP4 := by
  simpa only [n44] using n44_gt

/-- Tight positive-endpoint `P₄` diagonal cap. -/
theorem factorTwoIntrinsicSixP4Diagonal_plus_lt_one_thirty_nine_thousandths :
    factorTwoIntrinsicSixP4Diagonal 1 < (139 / 1000 : ℝ) := by
  have hclean := c44_lt_three_hundred_fifteen_thousandths
  have hpert := n44_gt
  have heq : factorTwoIntrinsicSixP4Diagonal 1 = c44 - n44 := by
    unfold factorTwoIntrinsicSixP4Diagonal factorTwoEndpointPhaseDiagonal
      c44 n44
    ring
  rw [heq]
  linarith

/-- The negative-endpoint `P₄` diagonal inherits a convenient rational
upper bound from the clean estimate and the proved perturbation lower
bound. -/
theorem factorTwoIntrinsicSixP4Diagonal_minus_lt_sixty_four_div_one_twenty_five :
    factorTwoIntrinsicSixP4Diagonal (-1) < (64 / 125 : ℝ) := by
  have hclean := factorTwoP4_clean_diagonal_lt_eight_div_twenty_five
  have hpert := factorTwoCenteredSymmetricPerturbation_p4_lower
  unfold factorTwoIntrinsicSixP4Diagonal factorTwoEndpointPhaseDiagonal
  norm_num at hclean hpert ⊢
  nlinarith

/-! ## Monotonicity of the cancellation-preserving bracket -/

private theorem positive_sq_bounds
    {u l r : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hur : u ≤ r) :
    l ^ 2 ≤ u ^ 2 ∧ u ^ 2 ≤ r ^ 2 := by
  have hu : 0 ≤ u := hl.trans hlu
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlu) (add_nonneg hu hl)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hur)
      (add_nonneg (hu.trans hur) hu)]

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

private def alphaSlope (γ S f x z : ℝ) : ℝ :=
  f * x ^ 2 - 2 * S * x * z + γ * z ^ 2

private def gammaSlope (α D f y z : ℝ) : ℝ :=
  f * y ^ 2 + 2 * D * y * z + α * z ^ 2

private def betaSecantSlope (β β' S D f x y z : ℝ) : ℝ :=
  2 * f * x * y + 2 * D * x * z - 2 * S * y * z -
    (β + β') * z ^ 2

private def sDescendingSlope (α β S S' D x y z : ℝ) : ℝ :=
  (S + S') * y ^ 2 + 2 * D * x * y + 2 * α * x * z +
    2 * β * y * z

private def dDescendingSlope (γ β S D D' x y z : ℝ) : ℝ :=
  (D + D') * x ^ 2 + 2 * S * x * y - 2 * β * x * z -
    2 * γ * y * z

private def fSlope (α γ β x y : ℝ) : ℝ :=
  α * x ^ 2 + γ * y ^ 2 + 2 * β * x * y

private theorem alphaSlope_pos
    {γ S f x z : ℝ}
    (hγ : 0 ≤ γ) (hS0 : 0 ≤ S) (hS : S ≤ 1 / 4)
    (hf : 17 / 100 ≤ f) (hfu : f ≤ 8 / 25)
    (hx : 14 / 25 ≤ x) (hxu : x ≤ 57 / 100)
    (hz : 7 / 50 ≤ z) (hzu : z ≤ 3 / 20) :
    0 < alphaSlope γ S f x z := by
  have hxsq := positive_sq_bounds (by norm_num : (0 : ℝ) ≤ 14 / 25)
    hx hxu
  have hfxsq := positive_mul_bounds (by norm_num : (0 : ℝ) ≤ 17 / 100)
    (sq_nonneg (14 / 25 : ℝ)) hf hfu hxsq.1 hxsq.2
  have hSxz := positive_mul3_bounds (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 14 / 25)
    (by norm_num : (0 : ℝ) ≤ 7 / 50)
    hS0 hS hx hxu hz hzu
  have hγz : 0 ≤ γ * z ^ 2 := mul_nonneg hγ (sq_nonneg z)
  unfold alphaSlope
  norm_num at hfxsq hSxz ⊢
  nlinarith

private theorem gammaSlope_nonneg
    {α D f y z : ℝ}
    (hα : 0 ≤ α) (hD : 0 ≤ D) (hf : 0 ≤ f)
    (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ gammaSlope α D f y z := by
  unfold gammaSlope
  positivity

private theorem betaSecantSlope_pos
    {β β' S D f x y z : ℝ}
    (hβ : β ≤ 0) (hβ' : β' ≤ 0)
    (hS0 : 0 ≤ S) (hS : S ≤ 1 / 4) (hD : 0 ≤ D)
    (hf : 17 / 100 ≤ f) (hfu : f ≤ 8 / 25)
    (hx : 14 / 25 ≤ x) (hxu : x ≤ 57 / 100)
    (hy : 2 / 125 ≤ y) (hyu : y ≤ 1 / 50)
    (hz : 7 / 50 ≤ z) (hzu : z ≤ 3 / 20) :
    0 < betaSecantSlope β β' S D f x y z := by
  have hfxy := positive_mul3_bounds (by norm_num : (0 : ℝ) ≤ 17 / 100)
    (by norm_num : (0 : ℝ) ≤ 14 / 25)
    (by norm_num : (0 : ℝ) ≤ 2 / 125)
    hf hfu hx hxu hy hyu
  have hSyz := positive_mul3_bounds (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 2 / 125)
    (by norm_num : (0 : ℝ) ≤ 7 / 50)
    hS0 hS hy hyu hz hzu
  have hDxz : 0 ≤ D * x * z := by positivity
  have hβz : (β + β') * z ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (add_nonpos hβ hβ') (sq_nonneg z)
  unfold betaSecantSlope
  norm_num at hfxy hSyz ⊢
  nlinarith

private theorem sDescendingSlope_pos
    {α β S S' D x y z : ℝ}
    (hα : 0 ≤ α) (hβl : (-1 / 25 : ℝ) ≤ β) (_hβu : β ≤ 0)
    (hS : 0 ≤ S) (hS' : 0 ≤ S')
    (hD : 1 / 50 ≤ D) (hDu : D ≤ 1 / 20)
    (hx : 14 / 25 ≤ x) (hxu : x ≤ 57 / 100)
    (hy : 2 / 125 ≤ y) (hyu : y ≤ 1 / 50)
    (hz : 7 / 50 ≤ z) (hzu : z ≤ 3 / 20) :
    0 < sDescendingSlope α β S S' D x y z := by
  have hDxy := positive_mul3_bounds (by norm_num : (0 : ℝ) ≤ 1 / 50)
    (by norm_num : (0 : ℝ) ≤ 14 / 25)
    (by norm_num : (0 : ℝ) ≤ 2 / 125)
    hD hDu hx hxu hy hyu
  have hyz := positive_mul_bounds (by norm_num : (0 : ℝ) ≤ 2 / 125)
    (by norm_num : (0 : ℝ) ≤ 7 / 50) hy hyu hz hzu
  have hβyz : (-1 / 25 : ℝ) * (1 / 50) * (3 / 20) ≤ β * y * z := by
    have hβy : (-1 / 25 : ℝ) * y ≤ β * y :=
      mul_le_mul_of_nonneg_right hβl (by linarith)
    have hlow : (-1 / 25 : ℝ) * (1 / 50) ≤
        (-1 / 25 : ℝ) * (y * z) := by
      have : y * z ≤ (1 / 50 : ℝ) * (3 / 20) := hyz.2
      nlinarith
    have hz0 : 0 ≤ z := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hβy hz0]
  have hrest : 0 ≤ (S + S') * y ^ 2 + 2 * α * x * z := by positivity
  unfold sDescendingSlope
  norm_num at hDxy hβyz ⊢
  nlinarith

private theorem dDescendingSlope_pos
    {γ β S D D' x y z : ℝ}
    (hγ : 0 ≤ γ) (hγu : γ ≤ 7 / 5)
    (hβ : β ≤ 0) (hS : 0 ≤ S)
    (hD : 1 / 50 ≤ D) (hD' : 1 / 50 ≤ D')
    (hx : 14 / 25 ≤ x) (hxu : x ≤ 57 / 100)
    (hy : 2 / 125 ≤ y) (hyu : y ≤ 1 / 50)
    (hz : 7 / 50 ≤ z) (hzu : z ≤ 3 / 20) :
    0 < dDescendingSlope γ β S D D' x y z := by
  have hxsq := positive_sq_bounds (by norm_num : (0 : ℝ) ≤ 14 / 25)
    hx hxu
  have hyz := positive_mul_bounds (by norm_num : (0 : ℝ) ≤ 2 / 125)
    (by norm_num : (0 : ℝ) ≤ 7 / 50) hy hyu hz hzu
  have hγyz : γ * y * z ≤ (7 / 5 : ℝ) * (1 / 50) * (3 / 20) :=
    (positive_mul3_bounds (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) ≤ 2 / 125)
      (by norm_num : (0 : ℝ) ≤ 7 / 50)
      hγ hγu hy hyu hz hzu).2
  have hDx : (2 / 50 : ℝ) * (14 / 25) ^ 2 ≤
      (D + D') * x ^ 2 := by
    have hsum : (2 / 50 : ℝ) ≤ D + D' := by linarith
    exact mul_le_mul hsum hxsq.1 (sq_nonneg _) (by positivity)
  have hSxy : 0 ≤ S * x * y := by positivity
  have hβxz : β * x * z ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hβ (by linarith)) (by linarith)
  have hhelp : 0 ≤ 2 * S * x * y - 2 * β * x * z := by linarith
  unfold dDescendingSlope
  norm_num at hγyz hDx ⊢
  nlinarith

private theorem fSlope_pos
    {α γ β x y : ℝ}
    (hα : 3 / 500 ≤ α) (hγ : 0 ≤ γ)
    (hβl : (-1 / 25 : ℝ) ≤ β) (_hβu : β ≤ 0)
    (hx : 14 / 25 ≤ x) (hxu : x ≤ 57 / 100)
    (hy : 2 / 125 ≤ y) (hyu : y ≤ 1 / 50) :
    0 < fSlope α γ β x y := by
  have hxsq := positive_sq_bounds (by norm_num : (0 : ℝ) ≤ 14 / 25)
    hx hxu
  have hα0 : 0 ≤ α := by linarith
  have hαx : (3 / 500 : ℝ) * (14 / 25) ^ 2 ≤ α * x ^ 2 :=
    mul_le_mul hα hxsq.1 (sq_nonneg _) hα0
  have hxy := positive_mul_bounds (by norm_num : (0 : ℝ) ≤ 14 / 25)
    (by norm_num : (0 : ℝ) ≤ 2 / 125) hx hxu hy hyu
  have hβxy : (-1 / 25 : ℝ) * (57 / 100) * (1 / 50) ≤
      β * x * y := by
    have hβx : (-1 / 25 : ℝ) * x ≤ β * x :=
      mul_le_mul_of_nonneg_right hβl (by linarith)
    have hlow : (-1 / 25 : ℝ) * ((57 / 100) * (1 / 50)) ≤
        (-1 / 25 : ℝ) * (x * y) := by nlinarith [hxy.2]
    nlinarith [mul_le_mul_of_nonneg_right hβx (by linarith : 0 ≤ y)]
  have hγy : 0 ≤ γ * y ^ 2 := mul_nonneg hγ (sq_nonneg y)
  unfold fSlope
  norm_num at hαx hβxy ⊢
  nlinarith

private theorem adjugateBracket_mono_alpha
    {α α' γ β S D f x y z : ℝ}
    (hα : α ≤ α') (hslope : 0 ≤ alphaSlope γ S f x z) :
    adjugateBracket α γ β S D f x y z ≤
      adjugateBracket α' γ β S D f x y z := by
  have hid :
      adjugateBracket α' γ β S D f x y z -
          adjugateBracket α γ β S D f x y z =
        (α' - α) * alphaSlope γ S f x z := by
    unfold adjugateBracket alphaSlope
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hα) hslope

private theorem adjugateBracket_mono_gamma
    {α γ γ' β S D f x y z : ℝ}
    (hγ : γ ≤ γ') (hslope : 0 ≤ gammaSlope α D f y z) :
    adjugateBracket α γ β S D f x y z ≤
      adjugateBracket α γ' β S D f x y z := by
  have hid :
      adjugateBracket α γ' β S D f x y z -
          adjugateBracket α γ β S D f x y z =
        (γ' - γ) * gammaSlope α D f y z := by
    unfold adjugateBracket gammaSlope
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hγ) hslope

private theorem adjugateBracket_mono_beta
    {α γ β β' S D f x y z : ℝ}
    (hβ : β ≤ β')
    (hslope : 0 ≤ betaSecantSlope β β' S D f x y z) :
    adjugateBracket α γ β S D f x y z ≤
      adjugateBracket α γ β' S D f x y z := by
  have hid :
      adjugateBracket α γ β' S D f x y z -
          adjugateBracket α γ β S D f x y z =
        (β' - β) * betaSecantSlope β β' S D f x y z := by
    unfold adjugateBracket betaSecantSlope
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hβ) hslope

private theorem adjugateBracket_mono_S_descending
    {α γ β S S' D f x y z : ℝ}
    (hS : S' ≤ S)
    (hslope : 0 ≤ sDescendingSlope α β S S' D x y z) :
    adjugateBracket α γ β S D f x y z ≤
      adjugateBracket α γ β S' D f x y z := by
  have hid :
      adjugateBracket α γ β S' D f x y z -
          adjugateBracket α γ β S D f x y z =
        (S - S') * sDescendingSlope α β S S' D x y z := by
    unfold adjugateBracket sDescendingSlope
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hS) hslope

private theorem adjugateBracket_mono_D_descending
    {α γ β S D D' f x y z : ℝ}
    (hD : D' ≤ D)
    (hslope : 0 ≤ dDescendingSlope γ β S D D' x y z) :
    adjugateBracket α γ β S D f x y z ≤
      adjugateBracket α γ β S D' f x y z := by
  have hid :
      adjugateBracket α γ β S D' f x y z -
          adjugateBracket α γ β S D f x y z =
        (D - D') * dDescendingSlope γ β S D D' x y z := by
    unfold adjugateBracket dDescendingSlope
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hD) hslope

private theorem adjugateBracket_mono_f
    {α γ β S D f f' x y z : ℝ}
    (hf : f ≤ f') (hslope : 0 ≤ fSlope α γ β x y) :
    adjugateBracket α γ β S D f x y z ≤
      adjugateBracket α γ β S D f' x y z := by
  have hid :
      adjugateBracket α γ β S D f' x y z -
          adjugateBracket α γ β S D f x y z =
        (f' - f) * fSlope α γ β x y := by
    unfold adjugateBracket fSlope
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hf) hslope

private theorem alternatingCoordinate_bounds :
    (56168 / 100000 : ℝ) < xAlt ∧ xAlt < (56173 / 100000 : ℝ) ∧
      (1687 / 100000 : ℝ) < yAlt ∧ yAlt < (1692 / 100000 : ℝ) ∧
      (141 / 1000 : ℝ) < a41 ∧ a41 < (144 / 1000 : ℝ) := by
  rcases factorTwoIntrinsicAlternatingSharpBounds with
    ⟨hxL, hxU, hyL, hyU, _h03⟩
  have hz := factorTwoIntrinsicFourP45Cross41_bounds
  simpa only [xAlt, yAlt, a01, a21, a41] using
    ⟨hxL, hxU, hyL, hyU, hz.1, hz.2⟩

private theorem abs_strongAnalyticError_le :
    |step01AnalyticError00 + 2 * step01AnalyticError02 +
        step01AnalyticError22| ≤ (9 / 10000 : ℝ) := by
  have hprofile := abs_poleFreeAnalyticError_profile_le 1 1
  have hfun : centeredEndpointCorrelation
      (factorTwoEvenStructuralLowProfile 1 1) = strongCorrelation := by
    funext t
    rw [centeredEndpointCorrelation_evenStructuralProfile]
    unfold strongCorrelation
    norm_num
  rw [hfun] at hprofile
  have heq := step01AnalyticError_pencil_eq 1 2 1
  norm_num at heq
  rw [show (fun t : ℝ ↦
      evenStructuralCorrelation00 t +
        2 * evenStructuralCorrelation02 t +
        evenStructuralCorrelation22 t) = strongCorrelation by
      funext t
      unfold strongCorrelation
      ring] at heq
  rw [heq]
  norm_num at hprofile ⊢
  exact hprofile

private theorem negativeCoordinate_box :
    0 < nAlpha ∧ 0 < nGamma ∧ nGamma < (7 / 5 : ℝ) ∧
      (-1 / 25 : ℝ) < nBeta ∧ nBeta < 0 ∧
      0 < nS ∧ nS < (1 / 4 : ℝ) ∧
      (1 / 50 : ℝ) < nD ∧ nD < (1 / 20 : ℝ) := by
  have hlow := negativeLowCoordinate_lower_bounds
  have hcrossU := negativeCrossCoordinate_upper_bounds
  have hclean := cleanCrossCoordinate_bounds
  have hplusS := factorTwoIntrinsicP4PlusCrossSum_bounds
  have hplusD := factorTwoIntrinsicP4PlusCrossDifference_bounds
  have hsplit := step01_negativePerturbation_eq_midpoint_sub_error
  have hmid00L := step01Midpoint00_gt
  have hmid00U := step01Midpoint00_lt
  have hmid02U := step01Midpoint02_lt
  have hmid22U := step01Midpoint22_lt
  have h00err := abs_le.mp abs_step01AnalyticError00_le
  have h22err := abs_le.mp abs_step01AnalyticError22_le
  have hstrongErr := abs_le.mp abs_strongAnalyticError_le
  have hn00 : n00 = evenNegativePerturbation00 := by rfl
  have hn02 : n02 = evenNegativePerturbation02 := by rfl
  have hn22 : n22 = evenNegativePerturbation22 := by rfl
  have hnGammaEq : nGamma =
      step01Midpoint00 + 2 * step01Midpoint02 + step01Midpoint22 -
        (step01AnalyticError00 + 2 * step01AnalyticError02 +
          step01AnalyticError22) := by
    unfold nGamma strongMass
    rw [hn00, hn02, hn22, hsplit.1, hsplit.2.1, hsplit.2.2]
    ring
  have hnBetaEq : nBeta =
      (step01Midpoint22 - step01AnalyticError22) -
        (step01Midpoint00 - step01AnalyticError00) := by
    unfold nBeta skewMass
    rw [hn00, hn22, hsplit.1, hsplit.2.2]
  have hSeq : nS = cS - factorTwoIntrinsicP4PlusCrossSum := by
    unfold nS cS crossSum n04 n24 c04 c24
      factorTwoIntrinsicP4PlusCrossSum factorTwoIntrinsicFourP45Cross04
      factorTwoIntrinsicFourP45Cross24
    ring
  have hDeq : nD = cD - factorTwoIntrinsicP4PlusCrossDifference := by
    unfold nD cD crossDiff n04 n24 c04 c24
      factorTwoIntrinsicP4PlusCrossDifference factorTwoIntrinsicFourP45Cross04
      factorTwoIntrinsicFourP45Cross24
    ring
  constructor
  · linarith [hlow.1]
  constructor
  · linarith [hlow.2.1]
  constructor
  · rw [hnGammaEq]
    norm_num at hmid00U hmid02U hmid22U hstrongErr ⊢
    linarith
  constructor
  · linarith [hlow.2.2]
  constructor
  · rw [hnBetaEq]
    norm_num at hmid00L hmid22U h00err h22err ⊢
    linarith
  constructor
  · rw [hSeq]
    norm_num at hclean hplusS ⊢
    linarith
  constructor
  · norm_num at hcrossU ⊢
    linarith
  constructor
  · rw [hDeq]
    norm_num at hclean hplusD ⊢
    linarith
  · norm_num at hcrossU ⊢
    linarith

private def cleanAlphaCorner : ℝ := 135 / 10000
private def cleanGammaCorner : ℝ := 13745 / 10000
private def cleanBetaCorner : ℝ := -394 / 10000
private def cleanSCorner : ℝ := 17 / 70 - 1 / 25000
private def cleanDCorner : ℝ := 3 / 70 - 1 / 25000
private def cleanFCorner : ℝ := 8 / 25

private def negativeAlphaCorner : ℝ := 6079 / 1000000
private def negativeGammaCorner : ℝ := 825379 / 1000000
private def negativeBetaCorner : ℝ := -39761 / 1000000
private def negativeSCorner : ℝ :=
  17 / 70 + 1 / 25000 - 1924 / 10000
private def negativeDCorner : ℝ :=
  3 / 70 + 1 / 25000 - 1925 / 100000
private def negativeFCorner : ℝ := 17645 / 100000

private theorem cleanBracket_le_corner
    {x y z : ℝ}
    (hxL : (56168 / 100000 : ℝ) < x)
    (hxU : x < (56173 / 100000 : ℝ))
    (hyL : (1687 / 100000 : ℝ) < y)
    (hyU : y < (1692 / 100000 : ℝ))
    (hzL : (141 / 1000 : ℝ) < z)
    (hzU : z < (144 / 1000 : ℝ)) :
    adjugateBracket cAlpha cGamma cBeta cS cD c44 x y z ≤
      adjugateBracket cleanAlphaCorner cleanGammaCorner cleanBetaCorner
        cleanSCorner cleanDCorner cleanFCorner x y z := by
  rcases cleanLowCoordinate_bounds with
    ⟨hαL, hαU, hγL, hγU, hβL, hβU⟩
  rcases cleanCrossCoordinate_bounds with ⟨hSL, hSU, hDL, hDU⟩
  have hfL : (1571 / 5000 : ℝ) < c44 := by
    simpa only [c44] using
      one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  have hx : (14 / 25 : ℝ) ≤ x := by linarith
  have hxu : x ≤ (57 / 100 : ℝ) := by linarith
  have hy : (2 / 125 : ℝ) ≤ y := by linarith
  have hyu : y ≤ (1 / 50 : ℝ) := by linarith
  have hz : (7 / 50 : ℝ) ≤ z := by linarith
  have hzu : z ≤ (3 / 20 : ℝ) := by linarith
  have hγ0 : 0 ≤ cGamma := by linarith
  have hS0 : 0 ≤ cS := by linarith
  have hSu : cS ≤ (1 / 4 : ℝ) := by norm_num at hSU ⊢; linarith
  have hD0 : 0 ≤ cD := by linarith
  have hDL' : (1 / 50 : ℝ) ≤ cD := by norm_num at hDL ⊢; linarith
  have hDU' : cD ≤ (1 / 20 : ℝ) := by norm_num at hDU ⊢; linarith
  have hf : (17 / 100 : ℝ) ≤ c44 := by linarith
  have hfu : c44 ≤ (8 / 25 : ℝ) := c44_lt.le
  have hβnonpos : cBeta ≤ 0 := by linarith
  have h1 : adjugateBracket cAlpha cGamma cBeta cS cD c44 x y z ≤
      adjugateBracket cleanAlphaCorner cGamma cBeta cS cD c44 x y z :=
    adjugateBracket_mono_alpha (by simpa only [cleanAlphaCorner] using hαU.le)
      (alphaSlope_pos hγ0 hS0 hSu hf hfu hx hxu hz hzu).le
  have h2 : adjugateBracket cleanAlphaCorner cGamma cBeta cS cD c44 x y z ≤
      adjugateBracket cleanAlphaCorner cleanGammaCorner cBeta cS cD c44 x y z :=
    adjugateBracket_mono_gamma
      (by simpa only [cleanGammaCorner] using hγU.le)
      (gammaSlope_nonneg (by norm_num [cleanAlphaCorner]) hD0
        (by linarith : 0 ≤ c44) (by linarith) (by linarith))
  have h3 :
      adjugateBracket cleanAlphaCorner cleanGammaCorner cBeta cS cD c44 x y z ≤
        adjugateBracket cleanAlphaCorner cleanGammaCorner cleanBetaCorner
          cS cD c44 x y z :=
    adjugateBracket_mono_beta
      (by simpa only [cleanBetaCorner] using hβU.le)
      (betaSecantSlope_pos hβnonpos (by norm_num [cleanBetaCorner])
        hS0 hSu hD0 hf hfu hx hxu hy hyu hz hzu).le
  have h4 :
      adjugateBracket cleanAlphaCorner cleanGammaCorner cleanBetaCorner
          cS cD c44 x y z ≤
        adjugateBracket cleanAlphaCorner cleanGammaCorner cleanBetaCorner
          cleanSCorner cD c44 x y z :=
    adjugateBracket_mono_S_descending
      (by simpa only [cleanSCorner] using hSL.le)
      (sDescendingSlope_pos (by norm_num [cleanAlphaCorner])
        (by norm_num [cleanBetaCorner]) (by norm_num [cleanBetaCorner])
        hS0 (by norm_num [cleanSCorner]) hDL' hDU' hx hxu hy hyu hz hzu).le
  have h5 :
      adjugateBracket cleanAlphaCorner cleanGammaCorner cleanBetaCorner
          cleanSCorner cD c44 x y z ≤
        adjugateBracket cleanAlphaCorner cleanGammaCorner cleanBetaCorner
          cleanSCorner cleanDCorner c44 x y z :=
    adjugateBracket_mono_D_descending
      (by simpa only [cleanDCorner] using hDL.le)
      (dDescendingSlope_pos (by norm_num [cleanGammaCorner])
        (by norm_num [cleanGammaCorner]) (by norm_num [cleanBetaCorner])
        (by norm_num [cleanSCorner]) hDL'
        (by norm_num [cleanDCorner]) hx hxu hy hyu hz hzu).le
  have h6 :
      adjugateBracket cleanAlphaCorner cleanGammaCorner cleanBetaCorner
          cleanSCorner cleanDCorner c44 x y z ≤
        adjugateBracket cleanAlphaCorner cleanGammaCorner cleanBetaCorner
          cleanSCorner cleanDCorner cleanFCorner x y z :=
    adjugateBracket_mono_f (by simpa only [cleanFCorner] using hfu)
      (fSlope_pos (by norm_num [cleanAlphaCorner])
        (by norm_num [cleanGammaCorner]) (by norm_num [cleanBetaCorner])
        (by norm_num [cleanBetaCorner]) hx hxu hy hyu).le
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

private theorem negativeCorner_le_bracket
    {x y z : ℝ}
    (hxL : (56168 / 100000 : ℝ) < x)
    (hxU : x < (56173 / 100000 : ℝ))
    (hyL : (1687 / 100000 : ℝ) < y)
    (hyU : y < (1692 / 100000 : ℝ))
    (hzL : (141 / 1000 : ℝ) < z)
    (hzU : z < (144 / 1000 : ℝ)) :
    adjugateBracket negativeAlphaCorner negativeGammaCorner negativeBetaCorner
        negativeSCorner negativeDCorner negativeFCorner x y z ≤
      adjugateBracket nAlpha nGamma nBeta nS nD n44 x y z := by
  rcases negativeLowCoordinate_lower_bounds with ⟨hα, hγ, hβ⟩
  rcases negativeCrossCoordinate_upper_bounds with ⟨hS, hD⟩
  rcases negativeCoordinate_box with
    ⟨hα0, hγ0, hγu, hβl, hβu, hS0, hSu, hDl, hDu⟩
  have hf := n44_gt
  have hx : (14 / 25 : ℝ) ≤ x := by linarith
  have hxu : x ≤ (57 / 100 : ℝ) := by linarith
  have hy : (2 / 125 : ℝ) ≤ y := by linarith
  have hyu : y ≤ (1 / 50 : ℝ) := by linarith
  have hz : (7 / 50 : ℝ) ≤ z := by linarith
  have hzu : z ≤ (3 / 20 : ℝ) := by linarith
  have h1 :
      adjugateBracket negativeAlphaCorner negativeGammaCorner negativeBetaCorner
          negativeSCorner negativeDCorner negativeFCorner x y z ≤
        adjugateBracket nAlpha negativeGammaCorner negativeBetaCorner
          negativeSCorner negativeDCorner negativeFCorner x y z :=
    adjugateBracket_mono_alpha
      (by simpa only [negativeAlphaCorner] using hα.le)
      (alphaSlope_pos (by norm_num [negativeGammaCorner])
        (by norm_num [negativeSCorner]) (by norm_num [negativeSCorner])
        (by norm_num [negativeFCorner]) (by norm_num [negativeFCorner])
        hx hxu hz hzu).le
  have h2 :
      adjugateBracket nAlpha negativeGammaCorner negativeBetaCorner
          negativeSCorner negativeDCorner negativeFCorner x y z ≤
        adjugateBracket nAlpha nGamma negativeBetaCorner negativeSCorner
          negativeDCorner negativeFCorner x y z :=
    adjugateBracket_mono_gamma
      (by simpa only [negativeGammaCorner] using hγ.le)
      (gammaSlope_nonneg hα0.le (by norm_num [negativeDCorner])
        (by norm_num [negativeFCorner]) (by linarith) (by linarith))
  have h3 :
      adjugateBracket nAlpha nGamma negativeBetaCorner negativeSCorner
          negativeDCorner negativeFCorner x y z ≤
        adjugateBracket nAlpha nGamma nBeta negativeSCorner negativeDCorner
          negativeFCorner x y z :=
    adjugateBracket_mono_beta
      (by simpa only [negativeBetaCorner] using hβ.le)
      (betaSecantSlope_pos (by norm_num [negativeBetaCorner]) hβu.le
        (by norm_num [negativeSCorner]) (by norm_num [negativeSCorner])
        (by norm_num [negativeDCorner]) (by norm_num [negativeFCorner])
        (by norm_num [negativeFCorner]) hx hxu hy hyu hz hzu).le
  have h4 :
      adjugateBracket nAlpha nGamma nBeta negativeSCorner negativeDCorner
          negativeFCorner x y z ≤
        adjugateBracket nAlpha nGamma nBeta nS negativeDCorner
          negativeFCorner x y z :=
    adjugateBracket_mono_S_descending
      (by simpa only [negativeSCorner] using hS.le)
      (sDescendingSlope_pos hα0.le hβl.le hβu.le
        (by norm_num [negativeSCorner]) hS0.le
        (by norm_num [negativeDCorner]) (by norm_num [negativeDCorner])
        hx hxu hy hyu hz hzu).le
  have h5 :
      adjugateBracket nAlpha nGamma nBeta nS negativeDCorner negativeFCorner
          x y z ≤
        adjugateBracket nAlpha nGamma nBeta nS nD negativeFCorner x y z :=
    adjugateBracket_mono_D_descending
      (by simpa only [negativeDCorner] using hD.le)
      (dDescendingSlope_pos hγ0.le hγu.le hβu.le hS0.le
        (by norm_num [negativeDCorner]) hDl.le hx hxu hy hyu hz hzu).le
  have h6 :
      adjugateBracket nAlpha nGamma nBeta nS nD negativeFCorner x y z ≤
        adjugateBracket nAlpha nGamma nBeta nS nD n44 x y z :=
    adjugateBracket_mono_f
      (by simpa only [negativeFCorner] using hf.le)
      (fSlope_pos (by linarith [hα]) hγ0.le
        hβl.le hβu.le hx hxu hy hyu).le
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

private def cornerXX : ℝ :=
  (cleanFCorner * cleanAlphaCorner - cleanDCorner ^ 2) -
    (negativeFCorner * negativeAlphaCorner - negativeDCorner ^ 2)

private def cornerYY : ℝ :=
  (cleanFCorner * cleanGammaCorner - cleanSCorner ^ 2) -
    (negativeFCorner * negativeGammaCorner - negativeSCorner ^ 2)

private def cornerXY : ℝ :=
  (cleanFCorner * cleanBetaCorner - cleanSCorner * cleanDCorner) -
    (negativeFCorner * negativeBetaCorner -
      negativeSCorner * negativeDCorner)

private def cornerXZ : ℝ :=
  (-cleanAlphaCorner * cleanSCorner + cleanBetaCorner * cleanDCorner) -
    (-negativeAlphaCorner * negativeSCorner +
      negativeBetaCorner * negativeDCorner)

private def cornerYZ : ℝ :=
  (-cleanBetaCorner * cleanSCorner + cleanGammaCorner * cleanDCorner) -
    (-negativeBetaCorner * negativeSCorner +
      negativeGammaCorner * negativeDCorner)

private def cornerZZ : ℝ :=
  (cleanAlphaCorner * cleanGammaCorner - cleanBetaCorner ^ 2) -
    (negativeAlphaCorner * negativeGammaCorner - negativeBetaCorner ^ 2)

private def cornerGap (x y z : ℝ) : ℝ :=
  (adjugateBracket cleanAlphaCorner cleanGammaCorner cleanBetaCorner
      cleanSCorner cleanDCorner cleanFCorner x y z -
    adjugateBracket negativeAlphaCorner negativeGammaCorner negativeBetaCorner
      negativeSCorner negativeDCorner negativeFCorner x y z) / 2

private def cornerXSecantSlope (x x' y z : ℝ) : ℝ :=
  cornerXX * (x + x') / 2 + cornerXY * y + cornerXZ * z

private def cornerYSecantSlope (x y y' z : ℝ) : ℝ :=
  cornerYY * (y + y') / 2 + cornerXY * x + cornerYZ * z

private def cornerZSecantSlope (x y z z' : ℝ) : ℝ :=
  cornerXZ * x + cornerYZ * y + cornerZZ * (z + z') / 2

private theorem cornerXSecantSlope_pos
    {x x' y z : ℝ}
    (hxL : (56168 / 100000 : ℝ) ≤ x)
    (_hxU : x ≤ (56173 / 100000 : ℝ))
    (hx'L : (56168 / 100000 : ℝ) ≤ x')
    (_hx'U : x' ≤ (56173 / 100000 : ℝ))
    (_hyL : (1687 / 100000 : ℝ) ≤ y)
    (hyU : y ≤ (1692 / 100000 : ℝ))
    (_hzL : (141 / 1000 : ℝ) ≤ z)
    (hzU : z ≤ (144 / 1000 : ℝ)) :
    0 < cornerXSecantSlope x x' y z := by
  unfold cornerXSecantSlope cornerXX cornerXY cornerXZ
    cleanAlphaCorner cleanBetaCorner cleanSCorner cleanDCorner cleanFCorner
    negativeAlphaCorner negativeBetaCorner negativeSCorner negativeDCorner
    negativeFCorner
  norm_num at hxL hx'L hyU hzU ⊢
  linarith

private theorem cornerYSecantSlope_pos
    {x y y' z : ℝ}
    (_hxL : (56168 / 100000 : ℝ) ≤ x)
    (hxU : x ≤ (56173 / 100000 : ℝ))
    (hyL : (1687 / 100000 : ℝ) ≤ y)
    (_hyU : y ≤ (1692 / 100000 : ℝ))
    (hy'L : (1687 / 100000 : ℝ) ≤ y')
    (_hy'U : y' ≤ (1692 / 100000 : ℝ))
    (hzL : (141 / 1000 : ℝ) ≤ z)
    (_hzU : z ≤ (144 / 1000 : ℝ)) :
    0 < cornerYSecantSlope x y y' z := by
  unfold cornerYSecantSlope cornerYY cornerXY cornerYZ
    cleanGammaCorner cleanBetaCorner cleanSCorner cleanDCorner cleanFCorner
    negativeGammaCorner negativeBetaCorner negativeSCorner negativeDCorner
    negativeFCorner
  norm_num at hxU hyL hy'L hzL ⊢
  linarith

private theorem cornerZSecantSlope_pos
    {x y z z' : ℝ}
    (_hxL : (56168 / 100000 : ℝ) ≤ x)
    (hxU : x ≤ (56173 / 100000 : ℝ))
    (hyL : (1687 / 100000 : ℝ) ≤ y)
    (_hyU : y ≤ (1692 / 100000 : ℝ))
    (hzL : (141 / 1000 : ℝ) ≤ z)
    (_hzU : z ≤ (144 / 1000 : ℝ))
    (hz'L : (141 / 1000 : ℝ) ≤ z')
    (_hz'U : z' ≤ (144 / 1000 : ℝ)) :
    0 < cornerZSecantSlope x y z z' := by
  unfold cornerZSecantSlope cornerXZ cornerYZ cornerZZ
    cleanAlphaCorner cleanGammaCorner cleanBetaCorner cleanSCorner cleanDCorner
    negativeAlphaCorner negativeGammaCorner negativeBetaCorner negativeSCorner
    negativeDCorner
  norm_num at hxU hyL hzL hz'L ⊢
  linarith

private theorem cornerGap_mono_x
    {x x' y z : ℝ} (hx : x ≤ x')
    (hslope : 0 ≤ cornerXSecantSlope x x' y z) :
    cornerGap x y z ≤ cornerGap x' y z := by
  have hid : cornerGap x' y z - cornerGap x y z =
      (x' - x) * cornerXSecantSlope x x' y z := by
    unfold cornerGap cornerXSecantSlope cornerXX cornerXY cornerXZ
      adjugateBracket
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hx) hslope

private theorem cornerGap_mono_y
    {x y y' z : ℝ} (hy : y ≤ y')
    (hslope : 0 ≤ cornerYSecantSlope x y y' z) :
    cornerGap x y z ≤ cornerGap x y' z := by
  have hid : cornerGap x y' z - cornerGap x y z =
      (y' - y) * cornerYSecantSlope x y y' z := by
    unfold cornerGap cornerYSecantSlope cornerYY cornerXY cornerYZ
      adjugateBracket
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hy) hslope

private theorem cornerGap_mono_z
    {x y z z' : ℝ} (hz : z ≤ z')
    (hslope : 0 ≤ cornerZSecantSlope x y z z') :
    cornerGap x y z ≤ cornerGap x y z' := by
  have hid : cornerGap x y z' - cornerGap x y z =
      (z' - z) * cornerZSecantSlope x y z z' := by
    unfold cornerGap cornerZSecantSlope cornerXZ cornerYZ cornerZZ
      adjugateBracket
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hz) hslope

private theorem alternatingAdjugateMixed_lt_four_div_twenty_five_thousand :
    alternatingAdjugateMixed < (4 / 25000 : ℝ) := by
  rcases alternatingCoordinate_bounds with ⟨hxL, hxU, hyL, hyU, hzL, hzU⟩
  have hclean := cleanBracket_le_corner hxL hxU hyL hyU hzL hzU
  have hnegative := negativeCorner_le_bracket hxL hxU hyL hyU hzL hzU
  have hactual : alternatingAdjugateMixed ≤ cornerGap xAlt yAlt a41 := by
    rw [alternatingAdjugateMixed_eq_brackets]
    change
      (adjugateBracket cAlpha cGamma cBeta cS cD c44 xAlt yAlt a41 -
        adjugateBracket nAlpha nGamma nBeta nS nD n44 xAlt yAlt a41) / 2 ≤
          cornerGap xAlt yAlt a41
    unfold cornerGap
    linarith
  have hxStep : cornerGap xAlt yAlt a41 ≤
      cornerGap (56173 / 100000) yAlt a41 :=
    cornerGap_mono_x hxU.le
      (cornerXSecantSlope_pos hxL.le hxU.le
        (by norm_num : (56168 / 100000 : ℝ) ≤ 56173 / 100000)
        (le_refl (56173 / 100000 : ℝ)) hyL.le hyU.le hzL.le hzU.le).le
  have hyStep : cornerGap (56173 / 100000) yAlt a41 ≤
      cornerGap (56173 / 100000) (1692 / 100000) a41 :=
    cornerGap_mono_y hyU.le
      (cornerYSecantSlope_pos
        (by norm_num : (56168 / 100000 : ℝ) ≤ 56173 / 100000)
        (le_refl (56173 / 100000 : ℝ))
        hyL.le hyU.le
        (by norm_num : (1687 / 100000 : ℝ) ≤ 1692 / 100000)
        (le_refl (1692 / 100000 : ℝ)) hzL.le hzU.le).le
  have hzStep :
      cornerGap (56173 / 100000) (1692 / 100000) a41 ≤
        cornerGap (56173 / 100000) (1692 / 100000) (144 / 1000) :=
    cornerGap_mono_z hzU.le
      (cornerZSecantSlope_pos
        (by norm_num : (56168 / 100000 : ℝ) ≤ 56173 / 100000)
        (le_refl (56173 / 100000 : ℝ))
        (by norm_num : (1687 / 100000 : ℝ) ≤ 1692 / 100000)
        (le_refl (1692 / 100000 : ℝ))
        hzL.le hzU.le
        (by norm_num : (141 / 1000 : ℝ) ≤ 144 / 1000)
        (le_refl (144 / 1000 : ℝ))).le
  have hcorner :
      cornerGap (56173 / 100000) (1692 / 100000) (144 / 1000) <
        (4 / 25000 : ℝ) := by
    norm_num [cornerGap, adjugateBracket, cleanAlphaCorner,
      cleanGammaCorner, cleanBetaCorner, cleanSCorner, cleanDCorner,
      cleanFCorner, negativeAlphaCorner, negativeGammaCorner,
      negativeBetaCorner, negativeSCorner, negativeDCorner, negativeFCorner]
  calc
    alternatingAdjugateMixed ≤ cornerGap xAlt yAlt a41 := hactual
    _ ≤ cornerGap (56173 / 100000) yAlt a41 := hxStep
    _ ≤ cornerGap (56173 / 100000) (1692 / 100000) a41 := hyStep
    _ ≤ cornerGap (56173 / 100000) (1692 / 100000) (144 / 1000) := hzStep
    _ < (4 / 25000 : ℝ) := hcorner

private def alternatingAdjugatePlus : ℝ :=
  (e22p * e44p - e24p ^ 2) * a01 ^ 2 +
    2 * (e04p * e24p - e02p * e44p) * a01 * a21 +
    2 * (e02p * e24p - e04p * e22p) * a01 * a41 +
    (e00p * e44p - e04p ^ 2) * a21 ^ 2 +
    2 * (e02p * e04p - e00p * e24p) * a21 * a41 +
    (e00p * e22p - e02p ^ 2) * a41 ^ 2

private def alternatingAdjugateMinus : ℝ :=
  (e22m * e44m - e24m ^ 2) * a01 ^ 2 +
    2 * (e04m * e24m - e02m * e44m) * a01 * a21 +
    2 * (e02m * e24m - e04m * e22m) * a01 * a41 +
    (e00m * e44m - e04m ^ 2) * a21 ^ 2 +
    2 * (e02m * e04m - e00m * e24m) * a21 * a41 +
    (e00m * e22m - e02m ^ 2) * a41 ^ 2

private theorem pivot_polynomial_expansion :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial =
      C evenDetPlus + C evenMixedOne * X + C evenMixedTwo * X ^ 2 +
        C evenDetMinus * X ^ 3 := by
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial evenDetPlus evenMixedOne evenMixedTwo evenDetMinus
    e00p e02p e22p e04p e24p e44p e00m e02m e22m e04m e24m e44m
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

private theorem evenMixedOne_eq_pivotCoeff_one :
    evenMixedOne = pivotCoeff 1 := by
  change evenMixedOne =
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 1
  rw [pivot_polynomial_expansion]
  simp

private theorem evenMixedTwo_eq_pivotCoeff_two :
    evenMixedTwo = pivotCoeff 2 := by
  change evenMixedTwo =
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 2
  rw [pivot_polynomial_expansion]
  simp

private theorem alternating_adjugate_polynomial_expansion :
    coefficientP1AlternatingAdjugatePolynomial =
      C alternatingAdjugatePlus + C alternatingAdjugateMixed * X +
        C alternatingAdjugateMinus * X ^ 2 := by
  unfold coefficientP1AlternatingAdjugatePolynomial
    coefficientLowDetPolynomial coefficientLow00Polynomial
    coefficientLow02Polynomial coefficientLow22Polynomial
    coefficientCross04Polynomial coefficientCross24Polynomial
    coefficientP4DiagonalPolynomial endpointAffinePolynomial
    alternatingAdjugatePlus alternatingAdjugateMixed alternatingAdjugateMinus
    e00p e02p e22p e04p e24p e44p e00m e02m e22m e04m e24m e44m
    a01 a21 a41
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

private theorem coefficient_two_eq_mixed :
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 2 =
      evenMixedOne * o11m + evenMixedTwo * o11p - alternatingAdjugateMixed := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  unfold pivotCoeff p1AlternatingAdjugateCoeff
  rw [pivot_polynomial_expansion, alternating_adjugate_polynomial_expansion]
  simp [coefficientOdd11Polynomial, endpointAffinePolynomial]
  unfold evenMixedOne evenMixedTwo
    e00p e02p e22p e04p e24p e44p e00m e02m e22m e04m e24m e44m
    o11p o11m
  ring

private theorem coefficient_two_pos_of_combined_reserve
    (H : ℝ)
    (hAdj : alternatingAdjugateMixed < H)
    (hReserve : H <
      (157 / 1000 : ℝ) * pivotCoeff 1 +
        (19 / 100 : ℝ) * pivotCoeff 2) :
    0 < factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 2 := by
  have hmixedOne : (157 / 1000 : ℝ) * pivotCoeff 1 <
      pivotCoeff 1 * o11m := by
    calc
      (157 / 1000 : ℝ) * pivotCoeff 1 =
          pivotCoeff 1 * (157 / 1000 : ℝ) := by ring
      _ < pivotCoeff 1 * o11m :=
        mul_lt_mul_of_pos_left o11m_gt pivotCoeff_one_pos
  have hmixedTwo : (19 / 100 : ℝ) * pivotCoeff 2 <
      pivotCoeff 2 * o11p := by
    calc
      (19 / 100 : ℝ) * pivotCoeff 2 =
          pivotCoeff 2 * (19 / 100 : ℝ) := by ring
      _ < pivotCoeff 2 * o11p :=
        mul_lt_mul_of_pos_left o11p_gt pivotCoeff_two_pos
  rw [coefficient_two_eq_mixed, evenMixedOne_eq_pivotCoeff_one,
    evenMixedTwo_eq_pivotCoeff_two]
  linarith

theorem factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_two_nonneg :
    0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 2 := by
  have h1 := pivotCoeff_one_gt_one_div_fifteen_thousand
  have h2 := pivotCoeff_two_gt_four_div_five_thousand
  have hreserve : (4 / 25000 : ℝ) <
      (157 / 1000 : ℝ) * pivotCoeff 1 +
        (19 / 100 : ℝ) * pivotCoeff 2 := by
    norm_num at h1 h2 ⊢
    nlinarith
  exact (coefficient_two_pos_of_combined_reserve (4 / 25000)
    alternatingAdjugateMixed_lt_four_div_twenty_five_thousand hreserve).le

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
