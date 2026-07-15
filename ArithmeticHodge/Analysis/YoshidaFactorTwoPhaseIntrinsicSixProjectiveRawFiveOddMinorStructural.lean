import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural

noncomputable section

open Polynomial
open YoshidaConstantBounds
open YoshidaEndpointOcticPotential
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddFullPolarization
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural

/-!
# The mixed odd endpoint determinant

The middle coefficient of the affine `P₁/P₃` determinant is positive for
the invariant reason that it is the mixed determinant of the two positive
endpoint forms.  The scalar lemma below records the two-dimensional argument
without entrywise numerical estimates.
-/

/-- The mixed determinant of two positive-definite symmetric `2 × 2` forms
is strictly positive. -/
theorem twoByTwoMixedDeterminant_pos
    {a b d A B D : ℝ}
    (ha : 0 < a) (hdet : 0 < a * d - b ^ 2)
    (hA : 0 < A) (hDet : 0 < A * D - B ^ 2) :
    0 < a * D + A * d - 2 * b * B := by
  have hd : 0 < d := by nlinarith [sq_nonneg b]
  have hD : 0 < D := by nlinarith [sq_nonneg B]
  have had : 0 < a * d := mul_pos ha hd
  have hAD : 0 < A * D := mul_pos hA hD
  have hb : b ^ 2 < a * d := by linarith
  have hB : B ^ 2 < A * D := by linarith
  have hproduct : (b * B) ^ 2 < (a * D) * (A * d) := by
    calc
      (b * B) ^ 2 = b ^ 2 * B ^ 2 := by ring
      _ ≤ (a * d) * B ^ 2 :=
        mul_le_mul_of_nonneg_right hb.le (sq_nonneg B)
      _ < (a * d) * (A * D) :=
        mul_lt_mul_of_pos_left hB had
      _ = (a * D) * (A * d) := by ring
  have hsum : 0 < a * D + A * d :=
    add_pos (mul_pos ha hD) (mul_pos hA hd)
  have hsquare : (2 * b * B) ^ 2 < (a * D + A * d) ^ 2 := by
    nlinarith [sq_nonneg (a * D - A * d)]
  by_cases hcross : 0 ≤ b * B
  · by_contra hnonpos
    have hle : a * D + A * d ≤ 2 * b * B := by linarith
    have hplus : 0 ≤ 2 * b * B + (a * D + A * d) := by linarith
    have hsquareLe : (a * D + A * d) ^ 2 ≤ (2 * b * B) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) hplus]
    linarith
  · have hcrossNeg : b * B < 0 := lt_of_not_ge hcross
    nlinarith

/-- Exact mixed coefficient of the affine odd endpoint determinant. -/
theorem rawFiveOddMinorCoeff_one_eq :
    rawFiveOddMinorCoeff 1 =
      factorTwoIntrinsicOddPhaseLow11 1 *
          factorTwoIntrinsicOddPhaseLow33 (-1) +
        factorTwoIntrinsicOddPhaseLow11 (-1) *
          factorTwoIntrinsicOddPhaseLow33 1 -
        2 * factorTwoIntrinsicOddPhaseLow13 1 *
          factorTwoIntrinsicOddPhaseLow13 (-1) := by
  change factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff 1 = _
  have hpoly :
      factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial =
        C (factorTwoIntrinsicOddPhaseLow11 1 *
              factorTwoIntrinsicOddPhaseLow33 1 -
            factorTwoIntrinsicOddPhaseLow13 1 ^ 2) +
          C (factorTwoIntrinsicOddPhaseLow11 1 *
                factorTwoIntrinsicOddPhaseLow33 (-1) +
              factorTwoIntrinsicOddPhaseLow11 (-1) *
                factorTwoIntrinsicOddPhaseLow33 1 -
              2 * factorTwoIntrinsicOddPhaseLow13 1 *
                factorTwoIntrinsicOddPhaseLow13 (-1)) * X +
          C (factorTwoIntrinsicOddPhaseLow11 (-1) *
                factorTwoIntrinsicOddPhaseLow33 (-1) -
              factorTwoIntrinsicOddPhaseLow13 (-1) ^ 2) * X ^ 2 := by
    unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
      coefficientOdd11Polynomial coefficientOdd13Polynomial
      coefficientOdd33Polynomial endpointAffinePolynomial
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

/-- The genuinely mixed coefficient of the odd `P₁/P₃` determinant is
strictly positive. -/
theorem rawFiveOddMinorCoeff_one_pos :
    0 < rawFiveOddMinorCoeff 1 := by
  rw [rawFiveOddMinorCoeff_one_eq]
  rcases oddStructuralLow_endpoint_gates with
    ⟨hp11, hpdet, hm11, hmdet⟩
  apply twoByTwoMixedDeterminant_pos
  · simpa [factorTwoIntrinsicOddPhaseLow11,
      YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11] using hp11
  · simpa [factorTwoIntrinsicOddPhaseLow11,
      factorTwoIntrinsicOddPhaseLow13, factorTwoIntrinsicOddPhaseLow33,
      YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11,
      YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow13,
      YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow33] using hpdet
  · simpa [factorTwoIntrinsicOddPhaseLow11,
      YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11] using hm11
  · simpa [factorTwoIntrinsicOddPhaseLow11,
      factorTwoIntrinsicOddPhaseLow13, factorTwoIntrinsicOddPhaseLow33,
      YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow11,
      YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow13,
      YoshidaFactorTwoPhaseOddLowSchur.factorTwoOddStructuralPhaseLow33] using hmdet

/-- Quantitative form of the mixed odd determinant reserve.  Polarizing the
two endpoints cancels the clean--perturbation cross terms; the perturbation
determinant is negative, while the clean determinant has a direct rational
Schur margin. -/
theorem rawFiveOddMinorCoeff_one_gt_one_div_twenty_five :
    (1 / 25 : ℝ) < rawFiveOddMinorCoeff 1 := by
  let c11 : ℝ := yoshidaEndpointOddLowGram11
  let c13 : ℝ := yoshidaEndpointOddLowGram13
  let c33 : ℝ := yoshidaEndpointOddLowGram33
  let p11 : ℝ := factorTwoCenteredSymmetricPerturbation centeredP1
  let p13 : ℝ :=
    factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3
  let p33 : ℝ := factorTwoCenteredSymmetricPerturbation centeredP3
  have heq : rawFiveOddMinorCoeff 1 =
      2 * ((c11 * c33 - c13 ^ 2) - (p11 * p33 - p13 ^ 2)) := by
    rw [rawFiveOddMinorCoeff_one_eq]
    unfold factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
      factorTwoIntrinsicOddPhaseLow33
    dsimp only [c11, c13, c33, p11, p13, p33]
    ring
  have hc11 : (1778 / 10000 : ℝ) < c11 := by
    simpa only [c11] using yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hc33 : (3315 / 10000 : ℝ) < c33 := by
    simpa only [c33] using yoshidaEndpointOddLowGram33_gt_3315_div_10000
  have hc13 : (1 / 5 : ℝ) < c13 ∧ c13 < 2002 / 10000 := by
    simpa only [c13] using yoshidaEndpointOddLowGram13_bounds
  have hc11pos : 0 < c11 := lt_trans (by norm_num) hc11
  have hcleanProduct :
      (1778 / 10000 : ℝ) * (3315 / 10000) < c11 * c33 := by
    calc
      (1778 / 10000 : ℝ) * (3315 / 10000) <
          c11 * (3315 / 10000) :=
        mul_lt_mul_of_pos_right hc11 (by norm_num)
      _ < c11 * c33 := mul_lt_mul_of_pos_left hc33 hc11pos
  have hc13pos : 0 < c13 := lt_trans (by norm_num) hc13.1
  have hcrossSum : 0 < (2002 / 10000 : ℝ) + c13 :=
    add_pos (by norm_num) hc13pos
  have hcleanCross : c13 ^ 2 < (2002 / 10000 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hc13.2) hcrossSum]
  rcases oddStructuralLow_perturbation_sharp_bounds with
    ⟨hp11, _hp13, hp33⟩
  have hp11pos : 0 < p11 := by
    dsimp only [p11]
    linarith [hp11.1]
  have hp33neg : p33 < 0 := by
    dsimp only [p33]
    linarith [hp33.2]
  have hpertProduct :
      p11 * p33 < (14 / 1000 : ℝ) * (-117 / 1000) := by
    calc
      p11 * p33 < p11 * (-117 / 1000 : ℝ) :=
        mul_lt_mul_of_pos_left hp33.2 hp11pos
      _ < (14 / 1000 : ℝ) * (-117 / 1000) :=
        mul_lt_mul_of_neg_right hp11.1 (by norm_num)
  have hpertDetUpper :
      p11 * p33 - p13 ^ 2 < (14 / 1000 : ℝ) * (-117 / 1000) := by
    nlinarith [sq_nonneg p13]
  rw [heq]
  norm_num at hcleanProduct hcleanCross hpertDetUpper ⊢
  nlinarith

/-- A slightly weaker denominator retained for callers that only need the
original quantitative reserve. -/
theorem rawFiveOddMinorCoeff_one_gt_three_div_eighty :
    (3 / 80 : ℝ) < rawFiveOddMinorCoeff 1 := by
  linarith [rawFiveOddMinorCoeff_one_gt_one_div_twenty_five]

/-! ## Quantitative endpoint boxes -/

private theorem rawFive_scalarMassLoss_gt :
    (13552 / 10000 : ℝ) < yoshidaEndpointScalarMassLoss := by
  have hsplit : Real.log (Real.pi * Real.log 2) =
      Real.log Real.pi + Real.log (Real.log 2) := by
    rw [Real.log_mul Real.pi_pos.ne'
      (Real.log_pos (by norm_num)).ne']
  unfold yoshidaEndpointScalarMassLoss
  rw [hsplit]
  linarith [strict_euler_gamma_bounds.1, strict_log_pi_bounds.1,
    strict_log_log_two_bounds.1]

private theorem rawFive_endpointA_pow_fine_bounds (n : ℕ) (hn : n ≠ 0) :
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

private theorem oddCleanRegularTotal11_gt_six_thousandths :
    (3 / 500 : ℝ) <
      oddCleanRegularPolynomialGram11 +
        oddCleanRegularEnvelopeError oddStructuralCorrelation11 := by
  have h1 := rawFive_endpointA_pow_fine_bounds 1 (by norm_num)
  have h2 := rawFive_endpointA_pow_fine_bounds 2 (by norm_num)
  have h3 := rawFive_endpointA_pow_fine_bounds 3 (by norm_num)
  have h4 := rawFive_endpointA_pow_fine_bounds 4 (by norm_num)
  have h5 := rawFive_endpointA_pow_fine_bounds 5 (by norm_num)
  have h6 := rawFive_endpointA_pow_fine_bounds 6 (by norm_num)
  have hpoly :
      (61 / 10000 : ℝ) < oddCleanRegularPolynomialGram11 := by
    unfold oddCleanRegularPolynomialGram11
    nlinarith [pow_nonneg yoshidaEndpointA_pos.le 3,
      pow_nonneg yoshidaEndpointA_pos.le 4]
  have herr := abs_oddCleanRegularEnvelopeError11_le
  have herrLower := neg_abs_le
    (oddCleanRegularEnvelopeError oddStructuralCorrelation11)
  nlinarith

private theorem oddCleanRegularTotal33_pos :
    0 < oddCleanRegularPolynomialGram33 +
      oddCleanRegularEnvelopeError oddStructuralCorrelation33 := by
  have h1 := rawFive_endpointA_pow_fine_bounds 1 (by norm_num)
  have hpoly :
      (1 / 10000 : ℝ) < oddCleanRegularPolynomialGram33 := by
    unfold oddCleanRegularPolynomialGram33
    nlinarith [pow_nonneg yoshidaEndpointA_pos.le 3,
      pow_nonneg yoshidaEndpointA_pos.le 5,
      pow_nonneg yoshidaEndpointA_pos.le 6]
  have herr := abs_oddCleanRegularEnvelopeError33_le
  have herrLower := neg_abs_le
    (oddCleanRegularEnvelopeError oddStructuralCorrelation33)
  nlinarith

/-- Structural upper boxes complementing the sharp clean diagonal lower
bounds used in the mixed determinant proof. -/
theorem yoshidaEndpointOddLowGram_diagonal_upper_bounds :
    yoshidaEndpointOddLowGram11 < (179 / 1000 : ℝ) ∧
      yoshidaEndpointOddLowGram33 < (333 / 1000 : ℝ) := by
  have hA :
      (69314718055 / 200000000000 : ℝ) < yoshidaEndpointA := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.1]
  have hlog := strict_log_two_fine_bounds.1
  have hmass := rawFive_scalarMassLoss_gt
  constructor
  · rw [yoshidaEndpointOddLowGram11_structural_eq]
    let R : ℝ := oddCleanRegularPolynomialGram11 +
      oddCleanRegularEnvelopeError oddStructuralCorrelation11
    have hR : (3 / 500 : ℝ) < R := by
      simpa only [R] using oddCleanRegularTotal11_gt_six_thousandths
    have hreg : (1 / 500 : ℝ) < yoshidaEndpointA * R := by
      calc
        (1 / 500 : ℝ) <
            (69314718055 / 200000000000 : ℝ) * (3 / 500) := by
          norm_num
        _ < yoshidaEndpointA * (3 / 500 : ℝ) :=
          mul_lt_mul_of_pos_right hA (by norm_num)
        _ < yoshidaEndpointA * R :=
          mul_lt_mul_of_pos_left hR yoshidaEndpointA_pos
    have hm := oddCleanSinhMoment1_gt
    have hmpos : 0 < oddCleanSinhMoment1 :=
      lt_trans (by norm_num) hm
    have hmsq :
        (11587142 / 100000000 : ℝ) ^ 2 <
          oddCleanSinhMoment1 ^ 2 := by
      nlinarith [sq_nonneg
        (oddCleanSinhMoment1 - (11587142 / 100000000 : ℝ))]
    have hhyper :
        (9 / 1000 : ℝ) <
          2 * yoshidaEndpointA * oddCleanSinhMoment1 ^ 2 := by
      calc
        (9 / 1000 : ℝ) <
            (2 * (69314718055 / 200000000000 : ℝ)) *
              (11587142 / 100000000 : ℝ) ^ 2 := by
          norm_num
        _ < (2 * yoshidaEndpointA) *
              (11587142 / 100000000 : ℝ) ^ 2 :=
          mul_lt_mul_of_pos_right (by linarith) (by positivity)
        _ < (2 * yoshidaEndpointA) * oddCleanSinhMoment1 ^ 2 :=
          mul_lt_mul_of_pos_left hmsq
            (mul_pos (by norm_num) yoshidaEndpointA_pos)
    dsimp only [R] at hreg
    nlinarith
  · rw [yoshidaEndpointOddLowGram33_structural_eq]
    let R : ℝ := oddCleanRegularPolynomialGram33 +
      oddCleanRegularEnvelopeError oddStructuralCorrelation33
    have hR : 0 < R := by
      simpa only [R] using oddCleanRegularTotal33_pos
    have hreg : 0 < yoshidaEndpointA * R :=
      mul_pos yoshidaEndpointA_pos hR
    have hhyper :
        0 ≤ 2 * yoshidaEndpointA * oddCleanSinhMoment3 ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le)
        (sq_nonneg _)
    dsimp only [R] at hreg
    nlinarith

/-- Tight entry boxes for the positive odd endpoint. -/
theorem factorTwoIntrinsicOddPhaseLow_plus_entry_bounds :
    (1918 / 10000 : ℝ) < factorTwoIntrinsicOddPhaseLow11 1 ∧
      factorTwoIntrinsicOddPhaseLow11 1 < (199 / 1000 : ℝ) ∧
      (189 / 1000 : ℝ) < factorTwoIntrinsicOddPhaseLow13 1 ∧
      factorTwoIntrinsicOddPhaseLow13 1 < (1912 / 10000 : ℝ) ∧
      (2115 / 10000 : ℝ) < factorTwoIntrinsicOddPhaseLow33 1 ∧
      factorTwoIntrinsicOddPhaseLow33 1 < (216 / 1000 : ℝ) := by
  have hc11L := yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hc33L := yoshidaEndpointOddLowGram33_gt_3315_div_10000
  have hcU := yoshidaEndpointOddLowGram_diagonal_upper_bounds
  have hc13 := yoshidaEndpointOddLowGram13_bounds
  rcases oddStructuralLow_perturbation_sharp_bounds with
    ⟨hp11, hp13, hp33⟩
  unfold factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
  norm_num
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Tight entry boxes for the negative odd endpoint. -/
theorem factorTwoIntrinsicOddPhaseLow_minus_entry_bounds :
    (1578 / 10000 : ℝ) < factorTwoIntrinsicOddPhaseLow11 (-1) ∧
      factorTwoIntrinsicOddPhaseLow11 (-1) < (165 / 1000 : ℝ) ∧
      (209 / 1000 : ℝ) < factorTwoIntrinsicOddPhaseLow13 (-1) ∧
      factorTwoIntrinsicOddPhaseLow13 (-1) < (2112 / 10000 : ℝ) ∧
      (4485 / 10000 : ℝ) < factorTwoIntrinsicOddPhaseLow33 (-1) ∧
      factorTwoIntrinsicOddPhaseLow33 (-1) < (453 / 1000 : ℝ) := by
  have hc11L := yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hc33L := yoshidaEndpointOddLowGram33_gt_3315_div_10000
  have hcU := yoshidaEndpointOddLowGram_diagonal_upper_bounds
  have hc13 := yoshidaEndpointOddLowGram13_bounds
  rcases oddStructuralLow_perturbation_sharp_bounds with
    ⟨hp11, hp13, hp33⟩
  unfold factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
  norm_num
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The positive odd endpoint minor retains a quantitative Schur margin. -/
theorem factorTwoIntrinsicOddPhaseLow_plus_minor_gt_one_div_two_fifty :
    (1 / 250 : ℝ) <
      factorTwoIntrinsicOddPhaseLow11 1 *
          factorTwoIntrinsicOddPhaseLow33 1 -
        factorTwoIntrinsicOddPhaseLow13 1 ^ 2 := by
  rcases factorTwoIntrinsicOddPhaseLow_plus_entry_bounds with
    ⟨h11L, _h11U, h13L, h13U, h33L, _h33U⟩
  have h11pos : 0 < factorTwoIntrinsicOddPhaseLow11 1 :=
    lt_trans (by norm_num) h11L
  have h13pos : 0 < factorTwoIntrinsicOddPhaseLow13 1 :=
    lt_trans (by norm_num) h13L
  have hprod :
      (1918 / 10000 : ℝ) * (2115 / 10000) <
        factorTwoIntrinsicOddPhaseLow11 1 *
          factorTwoIntrinsicOddPhaseLow33 1 := by
    calc
      (1918 / 10000 : ℝ) * (2115 / 10000) <
          factorTwoIntrinsicOddPhaseLow11 1 * (2115 / 10000) :=
        mul_lt_mul_of_pos_right h11L (by norm_num)
      _ < factorTwoIntrinsicOddPhaseLow11 1 *
            factorTwoIntrinsicOddPhaseLow33 1 :=
        mul_lt_mul_of_pos_left h33L h11pos
  have hcrossSum :
      0 < (1912 / 10000 : ℝ) + factorTwoIntrinsicOddPhaseLow13 1 :=
    add_pos (by norm_num) h13pos
  have hcross :
      factorTwoIntrinsicOddPhaseLow13 1 ^ 2 <
        (1912 / 10000 : ℝ) ^ 2 := by
    nlinarith [mul_pos
      (sub_pos.mpr h13U) hcrossSum]
  norm_num at hprod hcross ⊢
  nlinarith

/-- The negative odd endpoint minor has a larger quantitative Schur margin. -/
theorem factorTwoIntrinsicOddPhaseLow_minus_minor_gt_one_div_forty :
    (1 / 40 : ℝ) <
      factorTwoIntrinsicOddPhaseLow11 (-1) *
          factorTwoIntrinsicOddPhaseLow33 (-1) -
        factorTwoIntrinsicOddPhaseLow13 (-1) ^ 2 := by
  rcases factorTwoIntrinsicOddPhaseLow_minus_entry_bounds with
    ⟨h11L, _h11U, h13L, h13U, h33L, _h33U⟩
  have h11pos : 0 < factorTwoIntrinsicOddPhaseLow11 (-1) :=
    lt_trans (by norm_num) h11L
  have h13pos : 0 < factorTwoIntrinsicOddPhaseLow13 (-1) :=
    lt_trans (by norm_num) h13L
  have hprod :
      (1578 / 10000 : ℝ) * (4485 / 10000) <
        factorTwoIntrinsicOddPhaseLow11 (-1) *
          factorTwoIntrinsicOddPhaseLow33 (-1) := by
    calc
      (1578 / 10000 : ℝ) * (4485 / 10000) <
          factorTwoIntrinsicOddPhaseLow11 (-1) * (4485 / 10000) :=
        mul_lt_mul_of_pos_right h11L (by norm_num)
      _ < factorTwoIntrinsicOddPhaseLow11 (-1) *
            factorTwoIntrinsicOddPhaseLow33 (-1) :=
        mul_lt_mul_of_pos_left h33L h11pos
  have hcrossSum :
      0 < (2112 / 10000 : ℝ) + factorTwoIntrinsicOddPhaseLow13 (-1) :=
    add_pos (by norm_num) h13pos
  have hcross :
      factorTwoIntrinsicOddPhaseLow13 (-1) ^ 2 <
        (2112 / 10000 : ℝ) ^ 2 := by
    nlinarith [mul_pos
      (sub_pos.mpr h13U) hcrossSum]
  norm_num at hprod hcross ⊢
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
