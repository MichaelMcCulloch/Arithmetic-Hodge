import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural

noncomputable section

open Polynomial
open YoshidaEndpointOcticPotential
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

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
