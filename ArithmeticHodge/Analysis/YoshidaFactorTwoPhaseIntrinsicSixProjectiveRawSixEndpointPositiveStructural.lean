import ArithmeticHodge.Analysis.ThreeByThreeSymmetricDeterminantMonotone
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOddPencilStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixEndpointPositiveStructural

noncomputable section

open Matrix
open ThreeByThreeRankOneSchur
open ThreeByThreeSymmetricDeterminantMonotone
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixOddPencilStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur

/-!
# Structural positivity of the raw-six odd endpoint matrices

The two endpoint determinants are compared with one rational matrix each.
The comparison is a six-coordinate telescope: diagonal entries move upward,
the adjacent crosses move downward, and the long cross moves upward.  Each
step uses its exact cofactor or secant sign; no determinant box is expanded
over corners.
-/

/-! ## Plus endpoint -/

/-- The plus-endpoint determinant retains a strict rational margin. -/
theorem one_div_two_million_lt_rawSixOddPlusMatrix_det :
    (1 / 2000000 : ℝ) < rawSixOddPlusMatrix.det := by
  let A : ℝ := factorTwoIntrinsicOddPhaseLow11 1
  let B : ℝ := factorTwoIntrinsicOddPhaseLow13 1
  let C : ℝ := factorTwoIntrinsicFourP45Cross15 1
  let D : ℝ := factorTwoIntrinsicOddPhaseLow33 1
  let E : ℝ := factorTwoIntrinsicFourP45Cross35 1
  let F : ℝ := factorTwoIntrinsicSixP5Diagonal 1
  let a : ℝ := 1918 / 10000
  let b : ℝ := 1912 / 10000
  let c : ℝ := 131727 / 1000000
  let d : ℝ := 2115 / 10000
  let e : ℝ := 172427 / 1000000
  let f : ℝ := 343 / 2000
  rcases factorTwoIntrinsicOddPhaseLow_plus_entry_bounds with
    ⟨hA, _hAUpper, hBLower, hBUpper, hD, _hDUpper⟩
  rcases factorTwoIntrinsicFourP45Cross15_one_bounds with
    ⟨hC, hCUpper⟩
  rcases factorTwoIntrinsicFourP45Cross35_one_bounds with
    ⟨hELower, hEUpper⟩
  have hF := three_hundred_forty_three_two_thousandths_lt_p5_plus
  change a < A at hA
  change (189 / 1000 : ℝ) < B at hBLower
  change B < b at hBUpper
  change c < C at hC
  change C < (131929 / 1000000 : ℝ) at hCUpper
  change d < D at hD
  change (172324 / 1000000 : ℝ) < E at hELower
  change E < e at hEUpper
  change f < F at hF
  have hApos : 0 < A := lt_trans (by norm_num [a]) hA
  have hCpos : 0 < C := lt_trans (by norm_num [c]) hC
  have hminor00 : 0 ≤ d * f - e ^ 2 := by
    norm_num [d, e, f]
  have hslope01 : 2 * c * e ≤ f * (B + b) := by
    calc
      2 * c * e ≤ f * ((189 / 1000 : ℝ) + b) := by
        norm_num [b, c, e, f]
      _ ≤ f * (B + b) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num [f])
        linarith
  have hslope02 : d * (c + C) ≤ 2 * B * e := by
    calc
      d * (c + C) ≤ d * (c + (131929 / 1000000 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num [d])
        linarith
      _ ≤ 2 * (189 / 1000 : ℝ) * e := by
        norm_num [c, d, e]
      _ = (2 * e) * (189 / 1000 : ℝ) := by ring
      _ ≤ (2 * e) * B := by
        exact mul_le_mul_of_nonneg_left hBLower.le (by norm_num [e])
      _ = 2 * B * e := by ring
  have hAf : a * f ≤ A * f :=
    mul_le_mul_of_nonneg_right hA.le (by norm_num [f])
  have hCsq : C ^ 2 ≤ (131929 / 1000000 : ℝ) ^ 2 := by
    have hproduct : 0 ≤
        ((131929 / 1000000 : ℝ) - C) *
          ((131929 / 1000000 : ℝ) + C) :=
      mul_nonneg (sub_nonneg.mpr hCUpper.le)
        (add_nonneg (by norm_num) hCpos.le)
    nlinarith
  have hminor11 : 0 ≤ A * f - C ^ 2 := by
    have hcorner : 0 ≤
        a * f - (131929 / 1000000 : ℝ) ^ 2 := by
      norm_num [a, f]
    calc
      0 ≤ a * f - (131929 / 1000000 : ℝ) ^ 2 := hcorner
      _ ≤ A * f - (131929 / 1000000 : ℝ) ^ 2 :=
        sub_le_sub_right hAf _
      _ ≤ A * f - C ^ 2 := sub_le_sub_left hCsq _
  have hBC₁ : B * C ≤ b * C :=
    mul_le_mul_of_nonneg_right hBUpper.le hCpos.le
  have hBC₂ : b * C ≤ b * (131929 / 1000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hCUpper.le (by norm_num [b])
  have hBC : B * C ≤ b * (131929 / 1000000 : ℝ) :=
    hBC₁.trans hBC₂
  have hEside :
      (172324 / 1000000 : ℝ) + e ≤ E + e := by
    linarith
  have hslope12 : 2 * B * C ≤ A * (E + e) := by
    calc
      2 * B * C ≤ 2 * (b * (131929 / 1000000 : ℝ)) := by
        nlinarith
      _ ≤ a * ((172324 / 1000000 : ℝ) + e) := by
        norm_num [a, b, e]
      _ ≤ A * ((172324 / 1000000 : ℝ) + e) := by
        exact mul_le_mul_of_nonneg_right hA.le (by norm_num [e])
      _ ≤ A * (E + e) :=
        mul_le_mul_of_nonneg_left hEside hApos.le
  have hminor22 : 0 ≤ A * D - B ^ 2 := by
    have hminor :=
      factorTwoIntrinsicOddPhaseLow_plus_minor_gt_one_div_two_fifty
    change (1 / 250 : ℝ) < A * D - B ^ 2 at hminor
    linarith
  have hcorner_le :
      symmetricDeterminant a b c d e f ≤
        symmetricDeterminant A B C D E F :=
    symmetricDeterminant_corner_le_of_six_coordinate_telescope
      hA.le hBUpper.le hC.le hD.le hEUpper.le hF.le
      hminor00 hslope01 hslope02 hminor11 hslope12 hminor22
  have hcorner :
      (1 / 2000000 : ℝ) < symmetricDeterminant a b c d e f := by
    norm_num [symmetricDeterminant, a, b, c, d, e, f]
  have hdetEq :
      rawSixOddPlusMatrix.det = symmetricDeterminant A B C D E F := by
    simpa only [rawSixOddPlusMatrix, A, B, C, D, E, F] using
      rawSixOddEndpointMatrix_det_eq_symmetricDeterminant 1
  calc
    (1 / 2000000 : ℝ) < symmetricDeterminant a b c d e f := hcorner
    _ ≤ symmetricDeterminant A B C D E F := hcorner_le
    _ = rawSixOddPlusMatrix.det := hdetEq.symm

/-! ## Minus endpoint -/

/-- The minus-endpoint determinant retains the larger rational margin. -/
theorem three_div_five_hundred_lt_rawSixOddMinusMatrix_det :
    (3 / 500 : ℝ) < rawSixOddMinusMatrix.det := by
  let A : ℝ := factorTwoIntrinsicOddPhaseLow11 (-1)
  let B : ℝ := factorTwoIntrinsicOddPhaseLow13 (-1)
  let C : ℝ := factorTwoIntrinsicFourP45Cross15 (-1)
  let D : ℝ := factorTwoIntrinsicOddPhaseLow33 (-1)
  let E : ℝ := factorTwoIntrinsicFourP45Cross35 (-1)
  let F : ℝ := factorTwoIntrinsicSixP5Diagonal (-1)
  let a : ℝ := 1578 / 10000
  let b : ℝ := 2112 / 10000
  let c : ℝ := 10927 / 1000000
  let d : ℝ := 4485 / 10000
  let e : ℝ := 49927 / 1000000
  let f : ℝ := 14 / 55
  rcases factorTwoIntrinsicOddPhaseLow_minus_entry_bounds with
    ⟨hA, _hAUpper, hBLower, hBUpper, hD, _hDUpper⟩
  rcases factorTwoIntrinsicFourP45Cross15_neg_one_bounds with
    ⟨hC, hCUpper⟩
  rcases factorTwoIntrinsicFourP45Cross35_neg_one_bounds with
    ⟨hELower, hEUpper⟩
  have hF := fourteen_fifty_fifths_lt_p5_minus
  change a < A at hA
  change (209 / 1000 : ℝ) < B at hBLower
  change B < b at hBUpper
  change c < C at hC
  change C < (11129 / 1000000 : ℝ) at hCUpper
  change d < D at hD
  change (49824 / 1000000 : ℝ) < E at hELower
  change E < e at hEUpper
  change f < F at hF
  have hApos : 0 < A := lt_trans (by norm_num [a]) hA
  have hCpos : 0 < C := lt_trans (by norm_num [c]) hC
  have hminor00 : 0 ≤ d * f - e ^ 2 := by
    norm_num [d, e, f]
  have hslope01 : 2 * c * e ≤ f * (B + b) := by
    calc
      2 * c * e ≤ f * ((209 / 1000 : ℝ) + b) := by
        norm_num [b, c, e, f]
      _ ≤ f * (B + b) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num [f])
        linarith
  have hslope02 : d * (c + C) ≤ 2 * B * e := by
    calc
      d * (c + C) ≤ d * (c + (11129 / 1000000 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num [d])
        linarith
      _ ≤ 2 * (209 / 1000 : ℝ) * e := by
        norm_num [c, d, e]
      _ = (2 * e) * (209 / 1000 : ℝ) := by ring
      _ ≤ (2 * e) * B := by
        exact mul_le_mul_of_nonneg_left hBLower.le (by norm_num [e])
      _ = 2 * B * e := by ring
  have hAf : a * f ≤ A * f :=
    mul_le_mul_of_nonneg_right hA.le (by norm_num [f])
  have hCsq : C ^ 2 ≤ (11129 / 1000000 : ℝ) ^ 2 := by
    have hproduct : 0 ≤
        ((11129 / 1000000 : ℝ) - C) *
          ((11129 / 1000000 : ℝ) + C) :=
      mul_nonneg (sub_nonneg.mpr hCUpper.le)
        (add_nonneg (by norm_num) hCpos.le)
    nlinarith
  have hminor11 : 0 ≤ A * f - C ^ 2 := by
    have hcorner : 0 ≤
        a * f - (11129 / 1000000 : ℝ) ^ 2 := by
      norm_num [a, f]
    calc
      0 ≤ a * f - (11129 / 1000000 : ℝ) ^ 2 := hcorner
      _ ≤ A * f - (11129 / 1000000 : ℝ) ^ 2 :=
        sub_le_sub_right hAf _
      _ ≤ A * f - C ^ 2 := sub_le_sub_left hCsq _
  have hBC₁ : B * C ≤ b * C :=
    mul_le_mul_of_nonneg_right hBUpper.le hCpos.le
  have hBC₂ : b * C ≤ b * (11129 / 1000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hCUpper.le (by norm_num [b])
  have hBC : B * C ≤ b * (11129 / 1000000 : ℝ) :=
    hBC₁.trans hBC₂
  have hEside :
      (49824 / 1000000 : ℝ) + e ≤ E + e := by
    linarith
  have hslope12 : 2 * B * C ≤ A * (E + e) := by
    calc
      2 * B * C ≤ 2 * (b * (11129 / 1000000 : ℝ)) := by
        nlinarith
      _ ≤ a * ((49824 / 1000000 : ℝ) + e) := by
        norm_num [a, b, e]
      _ ≤ A * ((49824 / 1000000 : ℝ) + e) := by
        exact mul_le_mul_of_nonneg_right hA.le (by norm_num [e])
      _ ≤ A * (E + e) :=
        mul_le_mul_of_nonneg_left hEside hApos.le
  have hminor22 : 0 ≤ A * D - B ^ 2 := by
    have hminor :=
      factorTwoIntrinsicOddPhaseLow_minus_minor_gt_one_div_forty
    change (1 / 40 : ℝ) < A * D - B ^ 2 at hminor
    linarith
  have hcorner_le :
      symmetricDeterminant a b c d e f ≤
        symmetricDeterminant A B C D E F :=
    symmetricDeterminant_corner_le_of_six_coordinate_telescope
      hA.le hBUpper.le hC.le hD.le hEUpper.le hF.le
      hminor00 hslope01 hslope02 hminor11 hslope12 hminor22
  have hcorner :
      (3 / 500 : ℝ) < symmetricDeterminant a b c d e f := by
    norm_num [symmetricDeterminant, a, b, c, d, e, f]
  have hdetEq :
      rawSixOddMinusMatrix.det = symmetricDeterminant A B C D E F := by
    simpa only [rawSixOddMinusMatrix, A, B, C, D, E, F] using
      rawSixOddEndpointMatrix_det_eq_symmetricDeterminant (-1)
  calc
    (3 / 500 : ℝ) < symmetricDeterminant a b c d e f := hcorner
    _ ≤ symmetricDeterminant A B C D E F := hcorner_le
    _ = rawSixOddMinusMatrix.det := hdetEq.symm

/-! ## Endpoint positive definiteness -/

theorem rawSixOddPlusMatrix_posDef : rawSixOddPlusMatrix.PosDef := by
  rw [rawSixOddPlusMatrix_posDef_iff_det_pos]
  exact lt_trans (by norm_num)
    one_div_two_million_lt_rawSixOddPlusMatrix_det

theorem rawSixOddMinusMatrix_posDef : rawSixOddMinusMatrix.PosDef := by
  rw [rawSixOddMinusMatrix_posDef_iff_det_pos]
  exact lt_trans (by norm_num)
    three_div_five_hundred_lt_rawSixOddMinusMatrix_det

theorem rawSixOddEndpointMatrices_posDef :
    rawSixOddPlusMatrix.PosDef ∧ rawSixOddMinusMatrix.PosDef :=
  ⟨rawSixOddPlusMatrix_posDef, rawSixOddMinusMatrix_posDef⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixEndpointPositiveStructural
