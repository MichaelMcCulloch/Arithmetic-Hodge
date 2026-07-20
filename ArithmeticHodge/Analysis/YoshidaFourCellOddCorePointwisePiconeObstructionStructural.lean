import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreBlockPiconeStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddCorePointwisePiconeObstructionStructural

noncomputable section

open YoshidaFourCellOddCoreBlockPiconeStructural
open YoshidaFourCellOddCoreGroundStatePiconeStructural
open YoshidaFourCellOddP11RationalRieszGroundProfileStructural
open YoshidaFourCellParityOperatorStructural

/-!
# Pointwise obstruction for the raw--regular Picone row

The diagonal row left by the raw and folded-regular Picone transforms is not
pointwise nonnegative.  The exact rational pair `(x,y) = (1,1/2)` already
forces its first diagonal coefficient to be strictly negative.  This does not
obstruct an integrated argument, where the remaining local diagonal forms can
absorb the row.
-/

/-- Exact value of the rational Riesz ground at the witness point `1/2`. -/
theorem fourCellOddP11RationalRieszGroundProfile_oneHalf :
    fourCellOddP11RationalRieszGroundProfile (1 / 2 : ℝ) =
      1707463597 / 1638400000 := by
  rw [fourCellOddP11RationalRieszGroundProfile_eq_bernstein]
  norm_num

/-- At the witness pair the ground profile is strictly larger at `1/2` than
at `1`. -/
theorem fourCellOddP11RationalRieszGroundProfile_one_lt_oneHalf :
    fourCellOddP11RationalRieszGroundProfile 1 <
      fourCellOddP11RationalRieszGroundProfile (1 / 2 : ℝ) := by
  rw [fourCellOddP11RationalRieszGroundProfile_one,
    fourCellOddP11RationalRieszGroundProfile_oneHalf]
  norm_num

/-- The first raw--regular Picone diagonal coefficient is already strictly
negative at the exact rational pair `(1,1/2)`. -/
theorem rationalRieszRawRegularDiagonalCoefficientX_one_oneHalf_neg :
    rationalRieszRawRegularDiagonalCoefficientX 1 (1 / 2 : ℝ) < 0 := by
  have hqOne :
      0 < fourCellOddP11RationalRieszGroundProfile (1 : ℝ) :=
    fourCellOddP11RationalRieszGroundProfile_pos (by norm_num) (by norm_num)
  have hqSub :
      fourCellOddP11RationalRieszGroundProfile (1 : ℝ) -
          fourCellOddP11RationalRieszGroundProfile (1 / 2 : ℝ) < 0 :=
    sub_neg.mpr fourCellOddP11RationalRieszGroundProfile_one_lt_oneHalf
  have hkernel :
      0 ≤ fourCellOddFoldedRegularDifferenceKernel 1 (1 / 2 : ℝ) :=
    fourCellOddFoldedRegularDifferenceKernel_nonneg
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hwidth : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hregular :
      0 ≤ fourCellOperatorHalfWidth *
        fourCellOddFoldedRegularDifferenceKernel 1 (1 / 2 : ℝ) :=
    mul_nonneg hwidth hkernel
  have hrawWeight :
      positiveHalfSameReserveWeight 1 (1 / 2 : ℝ) +
          positiveHalfReflectedReserveWeight 1 (1 / 2 : ℝ) = 4 / 3 := by
    norm_num [positiveHalfSameReserveWeight,
      positiveHalfReflectedReserveWeight, abs_of_nonneg]
  have hrawTerm :
      (4 / 3 : ℝ) *
          (fourCellOddP11RationalRieszGroundProfile 1 -
            fourCellOddP11RationalRieszGroundProfile (1 / 2 : ℝ)) /
          fourCellOddP11RationalRieszGroundProfile 1 < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hqSub) hqOne
  have hregularTerm :
      fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel 1 (1 / 2 : ℝ) *
          (fourCellOddP11RationalRieszGroundProfile 1 -
            fourCellOddP11RationalRieszGroundProfile (1 / 2 : ℝ)) /
          fourCellOddP11RationalRieszGroundProfile 1 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hregular hqSub.le) hqOne.le
  unfold rationalRieszRawRegularDiagonalCoefficientX
  rw [hrawWeight]
  nlinarith

/-- Consequently the deliberately pointwise sufficient row condition fails
at the same exact pair. -/
theorem not_rationalRieszRawRegularPointwiseRowCondition_one_oneHalf :
    ¬ RationalRieszRawRegularPointwiseRowCondition 1 (1 / 2 : ℝ) := by
  intro hrow
  exact (not_lt_of_ge hrow.1)
    rationalRieszRawRegularDiagonalCoefficientX_one_oneHalf_neg

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddCorePointwisePiconeObstructionStructural
