import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreBlockPiconeStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddCoreOffStripRegularAbsorptionStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaFourCellOddCoreBlockPiconeStructural
open YoshidaFourCellOddCoreGroundStatePiconeStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Pointwise absorption of the folded regular cross

The complete positive-half raw reserve absorbs the signed folded-regular
cross pointwise.  The proof uses the two raw channels together: the reflected
plus-square alone pays for every positive cross, while a negative cross is
already favorable.  This remains valid on the totalized diagonal `x = y`, so
no artificial off-diagonal case is needed.
-/

/-! ## Reusable two-channel algebra -/

/-- A subtraction cross of size at most twice the plus-square weight is
absorbed by the two nonnegative difference/plus channels.  No comparison
between the two channel weights is required. -/
theorem twoChannelSquares_sub_cross_nonneg
    {kSub kAdd c wX wY : ℝ}
    (hkSub : 0 ≤ kSub) (hkAdd : 0 ≤ kAdd)
    (hc : 0 ≤ c) (hcap : c ≤ 2 * kAdd) :
    0 ≤ kSub * (wX - wY) ^ 2 + kAdd * (wX + wY) ^ 2 -
      2 * c * wX * wY := by
  by_cases hcross : 0 ≤ wX * wY
  · have hcapScaled : c * (wX * wY) ≤
        (2 * kAdd) * (wX * wY) :=
      mul_le_mul_of_nonneg_right hcap hcross
    have hsquare : 4 * (wX * wY) ≤ (wX + wY) ^ 2 := by
      nlinarith [sq_nonneg (wX - wY)]
    have hsquareScaled : kAdd * (4 * (wX * wY)) ≤
        kAdd * (wX + wY) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hkAdd
    have hsubSquare : 0 ≤ kSub * (wX - wY) ^ 2 :=
      mul_nonneg hkSub (sq_nonneg _)
    nlinarith
  · have hcross' : wX * wY ≤ 0 := le_of_not_ge hcross
    have hregular : c * (wX * wY) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc hcross'
    have hsubSquare : 0 ≤ kSub * (wX - wY) ^ 2 :=
      mul_nonneg hkSub (sq_nonneg _)
    have haddSquare : 0 ≤ kAdd * (wX + wY) ^ 2 :=
      mul_nonneg hkAdd (sq_nonneg _)
    nlinarith

/-- If the subtraction cross is at most half of the plus-square weight, then
the combined form retains at least three quarters of the original two-channel
energy. -/
theorem threeFourths_mul_twoChannelSquares_le_sub_cross
    {kSub kAdd c wX wY : ℝ}
    (hkSub : 0 ≤ kSub) (hkAdd : 0 ≤ kAdd)
    (hc : 0 ≤ c) (hcap : c ≤ kAdd / 2) :
    (3 / 4 : ℝ) *
        (kSub * (wX - wY) ^ 2 + kAdd * (wX + wY) ^ 2) ≤
      kSub * (wX - wY) ^ 2 + kAdd * (wX + wY) ^ 2 -
        2 * c * wX * wY := by
  by_cases hcross : 0 ≤ wX * wY
  · have hcapScaled : c * (wX * wY) ≤
        (kAdd / 2) * (wX * wY) :=
      mul_le_mul_of_nonneg_right hcap hcross
    have hsquare : 4 * (wX * wY) ≤ (wX + wY) ^ 2 := by
      nlinarith [sq_nonneg (wX - wY)]
    have hsquareScaled : kAdd * (4 * (wX * wY)) ≤
        kAdd * (wX + wY) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hkAdd
    have hsubSquare : 0 ≤ kSub * (wX - wY) ^ 2 :=
      mul_nonneg hkSub (sq_nonneg _)
    nlinarith
  · have hcross' : wX * wY ≤ 0 := le_of_not_ge hcross
    have hregular : c * (wX * wY) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc hcross'
    have hsubSquare : 0 ≤ kSub * (wX - wY) ^ 2 :=
      mul_nonneg hkSub (sq_nonneg _)
    have haddSquare : 0 ≤ kAdd * (wX + wY) ^ 2 :=
      mul_nonneg hkAdd (sq_nonneg _)
    nlinarith

/-! ## Kernel bounds -/

/-- The folded regular difference never exceeds the removable value `1/4`
on the complete positive half-square. -/
theorem fourCellOddFoldedRegularDifferenceKernel_le_quarter
    {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    fourCellOddFoldedRegularDifferenceKernel x y ≤ 1 / 4 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hwidth : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hdistArg : 0 ≤ fourCellOperatorHalfWidth * |x - y| :=
    mul_nonneg hwidth (abs_nonneg _)
  have hsumArg : 0 ≤ fourCellOperatorHalfWidth * (x + y) :=
    mul_nonneg hwidth (add_nonneg hx.le hy.le)
  have hsum : x + y ≤ 2 := by linarith
  have hsumArgUpper :
      fourCellOperatorHalfWidth * (x + y) ≤ 5 * Real.log 2 / 4 := by
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hsameUpper := yoshidaRegularKernel_le_quarter hdistArg
  have hreflectedNonneg := yoshidaRegularKernel_nonneg_fourCellRange
    hsumArg hsumArgUpper
  unfold fourCellOddFoldedRegularDifferenceKernel
  linarith

/-- The scaled folded regular kernel is much smaller than twice the reflected
raw reserve weight.  The constants are deliberately loose: the scaled kernel
is at most `1/4`, whereas twice the reflected weight is at least `1/2`. -/
theorem fourCellOperatorHalfWidth_mul_foldedRegularDifferenceKernel_le_two_reflected
    {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    fourCellOperatorHalfWidth *
        fourCellOddFoldedRegularDifferenceKernel x y ≤
      2 * positiveHalfReflectedReserveWeight x y := by
  have hkernel :
      0 ≤ fourCellOddFoldedRegularDifferenceKernel x y :=
    fourCellOddFoldedRegularDifferenceKernel_nonneg hx.le hx1 hy.le hy1
  have hkernelUpper :
      fourCellOddFoldedRegularDifferenceKernel x y ≤ 1 / 4 :=
    fourCellOddFoldedRegularDifferenceKernel_le_quarter hx hx1 hy hy1
  have hwidthLe : fourCellOperatorHalfWidth ≤ 1 := by
    have hlogUpper := strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hscaledUpper :
      fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y ≤ 1 / 4 := by
    calc
      fourCellOperatorHalfWidth *
            fourCellOddFoldedRegularDifferenceKernel x y ≤
          1 * fourCellOddFoldedRegularDifferenceKernel x y :=
        mul_le_mul_of_nonneg_right hwidthLe hkernel
      _ ≤ 1 * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hkernelUpper (by norm_num)
      _ = 1 / 4 := by ring
  have hsumPos : 0 < x + y := add_pos hx hy
  have hsumUpper : x + y ≤ 2 := by linarith
  have hinvLower : (1 / 2 : ℝ) ≤ 1 / (x + y) :=
    one_div_le_one_div_of_le hsumPos hsumUpper
  have hreflected :
      2 * positiveHalfReflectedReserveWeight x y = 1 / (x + y) := by
    unfold positiveHalfReflectedReserveWeight
    field_simp [hsumPos.ne']
  rw [hreflected]
  linarith

/-- Quantitative strengthening for retention: the scaled regular difference
costs at most half of the reflected raw channel. -/
theorem fourCellOperatorHalfWidth_mul_foldedRegularDifferenceKernel_le_half_reflected
    {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    fourCellOperatorHalfWidth *
        fourCellOddFoldedRegularDifferenceKernel x y ≤
      positiveHalfReflectedReserveWeight x y / 2 := by
  have hkernel :
      0 ≤ fourCellOddFoldedRegularDifferenceKernel x y :=
    fourCellOddFoldedRegularDifferenceKernel_nonneg hx.le hx1 hy.le hy1
  have hkernelUpper :
      fourCellOddFoldedRegularDifferenceKernel x y ≤ 1 / 4 :=
    fourCellOddFoldedRegularDifferenceKernel_le_quarter hx hx1 hy hy1
  have hwidthLe : fourCellOperatorHalfWidth ≤ 1 / 2 := by
    have hlogUpper := strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hscaledUpper :
      fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y ≤ 1 / 8 := by
    calc
      fourCellOperatorHalfWidth *
            fourCellOddFoldedRegularDifferenceKernel x y ≤
          (1 / 2 : ℝ) * fourCellOddFoldedRegularDifferenceKernel x y :=
        mul_le_mul_of_nonneg_right hwidthLe hkernel
      _ ≤ (1 / 2 : ℝ) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hkernelUpper (by norm_num)
      _ = 1 / 8 := by ring
  have hsumPos : 0 < x + y := add_pos hx hy
  have hdenPos : 0 < 2 * (x + y) := mul_pos (by norm_num) hsumPos
  have hdenUpper : 2 * (x + y) ≤ 4 := by linarith
  have hreflectedLower :
      (1 / 4 : ℝ) ≤ positiveHalfReflectedReserveWeight x y := by
    unfold positiveHalfReflectedReserveWeight
    exact one_div_le_one_div_of_le hdenPos hdenUpper
  linarith

/-! ## Raw absorption -/

/-- The unconditional pointwise off-strip estimate: the complete raw reserve
absorbs the signed folded-regular cross for every pair in `(0,1]`. -/
theorem positiveHalfRawReservePair_sub_foldedRegularCross_nonneg
    {x y wX wY : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    0 ≤ positiveHalfRawReservePair x y wX wY -
      2 * fourCellOperatorHalfWidth *
        fourCellOddFoldedRegularDifferenceKernel x y * wX * wY := by
  have hkSub : 0 ≤ positiveHalfSameReserveWeight x y :=
    positiveHalfSameReserveWeight_nonneg x y
  have hkAdd : 0 ≤ positiveHalfReflectedReserveWeight x y :=
    (positiveHalfReflectedReserveWeight_pos hx hy).le
  have hkernel :
      0 ≤ fourCellOddFoldedRegularDifferenceKernel x y :=
    fourCellOddFoldedRegularDifferenceKernel_nonneg hx.le hx1 hy.le hy1
  have hwidth : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hc :
      0 ≤ fourCellOperatorHalfWidth *
        fourCellOddFoldedRegularDifferenceKernel x y :=
    mul_nonneg hwidth hkernel
  have hcap :=
    fourCellOperatorHalfWidth_mul_foldedRegularDifferenceKernel_le_two_reflected
      hx hx1 hy hy1
  simpa only [positiveHalfRawReservePair, mul_assoc] using
    (twoChannelSquares_sub_cross_nonneg
      (kSub := positiveHalfSameReserveWeight x y)
      (kAdd := positiveHalfReflectedReserveWeight x y)
      (c := fourCellOperatorHalfWidth *
        fourCellOddFoldedRegularDifferenceKernel x y)
      (wX := wX) (wY := wY) hkSub hkAdd hc hcap)

/-- Quantitative pointwise absorption: at least three quarters of the complete
positive-half raw reserve remains after paying the folded-regular cross. -/
theorem threeFourths_mul_positiveHalfRawReservePair_le_sub_foldedRegularCross
    {x y wX wY : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    (3 / 4 : ℝ) * positiveHalfRawReservePair x y wX wY ≤
      positiveHalfRawReservePair x y wX wY -
        2 * fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel x y * wX * wY := by
  have hkSub : 0 ≤ positiveHalfSameReserveWeight x y :=
    positiveHalfSameReserveWeight_nonneg x y
  have hkAdd : 0 ≤ positiveHalfReflectedReserveWeight x y :=
    (positiveHalfReflectedReserveWeight_pos hx hy).le
  have hkernel :
      0 ≤ fourCellOddFoldedRegularDifferenceKernel x y :=
    fourCellOddFoldedRegularDifferenceKernel_nonneg hx.le hx1 hy.le hy1
  have hwidth : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hc :
      0 ≤ fourCellOperatorHalfWidth *
        fourCellOddFoldedRegularDifferenceKernel x y :=
    mul_nonneg hwidth hkernel
  have hcap :=
    fourCellOperatorHalfWidth_mul_foldedRegularDifferenceKernel_le_half_reflected
      hx hx1 hy hy1
  simpa only [positiveHalfRawReservePair, mul_assoc] using
    (threeFourths_mul_twoChannelSquares_le_sub_cross
      (kSub := positiveHalfSameReserveWeight x y)
      (kAdd := positiveHalfReflectedReserveWeight x y)
      (c := fourCellOperatorHalfWidth *
        fourCellOddFoldedRegularDifferenceKernel x y)
      (wX := wX) (wY := wY) hkSub hkAdd hc hcap)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddCoreOffStripRegularAbsorptionStructural
