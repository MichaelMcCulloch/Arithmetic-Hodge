import ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.ThreeByThreeSymmetricDeterminantMonotone

open ThreeByThreeRankOneSchur

/-!
# Coordinate monotonicity of a symmetric `3 x 3` determinant

Each result is the exact one-coordinate secant identity for
`symmetricDeterminant`, oriented by the sign of its cofactor or secant slope.
They provide a structural alternative to expanding a determinant over a
parameter box.
-/

/-- The determinant is increasing in `q00` when its complementary principal
minor is nonnegative. -/
theorem symmetricDeterminant_mono_q00
    {q00 q00' q01 q02 q11 q12 q22 : ℝ}
    (hq00 : q00 ≤ q00') (hminor : 0 ≤ q11 * q22 - q12 ^ 2) :
    symmetricDeterminant q00 q01 q02 q11 q12 q22 ≤
      symmetricDeterminant q00' q01 q02 q11 q12 q22 := by
  have hproduct : 0 ≤ (q00' - q00) * (q11 * q22 - q12 ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hq00) hminor
  unfold symmetricDeterminant
  nlinarith

/-- The determinant is increasing in `q11` when its complementary principal
minor is nonnegative. -/
theorem symmetricDeterminant_mono_q11
    {q00 q01 q02 q11 q11' q12 q22 : ℝ}
    (hq11 : q11 ≤ q11') (hminor : 0 ≤ q00 * q22 - q02 ^ 2) :
    symmetricDeterminant q00 q01 q02 q11 q12 q22 ≤
      symmetricDeterminant q00 q01 q02 q11' q12 q22 := by
  have hproduct : 0 ≤ (q11' - q11) * (q00 * q22 - q02 ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hq11) hminor
  unfold symmetricDeterminant
  nlinarith

/-- The determinant is increasing in `q22` when the leading principal minor
is nonnegative. -/
theorem symmetricDeterminant_mono_q22
    {q00 q01 q02 q11 q12 q22 q22' : ℝ}
    (hq22 : q22 ≤ q22') (hminor : 0 ≤ q00 * q11 - q01 ^ 2) :
    symmetricDeterminant q00 q01 q02 q11 q12 q22 ≤
      symmetricDeterminant q00 q01 q02 q11 q12 q22' := by
  have hproduct : 0 ≤ (q22' - q22) * (q00 * q11 - q01 ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hq22) hminor
  unfold symmetricDeterminant
  nlinarith

/-- Increasing `q01` decreases the determinant when its exact secant slope is
nonpositive. -/
theorem symmetricDeterminant_antitone_q01
    {q00 q01 q01' q02 q11 q12 q22 : ℝ}
    (hq01 : q01 ≤ q01')
    (hslope : 2 * q02 * q12 ≤ q22 * (q01 + q01')) :
    symmetricDeterminant q00 q01' q02 q11 q12 q22 ≤
      symmetricDeterminant q00 q01 q02 q11 q12 q22 := by
  have hproduct :
      (q01' - q01) * (2 * q02 * q12 - q22 * (q01 + q01')) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq01) (by linarith)
  unfold symmetricDeterminant
  nlinarith

/-- Increasing `q02` increases the determinant when its exact secant slope is
nonnegative. -/
theorem symmetricDeterminant_mono_q02
    {q00 q01 q02 q02' q11 q12 q22 : ℝ}
    (hq02 : q02 ≤ q02')
    (hslope : q11 * (q02 + q02') ≤ 2 * q01 * q12) :
    symmetricDeterminant q00 q01 q02 q11 q12 q22 ≤
      symmetricDeterminant q00 q01 q02' q11 q12 q22 := by
  have hproduct :
      0 ≤ (q02' - q02) * (2 * q01 * q12 - q11 * (q02 + q02')) :=
    mul_nonneg (sub_nonneg.mpr hq02) (by linarith)
  unfold symmetricDeterminant
  nlinarith

/-- Increasing `q12` decreases the determinant when its exact secant slope is
nonpositive. -/
theorem symmetricDeterminant_antitone_q12
    {q00 q01 q02 q11 q12 q12' q22 : ℝ}
    (hq12 : q12 ≤ q12')
    (hslope : 2 * q01 * q02 ≤ q00 * (q12 + q12')) :
    symmetricDeterminant q00 q01 q02 q11 q12' q22 ≤
      symmetricDeterminant q00 q01 q02 q11 q12 q22 := by
  have hproduct :
      (q12' - q12) * (2 * q01 * q02 - q00 * (q12 + q12')) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq12) (by linarith)
  unfold symmetricDeterminant
  nlinarith

end ArithmeticHodge.Analysis.ThreeByThreeSymmetricDeterminantMonotone
