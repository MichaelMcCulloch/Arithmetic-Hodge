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

/-- A six-coordinate lower telescope for a symmetric `3 x 3` determinant.

The lower matrix has smaller diagonal and long-cross coordinates, and larger
adjacent-cross coordinates.  The hypotheses are exactly the cofactor and
secant signs at the stage where the corresponding coordinate is moved.  This
packages a structural comparison with one rational matrix without expanding
the determinant over a coordinate box. -/
theorem symmetricDeterminant_corner_le_of_six_coordinate_telescope
    {a b c d e f A B C D E F : ℝ}
    (hA : a ≤ A) (hB : B ≤ b) (hC : c ≤ C)
    (hD : d ≤ D) (hE : E ≤ e) (hF : f ≤ F)
    (hminor00 : 0 ≤ d * f - e ^ 2)
    (hslope01 : 2 * c * e ≤ f * (B + b))
    (hslope02 : d * (c + C) ≤ 2 * B * e)
    (hminor11 : 0 ≤ A * f - C ^ 2)
    (hslope12 : 2 * B * C ≤ A * (E + e))
    (hminor22 : 0 ≤ A * D - B ^ 2) :
    symmetricDeterminant a b c d e f ≤
      symmetricDeterminant A B C D E F := by
  calc
    symmetricDeterminant a b c d e f ≤
        symmetricDeterminant A b c d e f :=
      symmetricDeterminant_mono_q00 hA hminor00
    _ ≤ symmetricDeterminant A B c d e f :=
      symmetricDeterminant_antitone_q01 hB hslope01
    _ ≤ symmetricDeterminant A B C d e f :=
      symmetricDeterminant_mono_q02 hC hslope02
    _ ≤ symmetricDeterminant A B C D e f :=
      symmetricDeterminant_mono_q11 hD hminor11
    _ ≤ symmetricDeterminant A B C D E f :=
      symmetricDeterminant_antitone_q12 hE hslope12
    _ ≤ symmetricDeterminant A B C D E F :=
      symmetricDeterminant_mono_q22 hF hminor22

end ArithmeticHodge.Analysis.ThreeByThreeSymmetricDeterminantMonotone
