import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhLoewnerStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhRationalStructural

noncomputable section

open YoshidaEndpointPotentialAtanhLower
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhLoewnerStructural

/-!
# Rational form of the direct retained-weight atanh lower bound

Writing `y = x²`, the exact retained mass and potential slope combine with
the two-term transformed atanh lower bound into one cubic numerator over the
positive denominator `800 (2-y)³`.
-/

/-- Cubic numerator of the direct retained-even two-term atanh weight. -/
def directP6RetainedEvenAtanhNumerator (y : ℝ) : ℝ :=
  421 * y ^ 3 - 951 * y ^ 2 + 327 * y + 832

/-- Exact rational form of the direct two-term atanh retained weight. -/
theorem directP6RetainedEvenAtanhTwoTermWeight_eq_rational
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    directP6RetainedEvenAtanhTwoTermWeight x =
      directP6RetainedEvenAtanhNumerator (x ^ 2) /
        (800 * (2 - x ^ 2) ^ 3) := by
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
  have hden : 2 - x ^ 2 ≠ 0 := by linarith
  unfold directP6RetainedEvenAtanhTwoTermWeight
    yoshidaEndpointPotentialAtanhTwoTerm
    directP6RetainedEvenAtanhNumerator
  dsimp only
  field_simp [hden]
  ring

/-- The cubic numerator is strictly positive throughout the physical
interval.  This follows structurally from positivity of the direct weight
and its positive rational denominator. -/
theorem directP6RetainedEvenAtanhNumerator_pos_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < directP6RetainedEvenAtanhNumerator (x ^ 2) := by
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
  have hbase : 0 < 2 - x ^ 2 := by linarith
  have hden : 0 < 800 * (2 - x ^ 2) ^ 3 := by positivity
  have hweight := directP6RetainedEvenAtanhTwoTermWeight_pos_on_Icc hx
  rw [directP6RetainedEvenAtanhTwoTermWeight_eq_rational hx] at hweight
  calc
    0 < (directP6RetainedEvenAtanhNumerator (x ^ 2) /
        (800 * (2 - x ^ 2) ^ 3)) *
          (800 * (2 - x ^ 2) ^ 3) := mul_pos hweight hden
    _ = directP6RetainedEvenAtanhNumerator (x ^ 2) := by
      field_simp [hden.ne']

/-- Equivalent positivity surface in the squared coordinate `y ∈ [0,1]`.
The displayed factorization gives the stronger lower bound `629 ≤ N(y)`. -/
theorem directP6RetainedEvenAtanhNumerator_pos_on_unitInterval
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 < directP6RetainedEvenAtanhNumerator y := by
  have hlinear : 0 ≤ 530 - 421 * y := by linarith [hy.2]
  have hquadratic : 0 ≤ -421 * y ^ 2 + 530 * y + 203 := by
    nlinarith [mul_nonneg hy.1 hlinear]
  have hfactor := mul_nonneg (sub_nonneg.mpr hy.2) hquadratic
  unfold directP6RetainedEvenAtanhNumerator
  nlinarith

/-- Exact rational reciprocal used by the direct atanh multiplier Gram. -/
theorem inv_directP6RetainedEvenAtanhTwoTermWeight_eq_rational
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (directP6RetainedEvenAtanhTwoTermWeight x)⁻¹ =
      800 * (2 - x ^ 2) ^ 3 /
        directP6RetainedEvenAtanhNumerator (x ^ 2) := by
  rw [directP6RetainedEvenAtanhTwoTermWeight_eq_rational hx]
  have hnum := directP6RetainedEvenAtanhNumerator_pos_on_Icc hx |>.ne'
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
  have hbase : 0 < 2 - x ^ 2 := by linarith
  have hden : 800 * (2 - x ^ 2) ^ 3 ≠ 0 := by positivity
  field_simp [hnum, hden]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhRationalStructural
