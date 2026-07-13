import ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhTailWeight

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhTailWeightRational

open YoshidaEndpointEvenAtanhTailWeight

noncomputable section

/-- Cubic denominator polynomial of the transformed two-term tail weight. -/
def atanhTailWeightDenominatorPolynomial (z : ℝ) : ℝ :=
  39 * z ^ 3 + 6 * z ^ 2 - 252 * z + 328

/-- Exact rational form after `z=x²` and `t=z/(2-z)`. -/
theorem yoshidaEndpointEvenAtanhTailWeight_eq_rational
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    yoshidaEndpointEvenAtanhTailWeight x =
      atanhTailWeightDenominatorPolynomial (x ^ 2) /
        (60 * (2 - x ^ 2) ^ 3) := by
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
  have hden : 2 - x ^ 2 ≠ 0 := by linarith
  unfold yoshidaEndpointEvenAtanhTailWeight
    YoshidaEndpointPotentialAtanhLower.yoshidaEndpointPotentialAtanhTwoTerm
    atanhTailWeightDenominatorPolynomial
  dsimp only
  field_simp [hden]
  ring

theorem atanhTailWeightDenominatorPolynomial_pos
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    0 < atanhTailWeightDenominatorPolynomial (x ^ 2) := by
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
  have hbase : 0 < 2 - x ^ 2 := by linarith
  have hden : 0 < 60 * (2 - x ^ 2) ^ 3 := by positivity
  have hweight := yoshidaEndpointEvenAtanhTailWeight_pos_on_Icc hx
  rw [yoshidaEndpointEvenAtanhTailWeight_eq_rational hx] at hweight
  calc
    0 < (atanhTailWeightDenominatorPolynomial (x ^ 2) /
        (60 * (2 - x ^ 2) ^ 3)) * (60 * (2 - x ^ 2) ^ 3) :=
      mul_pos hweight hden
    _ = atanhTailWeightDenominatorPolynomial (x ^ 2) := by
      field_simp [hden.ne']

/-- The reciprocal is a positive cubic rational function on the full closed
interval, ready for a fixed polynomial majorant. -/
theorem inv_yoshidaEndpointEvenAtanhTailWeight_eq_rational
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    (yoshidaEndpointEvenAtanhTailWeight x)⁻¹ =
      60 * (2 - x ^ 2) ^ 3 /
        atanhTailWeightDenominatorPolynomial (x ^ 2) := by
  rw [yoshidaEndpointEvenAtanhTailWeight_eq_rational hx]
  have hnum := atanhTailWeightDenominatorPolynomial_pos hx |>.ne'
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
  have hbase : 0 < 2 - x ^ 2 := by linarith
  have hden : 60 * (2 - x ^ 2) ^ 3 ≠ 0 := by positivity
  field_simp [hnum, hden]

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhTailWeightRational
