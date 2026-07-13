import ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhTailWeightRational

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhReciprocalMajorant

open YoshidaEndpointEvenAtanhTailWeight
open YoshidaEndpointEvenAtanhTailWeightRational

noncomputable section

/-- Degree-three polynomial in `y=x²` which structurally majorizes the
reciprocal transformed tail weight. -/
def atanhTailWeightReciprocalMajorantPolynomial (y : ℝ) : ℝ :=
  (60 / 41 : ℝ) - (1800 / 1681 : ℝ) * y +
    (17100 / 68921 : ℝ) * y ^ 2 - (18 / 125 : ℝ) * y ^ 3

def atanhTailWeightReciprocalMajorant (x : ℝ) : ℝ :=
  atanhTailWeightReciprocalMajorantPolynomial (x ^ 2)

private def reciprocalMajorantBernsteinRemainder (y : ℝ) : ℝ :=
  7690416 * (1 - y) ^ 5 +
    4127736 * y * (1 - y) ^ 4 +
    15525816 * y ^ 2 * (1 - y) ^ 3 +
    50332650 * y ^ 3 * (1 - y) ^ 2 +
    32146716 * y ^ 4 * (1 - y) +
    902562 * y ^ 5

/-- The reciprocal majorant follows from one exact factorization with a
manifestly nonnegative Bernstein-form remainder. -/
theorem inv_atanhTailWeight_le_reciprocalMajorant
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    (yoshidaEndpointEvenAtanhTailWeight x)⁻¹ ≤
      atanhTailWeightReciprocalMajorant x := by
  let y : ℝ := x ^ 2
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    positivity
  have hy1 : y ≤ 1 := by
    dsimp only [y]
    exact (sq_le_one_iff_abs_le_one x).2 hxAbs
  have htwo : 0 < 2 - y := by linarith
  have hNidentity :
      atanhTailWeightDenominatorPolynomial y =
        41 * (2 - y) ^ 3 + 60 * y * (2 - y) ^ 2 + 20 * y ^ 3 := by
    unfold atanhTailWeightDenominatorPolynomial
    ring
  have hNpos : 0 < atanhTailWeightDenominatorPolynomial y := by
    rw [hNidentity]
    positivity
  have hBnonneg : 0 ≤ reciprocalMajorantBernsteinRemainder y := by
    unfold reciprocalMajorantBernsteinRemainder
    have hone : 0 ≤ 1 - y := by linarith
    positivity
  have hfactor :
      (8615125 : ℝ) *
          (atanhTailWeightDenominatorPolynomial y *
              atanhTailWeightReciprocalMajorantPolynomial y -
            60 * (2 - y) ^ 3) =
        y ^ 3 * reciprocalMajorantBernsteinRemainder y := by
    unfold atanhTailWeightDenominatorPolynomial
      atanhTailWeightReciprocalMajorantPolynomial
      reciprocalMajorantBernsteinRemainder
    ring
  have hdiff :
      0 ≤ atanhTailWeightDenominatorPolynomial y *
          atanhTailWeightReciprocalMajorantPolynomial y -
        60 * (2 - y) ^ 3 := by
    have hrhs : 0 ≤ y ^ 3 * reciprocalMajorantBernsteinRemainder y :=
      mul_nonneg (by positivity) hBnonneg
    nlinarith
  rw [inv_yoshidaEndpointEvenAtanhTailWeight_eq_rational hx]
  unfold atanhTailWeightReciprocalMajorant
  dsimp only [y] at hNpos hdiff ⊢
  rw [div_le_iff₀ hNpos]
  nlinarith

theorem sq_div_atanhTailWeight_le_majorant_mul_sq
    (h : ℝ) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    h ^ 2 / yoshidaEndpointEvenAtanhTailWeight x ≤
      atanhTailWeightReciprocalMajorant x * h ^ 2 := by
  rw [div_eq_mul_inv]
  have hbound := inv_atanhTailWeight_le_reciprocalMajorant hx
  have hscaled := mul_le_mul_of_nonneg_left hbound (sq_nonneg h)
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhReciprocalMajorant
