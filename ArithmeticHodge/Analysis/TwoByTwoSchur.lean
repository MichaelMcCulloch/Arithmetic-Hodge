import Mathlib

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.TwoByTwoSchur

/-- A positive `2 × 2` low block plus a tail stays nonnegative when the two
low-to-tail functionals satisfy the exact adjugate Schur bound. -/
theorem quadratic_add_tail_nonneg
    (q00 q02 q22 ell0 ell2 tail c b : ℝ)
    (hq00 : 0 < q00)
    (hdet : 0 < q00 * q22 - q02 ^ 2)
    (hschur :
      q22 * ell0 ^ 2 - 2 * q02 * ell0 * ell2 + q00 * ell2 ^ 2 ≤
        (q00 * q22 - q02 ^ 2) * tail) :
    0 ≤ q00 * c ^ 2 + 2 * q02 * c * b + q22 * b ^ 2 +
      2 * c * ell0 + 2 * b * ell2 + tail := by
  let det : ℝ := q00 * q22 - q02 ^ 2
  let Q : ℝ := q00 * c ^ 2 + 2 * q02 * c * b + q22 * b ^ 2 +
    2 * c * ell0 + 2 * b * ell2 + tail
  have hdet' : 0 < det := by simpa only [det] using hdet
  have hrem : 0 ≤ det * tail -
      (q22 * ell0 ^ 2 - 2 * q02 * ell0 * ell2 + q00 * ell2 ^ 2) := by
    dsimp only [det]
    linarith
  have hid :
      q00 * det * Q =
        det * (q00 * c + q02 * b + ell0) ^ 2 +
          (det * b + q00 * ell2 - q02 * ell0) ^ 2 +
          q00 * (det * tail -
            (q22 * ell0 ^ 2 - 2 * q02 * ell0 * ell2 +
              q00 * ell2 ^ 2)) := by
    dsimp only [det, Q]
    ring
  have hscaled : 0 ≤ q00 * det * Q := by
    rw [hid]
    positivity
  have hfactor : 0 < q00 * det := mul_pos hq00 hdet'
  have hQ : 0 ≤ Q := nonneg_of_mul_nonneg_right hscaled hfactor
  simpa only [Q] using hQ

end ArithmeticHodge.Analysis.TwoByTwoSchur
