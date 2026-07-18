import Mathlib

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.AffineWeightQuotient

/-!
# Exact division by an affine singular weight

These identities extract the polynomial part of a residual of the form
`slope * V * p + h` before division by `mass + slope * V`.  The remaining
quotient contains the shifted remainder `h - mass * p`; no estimate enters.
-/

/-- Polarized affine-weight division.  This is the bilinear form of the
square extraction used by retained residual Gram matrices. -/
theorem mul_div_affine_weight_decomposition
    (V mass slope p q h k : ℝ)
    (hne : mass + slope * V ≠ 0) :
    (slope * V * p + h) * (slope * V * q + k) /
        (mass + slope * V) =
      slope * V * p * q + p * k + q * h - mass * p * q +
        (h - mass * p) * (k - mass * q) /
          (mass + slope * V) := by
  field_simp [hne]
  ring

/-- Square specialization of polarized affine-weight division. -/
theorem sq_div_affine_weight_decomposition
    (V mass slope p h : ℝ)
    (hne : mass + slope * V ≠ 0) :
    (slope * V * p + h) ^ 2 / (mass + slope * V) =
      slope * V * p ^ 2 + 2 * p * h - mass * p ^ 2 +
        (h - mass * p) ^ 2 / (mass + slope * V) := by
  field_simp [hne]
  ring

end ArithmeticHodge.Analysis.AffineWeightQuotient
