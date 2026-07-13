import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.FixedTwoModeQuadratic

/-!
# A fixed two-mode quadratic comparison

This is the scalar completion used after the structural low/tail Schur
reduction.  It is independent of any matrix enumeration or certificate.
-/

theorem nonneg_of_fixed_comparison
    {s11 s13 s33 a b : ℝ}
    (h11 : (1 / 16 : ℝ) ≤ s11)
    (h13 : |s13| ≤ (7 / 60 : ℝ))
    (h33 : (11 / 48 : ℝ) ≤ s33) :
    0 ≤ s11 * a ^ 2 + 2 * s13 * a * b + s33 * b ^ 2 := by
  have hab0 : 0 ≤ |a| * |b| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsab : |s13 * a * b| ≤ (7 / 60 : ℝ) * (|a| * |b|) := by
    rw [abs_mul, abs_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h13 hab0
  have hcross :
      -(7 / 30 : ℝ) * (|a| * |b|) ≤ 2 * s13 * a * b := by
    have hneg := neg_abs_le (s13 * a * b)
    nlinarith
  have hdiag1 : (1 / 16 : ℝ) * a ^ 2 ≤ s11 * a ^ 2 :=
    mul_le_mul_of_nonneg_right h11 (sq_nonneg a)
  have hdiag3 : (11 / 48 : ℝ) * b ^ 2 ≤ s33 * b ^ 2 :=
    mul_le_mul_of_nonneg_right h33 (sq_nonneg b)
  have hsquare : 0 ≤ (|a| / 4 - (7 / 15 : ℝ) * |b|) ^ 2 := sq_nonneg _
  have haSq : |a| ^ 2 = a ^ 2 := sq_abs a
  have hbSq : |b| ^ 2 = b ^ 2 := sq_abs b
  nlinarith

end ArithmeticHodge.Analysis.FixedTwoModeQuadratic
