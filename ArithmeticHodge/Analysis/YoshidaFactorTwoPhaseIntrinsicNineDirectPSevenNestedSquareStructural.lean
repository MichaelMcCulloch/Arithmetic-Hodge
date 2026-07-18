import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenNestedSquareStructural

noncomputable section

open Polynomial
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural

/-!
# Nested-square certificate for the seventh direct prefix

The first prefix beyond the proved six-mode core has degree seven.  Instead
of assigning its two negative-looking coefficients to arbitrarily chosen
quadratic heads, eliminate them successively by exact square completion.
The remaining obstruction is a cubic tail with manifestly nonnegative
coefficients on the projective half-line.
-/

/-- Exact denominator-free form of the two successive square completions.
This formulation avoids divisions and remains convenient for exact scalar
enclosures. -/
theorem degreeSeven_nestedSquareCompletion_pos
    (c0 c1 c2 c3 c4 c5 c6 c7 x : ℝ)
    (hx : 0 ≤ x)
    (h0 : 0 < c0)
    (hΔ1 : 0 < 4 * c0 * c2 - c1 ^ 2)
    (hΔ2 :
      0 < (4 * c0 * c2 - c1 ^ 2) * c4 - c0 * c3 ^ 2)
    (h5 : 0 ≤ c5) (h6 : 0 ≤ c6) (h7 : 0 ≤ c7) :
    0 < c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 +
      c4 * x ^ 4 + c5 * x ^ 5 + c6 * x ^ 6 + c7 * x ^ 7 := by
  let Δ1 := 4 * c0 * c2 - c1 ^ 2
  let Δ2 := Δ1 * c4 - c0 * c3 ^ 2
  let p := c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 +
    c4 * x ^ 4 + c5 * x ^ 5 + c6 * x ^ 6 + c7 * x ^ 7
  have hΔ1' : 0 < Δ1 := by simpa only [Δ1] using hΔ1
  have hΔ2' : 0 < Δ2 := by simpa only [Δ2, Δ1] using hΔ2
  have htail : 0 ≤ c5 * x + c6 * x ^ 2 + c7 * x ^ 3 := by
    positivity
  have hidentity :
      (4 * c0 * Δ1) * p =
        Δ1 * (2 * c0 + c1 * x) ^ 2 +
          x ^ 2 * (Δ1 + 2 * c0 * c3 * x) ^ 2 +
          4 * c0 * x ^ 4 * Δ2 +
          4 * c0 * Δ1 * x ^ 4 *
            (c5 * x + c6 * x ^ 2 + c7 * x ^ 3) := by
    dsimp only [p, Δ1, Δ2]
    ring
  have hrhs :
      0 < Δ1 * (2 * c0 + c1 * x) ^ 2 +
          x ^ 2 * (Δ1 + 2 * c0 * c3 * x) ^ 2 +
          4 * c0 * x ^ 4 * Δ2 +
          4 * c0 * Δ1 * x ^ 4 *
            (c5 * x + c6 * x ^ 2 + c7 * x ^ 3) := by
    by_cases hx0 : x = 0
    · subst x
      simp only [zero_pow (by omega : 2 ≠ 0), zero_mul, mul_zero,
        add_zero]
      positivity
    · have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hmain : 0 < 4 * c0 * x ^ 4 * Δ2 := by positivity
      positivity
  have hscale : 0 ≤ 4 * c0 * Δ1 := by positivity
  have hproduct : 0 < (4 * c0 * Δ1) * p := by
    rw [hidentity]
    exact hrhs
  have hp : 0 < p :=
    pos_of_mul_pos_left (by simpa only [mul_comm] using hproduct) hscale
  simpa only [p] using hp

private abbrev pSeven : ℝ[X] :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven

/-- Six scalar gates obtained from the nested-square certificate.  They are
strict only where square completion needs an invertible pivot; the cubic
tail is allowed to be merely coefficientwise nonnegative. -/
def FactorTwoIntrinsicNineDirectPSevenNestedSquareGates : Prop :=
  0 < pSeven.coeff 0 ∧
    0 < 4 * pSeven.coeff 0 * pSeven.coeff 2 - pSeven.coeff 1 ^ 2 ∧
    0 <
      (4 * pSeven.coeff 0 * pSeven.coeff 2 - pSeven.coeff 1 ^ 2) *
          pSeven.coeff 4 -
        pSeven.coeff 0 * pSeven.coeff 3 ^ 2 ∧
    0 ≤ pSeven.coeff 5 ∧
    0 ≤ pSeven.coeff 6 ∧
    0 ≤ pSeven.coeff 7

/-- The six nested-square gates imply strict positivity of the seventh
prefix determinant on the complete projective half-line. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_eval_pos
    (h : FactorTwoIntrinsicNineDirectPSevenNestedSquareGates)
    (x : ℝ) (hx : 0 ≤ x) :
    0 < pSeven.eval x := by
  have heval :
      pSeven.eval x =
        pSeven.coeff 0 + pSeven.coeff 1 * x +
          pSeven.coeff 2 * x ^ 2 + pSeven.coeff 3 * x ^ 3 +
          pSeven.coeff 4 * x ^ 4 + pSeven.coeff 5 * x ^ 5 +
          pSeven.coeff 6 * x ^ 6 + pSeven.coeff 7 * x ^ 7 := by
    rw [pSeven.as_sum_range_C_mul_X_pow' (n := 8)
      (lt_of_le_of_lt
        factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_natDegree_le
        (by norm_num))]
    norm_num [Finset.sum_range_succ]
  rw [heval]
  apply degreeSeven_nestedSquareCompletion_pos
  · exact hx
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenNestedSquareStructural
