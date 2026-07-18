import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveSylvesterStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveCoefficientGateStructural

noncomputable section

open Polynomial
open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveSylvesterStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

/-!
# Finite coefficient frontier for the cutoff-nine determinant cones

The determinant-polynomial construction is exact but intentionally leaves its
coefficients opaque.  Degree bounds reduce the global cone hypotheses to a
finite list of scalar signs and five discriminants.  This file records that
list without expanding a `7 x 7`, `8 x 8`, or `9 x 9` determinant.
-/

private abbrev pSeven : ℝ[X] :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven

private abbrev pEight : ℝ[X] :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight

private abbrev pNine : ℝ[X] :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine

/-- Two allocated quadratic heads, followed by the three nonnegative tail
coefficients of `p₇`. -/
def FactorTwoIntrinsicNineDirectPSevenCoefficientGates : Prop :=
  0 < pSeven.coeff 0 ∧
    pSeven.coeff 1 < 0 ∧
    0 < pSeven.coeff 2 ∧
    pSeven.coeff 3 < 0 ∧
    0 < pSeven.coeff 4 ∧
    3 * pSeven.coeff 1 ^ 2 <
      8 * pSeven.coeff 0 * pSeven.coeff 2 ∧
    3 * pSeven.coeff 3 ^ 2 <
      4 * pSeven.coeff 2 * pSeven.coeff 4 ∧
    0 ≤ pSeven.coeff 5 ∧
    0 ≤ pSeven.coeff 6 ∧
    0 < pSeven.coeff 7

/-- One positive quadratic head and six nonnegative tail coefficients of
`p₈`. -/
def FactorTwoIntrinsicNineDirectPEightCoefficientGates : Prop :=
  0 < pEight.coeff 0 ∧
    pEight.coeff 1 < 0 ∧
    0 < pEight.coeff 2 ∧
    pEight.coeff 1 ^ 2 <
      4 * pEight.coeff 0 * pEight.coeff 2 ∧
    0 ≤ pEight.coeff 3 ∧
    0 ≤ pEight.coeff 4 ∧
    0 ≤ pEight.coeff 5 ∧
    0 ≤ pEight.coeff 6 ∧
    0 ≤ pEight.coeff 7 ∧
    0 < pEight.coeff 8

/-- Two disjoint positive quadratic heads and four nonnegative tail
coefficients of `p₉`. -/
def FactorTwoIntrinsicNineDirectPNineCoefficientGates : Prop :=
  0 < pNine.coeff 0 ∧
    pNine.coeff 1 < 0 ∧
    0 < pNine.coeff 2 ∧
    0 < pNine.coeff 3 ∧
    pNine.coeff 4 < 0 ∧
    0 < pNine.coeff 5 ∧
    pNine.coeff 1 ^ 2 <
      4 * pNine.coeff 0 * pNine.coeff 2 ∧
    pNine.coeff 4 ^ 2 <
      4 * pNine.coeff 3 * pNine.coeff 5 ∧
    0 ≤ pNine.coeff 6 ∧
    0 ≤ pNine.coeff 7 ∧
    0 ≤ pNine.coeff 8 ∧
    0 < pNine.coeff 9

private theorem pSeven_decomposition :
    pSeven =
      (C (pSeven.coeff 0) + C (pSeven.coeff 1) * X +
          C ((2 / 3 : ℝ) * pSeven.coeff 2) * X ^ 2) +
        X ^ 2 *
          (C ((1 / 3 : ℝ) * pSeven.coeff 2) +
            C (pSeven.coeff 3) * X + C (pSeven.coeff 4) * X ^ 2) +
        X ^ 5 *
          (C (pSeven.coeff 5) + C (pSeven.coeff 6) * X +
            C (pSeven.coeff 7) * X ^ 2) := by
  rw [pSeven.as_sum_range_C_mul_X_pow' (n := 8)
    (lt_of_le_of_lt
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_natDegree_le
      (by norm_num))]
  norm_num [Finset.sum_range_succ]
  let z : ℝ := pSeven.coeff 2
  have hsplit : C z =
      C z * C (2 / 3 : ℝ) + C z * C (1 / 3 : ℝ) := by
    rw [← map_mul, ← map_mul, ← map_add]
    exact congrArg C (by ring)
  linear_combination X ^ 2 * hsplit

private theorem pEight_decomposition :
    pEight =
      C (pEight.coeff 0) + C (pEight.coeff 1) * X +
          C (pEight.coeff 2) * X ^ 2 +
        X ^ 3 *
          (C (pEight.coeff 3) + C (pEight.coeff 4) * X +
            C (pEight.coeff 5) * X ^ 2 + C (pEight.coeff 6) * X ^ 3 +
            C (pEight.coeff 7) * X ^ 4 + C (pEight.coeff 8) * X ^ 5) := by
  rw [pEight.as_sum_range_C_mul_X_pow' (n := 9)
    (lt_of_le_of_lt
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight_natDegree_le
      (by norm_num))]
  norm_num [Finset.sum_range_succ]
  ring

private theorem pNine_decomposition :
    pNine =
      (C (pNine.coeff 0) + C (pNine.coeff 1) * X +
          C (pNine.coeff 2) * X ^ 2) +
        X ^ 3 *
          (C (pNine.coeff 3) + C (pNine.coeff 4) * X +
            C (pNine.coeff 5) * X ^ 2) +
        X ^ 6 *
          (C (pNine.coeff 6) + C (pNine.coeff 7) * X +
            C (pNine.coeff 8) * X ^ 2 + C (pNine.coeff 9) * X ^ 3) := by
  rw [pNine.as_sum_range_C_mul_X_pow' (n := 10)
    (lt_of_le_of_lt
      factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine_natDegree_le
      (by norm_num))]
  norm_num [Finset.sum_range_succ]
  ring

theorem pSeven_mem_positiveTwoQuadraticHeadsNonnegativeTailCone
    (h : FactorTwoIntrinsicNineDirectPSevenCoefficientGates) :
    PositiveTwoQuadraticHeadsNonnegativeTailCone pSeven := by
  rcases h with
    ⟨h0, h1, h2, h3, h4, hdisc1, hdisc3, h5, h6, h7⟩
  refine ⟨pSeven.coeff 0, pSeven.coeff 1,
    (2 / 3 : ℝ) * pSeven.coeff 2,
    (1 / 3 : ℝ) * pSeven.coeff 2,
    pSeven.coeff 3, pSeven.coeff 4, 2,
    C (pSeven.coeff 5) + C (pSeven.coeff 6) * X +
      C (pSeven.coeff 7) * X ^ 2,
    pSeven_decomposition, h0, ?_, ?_, ?_, h4, ?_, ?_⟩
  · nlinarith
  · right
    constructor
    · exact h1
    · nlinarith
  · nlinarith
  · right
    constructor
    · exact h3
    · nlinarith
  · intro n
    rcases n with _ | n
    · simpa using h5
    rcases n with _ | n
    · simpa using h6
    rcases n with _ | n
    · simpa using h7.le
    simp

theorem pEight_mem_positiveQuadraticHeadNonnegativeTailCone
    (h : FactorTwoIntrinsicNineDirectPEightCoefficientGates) :
    PositiveQuadraticHeadNonnegativeTailCone pEight := by
  rcases h with
    ⟨h0, h1, h2, hdisc, h3, h4, h5, h6, h7, h8⟩
  refine ⟨pEight.coeff 0, pEight.coeff 1, pEight.coeff 2,
    C (pEight.coeff 3) + C (pEight.coeff 4) * X +
      C (pEight.coeff 5) * X ^ 2 + C (pEight.coeff 6) * X ^ 3 +
      C (pEight.coeff 7) * X ^ 4 + C (pEight.coeff 8) * X ^ 5,
    pEight_decomposition, h0, h2, ?_, ?_⟩
  · right
    exact ⟨h1, hdisc⟩
  · intro n
    rcases n with _ | n
    · simpa using h3
    rcases n with _ | n
    · simpa using h4
    rcases n with _ | n
    · simpa using h5
    rcases n with _ | n
    · simpa using h6
    rcases n with _ | n
    · simpa using h7
    rcases n with _ | n
    · simpa using h8.le
    simp

theorem pNine_mem_positiveTwoQuadraticHeadsNonnegativeTailCone
    (h : FactorTwoIntrinsicNineDirectPNineCoefficientGates) :
    PositiveTwoQuadraticHeadsNonnegativeTailCone pNine := by
  rcases h with
    ⟨h0, h1, h2, h3, h4, h5, hdisc1, hdisc4, h6, h7, h8, h9⟩
  refine ⟨pNine.coeff 0, pNine.coeff 1, pNine.coeff 2,
    pNine.coeff 3, pNine.coeff 4, pNine.coeff 5, 3,
    C (pNine.coeff 6) + C (pNine.coeff 7) * X +
      C (pNine.coeff 8) * X ^ 2 + C (pNine.coeff 9) * X ^ 3,
    pNine_decomposition, h0, h2, ?_, h3, h5, ?_, ?_⟩
  · right
    exact ⟨h1, hdisc1⟩
  · right
    exact ⟨h4, hdisc4⟩
  · intro n
    rcases n with _ | n
    · simpa using h6
    rcases n with _ | n
    · simpa using h7
    rcases n with _ | n
    · simpa using h8
    rcases n with _ | n
    · simpa using h9.le
    simp

/-- The finite scalar frontier closes the direct cutoff-nine matrix on the
whole phase circle. -/
theorem factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_coefficient_gates
    (hSeven : FactorTwoIntrinsicNineDirectPSevenCoefficientGates)
    (hEight : FactorTwoIntrinsicNineDirectPEightCoefficientGates)
    (hNine : FactorTwoIntrinsicNineDirectPNineCoefficientGates)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (factorTwoIntrinsicNineDirectLowMatrix a b).PosSemidef := by
  apply factorTwoIntrinsicNineDirectLowMatrix_posSemidef_of_polynomial_cones
  · exact pSeven_mem_positiveTwoQuadraticHeadsNonnegativeTailCone hSeven
  · exact pEight_mem_positiveQuadraticHeadNonnegativeTailCone hEight
  · exact pNine_mem_positiveTwoQuadraticHeadsNonnegativeTailCone hNine
  · exact hSeven.2.2.2.2.2.2.2.2.2
  · exact hEight.2.2.2.2.2.2.2.2.2
  · exact hNine.2.2.2.2.2.2.2.2.2.2.2
  · exact hab

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveCoefficientGateStructural
