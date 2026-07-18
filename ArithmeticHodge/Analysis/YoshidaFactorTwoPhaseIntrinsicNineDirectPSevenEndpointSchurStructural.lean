import ArithmeticHodge.Analysis.ThreeByThreeConvexPencil
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenNestedSquareStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenEndpointSchurStructural

noncomputable section

open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenNestedSquareStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectSixSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseIntrinsicSixStrictDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# Endpoint Schur reduction for the seventh direct prefix

At either projective endpoint the `P6` border has no odd coordinates.  The
seven-dimensional determinant gate therefore reduces exactly to adjoining
one row to the positive `P0/P2/P4` block.  The two remaining analytic
obligations are scalar adjugate gaps; no determinant is expanded.
-/

/-- The positive-endpoint inverse-free Schur gap for adjoining `P6` to
`P0/P2/P4`. -/
def factorTwoIntrinsicNineDirectP6PlusAdjugateGap : ℝ :=
  factorTwoIntrinsicSixUnbalancedEPlusDet *
      factorTwoIntrinsicNineDirectP6RetainedDiagonal 1 0 -
    adjugateQuadratic
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus22
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedEPlus44
      factorTwoIntrinsicNineEPlus06
      factorTwoIntrinsicNineEPlus26
      factorTwoIntrinsicNineEPlus46

/-- The negative-endpoint inverse-free Schur gap for adjoining `P6` to
`P0/P2/P4`. -/
def factorTwoIntrinsicNineDirectP6MinusAdjugateGap : ℝ :=
  factorTwoIntrinsicSixUnbalancedEMinusDet *
      factorTwoIntrinsicNineDirectP6RetainedDiagonal (-1) 0 -
    adjugateQuadratic
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44
      factorTwoIntrinsicNineEMinus06
      factorTwoIntrinsicNineEMinus26
      factorTwoIntrinsicNineEMinus46

/-- A strict adjugate gap gives strict Cauchy for a nonzero vector in a
positive `3 x 3` form.  This is the division-free one-row Schur step used at
both endpoints. -/
theorem border_cauchy_of_adjugate_gap
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 d : ℝ)
    (h00 : 0 < q00)
    (hminor : 0 < leadingMinorTwo q00 q01 q11)
    (hdet : 0 < symmetricDeterminant q00 q01 q02 q11 q12 q22)
    (hgap :
      adjugateQuadratic q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 <
        symmetricDeterminant q00 q01 q02 q11 q12 q22 * d)
    (x0 x1 x2 : ℝ) (hx : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0) :
    (ell0 * x0 + ell1 * x1 + ell2 * x2) ^ 2 <
      symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2 * d := by
  let D := symmetricDeterminant q00 q01 q02 q11 q12 q22
  let A := adjugateQuadratic
    q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
  let Q := symmetricQuadratic
    q00 q01 q02 q11 q12 q22 x0 x1 x2
  let L := ell0 * x0 + ell1 * x1 + ell2 * x2
  have hA : 0 ≤ A := by
    simpa only [A] using adjugateQuadratic_nonneg
      q00 q01 q02 q11 q12 q22 h00 hminor hdet ell0 ell1 ell2
  have hD : 0 < D := by simpa only [D] using hdet
  have hQ : 0 < Q := by
    simpa only [Q] using symmetricQuadratic_pos
      q00 q01 q02 q11 q12 q22 h00 hminor hdet x0 x1 x2 hx
  have hd : 0 < d := by
    have : A < D * d := by simpa only [A, D] using hgap
    nlinarith
  have hCauchy := adjugate_cauchy
    q00 q01 q02 q11 q12 q22 h00 hminor hdet
    ell0 ell1 ell2 x0 x1 x2
  change D * L ^ 2 ≤ Q * A at hCauchy
  have hgap' : A < D * d := by simpa only [A, D] using hgap
  have hstrict : D * L ^ 2 < D * (Q * d) := by
    calc
      D * L ^ 2 ≤ Q * A := hCauchy
      _ < Q * (D * d) := (mul_lt_mul_of_pos_left hgap' hQ)
      _ = D * (Q * d) := by ring
  nlinarith

private theorem staticEven_plus_eq_symmetricQuadratic
    (c0 c2 c4 : ℝ) :
    factorTwoIntrinsicSixStaticEven 1 c0 c2 c4 =
      symmetricQuadratic
        factorTwoIntrinsicSixUnbalancedEPlus00
        factorTwoIntrinsicSixUnbalancedEPlus02
        factorTwoIntrinsicSixUnbalancedEPlus04
        factorTwoIntrinsicSixUnbalancedEPlus22
        factorTwoIntrinsicSixUnbalancedEPlus24
        factorTwoIntrinsicSixUnbalancedEPlus44 c0 c2 c4 := by
  unfold factorTwoIntrinsicSixStaticEven symmetricQuadratic
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
  ring

private theorem staticEven_minus_eq_symmetricQuadratic
    (c0 c2 c4 : ℝ) :
    factorTwoIntrinsicSixStaticEven (-1) c0 c2 c4 =
      symmetricQuadratic
        factorTwoIntrinsicSixUnbalancedEMinus00
        factorTwoIntrinsicSixUnbalancedEMinus02
        factorTwoIntrinsicSixUnbalancedEMinus04
        factorTwoIntrinsicSixUnbalancedEMinus22
        factorTwoIntrinsicSixUnbalancedEMinus24
        factorTwoIntrinsicSixUnbalancedEMinus44 c0 c2 c4 := by
  unfold factorTwoIntrinsicSixStaticEven symmetricQuadratic
    factorTwoIntrinsicSixUnbalancedEMinus00
    factorTwoIntrinsicSixUnbalancedEMinus02
    factorTwoIntrinsicSixUnbalancedEMinus04
    factorTwoIntrinsicSixUnbalancedEMinus22
    factorTwoIntrinsicSixUnbalancedEMinus24
    factorTwoIntrinsicSixUnbalancedEMinus44
  ring

private theorem P6BorderVector_plus_eq
    (i : Fin 6) :
    factorTwoIntrinsicNineDirectP6BorderVector 1 0 i =
      ![factorTwoIntrinsicNineEPlus06,
        factorTwoIntrinsicNineEPlus26,
        factorTwoIntrinsicNineEPlus46, 0, 0, 0] i := by
  fin_cases i <;>
    unfold factorTwoIntrinsicNineDirectP6BorderVector
      factorTwoIntrinsicNineDirectP6PrefixMatrix
      factorTwoIntrinsicNineDirectPrefix
      factorTwoIntrinsicNineDirectLowMatrix
      factorTwoIntrinsicNineDirectCoordinateBilinear
      factorTwoIntrinsicNineDirectCoordinateQuadratic
      factorTwoIntrinsicNineDirectLowQuadratic
      factorTwoIntrinsicNineDirectEvenQuadratic
      factorTwoIntrinsicNineDirectOddQuadratic
      factorTwoIntrinsicNineDirectAlternating
      factorTwoIntrinsicNineDirectUnit
      factorTwoIntrinsicSixStaticEven
      factorTwoIntrinsicSixStaticOdd
      factorTwoIntrinsicSixStaticAlternating
      factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicNineP678LowReserve
      factorTwoIntrinsicNineEPlus06
      factorTwoIntrinsicNineEPlus26
      factorTwoIntrinsicNineEPlus46
      factorTwoIntrinsicNineEvenEntry <;>
    simp [Pi.single_apply] <;>
    ring

private theorem P6BorderVector_minus_eq
    (i : Fin 6) :
    factorTwoIntrinsicNineDirectP6BorderVector (-1) 0 i =
      ![factorTwoIntrinsicNineEMinus06,
        factorTwoIntrinsicNineEMinus26,
        factorTwoIntrinsicNineEMinus46, 0, 0, 0] i := by
  fin_cases i <;>
    unfold factorTwoIntrinsicNineDirectP6BorderVector
      factorTwoIntrinsicNineDirectP6PrefixMatrix
      factorTwoIntrinsicNineDirectPrefix
      factorTwoIntrinsicNineDirectLowMatrix
      factorTwoIntrinsicNineDirectCoordinateBilinear
      factorTwoIntrinsicNineDirectCoordinateQuadratic
      factorTwoIntrinsicNineDirectLowQuadratic
      factorTwoIntrinsicNineDirectEvenQuadratic
      factorTwoIntrinsicNineDirectOddQuadratic
      factorTwoIntrinsicNineDirectAlternating
      factorTwoIntrinsicNineDirectUnit
      factorTwoIntrinsicSixStaticEven
      factorTwoIntrinsicSixStaticOdd
      factorTwoIntrinsicSixStaticAlternating
      factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicNineP678LowReserve
      factorTwoIntrinsicNineEMinus06
      factorTwoIntrinsicNineEMinus26
      factorTwoIntrinsicNineEMinus46
      factorTwoIntrinsicNineEvenEntry <;>
    simp [Pi.single_apply] <;>
    ring

theorem factorTwoIntrinsicNineDirectP6BorderFunctional_plus_eq
    (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectP6BorderFunctional 1 0 x =
      factorTwoIntrinsicNineEPlus06 * x 0 +
        factorTwoIntrinsicNineEPlus26 * x 1 +
        factorTwoIntrinsicNineEPlus46 * x 2 := by
  unfold factorTwoIntrinsicNineDirectP6BorderFunctional dotProduct
  simp_rw [P6BorderVector_plus_eq]
  norm_num [Fin.sum_univ_succ]
  ring

theorem factorTwoIntrinsicNineDirectP6BorderFunctional_minus_eq
    (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectP6BorderFunctional (-1) 0 x =
      factorTwoIntrinsicNineEMinus06 * x 0 +
        factorTwoIntrinsicNineEMinus26 * x 1 +
        factorTwoIntrinsicNineEMinus46 * x 2 := by
  unfold factorTwoIntrinsicNineDirectP6BorderFunctional dotProduct
  simp_rw [P6BorderVector_minus_eq]
  norm_num [Fin.sum_univ_succ]
  ring

private theorem staticOdd_minus_nonneg
    (c1 c3 c5 : ℝ) :
    0 ≤ factorTwoIntrinsicSixStaticOdd (-1) c1 c3 c5 := by
  by_cases hne : c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0
  · have h := factorTwoIntrinsicSixPhaseCoordinates_pos
      0 0 0 c1 c3 c5 1 0 (by norm_num)
      (by simpa using hne)
    simpa [factorTwoIntrinsicSixStaticEven] using h.le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl, rfl⟩
    simp [factorTwoIntrinsicSixStaticOdd,
      factorTwoIntrinsicOddPhaseQuadratic]

private theorem staticOdd_plus_nonneg
    (c1 c3 c5 : ℝ) :
    0 ≤ factorTwoIntrinsicSixStaticOdd 1 c1 c3 c5 := by
  by_cases hne : c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0
  · have h := factorTwoIntrinsicSixPhaseCoordinates_pos
      0 0 0 c1 c3 c5 (-1) 0 (by norm_num)
      (by simpa using hne)
    simpa [factorTwoIntrinsicSixStaticEven] using h.le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl, rfl⟩
    simp [factorTwoIntrinsicSixStaticOdd,
      factorTwoIntrinsicOddPhaseQuadratic]

/-- Positivity of the one scalar plus-endpoint adjugate gap closes the actual
seven-coordinate prefix at `(1,0)`. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_plus_posDef_of_adjugateGap
    (hgap : 0 < factorTwoIntrinsicNineDirectP6PlusAdjugateGap) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix 1 0).PosDef := by
  rcases factorTwoIntrinsicSixUnbalancedEPlus_positive with
    ⟨h00, hminor, hdet⟩
  have hd : 0 < factorTwoIntrinsicNineDirectP6RetainedDiagonal 1 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 160)
      (one_div_one_hundred_sixty_le_P6RetainedDiagonal 1 0 (by norm_num))
  apply factorTwoIntrinsicNineDirectP6PrefixMatrix_posDef_of_border_cauchy
    1 0 (by norm_num)
  intro x hx
  by_cases heven : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0
  · have hsmall := border_cauchy_of_adjugate_gap
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus22
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedEPlus44
      factorTwoIntrinsicNineEPlus06
      factorTwoIntrinsicNineEPlus26
      factorTwoIntrinsicNineEPlus46
      (factorTwoIntrinsicNineDirectP6RetainedDiagonal 1 0)
      h00 hminor hdet (by
        apply sub_pos.mp
        simpa only [factorTwoIntrinsicNineDirectP6PlusAdjugateGap,
          factorTwoIntrinsicSixUnbalancedEPlusDet] using hgap)
      (x 0) (x 1) (x 2) heven
    have hodd := staticOdd_minus_nonneg (x 3) (x 4) (x 5)
    rw [factorTwoIntrinsicNineDirectP6BorderFunctional_plus_eq]
    rw [factorTwoIntrinsicNineDirectCoreMatrix_quadratic,
      staticEven_plus_eq_symmetricQuadratic]
    simp only [zero_mul, add_zero]
    nlinarith
  · push_neg at heven
    rcases heven with ⟨h0, h1, h2⟩
    have hcore :=
      (factorTwoIntrinsicNineDirectCoreMatrix_posDef 1 0
        (by norm_num)).dotProduct_mulVec_pos hx
    simp only [star_trivial] at hcore
    rw [factorTwoIntrinsicNineDirectP6BorderFunctional_plus_eq,
      h0, h1, h2]
    norm_num
    positivity

/-- Positivity of the one scalar minus-endpoint adjugate gap closes the
omitted projective endpoint. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_minus_posDef_of_adjugateGap
    (hgap : 0 < factorTwoIntrinsicNineDirectP6MinusAdjugateGap) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix (-1) 0).PosDef := by
  rcases factorTwoIntrinsicSixUnbalancedEMinus_positive with
    ⟨h00, hminor, hdet⟩
  have hd : 0 < factorTwoIntrinsicNineDirectP6RetainedDiagonal (-1) 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 160)
      (one_div_one_hundred_sixty_le_P6RetainedDiagonal (-1) 0 (by norm_num))
  apply factorTwoIntrinsicNineDirectP6PrefixMatrix_posDef_of_border_cauchy
    (-1) 0 (by norm_num)
  intro x hx
  by_cases heven : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0
  · have hsmall := border_cauchy_of_adjugate_gap
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44
      factorTwoIntrinsicNineEMinus06
      factorTwoIntrinsicNineEMinus26
      factorTwoIntrinsicNineEMinus46
      (factorTwoIntrinsicNineDirectP6RetainedDiagonal (-1) 0)
      h00 hminor hdet (by
        apply sub_pos.mp
        simpa only [factorTwoIntrinsicNineDirectP6MinusAdjugateGap,
          factorTwoIntrinsicSixUnbalancedEMinusDet] using hgap)
      (x 0) (x 1) (x 2) heven
    have hodd := staticOdd_plus_nonneg (x 3) (x 4) (x 5)
    rw [factorTwoIntrinsicNineDirectP6BorderFunctional_minus_eq]
    rw [factorTwoIntrinsicNineDirectCoreMatrix_quadratic,
      staticEven_minus_eq_symmetricQuadratic]
    simp only [neg_neg, zero_mul, add_zero]
    nlinarith
  · push_neg at heven
    rcases heven with ⟨h0, h1, h2⟩
    have hcore :=
      (factorTwoIntrinsicNineDirectCoreMatrix_posDef (-1) 0
        (by norm_num)).dotProduct_mulVec_pos hx
    simp only [star_trivial] at hcore
    rw [factorTwoIntrinsicNineDirectP6BorderFunctional_minus_eq,
      h0, h1, h2]
    norm_num
    positivity

/-- The constant coefficient of the seventh-prefix determinant is positive
as soon as the plus endpoint adjugate gap is positive. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_coeff_zero_pos_of_adjugateGap
    (hgap : 0 < factorTwoIntrinsicNineDirectP6PlusAdjugateGap) :
    0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 0 := by
  change 0 <
    (factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial 7
      (by omega)).coeff 0
  rw [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_zero]
  have hdet :=
    (factorTwoIntrinsicNineDirectP6PrefixMatrix_plus_posDef_of_adjugateGap
      hgap).det_pos
  simpa only [factorTwoIntrinsicNineDirectPrefixPlus,
    factorTwoIntrinsicNineDirectP6PrefixMatrix] using hdet

/-- The top coefficient of the seventh-prefix determinant is positive as
soon as the minus endpoint adjugate gap is positive. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_coeff_top_pos_of_adjugateGap
    (hgap : 0 < factorTwoIntrinsicNineDirectP6MinusAdjugateGap) :
    0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 7 := by
  change 0 <
    (factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial 7
      (by omega)).coeff 7
  rw [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_top]
  have hdet :=
    (factorTwoIntrinsicNineDirectP6PrefixMatrix_minus_posDef_of_adjugateGap
      hgap).det_pos
  simpa only [factorTwoIntrinsicNineDirectPrefixMinus,
    factorTwoIntrinsicNineDirectP6PrefixMatrix] using hdet

/-- Thus the two endpoint gates in the nested-square certificate are exactly
reduced to two scalar `3 x 3` adjugate gaps. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_endpoint_coefficients_pos_of_adjugateGaps
    (hPlus : 0 < factorTwoIntrinsicNineDirectP6PlusAdjugateGap)
    (hMinus : 0 < factorTwoIntrinsicNineDirectP6MinusAdjugateGap) :
    0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 0 ∧
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 7 :=
  ⟨factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_coeff_zero_pos_of_adjugateGap
      hPlus,
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_coeff_top_pos_of_adjugateGap
      hMinus⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenEndpointSchurStructural
