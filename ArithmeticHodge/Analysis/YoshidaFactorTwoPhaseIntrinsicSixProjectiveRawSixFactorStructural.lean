import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4UniformStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixFactorStructural

noncomputable section

open Polynomial
open ThreeByThreeFractionFreeGram
open YoshidaFactorTwoPhaseIntrinsicSixP4UniformStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

/-!
# Structural factorization of the final projective gap

The final `P₅` gap is a bordered symmetric determinant.  Fraction-free Schur
elimination, the polarized adjugate update, and the three-dimensional Gram
identities factor it as the cube of the low determinant times the raw
six-mode determinant.  The proof never enumerates polynomial coefficients.
-/

private abbrev lowDet : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveRawLowDetPolynomial

private abbrev pivot : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveRawP4PivotPolynomial

private abbrev oddEntry (i j : Fin 3) : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveRawOddEntryPolynomial i j

private abbrev lowAdjugatePair (i j : Fin 3) : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveRawLowAdjugatePairPolynomial i j

private abbrev pivotOddCross (i : Fin 3) : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveRawP4OddCrossPolynomial i

private abbrev adjugatePair (i j : Fin 3) : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveRawAdjugatePairPolynomial i j

private abbrev adjugateCofactor (i j : Fin 3) : ℝ[X] :=
  factorTwoIntrinsicSixProjectiveRawAdjugateCofactorPolynomial i j

private theorem pivot_ne_zero : pivot ≠ 0 := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial ≠ 0
  intro hp
  have heval :
      factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.eval 0 = 0 := by
    rw [hp]
    simp
  rw [eval_factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial] at heval
  have hpos := factorTwoIntrinsicSixProjectiveP4Pivot_pos 0 (by norm_num)
  linarith

private theorem cofactor00 :
    adjugatePair 1 1 * adjugatePair 2 2 - adjugatePair 1 2 ^ 2 =
      pivot * adjugateCofactor 0 0 := by
  have hminor := factorTwoIntrinsicSixProjectiveRawAdjugatePairMinor_factor 0 0
  unfold factorTwoIntrinsicSixProjectiveRawAdjugatePairMinorPolynomial
    factorTwoIntrinsicSixProjectiveRawCofactorLeftIndex
    factorTwoIntrinsicSixProjectiveRawCofactorRightIndex at hminor
  rw [factorTwoIntrinsicSixProjectiveRawAdjugatePair_symmetric 2 1] at hminor
  simpa [pow_two] using hminor

private theorem cofactor01 :
    adjugatePair 0 2 * adjugatePair 1 2 -
        adjugatePair 0 1 * adjugatePair 2 2 =
      pivot * adjugateCofactor 0 1 := by
  have hminor := factorTwoIntrinsicSixProjectiveRawAdjugatePairMinor_factor 0 1
  unfold factorTwoIntrinsicSixProjectiveRawAdjugatePairMinorPolynomial
    factorTwoIntrinsicSixProjectiveRawCofactorLeftIndex
    factorTwoIntrinsicSixProjectiveRawCofactorRightIndex at hminor
  rw [factorTwoIntrinsicSixProjectiveRawAdjugatePair_symmetric 2 0,
    factorTwoIntrinsicSixProjectiveRawAdjugatePair_symmetric 1 0] at hminor
  ring_nf at hminor ⊢
  exact hminor

private theorem cofactor02 :
    adjugatePair 0 1 * adjugatePair 1 2 -
        adjugatePair 0 2 * adjugatePair 1 1 =
      pivot * adjugateCofactor 0 2 := by
  have hminor := factorTwoIntrinsicSixProjectiveRawAdjugatePairMinor_factor 0 2
  unfold factorTwoIntrinsicSixProjectiveRawAdjugatePairMinorPolynomial
    factorTwoIntrinsicSixProjectiveRawCofactorLeftIndex
    factorTwoIntrinsicSixProjectiveRawCofactorRightIndex at hminor
  rw [factorTwoIntrinsicSixProjectiveRawAdjugatePair_symmetric 1 0,
    factorTwoIntrinsicSixProjectiveRawAdjugatePair_symmetric 2 1,
    factorTwoIntrinsicSixProjectiveRawAdjugatePair_symmetric 2 0] at hminor
  ring_nf at hminor ⊢
  exact hminor

private theorem cofactor11 :
    adjugatePair 0 0 * adjugatePair 2 2 - adjugatePair 0 2 ^ 2 =
      pivot * adjugateCofactor 1 1 := by
  have hminor := factorTwoIntrinsicSixProjectiveRawAdjugatePairMinor_factor 1 1
  unfold factorTwoIntrinsicSixProjectiveRawAdjugatePairMinorPolynomial
    factorTwoIntrinsicSixProjectiveRawCofactorLeftIndex
    factorTwoIntrinsicSixProjectiveRawCofactorRightIndex at hminor
  rw [factorTwoIntrinsicSixProjectiveRawAdjugatePair_symmetric 2 0] at hminor
  ring_nf at hminor ⊢
  exact hminor

private theorem cofactor12 :
    adjugatePair 0 1 * adjugatePair 0 2 -
        adjugatePair 0 0 * adjugatePair 1 2 =
      pivot * adjugateCofactor 1 2 := by
  have hminor := factorTwoIntrinsicSixProjectiveRawAdjugatePairMinor_factor 1 2
  unfold factorTwoIntrinsicSixProjectiveRawAdjugatePairMinorPolynomial
    factorTwoIntrinsicSixProjectiveRawCofactorLeftIndex
    factorTwoIntrinsicSixProjectiveRawCofactorRightIndex at hminor
  rw [factorTwoIntrinsicSixProjectiveRawAdjugatePair_symmetric 2 0,
    factorTwoIntrinsicSixProjectiveRawAdjugatePair_symmetric 2 1] at hminor
  simpa [mul_comm] using hminor

private theorem cofactor22 :
    adjugatePair 0 0 * adjugatePair 1 1 - adjugatePair 0 1 ^ 2 =
      pivot * adjugateCofactor 2 2 := by
  have hminor := factorTwoIntrinsicSixProjectiveRawAdjugatePairMinor_factor 2 2
  unfold factorTwoIntrinsicSixProjectiveRawAdjugatePairMinorPolynomial
    factorTwoIntrinsicSixProjectiveRawCofactorLeftIndex
    factorTwoIntrinsicSixProjectiveRawCofactorRightIndex at hminor
  rw [factorTwoIntrinsicSixProjectiveRawAdjugatePair_symmetric 1 0] at hminor
  simpa [pow_two] using hminor

private theorem adjugatePair_det :
    det3 (adjugatePair 0 0) (adjugatePair 0 1) (adjugatePair 0 2)
        (adjugatePair 1 1) (adjugatePair 1 2) (adjugatePair 2 2) =
      pivot ^ 2 * C factorTwoIntrinsicSixProjectiveRawAlternatingDeterminant ^ 2 := by
  have hfactor :=
    factorTwoIntrinsicSixProjectiveRawAdjugatePairDeterminant_factor
  unfold factorTwoIntrinsicSixProjectiveRawAdjugatePairDeterminantPolynomial at hfactor
  rw [show C (factorTwoIntrinsicSixProjectiveRawAlternatingDeterminant ^ 2) =
      C factorTwoIntrinsicSixProjectiveRawAlternatingDeterminant ^ 2 by
        simp] at hfactor
  simpa [det3] using hfactor

/-- Exact fraction-free factorization of the final projective `P₅` gap into
the cube of the low determinant and the raw six-mode determinant. -/
theorem factorTwoIntrinsicSixProjectiveP5GapPolynomial_factor :
    factorTwoIntrinsicSixProjectiveP5GapPolynomial =
      lowDet ^ 3 * factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial := by
  rw [factorTwoIntrinsicSixProjectiveP5GapPolynomial_eq_borderedGap]
  rw [factorTwoIntrinsicSixProjectiveRawOddResidual_eq_components 0 0,
    factorTwoIntrinsicSixProjectiveRawOddResidual_eq_components 0 1,
    factorTwoIntrinsicSixProjectiveRawOddResidual_eq_components 0 2,
    factorTwoIntrinsicSixProjectiveRawOddResidual_eq_components 1 1,
    factorTwoIntrinsicSixProjectiveRawOddResidual_eq_components 1 2,
    factorTwoIntrinsicSixProjectiveRawOddResidual_eq_components 2 2]
  rw [factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial_eq_fractionFreeGram]
  exact complete_fractionFree_factor
    lowDet pivot X (C factorTwoIntrinsicSixProjectiveRawAlternatingDeterminant)
    (pivotOddCross 0) (pivotOddCross 1) (pivotOddCross 2)
    (oddEntry 0 0) (oddEntry 0 1) (oddEntry 0 2)
    (oddEntry 1 1) (oddEntry 1 2) (oddEntry 2 2)
    (lowAdjugatePair 0 0) (lowAdjugatePair 0 1) (lowAdjugatePair 0 2)
    (lowAdjugatePair 1 1) (lowAdjugatePair 1 2) (lowAdjugatePair 2 2)
    (adjugatePair 0 0) (adjugatePair 0 1) (adjugatePair 0 2)
    (adjugatePair 1 1) (adjugatePair 1 2) (adjugatePair 2 2)
    (adjugateCofactor 0 0) (adjugateCofactor 0 1) (adjugateCofactor 0 2)
    (adjugateCofactor 1 1) (adjugateCofactor 1 2) (adjugateCofactor 2 2)
    pivot_ne_zero
    (factorTwoIntrinsicSixProjectiveRawAdjugatePair_fractionFree 0 0).symm
    (factorTwoIntrinsicSixProjectiveRawAdjugatePair_fractionFree 0 1).symm
    (factorTwoIntrinsicSixProjectiveRawAdjugatePair_fractionFree 0 2).symm
    (factorTwoIntrinsicSixProjectiveRawAdjugatePair_fractionFree 1 1).symm
    (factorTwoIntrinsicSixProjectiveRawAdjugatePair_fractionFree 1 2).symm
    (factorTwoIntrinsicSixProjectiveRawAdjugatePair_fractionFree 2 2).symm
    cofactor00 cofactor01 cofactor02 cofactor11 cofactor12 cofactor22
    adjugatePair_det

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixFactorStructural
