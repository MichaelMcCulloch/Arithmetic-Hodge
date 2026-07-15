import ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDiscriminant
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotMixedStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural

noncomputable section

open Polynomial
open ThreeByThreeConvexPencil
open ThreeByThreePositiveMixedDiscriminant
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLowSchur

private def pivotShift : ℝ := 1 / 100000

private theorem plus_diagonal_lower :
    (3439 / 25000 : ℝ) < factorTwoIntrinsicSixP4Diagonal 1 := by
  have hclean :=
    one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  have hpert := factorTwoCenteredSymmetricPerturbation_p4_lower
  change (3439 / 25000 : ℝ) < factorTwoIntrinsicP4PhaseDiagonal 1
  unfold factorTwoIntrinsicP4PhaseDiagonal
  norm_num at hclean hpert ⊢
  nlinarith

private theorem plus_lower_shifted_gates :
    0 < evenPositiveEndpointUltraSharp00 - pivotShift ∧
      0 < leadingMinorTwo
        (evenPositiveEndpointUltraSharp00 - pivotShift)
        evenPositiveEndpointUltraSharp02
        (evenPositiveEndpointUltraSharp22 - pivotShift) ∧
      0 < symmetricDeterminant
        (evenPositiveEndpointUltraSharp00 - pivotShift)
        evenPositiveEndpointUltraSharp02
        (factorTwoIntrinsicFourP45Cross04 1)
        (evenPositiveEndpointUltraSharp22 - pivotShift)
        (factorTwoIntrinsicFourP45Cross24 1)
        ((3439 / 25000 : ℝ) - pivotShift) := by
  let S : ℝ := factorTwoIntrinsicP4PlusCrossSum
  let D : ℝ := factorTwoIntrinsicP4PlusCrossDifference
  have hS := factorTwoIntrinsicP4PlusCrossSum_bounds
  have hD := factorTwoIntrinsicP4PlusCrossDifference_bounds
  have hSsq : S ^ 2 < (193 / 1000 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hS.2 hS.1.le (by norm_num)
  have hDsq : D ^ 2 < (39 / 2000 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hD.2 hD.1.le (by norm_num)
  have hSD : S * D < (193 / 1000 : ℝ) * (39 / 2000 : ℝ) := by
    calc
      S * D < (193 / 1000 : ℝ) * D :=
        mul_lt_mul_of_pos_right hS.2 hD.1
      _ < (193 / 1000 : ℝ) * (39 / 2000 : ℝ) :=
        mul_lt_mul_of_pos_left hD.2 (by norm_num)
  have h04 : factorTwoIntrinsicFourP45Cross04 1 = (S - D) / 2 := by
    dsimp only [S, D]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  have h24 : factorTwoIntrinsicFourP45Cross24 1 = (S + D) / 2 := by
    dsimp only [S, D]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  constructor
  · norm_num [evenPositiveEndpointUltraSharp00, pivotShift]
  constructor
  · norm_num [leadingMinorTwo, evenPositiveEndpointUltraSharp00,
      evenPositiveEndpointUltraSharp02, evenPositiveEndpointUltraSharp22,
      pivotShift]
  · rw [h04, h24]
    unfold symmetricDeterminant evenPositiveEndpointUltraSharp00
      evenPositiveEndpointUltraSharp02 evenPositiveEndpointUltraSharp22
      pivotShift
    dsimp only [S, D] at hSsq hDsq hSD ⊢
    nlinarith

private theorem minus_lower_shifted_gates :
    0 < intrinsicStaticMinusEvenLower00 - pivotShift ∧
      0 < leadingMinorTwo
        (intrinsicStaticMinusEvenLower00 - pivotShift)
        intrinsicStaticMinusEvenLower02
        (intrinsicStaticMinusEvenLower22 - pivotShift) ∧
      0 < symmetricDeterminant
        (intrinsicStaticMinusEvenLower00 - pivotShift)
        intrinsicStaticMinusEvenLower02
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (intrinsicStaticMinusEvenLower22 - pivotShift)
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicP4MinusDiagonalLower - pivotShift) := by
  let S : ℝ := factorTwoIntrinsicP4MinusCrossSum
  let D : ℝ := factorTwoIntrinsicP4MinusCrossDifference
  have h := factorTwoIntrinsicP4MinusCross_sum_difference_bounds
  have hS : 0 < S ∧ S < (3 / 10 : ℝ) := by
    simpa only [S] using ⟨h.1, h.2.1⟩
  have hD : 0 < D ∧ D < (7 / 100 : ℝ) := by
    simpa only [D] using ⟨h.2.2.1, h.2.2.2⟩
  have hSsq : S ^ 2 < (3 / 10 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hS.2 hS.1.le (by norm_num)
  have hDsq : D ^ 2 < (7 / 100 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hD.2 hD.1.le (by norm_num)
  have hSD : S * D < (3 / 10 : ℝ) * (7 / 100 : ℝ) := by
    calc
      S * D < (3 / 10 : ℝ) * D :=
        mul_lt_mul_of_pos_right hS.2 hD.1
      _ < (3 / 10 : ℝ) * (7 / 100 : ℝ) :=
        mul_lt_mul_of_pos_left hD.2 (by norm_num)
  have h04 : factorTwoIntrinsicFourP45Cross04 (-1) = (S - D) / 2 := by
    dsimp only [S, D]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  have h24 : factorTwoIntrinsicFourP45Cross24 (-1) = (S + D) / 2 := by
    dsimp only [S, D]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  constructor
  · norm_num [intrinsicStaticMinusEvenLower00, pivotShift]
  constructor
  · norm_num [leadingMinorTwo, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22,
      pivotShift]
  · rw [h04, h24]
    unfold symmetricDeterminant intrinsicStaticMinusEvenLower00
      intrinsicStaticMinusEvenLower02 intrinsicStaticMinusEvenLower22
      factorTwoIntrinsicP4MinusDiagonalLower pivotShift
    dsimp only [S, D] at hSsq hDsq hSD ⊢
    nlinarith

private theorem shifted_remainder_gates_of_quadratic_lower
    (q00 q01 q02 q11 q12 q22 l00 l01 l02 l11 l12 l22 mu : ℝ)
    (hmu : 0 < mu)
    (hlower : ∀ x0 x1 x2 : ℝ,
      symmetricQuadratic l00 l01 l02 l11 l12 l22 x0 x1 x2 ≤
        symmetricQuadratic q00 q01 q02 q11 q12 q22 x0 x1 x2) :
    0 < q00 - (l00 - mu) ∧
      0 < leadingMinorTwo
        (q00 - (l00 - mu)) (q01 - l01) (q11 - (l11 - mu)) ∧
      0 < symmetricDeterminant
        (q00 - (l00 - mu)) (q01 - l01) (q02 - l02)
        (q11 - (l11 - mu)) (q12 - l12) (q22 - (l22 - mu)) := by
  apply leadingMinors_pos_of_symmetricQuadratic_pos
  intro x0 x1 x2 hne
  have hsum : 0 < x0 ^ 2 + x1 ^ 2 + x2 ^ 2 := by
    rcases hne with hx0 | hx1 | hx2
    · exact add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx0) (sq_nonneg x1))
        (sq_nonneg x2)
    · exact add_pos_of_pos_of_nonneg
        (add_pos_of_nonneg_of_pos (sq_nonneg x0) (sq_pos_of_ne_zero hx1))
        (sq_nonneg x2)
    · exact add_pos_of_nonneg_of_pos
        (add_nonneg (sq_nonneg x0) (sq_nonneg x1))
        (sq_pos_of_ne_zero hx2)
  have hstrict : 0 < mu * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) :=
    mul_pos hmu hsum
  have hle := hlower x0 x1 x2
  unfold symmetricQuadratic at hle ⊢
  nlinarith

private theorem plus_shifted_remainder_gates :
    0 < factorTwoStructuralPhaseLow00 1 -
        (evenPositiveEndpointUltraSharp00 - pivotShift) ∧
      0 < leadingMinorTwo
        (factorTwoStructuralPhaseLow00 1 -
          (evenPositiveEndpointUltraSharp00 - pivotShift))
        (factorTwoStructuralPhaseLow02 1 - evenPositiveEndpointUltraSharp02)
        (factorTwoStructuralPhaseLow22 1 -
          (evenPositiveEndpointUltraSharp22 - pivotShift)) ∧
      0 < symmetricDeterminant
        (factorTwoStructuralPhaseLow00 1 -
          (evenPositiveEndpointUltraSharp00 - pivotShift))
        (factorTwoStructuralPhaseLow02 1 - evenPositiveEndpointUltraSharp02)
        (factorTwoIntrinsicFourP45Cross04 1 -
          factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1 -
          (evenPositiveEndpointUltraSharp22 - pivotShift))
        (factorTwoIntrinsicFourP45Cross24 1 -
          factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1 -
          ((3439 / 25000 : ℝ) - pivotShift)) := by
  refine shifted_remainder_gates_of_quadratic_lower
    (q00 := factorTwoStructuralPhaseLow00 1)
    (q01 := factorTwoStructuralPhaseLow02 1)
    (q02 := factorTwoIntrinsicFourP45Cross04 1)
    (q11 := factorTwoStructuralPhaseLow22 1)
    (q12 := factorTwoIntrinsicFourP45Cross24 1)
    (q22 := factorTwoIntrinsicSixP4Diagonal 1)
    (l00 := evenPositiveEndpointUltraSharp00)
    (l01 := evenPositiveEndpointUltraSharp02)
    (l02 := factorTwoIntrinsicFourP45Cross04 1)
    (l11 := evenPositiveEndpointUltraSharp22)
    (l12 := factorTwoIntrinsicFourP45Cross24 1)
    (l22 := (3439 / 25000 : ℝ))
    (mu := pivotShift) (by norm_num [pivotShift]) ?_
  intro x0 x1 x2
  have hbase := factorTwoIntrinsicP024PlusUltraQuadratic_le_exact x0 x1 x2
  have hdiag := plus_diagonal_lower.le
  unfold factorTwoIntrinsicP024PlusUltraQuadratic at hbase
  have hbase' :
      symmetricQuadratic
          evenPositiveEndpointUltraSharp00 evenPositiveEndpointUltraSharp02
          (factorTwoIntrinsicFourP45Cross04 1)
          evenPositiveEndpointUltraSharp22
          (factorTwoIntrinsicFourP45Cross24 1)
          (factorTwoIntrinsicSixP4Diagonal 1) x0 x1 x2 ≤
        symmetricQuadratic
          (factorTwoStructuralPhaseLow00 1) (factorTwoStructuralPhaseLow02 1)
          (factorTwoIntrinsicFourP45Cross04 1)
          (factorTwoStructuralPhaseLow22 1)
          (factorTwoIntrinsicFourP45Cross24 1)
          (factorTwoIntrinsicSixP4Diagonal 1) x0 x1 x2 := by
    simpa [factorTwoIntrinsicSixP4Diagonal, factorTwoIntrinsicP4PhaseDiagonal,
      factorTwoEndpointPhaseDiagonal] using hbase
  change symmetricQuadratic
      evenPositiveEndpointUltraSharp00 evenPositiveEndpointUltraSharp02
      (factorTwoIntrinsicFourP45Cross04 1)
      evenPositiveEndpointUltraSharp22
      (factorTwoIntrinsicFourP45Cross24 1) (3439 / 25000)
      x0 x1 x2 ≤
    symmetricQuadratic
      (factorTwoStructuralPhaseLow00 1) (factorTwoStructuralPhaseLow02 1)
      (factorTwoIntrinsicFourP45Cross04 1)
      (factorTwoStructuralPhaseLow22 1)
      (factorTwoIntrinsicFourP45Cross24 1)
      (factorTwoIntrinsicSixP4Diagonal 1) x0 x1 x2
  unfold symmetricQuadratic at hbase' ⊢
  nlinarith [sq_nonneg x2]

private theorem minus_shifted_remainder_gates :
    0 < factorTwoStructuralPhaseLow00 (-1) -
        (intrinsicStaticMinusEvenLower00 - pivotShift) ∧
      0 < leadingMinorTwo
        (factorTwoStructuralPhaseLow00 (-1) -
          (intrinsicStaticMinusEvenLower00 - pivotShift))
        (factorTwoStructuralPhaseLow02 (-1) - intrinsicStaticMinusEvenLower02)
        (factorTwoStructuralPhaseLow22 (-1) -
          (intrinsicStaticMinusEvenLower22 - pivotShift)) ∧
      0 < symmetricDeterminant
        (factorTwoStructuralPhaseLow00 (-1) -
          (intrinsicStaticMinusEvenLower00 - pivotShift))
        (factorTwoStructuralPhaseLow02 (-1) - intrinsicStaticMinusEvenLower02)
        (factorTwoIntrinsicFourP45Cross04 (-1) -
          factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1) -
          (intrinsicStaticMinusEvenLower22 - pivotShift))
        (factorTwoIntrinsicFourP45Cross24 (-1) -
          factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1) -
          (factorTwoIntrinsicP4MinusDiagonalLower - pivotShift)) := by
  refine shifted_remainder_gates_of_quadratic_lower
    (q00 := factorTwoStructuralPhaseLow00 (-1))
    (q01 := factorTwoStructuralPhaseLow02 (-1))
    (q02 := factorTwoIntrinsicFourP45Cross04 (-1))
    (q11 := factorTwoStructuralPhaseLow22 (-1))
    (q12 := factorTwoIntrinsicFourP45Cross24 (-1))
    (q22 := factorTwoIntrinsicSixP4Diagonal (-1))
    (l00 := intrinsicStaticMinusEvenLower00)
    (l01 := intrinsicStaticMinusEvenLower02)
    (l02 := factorTwoIntrinsicFourP45Cross04 (-1))
    (l11 := intrinsicStaticMinusEvenLower22)
    (l12 := factorTwoIntrinsicFourP45Cross24 (-1))
    (l22 := factorTwoIntrinsicP4MinusDiagonalLower)
    (mu := pivotShift) (by norm_num [pivotShift]) ?_
  intro x0 x1 x2
  have h := factorTwoIntrinsicP024MinusLowerQuadratic_le_exact x0 x1 x2
  unfold factorTwoIntrinsicP024MinusLowerQuadratic at h
  simpa [factorTwoIntrinsicSixP4Diagonal, factorTwoIntrinsicP4PhaseDiagonal,
    factorTwoEndpointPhaseDiagonal] using h

private def plusExactMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoStructuralPhaseLow00 1)
    (factorTwoStructuralPhaseLow02 1)
    (factorTwoIntrinsicFourP45Cross04 1)
    (factorTwoStructuralPhaseLow22 1)
    (factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicSixP4Diagonal 1)

private def minusExactMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoStructuralPhaseLow00 (-1))
    (factorTwoStructuralPhaseLow02 (-1))
    (factorTwoIntrinsicFourP45Cross04 (-1))
    (factorTwoStructuralPhaseLow22 (-1))
    (factorTwoIntrinsicFourP45Cross24 (-1))
    (factorTwoIntrinsicSixP4Diagonal (-1))

private def plusShiftedLowerMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (evenPositiveEndpointUltraSharp00 - pivotShift)
    evenPositiveEndpointUltraSharp02
    (factorTwoIntrinsicFourP45Cross04 1)
    (evenPositiveEndpointUltraSharp22 - pivotShift)
    (factorTwoIntrinsicFourP45Cross24 1)
    ((3439 / 25000 : ℝ) - pivotShift)

private def minusShiftedLowerMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (intrinsicStaticMinusEvenLower00 - pivotShift)
    intrinsicStaticMinusEvenLower02
    (factorTwoIntrinsicFourP45Cross04 (-1))
    (intrinsicStaticMinusEvenLower22 - pivotShift)
    (factorTwoIntrinsicFourP45Cross24 (-1))
    (factorTwoIntrinsicP4MinusDiagonalLower - pivotShift)

private def plusShiftedRemainderMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoStructuralPhaseLow00 1 -
      (evenPositiveEndpointUltraSharp00 - pivotShift))
    (factorTwoStructuralPhaseLow02 1 - evenPositiveEndpointUltraSharp02)
    (factorTwoIntrinsicFourP45Cross04 1 - factorTwoIntrinsicFourP45Cross04 1)
    (factorTwoStructuralPhaseLow22 1 -
      (evenPositiveEndpointUltraSharp22 - pivotShift))
    (factorTwoIntrinsicFourP45Cross24 1 - factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicSixP4Diagonal 1 -
      ((3439 / 25000 : ℝ) - pivotShift))

private def minusShiftedRemainderMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoStructuralPhaseLow00 (-1) -
      (intrinsicStaticMinusEvenLower00 - pivotShift))
    (factorTwoStructuralPhaseLow02 (-1) - intrinsicStaticMinusEvenLower02)
    (factorTwoIntrinsicFourP45Cross04 (-1) -
      factorTwoIntrinsicFourP45Cross04 (-1))
    (factorTwoStructuralPhaseLow22 (-1) -
      (intrinsicStaticMinusEvenLower22 - pivotShift))
    (factorTwoIntrinsicFourP45Cross24 (-1) -
      factorTwoIntrinsicFourP45Cross24 (-1))
    (factorTwoIntrinsicSixP4Diagonal (-1) -
      (factorTwoIntrinsicP4MinusDiagonalLower - pivotShift))

private theorem plusExactMatrix_eq_add :
    plusExactMatrix = plusShiftedLowerMatrix + plusShiftedRemainderMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusExactMatrix, plusShiftedLowerMatrix,
      plusShiftedRemainderMatrix, symmetricMatrix3]

private theorem minusExactMatrix_eq_add :
    minusExactMatrix = minusShiftedLowerMatrix + minusShiftedRemainderMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusExactMatrix, minusShiftedLowerMatrix,
      minusShiftedRemainderMatrix, symmetricMatrix3]

private theorem plusShiftedLowerMatrix_posDef : plusShiftedLowerMatrix.PosDef := by
  exact symmetricMatrix3_posDef _ _ _ _ _ _
    plus_lower_shifted_gates.1 plus_lower_shifted_gates.2.1
    plus_lower_shifted_gates.2.2

private theorem minusShiftedLowerMatrix_posDef : minusShiftedLowerMatrix.PosDef := by
  exact symmetricMatrix3_posDef _ _ _ _ _ _
    minus_lower_shifted_gates.1 minus_lower_shifted_gates.2.1
    minus_lower_shifted_gates.2.2

private theorem plusShiftedRemainderMatrix_posDef :
    plusShiftedRemainderMatrix.PosDef := by
  exact symmetricMatrix3_posDef _ _ _ _ _ _
    plus_shifted_remainder_gates.1 plus_shifted_remainder_gates.2.1
    plus_shifted_remainder_gates.2.2

private theorem minusShiftedRemainderMatrix_posDef :
    minusShiftedRemainderMatrix.PosDef := by
  exact symmetricMatrix3_posDef _ _ _ _ _ _
    minus_shifted_remainder_gates.1 minus_shifted_remainder_gates.2.1
    minus_shifted_remainder_gates.2.2

private theorem shifted_lower_mixed_one_lt_exact :
    mixedDeterminantOne
        (evenPositiveEndpointUltraSharp00 - pivotShift)
        evenPositiveEndpointUltraSharp02
        (factorTwoIntrinsicFourP45Cross04 1)
        (evenPositiveEndpointUltraSharp22 - pivotShift)
        (factorTwoIntrinsicFourP45Cross24 1)
        ((3439 / 25000 : ℝ) - pivotShift)
        (intrinsicStaticMinusEvenLower00 - pivotShift)
        intrinsicStaticMinusEvenLower02
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (intrinsicStaticMinusEvenLower22 - pivotShift)
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicP4MinusDiagonalLower - pivotShift) <
      mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1)) := by
  have h := matrixMixedDeterminantOne_add_add_gt
    plusShiftedLowerMatrix_posDef plusShiftedRemainderMatrix_posDef
    minusShiftedLowerMatrix_posDef minusShiftedRemainderMatrix_posDef
  rw [← plusExactMatrix_eq_add, ← minusExactMatrix_eq_add] at h
  simpa [plusShiftedLowerMatrix, minusShiftedLowerMatrix,
    plusExactMatrix, minusExactMatrix,
    matrixMixedDeterminantOne_symmetricMatrix3] using h

private theorem shifted_lower_mixed_two_lt_exact :
    mixedDeterminantOne
        (intrinsicStaticMinusEvenLower00 - pivotShift)
        intrinsicStaticMinusEvenLower02
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (intrinsicStaticMinusEvenLower22 - pivotShift)
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicP4MinusDiagonalLower - pivotShift)
        (evenPositiveEndpointUltraSharp00 - pivotShift)
        evenPositiveEndpointUltraSharp02
        (factorTwoIntrinsicFourP45Cross04 1)
        (evenPositiveEndpointUltraSharp22 - pivotShift)
        (factorTwoIntrinsicFourP45Cross24 1)
        ((3439 / 25000 : ℝ) - pivotShift) <
      mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1) := by
  have h := matrixMixedDeterminantOne_add_add_gt
    minusShiftedLowerMatrix_posDef minusShiftedRemainderMatrix_posDef
    plusShiftedLowerMatrix_posDef plusShiftedRemainderMatrix_posDef
  rw [← minusExactMatrix_eq_add, ← plusExactMatrix_eq_add] at h
  simpa [plusShiftedLowerMatrix, minusShiftedLowerMatrix,
    plusExactMatrix, minusExactMatrix,
    matrixMixedDeterminantOne_symmetricMatrix3] using h

private theorem shifted_lower_mixed_one_gt :
    (1 / 15000 : ℝ) < mixedDeterminantOne
      (evenPositiveEndpointUltraSharp00 - pivotShift)
      evenPositiveEndpointUltraSharp02
      (factorTwoIntrinsicFourP45Cross04 1)
      (evenPositiveEndpointUltraSharp22 - pivotShift)
      (factorTwoIntrinsicFourP45Cross24 1)
      ((3439 / 25000 : ℝ) - pivotShift)
      (intrinsicStaticMinusEvenLower00 - pivotShift)
      intrinsicStaticMinusEvenLower02
      (factorTwoIntrinsicFourP45Cross04 (-1))
      (intrinsicStaticMinusEvenLower22 - pivotShift)
      (factorTwoIntrinsicFourP45Cross24 (-1))
      (factorTwoIntrinsicP4MinusDiagonalLower - pivotShift) := by
  let Sp : ℝ := factorTwoIntrinsicP4PlusCrossSum
  let Dp : ℝ := factorTwoIntrinsicP4PlusCrossDifference
  let Sm : ℝ := factorTwoIntrinsicP4MinusCrossSum
  let Dm : ℝ := factorTwoIntrinsicP4MinusCrossDifference
  have hpS : 0 < Sp ∧ Sp < (193 / 1000 : ℝ) := by
    simpa only [Sp] using factorTwoIntrinsicP4PlusCrossSum_bounds
  have hpD : 0 < Dp ∧ Dp < (39 / 2000 : ℝ) := by
    simpa only [Dp] using factorTwoIntrinsicP4PlusCrossDifference_bounds
  have hm := factorTwoIntrinsicP4MinusCross_sum_difference_bounds
  have hmS : 0 < Sm ∧ Sm < (3 / 10 : ℝ) := by
    simpa only [Sm] using ⟨hm.1, hm.2.1⟩
  have hmD : 0 < Dm ∧ Dm < (7 / 100 : ℝ) := by
    simpa only [Dm] using ⟨hm.2.2.1, hm.2.2.2⟩
  have hpSsq : Sp ^ 2 < (193 / 1000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hpS.2 hpS.1.le (by norm_num)
  have hpDsq : Dp ^ 2 < (39 / 2000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hpD.2 hpD.1.le (by norm_num)
  have hpSD : Sp * Dp < (193 / 1000 : ℝ) * (39 / 2000 : ℝ) := by
    calc
      Sp * Dp < (193 / 1000 : ℝ) * Dp :=
        mul_lt_mul_of_pos_right hpS.2 hpD.1
      _ < (193 / 1000 : ℝ) * (39 / 2000 : ℝ) :=
        mul_lt_mul_of_pos_left hpD.2 (by norm_num)
  have hpD_mD : Dp * Dm < (39 / 2000 : ℝ) * (7 / 100 : ℝ) := by
    calc
      Dp * Dm < (39 / 2000 : ℝ) * Dm :=
        mul_lt_mul_of_pos_right hpD.2 hmD.1
      _ < (39 / 2000 : ℝ) * (7 / 100 : ℝ) :=
        mul_lt_mul_of_pos_left hmD.2 (by norm_num)
  have hpD_mS : Dp * Sm < (39 / 2000 : ℝ) * (3 / 10 : ℝ) := by
    calc
      Dp * Sm < (39 / 2000 : ℝ) * Sm :=
        mul_lt_mul_of_pos_right hpD.2 hmS.1
      _ < (39 / 2000 : ℝ) * (3 / 10 : ℝ) :=
        mul_lt_mul_of_pos_left hmS.2 (by norm_num)
  have hpS_mD : Sp * Dm < (193 / 1000 : ℝ) * (7 / 100 : ℝ) := by
    calc
      Sp * Dm < (193 / 1000 : ℝ) * Dm :=
        mul_lt_mul_of_pos_right hpS.2 hmD.1
      _ < (193 / 1000 : ℝ) * (7 / 100 : ℝ) :=
        mul_lt_mul_of_pos_left hmD.2 (by norm_num)
  have hpS_mS : Sp * Sm < (193 / 1000 : ℝ) * (3 / 10 : ℝ) := by
    calc
      Sp * Sm < (193 / 1000 : ℝ) * Sm :=
        mul_lt_mul_of_pos_right hpS.2 hmS.1
      _ < (193 / 1000 : ℝ) * (3 / 10 : ℝ) :=
        mul_lt_mul_of_pos_left hmS.2 (by norm_num)
  have hp04 : factorTwoIntrinsicFourP45Cross04 1 = (Sp - Dp) / 2 := by
    dsimp only [Sp, Dp]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  have hp24 : factorTwoIntrinsicFourP45Cross24 1 = (Sp + Dp) / 2 := by
    dsimp only [Sp, Dp]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  have hm04 : factorTwoIntrinsicFourP45Cross04 (-1) = (Sm - Dm) / 2 := by
    dsimp only [Sm, Dm]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  have hm24 : factorTwoIntrinsicFourP45Cross24 (-1) = (Sm + Dm) / 2 := by
    dsimp only [Sm, Dm]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  rw [hp04, hp24, hm04, hm24]
  unfold mixedDeterminantOne evenPositiveEndpointUltraSharp00
    evenPositiveEndpointUltraSharp02 evenPositiveEndpointUltraSharp22
    intrinsicStaticMinusEvenLower00 intrinsicStaticMinusEvenLower02
    intrinsicStaticMinusEvenLower22 factorTwoIntrinsicP4MinusDiagonalLower
    pivotShift
  dsimp only [Sp, Dp, Sm, Dm] at hpSsq hpDsq hpSD hpD_mD hpD_mS hpS_mD hpS_mS ⊢
  nlinarith

private theorem shifted_lower_mixed_two_gt :
    (1 / 5000 : ℝ) < mixedDeterminantOne
      (intrinsicStaticMinusEvenLower00 - pivotShift)
      intrinsicStaticMinusEvenLower02
      (factorTwoIntrinsicFourP45Cross04 (-1))
      (intrinsicStaticMinusEvenLower22 - pivotShift)
      (factorTwoIntrinsicFourP45Cross24 (-1))
      (factorTwoIntrinsicP4MinusDiagonalLower - pivotShift)
      (evenPositiveEndpointUltraSharp00 - pivotShift)
      evenPositiveEndpointUltraSharp02
      (factorTwoIntrinsicFourP45Cross04 1)
      (evenPositiveEndpointUltraSharp22 - pivotShift)
      (factorTwoIntrinsicFourP45Cross24 1)
      ((3439 / 25000 : ℝ) - pivotShift) := by
  let Sp : ℝ := factorTwoIntrinsicP4PlusCrossSum
  let Dp : ℝ := factorTwoIntrinsicP4PlusCrossDifference
  let Sm : ℝ := factorTwoIntrinsicP4MinusCrossSum
  let Dm : ℝ := factorTwoIntrinsicP4MinusCrossDifference
  have hpS : 0 < Sp ∧ Sp < (193 / 1000 : ℝ) := by
    simpa only [Sp] using factorTwoIntrinsicP4PlusCrossSum_bounds
  have hpD : 0 < Dp ∧ Dp < (39 / 2000 : ℝ) := by
    simpa only [Dp] using factorTwoIntrinsicP4PlusCrossDifference_bounds
  have hm := factorTwoIntrinsicP4MinusCross_sum_difference_bounds
  have hmS : 0 < Sm ∧ Sm < (3 / 10 : ℝ) := by
    simpa only [Sm] using ⟨hm.1, hm.2.1⟩
  have hmD : 0 < Dm ∧ Dm < (7 / 100 : ℝ) := by
    simpa only [Dm] using ⟨hm.2.2.1, hm.2.2.2⟩
  have hmSsq : Sm ^ 2 < (3 / 10 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hmS.2 hmS.1.le (by norm_num)
  have hmDsq : Dm ^ 2 < (7 / 100 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hmD.2 hmD.1.le (by norm_num)
  have hmSD : Sm * Dm < (3 / 10 : ℝ) * (7 / 100 : ℝ) := by
    calc
      Sm * Dm < (3 / 10 : ℝ) * Dm :=
        mul_lt_mul_of_pos_right hmS.2 hmD.1
      _ < (3 / 10 : ℝ) * (7 / 100 : ℝ) :=
        mul_lt_mul_of_pos_left hmD.2 (by norm_num)
  have hpD_mD : Dp * Dm < (39 / 2000 : ℝ) * (7 / 100 : ℝ) := by
    calc
      Dp * Dm < (39 / 2000 : ℝ) * Dm :=
        mul_lt_mul_of_pos_right hpD.2 hmD.1
      _ < (39 / 2000 : ℝ) * (7 / 100 : ℝ) :=
        mul_lt_mul_of_pos_left hmD.2 (by norm_num)
  have hpD_mS : Dp * Sm < (39 / 2000 : ℝ) * (3 / 10 : ℝ) := by
    calc
      Dp * Sm < (39 / 2000 : ℝ) * Sm :=
        mul_lt_mul_of_pos_right hpD.2 hmS.1
      _ < (39 / 2000 : ℝ) * (3 / 10 : ℝ) :=
        mul_lt_mul_of_pos_left hmS.2 (by norm_num)
  have hpS_mD : Sp * Dm < (193 / 1000 : ℝ) * (7 / 100 : ℝ) := by
    calc
      Sp * Dm < (193 / 1000 : ℝ) * Dm :=
        mul_lt_mul_of_pos_right hpS.2 hmD.1
      _ < (193 / 1000 : ℝ) * (7 / 100 : ℝ) :=
        mul_lt_mul_of_pos_left hmD.2 (by norm_num)
  have hpS_mS : Sp * Sm < (193 / 1000 : ℝ) * (3 / 10 : ℝ) := by
    calc
      Sp * Sm < (193 / 1000 : ℝ) * Sm :=
        mul_lt_mul_of_pos_right hpS.2 hmS.1
      _ < (193 / 1000 : ℝ) * (3 / 10 : ℝ) :=
        mul_lt_mul_of_pos_left hmS.2 (by norm_num)
  have hp04 : factorTwoIntrinsicFourP45Cross04 1 = (Sp - Dp) / 2 := by
    dsimp only [Sp, Dp]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  have hp24 : factorTwoIntrinsicFourP45Cross24 1 = (Sp + Dp) / 2 := by
    dsimp only [Sp, Dp]
    unfold factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
    ring
  have hm04 : factorTwoIntrinsicFourP45Cross04 (-1) = (Sm - Dm) / 2 := by
    dsimp only [Sm, Dm]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  have hm24 : factorTwoIntrinsicFourP45Cross24 (-1) = (Sm + Dm) / 2 := by
    dsimp only [Sm, Dm]
    unfold factorTwoIntrinsicP4MinusCrossSum
      factorTwoIntrinsicP4MinusCrossDifference
    ring
  rw [hp04, hp24, hm04, hm24]
  unfold mixedDeterminantOne evenPositiveEndpointUltraSharp00
    evenPositiveEndpointUltraSharp02 evenPositiveEndpointUltraSharp22
    intrinsicStaticMinusEvenLower00 intrinsicStaticMinusEvenLower02
    intrinsicStaticMinusEvenLower22 factorTwoIntrinsicP4MinusDiagonalLower
    pivotShift
  dsimp only [Sp, Dp, Sm, Dm] at hmSsq hmDsq hmSD hpD_mD hpD_mS hpS_mD hpS_mS ⊢
  nlinarith

private theorem p4PivotCoefficientPolynomial_expansion :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial =
      C (symmetricDeterminant
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)) +
      C (mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))) * X +
      C (mixedDeterminantOne
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))
        (factorTwoStructuralPhaseLow00 1)
        (factorTwoStructuralPhaseLow02 1)
        (factorTwoIntrinsicFourP45Cross04 1)
        (factorTwoStructuralPhaseLow22 1)
        (factorTwoIntrinsicFourP45Cross24 1)
        (factorTwoIntrinsicSixP4Diagonal 1)) * X ^ 2 +
      C (symmetricDeterminant
        (factorTwoStructuralPhaseLow00 (-1))
        (factorTwoStructuralPhaseLow02 (-1))
        (factorTwoIntrinsicFourP45Cross04 (-1))
        (factorTwoStructuralPhaseLow22 (-1))
        (factorTwoIntrinsicFourP45Cross24 (-1))
        (factorTwoIntrinsicSixP4Diagonal (-1))) * X ^ 3 := by
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial mixedDeterminantOne symmetricDeterminant
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

private theorem pivotCoeff_one_eq_exact_mixed :
    pivotCoeff 1 = mixedDeterminantOne
      (factorTwoStructuralPhaseLow00 1)
      (factorTwoStructuralPhaseLow02 1)
      (factorTwoIntrinsicFourP45Cross04 1)
      (factorTwoStructuralPhaseLow22 1)
      (factorTwoIntrinsicFourP45Cross24 1)
      (factorTwoIntrinsicSixP4Diagonal 1)
      (factorTwoStructuralPhaseLow00 (-1))
      (factorTwoStructuralPhaseLow02 (-1))
      (factorTwoIntrinsicFourP45Cross04 (-1))
      (factorTwoStructuralPhaseLow22 (-1))
      (factorTwoIntrinsicFourP45Cross24 (-1))
      (factorTwoIntrinsicSixP4Diagonal (-1)) := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 1 = _
  rw [p4PivotCoefficientPolynomial_expansion]
  simp

private theorem pivotCoeff_two_eq_exact_mixed :
    pivotCoeff 2 = mixedDeterminantOne
      (factorTwoStructuralPhaseLow00 (-1))
      (factorTwoStructuralPhaseLow02 (-1))
      (factorTwoIntrinsicFourP45Cross04 (-1))
      (factorTwoStructuralPhaseLow22 (-1))
      (factorTwoIntrinsicFourP45Cross24 (-1))
      (factorTwoIntrinsicSixP4Diagonal (-1))
      (factorTwoStructuralPhaseLow00 1)
      (factorTwoStructuralPhaseLow02 1)
      (factorTwoIntrinsicFourP45Cross04 1)
      (factorTwoStructuralPhaseLow22 1)
      (factorTwoIntrinsicFourP45Cross24 1)
      (factorTwoIntrinsicSixP4Diagonal 1) := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 2 = _
  rw [p4PivotCoefficientPolynomial_expansion]
  simp

/-- A quantitative structural reserve for the first mixed projective
`P0/P2/P4` determinant coefficient. -/
theorem pivotCoeff_one_gt_one_div_fifteen_thousand :
    (1 / 15000 : ℝ) < pivotCoeff 1 := by
  rw [pivotCoeff_one_eq_exact_mixed]
  exact shifted_lower_mixed_one_gt.trans shifted_lower_mixed_one_lt_exact

/-- A quantitative structural reserve for the reverse mixed projective
`P0/P2/P4` determinant coefficient. -/
theorem pivotCoeff_two_gt_one_div_five_thousand :
    (1 / 5000 : ℝ) < pivotCoeff 2 := by
  rw [pivotCoeff_two_eq_exact_mixed]
  exact shifted_lower_mixed_two_gt.trans shifted_lower_mixed_two_lt_exact

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural
