import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5CleanSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural

noncomputable section

open YoshidaFactorTwoEndpointBilinear
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP5CleanSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural odd `P5` endpoint diagonals

The sharp clean reserve and the signed perturbation box combine directly in
the affine endpoint pencil.  No endpoint diagonal is evaluated.
-/

private theorem fourteen_fifty_fifths_le_clean_p5 :
    (14 / 55 : ℝ) ≤
      yoshidaEndpointOddCleanQuadratic factorTwoCenteredP5 := by
  have hclean := seven_fifths_energy_le_clean_P5
  have henergy :
      factorTwoIntrinsicEnergy factorTwoCenteredP5 = (2 / 11 : ℝ) := by
    simpa [factorTwoIntrinsicEnergy] using integral_factorTwoCenteredP5_sq
  rw [henergy] at hclean
  norm_num at hclean ⊢
  exact hclean

/-- The plus-endpoint `P5` diagonal retains the reserve needed by the odd
`3 x 3` determinant. -/
theorem three_hundred_forty_three_two_thousandths_lt_p5_plus :
    (343 / 2000 : ℝ) < factorTwoIntrinsicSixP5Diagonal 1 := by
  have hclean := fourteen_fifty_fifths_le_clean_p5
  have hpert :=
    neg_eighty_three_thousandths_lt_factorTwoCenteredSymmetricPerturbation_p5
  unfold factorTwoIntrinsicSixP5Diagonal factorTwoEndpointPhaseDiagonal
  norm_num at *
  linarith

/-- Negativity of the perturbation strengthens the minus-endpoint clean
reserve strictly. -/
theorem fourteen_fifty_fifths_lt_p5_minus :
    (14 / 55 : ℝ) < factorTwoIntrinsicSixP5Diagonal (-1) := by
  have hclean := fourteen_fifty_fifths_le_clean_p5
  have hpert := factorTwoCenteredSymmetricPerturbation_p5_neg
  unfold factorTwoIntrinsicSixP5Diagonal factorTwoEndpointPhaseDiagonal
  norm_num at *
  linarith

/-- Both endpoint diagonal reserves, packaged for odd-matrix assembly. -/
theorem factorTwoIntrinsicSixP5_endpoint_diagonal_bounds :
    (343 / 2000 : ℝ) < factorTwoIntrinsicSixP5Diagonal 1 ∧
      (14 / 55 : ℝ) < factorTwoIntrinsicSixP5Diagonal (-1) :=
  ⟨three_hundred_forty_three_two_thousandths_lt_p5_plus,
    fourteen_fifty_fifths_lt_p5_minus⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5EndpointDiagonalStructural
