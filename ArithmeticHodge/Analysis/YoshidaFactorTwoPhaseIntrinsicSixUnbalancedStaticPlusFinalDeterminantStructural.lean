import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusFinalDeterminantStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# The last positive static Schur determinant

The complete six-variable static-plus form is already strictly positive.
Evaluating it at the fraction-free Schur minimizer turns that fact into strict
positivity of the final odd `3 × 3` determinant.  No entrywise enclosure or
new analytic estimate is used here.
-/

private def plusTDetEll0 (c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedKPlus01 * c1 +
    factorTwoIntrinsicSixUnbalancedKPlus03 * c3 +
    factorTwoIntrinsicSixUnbalancedKPlus05 * c5

private def plusTDetEll2 (c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedKPlus21 * c1 +
    factorTwoIntrinsicSixUnbalancedKPlus23 * c3 +
    factorTwoIntrinsicSixUnbalancedKPlus25 * c5

private def plusTDetEll4 (c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedKPlus41 * c1 +
    factorTwoIntrinsicSixUnbalancedKPlus43 * c3 +
    factorTwoIntrinsicSixUnbalancedKPlus45 * c5

private def plusTDetAdjugateVector
    (c1 c3 c5 : ℝ) (i : Fin 3) : ℝ :=
  adjugateVector
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (plusTDetEll0 c1 c3 c5) (plusTDetEll2 c1 c3 c5)
    (plusTDetEll4 c1 c3 c5) i

/-- Exact specialization of the six-variable form at the adjugate Schur
minimizer.  This is Cramer's rule with all denominators cleared. -/
private theorem plusTDetExactSix_adjugate_specialization
    (c1 c3 c5 : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorPlusExactSixQuadratic
        (-plusTDetAdjugateVector c1 c3 c5 0)
        (-plusTDetAdjugateVector c1 c3 c5 1)
        (-plusTDetAdjugateVector c1 c3 c5 2)
        (factorTwoIntrinsicSixUnbalancedEPlusDet * c1)
        (factorTwoIntrinsicSixUnbalancedEPlusDet * c3)
        (factorTwoIntrinsicSixUnbalancedEPlusDet * c5) =
      factorTwoIntrinsicSixUnbalancedEPlusDet *
        factorTwoIntrinsicSixUnbalancedTPlusQuadratic c1 c3 c5 := by
  rw [factorTwoIntrinsicSixUnbalancedMinorPlusExactSixQuadratic_eq_staticPlus,
    factorTwoIntrinsicSixUnbalancedStaticPlus_eq_block,
    factorTwoIntrinsicSixUnbalancedTPlusQuadratic_eq_fractionFree]
  unfold plusTDetAdjugateVector plusTDetEll0 plusTDetEll2 plusTDetEll4
  simp only [adjugateVector]
  unfold factorTwoIntrinsicSixUnbalancedEPlusDet symmetricQuadratic
    symmetricDeterminant adjugateQuadratic
  ring

/-- The standard last-column witness evaluates a symmetric `3 × 3`
quadratic form to its leading `2 × 2` minor times its determinant. -/
private theorem plusTDetQuadratic_determinant_witness :
    factorTwoIntrinsicSixUnbalancedTPlusQuadratic
        (factorTwoIntrinsicSixUnbalancedTPlus13 *
            factorTwoIntrinsicSixUnbalancedTPlus35 -
          factorTwoIntrinsicSixUnbalancedTPlus33 *
            factorTwoIntrinsicSixUnbalancedTPlus15)
        (factorTwoIntrinsicSixUnbalancedTPlus13 *
            factorTwoIntrinsicSixUnbalancedTPlus15 -
          factorTwoIntrinsicSixUnbalancedTPlus11 *
            factorTwoIntrinsicSixUnbalancedTPlus35)
        factorTwoIntrinsicSixUnbalancedTPlusMinor =
      factorTwoIntrinsicSixUnbalancedTPlusMinor *
        factorTwoIntrinsicSixUnbalancedTPlusDet := by
  unfold factorTwoIntrinsicSixUnbalancedTPlusQuadratic
    factorTwoIntrinsicSixUnbalancedTPlusMinor
    factorTwoIntrinsicSixUnbalancedTPlusDet leadingMinorTwo
    symmetricQuadratic symmetricDeterminant
  ring

/-- The final positive static fraction-free Schur block has strictly positive
determinant. -/
theorem factorTwoIntrinsicSixUnbalancedTPlusDet_pos :
    0 < factorTwoIntrinsicSixUnbalancedTPlusDet := by
  let d : ℝ := factorTwoIntrinsicSixUnbalancedEPlusDet
  let p : ℝ :=
    factorTwoIntrinsicSixUnbalancedTPlus13 *
        factorTwoIntrinsicSixUnbalancedTPlus35 -
      factorTwoIntrinsicSixUnbalancedTPlus33 *
        factorTwoIntrinsicSixUnbalancedTPlus15
  let q : ℝ :=
    factorTwoIntrinsicSixUnbalancedTPlus13 *
        factorTwoIntrinsicSixUnbalancedTPlus15 -
      factorTwoIntrinsicSixUnbalancedTPlus11 *
        factorTwoIntrinsicSixUnbalancedTPlus35
  let m : ℝ := factorTwoIntrinsicSixUnbalancedTPlusMinor
  have hd : 0 < d := by
    simpa only [d] using factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2
  have hm : 0 < m := by
    simpa only [m] using factorTwoIntrinsicSixUnbalancedTPlusMinor_pos
  have hne :
      -plusTDetAdjugateVector p q m 0 ≠ 0 ∨
        -plusTDetAdjugateVector p q m 1 ≠ 0 ∨
        -plusTDetAdjugateVector p q m 2 ≠ 0 ∨
        d * p ≠ 0 ∨ d * q ≠ 0 ∨ d * m ≠ 0 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (mul_ne_zero hd.ne' hm.ne')))))
  have hquad :=
    factorTwoIntrinsicSixUnbalancedMinorPlusExactSix_pos
      (-plusTDetAdjugateVector p q m 0)
      (-plusTDetAdjugateVector p q m 1)
      (-plusTDetAdjugateVector p q m 2)
      (d * p) (d * q) (d * m) hne
  have hspecial := plusTDetExactSix_adjugate_specialization p q m
  dsimp only [d] at hspecial hquad
  rw [hspecial] at hquad
  dsimp only [p, q, m] at hquad
  rw [plusTDetQuadratic_determinant_witness] at hquad
  have hminorDet :
      0 < factorTwoIntrinsicSixUnbalancedTPlusMinor *
        factorTwoIntrinsicSixUnbalancedTPlusDet :=
    pos_of_mul_pos_right hquad
      factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2.le
  exact pos_of_mul_pos_right hminorDet
    factorTwoIntrinsicSixUnbalancedTPlusMinor_pos.le

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusFinalDeterminantStructural
