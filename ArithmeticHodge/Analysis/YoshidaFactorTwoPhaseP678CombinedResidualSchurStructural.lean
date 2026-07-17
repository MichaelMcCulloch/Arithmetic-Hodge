import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67CombinedForwardSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8ForwardSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseWeightedFiniteSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural

open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseP67CombinedForwardSchurStructural
open YoshidaFactorTwoPhaseP67ResidualPolynomialCancellationStructural
open YoshidaFactorTwoPhaseP8ForwardSchurStructural
open YoshidaFactorTwoPhaseWeightedFiniteSchurStructural

noncomputable section

/-!
# The complete cutoff-nine residual Schur closure

The retained `P6/P7` border is one aggregate cell.  Adjoining `P8` adds
three cells: even ordinary energy, odd ordinary energy, and odd endpoint
potential.  Their normalized weights are respectively

* `5 / 6`;
* `7 / 16896`;
* `1 / 132`;
* `17 / 528`.

Their sum is strictly below one.  The finite weighted Schur lemma therefore
closes the whole border without enumerating residual modes.
-/

/-- The complete analytic plus forward-Hankel half-cross for the scaled
`P6/P7/P8` low block. -/
def factorTwoP678ResidualCombinedForwardMixed
    (eR oR : ℝ → ℝ) (c d f a b : ℝ) : ℝ :=
  factorTwoP67ResidualCombinedForwardMixed
      (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
      eR oR a b +
    factorTwoP8ResidualCombinedForwardMixed eR oR f a b

/-- The four structural residual cells close inside the combined retained
`P6/P7/P8` phase reserve. -/
theorem factorTwoP678ResidualCombinedForwardMixed_sq_le_reserve_mul
    (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (heLow : centeredLegendreMomentsVanishBelow eR 9)
    (hoLow : centeredLegendreMomentsVanishBelow oR 9)
    (c d f a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoP678ResidualCombinedForwardMixed eR oR c d f a b ^ 2 ≤
      (((1 / 100 : ℝ) *
          (factorTwoIntrinsicEnergy factorTwoCenteredP6 * c ^ 2 +
            factorTwoIntrinsicEnergy factorTwoCenteredP7 * d ^ 2)) +
        ((33 / 100 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP8 * f ^ 2)) *
      ((1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR +
        (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR +
        (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy oR) := by
  let XP67 : ℝ := (1 / 100 : ℝ) *
    (factorTwoIntrinsicEnergy factorTwoCenteredP6 * c ^ 2 +
      factorTwoIntrinsicEnergy factorTwoCenteredP7 * d ^ 2)
  let X8 : ℝ := (33 / 100 : ℝ) *
    factorTwoIntrinsicEnergy factorTwoCenteredP8 * f ^ 2
  let yE : ℝ := (1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR
  let yO : ℝ := (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR
  let yPot : ℝ := (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy oR

  let z67 : ℝ := factorTwoP67ResidualCombinedForwardMixed
    (c • factorTwoCenteredP6) (d • factorTwoCenteredP7) eR oR a b
  let z8E : ℝ := factorTwoP8ResidualEvenAnalyticKCell eR f a
  let z8O : ℝ := factorTwoP8ResidualOddAnalyticCell oR f b
  let z8Pot : ℝ := factorTwoP8ResidualOddForwardPotentialCell oR f b

  have hXP67 : 0 ≤ XP67 := by
    dsimp only [XP67]
    exact mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg (factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP6)
        (sq_nonneg c))
      (mul_nonneg (factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP7)
        (sq_nonneg d)))
  have hX8 : 0 ≤ X8 := by
    dsimp only [X8]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP8))
      (sq_nonneg f)
  have hyE : 0 ≤ yE := by
    dsimp only [yE]
    exact mul_nonneg (by norm_num) (factorTwoIntrinsicEnergy_nonneg eR)
  have hyO : 0 ≤ yO := by
    dsimp only [yO]
    exact mul_nonneg (by norm_num) (factorTwoIntrinsicEnergy_nonneg oR)
  have hyPot : 0 ≤ yPot := by
    dsimp only [yPot]
    exact mul_nonneg (by norm_num)
      (factorTwoIntrinsicPotentialEnergy_nonneg oR)

  have hz67 : z67 ^ 2 ≤ (5 / 6 : ℝ) * (XP67 * (yE + yO)) := by
    simpa only [z67, XP67, yE, yO] using
      factorTwoP67ResidualCombinedForwardMixed_sq_le_five_six_mul_reserve_mul
        eR oR heRc hoRc heRe hoRo heLow hoLow c d a b hab
  have hz8E : z8E ^ 2 ≤ (7 / 16896 : ℝ) * (X8 * yE) := by
    have h := factorTwoP8ResidualEvenAnalyticKCell_sq_le
      eR heRc heLow f a b hab
    simpa only [z8E, X8, yE, mul_assoc] using h
  have hz8O : z8O ^ 2 ≤ (1 / 132 : ℝ) * (X8 * yO) := by
    have h := factorTwoP8ResidualOddAnalyticCell_sq_le
      oR hoRc hoRo f a b hab
    simpa only [z8O, X8, yO, mul_assoc] using h
  have hz8Pot : z8Pot ^ 2 ≤ (17 / 528 : ℝ) * (X8 * yPot) := by
    have h := factorTwoP8ResidualOddForwardPotentialCell_sq_le
      oR hoRc hoLow f a b hab
    simpa only [z8Pot, X8, yPot, mul_assoc] using h

  let weights : Fin 4 → ℝ :=
    ![(5 / 6 : ℝ), (7 / 16896 : ℝ), (1 / 132 : ℝ), (17 / 528 : ℝ)]
  let cells : Fin 4 → ℝ := ![z67, z8E, z8O, z8Pot]
  let masses : Fin 4 → ℝ :=
    ![XP67 * (yE + yO), X8 * yE, X8 * yO, X8 * yPot]

  have hschur :
      (∑ i : Fin 4, cells i) ^ 2 ≤
        (XP67 + X8) * (yE + yO + yPot) := by
    apply finset_schur_of_normalized_sq_bounds
      (Finset.univ : Finset (Fin 4)) weights cells masses
      ((XP67 + X8) * (yE + yO + yPot))
    · intro i _hi
      fin_cases i <;> norm_num [weights]
    · norm_num [weights, Fin.sum_univ_succ]
    · intro i _hi
      fin_cases i
      · simpa [masses] using mul_nonneg hXP67 (add_nonneg hyE hyO)
      · simpa [masses] using mul_nonneg hX8 hyE
      · simpa [masses] using mul_nonneg hX8 hyO
      · simpa [masses] using mul_nonneg hX8 hyPot
    · intro i _hi
      fin_cases i
      · simpa [weights, cells, masses] using hz67
      · simpa [weights, cells, masses] using hz8E
      · simpa [weights, cells, masses] using hz8O
      · simpa [weights, cells, masses] using hz8Pot
    · have hgap :
          (XP67 + X8) * (yE + yO + yPot) -
              (XP67 * (yE + yO) + X8 * yE + X8 * yO + X8 * yPot) =
            XP67 * yPot := by ring
      have hprod : 0 ≤ XP67 * yPot := mul_nonneg hXP67 hyPot
      have hmasssum :
          (∑ i : Fin 4, masses i) =
            XP67 * (yE + yO) + X8 * yE + X8 * yO + X8 * yPot := by
        simp [masses, Fin.sum_univ_succ]
        ring
      rw [hmasssum]
      nlinarith

  have hthree := factorTwoP8ResidualCombinedForwardMixed_eq_threeCells
    eR oR heRc hoRc f a b
  calc
    factorTwoP678ResidualCombinedForwardMixed eR oR c d f a b ^ 2 =
        (z67 + z8E + z8O + z8Pot) ^ 2 := by
      dsimp only [factorTwoP678ResidualCombinedForwardMixed, z67, z8E,
        z8O, z8Pot]
      rw [hthree]
      ring
    _ = (∑ i : Fin 4, cells i) ^ 2 := by
      simp [cells, Fin.sum_univ_succ]
      ring
    _ ≤ (XP67 + X8) * (yE + yO + yPot) := hschur
    _ = (((1 / 100 : ℝ) *
          (factorTwoIntrinsicEnergy factorTwoCenteredP6 * c ^ 2 +
            factorTwoIntrinsicEnergy factorTwoCenteredP7 * d ^ 2)) +
        ((33 / 100 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP8 * f ^ 2)) *
        ((1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR +
          (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR +
          (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy oR) := by
      rfl

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural
