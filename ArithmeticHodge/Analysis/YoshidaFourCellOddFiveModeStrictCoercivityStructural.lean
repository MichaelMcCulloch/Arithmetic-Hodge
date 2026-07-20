import ArithmeticHodge.Analysis.YoshidaFourCellOddP11SelectorConstructionStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddFiveModeStrictCoercivityStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Strict coercivity of the retained odd five-mode block

The existing rational congruence proves that a lower matrix for the complete
`P₁/P₃/P₅/P₇/P₉` block is positive definite.  Here that strict information is
transported back to the function-level quadratic and its `P₁` Schur
complement.  In particular, no nonzero retained direction has zero corrected
reserve.
-/

set_option maxHeartbeats 2000000 in
/-- The actual five-mode coefficient form is strictly positive away from the
zero coefficient vector. -/
theorem fourCellOddFiveModeCoreExpression_pos
    (c d e f g : ℝ)
    (hcoeff : (![c, d, e, f, g] : Fin 5 → ℝ) ≠ 0) :
    0 < fourCellOddFiveModeCoreExpression c d e f g := by
  let x : Fin 5 → ℝ := ![c, d, e, f, g]
  have hx : x ≠ 0 := by
    simpa only [x] using hcoeff
  have hmatrix :=
    fourCellOddFiveModeLowerMatrix_posDef.dotProduct_mulVec_pos hx
  simp only [star_trivial] at hmatrix
  have hlower : 0 <
      fourCellOddOneThreeFivePerturbedQuadratic c d e +
        2 * fourCellOddCoreLocalBilinear
            centeredP1 factorTwoCenteredP7 * c * f +
        2 * fourCellOddCoreLocalBilinear
            centeredP3 factorTwoCenteredP7 * d * f +
        2 * fourCellOddCoreLocalBilinear
            factorTwoCenteredP5 factorTwoCenteredP7 * e * f +
        (1 / 5 : ℝ) * f ^ 2 +
        2 * fourCellOddCoreLocalBilinear
            centeredP1 factorTwoCenteredP9 * c * g +
        2 * fourCellOddCoreLocalBilinear
            centeredP3 factorTwoCenteredP9 * d * g +
        2 * fourCellOddCoreLocalBilinear
            factorTwoCenteredP5 factorTwoCenteredP9 * e * g +
        2 * fourCellOddCoreLocalBilinear
            factorTwoCenteredP7 factorTwoCenteredP9 * f * g +
        (29 / 200 : ℝ) * g ^ 2 := by
    simp [x, fourCellOddFiveModeLowerMatrix, dotProduct, Matrix.mulVec,
      Fin.sum_univ_succ] at hmatrix
    unfold fourCellOddOneThreeFivePerturbedQuadratic
    convert hmatrix using 1
    all_goals ring
  have h7 := one_fifth_lt_fourCellOddCoreLocalQuadratic_P7
  have h9 := twenty_nine_two_hundredths_lt_fourCellOddCoreLocalQuadratic_P9
  unfold fourCellOddFiveModeCoreExpression
  nlinarith [mul_le_mul_of_nonneg_right h7.le (sq_nonneg f),
    mul_le_mul_of_nonneg_right h9.le (sq_nonneg g)]

/-- Function-level strict coercivity for the retained five-mode profile. -/
theorem fourCellOddCoreLocalQuadratic_fiveMode_pos
    (c d e f g : ℝ)
    (hcoeff : (![c, d, e, f, g] : Fin 5 → ℝ) ≠ 0) :
    0 < fourCellOddCoreLocalQuadratic
      (fourCellOddOneThreeFiveSevenNineLowProfile c d e f g) := by
  rw [fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression]
  exact fourCellOddFiveModeCoreExpression_pos c d e f g hcoeff

/-- The `P₁` pivot is strictly positive. -/
theorem fourCellOddCoreLocalQuadratic_centeredP1_pos :
    0 < fourCellOddCoreLocalQuadratic centeredP1 := by
  have hprofile :
      fourCellOddOneThreeFiveSevenNineLowProfile 1 0 0 0 0 = centeredP1 := by
    funext x
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
      fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    simp
  rw [← hprofile]
  apply fourCellOddCoreLocalQuadratic_fiveMode_pos
  intro hzero
  have hfirst := congrFun hzero 0
  norm_num at hfirst

/-- Every nonzero retained `P₃/P₅/P₇/P₉` direction has strictly positive
`P₁`-corrected reserve.  This rules out singular finite Schur fibers before
any infinite-tail estimate is imposed. -/
theorem fourCellOddP11FiniteCorrectedReserve_pos
    (d e f g : ℝ)
    (hcoeff : (![d, e, f, g] : Fin 4 → ℝ) ≠ 0) :
    0 < fourCellOddP11FiniteCorrectedReserve d e f g := by
  let p := fourCellOddOneThreeFiveSevenNineLowProfile 0 d e f g
  let A := fourCellOddCoreLocalQuadratic centeredP1
  let b := fourCellOddCoreLocalBilinear centeredP1 p
  have hA : 0 < A := by
    dsimp only [A]
    exact fourCellOddCoreLocalQuadratic_centeredP1_pos
  have hsome : d ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0 ∨ g ≠ 0 := by
    by_contra hall
    push_neg at hall
    rcases hall with ⟨hd, he, hf, hg⟩
    apply hcoeff
    funext i
    fin_cases i <;> simp [hd, he, hf, hg]
  have hschurCoeff :
      (![(-b), A * d, A * e, A * f, A * g] : Fin 5 → ℝ) ≠ 0 := by
    intro hzero
    rcases hsome with hd | he | hf | hg
    · have hi : A * d = 0 := by
        simpa using congrFun hzero (1 : Fin 5)
      exact (mul_ne_zero hA.ne' hd) hi
    · have hi : A * e = 0 := by
        simpa using congrFun hzero (2 : Fin 5)
      exact (mul_ne_zero hA.ne' he) hi
    · have hi : A * f = 0 := by
        simpa using congrFun hzero (3 : Fin 5)
      exact (mul_ne_zero hA.ne' hf) hi
    · have hi : A * g = 0 := by
        simpa using congrFun hzero (4 : Fin 5)
      exact (mul_ne_zero hA.ne' hg) hi
  have hnorm :
      0 < fourCellOddCoreLocalQuadratic
        (fourCellOddP11FiniteSchurResidualProfile d e f g) := by
    change 0 < fourCellOddCoreLocalQuadratic
      (fourCellOddOneThreeFiveSevenNineLowProfile
        (-b) (A * d) (A * e) (A * f) (A * g))
    exact fourCellOddCoreLocalQuadratic_fiveMode_pos
      (-b) (A * d) (A * e) (A * f) (A * g) hschurCoeff
  rw [fourCellOddCoreLocalQuadratic_finiteSchurResidualProfile] at hnorm
  change 0 < A * fourCellOddP11FiniteCorrectedReserve d e f g at hnorm
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddFiveModeStrictCoercivityStructural
