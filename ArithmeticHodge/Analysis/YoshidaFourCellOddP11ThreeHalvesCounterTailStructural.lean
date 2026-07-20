import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ExplicitSelectorCauchyStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11ThreeHalvesCounterTailStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# A sparse `P₁₁+` tail for the factor-three-halves obstruction

The candidate uses four odd centered Legendre modes.  Its membership in the
genuine `P₁₁+` tail is proved from all-degree orthogonality, rather than by
expanding the degree-25 polynomial or sampling its moments.
-/

/-- The sparse high tail, in the centered shifted-Legendre sign convention. -/
def fourCellOddP11ThreeHalvesCounterTailPolynomial : ℝ[X] :=
  (-(4 / 5 : ℝ)) • centeredShiftedLegendreReal 13 +
    centeredShiftedLegendreReal 17 -
      centeredShiftedLegendreReal 21 +
        (2 / 3 : ℝ) • centeredShiftedLegendreReal 25

def fourCellOddP11ThreeHalvesCounterTail : ℝ → ℝ := fun x ↦
  fourCellOddP11ThreeHalvesCounterTailPolynomial.eval x

theorem contDiff_fourCellOddP11ThreeHalvesCounterTail :
    ContDiff ℝ 1 fourCellOddP11ThreeHalvesCounterTail := by
  unfold fourCellOddP11ThreeHalvesCounterTail
  exact fourCellOddP11ThreeHalvesCounterTailPolynomial.contDiff_aeval
    (𝕜 := ℝ) 1

theorem odd_fourCellOddP11ThreeHalvesCounterTail :
    Function.Odd fourCellOddP11ThreeHalvesCounterTail := by
  intro x
  unfold fourCellOddP11ThreeHalvesCounterTail
    fourCellOddP11ThreeHalvesCounterTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul, eval_centeredShiftedLegendreReal_neg]
  norm_num
  ring

private theorem centeredP1_eq_neg_centeredMode_one :
    centeredP1 = fun x ↦ -(centeredShiftedLegendreReal 1).eval x := by
  funext x
  rw [eval_centeredShiftedLegendreReal_one]
  unfold centeredP1
  ring

private theorem centeredP3_eq_neg_centeredMode_three :
    centeredP3 = fun x ↦ -(centeredShiftedLegendreReal 3).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP3,
    Polynomial.smul_eq_C_mul]
  ring

private theorem centeredP5_eq_neg_centeredMode_five :
    factorTwoCenteredP5 =
      fun x ↦ -(centeredShiftedLegendreReal 5).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP5,
    Polynomial.smul_eq_C_mul]
  ring

private theorem centeredP7_eq_neg_centeredMode_seven :
    factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP7 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem centeredP9_eq_neg_centeredMode_nine :
    factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP9 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

/-- Every centered Legendre coordinate below degree eleven annihilates the
sparse tail. -/
theorem integral_threeHalvesCounterTail_mul_centeredMode_eq_zero
    (n : ℕ) (hn : n < 11) :
    (∫ x : ℝ in -1..1,
      fourCellOddP11ThreeHalvesCounterTail x *
        (centeredShiftedLegendreReal n).eval x) = 0 := by
  have h13 := centeredPolynomialPair_legendre_eq_zero
    (m := 13) (n := n) (by omega)
  have h17 := centeredPolynomialPair_legendre_eq_zero
    (m := 17) (n := n) (by omega)
  have h21 := centeredPolynomialPair_legendre_eq_zero
    (m := 21) (n := n) (by omega)
  have h25 := centeredPolynomialPair_legendre_eq_zero
    (m := 25) (n := n) (by omega)
  unfold centeredPolynomialPair at h13 h17 h21 h25
  have h13I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 13).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 :=
    ((centeredShiftedLegendreReal 13).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  have h17I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 17).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 :=
    ((centeredShiftedLegendreReal 17).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  have h21I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 21).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 :=
    ((centeredShiftedLegendreReal 21).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  have h25I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 25).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 :=
    ((centeredShiftedLegendreReal 25).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  unfold fourCellOddP11ThreeHalvesCounterTail
    fourCellOddP11ThreeHalvesCounterTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  rw [show (fun x : ℝ ↦
      (((-(4 / 5 : ℝ)) * (centeredShiftedLegendreReal 13).eval x +
          (centeredShiftedLegendreReal 17).eval x -
            (centeredShiftedLegendreReal 21).eval x) +
          (2 / 3 : ℝ) * (centeredShiftedLegendreReal 25).eval x) *
        (centeredShiftedLegendreReal n).eval x) = fun x ↦
      (-(4 / 5 : ℝ)) * ((centeredShiftedLegendreReal 13).eval x *
        (centeredShiftedLegendreReal n).eval x) +
      (centeredShiftedLegendreReal 17).eval x *
        (centeredShiftedLegendreReal n).eval x -
      (centeredShiftedLegendreReal 21).eval x *
        (centeredShiftedLegendreReal n).eval x +
      (2 / 3 : ℝ) * ((centeredShiftedLegendreReal 25).eval x *
        (centeredShiftedLegendreReal n).eval x) by
    funext x
    ring]
  rw [intervalIntegral.integral_add
      (((h13I.const_mul (-(4 / 5 : ℝ))).add h17I).sub h21I)
      (h25I.const_mul (2 / 3 : ℝ)),
    intervalIntegral.integral_sub
      ((h13I.const_mul (-(4 / 5 : ℝ))).add h17I) h21I,
    intervalIntegral.integral_add
      (h13I.const_mul (-(4 / 5 : ℝ))) h17I,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    h13, h17, h21, h25]
  ring

/-- The sparse counter-tail is a genuine `P₁₁+` residual. -/
theorem fourCellOddP11ThreeHalvesCounterTail_moments :
    centeredOddP1Coefficient fourCellOddP11ThreeHalvesCounterTail = 0 ∧
    centeredOddP3Coefficient fourCellOddP11ThreeHalvesCounterTail = 0 ∧
    centeredOddP5Coefficient fourCellOddP11ThreeHalvesCounterTail = 0 ∧
    centeredOddP7Coefficient fourCellOddP11ThreeHalvesCounterTail = 0 ∧
    centeredOddP9Coefficient fourCellOddP11ThreeHalvesCounterTail = 0 := by
  unfold centeredOddP1Coefficient centeredOddP3Coefficient
    centeredOddP5Coefficient centeredOddP7Coefficient centeredOddP9Coefficient
  rw [centeredP1_eq_neg_centeredMode_one,
    centeredP3_eq_neg_centeredMode_three,
    centeredP5_eq_neg_centeredMode_five,
    centeredP7_eq_neg_centeredMode_seven,
    centeredP9_eq_neg_centeredMode_nine]
  have h1 := integral_threeHalvesCounterTail_mul_centeredMode_eq_zero 1
    (by omega)
  have h3 := integral_threeHalvesCounterTail_mul_centeredMode_eq_zero 3
    (by omega)
  have h5 := integral_threeHalvesCounterTail_mul_centeredMode_eq_zero 5
    (by omega)
  have h7 := integral_threeHalvesCounterTail_mul_centeredMode_eq_zero 7
    (by omega)
  have h9 := integral_threeHalvesCounterTail_mul_centeredMode_eq_zero 9
    (by omega)
  rw [show (fun x : ℝ ↦ fourCellOddP11ThreeHalvesCounterTail x *
      -(centeredShiftedLegendreReal 1).eval x) = fun x ↦
        -(fourCellOddP11ThreeHalvesCounterTail x *
          (centeredShiftedLegendreReal 1).eval x) by funext x; ring,
    intervalIntegral.integral_neg, h1]
  rw [show (fun x : ℝ ↦ fourCellOddP11ThreeHalvesCounterTail x *
      -(centeredShiftedLegendreReal 3).eval x) = fun x ↦
        -(fourCellOddP11ThreeHalvesCounterTail x *
          (centeredShiftedLegendreReal 3).eval x) by funext x; ring,
    intervalIntegral.integral_neg, h3]
  rw [show (fun x : ℝ ↦ fourCellOddP11ThreeHalvesCounterTail x *
      -(centeredShiftedLegendreReal 5).eval x) = fun x ↦
        -(fourCellOddP11ThreeHalvesCounterTail x *
          (centeredShiftedLegendreReal 5).eval x) by funext x; ring,
    intervalIntegral.integral_neg, h5]
  rw [show (fun x : ℝ ↦ fourCellOddP11ThreeHalvesCounterTail x *
      -(centeredShiftedLegendreReal 7).eval x) = fun x ↦
        -(fourCellOddP11ThreeHalvesCounterTail x *
          (centeredShiftedLegendreReal 7).eval x) by funext x; ring,
    intervalIntegral.integral_neg, h7]
  rw [show (fun x : ℝ ↦ fourCellOddP11ThreeHalvesCounterTail x *
      -(centeredShiftedLegendreReal 9).eval x) = fun x ↦
        -(fourCellOddP11ThreeHalvesCounterTail x *
          (centeredShiftedLegendreReal 9).eval x) by funext x; ring,
    intervalIntegral.integral_neg, h9]
  norm_num

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11ThreeHalvesCounterTailStructural
