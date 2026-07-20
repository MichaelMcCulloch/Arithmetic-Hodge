import ArithmeticHodge.Analysis.EndpointPotentialPolynomialPairBilinearStructural
import ArithmeticHodge.Analysis.ShiftedLegendreCenteredL2Structural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailReserveFactorStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11MatchedFactorObstructionStructural

noncomputable section

open CenteredOddOneThreeEnergy
open EndpointPotentialPolynomialPairBilinearStructural
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddP11ThreeHalvesClosureStructural
open YoshidaFourCellOddP11TailReserveFactorStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# A fixed obstruction to every common matched-factor closure

The matched-factor mechanism asks one scalar `kappa` to serve two unrelated
operator norms: it must be large enough for the retained five-mode row and
small enough for the genuine tail reserve.  The tail below is deliberately
structural: it is the unweighted sum of the first eight odd Legendre modes
above the retained block.  The eventual estimate `Q tail < 2 * W tail`,
together with a retained-row witness forcing `2 < kappa`, rules out every
common factor without a truncation or a spectral enumeration.
-/

/-- The unweighted odd Legendre packet from degree eleven through degree
twenty-five. -/
def fourCellOddP11MatchedFactorUpperTailPolynomial : ℝ[X] :=
  centeredShiftedLegendreReal 11 + centeredShiftedLegendreReal 13 +
    centeredShiftedLegendreReal 15 + centeredShiftedLegendreReal 17 +
      centeredShiftedLegendreReal 19 + centeredShiftedLegendreReal 21 +
        centeredShiftedLegendreReal 23 + centeredShiftedLegendreReal 25

def fourCellOddP11MatchedFactorUpperTail : ℝ → ℝ := fun x ↦
  fourCellOddP11MatchedFactorUpperTailPolynomial.eval x

theorem contDiff_fourCellOddP11MatchedFactorUpperTail :
    ContDiff ℝ 1 fourCellOddP11MatchedFactorUpperTail := by
  unfold fourCellOddP11MatchedFactorUpperTail
  exact fourCellOddP11MatchedFactorUpperTailPolynomial.contDiff_aeval
    (𝕜 := ℝ) 1

theorem odd_fourCellOddP11MatchedFactorUpperTail :
    Function.Odd fourCellOddP11MatchedFactorUpperTail := by
  intro x
  unfold fourCellOddP11MatchedFactorUpperTail
    fourCellOddP11MatchedFactorUpperTailPolynomial
  simp only [Polynomial.eval_add, eval_centeredShiftedLegendreReal_neg]
  norm_num
  ring

private theorem integral_matchedFactorUpperTail_mul_centeredMode_eq_zero
    (n : ℕ) (hn : n < 11) :
    (∫ x : ℝ in -1..1,
      fourCellOddP11MatchedFactorUpperTail x *
        (centeredShiftedLegendreReal n).eval x) = 0 := by
  have h11 := centeredPolynomialPair_legendre_eq_zero
    (m := 11) (n := n) (by omega)
  have h13 := centeredPolynomialPair_legendre_eq_zero
    (m := 13) (n := n) (by omega)
  have h15 := centeredPolynomialPair_legendre_eq_zero
    (m := 15) (n := n) (by omega)
  have h17 := centeredPolynomialPair_legendre_eq_zero
    (m := 17) (n := n) (by omega)
  have h19 := centeredPolynomialPair_legendre_eq_zero
    (m := 19) (n := n) (by omega)
  have h21 := centeredPolynomialPair_legendre_eq_zero
    (m := 21) (n := n) (by omega)
  have h23 := centeredPolynomialPair_legendre_eq_zero
    (m := 23) (n := n) (by omega)
  have h25 := centeredPolynomialPair_legendre_eq_zero
    (m := 25) (n := n) (by omega)
  unfold centeredPolynomialPair at h11 h13 h15 h17 h19 h21 h23 h25
  have hInt (m : ℕ) : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal m).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 :=
    ((centeredShiftedLegendreReal m).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  have h1113 := (hInt 11).add (hInt 13)
  have h111315 := h1113.add (hInt 15)
  have h11131517 := h111315.add (hInt 17)
  have h1113151719 := h11131517.add (hInt 19)
  have h111315171921 := h1113151719.add (hInt 21)
  have h11131517192123 := h111315171921.add (hInt 23)
  unfold fourCellOddP11MatchedFactorUpperTail
    fourCellOddP11MatchedFactorUpperTailPolynomial
  simp only [Polynomial.eval_add, add_mul]
  rw [intervalIntegral.integral_add h11131517192123 (hInt 25),
    intervalIntegral.integral_add h111315171921 (hInt 23),
    intervalIntegral.integral_add h1113151719 (hInt 21),
    intervalIntegral.integral_add h11131517 (hInt 19),
    intervalIntegral.integral_add h111315 (hInt 17),
    intervalIntegral.integral_add h1113 (hInt 15),
    intervalIntegral.integral_add (hInt 11) (hInt 13)]
  rw [h11, h13, h15, h17, h19, h21, h23, h25]
  norm_num

private theorem matchedFactor_centeredP1_eq_legendre :
    centeredP1 = fun x ↦ -(centeredShiftedLegendreReal 1).eval x := by
  funext x
  rw [eval_centeredShiftedLegendreReal_one]
  unfold centeredP1
  ring

private theorem matchedFactor_centeredP3_eq_legendre :
    centeredP3 = fun x ↦ -(centeredShiftedLegendreReal 3).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose, centeredP3,
    Polynomial.smul_eq_C_mul]
  ring

private theorem matchedFactor_centeredP5_eq_legendre :
    factorTwoCenteredP5 =
      fun x ↦ -(centeredShiftedLegendreReal 5).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    factorTwoCenteredP5, Polynomial.smul_eq_C_mul]
  ring

private theorem matchedFactor_centeredP7_eq_legendre :
    factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP7 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem matchedFactor_centeredP9_eq_legendre :
    factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP9 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

/-- The packet is a genuine `P11+` tail by Legendre orthogonality. -/
theorem fourCellOddP11MatchedFactorUpperTail_moments :
    centeredOddP1Coefficient fourCellOddP11MatchedFactorUpperTail = 0 ∧
    centeredOddP3Coefficient fourCellOddP11MatchedFactorUpperTail = 0 ∧
    centeredOddP5Coefficient fourCellOddP11MatchedFactorUpperTail = 0 ∧
    centeredOddP7Coefficient fourCellOddP11MatchedFactorUpperTail = 0 ∧
    centeredOddP9Coefficient fourCellOddP11MatchedFactorUpperTail = 0 := by
  unfold centeredOddP1Coefficient centeredOddP3Coefficient
    centeredOddP5Coefficient centeredOddP7Coefficient centeredOddP9Coefficient
  rw [matchedFactor_centeredP1_eq_legendre,
    matchedFactor_centeredP3_eq_legendre,
    matchedFactor_centeredP5_eq_legendre,
    matchedFactor_centeredP7_eq_legendre,
    matchedFactor_centeredP9_eq_legendre]
  have h1 := integral_matchedFactorUpperTail_mul_centeredMode_eq_zero 1 (by omega)
  have h3 := integral_matchedFactorUpperTail_mul_centeredMode_eq_zero 3 (by omega)
  have h5 := integral_matchedFactorUpperTail_mul_centeredMode_eq_zero 5 (by omega)
  have h7 := integral_matchedFactorUpperTail_mul_centeredMode_eq_zero 7 (by omega)
  have h9 := integral_matchedFactorUpperTail_mul_centeredMode_eq_zero 9 (by omega)
  simp only []
  constructor
  · rw [show (fun x : ℝ ↦ fourCellOddP11MatchedFactorUpperTail x *
        -(centeredShiftedLegendreReal 1).eval x) = fun x ↦
      -(fourCellOddP11MatchedFactorUpperTail x *
        (centeredShiftedLegendreReal 1).eval x) by funext x; ring,
      intervalIntegral.integral_neg, h1]
    norm_num
  · constructor
    · rw [show (fun x : ℝ ↦ fourCellOddP11MatchedFactorUpperTail x *
          -(centeredShiftedLegendreReal 3).eval x) = fun x ↦
        -(fourCellOddP11MatchedFactorUpperTail x *
          (centeredShiftedLegendreReal 3).eval x) by funext x; ring,
        intervalIntegral.integral_neg, h3]
      norm_num
    · constructor
      · rw [show (fun x : ℝ ↦ fourCellOddP11MatchedFactorUpperTail x *
            -(centeredShiftedLegendreReal 5).eval x) = fun x ↦
          -(fourCellOddP11MatchedFactorUpperTail x *
            (centeredShiftedLegendreReal 5).eval x) by funext x; ring,
          intervalIntegral.integral_neg, h5]
        norm_num
      · constructor
        · rw [show (fun x : ℝ ↦ fourCellOddP11MatchedFactorUpperTail x *
              -(centeredShiftedLegendreReal 7).eval x) = fun x ↦
            -(fourCellOddP11MatchedFactorUpperTail x *
              (centeredShiftedLegendreReal 7).eval x) by funext x; ring,
            intervalIntegral.integral_neg, h7]
          norm_num
        · rw [show (fun x : ℝ ↦ fourCellOddP11MatchedFactorUpperTail x *
              -(centeredShiftedLegendreReal 9).eval x) = fun x ↦
            -(fourCellOddP11MatchedFactorUpperTail x *
              (centeredShiftedLegendreReal 9).eval x) by funext x; ring,
            intervalIntegral.integral_neg, h9]
          norm_num

private theorem centeredPolynomialPair_add_left_local
    (p q r : ℝ[X]) :
    centeredPolynomialPair (p + q) r =
      centeredPolynomialPair p r + centeredPolynomialPair q r := by
  unfold centeredPolynomialPair
  simp only [Polynomial.eval_add, add_mul]
  exact intervalIntegral.integral_add
    ((p.continuous.mul r.continuous).intervalIntegrable _ _)
    ((q.continuous.mul r.continuous).intervalIntegrable _ _)

private theorem centeredPolynomialPair_add_right_local
    (p q r : ℝ[X]) :
    centeredPolynomialPair p (q + r) =
      centeredPolynomialPair p q + centeredPolynomialPair p r := by
  rw [centeredPolynomialPair_comm p (q + r),
    centeredPolynomialPair_add_left_local,
    centeredPolynomialPair_comm q p,
    centeredPolynomialPair_comm r p]

private theorem centeredPolynomialPair_legendre_eq_local (m n : ℕ) :
    centeredPolynomialPair
        (centeredShiftedLegendreReal m)
        (centeredShiftedLegendreReal n) =
      if m = n then 2 / (2 * (n : ℝ) + 1) else 0 := by
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl]
    exact centeredLegendreL2Diagonal_closed m
  · rw [if_neg hmn]
    exact centeredPolynomialPair_legendre_eq_zero hmn

/-- The packet's total positive-half mass is obtained from the all-degree
Legendre Gram identity; no coefficient expansion is used. -/
theorem integral_zero_one_matchedFactorUpperTail_sq_eq :
    (∫ x : ℝ in 0..1,
      fourCellOddP11MatchedFactorUpperTail x ^ 2) =
      (1 / 23 + 1 / 27 + 1 / 31 + 1 / 35 +
        1 / 39 + 1 / 43 + 1 / 47 + 1 / 51 : ℝ) := by
  have hpair : centeredPolynomialPair
      fourCellOddP11MatchedFactorUpperTailPolynomial
      fourCellOddP11MatchedFactorUpperTailPolynomial =
        2 * (1 / 23 + 1 / 27 + 1 / 31 + 1 / 35 +
          1 / 39 + 1 / 43 + 1 / 47 + 1 / 51 : ℝ) := by
    unfold fourCellOddP11MatchedFactorUpperTailPolynomial
    simp only [centeredPolynomialPair_add_left_local,
      centeredPolynomialPair_add_right_local,
      centeredPolynomialPair_legendre_eq_local]
    norm_num
  unfold centeredPolynomialPair at hpair
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP11MatchedFactorUpperTail
    contDiff_fourCellOddP11MatchedFactorUpperTail.continuous
    (Or.inr odd_fourCellOddP11MatchedFactorUpperTail)
  unfold fourCellOddP11MatchedFactorUpperTail at hfold
  rw [show (fun x : ℝ ↦
      fourCellOddP11MatchedFactorUpperTailPolynomial.eval x *
        fourCellOddP11MatchedFactorUpperTailPolynomial.eval x) = fun x ↦
      fourCellOddP11MatchedFactorUpperTailPolynomial.eval x ^ 2 by
    funext x
    ring] at hpair
  unfold fourCellOddP11MatchedFactorUpperTail
  linarith

theorem twenty_three_hundredths_lt_matchedFactorUpperTail_mass :
    (23 / 100 : ℝ) < ∫ x : ℝ in 0..1,
      fourCellOddP11MatchedFactorUpperTail x ^ 2 := by
  rw [integral_zero_one_matchedFactorUpperTail_sq_eq]
  norm_num

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11MatchedFactorObstructionStructural
