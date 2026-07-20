import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinSolutionBoxStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreBlockPiconeIntegralStructural
import ArithmeticHodge.Analysis.EndpointPotentialPolynomialPairBilinearStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualDualDirectStructural

noncomputable section

open CenteredOddOneThreeEnergy
open EndpointPotentialPolynomialPairBilinearStructural
open ShiftedLegendreOrthogonality
open ShiftedLegendreLogKernel
open ShiftedLegendreLogEigen
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialLegendreDiagonalStructural
open YoshidaEndpointPotentialLegendreOffDiagonalStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFourCellOddCoreBlockPiconeIntegralStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP11FiveModeThreeHalvesStructural
open YoshidaFourCellOddP11GalerkinFiniteSolveStructural
open YoshidaFourCellOddP11GalerkinResidualRepresenterStructural
open YoshidaFourCellOddP11GalerkinRieszStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaRegularKernelBound

/-!
# Direct tests for the exact Galerkin residual dual

This file makes the exact inverse-defined Galerkin residual the ground
profile, and tests the proposed `1 / 50` unweighted dual constant on the first
genuine tail direction.  The result is a finite scalar obstruction, not a
new hypothesis replacing the universal dual statement.

The exploratory norm route has two logically separate parts.  Positivity of
the exact residual supplies a valid Picone ground after changing its value at
the null endpoint `0`.  On the other hand, any unweighted Cauchy proof of the
desired dual must pass the degree-eleven scalar test proved below.  Thus the
remaining quantitative question is exposed before any selector search.
-/

/-! ## The first exact `P11+` test direction -/

/-- Classical centered `P11`, with the sign convention of the production odd
basis. -/
def fourCellOddP11DirectTail (x : ℝ) : ℝ :=
  -(centeredShiftedLegendreReal 11).eval x

theorem contDiff_fourCellOddP11DirectTail :
    ContDiff ℝ 1 fourCellOddP11DirectTail := by
  unfold fourCellOddP11DirectTail
  exact (centeredShiftedLegendreReal 11).contDiff_aeval (𝕜 := ℝ) 1 |>.neg

theorem odd_fourCellOddP11DirectTail :
    Function.Odd fourCellOddP11DirectTail := by
  intro x
  unfold fourCellOddP11DirectTail
  rw [eval_centeredShiftedLegendreReal_neg]
  norm_num

private theorem centeredP1_eq_neg_centeredLegendre_one :
    centeredP1 = fun x ↦ -(centeredShiftedLegendreReal 1).eval x := by
  funext x
  rw [ShiftedLegendreCenteredLowModes.eval_centeredShiftedLegendreReal_one]
  unfold centeredP1
  ring

private theorem centeredP3_eq_neg_centeredLegendre_three :
    centeredP3 = fun x ↦ -(centeredShiftedLegendreReal 3).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP3,
    Polynomial.smul_eq_C_mul]
  ring

private theorem centeredP5_eq_neg_centeredLegendre_five :
    factorTwoCenteredP5 =
      fun x ↦ -(centeredShiftedLegendreReal 5).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP5,
    Polynomial.smul_eq_C_mul]
  ring

private theorem centeredP7_eq_neg_centeredLegendre_seven :
    factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP7 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem centeredP9_eq_neg_centeredLegendre_nine :
    factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP9 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem integral_directTail_mul_centeredLegendre_eq_zero
    (n : ℕ) (hn : n < 11) :
    (∫ x : ℝ in -1..1,
      fourCellOddP11DirectTail x *
        (-(centeredShiftedLegendreReal n).eval x)) = 0 := by
  have hne : (11 : ℕ) ≠ n := by omega
  have horth := centeredPolynomialPair_legendre_eq_zero hne
  unfold centeredPolynomialPair at horth
  simpa only [fourCellOddP11DirectTail, neg_mul_neg] using horth

/-- The direct test is a genuine `P11+` tail, proved from exact Legendre
orthogonality rather than a coefficient enumeration. -/
theorem fourCellOddP11DirectTail_moments :
    centeredOddP1Coefficient fourCellOddP11DirectTail = 0 ∧
    centeredOddP3Coefficient fourCellOddP11DirectTail = 0 ∧
    centeredOddP5Coefficient fourCellOddP11DirectTail = 0 ∧
    centeredOddP7Coefficient fourCellOddP11DirectTail = 0 ∧
    centeredOddP9Coefficient fourCellOddP11DirectTail = 0 := by
  have h1 := integral_directTail_mul_centeredLegendre_eq_zero 1 (by omega)
  have h3 := integral_directTail_mul_centeredLegendre_eq_zero 3 (by omega)
  have h5 := integral_directTail_mul_centeredLegendre_eq_zero 5 (by omega)
  have h7 := integral_directTail_mul_centeredLegendre_eq_zero 7 (by omega)
  have h9 := integral_directTail_mul_centeredLegendre_eq_zero 9 (by omega)
  have h1' :
      (∫ x : ℝ in -1..1, fourCellOddP11DirectTail x * centeredP1 x) = 0 := by
    rw [centeredP1_eq_neg_centeredLegendre_one]
    exact h1
  have h3' :
      (∫ x : ℝ in -1..1, fourCellOddP11DirectTail x * centeredP3 x) = 0 := by
    rw [centeredP3_eq_neg_centeredLegendre_three]
    exact h3
  have h5' :
      (∫ x : ℝ in -1..1,
        fourCellOddP11DirectTail x * factorTwoCenteredP5 x) = 0 := by
    rw [centeredP5_eq_neg_centeredLegendre_five]
    exact h5
  have h7' :
      (∫ x : ℝ in -1..1,
        fourCellOddP11DirectTail x * factorTwoCenteredP7 x) = 0 := by
    rw [centeredP7_eq_neg_centeredLegendre_seven]
    exact h7
  have h9' :
      (∫ x : ℝ in -1..1,
        fourCellOddP11DirectTail x * factorTwoCenteredP9 x) = 0 := by
    rw [centeredP9_eq_neg_centeredLegendre_nine]
    exact h9
  unfold centeredOddP1Coefficient centeredOddP3Coefficient
    centeredOddP5Coefficient centeredOddP7Coefficient
    centeredOddP9Coefficient
  rw [h1', h3', h5', h7', h9']
  norm_num

/-- Exact positive-half mass of the first tail direction. -/
theorem integral_zero_one_fourCellOddP11DirectTail_sq :
    (∫ x : ℝ in 0..1, fourCellOddP11DirectTail x ^ 2) = 1 / 23 := by
  have hdiag := centeredLegendreL2Diagonal_closed 11
  unfold centeredLegendreL2Diagonal centeredPolynomialPair at hdiag
  have hfull :
      (∫ x : ℝ in -1..1, fourCellOddP11DirectTail x ^ 2) = 2 / 23 := by
    rw [show (fun x : ℝ ↦ fourCellOddP11DirectTail x ^ 2) =
        fun x ↦ (centeredShiftedLegendreReal 11).eval x *
          (centeredShiftedLegendreReal 11).eval x by
      funext x
      unfold fourCellOddP11DirectTail
      ring]
    norm_num at hdiag ⊢
    exact hdiag
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail.continuous
    (Or.inr odd_fourCellOddP11DirectTail)
  linarith

/-! The following two polynomials keep the one-mode obstruction in the
all-degree Legendre API.  In particular, the endpoint-potential row below
uses the uniform off-diagonal formula, not an expansion of `P11`. -/

private def fourCellOddP11DirectGalerkinPolynomial : ℝ[X] :=
  -(centeredShiftedLegendreReal 1) +
    fourCellOddP11GalerkinRetainedSolution 0 •
      centeredShiftedLegendreReal 3 +
    fourCellOddP11GalerkinRetainedSolution 1 •
      centeredShiftedLegendreReal 5 +
    fourCellOddP11GalerkinRetainedSolution 2 •
      centeredShiftedLegendreReal 7 +
    fourCellOddP11GalerkinRetainedSolution 3 •
      centeredShiftedLegendreReal 9

private def fourCellOddP11DirectTailPolynomial : ℝ[X] :=
  -(centeredShiftedLegendreReal 11)

private theorem fourCellOddP11GalerkinResidual_eq_directPolynomial
    (x : ℝ) :
    fourCellOddP11GalerkinRetainedResidualProfile x =
      fourCellOddP11DirectGalerkinPolynomial.eval x := by
  unfold fourCellOddP11GalerkinRetainedResidualProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  unfold fourCellOddP11DirectGalerkinPolynomial
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
  simp only [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_smul,
    smul_eq_mul]
  rw [centeredP1_eq_neg_centeredLegendre_one,
    centeredP3_eq_neg_centeredLegendre_three,
    centeredP5_eq_neg_centeredLegendre_five,
    centeredP7_eq_neg_centeredLegendre_seven,
    centeredP9_eq_neg_centeredLegendre_nine]
  ring

private theorem fourCellOddP11DirectTail_eq_eval (x : ℝ) :
    fourCellOddP11DirectTail x =
      fourCellOddP11DirectTailPolynomial.eval x := by
  unfold fourCellOddP11DirectTail fourCellOddP11DirectTailPolynomial
  simp

private theorem endpointPotentialPair_directGalerkin_tail_eq :
    endpointPotentialPolynomialPair fourCellOddP11DirectGalerkinPolynomial
        fourCellOddP11DirectTailPolynomial =
      (1 / 65 : ℝ) - fourCellOddP11GalerkinRetainedSolution 0 / 60 -
        fourCellOddP11GalerkinRetainedSolution 1 / 51 -
        fourCellOddP11GalerkinRetainedSolution 2 / 38 -
        fourCellOddP11GalerkinRetainedSolution 3 / 21 := by
  have hoff : ∀ {m n : ℕ}, m < n → Even (m + n) →
      endpointPotentialPolynomialPair
          (centeredShiftedLegendreReal m)
          (centeredShiftedLegendreReal n) =
        2 / (((n : ℝ) - m) * ((n : ℝ) + m + 1)) := by
    intro m n hmn heven
    simpa only [endpointPotentialPolynomialPair] using
      integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
        hmn heven
  unfold fourCellOddP11DirectGalerkinPolynomial
    fourCellOddP11DirectTailPolynomial
  simp only [endpointPotentialPolynomialPair_add_left,
    endpointPotentialPolynomialPair_smul_left,
    endpointPotentialPolynomialPair_neg_left,
    endpointPotentialPolynomialPair_neg_right, neg_neg]
  rw [hoff (m := 1) (n := 11) (by omega) (by norm_num),
    hoff (m := 3) (n := 11) (by omega) (by norm_num),
    hoff (m := 5) (n := 11) (by omega) (by norm_num),
    hoff (m := 7) (n := 11) (by omega) (by norm_num),
    hoff (m := 9) (n := 11) (by omega) (by norm_num)]
  ring

/-- Exact endpoint-potential part of the `P11` residual row.  The five
rational denominators come from the single all-degree Legendre commutator
formula. -/
theorem integral_endpointPotential_exactGalerkinResidual_directTail_eq :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x *
        fourCellOddP11GalerkinRetainedResidualProfile x *
          fourCellOddP11DirectTail x) =
      (1 / 130 : ℝ) - fourCellOddP11GalerkinRetainedSolution 0 / 120 -
        fourCellOddP11GalerkinRetainedSolution 1 / 102 -
        fourCellOddP11GalerkinRetainedSolution 2 / 76 -
        fourCellOddP11GalerkinRetainedSolution 3 / 42 := by
  have hpair := endpointPotentialPair_directGalerkin_tail_eq
  unfold endpointPotentialPolynomialPair at hpair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x *
        fourCellOddP11DirectGalerkinPolynomial.eval x *
          fourCellOddP11DirectTailPolynomial.eval x) = fun x ↦
      yoshidaEndpointPotential x *
        fourCellOddP11GalerkinRetainedResidualProfile x *
          fourCellOddP11DirectTail x by
    funext x
    rw [fourCellOddP11GalerkinResidual_eq_directPolynomial,
      fourCellOddP11DirectTail_eq_eval]] at hpair
  have hq : ContDiff ℝ 1 fourCellOddP11GalerkinRetainedResidualProfile := by
    unfold fourCellOddP11GalerkinRetainedResidualProfile
    rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hqodd : Function.Odd fourCellOddP11GalerkinRetainedResidualProfile := by
    unfold fourCellOddP11GalerkinRetainedResidualProfile
    rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hInt : IntervalIntegrable (fun x : ℝ ↦
      yoshidaEndpointPotential x *
        (fourCellOddP11GalerkinRetainedResidualProfile x *
          fourCellOddP11DirectTail x)) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul
      (fun x : ℝ ↦ fourCellOddP11GalerkinRetainedResidualProfile x *
        fourCellOddP11DirectTail x)
      (hq.continuous.mul contDiff_fourCellOddP11DirectTail.continuous)
  have heven : Function.Even (fun x : ℝ ↦
      yoshidaEndpointPotential x *
        (fourCellOddP11GalerkinRetainedResidualProfile x *
          fourCellOddP11DirectTail x)) := by
    intro x
    change yoshidaEndpointPotential (-x) *
        (fourCellOddP11GalerkinRetainedResidualProfile (-x) *
          fourCellOddP11DirectTail (-x)) = _
    unfold yoshidaEndpointPotential
    rw [hqodd, odd_fourCellOddP11DirectTail]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ yoshidaEndpointPotential x *
      (fourCellOddP11GalerkinRetainedResidualProfile x *
        fourCellOddP11DirectTail x)) hInt heven
  rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x *
      (fourCellOddP11GalerkinRetainedResidualProfile x *
        fourCellOddP11DirectTail x)) = fun x ↦
      yoshidaEndpointPotential x *
        fourCellOddP11GalerkinRetainedResidualProfile x *
          fourCellOddP11DirectTail x by
    funext x
    ring] at hfold
  rw [hpair] at hfold
  linarith

set_option maxHeartbeats 10000000 in
private theorem endpointStripEvenMass_exactGalerkinResidual_directTail_eq :
    fourCellOddEndpointStripEvenMassBilinear
        fourCellOddP11GalerkinRetainedResidualProfile
        fourCellOddP11DirectTail =
      (-(8247648 / 1220703125 : ℝ)) -
        fourCellOddP11GalerkinRetainedSolution 0 *
          (-(27796288 / 6103515625 : ℝ)) -
        fourCellOddP11GalerkinRetainedSolution 1 *
          (-(7238485664 / 762939453125 : ℝ)) -
        fourCellOddP11GalerkinRetainedSolution 2 *
          (-(30904212608 / 3814697265625 : ℝ)) -
        fourCellOddP11GalerkinRetainedSolution 3 *
          (4121778714144 / 476837158203125 : ℝ) := by
  unfold fourCellOddP11GalerkinRetainedResidualProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  unfold fourCellOddEndpointStripEvenMassBilinear
    fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
    fourCellOddP11DirectTail
  simp_rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num
  ring

set_option maxHeartbeats 10000000 in
private theorem endpointStripOddMass_exactGalerkinResidual_directTail_eq :
    fourCellOddEndpointStripOddMassBilinear
        fourCellOddP11GalerkinRetainedResidualProfile
        fourCellOddP11DirectTail =
      (3392184 / 1220703125 : ℝ) -
        fourCellOddP11GalerkinRetainedSolution 0 *
          (287372792 / 30517578125 : ℝ) -
        fourCellOddP11GalerkinRetainedSolution 1 *
          (5704438328 / 762939453125 : ℝ) -
        fourCellOddP11GalerkinRetainedSolution 2 *
          (55320193912 / 19073486328125 : ℝ) -
        fourCellOddP11GalerkinRetainedSolution 3 *
          (2278454711736 / 476837158203125 : ℝ) := by
  unfold fourCellOddP11GalerkinRetainedResidualProfile
  rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
  unfold fourCellOddEndpointStripOddMassBilinear
    fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
    fourCellOddP11DirectTail
  simp_rw [factorTwoCenteredP7_eq, factorTwoCenteredP9_eq]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num
  ring

/-! The adverse strip-log term is evaluated through its polynomial
representer.  The displayed polynomial is the shifted-Legendre image of the
whole exact Galerkin low profile, so one spectral identity handles all five
retained coordinates at once. -/

private def directGalerkinEndpointLogKernelPolynomial : ℝ[X] :=
  (2 * (-(1 / 5 : ℝ) +
      (84 / 125) * fourCellOddP11GalerkinRetainedSolution 0 +
      (276 / 625) * fourCellOddP11GalerkinRetainedSolution 1 -
      (9804 / 78125) * fourCellOddP11GalerkinRetainedSolution 2 -
      (303036 / 1953125) * fourCellOddP11GalerkinRetainedSolution 3)) •
        shiftedLegendreReal 1 +
    ((11 / 3 : ℝ) *
      ((1 / 125) * fourCellOddP11GalerkinRetainedSolution 0 +
        (84 / 625) * fourCellOddP11GalerkinRetainedSolution 1 +
        (35252 / 78125) * fourCellOddP11GalerkinRetainedSolution 2 +
        (1126916 / 1953125) *
          fourCellOddP11GalerkinRetainedSolution 3)) •
      shiftedLegendreReal 3 +
    ((137 / 30 : ℝ) *
      ((1 / 3125) * fourCellOddP11GalerkinRetainedSolution 1 +
        (1012 / 78125) * fourCellOddP11GalerkinRetainedSolution 2 +
        (195844 / 1953125) *
          fourCellOddP11GalerkinRetainedSolution 3)) •
      shiftedLegendreReal 5 +
    ((363 / 70 : ℝ) *
      ((1 / 78125) * fourCellOddP11GalerkinRetainedSolution 2 +
        (372 / 390625) * fourCellOddP11GalerkinRetainedSolution 3)) •
      shiftedLegendreReal 7 +
    ((7129 / 1260 : ℝ) *
      ((1 / 1953125) * fourCellOddP11GalerkinRetainedSolution 3)) •
      shiftedLegendreReal 9

set_option maxHeartbeats 5000000 in
private theorem shiftedLogKernel_directGalerkinEndpoint_eq :
    shiftedLogKernel
        (fourCellOddFiveModeEndpointStripOddUnitPolynomial
          1 (-fourCellOddP11GalerkinRetainedSolution 0)
            (-fourCellOddP11GalerkinRetainedSolution 1)
            (-fourCellOddP11GalerkinRetainedSolution 2)
            (-fourCellOddP11GalerkinRetainedSolution 3)) =
      directGalerkinEndpointLogKernelPolynomial := by
  have hp :
      fourCellOddFiveModeEndpointStripOddUnitPolynomial
          1 (-fourCellOddP11GalerkinRetainedSolution 0)
            (-fourCellOddP11GalerkinRetainedSolution 1)
            (-fourCellOddP11GalerkinRetainedSolution 2)
            (-fourCellOddP11GalerkinRetainedSolution 3) =
        (-(1 / 5 : ℝ) +
          (84 / 125) * fourCellOddP11GalerkinRetainedSolution 0 +
          (276 / 625) * fourCellOddP11GalerkinRetainedSolution 1 -
          (9804 / 78125) * fourCellOddP11GalerkinRetainedSolution 2 -
          (303036 / 1953125) *
            fourCellOddP11GalerkinRetainedSolution 3) •
            shiftedLegendreReal 1 +
        ((1 / 125) * fourCellOddP11GalerkinRetainedSolution 0 +
          (84 / 625) * fourCellOddP11GalerkinRetainedSolution 1 +
          (35252 / 78125) * fourCellOddP11GalerkinRetainedSolution 2 +
          (1126916 / 1953125) *
            fourCellOddP11GalerkinRetainedSolution 3) •
            shiftedLegendreReal 3 +
        ((1 / 3125) * fourCellOddP11GalerkinRetainedSolution 1 +
          (1012 / 78125) * fourCellOddP11GalerkinRetainedSolution 2 +
          (195844 / 1953125) *
            fourCellOddP11GalerkinRetainedSolution 3) •
            shiftedLegendreReal 5 +
        ((1 / 78125) * fourCellOddP11GalerkinRetainedSolution 2 +
          (372 / 390625) *
            fourCellOddP11GalerkinRetainedSolution 3) •
            shiftedLegendreReal 7 +
        ((1 / 1953125) * fourCellOddP11GalerkinRetainedSolution 3) •
            shiftedLegendreReal 9 := by
    apply Polynomial.funext
    intro x
    unfold fourCellOddFiveModeEndpointStripOddUnitPolynomial
      fourCellOddFiveModeEndpointStripOddPolynomial
      fourCellOddFiveModePolynomial
    simp only [Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_smul, Polynomial.eval_comp, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, smul_eq_mul]
    norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
      Polynomial.eval_map, Polynomial.eval_finset_sum,
      Finset.sum_range_succ, Nat.choose]
    ring
  rw [hp]
  simp only [map_add, map_smul, shiftedLogKernel_shiftedLegendreReal]
  unfold directGalerkinEndpointLogKernelPolynomial
  apply Polynomial.funext
  intro x
  norm_num [harmonic, Finset.sum_range_succ]
  ring

set_option maxHeartbeats 10000000 in
private theorem endpointStripOddRaw_exactGalerkinResidual_directTail_eq :
    fourCellOddEndpointStripOddRawPolarization
        fourCellOddP11GalerkinRetainedResidualProfile
        fourCellOddP11DirectTail =
      (13568736 / 1220703125 : ℝ) -
        fourCellOddP11GalerkinRetainedSolution 0 *
          (3472766864 / 91552734375 : ℝ) -
        fourCellOddP11GalerkinRetainedSolution 1 *
          (393505908856 / 11444091796875 : ℝ) -
        fourCellOddP11GalerkinRetainedSolution 2 *
          (18263940974568 / 667572021484375 : ℝ) -
        fourCellOddP11GalerkinRetainedSolution 3 *
          (2221708644118996 / 50067901611328125 : ℝ) := by
  have hraw :=
    fourCellOddEndpointStripOddRawPolarization_fiveMode_eq_integral
      1 (-fourCellOddP11GalerkinRetainedSolution 0)
        (-fourCellOddP11GalerkinRetainedSolution 1)
        (-fourCellOddP11GalerkinRetainedSolution 2)
        (-fourCellOddP11GalerkinRetainedSolution 3)
        fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail
  have hprofile :
      fourCellOddP11GalerkinRetainedResidualProfile =
        fourCellOddOneThreeFiveSevenNineLowProfile
          1 (-fourCellOddP11GalerkinRetainedSolution 0)
            (-fourCellOddP11GalerkinRetainedSolution 1)
            (-fourCellOddP11GalerkinRetainedSolution 2)
            (-fourCellOddP11GalerkinRetainedSolution 3) := by
    unfold fourCellOddP11GalerkinRetainedResidualProfile
    exact fourCellOddP11GalerkinResidualProfile_eq_fiveMode _ _ _ _
  rw [hprofile, hraw]
  simp_rw [fourCellOddFiveModeRawUpperRepresenter,
    shiftedLogKernel_directGalerkinEndpoint_eq]
  unfold directGalerkinEndpointLogKernelPolynomial fourCellOddP11DirectTail
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  have hlinear (c : ℝ) :
      (∫ x : ℝ in 3 / 5..1, c * x) = c * (8 / 25 : ℝ) := by
    calc
      (∫ x : ℝ in 3 / 5..1, c * x) =
          c * (∫ x : ℝ in 3 / 5..1, x) :=
        intervalIntegral.integral_const_mul c (fun x : ℝ ↦ x)
      _ = c * (8 / 25 : ℝ) := by norm_num
  norm_num
  rw [hlinear (fourCellOddP11GalerkinRetainedSolution 0),
    hlinear (fourCellOddP11GalerkinRetainedSolution 1),
    hlinear (fourCellOddP11GalerkinRetainedSolution 2),
    hlinear (fourCellOddP11GalerkinRetainedSolution 3)]
  ring

/-! ## The exact residual is a Picone ground -/

/-- The exact residual vanishes at `0`.  Changing only that null endpoint
makes it strictly positive on the closed positive half, as required by the
totalized Picone API. -/
def fourCellOddP11GalerkinPiconeGround (x : ℝ) : ℝ :=
  if x = 0 then 1 else fourCellOddP11GalerkinRetainedResidualProfile x

private theorem endpointStripEven_galerkinPiconeGround_eq
    {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) :
    fourCellOddEndpointStripEven fourCellOddP11GalerkinPiconeGround z =
      fourCellOddEndpointStripEven
        fourCellOddP11GalerkinRetainedResidualProfile z := by
  rcases hz with ⟨hz0, hz1⟩
  have hp : (4 / 5 : ℝ) + z / 5 ≠ 0 := by
    apply ne_of_gt
    linarith
  have hm : (4 / 5 : ℝ) + (-z) / 5 ≠ 0 := by
    apply ne_of_gt
    linarith
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    fourCellOddP11GalerkinPiconeGround
  rw [if_neg hp, if_neg hm]

/-- Certified ground signs for the exact inverse-defined Galerkin residual.
No rational surrogate is used. -/
theorem fourCellOddP11GalerkinPiconeGround_signs :
    BlockPiconeGroundSigns fourCellOddP11GalerkinPiconeGround := by
  constructor
  · intro x hx
    by_cases hx0 : x = 0
    · simp [fourCellOddP11GalerkinPiconeGround, hx0]
    · rw [fourCellOddP11GalerkinPiconeGround, if_neg hx0]
      exact fourCellOddP11GalerkinRetainedResidualProfile_pos
        (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hx.2
  · intro z hz
    rw [endpointStripEven_galerkinPiconeGround_eq hz]
    exact fourCellOddEndpointStripEven_galerkinResidual_pos hz

/-- The actual core therefore has the exact paired block-Picone
decomposition with the exact Galerkin residual as ground. -/
theorem fourCellOddCoreLocalQuadratic_eq_exactGalerkinBlockPicone
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    fourCellOddCoreLocalQuadratic w =
      integratedRawBlockPicone fourCellOddP11GalerkinPiconeGround w +
        integratedRegularPicone fourCellOddP11GalerkinPiconeGround w +
        fourCellOddRetainedLocalDiagonal w := by
  exact fourCellOddCoreLocalQuadratic_eq_integratedBlockPicone
    fourCellOddP11GalerkinPiconeGround w hw hodd
      fourCellOddP11GalerkinPiconeGround_signs

/-! ## Finite Schur identities and the degree-eleven obstruction -/

private theorem contDiff_factorTwoCenteredP7_local :
    ContDiff ℝ 1 factorTwoCenteredP7 := by
  rw [show factorTwoCenteredP7 = fun x ↦
      (429 * x ^ 7 - 693 * x ^ 5 + 315 * x ^ 3 - 35 * x) / 16 by
    funext x
    exact factorTwoCenteredP7_eq x]
  fun_prop

private theorem contDiff_factorTwoCenteredP9_local :
    ContDiff ℝ 1 factorTwoCenteredP9 := by
  rw [show factorTwoCenteredP9 = fun x ↦
      (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128 by
    funext x
    exact factorTwoCenteredP9_eq x]
  fun_prop

/-- Exact coefficient expansion of the direct tail row of the inverse-defined
Galerkin residual. -/
theorem fourCellOddCoreLocalBilinear_exactGalerkinResidual_directTail_eq :
    fourCellOddCoreLocalBilinear
        fourCellOddP11GalerkinRetainedResidualProfile
        fourCellOddP11DirectTail =
      fourCellOddCoreLocalBilinear centeredP1 fourCellOddP11DirectTail -
        fourCellOddP11GalerkinRetainedSolution 0 *
          fourCellOddCoreLocalBilinear centeredP3 fourCellOddP11DirectTail -
        fourCellOddP11GalerkinRetainedSolution 1 *
          fourCellOddCoreLocalBilinear factorTwoCenteredP5
            fourCellOddP11DirectTail -
        fourCellOddP11GalerkinRetainedSolution 2 *
          fourCellOddCoreLocalBilinear factorTwoCenteredP7
            fourCellOddP11DirectTail -
        fourCellOddP11GalerkinRetainedSolution 3 *
          fourCellOddCoreLocalBilinear factorTwoCenteredP9
            fourCellOddP11DirectTail := by
  let p := fourCellOddOneThreeFiveLowProfile
    1 (-fourCellOddP11GalerkinRetainedSolution 0)
      (-fourCellOddP11GalerkinRetainedSolution 1)
  let p7 : ℝ → ℝ := fun x ↦
    (-fourCellOddP11GalerkinRetainedSolution 2) * factorTwoCenteredP7 x
  let p9 : ℝ → ℝ := fun x ↦
    (-fourCellOddP11GalerkinRetainedSolution 3) * factorTwoCenteredP9 x
  have hp : ContDiff ℝ 1 p := by
    dsimp only [p]
    exact contDiff_fourCellOddOneThreeFiveLowProfile _ _ _
  have hpodd : Function.Odd p := by
    dsimp only [p]
    exact odd_fourCellOddOneThreeFiveLowProfile _ _ _
  have hp7 : ContDiff ℝ 1 p7 := contDiff_const.mul
    contDiff_factorTwoCenteredP7_local
  have hp9 : ContDiff ℝ 1 p9 := contDiff_const.mul
    contDiff_factorTwoCenteredP9_local
  have hp7odd : Function.Odd p7 := by
    intro x
    dsimp only [p7]
    rw [odd_factorTwoCenteredP7]
    ring
  have hp9odd : Function.Odd p9 := by
    intro x
    dsimp only [p9]
    rw [odd_factorTwoCenteredP9]
    ring
  have hprofile :
      fourCellOddP11GalerkinRetainedResidualProfile = (p + p7) + p9 := by
    rw [show fourCellOddP11GalerkinRetainedResidualProfile =
        fourCellOddP11GalerkinResidualProfile
          (fourCellOddP11GalerkinRetainedSolution 0)
          (fourCellOddP11GalerkinRetainedSolution 1)
          (fourCellOddP11GalerkinRetainedSolution 2)
          (fourCellOddP11GalerkinRetainedSolution 3) by rfl,
      fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
    funext x
    dsimp only [p, p7, p9]
    unfold fourCellOddOneThreeFiveSevenNineLowProfile
    simp only [Pi.add_apply]
  rw [hprofile,
    fourCellOddCoreLocalBilinear_add_left (p + p7) p9
      fourCellOddP11DirectTail (hp.add hp7) hp9
      contDiff_fourCellOddP11DirectTail (hpodd.add hp7odd) hp9odd
      odd_fourCellOddP11DirectTail,
    fourCellOddCoreLocalBilinear_add_left p p7
      fourCellOddP11DirectTail hp hp7 contDiff_fourCellOddP11DirectTail
      hpodd hp7odd odd_fourCellOddP11DirectTail]
  dsimp only [p7, p9]
  rw [fourCellOddCoreLocalBilinear_const_mul_left
      factorTwoCenteredP7 fourCellOddP11DirectTail
      contDiff_factorTwoCenteredP7_local contDiff_fourCellOddP11DirectTail
      odd_factorTwoCenteredP7 odd_fourCellOddP11DirectTail,
    fourCellOddCoreLocalBilinear_const_mul_left
      factorTwoCenteredP9 fourCellOddP11DirectTail
      contDiff_factorTwoCenteredP9_local contDiff_fourCellOddP11DirectTail
      odd_factorTwoCenteredP9 odd_fourCellOddP11DirectTail]
  dsimp only [p]
  rw [fourCellOddCoreLocalBilinear_oneThreeFiveLowProfile_left
      1 (-fourCellOddP11GalerkinRetainedSolution 0)
      (-fourCellOddP11GalerkinRetainedSolution 1)
      fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail
      odd_fourCellOddP11DirectTail]
  ring

/-- Galerkin orthogonality identifies the residual quadratic with its
remaining `P1` row. -/
theorem fourCellOddCoreLocalQuadratic_exactGalerkinResidual_eq_P1_row :
    fourCellOddCoreLocalQuadratic
        fourCellOddP11GalerkinRetainedResidualProfile =
      fourCellOddCoreLocalBilinear
        fourCellOddP11GalerkinRetainedResidualProfile centeredP1 := by
  let q := fourCellOddP11GalerkinRetainedResidualProfile
  let h := fourCellOddP11GalerkinLowProfile
    (fourCellOddP11GalerkinRetainedSolution 0)
    (fourCellOddP11GalerkinRetainedSolution 1)
    (fourCellOddP11GalerkinRetainedSolution 2)
    (fourCellOddP11GalerkinRetainedSolution 3)
  have hq : ContDiff ℝ 1 q := by
    dsimp only [q, fourCellOddP11GalerkinRetainedResidualProfile]
    rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hqodd : Function.Odd q := by
    dsimp only [q, fourCellOddP11GalerkinRetainedResidualProfile]
    rw [fourCellOddP11GalerkinResidualProfile_eq_fiveMode]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hh : ContDiff ℝ 1 h := by
    dsimp only [h, fourCellOddP11GalerkinLowProfile]
    exact contDiff_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have hhodd : Function.Odd h := by
    dsimp only [h, fourCellOddP11GalerkinLowProfile]
    exact odd_fourCellOddOneThreeFiveSevenNineLowProfile _ _ _ _ _
  have horth : fourCellOddCoreLocalBilinear q h = 0 := by
    dsimp only [q, h, fourCellOddP11GalerkinRetainedResidualProfile,
      fourCellOddP11GalerkinLowProfile]
    exact fourCellOddP11GalerkinRetainedSolution_orthogonal _ _ _ _
  have hreconstruct : centeredP1 = q + h := by
    funext x
    dsimp only [q, h, fourCellOddP11GalerkinRetainedResidualProfile]
    unfold fourCellOddP11GalerkinResidualProfile
      fourCellOddP11GalerkinLowProfile
    simp only [Pi.add_apply]
    ring
  have hself := fourCellOddCoreLocalBilinear_self_eq_quadratic q hq hqodd
  rw [hreconstruct,
    fourCellOddCoreLocalBilinear_comm q (q + h)
      hq.continuous (hq.add hh).continuous,
    fourCellOddCoreLocalBilinear_add_left q h q
      hq hh hq hqodd hhodd hqodd,
    fourCellOddCoreLocalBilinear_comm h q hh.continuous hq.continuous,
    horth, hself]
  ring

/-- Any proof of the proposed exact residual dual must pass the very first
tail mode.  Its required scalar constant is exactly `1 / 1150`; there is no
selector or integral estimate left in this necessary condition. -/
theorem exactGalerkinResidualL2Dual_implies_directTail_scalar :
    FourCellOddP11GalerkinResidualL2Dual
        (fourCellOddP11GalerkinRetainedSolution 0)
        (fourCellOddP11GalerkinRetainedSolution 1)
        (fourCellOddP11GalerkinRetainedSolution 2)
        (fourCellOddP11GalerkinRetainedSolution 3) →
      fourCellOddCoreLocalBilinear
          fourCellOddP11GalerkinRetainedResidualProfile
          fourCellOddP11DirectTail ^ 2 ≤
        fourCellOddCoreLocalQuadratic
            fourCellOddP11GalerkinRetainedResidualProfile / 1150 := by
  intro hdual
  rcases fourCellOddP11DirectTail_moments with ⟨h1, h3, h5, h7, h9⟩
  have h := hdual fourCellOddP11DirectTail
    contDiff_fourCellOddP11DirectTail odd_fourCellOddP11DirectTail
    h1 h3 h5 h7 h9
  rw [integral_zero_one_fourCellOddP11DirectTail_sq] at h
  simpa only [fourCellOddP11GalerkinRetainedResidualProfile] using
    (show fourCellOddCoreLocalBilinear
          (fourCellOddP11GalerkinResidualProfile
            (fourCellOddP11GalerkinRetainedSolution 0)
            (fourCellOddP11GalerkinRetainedSolution 1)
            (fourCellOddP11GalerkinRetainedSolution 2)
            (fourCellOddP11GalerkinRetainedSolution 3))
          fourCellOddP11DirectTail ^ 2 ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP11GalerkinResidualProfile
            (fourCellOddP11GalerkinRetainedSolution 0)
            (fourCellOddP11GalerkinRetainedSolution 1)
            (fourCellOddP11GalerkinRetainedSolution 2)
            (fourCellOddP11GalerkinRetainedSolution 3)) / 1150 by
      nlinarith only [h])

/-- A strict reversal of the displayed finite scalar test disproves the
exact residual dual.  This is a one-mode obstruction, strictly weaker than
assuming the negation of the universal target. -/
theorem not_exactGalerkinResidualL2Dual_of_directTail_reversal
    (hreverse :
      fourCellOddCoreLocalQuadratic
          fourCellOddP11GalerkinRetainedResidualProfile / 1150 <
        fourCellOddCoreLocalBilinear
          fourCellOddP11GalerkinRetainedResidualProfile
          fourCellOddP11DirectTail ^ 2) :
    ¬ FourCellOddP11GalerkinResidualL2Dual
        (fourCellOddP11GalerkinRetainedSolution 0)
        (fourCellOddP11GalerkinRetainedSolution 1)
        (fourCellOddP11GalerkinRetainedSolution 2)
        (fourCellOddP11GalerkinRetainedSolution 3) := by
  intro hdual
  exact (not_lt_of_ge
    (exactGalerkinResidualL2Dual_implies_directTail_scalar hdual)) hreverse

/-- The same one-mode reversal also rules out every ordinary unweighted
five-mode selector certificate at the proposed constant. -/
theorem not_exactGalerkinModuloFiveModeTwoStripNormBound_of_directTail_reversal
    (hreverse :
      fourCellOddCoreLocalQuadratic
          fourCellOddP11GalerkinRetainedResidualProfile / 1150 <
        fourCellOddCoreLocalBilinear
          fourCellOddP11GalerkinRetainedResidualProfile
          fourCellOddP11DirectTail ^ 2) :
    ¬ FourCellOddP11GalerkinResidualModuloFiveModeTwoStripNormBound
        (fourCellOddP11GalerkinRetainedSolution 0)
        (fourCellOddP11GalerkinRetainedSolution 1)
        (fourCellOddP11GalerkinRetainedSolution 2)
        (fourCellOddP11GalerkinRetainedSolution 3) := by
  intro hnorm
  apply not_exactGalerkinResidualL2Dual_of_directTail_reversal hreverse
  exact fourCellOddP11GalerkinResidualL2Dual_of_moduloFiveModeTwoStripNormBound
    _ _ _ _ hnorm

/-- Equivalently, the proposed dual forces nonnegativity of the exact
two-dimensional pencil generated by the Galerkin residual and `P11`, with
the tail diagonal replaced by its allocated `1 / 50` mass. -/
theorem exactGalerkinResidualL2Dual_directTail_pencil_nonneg
    (hdual : FourCellOddP11GalerkinResidualL2Dual
      (fourCellOddP11GalerkinRetainedSolution 0)
      (fourCellOddP11GalerkinRetainedSolution 1)
      (fourCellOddP11GalerkinRetainedSolution 2)
      (fourCellOddP11GalerkinRetainedSolution 3))
    (s t : ℝ) :
    0 ≤ fourCellOddCoreLocalQuadratic
          fourCellOddP11GalerkinRetainedResidualProfile * s ^ 2 +
        2 * fourCellOddCoreLocalBilinear
            fourCellOddP11GalerkinRetainedResidualProfile
            fourCellOddP11DirectTail * s * t +
          (1 / 1150 : ℝ) * t ^ 2 := by
  have hq := fourCellOddP11GalerkinRetainedSolution_residual_core_pos.le
  have hcross := exactGalerkinResidualL2Dual_implies_directTail_scalar hdual
  exact (real_quadratic_pencil_nonneg_iff
    (fourCellOddCoreLocalQuadratic
      fourCellOddP11GalerkinRetainedResidualProfile)
    (1 / 1150 : ℝ)
    (fourCellOddCoreLocalBilinear
      fourCellOddP11GalerkinRetainedResidualProfile
      fourCellOddP11DirectTail)).2
      ⟨hq, by norm_num, by
        convert hcross using 1 <;> ring⟩ s t

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
