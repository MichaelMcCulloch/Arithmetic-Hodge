import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorP13ObstructionStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddP13AugmentedFiniteSolveStructural
open YoshidaFourCellOddP13AugmentedGalerkinRieszStructural
open YoshidaFourCellOddP13AugmentedOptimalSelectorStructural
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# The first omitted-mode obstruction to the augmented optimal selector

The shared selector removes exactly the retained modes through `P11`.  The
next centered Legendre mode `P13` is therefore selector-independent.  Its
exact positive-half mass is `1 / 27`, so ordinary Hilbert-space Cauchy forces
the scalar necessary condition proved below for every proposed quotient
bound.  This is a structural one-mode obstruction, with no finite grid or
exhaustive selector search.
-/

/-- The first centered Legendre mode omitted by the augmented selector. -/
def fourCellOddP13FirstOmittedMode (x : ℝ) : ℝ :=
  -(centeredShiftedLegendreReal 13).eval x

theorem contDiff_fourCellOddP13FirstOmittedMode :
    ContDiff ℝ 1 fourCellOddP13FirstOmittedMode := by
  unfold fourCellOddP13FirstOmittedMode
  exact (centeredShiftedLegendreReal 13).contDiff_aeval (𝕜 := ℝ) 1 |>.neg

theorem odd_fourCellOddP13FirstOmittedMode :
    Function.Odd fourCellOddP13FirstOmittedMode := by
  intro x
  unfold fourCellOddP13FirstOmittedMode
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

private theorem integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
    (m n : ℕ) (hne : m ≠ n) :
    (∫ x : ℝ in -1..1,
      (-(centeredShiftedLegendreReal m).eval x) *
        (-(centeredShiftedLegendreReal n).eval x)) = 0 := by
  have horth := centeredPolynomialPair_legendre_eq_zero hne
  unfold centeredPolynomialPair at horth
  simpa only [neg_mul_neg] using horth

private theorem lowMoments_eq_zero_of_centeredLegendre_orthogonal
    (r : ℝ → ℝ)
    (h1 : (∫ x : ℝ in -1..1,
      r x * (-(centeredShiftedLegendreReal 1).eval x)) = 0)
    (h3 : (∫ x : ℝ in -1..1,
      r x * (-(centeredShiftedLegendreReal 3).eval x)) = 0)
    (h5 : (∫ x : ℝ in -1..1,
      r x * (-(centeredShiftedLegendreReal 5).eval x)) = 0)
    (h7 : (∫ x : ℝ in -1..1,
      r x * (-(centeredShiftedLegendreReal 7).eval x)) = 0)
    (h9 : (∫ x : ℝ in -1..1,
      r x * (-(centeredShiftedLegendreReal 9).eval x)) = 0) :
    centeredOddP1Coefficient r = 0 ∧
    centeredOddP3Coefficient r = 0 ∧
    centeredOddP5Coefficient r = 0 ∧
    centeredOddP7Coefficient r = 0 ∧
    centeredOddP9Coefficient r = 0 := by
  have h1' : (∫ x : ℝ in -1..1, r x * centeredP1 x) = 0 := by
    rw [centeredP1_eq_neg_centeredLegendre_one]
    exact h1
  have h3' : (∫ x : ℝ in -1..1, r x * centeredP3 x) = 0 := by
    rw [centeredP3_eq_neg_centeredLegendre_three]
    exact h3
  have h5' :
      (∫ x : ℝ in -1..1, r x * factorTwoCenteredP5 x) = 0 := by
    rw [centeredP5_eq_neg_centeredLegendre_five]
    exact h5
  have h7' :
      (∫ x : ℝ in -1..1, r x * factorTwoCenteredP7 x) = 0 := by
    rw [centeredP7_eq_neg_centeredLegendre_seven]
    exact h7
  have h9' :
      (∫ x : ℝ in -1..1, r x * factorTwoCenteredP9 x) = 0 := by
    rw [centeredP9_eq_neg_centeredLegendre_nine]
    exact h9
  unfold centeredOddP1Coefficient centeredOddP3Coefficient
    centeredOddP5Coefficient centeredOddP7Coefficient
    centeredOddP9Coefficient
  rw [h1', h3', h5', h7', h9']
  norm_num

private theorem integral_firstOmitted_mul_centeredLegendre_eq_zero
    (n : ℕ) (hn : n < 13) :
    (∫ x : ℝ in -1..1,
      fourCellOddP13FirstOmittedMode x *
        (-(centeredShiftedLegendreReal n).eval x)) = 0 := by
  unfold fourCellOddP13FirstOmittedMode
  exact integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
    13 n (by omega)

/-- `P13` has zero moments against all five legacy retained modes. -/
theorem fourCellOddP13FirstOmittedMode_lowMoments :
    centeredOddP1Coefficient fourCellOddP13FirstOmittedMode = 0 ∧
    centeredOddP3Coefficient fourCellOddP13FirstOmittedMode = 0 ∧
    centeredOddP5Coefficient fourCellOddP13FirstOmittedMode = 0 ∧
    centeredOddP7Coefficient fourCellOddP13FirstOmittedMode = 0 ∧
    centeredOddP9Coefficient fourCellOddP13FirstOmittedMode = 0 := by
  exact lowMoments_eq_zero_of_centeredLegendre_orthogonal
    fourCellOddP13FirstOmittedMode
    (integral_firstOmitted_mul_centeredLegendre_eq_zero 1 (by omega))
    (integral_firstOmitted_mul_centeredLegendre_eq_zero 3 (by omega))
    (integral_firstOmitted_mul_centeredLegendre_eq_zero 5 (by omega))
    (integral_firstOmitted_mul_centeredLegendre_eq_zero 7 (by omega))
    (integral_firstOmitted_mul_centeredLegendre_eq_zero 9 (by omega))

/-- `P13` is also orthogonal to the newly retained `P11` mode on `[0,1]`. -/
theorem integral_zero_one_fourCellOddP11DirectTail_mul_firstOmittedMode :
    (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * fourCellOddP13FirstOmittedMode x) = 0 := by
  have horth := integral_firstOmitted_mul_centeredLegendre_eq_zero 11 (by omega)
  have hfull :
      (∫ x : ℝ in -1..1,
        fourCellOddP11DirectTail x * fourCellOddP13FirstOmittedMode x) = 0 := by
    rw [show (fun x : ℝ ↦
        fourCellOddP11DirectTail x * fourCellOddP13FirstOmittedMode x) =
      fun x ↦ fourCellOddP13FirstOmittedMode x *
        (-(centeredShiftedLegendreReal 11).eval x) by
      funext x
      unfold fourCellOddP11DirectTail
      ring]
    exact horth
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦
      fourCellOddP11DirectTail x * fourCellOddP13FirstOmittedMode x)
    ((contDiff_fourCellOddP11DirectTail.continuous.mul
      contDiff_fourCellOddP13FirstOmittedMode.continuous).intervalIntegrable _ _)
    (by
      intro x
      change fourCellOddP11DirectTail (-x) *
          fourCellOddP13FirstOmittedMode (-x) =
        fourCellOddP11DirectTail x * fourCellOddP13FirstOmittedMode x
      rw [odd_fourCellOddP11DirectTail,
        odd_fourCellOddP13FirstOmittedMode]
      ring)
  rw [hfull] at hfold
  linarith

/-- Exact positive-half mass of the first omitted direction. -/
theorem integral_zero_one_fourCellOddP13FirstOmittedMode_sq :
    (∫ x : ℝ in 0..1, fourCellOddP13FirstOmittedMode x ^ 2) = 1 / 27 := by
  have hdiag := centeredLegendreL2Diagonal_closed 13
  unfold centeredLegendreL2Diagonal centeredPolynomialPair at hdiag
  have hfull :
      (∫ x : ℝ in -1..1, fourCellOddP13FirstOmittedMode x ^ 2) =
        2 / 27 := by
    rw [show (fun x : ℝ ↦ fourCellOddP13FirstOmittedMode x ^ 2) =
        fun x ↦ (centeredShiftedLegendreReal 13).eval x *
          (centeredShiftedLegendreReal 13).eval x by
      funext x
      unfold fourCellOddP13FirstOmittedMode
      ring]
    norm_num at hdiag ⊢
    exact hdiag
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP13FirstOmittedMode
    contDiff_fourCellOddP13FirstOmittedMode.continuous
    (Or.inr odd_fourCellOddP13FirstOmittedMode)
  linarith

private theorem integral_zero_one_mul_eq_zero_of_odd_orthogonal
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (huodd : Function.Odd u) (hvodd : Function.Odd v)
    (hfull : (∫ x : ℝ in -1..1, u x * v x) = 0) :
    (∫ x : ℝ in 0..1, u x * v x) = 0 := by
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ u x * v x)
    ((hu.mul hv).intervalIntegrable _ _)
    (by
      intro x
      change u (-x) * v (-x) = u x * v x
      rw [huodd, hvodd]
      ring)
  rw [hfull] at hfold
  linarith

/-! The next two omitted modes complete the short Bessel audit. -/

/-- Centered `P15`, the second omitted odd mode. -/
def fourCellOddP13SecondOmittedMode (x : ℝ) : ℝ :=
  -(centeredShiftedLegendreReal 15).eval x

theorem contDiff_fourCellOddP13SecondOmittedMode :
    ContDiff ℝ 1 fourCellOddP13SecondOmittedMode := by
  unfold fourCellOddP13SecondOmittedMode
  exact (centeredShiftedLegendreReal 15).contDiff_aeval (𝕜 := ℝ) 1 |>.neg

theorem odd_fourCellOddP13SecondOmittedMode :
    Function.Odd fourCellOddP13SecondOmittedMode := by
  intro x
  unfold fourCellOddP13SecondOmittedMode
  rw [eval_centeredShiftedLegendreReal_neg]
  norm_num

theorem fourCellOddP13SecondOmittedMode_lowMoments :
    centeredOddP1Coefficient fourCellOddP13SecondOmittedMode = 0 ∧
    centeredOddP3Coefficient fourCellOddP13SecondOmittedMode = 0 ∧
    centeredOddP5Coefficient fourCellOddP13SecondOmittedMode = 0 ∧
    centeredOddP7Coefficient fourCellOddP13SecondOmittedMode = 0 ∧
    centeredOddP9Coefficient fourCellOddP13SecondOmittedMode = 0 := by
  apply lowMoments_eq_zero_of_centeredLegendre_orthogonal
  all_goals
    unfold fourCellOddP13SecondOmittedMode
    apply integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
    norm_num

theorem integral_zero_one_fourCellOddP11DirectTail_mul_secondOmittedMode :
    (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * fourCellOddP13SecondOmittedMode x) = 0 := by
  apply integral_zero_one_mul_eq_zero_of_odd_orthogonal
    fourCellOddP11DirectTail fourCellOddP13SecondOmittedMode
    contDiff_fourCellOddP11DirectTail.continuous
    contDiff_fourCellOddP13SecondOmittedMode.continuous
    odd_fourCellOddP11DirectTail odd_fourCellOddP13SecondOmittedMode
  simpa only [fourCellOddP11DirectTail, fourCellOddP13SecondOmittedMode] using
    integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
      11 15 (by norm_num)

theorem integral_zero_one_fourCellOddP13SecondOmittedMode_sq :
    (∫ x : ℝ in 0..1, fourCellOddP13SecondOmittedMode x ^ 2) = 1 / 31 := by
  have hdiag := centeredLegendreL2Diagonal_closed 15
  unfold centeredLegendreL2Diagonal centeredPolynomialPair at hdiag
  have hfull :
      (∫ x : ℝ in -1..1, fourCellOddP13SecondOmittedMode x ^ 2) =
        2 / 31 := by
    rw [show (fun x : ℝ ↦ fourCellOddP13SecondOmittedMode x ^ 2) =
        fun x ↦ (centeredShiftedLegendreReal 15).eval x *
          (centeredShiftedLegendreReal 15).eval x by
      funext x
      unfold fourCellOddP13SecondOmittedMode
      ring]
    norm_num at hdiag ⊢
    exact hdiag
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP13SecondOmittedMode
    contDiff_fourCellOddP13SecondOmittedMode.continuous
    (Or.inr odd_fourCellOddP13SecondOmittedMode)
  linarith

/-- Centered `P17`, the third omitted odd mode. -/
def fourCellOddP13ThirdOmittedMode (x : ℝ) : ℝ :=
  -(centeredShiftedLegendreReal 17).eval x

theorem contDiff_fourCellOddP13ThirdOmittedMode :
    ContDiff ℝ 1 fourCellOddP13ThirdOmittedMode := by
  unfold fourCellOddP13ThirdOmittedMode
  exact (centeredShiftedLegendreReal 17).contDiff_aeval (𝕜 := ℝ) 1 |>.neg

theorem odd_fourCellOddP13ThirdOmittedMode :
    Function.Odd fourCellOddP13ThirdOmittedMode := by
  intro x
  unfold fourCellOddP13ThirdOmittedMode
  rw [eval_centeredShiftedLegendreReal_neg]
  norm_num

theorem fourCellOddP13ThirdOmittedMode_lowMoments :
    centeredOddP1Coefficient fourCellOddP13ThirdOmittedMode = 0 ∧
    centeredOddP3Coefficient fourCellOddP13ThirdOmittedMode = 0 ∧
    centeredOddP5Coefficient fourCellOddP13ThirdOmittedMode = 0 ∧
    centeredOddP7Coefficient fourCellOddP13ThirdOmittedMode = 0 ∧
    centeredOddP9Coefficient fourCellOddP13ThirdOmittedMode = 0 := by
  apply lowMoments_eq_zero_of_centeredLegendre_orthogonal
  all_goals
    unfold fourCellOddP13ThirdOmittedMode
    apply integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
    norm_num

theorem integral_zero_one_fourCellOddP11DirectTail_mul_thirdOmittedMode :
    (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * fourCellOddP13ThirdOmittedMode x) = 0 := by
  apply integral_zero_one_mul_eq_zero_of_odd_orthogonal
    fourCellOddP11DirectTail fourCellOddP13ThirdOmittedMode
    contDiff_fourCellOddP11DirectTail.continuous
    contDiff_fourCellOddP13ThirdOmittedMode.continuous
    odd_fourCellOddP11DirectTail odd_fourCellOddP13ThirdOmittedMode
  simpa only [fourCellOddP11DirectTail, fourCellOddP13ThirdOmittedMode] using
    integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
      11 17 (by norm_num)

theorem integral_zero_one_fourCellOddP13ThirdOmittedMode_sq :
    (∫ x : ℝ in 0..1, fourCellOddP13ThirdOmittedMode x ^ 2) = 1 / 35 := by
  have hdiag := centeredLegendreL2Diagonal_closed 17
  unfold centeredLegendreL2Diagonal centeredPolynomialPair at hdiag
  have hfull :
      (∫ x : ℝ in -1..1, fourCellOddP13ThirdOmittedMode x ^ 2) =
        2 / 35 := by
    rw [show (fun x : ℝ ↦ fourCellOddP13ThirdOmittedMode x ^ 2) =
        fun x ↦ (centeredShiftedLegendreReal 17).eval x *
          (centeredShiftedLegendreReal 17).eval x by
      funext x
      unfold fourCellOddP13ThirdOmittedMode
      ring]
    norm_num at hdiag ⊢
    exact hdiag
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP13ThirdOmittedMode
    contDiff_fourCellOddP13ThirdOmittedMode.continuous
    (Or.inr odd_fourCellOddP13ThirdOmittedMode)
  linarith

theorem integral_zero_one_firstOmittedMode_mul_secondOmittedMode :
    (∫ x : ℝ in 0..1,
      fourCellOddP13FirstOmittedMode x *
        fourCellOddP13SecondOmittedMode x) = 0 := by
  apply integral_zero_one_mul_eq_zero_of_odd_orthogonal
    fourCellOddP13FirstOmittedMode fourCellOddP13SecondOmittedMode
    contDiff_fourCellOddP13FirstOmittedMode.continuous
    contDiff_fourCellOddP13SecondOmittedMode.continuous
    odd_fourCellOddP13FirstOmittedMode odd_fourCellOddP13SecondOmittedMode
  simpa only [fourCellOddP13FirstOmittedMode,
    fourCellOddP13SecondOmittedMode] using
      integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
        13 15 (by norm_num)

theorem integral_zero_one_firstOmittedMode_mul_thirdOmittedMode :
    (∫ x : ℝ in 0..1,
      fourCellOddP13FirstOmittedMode x *
        fourCellOddP13ThirdOmittedMode x) = 0 := by
  apply integral_zero_one_mul_eq_zero_of_odd_orthogonal
    fourCellOddP13FirstOmittedMode fourCellOddP13ThirdOmittedMode
    contDiff_fourCellOddP13FirstOmittedMode.continuous
    contDiff_fourCellOddP13ThirdOmittedMode.continuous
    odd_fourCellOddP13FirstOmittedMode odd_fourCellOddP13ThirdOmittedMode
  simpa only [fourCellOddP13FirstOmittedMode,
    fourCellOddP13ThirdOmittedMode] using
      integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
        13 17 (by norm_num)

theorem integral_zero_one_secondOmittedMode_mul_thirdOmittedMode :
    (∫ x : ℝ in 0..1,
      fourCellOddP13SecondOmittedMode x *
        fourCellOddP13ThirdOmittedMode x) = 0 := by
  apply integral_zero_one_mul_eq_zero_of_odd_orthogonal
    fourCellOddP13SecondOmittedMode fourCellOddP13ThirdOmittedMode
    contDiff_fourCellOddP13SecondOmittedMode.continuous
    contDiff_fourCellOddP13ThirdOmittedMode.continuous
    odd_fourCellOddP13SecondOmittedMode odd_fourCellOddP13ThirdOmittedMode
  simpa only [fourCellOddP13SecondOmittedMode,
    fourCellOddP13ThirdOmittedMode] using
      integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
        15 17 (by norm_num)

/-! ## The selector-independent scalar moment -/

/-- The exact augmented residual row tested on the first omitted mode. -/
def fourCellOddP13AugmentedFirstOmittedMoment
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddCoreLocalBilinear
    (fourCellOddP13AugmentedGalerkinResidualProfile a3 a5 a7 a9 a11)
    fourCellOddP13FirstOmittedMode

/-- Augmented residual moment on centered `P15`. -/
def fourCellOddP13AugmentedSecondOmittedMoment
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddCoreLocalBilinear
    (fourCellOddP13AugmentedGalerkinResidualProfile a3 a5 a7 a9 a11)
    fourCellOddP13SecondOmittedMode

/-- Augmented residual moment on centered `P17`. -/
def fourCellOddP13AugmentedThirdOmittedMoment
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  fourCellOddCoreLocalBilinear
    (fourCellOddP13AugmentedGalerkinResidualProfile a3 a5 a7 a9 a11)
    fourCellOddP13ThirdOmittedMode

/-- The exact three-mode Bessel payment from `P13/P15/P17`. -/
def fourCellOddP13AugmentedThreeOmittedModeBesselBudget
    (a3 a5 a7 a9 a11 : ℝ) : ℝ :=
  27 * fourCellOddP13AugmentedFirstOmittedMoment a3 a5 a7 a9 a11 ^ 2 +
  31 * fourCellOddP13AugmentedSecondOmittedMoment a3 a5 a7 a9 a11 ^ 2 +
  35 * fourCellOddP13AugmentedThirdOmittedMoment a3 a5 a7 a9 a11 ^ 2

/-- The optimized three-mode Bessel test vector. -/
def fourCellOddP13AugmentedThreeOmittedModeTest
    (a3 a5 a7 a9 a11 : ℝ) : ℝ → ℝ := fun x ↦
  27 * fourCellOddP13AugmentedFirstOmittedMoment a3 a5 a7 a9 a11 *
      fourCellOddP13FirstOmittedMode x +
    31 * fourCellOddP13AugmentedSecondOmittedMoment a3 a5 a7 a9 a11 *
      fourCellOddP13SecondOmittedMode x +
    35 * fourCellOddP13AugmentedThirdOmittedMoment a3 a5 a7 a9 a11 *
      fourCellOddP13ThirdOmittedMode x

theorem contDiff_fourCellOddP13AugmentedThreeOmittedModeTest
    (a3 a5 a7 a9 a11 : ℝ) :
    ContDiff ℝ 1
      (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11) := by
  unfold fourCellOddP13AugmentedThreeOmittedModeTest
  exact ((contDiff_const.mul contDiff_fourCellOddP13FirstOmittedMode).add
    (contDiff_const.mul contDiff_fourCellOddP13SecondOmittedMode)).add
      (contDiff_const.mul contDiff_fourCellOddP13ThirdOmittedMode)

theorem odd_fourCellOddP13AugmentedThreeOmittedModeTest
    (a3 a5 a7 a9 a11 : ℝ) :
    Function.Odd
      (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11) := by
  intro x
  unfold fourCellOddP13AugmentedThreeOmittedModeTest
  rw [odd_fourCellOddP13FirstOmittedMode,
    odd_fourCellOddP13SecondOmittedMode,
    odd_fourCellOddP13ThirdOmittedMode]
  ring

private theorem integral_threeOmittedModeTest_mul_centeredLegendre_eq_zero
    (a3 a5 a7 a9 a11 : ℝ) (n : ℕ) (hn : n < 13) :
    (∫ x : ℝ in -1..1,
      fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11 x *
        (-(centeredShiftedLegendreReal n).eval x)) = 0 := by
  let p : ℝ → ℝ := fun x ↦ -(centeredShiftedLegendreReal n).eval x
  let A := 27 * fourCellOddP13AugmentedFirstOmittedMoment
    a3 a5 a7 a9 a11
  let B := 31 * fourCellOddP13AugmentedSecondOmittedMoment
    a3 a5 a7 a9 a11
  let C := 35 * fourCellOddP13AugmentedThirdOmittedMoment
    a3 a5 a7 a9 a11
  have hp : Continuous p := by
    dsimp only [p]
    exact ((centeredShiftedLegendreReal n).contDiff_aeval
      (𝕜 := ℝ) 1 |>.neg).continuous
  have hAI : IntervalIntegrable (fun x : ℝ ↦
      A * (fourCellOddP13FirstOmittedMode x * p x)) volume (-1) 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP13FirstOmittedMode.continuous.mul hp))
      |>.intervalIntegrable _ _
  have hBI : IntervalIntegrable (fun x : ℝ ↦
      B * (fourCellOddP13SecondOmittedMode x * p x)) volume (-1) 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP13SecondOmittedMode.continuous.mul hp))
      |>.intervalIntegrable _ _
  have hCI : IntervalIntegrable (fun x : ℝ ↦
      C * (fourCellOddP13ThirdOmittedMode x * p x)) volume (-1) 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP13ThirdOmittedMode.continuous.mul hp))
      |>.intervalIntegrable _ _
  change (∫ x : ℝ in -1..1,
    (A * fourCellOddP13FirstOmittedMode x +
      B * fourCellOddP13SecondOmittedMode x +
      C * fourCellOddP13ThirdOmittedMode x) * p x) = 0
  rw [show (fun x : ℝ ↦
      (A * fourCellOddP13FirstOmittedMode x +
        B * fourCellOddP13SecondOmittedMode x +
        C * fourCellOddP13ThirdOmittedMode x) * p x) =
      fun x ↦
        (A * (fourCellOddP13FirstOmittedMode x * p x) +
          B * (fourCellOddP13SecondOmittedMode x * p x)) +
        C * (fourCellOddP13ThirdOmittedMode x * p x) by
    funext x
    ring,
    intervalIntegral.integral_add (hAI.add hBI) hCI,
    intervalIntegral.integral_add hAI hBI,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have h13 := integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
    13 n (by omega)
  have h15 := integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
    15 n (by omega)
  have h17 := integral_neg_centeredLegendre_mul_neg_centeredLegendre_eq_zero
    17 n (by omega)
  dsimp only [p] at h13 h15 h17 ⊢
  rw [show (∫ x : ℝ in -1..1,
      fourCellOddP13FirstOmittedMode x *
        -(centeredShiftedLegendreReal n).eval x) = 0 by
      simpa only [fourCellOddP13FirstOmittedMode] using h13,
    show (∫ x : ℝ in -1..1,
      fourCellOddP13SecondOmittedMode x *
        -(centeredShiftedLegendreReal n).eval x) = 0 by
      simpa only [fourCellOddP13SecondOmittedMode] using h15,
    show (∫ x : ℝ in -1..1,
      fourCellOddP13ThirdOmittedMode x *
        -(centeredShiftedLegendreReal n).eval x) = 0 by
      simpa only [fourCellOddP13ThirdOmittedMode] using h17]
  ring

theorem fourCellOddP13AugmentedThreeOmittedModeTest_lowMoments
    (a3 a5 a7 a9 a11 : ℝ) :
    centeredOddP1Coefficient
        (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11) = 0 ∧
    centeredOddP3Coefficient
        (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11) = 0 ∧
    centeredOddP5Coefficient
        (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11) = 0 ∧
    centeredOddP7Coefficient
        (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11) = 0 ∧
    centeredOddP9Coefficient
        (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11) = 0 := by
  exact lowMoments_eq_zero_of_centeredLegendre_orthogonal
    (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11)
    (integral_threeOmittedModeTest_mul_centeredLegendre_eq_zero
      a3 a5 a7 a9 a11 1 (by omega))
    (integral_threeOmittedModeTest_mul_centeredLegendre_eq_zero
      a3 a5 a7 a9 a11 3 (by omega))
    (integral_threeOmittedModeTest_mul_centeredLegendre_eq_zero
      a3 a5 a7 a9 a11 5 (by omega))
    (integral_threeOmittedModeTest_mul_centeredLegendre_eq_zero
      a3 a5 a7 a9 a11 7 (by omega))
    (integral_threeOmittedModeTest_mul_centeredLegendre_eq_zero
      a3 a5 a7 a9 a11 9 (by omega))

theorem integral_zero_one_fourCellOddP11DirectTail_mul_threeOmittedModeTest
    (a3 a5 a7 a9 a11 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x *
        fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11 x) = 0 := by
  apply integral_zero_one_mul_eq_zero_of_odd_orthogonal
    fourCellOddP11DirectTail
    (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11)
    contDiff_fourCellOddP11DirectTail.continuous
    (contDiff_fourCellOddP13AugmentedThreeOmittedModeTest
      a3 a5 a7 a9 a11).continuous
    odd_fourCellOddP11DirectTail
    (odd_fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11)
  have h := integral_threeOmittedModeTest_mul_centeredLegendre_eq_zero
    a3 a5 a7 a9 a11 11 (by omega)
  rw [show (fun x : ℝ ↦
      fourCellOddP11DirectTail x *
        fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11 x) =
      fun x ↦
        fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11 x *
          (-(centeredShiftedLegendreReal 11).eval x) by
    funext x
    unfold fourCellOddP11DirectTail
    ring]
  exact h

/-- Exact mass of the optimized test equals the three-mode Bessel budget. -/
theorem integral_zero_one_threeOmittedModeTest_sq
    (a3 a5 a7 a9 a11 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13AugmentedThreeOmittedModeTest
        a3 a5 a7 a9 a11 x ^ 2) =
      fourCellOddP13AugmentedThreeOmittedModeBesselBudget
        a3 a5 a7 a9 a11 := by
  let A := 27 * fourCellOddP13AugmentedFirstOmittedMoment
    a3 a5 a7 a9 a11
  let B := 31 * fourCellOddP13AugmentedSecondOmittedMoment
    a3 a5 a7 a9 a11
  let C := 35 * fourCellOddP13AugmentedThirdOmittedMoment
    a3 a5 a7 a9 a11
  let r13 := fourCellOddP13FirstOmittedMode
  let r15 := fourCellOddP13SecondOmittedMode
  let r17 := fourCellOddP13ThirdOmittedMode
  have h13I : IntervalIntegrable (fun x : ℝ ↦ A ^ 2 * r13 x ^ 2)
      volume 0 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP13FirstOmittedMode.continuous.pow 2))
      |>.intervalIntegrable _ _
  have h15I : IntervalIntegrable (fun x : ℝ ↦ B ^ 2 * r15 x ^ 2)
      volume 0 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP13SecondOmittedMode.continuous.pow 2))
      |>.intervalIntegrable _ _
  have h17I : IntervalIntegrable (fun x : ℝ ↦ C ^ 2 * r17 x ^ 2)
      volume 0 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP13ThirdOmittedMode.continuous.pow 2))
      |>.intervalIntegrable _ _
  have h1315I : IntervalIntegrable (fun x : ℝ ↦
      2 * A * B * (r13 x * r15 x)) volume 0 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP13FirstOmittedMode.continuous.mul
        contDiff_fourCellOddP13SecondOmittedMode.continuous))
      |>.intervalIntegrable _ _
  have h1317I : IntervalIntegrable (fun x : ℝ ↦
      2 * A * C * (r13 x * r17 x)) volume 0 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP13FirstOmittedMode.continuous.mul
        contDiff_fourCellOddP13ThirdOmittedMode.continuous))
      |>.intervalIntegrable _ _
  have h1517I : IntervalIntegrable (fun x : ℝ ↦
      2 * B * C * (r15 x * r17 x)) volume 0 1 :=
    (continuous_const.mul
      (contDiff_fourCellOddP13SecondOmittedMode.continuous.mul
        contDiff_fourCellOddP13ThirdOmittedMode.continuous))
      |>.intervalIntegrable _ _
  change (∫ x : ℝ in 0..1,
    (A * r13 x + B * r15 x + C * r17 x) ^ 2) = _
  rw [show (fun x : ℝ ↦ (A * r13 x + B * r15 x + C * r17 x) ^ 2) =
      fun x ↦
        ((((A ^ 2 * r13 x ^ 2 + B ^ 2 * r15 x ^ 2) +
          C ^ 2 * r17 x ^ 2) + 2 * A * B * (r13 x * r15 x)) +
          2 * A * C * (r13 x * r17 x)) +
          2 * B * C * (r15 x * r17 x) by
    funext x
    ring,
    intervalIntegral.integral_add
      ((((h13I.add h15I).add h17I).add h1315I).add h1317I) h1517I,
    intervalIntegral.integral_add
      (((h13I.add h15I).add h17I).add h1315I) h1317I,
    intervalIntegral.integral_add
      ((h13I.add h15I).add h17I) h1315I,
    intervalIntegral.integral_add (h13I.add h15I) h17I,
    intervalIntegral.integral_add h13I h15I,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  dsimp only [r13, r15, r17]
  rw [integral_zero_one_fourCellOddP13FirstOmittedMode_sq,
    integral_zero_one_fourCellOddP13SecondOmittedMode_sq,
    integral_zero_one_fourCellOddP13ThirdOmittedMode_sq,
    integral_zero_one_firstOmittedMode_mul_secondOmittedMode,
    integral_zero_one_firstOmittedMode_mul_thirdOmittedMode,
    integral_zero_one_secondOmittedMode_mul_thirdOmittedMode]
  unfold fourCellOddP13AugmentedThreeOmittedModeBesselBudget
  dsimp only [A, B, C]
  ring

/-- The augmented row pairs with its optimized test by exactly the same
three-mode Bessel budget. -/
theorem fourCellOddCoreLocalBilinear_threeOmittedModeTest_eq_budget
    (a3 a5 a7 a9 a11 : ℝ) :
    fourCellOddCoreLocalBilinear
        (fourCellOddP13AugmentedGalerkinResidualProfile a3 a5 a7 a9 a11)
        (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11) =
      fourCellOddP13AugmentedThreeOmittedModeBesselBudget
        a3 a5 a7 a9 a11 := by
  let q := fourCellOddP13AugmentedGalerkinResidualProfile a3 a5 a7 a9 a11
  let A := 27 * fourCellOddP13AugmentedFirstOmittedMoment
    a3 a5 a7 a9 a11
  let B := 31 * fourCellOddP13AugmentedSecondOmittedMoment
    a3 a5 a7 a9 a11
  let C := 35 * fourCellOddP13AugmentedThirdOmittedMoment
    a3 a5 a7 a9 a11
  let r13 := fourCellOddP13FirstOmittedMode
  let r15 := fourCellOddP13SecondOmittedMode
  let r17 := fourCellOddP13ThirdOmittedMode
  have hq : ContDiff ℝ 1 q := by
    dsimp only [q]
    exact contDiff_fourCellOddP13AugmentedGalerkinResidualProfile
      a3 a5 a7 a9 a11
  have hqodd : Function.Odd q := by
    dsimp only [q]
    exact odd_fourCellOddP13AugmentedGalerkinResidualProfile
      a3 a5 a7 a9 a11
  have hA : ContDiff ℝ 1 (fun x ↦ A * r13 x) :=
    contDiff_const.mul contDiff_fourCellOddP13FirstOmittedMode
  have hB : ContDiff ℝ 1 (fun x ↦ B * r15 x) :=
    contDiff_const.mul contDiff_fourCellOddP13SecondOmittedMode
  have hC : ContDiff ℝ 1 (fun x ↦ C * r17 x) :=
    contDiff_const.mul contDiff_fourCellOddP13ThirdOmittedMode
  have hAodd : Function.Odd (fun x ↦ A * r13 x) := by
    intro x
    dsimp only [r13]
    rw [odd_fourCellOddP13FirstOmittedMode]
    ring
  have hBodd : Function.Odd (fun x ↦ B * r15 x) := by
    intro x
    dsimp only [r15]
    rw [odd_fourCellOddP13SecondOmittedMode]
    ring
  have hCodd : Function.Odd (fun x ↦ C * r17 x) := by
    intro x
    dsimp only [r17]
    rw [odd_fourCellOddP13ThirdOmittedMode]
    ring
  rw [fourCellOddCoreLocalBilinear_comm
    q (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11)
    hq.continuous
    (contDiff_fourCellOddP13AugmentedThreeOmittedModeTest
      a3 a5 a7 a9 a11).continuous]
  change fourCellOddCoreLocalBilinear
    (((fun x ↦ A * r13 x) + (fun x ↦ B * r15 x)) +
      (fun x ↦ C * r17 x)) q = _
  rw [fourCellOddCoreLocalBilinear_add_left
      ((fun x ↦ A * r13 x) + (fun x ↦ B * r15 x))
      (fun x ↦ C * r17 x) q (hA.add hB) hC hq
      (hAodd.add hBodd) hCodd hqodd,
    fourCellOddCoreLocalBilinear_add_left
      (fun x ↦ A * r13 x) (fun x ↦ B * r15 x) q
      hA hB hq hAodd hBodd hqodd,
    fourCellOddCoreLocalBilinear_const_mul_left
      r13 q contDiff_fourCellOddP13FirstOmittedMode hq
      odd_fourCellOddP13FirstOmittedMode hqodd A,
    fourCellOddCoreLocalBilinear_const_mul_left
      r15 q contDiff_fourCellOddP13SecondOmittedMode hq
      odd_fourCellOddP13SecondOmittedMode hqodd B,
    fourCellOddCoreLocalBilinear_const_mul_left
      r17 q contDiff_fourCellOddP13ThirdOmittedMode hq
      odd_fourCellOddP13ThirdOmittedMode hqodd C,
    fourCellOddCoreLocalBilinear_comm r13 q
      contDiff_fourCellOddP13FirstOmittedMode.continuous hq.continuous,
    fourCellOddCoreLocalBilinear_comm r15 q
      contDiff_fourCellOddP13SecondOmittedMode.continuous hq.continuous,
    fourCellOddCoreLocalBilinear_comm r17 q
      contDiff_fourCellOddP13ThirdOmittedMode.continuous hq.continuous]
  unfold fourCellOddP13AugmentedThreeOmittedModeBesselBudget
    fourCellOddP13AugmentedFirstOmittedMoment
    fourCellOddP13AugmentedSecondOmittedMoment
    fourCellOddP13AugmentedThirdOmittedMoment
  dsimp only [q, A, B, C, r13, r15, r17]
  unfold fourCellOddP13AugmentedFirstOmittedMoment
    fourCellOddP13AugmentedSecondOmittedMoment
    fourCellOddP13AugmentedThirdOmittedMoment
  ring

/-- Every claimed optimal-selector bound must dominate the exact finite
`P13/P15/P17` Bessel budget. -/
theorem threeOmittedModeBesselBudget_le_of_optimalNormBound
    (kappa a3 a5 a7 a9 a11 : ℝ)
    (hnorm :
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          a3 a5 a7 a9 a11 ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * kappa) :
    fourCellOddP13AugmentedThreeOmittedModeBesselBudget
        a3 a5 a7 a9 a11 ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddP13AugmentedGalerkinResidualProfile
          a3 a5 a7 a9 a11) * kappa := by
  have hselector :=
    (fourCellOddP13AugmentedResidualSelectorTwoStripNormBound_optimal_iff
      kappa a3 a5 a7 a9 a11).2 hnorm
  have hdual :=
    fourCellOddP13AugmentedGalerkinResidualL2Dual_of_selectorTwoStripNormBound
      kappa a3 a5 a7 a9 a11
      (fourCellOddP13AugmentedOptimalSelectorCoefficientOne
        a3 a5 a7 a9 a11)
      (fourCellOddP13AugmentedOptimalSelectorCoefficientThree
        a3 a5 a7 a9 a11)
      (fourCellOddP13AugmentedOptimalSelectorCoefficientFive
        a3 a5 a7 a9 a11)
      (fourCellOddP13AugmentedOptimalSelectorCoefficientSeven
        a3 a5 a7 a9 a11)
      (fourCellOddP13AugmentedOptimalSelectorCoefficientNine
        a3 a5 a7 a9 a11)
      (fourCellOddP13AugmentedOptimalSelectorCoefficientEleven
        a3 a5 a7 a9 a11) hselector
  rcases fourCellOddP13AugmentedThreeOmittedModeTest_lowMoments
      a3 a5 a7 a9 a11 with ⟨h1, h3, h5, h7, h9⟩
  have htest := hdual
    (fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11)
    (contDiff_fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11)
    (odd_fourCellOddP13AugmentedThreeOmittedModeTest a3 a5 a7 a9 a11)
    h1 h3 h5 h7 h9
    (integral_zero_one_fourCellOddP11DirectTail_mul_threeOmittedModeTest
      a3 a5 a7 a9 a11)
  rw [fourCellOddCoreLocalBilinear_threeOmittedModeTest_eq_budget,
    integral_zero_one_threeOmittedModeTest_sq] at htest
  have hbudget : 0 ≤
      fourCellOddP13AugmentedThreeOmittedModeBesselBudget
        a3 a5 a7 a9 a11 := by
    unfold fourCellOddP13AugmentedThreeOmittedModeBesselBudget
    positivity
  by_cases hzero :
      fourCellOddP13AugmentedThreeOmittedModeBesselBudget
        a3 a5 a7 a9 a11 = 0
  · rw [hzero]
    have hoptimalNonneg : 0 ≤
        fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          a3 a5 a7 a9 a11 := by
      unfold fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
        fourCellOddP13AugmentedSelectorResidualTwoStripNormSq
        fourCellOddP13TwoStripNormSq
      exact add_nonneg
        (intervalIntegral.integral_nonneg (by norm_num)
          (fun _ _ ↦ sq_nonneg _))
        (intervalIntegral.integral_nonneg (by norm_num)
          (fun _ _ ↦ sq_nonneg _))
    exact hoptimalNonneg.trans hnorm
  · have hbudgetPos : 0 <
        fourCellOddP13AugmentedThreeOmittedModeBesselBudget
          a3 a5 a7 a9 a11 := lt_of_le_of_ne hbudget (Ne.symm hzero)
    nlinarith only [htest, hbudgetPos]

/-- A strict three-mode Bessel excess refutes the proposed optimal norm. -/
theorem not_optimalNormBound_of_threeOmittedModeBessel_obstruction
    (kappa a3 a5 a7 a9 a11 : ℝ)
    (hobstruction :
      fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * kappa <
        fourCellOddP13AugmentedThreeOmittedModeBesselBudget
          a3 a5 a7 a9 a11) :
    ¬ fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          a3 a5 a7 a9 a11 ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * kappa := by
  intro hnorm
  have hbudget := threeOmittedModeBesselBudget_le_of_optimalNormBound
    kappa a3 a5 a7 a9 a11 hnorm
  linarith

/-- Exact-solution specialization of the genuine three-mode obstruction. -/
theorem fourCellOddP13AugmentedExactSolution_not_optimalNorm_of_threeModeBessel
    (hobstruction :
      fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) * (39 / 400) <
        fourCellOddP13AugmentedThreeOmittedModeBesselBudget
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4)) :
    ¬ fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4) ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) * (39 / 400) := by
  exact not_optimalNormBound_of_threeOmittedModeBessel_obstruction
    (39 / 400)
    (fourCellOddP13AugmentedRetainedSolution 0)
    (fourCellOddP13AugmentedRetainedSolution 1)
    (fourCellOddP13AugmentedRetainedSolution 2)
    (fourCellOddP13AugmentedRetainedSolution 3)
    (fourCellOddP13AugmentedRetainedSolution 4) hobstruction

/-- The same scalar excess refutes the full existential selector certificate
at `19/20`. -/
theorem fourCellOddP13AugmentedExactSolution_not_nineteenTwentieths_of_threeModeBessel
    (hobstruction :
      fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) * (39 / 400) <
        fourCellOddP13AugmentedThreeOmittedModeBesselBudget
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4)) :
    ¬ FourCellOddP13AugmentedResidualModuloSixModeTwoStripNormBound
        (1 - (19 / 20 : ℝ) ^ 2)
        (fourCellOddP13AugmentedRetainedSolution 0)
        (fourCellOddP13AugmentedRetainedSolution 1)
        (fourCellOddP13AugmentedRetainedSolution 2)
        (fourCellOddP13AugmentedRetainedSolution 3)
        (fourCellOddP13AugmentedRetainedSolution 4) := by
  intro hcertificate
  have hnorm :=
    fourCellOddP13AugmentedExactSolution_nineteenTwentieths_iff_optimalNorm.mp
      hcertificate
  exact
    (fourCellOddP13AugmentedExactSolution_not_optimalNorm_of_threeModeBessel
      hobstruction) hnorm

/-- The first omitted moment is exactly the pairing with the explicit
piecewise two-strip row. -/
theorem fourCellOddP13AugmentedFirstOmittedMoment_eq_twoStripPair
    (a3 a5 a7 a9 a11 : ℝ) :
    fourCellOddP13AugmentedFirstOmittedMoment a3 a5 a7 a9 a11 =
      fourCellOddP13AugmentedTwoStripPair a3 a5 a7 a9 a11
        fourCellOddP13FirstOmittedMode := by
  rcases fourCellOddP13FirstOmittedMode_lowMoments with
    ⟨h1, h3, h5, h7, h9⟩
  have hrow :=
    fourCellOddCoreLocalBilinear_sixMode_P13Plus_eq_twoStripRepresenter
      1 (-a3) (-a5) (-a7) (-a9) (-a11)
      fourCellOddP13FirstOmittedMode
      contDiff_fourCellOddP13FirstOmittedMode
      odd_fourCellOddP13FirstOmittedMode h1 h3 h5 h7 h9
      integral_zero_one_fourCellOddP11DirectTail_mul_firstOmittedMode
  unfold fourCellOddP13AugmentedFirstOmittedMoment
    fourCellOddP13AugmentedTwoStripPair
    fourCellOddP13AugmentedLowerRow fourCellOddP13AugmentedUpperRow
  rw [fourCellOddP13AugmentedGalerkinResidualProfile_eq_sixMode]
  exact hrow

/-- Every retained selector has zero pairing with the first omitted mode. -/
theorem integral_zero_one_sixModeSelector_mul_firstOmittedMode_eq_zero
    (b1 b3 b5 b7 b9 b11 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11 x *
        fourCellOddP13FirstOmittedMode x) = 0 := by
  rcases fourCellOddP13FirstOmittedMode_lowMoments with
    ⟨h1, h3, h5, h7, h9⟩
  unfold fourCellOddP13SixModeSelector
  exact integral_zero_one_sixMode_mul_P13Plus_eq_zero
    b1 b3 b5 b7 b9 b11 fourCellOddP13FirstOmittedMode
    contDiff_fourCellOddP13FirstOmittedMode
    odd_fourCellOddP13FirstOmittedMode h1 h3 h5 h7 h9
    integral_zero_one_fourCellOddP11DirectTail_mul_firstOmittedMode

private theorem memLp_two_restrict_of_continuous_local
    (f : ℝ → ℝ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (-1 : ℝ) 1)) :=
    hf.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
      (Icc (-1 : ℝ) 1) :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

private theorem memLp_mono_lower_strip_local
    (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1))) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (3 / 5))) := by
  apply hf.mono_measure
  apply Measure.restrict_mono
  · intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · exact le_rfl

private theorem memLp_mono_upper_strip_local
    (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1))) :
    MemLp f 2 (volume.restrict (Ioc (3 / 5 : ℝ) 1)) := by
  apply hf.mono_measure
  apply Measure.restrict_mono
  · intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  · exact le_rfl

/-- Subtracting any retained selector leaves the first omitted pairing
unchanged. -/
theorem fourCellOddP13AugmentedFirstOmittedMoment_eq_selectorResidualPair
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    fourCellOddP13AugmentedFirstOmittedMoment a3 a5 a7 a9 a11 =
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP13AugmentedResidualLowerSelectorResidual
          a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 x *
            fourCellOddP13FirstOmittedMode x) +
      ∫ x : ℝ in 3 / 5..1,
        fourCellOddP13AugmentedResidualUpperSelectorResidual
          a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 x *
            fourCellOddP13FirstOmittedMode x := by
  let L := fourCellOddP13AugmentedResidualLowerSelectorResidual
    a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  let U := fourCellOddP13AugmentedResidualUpperSelectorResidual
    a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  let S := fourCellOddP13SixModeSelector b1 b3 b5 b7 b9 b11
  let r := fourCellOddP13FirstOmittedMode
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  let μU : Measure ℝ := volume.restrict (Ioc (3 / 5 : ℝ) 1)
  have hL : MemLp L 2 μL := by
    dsimp only [L, μL]
    apply memLp_mono_lower_strip_local
    exact
      memLp_fourCellOddP13AugmentedResidualLowerSelectorResidual_two_restrict
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  have hU : MemLp U 2 μU := by
    dsimp only [U, μU]
    apply memLp_mono_upper_strip_local
    exact
      memLp_fourCellOddP13AugmentedResidualUpperSelectorResidual_two_restrict
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  have hrFull : MemLp r 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply memLp_two_restrict_of_continuous_local
    exact contDiff_fourCellOddP13FirstOmittedMode.continuous
  have hrL : MemLp r 2 μL := by
    dsimp only [μL]
    exact memLp_mono_lower_strip_local r hrFull
  have hrU : MemLp r 2 μU := by
    dsimp only [μU]
    exact memLp_mono_upper_strip_local r hrFull
  have hLprodI : IntervalIntegrable (fun x : ℝ ↦ L x * r x)
      volume 0 (3 / 5) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    simpa only [μL] using hL.integrable_mul hrL
  have hUprodI : IntervalIntegrable (fun x : ℝ ↦ U x * r x)
      volume (3 / 5) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    simpa only [μU] using hU.integrable_mul hrU
  have hS : Continuous S := by
    dsimp only [S, fourCellOddP13SixModeSelector]
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  have hr : Continuous r := by
    exact contDiff_fourCellOddP13FirstOmittedMode.continuous
  have hSL : IntervalIntegrable (fun x : ℝ ↦ S x * r x)
      volume 0 (3 / 5) := (hS.mul hr).intervalIntegrable _ _
  have hSU : IntervalIntegrable (fun x : ℝ ↦ S x * r x)
      volume (3 / 5) 1 := (hS.mul hr).intervalIntegrable _ _
  have hSsplit := intervalIntegral.integral_add_adjacent_intervals hSL hSU
  have hSzero : (∫ x : ℝ in 0..1, S x * r x) = 0 := by
    dsimp only [S, r]
    exact integral_zero_one_sixModeSelector_mul_firstOmittedMode_eq_zero
      b1 b3 b5 b7 b9 b11
  have hrawL :
      (∫ x : ℝ in 0..3 / 5,
        fourCellOddP13AugmentedLowerRow a3 a5 a7 a9 a11 x * r x) =
      (∫ x : ℝ in 0..3 / 5, L x * r x) +
        ∫ x : ℝ in 0..3 / 5, S x * r x := by
    rw [← intervalIntegral.integral_add hLprodI hSL]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [L, S]
    unfold fourCellOddP13AugmentedLowerRow
      fourCellOddP13AugmentedResidualLowerSelectorResidual
      fourCellOddP13SixModeSelector
    ring
  have hrawU :
      (∫ x : ℝ in 3 / 5..1,
        fourCellOddP13AugmentedUpperRow a3 a5 a7 a9 a11 x * r x) =
      (∫ x : ℝ in 3 / 5..1, U x * r x) +
        ∫ x : ℝ in 3 / 5..1, S x * r x := by
    rw [← intervalIntegral.integral_add hUprodI hSU]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [U, S]
    unfold fourCellOddP13AugmentedUpperRow
      fourCellOddP13AugmentedResidualUpperSelectorResidual
      fourCellOddP13SixModeSelector
    ring
  rw [fourCellOddP13AugmentedFirstOmittedMoment_eq_twoStripPair]
  unfold fourCellOddP13AugmentedTwoStripPair
  dsimp only [r] at hrawL hrawU ⊢
  rw [hrawL, hrawU]
  linarith only [hSsplit, hSzero]

private theorem sum_pair_sq_le_sum_norm_mul_sum_mass
    (A B NL NU ML MU : ℝ)
    (hNL : 0 ≤ NL) (hNU : 0 ≤ NU)
    (hML : 0 ≤ ML) (hMU : 0 ≤ MU)
    (hA : A ^ 2 ≤ NL * ML) (hB : B ^ 2 ≤ NU * MU) :
    (A + B) ^ 2 ≤ (NL + NU) * (ML + MU) := by
  have hcross : 2 * A * B ≤ NL * MU + NU * ML := by
    by_cases hab : A * B ≤ 0
    · have hright : 0 ≤ NL * MU + NU * ML :=
        add_nonneg (mul_nonneg hNL hMU) (mul_nonneg hNU hML)
      nlinarith
    · have habpos : 0 < A * B := lt_of_not_ge hab
      have hprod : (A * B) ^ 2 ≤ (NL * ML) * (NU * MU) := by
        rw [mul_pow]
        exact mul_le_mul hA hB (sq_nonneg B) (mul_nonneg hNL hML)
      have hscaled := mul_le_mul_of_nonneg_left hprod
        (by norm_num : (0 : ℝ) ≤ 4)
      have hamgm :
          4 * ((NL * ML) * (NU * MU)) ≤ (NL * MU + NU * ML) ^ 2 := by
        nlinarith only [sq_nonneg (NL * MU - NU * ML)]
      have hsquares : (2 * A * B) ^ 2 ≤
          (NL * MU + NU * ML) ^ 2 := by
        nlinarith only [hscaled, hamgm]
      have hleft : 0 ≤ 2 * A * B := by nlinarith
      have hright : 0 ≤ NL * MU + NU * ML :=
        add_nonneg (mul_nonneg hNL hMU) (mul_nonneg hNU hML)
      exact (sq_le_sq₀ hleft hright).1 hsquares
  nlinarith only [hA, hB, hcross]

/-- Bessel's inequality on the first omitted mode: every retained selector
leaves at least `27 M13²` of two-strip residual norm. -/
theorem twentySeven_mul_firstOmittedMoment_sq_le_selectorResidualNorm
    (a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 : ℝ) :
    27 * fourCellOddP13AugmentedFirstOmittedMoment
        a3 a5 a7 a9 a11 ^ 2 ≤
      fourCellOddP13AugmentedSelectorResidualTwoStripNormSq
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11 := by
  let L := fourCellOddP13AugmentedResidualLowerSelectorResidual
    a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  let U := fourCellOddP13AugmentedResidualUpperSelectorResidual
    a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  let r := fourCellOddP13FirstOmittedMode
  let μL : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  let μU : Measure ℝ := volume.restrict (Ioc (3 / 5 : ℝ) 1)
  have hL : MemLp L 2 μL := by
    dsimp only [L, μL]
    apply memLp_mono_lower_strip_local
    exact
      memLp_fourCellOddP13AugmentedResidualLowerSelectorResidual_two_restrict
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  have hU : MemLp U 2 μU := by
    dsimp only [U, μU]
    apply memLp_mono_upper_strip_local
    exact
      memLp_fourCellOddP13AugmentedResidualUpperSelectorResidual_two_restrict
        a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  have hrFull : MemLp r 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply memLp_two_restrict_of_continuous_local
    exact contDiff_fourCellOddP13FirstOmittedMode.continuous
  have hrL : MemLp r 2 μL := by
    dsimp only [μL]
    exact memLp_mono_lower_strip_local r hrFull
  have hrU : MemLp r 2 μU := by
    dsimp only [μU]
    exact memLp_mono_upper_strip_local r hrFull
  have hcauchyL := YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
    μL (fun _ : ℝ ↦ 1) L r (by simp)
      (by simpa only [div_one, Real.sqrt_one] using hL)
      (by simpa only [Real.sqrt_one, one_mul] using hrL)
  have hcauchyU := YoshidaEndpointWeightedCauchy.sq_integral_mul_le_weighted
    μU (fun _ : ℝ ↦ 1) U r (by simp)
      (by simpa only [div_one, Real.sqrt_one] using hU)
      (by simpa only [Real.sqrt_one, one_mul] using hrU)
  have hcauchyL' :
      (∫ x : ℝ in 0..3 / 5, L x * r x) ^ 2 ≤
        (∫ x : ℝ in 0..3 / 5, L x ^ 2) *
          (∫ x : ℝ in 0..3 / 5, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μL, div_one, one_mul] using hcauchyL
  have hcauchyU' :
      (∫ x : ℝ in 3 / 5..1, U x * r x) ^ 2 ≤
        (∫ x : ℝ in 3 / 5..1, U x ^ 2) *
          (∫ x : ℝ in 3 / 5..1, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μU, div_one, one_mul] using hcauchyU
  have hNL : 0 ≤ ∫ x : ℝ in 0..3 / 5, L x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hNU : 0 ≤ ∫ x : ℝ in 3 / 5..1, U x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hML : 0 ≤ ∫ x : ℝ in 0..3 / 5, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hMU : 0 ≤ ∫ x : ℝ in 3 / 5..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have htwo := sum_pair_sq_le_sum_norm_mul_sum_mass
    (∫ x : ℝ in 0..3 / 5, L x * r x)
    (∫ x : ℝ in 3 / 5..1, U x * r x)
    (∫ x : ℝ in 0..3 / 5, L x ^ 2)
    (∫ x : ℝ in 3 / 5..1, U x ^ 2)
    (∫ x : ℝ in 0..3 / 5, r x ^ 2)
    (∫ x : ℝ in 3 / 5..1, r x ^ 2)
    hNL hNU hML hMU hcauchyL' hcauchyU'
  have hrLInt : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume 0 (3 / 5) :=
    (contDiff_fourCellOddP13FirstOmittedMode.continuous.pow 2)
      |>.intervalIntegrable _ _
  have hrUInt : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2)
      volume (3 / 5) 1 :=
    (contDiff_fourCellOddP13FirstOmittedMode.continuous.pow 2)
      |>.intervalIntegrable _ _
  have hmassSplit :=
    intervalIntegral.integral_add_adjacent_intervals hrLInt hrUInt
  have hpair :=
    fourCellOddP13AugmentedFirstOmittedMoment_eq_selectorResidualPair
      a3 a5 a7 a9 a11 b1 b3 b5 b7 b9 b11
  dsimp only [L, U, r] at htwo hmassSplit
  rw [← hpair, hmassSplit,
    integral_zero_one_fourCellOddP13FirstOmittedMode_sq] at htwo
  unfold fourCellOddP13AugmentedSelectorResidualTwoStripNormSq
    fourCellOddP13TwoStripNormSq
  nlinarith

/-- In particular, the canonical optimal selector cannot evade the first
omitted-mode lower bound. -/
theorem twentySeven_mul_firstOmittedMoment_sq_le_optimalResidualNorm
    (a3 a5 a7 a9 a11 : ℝ) :
    27 * fourCellOddP13AugmentedFirstOmittedMoment
        a3 a5 a7 a9 a11 ^ 2 ≤
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
        a3 a5 a7 a9 a11 := by
  exact twentySeven_mul_firstOmittedMoment_sq_le_selectorResidualNorm
    a3 a5 a7 a9 a11
    (fourCellOddP13AugmentedOptimalSelectorCoefficientOne a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientThree a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientFive a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientSeven a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientNine a3 a5 a7 a9 a11)
    (fourCellOddP13AugmentedOptimalSelectorCoefficientEleven a3 a5 a7 a9 a11)

/-- A strict failure of the one-mode scalar test refutes the proposed
optimal-norm bound. -/
theorem not_optimalNormBound_of_firstOmittedMoment_obstruction
    (kappa a3 a5 a7 a9 a11 : ℝ)
    (hobstruction :
      fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * kappa <
        27 * fourCellOddP13AugmentedFirstOmittedMoment
          a3 a5 a7 a9 a11 ^ 2) :
    ¬ fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          a3 a5 a7 a9 a11 ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * kappa := by
  intro hnorm
  have hlower :=
    twentySeven_mul_firstOmittedMoment_sq_le_optimalResidualNorm
      a3 a5 a7 a9 a11
  linarith

/-- Exact-solution rejection interface: proving this one strict scalar
inequality is enough to rule out the production `39/400` endpoint. -/
theorem fourCellOddP13AugmentedExactSolution_not_optimalNorm_of_P13_obstruction
    (hobstruction :
      fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) * (39 / 400) <
        27 * fourCellOddP13AugmentedFirstOmittedMoment
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4) ^ 2) :
    ¬ fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4) ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) * (39 / 400) := by
  exact not_optimalNormBound_of_firstOmittedMoment_obstruction
    (39 / 400)
    (fourCellOddP13AugmentedRetainedSolution 0)
    (fourCellOddP13AugmentedRetainedSolution 1)
    (fourCellOddP13AugmentedRetainedSolution 2)
    (fourCellOddP13AugmentedRetainedSolution 3)
    (fourCellOddP13AugmentedRetainedSolution 4) hobstruction

/-! ## Structural necessary conditions for an optimal-norm claim -/

/-- Any proposed upper bound for the optimal selector norm must pass the
single exact `P13` moment test. -/
theorem fourCellOddP13AugmentedOptimalNormBound_implies_firstOmittedMomentBound
    (kappa a3 a5 a7 a9 a11 : ℝ)
    (hnorm :
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          a3 a5 a7 a9 a11 ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * kappa) :
    fourCellOddP13AugmentedFirstOmittedMoment a3 a5 a7 a9 a11 ^ 2 ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddP13AugmentedGalerkinResidualProfile
          a3 a5 a7 a9 a11) * (kappa * (1 / 27)) := by
  have hselector :=
    (fourCellOddP13AugmentedResidualSelectorTwoStripNormBound_optimal_iff
      kappa a3 a5 a7 a9 a11).2 hnorm
  have hdual :=
    fourCellOddP13AugmentedGalerkinResidualL2Dual_of_selectorTwoStripNormBound
      kappa a3 a5 a7 a9 a11
      (fourCellOddP13AugmentedOptimalSelectorCoefficientOne
        a3 a5 a7 a9 a11)
      (fourCellOddP13AugmentedOptimalSelectorCoefficientThree
        a3 a5 a7 a9 a11)
      (fourCellOddP13AugmentedOptimalSelectorCoefficientFive
        a3 a5 a7 a9 a11)
      (fourCellOddP13AugmentedOptimalSelectorCoefficientSeven
        a3 a5 a7 a9 a11)
      (fourCellOddP13AugmentedOptimalSelectorCoefficientNine
        a3 a5 a7 a9 a11)
      (fourCellOddP13AugmentedOptimalSelectorCoefficientEleven
        a3 a5 a7 a9 a11) hselector
  rcases fourCellOddP13FirstOmittedMode_lowMoments with
    ⟨h1, h3, h5, h7, h9⟩
  have htest := hdual fourCellOddP13FirstOmittedMode
    contDiff_fourCellOddP13FirstOmittedMode
    odd_fourCellOddP13FirstOmittedMode h1 h3 h5 h7 h9
    integral_zero_one_fourCellOddP11DirectTail_mul_firstOmittedMode
  rw [integral_zero_one_fourCellOddP13FirstOmittedMode_sq] at htest
  exact htest

/-- Equivalent denominator-free form: `27` times the omitted moment square
must fit below the claimed selector budget. -/
theorem twentySeven_mul_firstOmittedMoment_sq_le_of_optimalNormBound
    (kappa a3 a5 a7 a9 a11 : ℝ)
    (hnorm :
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          a3 a5 a7 a9 a11 ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * kappa) :
    27 * fourCellOddP13AugmentedFirstOmittedMoment
        a3 a5 a7 a9 a11 ^ 2 ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddP13AugmentedGalerkinResidualProfile
          a3 a5 a7 a9 a11) * kappa := by
  have h :=
    fourCellOddP13AugmentedOptimalNormBound_implies_firstOmittedMomentBound
      kappa a3 a5 a7 a9 a11 hnorm
  nlinarith

/-- At the production constant `39/400`, the whole remaining optimal-norm
claim implies one exact scalar inequality. -/
theorem thirtyNineFourHundredths_optimalNorm_implies_P13_obstruction
    (a3 a5 a7 a9 a11 : ℝ)
    (hnorm :
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          a3 a5 a7 a9 a11 ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            a3 a5 a7 a9 a11) * (39 / 400)) :
    27 * fourCellOddP13AugmentedFirstOmittedMoment
        a3 a5 a7 a9 a11 ^ 2 ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddP13AugmentedGalerkinResidualProfile
          a3 a5 a7 a9 a11) * (39 / 400) := by
  exact twentySeven_mul_firstOmittedMoment_sq_le_of_optimalNormBound
    (39 / 400) a3 a5 a7 a9 a11 hnorm

/-- Exact-solution specialization of the `P13` obstruction. -/
theorem fourCellOddP13AugmentedExactSolution_optimalNorm_implies_P13_obstruction
    (hnorm :
      fourCellOddP13AugmentedOptimalSelectorResidualTwoStripNormSq
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4) ≤
        fourCellOddCoreLocalQuadratic
          (fourCellOddP13AugmentedGalerkinResidualProfile
            (fourCellOddP13AugmentedRetainedSolution 0)
            (fourCellOddP13AugmentedRetainedSolution 1)
            (fourCellOddP13AugmentedRetainedSolution 2)
            (fourCellOddP13AugmentedRetainedSolution 3)
            (fourCellOddP13AugmentedRetainedSolution 4)) * (39 / 400)) :
    27 * fourCellOddP13AugmentedFirstOmittedMoment
        (fourCellOddP13AugmentedRetainedSolution 0)
        (fourCellOddP13AugmentedRetainedSolution 1)
        (fourCellOddP13AugmentedRetainedSolution 2)
        (fourCellOddP13AugmentedRetainedSolution 3)
        (fourCellOddP13AugmentedRetainedSolution 4) ^ 2 ≤
      fourCellOddCoreLocalQuadratic
        (fourCellOddP13AugmentedGalerkinResidualProfile
          (fourCellOddP13AugmentedRetainedSolution 0)
          (fourCellOddP13AugmentedRetainedSolution 1)
          (fourCellOddP13AugmentedRetainedSolution 2)
          (fourCellOddP13AugmentedRetainedSolution 3)
          (fourCellOddP13AugmentedRetainedSolution 4)) * (39 / 400) := by
  exact thirtyNineFourHundredths_optimalNorm_implies_P13_obstruction
    (fourCellOddP13AugmentedRetainedSolution 0)
    (fourCellOddP13AugmentedRetainedSolution 1)
    (fourCellOddP13AugmentedRetainedSolution 2)
    (fourCellOddP13AugmentedRetainedSolution 3)
    (fourCellOddP13AugmentedRetainedSolution 4) hnorm

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorP13ObstructionStructural
