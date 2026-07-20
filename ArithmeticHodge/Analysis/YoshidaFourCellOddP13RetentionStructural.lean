import ArithmeticHodge.Analysis.YoshidaFourCellOddP13AugmentedOptimalSelectorStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP13RetentionStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialLegendreOffDiagonalStructural
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddP11FiveModeThreeHalvesStructural
open YoshidaFourCellOddP13AugmentedOptimalSelectorStructural
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# Genuine centered `P13` retention

The existing cutoff-13 construction retains the six odd modes through
`P11`.  This file adjoins the genuine centered `P13` direction, with the
same sign convention as `fourCellOddP11DirectTail`, and records the exact
seven-mode positive-half Gram diagonal.

All vanishing statements below come from all-degree shifted-Legendre
orthogonality.  No coefficient expansion of `P13` is used.
-/

/-- Classical centered `P13`, with the sign convention of the production
odd basis. -/
def fourCellOddP13DirectTail (x : ℝ) : ℝ :=
  -(centeredShiftedLegendreReal 13).eval x

theorem contDiff_fourCellOddP13DirectTail :
    ContDiff ℝ 1 fourCellOddP13DirectTail := by
  unfold fourCellOddP13DirectTail
  exact (centeredShiftedLegendreReal 13).contDiff_aeval (𝕜 := ℝ) 1 |>.neg

theorem odd_fourCellOddP13DirectTail :
    Function.Odd fourCellOddP13DirectTail := by
  intro x
  unfold fourCellOddP13DirectTail
  rw [eval_centeredShiftedLegendreReal_neg]
  norm_num

/-- The retained six-mode polynomial has degree strictly below `13`.
This is the only finite-degree fact used in the P13 orthogonality proof. -/
private theorem fourCellOddP13SixModePolynomial_natDegree_lt_thirteen
    (b1 b3 b5 b7 b9 b11 : ℝ) :
    (fourCellOddP13SixModePolynomial b1 b3 b5 b7 b9 b11).natDegree < 13 := by
  unfold fourCellOddP13SixModePolynomial fourCellOddFiveModePolynomial
  compute_degree
  apply max_lt
  · omega
  · exact (natDegree_centeredShiftedLegendreReal_le 11).trans_lt (by omega)

/-- Every retained six-mode profile is positive-half orthogonal to the
genuine centered `P13` direction. -/
theorem integral_zero_one_fourCellOddP13SixModeProfile_mul_P13_eq_zero
    (b1 b3 b5 b7 b9 b11 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13SixModeProfile b1 b3 b5 b7 b9 b11 x *
        fourCellOddP13DirectTail x) = 0 := by
  let p : ℝ[X] :=
    fourCellOddP13SixModePolynomial b1 b3 b5 b7 b9 b11
  let u : ℝ → ℝ :=
    fourCellOddP13SixModeProfile b1 b3 b5 b7 b9 b11
  have hpdeg : p.natDegree < 13 := by
    dsimp only [p]
    exact fourCellOddP13SixModePolynomial_natDegree_lt_thirteen
      b1 b3 b5 b7 b9 b11
  have horth :=
    integral_eval_mul_centeredShiftedLegendreReal_eq_zero 13 p hpdeg
  have hfull :
      (∫ x : ℝ in -1..1, u x * fourCellOddP13DirectTail x) = 0 := by
    rw [show (fun x : ℝ ↦ u x * fourCellOddP13DirectTail x) =
        fun x ↦ -(p.eval x * (centeredShiftedLegendreReal 13).eval x) by
      funext x
      dsimp only [u, p]
      rw [fourCellOddP13SixModePolynomial_eval]
      unfold fourCellOddP13DirectTail
      ring,
      intervalIntegral.integral_neg,
      horth,
      neg_zero]
  have hu : Continuous u := by
    dsimp only [u]
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  have huodd : Function.Odd u := by
    dsimp only [u]
    exact odd_fourCellOddP13SixModeProfile _ _ _ _ _ _
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ u x * fourCellOddP13DirectTail x)
    ((hu.mul contDiff_fourCellOddP13DirectTail.continuous)
      |>.intervalIntegrable _ _)
    (by
      intro x
      change u (-x) * fourCellOddP13DirectTail (-x) =
        u x * fourCellOddP13DirectTail x
      rw [huodd, odd_fourCellOddP13DirectTail]
      ring)
  rw [hfull] at hfold
  linarith

theorem integral_zero_one_centeredP1_mul_fourCellOddP13DirectTail_eq_zero :
    (∫ x : ℝ in 0..1,
      centeredP1 x * fourCellOddP13DirectTail x) = 0 := by
  simpa [fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SixModeProfile_mul_P13_eq_zero
      1 0 0 0 0 0

theorem integral_zero_one_centeredP3_mul_fourCellOddP13DirectTail_eq_zero :
    (∫ x : ℝ in 0..1,
      centeredP3 x * fourCellOddP13DirectTail x) = 0 := by
  simpa [fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SixModeProfile_mul_P13_eq_zero
      0 1 0 0 0 0

theorem integral_zero_one_factorTwoCenteredP5_mul_fourCellOddP13DirectTail_eq_zero :
    (∫ x : ℝ in 0..1,
      factorTwoCenteredP5 x * fourCellOddP13DirectTail x) = 0 := by
  simpa [fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SixModeProfile_mul_P13_eq_zero
      0 0 1 0 0 0

theorem integral_zero_one_factorTwoCenteredP7_mul_fourCellOddP13DirectTail_eq_zero :
    (∫ x : ℝ in 0..1,
      factorTwoCenteredP7 x * fourCellOddP13DirectTail x) = 0 := by
  simpa [fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SixModeProfile_mul_P13_eq_zero
      0 0 0 1 0 0

theorem integral_zero_one_factorTwoCenteredP9_mul_fourCellOddP13DirectTail_eq_zero :
    (∫ x : ℝ in 0..1,
      factorTwoCenteredP9 x * fourCellOddP13DirectTail x) = 0 := by
  simpa [fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SixModeProfile_mul_P13_eq_zero
      0 0 0 0 1 0

theorem integral_zero_one_fourCellOddP11DirectTail_mul_P13_eq_zero :
    (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * fourCellOddP13DirectTail x) = 0 := by
  simpa [fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SixModeProfile_mul_P13_eq_zero
      0 0 0 0 0 1

/-- Exact positive-half mass of the genuine centered `P13` direction. -/
theorem integral_zero_one_fourCellOddP13DirectTail_sq :
    (∫ x : ℝ in 0..1, fourCellOddP13DirectTail x ^ 2) = 1 / 27 := by
  have hdiag := centeredLegendreL2Diagonal_closed 13
  unfold centeredLegendreL2Diagonal centeredPolynomialPair at hdiag
  have hfull :
      (∫ x : ℝ in -1..1, fourCellOddP13DirectTail x ^ 2) = 2 / 27 := by
    rw [show (fun x : ℝ ↦ fourCellOddP13DirectTail x ^ 2) =
        fun x ↦ (centeredShiftedLegendreReal 13).eval x *
          (centeredShiftedLegendreReal 13).eval x by
      funext x
      unfold fourCellOddP13DirectTail
      ring]
    norm_num at hdiag ⊢
    exact hdiag
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP13DirectTail contDiff_fourCellOddP13DirectTail.continuous
    (Or.inr odd_fourCellOddP13DirectTail)
  linarith

/-- The seven retained odd modes through `P13`. -/
def fourCellOddP13SevenModeProfile
    (b1 b3 b5 b7 b9 b11 b13 : ℝ) : ℝ → ℝ := fun x ↦
  fourCellOddP13SixModeProfile b1 b3 b5 b7 b9 b11 x +
    b13 * fourCellOddP13DirectTail x

theorem contDiff_fourCellOddP13SevenModeProfile
    (b1 b3 b5 b7 b9 b11 b13 : ℝ) :
    ContDiff ℝ 1
      (fourCellOddP13SevenModeProfile b1 b3 b5 b7 b9 b11 b13) := by
  unfold fourCellOddP13SevenModeProfile
  exact (contDiff_fourCellOddP13SixModeProfile b1 b3 b5 b7 b9 b11).add
    (contDiff_const.mul contDiff_fourCellOddP13DirectTail)

theorem odd_fourCellOddP13SevenModeProfile
    (b1 b3 b5 b7 b9 b11 b13 : ℝ) :
    Function.Odd
      (fourCellOddP13SevenModeProfile b1 b3 b5 b7 b9 b11 b13) := by
  intro x
  unfold fourCellOddP13SevenModeProfile
  rw [odd_fourCellOddP13SixModeProfile, odd_fourCellOddP13DirectTail]
  ring

/-- An arbitrary retained selector through the genuine `P13` mode. -/
def fourCellOddP13SevenModeSelector
    (b1 b3 b5 b7 b9 b11 b13 : ℝ) : ℝ → ℝ :=
  fourCellOddP13SevenModeProfile b1 b3 b5 b7 b9 b11 b13

/-- Exact positive-half mass of an arbitrary retained seven-mode selector. -/
theorem integral_zero_one_fourCellOddP13SevenModeSelector_sq
    (b1 b3 b5 b7 b9 b11 b13 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13SevenModeSelector b1 b3 b5 b7 b9 b11 b13 x ^ 2) =
      b1 ^ 2 / 3 + b3 ^ 2 / 7 + b5 ^ 2 / 11 +
        b7 ^ 2 / 15 + b9 ^ 2 / 19 + b11 ^ 2 / 23 + b13 ^ 2 / 27 := by
  let u := fourCellOddP13SixModeProfile b1 b3 b5 b7 b9 b11
  let r := fourCellOddP13DirectTail
  have hu : Continuous u := by
    dsimp only [u]
    exact (contDiff_fourCellOddP13SixModeProfile _ _ _ _ _ _).continuous
  have hr : Continuous r := by
    dsimp only [r]
    exact contDiff_fourCellOddP13DirectTail.continuous
  have huuI : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2) volume 0 1 :=
    (hu.pow 2).intervalIntegrable _ _
  have hurI : IntervalIntegrable (fun x : ℝ ↦ u x * r x) volume 0 1 :=
    (hu.mul hr).intervalIntegrable _ _
  have hrrI : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2) volume 0 1 :=
    (hr.pow 2).intervalIntegrable _ _
  unfold fourCellOddP13SevenModeSelector fourCellOddP13SevenModeProfile
  rw [show (fun x : ℝ ↦
      (fourCellOddP13SixModeProfile b1 b3 b5 b7 b9 b11 x +
        b13 * fourCellOddP13DirectTail x) ^ 2) =
      fun x ↦ u x ^ 2 + 2 * b13 * (u x * r x) + b13 ^ 2 * r x ^ 2 by
    funext x
    dsimp only [u, r]
    ring,
    intervalIntegral.integral_add
      (huuI.add (hurI.const_mul _)) (hrrI.const_mul _),
    intervalIntegral.integral_add huuI (hurI.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [show (∫ x : ℝ in 0..1, u x ^ 2) =
      b1 ^ 2 / 3 + b3 ^ 2 / 7 + b5 ^ 2 / 11 +
        b7 ^ 2 / 15 + b9 ^ 2 / 19 + b11 ^ 2 / 23 by
    dsimp only [u]
    exact integral_zero_one_fourCellOddP13SixModeSelector_sq
      b1 b3 b5 b7 b9 b11,
    show (∫ x : ℝ in 0..1, u x * r x) = 0 by
      dsimp only [u, r]
      exact integral_zero_one_fourCellOddP13SixModeProfile_mul_P13_eq_zero
        b1 b3 b5 b7 b9 b11,
    show (∫ x : ℝ in 0..1, r x ^ 2) = 1 / 27 by
      dsimp only [r]
      exact integral_zero_one_fourCellOddP13DirectTail_sq]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP13RetentionStructural
