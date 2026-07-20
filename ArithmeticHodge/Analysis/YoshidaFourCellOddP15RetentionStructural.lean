import ArithmeticHodge.Analysis.YoshidaFourCellOddP13RetentionStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP15RetentionStructural

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
open YoshidaFourCellOddP13AugmentedResidualRepresenterStructural
open YoshidaFourCellOddP13RetentionStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# Genuine centered `P15` retention

This file adjoins the centered `P15` direction to the seven retained odd
modes through `P13`.  Orthogonality is obtained from the all-degree
shifted-Legendre theorem and a degree bound on the retained polynomial;
`P15` is never expanded into monomials.
-/

/-- Classical centered `P15`, with the production odd-basis sign. -/
def fourCellOddP15DirectTail (x : ℝ) : ℝ :=
  -(centeredShiftedLegendreReal 15).eval x

theorem contDiff_fourCellOddP15DirectTail :
    ContDiff ℝ 1 fourCellOddP15DirectTail := by
  unfold fourCellOddP15DirectTail
  exact (centeredShiftedLegendreReal 15).contDiff_aeval (𝕜 := ℝ) 1 |>.neg

theorem odd_fourCellOddP15DirectTail :
    Function.Odd fourCellOddP15DirectTail := by
  intro x
  unfold fourCellOddP15DirectTail
  rw [eval_centeredShiftedLegendreReal_neg]
  norm_num

private def fourCellOddP15SevenModePolynomial
    (b1 b3 b5 b7 b9 b11 b13 : ℝ) : ℝ[X] :=
  fourCellOddP13SixModePolynomial b1 b3 b5 b7 b9 b11 +
    b13 • (-(centeredShiftedLegendreReal 13))

private theorem fourCellOddP15SevenModePolynomial_eval
    (b1 b3 b5 b7 b9 b11 b13 x : ℝ) :
    (fourCellOddP15SevenModePolynomial
      b1 b3 b5 b7 b9 b11 b13).eval x =
      fourCellOddP13SevenModeProfile b1 b3 b5 b7 b9 b11 b13 x := by
  unfold fourCellOddP15SevenModePolynomial
    fourCellOddP13SevenModeProfile
  simp only [Polynomial.eval_add, Polynomial.eval_smul, Polynomial.eval_neg,
    smul_eq_mul]
  rw [fourCellOddP13SixModePolynomial_eval]
  unfold fourCellOddP13DirectTail
  ring

private theorem fourCellOddP15SevenModePolynomial_natDegree_lt_fifteen
    (b1 b3 b5 b7 b9 b11 b13 : ℝ) :
    (fourCellOddP15SevenModePolynomial
      b1 b3 b5 b7 b9 b11 b13).natDegree < 15 := by
  unfold fourCellOddP15SevenModePolynomial
    fourCellOddP13SixModePolynomial fourCellOddFiveModePolynomial
  compute_degree
  apply max_lt
  · omega
  · apply max_lt
    · exact (natDegree_centeredShiftedLegendreReal_le 11).trans_lt (by omega)
    · exact (natDegree_centeredShiftedLegendreReal_le 13).trans_lt (by omega)

/-- Every seven-mode profile through `P13` is positive-half orthogonal to
the genuine centered `P15` direction. -/
theorem integral_zero_one_fourCellOddP13SevenModeProfile_mul_P15_eq_zero
    (b1 b3 b5 b7 b9 b11 b13 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP13SevenModeProfile b1 b3 b5 b7 b9 b11 b13 x *
        fourCellOddP15DirectTail x) = 0 := by
  let p : ℝ[X] :=
    fourCellOddP15SevenModePolynomial b1 b3 b5 b7 b9 b11 b13
  let u : ℝ → ℝ :=
    fourCellOddP13SevenModeProfile b1 b3 b5 b7 b9 b11 b13
  have hpdeg : p.natDegree < 15 := by
    dsimp only [p]
    exact fourCellOddP15SevenModePolynomial_natDegree_lt_fifteen
      b1 b3 b5 b7 b9 b11 b13
  have horth :=
    integral_eval_mul_centeredShiftedLegendreReal_eq_zero 15 p hpdeg
  have hfull :
      (∫ x : ℝ in -1..1, u x * fourCellOddP15DirectTail x) = 0 := by
    rw [show (fun x : ℝ ↦ u x * fourCellOddP15DirectTail x) =
        fun x ↦ -(p.eval x * (centeredShiftedLegendreReal 15).eval x) by
      funext x
      dsimp only [u, p]
      rw [fourCellOddP15SevenModePolynomial_eval]
      unfold fourCellOddP15DirectTail
      ring,
      intervalIntegral.integral_neg,
      horth,
      neg_zero]
  have hu : Continuous u := by
    dsimp only [u]
    exact (contDiff_fourCellOddP13SevenModeProfile _ _ _ _ _ _ _).continuous
  have huodd : Function.Odd u := by
    dsimp only [u]
    exact odd_fourCellOddP13SevenModeProfile _ _ _ _ _ _ _
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ u x * fourCellOddP15DirectTail x)
    ((hu.mul contDiff_fourCellOddP15DirectTail.continuous)
      |>.intervalIntegrable _ _)
    (by
      intro x
      change u (-x) * fourCellOddP15DirectTail (-x) =
        u x * fourCellOddP15DirectTail x
      rw [huodd, odd_fourCellOddP15DirectTail]
      ring)
  rw [hfull] at hfold
  linarith

theorem integral_zero_one_centeredP1_mul_fourCellOddP15DirectTail_eq_zero :
    (∫ x : ℝ in 0..1, centeredP1 x * fourCellOddP15DirectTail x) = 0 := by
  simpa [fourCellOddP13SevenModeProfile, fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SevenModeProfile_mul_P15_eq_zero
      1 0 0 0 0 0 0

theorem integral_zero_one_centeredP3_mul_fourCellOddP15DirectTail_eq_zero :
    (∫ x : ℝ in 0..1, centeredP3 x * fourCellOddP15DirectTail x) = 0 := by
  simpa [fourCellOddP13SevenModeProfile, fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SevenModeProfile_mul_P15_eq_zero
      0 1 0 0 0 0 0

theorem integral_zero_one_factorTwoCenteredP5_mul_fourCellOddP15DirectTail_eq_zero :
    (∫ x : ℝ in 0..1,
      factorTwoCenteredP5 x * fourCellOddP15DirectTail x) = 0 := by
  simpa [fourCellOddP13SevenModeProfile, fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SevenModeProfile_mul_P15_eq_zero
      0 0 1 0 0 0 0

theorem integral_zero_one_factorTwoCenteredP7_mul_fourCellOddP15DirectTail_eq_zero :
    (∫ x : ℝ in 0..1,
      factorTwoCenteredP7 x * fourCellOddP15DirectTail x) = 0 := by
  simpa [fourCellOddP13SevenModeProfile, fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SevenModeProfile_mul_P15_eq_zero
      0 0 0 1 0 0 0

theorem integral_zero_one_factorTwoCenteredP9_mul_fourCellOddP15DirectTail_eq_zero :
    (∫ x : ℝ in 0..1,
      factorTwoCenteredP9 x * fourCellOddP15DirectTail x) = 0 := by
  simpa [fourCellOddP13SevenModeProfile, fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SevenModeProfile_mul_P15_eq_zero
      0 0 0 0 1 0 0

theorem integral_zero_one_fourCellOddP11DirectTail_mul_P15_eq_zero :
    (∫ x : ℝ in 0..1,
      fourCellOddP11DirectTail x * fourCellOddP15DirectTail x) = 0 := by
  simpa [fourCellOddP13SevenModeProfile, fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SevenModeProfile_mul_P15_eq_zero
      0 0 0 0 0 1 0

theorem integral_zero_one_fourCellOddP13DirectTail_mul_P15_eq_zero :
    (∫ x : ℝ in 0..1,
      fourCellOddP13DirectTail x * fourCellOddP15DirectTail x) = 0 := by
  simpa [fourCellOddP13SevenModeProfile, fourCellOddP13SixModeProfile,
    fourCellOddOneThreeFiveSevenNineLowProfile,
    fourCellOddOneThreeFiveLowProfile,
    factorTwoOddStructuralLowProfile] using
    integral_zero_one_fourCellOddP13SevenModeProfile_mul_P15_eq_zero
      0 0 0 0 0 0 1

/-- Exact positive-half mass of the genuine centered `P15` direction. -/
theorem integral_zero_one_fourCellOddP15DirectTail_sq :
    (∫ x : ℝ in 0..1, fourCellOddP15DirectTail x ^ 2) = 1 / 31 := by
  have hdiag := centeredLegendreL2Diagonal_closed 15
  unfold centeredLegendreL2Diagonal centeredPolynomialPair at hdiag
  have hfull :
      (∫ x : ℝ in -1..1, fourCellOddP15DirectTail x ^ 2) = 2 / 31 := by
    rw [show (fun x : ℝ ↦ fourCellOddP15DirectTail x ^ 2) =
        fun x ↦ (centeredShiftedLegendreReal 15).eval x *
          (centeredShiftedLegendreReal 15).eval x by
      funext x
      unfold fourCellOddP15DirectTail
      ring]
    norm_num at hdiag ⊢
    exact hdiag
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP15DirectTail contDiff_fourCellOddP15DirectTail.continuous
    (Or.inr odd_fourCellOddP15DirectTail)
  linarith

/-- The eight retained odd modes through `P15`. -/
def fourCellOddP15EightModeProfile
    (b1 b3 b5 b7 b9 b11 b13 b15 : ℝ) : ℝ → ℝ := fun x ↦
  fourCellOddP13SevenModeProfile b1 b3 b5 b7 b9 b11 b13 x +
    b15 * fourCellOddP15DirectTail x

theorem contDiff_fourCellOddP15EightModeProfile
    (b1 b3 b5 b7 b9 b11 b13 b15 : ℝ) :
    ContDiff ℝ 1
      (fourCellOddP15EightModeProfile b1 b3 b5 b7 b9 b11 b13 b15) := by
  unfold fourCellOddP15EightModeProfile
  exact (contDiff_fourCellOddP13SevenModeProfile
    b1 b3 b5 b7 b9 b11 b13).add
      (contDiff_const.mul contDiff_fourCellOddP15DirectTail)

theorem odd_fourCellOddP15EightModeProfile
    (b1 b3 b5 b7 b9 b11 b13 b15 : ℝ) :
    Function.Odd
      (fourCellOddP15EightModeProfile b1 b3 b5 b7 b9 b11 b13 b15) := by
  intro x
  unfold fourCellOddP15EightModeProfile
  rw [odd_fourCellOddP13SevenModeProfile, odd_fourCellOddP15DirectTail]
  ring

/-- An arbitrary retained selector through the genuine `P15` mode. -/
def fourCellOddP15EightModeSelector
    (b1 b3 b5 b7 b9 b11 b13 b15 : ℝ) : ℝ → ℝ :=
  fourCellOddP15EightModeProfile b1 b3 b5 b7 b9 b11 b13 b15

/-- Exact positive-half mass of an arbitrary retained eight-mode selector. -/
theorem integral_zero_one_fourCellOddP15EightModeSelector_sq
    (b1 b3 b5 b7 b9 b11 b13 b15 : ℝ) :
    (∫ x : ℝ in 0..1,
      fourCellOddP15EightModeSelector
        b1 b3 b5 b7 b9 b11 b13 b15 x ^ 2) =
      b1 ^ 2 / 3 + b3 ^ 2 / 7 + b5 ^ 2 / 11 +
        b7 ^ 2 / 15 + b9 ^ 2 / 19 + b11 ^ 2 / 23 +
        b13 ^ 2 / 27 + b15 ^ 2 / 31 := by
  let u := fourCellOddP13SevenModeProfile b1 b3 b5 b7 b9 b11 b13
  let r := fourCellOddP15DirectTail
  have hu : Continuous u := by
    dsimp only [u]
    exact (contDiff_fourCellOddP13SevenModeProfile _ _ _ _ _ _ _).continuous
  have hr : Continuous r := by
    dsimp only [r]
    exact contDiff_fourCellOddP15DirectTail.continuous
  have huuI : IntervalIntegrable (fun x : ℝ ↦ u x ^ 2) volume 0 1 :=
    (hu.pow 2).intervalIntegrable _ _
  have hurI : IntervalIntegrable (fun x : ℝ ↦ u x * r x) volume 0 1 :=
    (hu.mul hr).intervalIntegrable _ _
  have hrrI : IntervalIntegrable (fun x : ℝ ↦ r x ^ 2) volume 0 1 :=
    (hr.pow 2).intervalIntegrable _ _
  unfold fourCellOddP15EightModeSelector fourCellOddP15EightModeProfile
  rw [show (fun x : ℝ ↦
      (fourCellOddP13SevenModeProfile b1 b3 b5 b7 b9 b11 b13 x +
        b15 * fourCellOddP15DirectTail x) ^ 2) =
      fun x ↦ u x ^ 2 + 2 * b15 * (u x * r x) + b15 ^ 2 * r x ^ 2 by
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
        b7 ^ 2 / 15 + b9 ^ 2 / 19 + b11 ^ 2 / 23 + b13 ^ 2 / 27 by
    dsimp only [u]
    exact integral_zero_one_fourCellOddP13SevenModeSelector_sq
      b1 b3 b5 b7 b9 b11 b13,
    show (∫ x : ℝ in 0..1, u x * r x) = 0 by
      dsimp only [u, r]
      exact integral_zero_one_fourCellOddP13SevenModeProfile_mul_P15_eq_zero
        b1 b3 b5 b7 b9 b11 b13,
    show (∫ x : ℝ in 0..1, r x ^ 2) = 1 / 31 by
      dsimp only [r]
      exact integral_zero_one_fourCellOddP15DirectTail_sq]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP15RetentionStructural
