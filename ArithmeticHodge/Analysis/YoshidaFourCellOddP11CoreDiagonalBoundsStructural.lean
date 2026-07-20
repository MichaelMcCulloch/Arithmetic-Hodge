import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreEntryBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreDiagonalBoundsStructural

noncomputable section

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open EndpointPotentialPolynomialPairBilinearStructural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open ShiftedLegendrePolynomialGap
open YoshidaConstantBounds
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialLegendreDiagonalStructural
open YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddP11CoreEntryBoundsStructural
open YoshidaFourCellOddP11FiveModeThreeHalvesStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaRegularKernelBound

/-!
# Structural diagonal bound for the first augmented odd mode

The augmented six-mode Galerkin block needs one new diagonal entry, the core
quadratic of the genuine `P₁₁` tail direction.  Its positivity does not
require a sampled kernel estimate: the already proved infinite-dimensional
odd coercivity theorem applies directly, because `P₁₁` is exactly
orthogonal to `P₁` and has positive-half mass `1 / 23`.
-/

/-- Rational, assumption-free lower bound for the new `P₁₁` diagonal.
This is the normalized coercivity floor `(343 / 12500) * (1 / 23)`. -/
theorem threeHundredFortyThree_div_twoHundredEightySevenThousandFiveHundred_le_fourCellOddCoreLocalQuadratic_P11 :
    (343 / 287500 : ℝ) ≤
      fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail := by
  have hP1 : centeredOddP1Coefficient fourCellOddP11DirectTail = 0 :=
    fourCellOddP11DirectTail_moments.1
  have h :=
    threeHundredFortyThree_div_twelveThousandFiveHundred_mul_mass_le_coreLocalQuadratic_of_P1
      fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail
      odd_fourCellOddP11DirectTail hP1
  rw [integral_zero_one_fourCellOddP11DirectTail_sq] at h
  norm_num at h ⊢
  exact h

/-- In particular, the augmented diagonal is strictly positive. -/
theorem fourCellOddCoreLocalQuadratic_P11_pos :
    0 < fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail := by
  have h :=
    threeHundredFortyThree_div_twoHundredEightySevenThousandFiveHundred_le_fourCellOddCoreLocalQuadratic_P11
  norm_num at h ⊢
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 343 / 287500) h

/-! ## The sole smooth diagonal moment -/

/-- The smooth-kernel moment left intact in the exact `P₁₁` diagonal. -/
def fourCellOddP11CoreDiagonalRegularMoment : ℝ :=
  ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation fourCellOddP11DirectTail t

theorem factorTwoIntrinsicEnergy_fourCellOddP11DirectTail :
    factorTwoIntrinsicEnergy fourCellOddP11DirectTail = (2 / 23 : ℝ) := by
  have hfold := integral_sq_eq_two_mul_positiveHalf
    fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail.continuous
    (Or.inr odd_fourCellOddP11DirectTail)
  unfold factorTwoIntrinsicEnergy
  rw [hfold, integral_zero_one_fourCellOddP11DirectTail_sq]
  norm_num

/-- Cauchy control of the whole smooth correction.  This is an
infinite-dimensional correlation estimate, not a quadrature certificate. -/
theorem fourCellOddP11CoreDiagonalRegularCorrection_sq_le :
    (2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreDiagonalRegularMoment) ^ 2 ≤
      (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 529 : ℝ) := by
  let I : ℝ := ∫ t : ℝ in 0..2,
    |factorTwoCenteredCorrelationBilinear
      fourCellOddP11DirectTail fourCellOddP11DirectTail t|
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      factorTwoCenteredCorrelationBilinear
        fourCellOddP11DirectTail fourCellOddP11DirectTail t
  have hregular : |R| ≤ (1 / 20 : ℝ) * I := by
    simpa only [R, I] using
      abs_fourCellRegularBilinear_le_one_twentieth_integral_abs
        fourCellOddP11DirectTail fourCellOddP11DirectTail
        contDiff_fourCellOddP11DirectTail.continuous
        contDiff_fourCellOddP11DirectTail.continuous
        odd_fourCellOddP11DirectTail odd_fourCellOddP11DirectTail
  have hI : I ^ 2 ≤ (2 / 23 : ℝ) * (2 / 23 : ℝ) := by
    have h :=
      ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural.integral_abs_factorTwoCenteredCorrelationBilinear_sq_le_energy_mul
        fourCellOddP11DirectTail fourCellOddP11DirectTail
        contDiff_fourCellOddP11DirectTail.continuous
        contDiff_fourCellOddP11DirectTail.continuous
    simpa only [I, factorTwoIntrinsicEnergy_fourCellOddP11DirectTail] using h
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _t _ht ↦ abs_nonneg _)
  have hR :
      (2 * fourCellOperatorHalfWidth * R) ^ 2 ≤
        (fourCellOperatorHalfWidth / 10) ^ 2 * I ^ 2 := by
    have habs :
        |2 * fourCellOperatorHalfWidth * R| ≤
          (fourCellOperatorHalfWidth / 10) * I := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity :
        0 ≤ (2 : ℝ)), abs_of_nonneg ha0]
      nlinarith
    calc
      (2 * fourCellOperatorHalfWidth * R) ^ 2 =
          |2 * fourCellOperatorHalfWidth * R| ^ 2 := by rw [sq_abs]
      _ ≤ ((fourCellOperatorHalfWidth / 10) * I) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (div_nonneg ha0 (by norm_num)) hI0)).2 habs
      _ = (fourCellOperatorHalfWidth / 10) ^ 2 * I ^ 2 := by ring
  have hmul := mul_le_mul_of_nonneg_left hI
    (sq_nonneg (fourCellOperatorHalfWidth / 10))
  have hfinal :
      (2 * fourCellOperatorHalfWidth * R) ^ 2 ≤
        (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 529 : ℝ) := by
    calc
      (2 * fourCellOperatorHalfWidth * R) ^ 2 ≤
          (fourCellOperatorHalfWidth / 10) ^ 2 * I ^ 2 := hR
      _ ≤ (fourCellOperatorHalfWidth / 10) ^ 2 *
          ((2 / 23 : ℝ) * (2 / 23 : ℝ)) := hmul
      _ = (fourCellOperatorHalfWidth / 10) ^ 2 * (4 / 529 : ℝ) := by
        ring
  simpa only [R, fourCellOddP11CoreDiagonalRegularMoment,
    factorTwoCenteredCorrelationBilinear_self] using hfinal

private theorem fourCellOperatorHalfWidth_le_one_half :
    fourCellOperatorHalfWidth ≤ (1 / 2 : ℝ) := by
  have hlog := strict_log_two_bounds.2
  unfold fourCellOperatorHalfWidth
  nlinarith

/-- Fully rational square radius for the smooth diagonal correction. -/
theorem fourCellOddP11CoreDiagonalRegularCorrection_sq_le_rational :
    (2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreDiagonalRegularMoment) ^ 2 ≤
      (1 / 230 : ℝ) ^ 2 := by
  have h := fourCellOddP11CoreDiagonalRegularCorrection_sq_le
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha := fourCellOperatorHalfWidth_le_one_half
  nlinarith [sq_nonneg (fourCellOperatorHalfWidth - 1 / 2)]

/-- Absolute-value form of the same rational radius. -/
theorem abs_fourCellOddP11CoreDiagonalRegularCorrection_le :
    |2 * fourCellOperatorHalfWidth *
        fourCellOddP11CoreDiagonalRegularMoment| ≤ (1 / 230 : ℝ) := by
  have h := fourCellOddP11CoreDiagonalRegularCorrection_sq_le_rational
  rw [← sq_abs] at h
  nlinarith [abs_nonneg (2 * fourCellOperatorHalfWidth *
    fourCellOddP11CoreDiagonalRegularMoment)]

/-! ## Exact nonsingular diagonal data -/

set_option maxHeartbeats 10000000 in
theorem fourCellOddEndpointStripEvenMass_P11_eq :
    fourCellOddEndpointStripEvenMass fourCellOddP11DirectTail =
      (233000508101952 / 11920928955078125 : ℝ) := by
  rw [show fourCellOddEndpointStripEvenMass fourCellOddP11DirectTail =
      fourCellOddEndpointStripEvenMassBilinear
        fourCellOddP11DirectTail fourCellOddP11DirectTail by
    unfold fourCellOddEndpointStripEvenMass
      fourCellOddEndpointStripEvenMassBilinear
    congr 2
    funext z
    ring]
  rw [fourCellOddEndpointStripEvenMassBilinear_eq_integral
    fourCellOddP11DirectTail fourCellOddP11DirectTail
    contDiff_fourCellOddP11DirectTail.continuous
    contDiff_fourCellOddP11DirectTail.continuous]
  unfold fourCellOddP11DirectTail
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  norm_num

set_option maxHeartbeats 10000000 in
theorem fourCellOddEndpointStripOddMass_P11_eq :
    fourCellOddEndpointStripOddMass fourCellOddP11DirectTail =
      (1939619493150242 / 274181365966796875 : ℝ) := by
  rw [show fourCellOddEndpointStripOddMass fourCellOddP11DirectTail =
      fourCellOddEndpointStripOddMassBilinear
        fourCellOddP11DirectTail fourCellOddP11DirectTail by
    unfold fourCellOddEndpointStripOddMass
      fourCellOddEndpointStripOddMassBilinear
    congr 2
    funext z
    ring]
  rw [fourCellOddEndpointStripOddMassBilinear_eq_integral
    fourCellOddP11DirectTail fourCellOddP11DirectTail
    contDiff_fourCellOddP11DirectTail.continuous
    contDiff_fourCellOddP11DirectTail.continuous]
  unfold fourCellOddP11DirectTail
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  norm_num

private theorem endpointPotentialLegendreDiagonal_eleven_eq :
    endpointPotentialLegendreDiagonal 11 =
      (3708740681 / 30786816060 : ℝ) -
        (2 / 23 : ℝ) * Real.log 2 := by
  have h0 := endpointPotentialLegendreDiagonal_zero
  have h1r := endpointPotentialLegendreDiagonal_succ 0
  norm_num [h0] at h1r
  have h1 : endpointPotentialLegendreDiagonal 1 =
      (8 / 9 : ℝ) - (2 / 3) * Real.log 2 := by linarith
  have h2r := endpointPotentialLegendreDiagonal_succ 1
  norm_num [h1] at h2r
  have h2 : endpointPotentialLegendreDiagonal 2 =
      (41 / 75 : ℝ) - (2 / 5) * Real.log 2 := by linarith
  have h3r := endpointPotentialLegendreDiagonal_succ 2
  norm_num [h2] at h3r
  have h3 : endpointPotentialLegendreDiagonal 3 =
      (289 / 735 : ℝ) - (2 / 7) * Real.log 2 := by linarith
  have h4r := endpointPotentialLegendreDiagonal_succ 3
  norm_num [h3] at h4r
  have h4 : endpointPotentialLegendreDiagonal 4 =
      (1739 / 5670 : ℝ) - (2 / 9) * Real.log 2 := by linarith
  have h5r := endpointPotentialLegendreDiagonal_succ 4
  norm_num [h4] at h5r
  have h5 : endpointPotentialLegendreDiagonal 5 =
      (19157 / 76230 : ℝ) - (2 / 11) * Real.log 2 := by linarith
  have h6r := endpointPotentialLegendreDiagonal_succ 5
  norm_num [h5] at h6r
  have h6 : endpointPotentialLegendreDiagonal 6 =
      (249251 / 1171170 : ℝ) - (2 / 13) * Real.log 2 := by linarith
  have h7r := endpointPotentialLegendreDiagonal_succ 6
  norm_num [h6] at h7r
  have h7 : endpointPotentialLegendreDiagonal 7 =
      (249383 / 1351350 : ℝ) - (2 / 15) * Real.log 2 := by linarith
  have h8r := endpointPotentialLegendreDiagonal_succ 7
  norm_num [h7] at h8r
  have h8 : endpointPotentialLegendreDiagonal 8 =
      (1696405 / 10414404 : ℝ) - (2 / 17) * Real.log 2 := by linarith
  have h9r := endpointPotentialLegendreDiagonal_succ 8
  norm_num [h8] at h9r
  have h9 : endpointPotentialLegendreDiagonal 9 =
      (32239703 / 221152932 : ℝ) - (2 / 19) * Real.log 2 := by linarith
  have h10r := endpointPotentialLegendreDiagonal_succ 9
  norm_num [h9] at h10r
  have h10 : endpointPotentialLegendreDiagonal 10 =
      (161227687 / 1222160940 : ℝ) - (2 / 21) * Real.log 2 := by linarith
  have h11r := endpointPotentialLegendreDiagonal_succ 10
  norm_num [h10] at h11r
  linarith

/-- Exact positive-half endpoint-potential diagonal of `P₁₁`. -/
theorem integral_endpointPotential_P11_sq_eq :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * fourCellOddP11DirectTail x ^ 2) =
      (1 / 2 : ℝ) *
        ((3708740681 / 30786816060 : ℝ) -
          (2 / 23 : ℝ) * Real.log 2) := by
  let p : ℝ[X] := -(centeredShiftedLegendreReal 11)
  have hpodd : Function.Odd (fun x : ℝ ↦ p.eval x) := by
    intro x
    dsimp only [p]
    simp only [Polynomial.eval_neg]
    rw [eval_centeredShiftedLegendreReal_neg]
    norm_num
  have h := integral_zero_one_endpointPotential_polynomial_sq_eq_half_pair
    p hpodd
  have hpair : endpointPotentialPolynomialPair p p =
      endpointPotentialLegendreDiagonal 11 := by
    dsimp only [p]
    rw [endpointPotentialPolynomialPair_neg_left,
      endpointPotentialPolynomialPair_neg_right]
    simp only [neg_neg]
    rfl
  rw [hpair, endpointPotentialLegendreDiagonal_eleven_eq] at h
  calc
    (∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * fourCellOddP11DirectTail x ^ 2) =
        ∫ x : ℝ in 0..1,
          yoshidaEndpointPotential x * (p.eval x) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [p]
      unfold fourCellOddP11DirectTail
      simp
    _ = _ := h

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreDiagonalBoundsStructural
