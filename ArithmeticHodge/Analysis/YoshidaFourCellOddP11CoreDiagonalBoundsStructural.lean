import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreEntryBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreDiagonalBoundsStructural

noncomputable section

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open EndpointPotentialPolynomialPairBilinearStructural
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogEigen
open ShiftedLegendreOrthogonality
open ShiftedLegendrePolynomialGap
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaEndpointOcticPotential
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialLegendreDiagonalStructural
open YoshidaEndpointEvenTailRepresenter
open YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddP11CoreEntryBoundsStructural
open YoshidaFourCellOddP11FiveModeThreeHalvesStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
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

/-! ## Exact singular diagonal data -/

private theorem centeredRawLogEnergy_eq_bilinear_self
    (w : ℝ → ℝ) :
    centeredRawLogEnergy w = centeredRawLogBilinear w w := by
  unfold centeredRawLogEnergy centeredRawLogBilinear
  apply intervalIntegral.integral_congr
  intro x _hx
  apply intervalIntegral.integral_congr
  intro y _hy
  ring

private theorem integral_shiftedLegendreReal_sq_closed (n : ℕ) :
    (∫ x : ℝ in 0..1, (shiftedLegendreReal n).eval x ^ 2) =
      1 / (2 * (n : ℝ) + 1) := by
  have hdiag := centeredLegendreL2Diagonal_closed n
  unfold centeredLegendreL2Diagonal centeredPolynomialPair at hdiag
  have htransport := integral_comp_two_mul_sub_one
    (fun x : ℝ ↦ (centeredShiftedLegendreReal n).eval x ^ 2)
  rw [show (fun t : ℝ ↦
      (centeredShiftedLegendreReal n).eval (2 * t - 1) ^ 2) =
      fun t ↦ (shiftedLegendreReal n).eval t ^ 2 by
    funext t
    rw [eval_centeredShiftedLegendreReal]
    congr 2
    ring] at htransport
  rw [show (fun x : ℝ ↦
      (centeredShiftedLegendreReal n).eval x ^ 2) = fun x ↦
      (centeredShiftedLegendreReal n).eval x *
        (centeredShiftedLegendreReal n).eval x by
    funext x
    ring,
    hdiag] at htransport
  calc
    (∫ x : ℝ in 0..1, (shiftedLegendreReal n).eval x ^ 2) =
        (1 / 2 : ℝ) * (2 / (2 * (n : ℝ) + 1)) := htransport
    _ = 1 / (2 * (n : ℝ) + 1) := by ring

private theorem shiftedLogEnergyBilinear_legendre_ne
    {m n : ℕ} (hmn : m ≠ n) :
    shiftedLogEnergyBilinear
        (shiftedLegendreReal m) (shiftedLegendreReal n) = 0 := by
  rw [shiftedLogEnergyBilinear_apply,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦
      (shiftedLegendreReal m).eval x *
        (2 * (harmonic n : ℝ) * (shiftedLegendreReal n).eval x)) =
      fun x ↦ (2 * (harmonic n : ℝ)) *
        ((shiftedLegendreReal m).eval x *
          (shiftedLegendreReal n).eval x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    ShiftedLegendreBasis.integral_shiftedLegendreReal_mul_eq_zero hmn]
  ring

private theorem shiftedLogEnergyBilinear_legendre_self (n : ℕ) :
    shiftedLogEnergyBilinear
        (shiftedLegendreReal n) (shiftedLegendreReal n) =
      2 * (harmonic n : ℝ) / (2 * (n : ℝ) + 1) := by
  rw [shiftedLogEnergyBilinear_apply,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦
      (shiftedLegendreReal n).eval x *
        (2 * (harmonic n : ℝ) * (shiftedLegendreReal n).eval x)) =
      fun x ↦ (2 * (harmonic n : ℝ)) *
        ((shiftedLegendreReal n).eval x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    integral_shiftedLegendreReal_sq_closed]
  ring

private theorem shiftedLogEnergyBilinear_legendre_eq (m n : ℕ) :
    shiftedLogEnergyBilinear
        (shiftedLegendreReal m) (shiftedLegendreReal n) =
      if m = n then 2 * (harmonic n : ℝ) / (2 * (n : ℝ) + 1)
      else 0 := by
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl, shiftedLogEnergyBilinear_legendre_self]
  · rw [if_neg hmn, shiftedLogEnergyBilinear_legendre_ne hmn]

private theorem centeredRawLogBilinear_eq_four_mul_shiftedPair_of_polynomials
    (q r : ℝ → ℝ) (p s : ℝ[X]) (hr : Continuous r)
    (hqmode : ∀ t : ℝ, centeredPullback q t = p.eval t)
    (hrmode : ∀ t : ℝ, centeredPullback r t = s.eval t) :
    centeredRawLogBilinear q r =
      4 * shiftedLogEnergyBilinear s p := by
  rw [centeredRawLogBilinear_polynomialMode_eq_four_mul_pair
    p q r hr hqmode,
    shiftedLogEnergyBilinear_apply,
    ← integral_unitInterval_eq_intervalIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hrmode]

private theorem centeredPullback_fourCellOddP11DirectTail
    (t : ℝ) :
  centeredPullback fourCellOddP11DirectTail t =
      (-(shiftedLegendreReal 11)).eval t := by
  unfold centeredPullback fourCellOddP11DirectTail
  simp only [Polynomial.eval_neg]
  rw [eval_centeredShiftedLegendreReal]
  congr 3
  ring

/-- Exact global raw-log energy of the first augmented mode, obtained from
the `P₁₁` logarithmic eigenvalue. -/
theorem centeredRawLogEnergy_fourCellOddP11DirectTail_eq :
    centeredRawLogEnergy fourCellOddP11DirectTail =
      (83711 / 79695 : ℝ) := by
  rw [centeredRawLogEnergy_eq_bilinear_self,
    centeredRawLogBilinear_eq_four_mul_shiftedPair_of_polynomials
      fourCellOddP11DirectTail fourCellOddP11DirectTail
      (-(shiftedLegendreReal 11)) (-(shiftedLegendreReal 11))
      contDiff_fourCellOddP11DirectTail.continuous
      centeredPullback_fourCellOddP11DirectTail
      centeredPullback_fourCellOddP11DirectTail]
  simp only [map_neg, LinearMap.neg_apply, neg_neg,
    shiftedLogEnergyBilinear_legendre_self]
  norm_num [harmonic, Finset.sum_range_succ]

private def p11EndpointStripOddShiftedPolynomial : ℝ[X] := -(
  (5088276 / 48828125 : ℝ) • shiftedLegendreReal 1 +
    (8502676 / 48828125 : ℝ) • shiftedLegendreReal 3 +
    (15968084 / 48828125 : ℝ) • shiftedLegendreReal 5 +
    (25716 / 1953125 : ℝ) • shiftedLegendreReal 7 +
    (2964 / 48828125 : ℝ) • shiftedLegendreReal 9 +
    (1 / 48828125 : ℝ) • shiftedLegendreReal 11)

set_option maxHeartbeats 2000000 in
private theorem centeredPullback_endpointStripOdd_P11_eq_shiftedPolynomial
    (t : ℝ) :
    centeredPullback
        (fourCellOddEndpointStripOdd fourCellOddP11DirectTail) t =
      p11EndpointStripOddShiftedPolynomial.eval t := by
  unfold centeredPullback fourCellOddEndpointStripOdd
    fourCellOddEndpointStripPullback fourCellOddP11DirectTail
    p11EndpointStripOddShiftedPolynomial
  simp only [Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring

/-- Exact raw-log energy of the reflection-odd endpoint strip. -/
theorem centeredRawLogEnergy_endpointStripOdd_P11_eq :
    centeredRawLogEnergy
        (fourCellOddEndpointStripOdd fourCellOddP11DirectTail) =
      (51364238588241191471 / 190007686614990234375 : ℝ) := by
  have hstrip : Continuous
      (fourCellOddEndpointStripOdd fourCellOddP11DirectTail) := by
    exact continuous_fourCellOddEndpointStripOdd
      fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail.continuous
  rw [centeredRawLogEnergy_eq_bilinear_self,
    centeredRawLogBilinear_eq_four_mul_shiftedPair_of_polynomials
      (fourCellOddEndpointStripOdd fourCellOddP11DirectTail)
      (fourCellOddEndpointStripOdd fourCellOddP11DirectTail)
      p11EndpointStripOddShiftedPolynomial
      p11EndpointStripOddShiftedPolynomial hstrip
      centeredPullback_endpointStripOdd_P11_eq_shiftedPolynomial
      centeredPullback_endpointStripOdd_P11_eq_shiftedPolynomial]
  unfold p11EndpointStripOddShiftedPolynomial
  simp only [map_neg, LinearMap.neg_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    shiftedLogEnergyBilinear_legendre_eq]
  norm_num [harmonic, Finset.sum_range_succ]

/-- Exact physical raw-log energy of the adverse endpoint strip. -/
theorem fourCellOddEndpointStripOddRawEnergy_P11_eq :
    fourCellOddEndpointStripOddRawEnergy fourCellOddP11DirectTail =
      (51364238588241191471 / 950038433074951171875 : ℝ) := by
  unfold fourCellOddEndpointStripOddRawEnergy
  rw [centeredRawLogEnergy_endpointStripOdd_P11_eq]
  ring

private theorem fourCellOddRawStripCancellationReserve_eq_raw_sub_strip
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    fourCellOddRawStripCancellationReserve w =
      (1 / 4 : ℝ) * centeredRawLogEnergy w -
        (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w := by
  have hwLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hfold := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hwLocal hodd
  unfold fourCellOddRawStripCancellationReserve
  rw [← hfold]
  ring

/-- Exact retained raw reserve in the new diagonal. -/
theorem fourCellOddRawStripCancellationReserve_P11_eq :
    fourCellOddRawStripCancellationReserve fourCellOddP11DirectTail =
      (83711 / 318780 : ℝ) -
        (1 / 2 : ℝ) *
          (51364238588241191471 / 950038433074951171875 : ℝ) := by
  rw [fourCellOddRawStripCancellationReserve_eq_raw_sub_strip
      fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail
      odd_fourCellOddP11DirectTail,
    centeredRawLogEnergy_fourCellOddP11DirectTail_eq,
    fourCellOddEndpointStripOddRawEnergy_P11_eq]
  ring

/-! ## Complete exact diagonal -/

/-- Every explicitly evaluated part of the `P₁₁` core diagonal.  The
only omitted summand is the smooth regular-kernel correction. -/
def fourCellOddP11CoreDiagonalAlgebraicPart : ℝ :=
  (16063548470776166525119823 /
      44485751152038574218750000 : ℝ) +
    (3419392193194654 / 274181365966796875 : ℝ) *
      (Real.sqrt 2 * Real.log 2) -
    (93 / 1150 : ℝ) * Real.log 2 -
    (2 / 23 : ℝ) *
      (Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi)

/-- Exact structural normal form for the augmented diagonal.  All singular,
prime, mass, and endpoint-potential pieces are evaluated; one smooth moment
remains intact. -/
theorem fourCellOddCoreLocalQuadratic_P11_eq_algebraic_sub_regular :
    fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail =
      fourCellOddP11CoreDiagonalAlgebraicPart -
        2 * fourCellOperatorHalfWidth *
          fourCellOddP11CoreDiagonalRegularMoment := by
  rw [fourCellOddCoreLocalQuadratic_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointQuadratic
    fourCellOddRetainedPrimePotentialQuadratic
    fourCellOddSignedMassRegularQuadratic
  rw [fourCellOddRawStripCancellationReserve_P11_eq,
    fourCellOddEndpointStripEvenMass_P11_eq,
    fourCellOddEndpointStripOddMass_P11_eq,
    integral_endpointPotential_P11_sq_eq,
    integral_zero_one_fourCellOddP11DirectTail_sq]
  unfold fourCellOddP11CoreDiagonalAlgebraicPart
    fourCellOddP11CoreDiagonalRegularMoment
  ring

/-- Rational-radius enclosure around the exact algebraic diagonal. -/
theorem fourCellOddCoreLocalQuadratic_P11_algebraic_enclosure :
    fourCellOddP11CoreDiagonalAlgebraicPart - (1 / 230 : ℝ) ≤
        fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail ∧
      fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail ≤
        fourCellOddP11CoreDiagonalAlgebraicPart + (1 / 230 : ℝ) := by
  have hregular := abs_fourCellOddP11CoreDiagonalRegularCorrection_le
  rw [abs_le] at hregular
  rw [fourCellOddCoreLocalQuadratic_P11_eq_algebraic_sub_regular]
  constructor <;> linarith

private theorem log_five_four_lt_one_fourth :
    Real.log (5 / 4 : ℝ) < (1 / 4 : ℝ) := by
  have h := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 5 / 4)
    (by norm_num : (5 / 4 : ℝ) ≠ 1)
  norm_num at h ⊢
  exact h

private theorem fourCellScalar_lt_16057_div_10000 :
    Real.log (2 * fourCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi <
      (16057 / 10000 : ℝ) := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hwidth :
      Real.log (2 * fourCellOperatorHalfWidth) =
        Real.log (5 / 4 : ℝ) + Real.log (Real.log 2) := by
    rw [show 2 * fourCellOperatorHalfWidth =
        (5 / 4 : ℝ) * Real.log 2 by
      unfold fourCellOperatorHalfWidth
      ring,
      Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  rw [hwidth]
  linarith [log_five_four_lt_one_fourth,
    strict_log_log_two_bounds.2, strict_euler_gamma_bounds.2,
    strict_log_pi_bounds.2]

private theorem sqrt_two_mul_log_two_lower :
    (141421 / 100000 : ℝ) * (6931 / 10000 : ℝ) <
      Real.sqrt 2 * Real.log 2 := by
  have hs := sqrt_two_kernel_bounds.1
  have hl := strict_log_two_bounds.1
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  calc
    (141421 / 100000 : ℝ) * (6931 / 10000 : ℝ) <
        Real.sqrt 2 * (6931 / 10000 : ℝ) :=
      mul_lt_mul_of_pos_right hs (by norm_num)
    _ < Real.sqrt 2 * Real.log 2 := mul_lt_mul_of_pos_left hl hspos

/-- Strong rational lower bound for the actual augmented diagonal.  This is
the scale needed by the rank-one Schur step; it is much sharper than the
uniform coercivity floor because the full `P₁₁` structure is retained. -/
theorem seventeen_div_oneHundred_lt_fourCellOddCoreLocalQuadratic_P11 :
    (17 / 100 : ℝ) <
      fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail := by
  have hA :
      (17 / 100 : ℝ) + 1 / 230 <
        fourCellOddP11CoreDiagonalAlgebraicPart := by
    have halpha := sqrt_two_mul_log_two_lower
    have hlog := strict_log_two_bounds.2
    have hscalar := fourCellScalar_lt_16057_div_10000
    unfold fourCellOddP11CoreDiagonalAlgebraicPart
    nlinarith
  have henclosure :=
    fourCellOddCoreLocalQuadratic_P11_algebraic_enclosure.1
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreDiagonalBoundsStructural
