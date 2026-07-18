import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCenteredP9Structural

noncomputable section

open ShiftedLegendreBasis
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaCoercivityNumerics
open YoshidaEndpointPotentialLegendreDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicResidual

/-!
# The first omitted odd Legendre mode

The cutoff-nine tail starts with centered `P9`.  Its endpoint-potential mass
is obtained from the all-degree Jacobi recurrence, not by expanding and
integrating the degree-eighteen square.  The resulting coarse rational upper
bound is the quantitative input needed by the `P7/P9` survivor obstruction.
-/

/-- Classical centered Legendre `P9`, normalized by `P9(1) = 1`. -/
def factorTwoCenteredP9 (x : ℝ) : ℝ :=
  -(shiftedLegendreReal 9).eval ((x + 1) / 2)

theorem factorTwoCenteredP9_eq (x : ℝ) :
    factorTwoCenteredP9 x =
      (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128 := by
  unfold factorTwoCenteredP9 shiftedLegendreReal
  simp [Polynomial.shiftedLegendre, Finset.sum_range_succ, Nat.choose]
  ring

theorem continuous_factorTwoCenteredP9 : Continuous factorTwoCenteredP9 := by
  rw [show factorTwoCenteredP9 = fun x ↦
      (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128 by
    funext x
    exact factorTwoCenteredP9_eq x]
  fun_prop

theorem odd_factorTwoCenteredP9 : Function.Odd factorTwoCenteredP9 := by
  intro x
  rw [factorTwoCenteredP9_eq, factorTwoCenteredP9_eq]
  ring

theorem locallyLipschitzOn_factorTwoCenteredP9 :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) factorTwoCenteredP9 := by
  have h : ContDiff ℝ 1 factorTwoCenteredP9 := by
    rw [show factorTwoCenteredP9 = fun x ↦
        (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
          4620 * x ^ 3 + 315 * x) / 128 by
      funext x
      exact factorTwoCenteredP9_eq x]
    fun_prop
  exact h.locallyLipschitz.locallyLipschitzOn

theorem centeredPullback_factorTwoCenteredP9 (t : ℝ) :
    centeredPullback factorTwoCenteredP9 t =
      -(shiftedLegendreReal 9).eval t := by
  unfold centeredPullback factorTwoCenteredP9
  congr 2
  ring

theorem factorTwoCenteredP9_momentsVanishBelow :
    centeredLegendreMomentsVanishBelow factorTwoCenteredP9 9 := by
  intro n hn
  rw [show (fun t : unitInterval ↦
      centeredPullback factorTwoCenteredP9 (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) =
      fun t : unitInterval ↦
        -((shiftedLegendreReal 9).eval (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) by
    funext t
    rw [centeredPullback_factorTwoCenteredP9]
    ring]
  rw [integral_neg]
  change -(∫ t : unitInterval,
    (fun x : ℝ ↦ (shiftedLegendreReal 9).eval x *
      (shiftedLegendreReal n).eval x) (t : ℝ)) = 0
  rw [integral_unitInterval_eq_intervalIntegral
      (fun x : ℝ ↦ (shiftedLegendreReal 9).eval x *
        (shiftedLegendreReal n).eval x),
    integral_shiftedLegendreReal_mul_eq_zero (by omega), neg_zero]

theorem factorTwoCenteredP9_energy :
    factorTwoIntrinsicEnergy factorTwoCenteredP9 = 2 / 19 := by
  unfold factorTwoIntrinsicEnergy
  rw [show (fun x : ℝ ↦ factorTwoCenteredP9 x ^ 2) = fun x ↦
      ((12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128) ^ 2 by
    funext x
    rw [factorTwoCenteredP9_eq]]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

/-! ## Structural endpoint-potential mass -/

/-- Nine applications of the all-degree diagonal recurrence. -/
theorem endpointPotentialLegendreDiagonal_nine :
    endpointPotentialLegendreDiagonal 9 =
      32239703 / 221152932 - (2 / 19 : ℝ) * Real.log 2 := by
  have h0 := endpointPotentialLegendreDiagonal_zero
  have h1 := endpointPotentialLegendreDiagonal_succ 0
  have h2 := endpointPotentialLegendreDiagonal_succ 1
  have h3 := endpointPotentialLegendreDiagonal_succ 2
  have h4 := endpointPotentialLegendreDiagonal_succ 3
  have h5 := endpointPotentialLegendreDiagonal_succ 4
  have h6 := endpointPotentialLegendreDiagonal_succ 5
  have h7 := endpointPotentialLegendreDiagonal_succ 6
  have h8 := endpointPotentialLegendreDiagonal_succ 7
  have h9 := endpointPotentialLegendreDiagonal_succ 8
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [h0] at h1
  have d1 : endpointPotentialLegendreDiagonal 1 =
      8 / 9 - (2 / 3 : ℝ) * Real.log 2 := by
    linarith
  rw [d1] at h2
  have d2 : endpointPotentialLegendreDiagonal 2 =
      41 / 75 - (2 / 5 : ℝ) * Real.log 2 := by
    linarith
  rw [d2] at h3
  have d3 : endpointPotentialLegendreDiagonal 3 =
      289 / 735 - (2 / 7 : ℝ) * Real.log 2 := by
    linarith
  rw [d3] at h4
  have d4 : endpointPotentialLegendreDiagonal 4 =
      1739 / 5670 - (2 / 9 : ℝ) * Real.log 2 := by
    linarith
  rw [d4] at h5
  have d5 : endpointPotentialLegendreDiagonal 5 =
      19157 / 76230 - (2 / 11 : ℝ) * Real.log 2 := by
    linarith
  rw [d5] at h6
  have d6 : endpointPotentialLegendreDiagonal 6 =
      249251 / 1171170 - (2 / 13 : ℝ) * Real.log 2 := by
    linarith
  rw [d6] at h7
  have d7 : endpointPotentialLegendreDiagonal 7 =
      249383 / 1351350 - (2 / 15 : ℝ) * Real.log 2 := by
    linarith
  rw [d7] at h8
  have d8 : endpointPotentialLegendreDiagonal 8 =
      1696405 / 10414404 - (2 / 17 : ℝ) * Real.log 2 := by
    linarith
  rw [d8] at h9
  linarith

theorem factorTwoCenteredP9_potential_eq_legendreDiagonal :
    factorTwoIntrinsicPotentialEnergy factorTwoCenteredP9 =
      endpointPotentialLegendreDiagonal 9 := by
  unfold factorTwoIntrinsicPotentialEnergy
    endpointPotentialLegendreDiagonal endpointPotentialPolynomialPair
  apply intervalIntegral.integral_congr
  intro x _hx
  change YoshidaEndpointPotentialBound.yoshidaEndpointPotential x *
      factorTwoCenteredP9 x ^ 2 =
    YoshidaEndpointPotentialBound.yoshidaEndpointPotential x *
      (centeredShiftedLegendreReal 9).eval x *
      (centeredShiftedLegendreReal 9).eval x
  rw [eval_centeredShiftedLegendreReal]
  unfold factorTwoCenteredP9
  ring

theorem factorTwoCenteredP9_potential_exact :
    factorTwoIntrinsicPotentialEnergy factorTwoCenteredP9 =
      32239703 / 221152932 - (2 / 19 : ℝ) * Real.log 2 := by
  rw [factorTwoCenteredP9_potential_eq_legendreDiagonal,
    endpointPotentialLegendreDiagonal_nine]

/-- Coarse rational upper bound used by the survivor obstruction. -/
theorem factorTwoCenteredP9_potential_lt_seventy_three_thousandths :
    factorTwoIntrinsicPotentialEnergy factorTwoCenteredP9 < 73 / 1000 := by
  rw [factorTwoCenteredP9_potential_exact]
  have hlog := log_two_gt_693_div_1000
  linarith

theorem factorTwoCenteredP9_survivor_reserve_lt_three_fortieths :
    1 / 23750 + (1 / 2 : ℝ) *
        factorTwoIntrinsicPotentialEnergy factorTwoCenteredP9 < 3 / 80 := by
  have hpot := factorTwoCenteredP9_potential_lt_seventy_three_thousandths
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCenteredP9Structural
