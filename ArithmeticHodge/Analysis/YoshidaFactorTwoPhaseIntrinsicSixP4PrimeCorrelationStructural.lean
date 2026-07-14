import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural

set_option autoImplicit false

open Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PrimeCorrelationStructural

noncomputable section

open YoshidaFactorTwoCenteredPhysical
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationLoewnerSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural

/-!
# Structural retained-prime bounds for the intrinsic `P4` correlations

The retained `p = 3` lag already lies in a short interval by the global
odd-power logarithm bounds.  On that interval the sum and difference of the
`P0-P4` and `P2-P4` overlap polynomials are both strictly decreasing.  This
gives the sharp rational bounds needed by the signed endpoint Schur proofs
without sampling or interval-certificate replay.
-/

/-- Sum of the two low-to-`P4` overlap polynomials. -/
def factorTwoIntrinsicP4CorrelationSum (t : ℝ) : ℝ :=
  factorTwoIntrinsicP4Correlation04 t + factorTwoIntrinsicP4Correlation24 t

/-- Difference of the two low-to-`P4` overlap polynomials. -/
def factorTwoIntrinsicP4CorrelationDifference (t : ℝ) : ℝ :=
  factorTwoIntrinsicP4Correlation24 t - factorTwoIntrinsicP4Correlation04 t

private def factorTwoIntrinsicP4CorrelationSumShift (y : ℝ) : ℝ :=
  (1 - 11 * y - 9 * y ^ 2 + 37 * y ^ 3 + 15 * y ^ 4 -
    25 * y ^ 5 - 7 * y ^ 6 - y ^ 7) / 16

private def factorTwoIntrinsicP4CorrelationDifferenceShift (y : ℝ) : ℝ :=
  (1 + y - 9 * y ^ 2 - 3 * y ^ 3 + 15 * y ^ 4 +
    3 * y ^ 5 - 7 * y ^ 6 - y ^ 7) / 16

private theorem factorTwoIntrinsicP4CorrelationSum_eq_shift (t : ℝ) :
    factorTwoIntrinsicP4CorrelationSum t =
      factorTwoIntrinsicP4CorrelationSumShift (t - 1) := by
  unfold factorTwoIntrinsicP4CorrelationSum
    factorTwoIntrinsicP4CorrelationSumShift
    factorTwoIntrinsicP4Correlation04 factorTwoIntrinsicP4Correlation24
  ring

private theorem factorTwoIntrinsicP4CorrelationDifference_eq_shift (t : ℝ) :
    factorTwoIntrinsicP4CorrelationDifference t =
      factorTwoIntrinsicP4CorrelationDifferenceShift (t - 1) := by
  unfold factorTwoIntrinsicP4CorrelationDifference
    factorTwoIntrinsicP4CorrelationDifferenceShift
    factorTwoIntrinsicP4Correlation04 factorTwoIntrinsicP4Correlation24
  ring

private theorem hasDerivAt_factorTwoIntrinsicP4CorrelationSumShift (y : ℝ) :
    HasDerivAt factorTwoIntrinsicP4CorrelationSumShift
      ((-11 - 18 * y + 111 * y ^ 2 + 60 * y ^ 3 - 125 * y ^ 4 -
        42 * y ^ 5 - 7 * y ^ 6) / 16) y := by
  unfold factorTwoIntrinsicP4CorrelationSumShift
  convert (((((((((hasDerivAt_const y (1 : ℝ)).sub
      ((hasDerivAt_id y).const_mul 11)).sub
      (((hasDerivAt_id y).pow 2).const_mul 9)).add
      (((hasDerivAt_id y).pow 3).const_mul 37)).add
      (((hasDerivAt_id y).pow 4).const_mul 15)).sub
      (((hasDerivAt_id y).pow 5).const_mul 25)).sub
      (((hasDerivAt_id y).pow 6).const_mul 7)).sub
      ((hasDerivAt_id y).pow 7)).div_const 16) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem hasDerivAt_factorTwoIntrinsicP4CorrelationDifferenceShift
    (y : ℝ) :
    HasDerivAt factorTwoIntrinsicP4CorrelationDifferenceShift
      ((1 - 18 * y - 9 * y ^ 2 + 60 * y ^ 3 + 15 * y ^ 4 -
        42 * y ^ 5 - 7 * y ^ 6) / 16) y := by
  unfold factorTwoIntrinsicP4CorrelationDifferenceShift
  convert (((((((((hasDerivAt_const y (1 : ℝ)).add
      (hasDerivAt_id y)).sub
      (((hasDerivAt_id y).pow 2).const_mul 9)).sub
      (((hasDerivAt_id y).pow 3).const_mul 3)).add
      (((hasDerivAt_id y).pow 4).const_mul 15)).add
      (((hasDerivAt_id y).pow 5).const_mul 3)).sub
      (((hasDerivAt_id y).pow 6).const_mul 7)).sub
      ((hasDerivAt_id y).pow 7)).div_const 16) using 1
  all_goals simp only [id_eq]
  all_goals ring

private theorem factorTwoIntrinsicP4CorrelationSumShift_strictAntiOn :
    StrictAntiOn factorTwoIntrinsicP4CorrelationSumShift
      (Icc (1699 / 10000 : ℝ) (17 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold factorTwoIntrinsicP4CorrelationSumShift; fun_prop)
  intro y hy
  rw [interior_Icc] at hy
  rw [(hasDerivAt_factorTwoIntrinsicP4CorrelationSumShift y).deriv]
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hy2 := pow_lt_pow_left₀ hy.2 hy0
    (by norm_num : (2 : ℕ) ≠ 0)
  have hy3 := pow_lt_pow_left₀ hy.2 hy0
    (by norm_num : (3 : ℕ) ≠ 0)
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have hy5 : 0 ≤ y ^ 5 := by positivity
  have hy6 : 0 ≤ y ^ 6 := by positivity
  norm_num at hy2 hy3 ⊢
  nlinarith

private theorem factorTwoIntrinsicP4CorrelationDifferenceShift_strictAntiOn :
    StrictAntiOn factorTwoIntrinsicP4CorrelationDifferenceShift
      (Icc (1699 / 10000 : ℝ) (17 / 100)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (by unfold factorTwoIntrinsicP4CorrelationDifferenceShift; fun_prop)
  intro y hy
  rw [interior_Icc] at hy
  rw [(hasDerivAt_factorTwoIntrinsicP4CorrelationDifferenceShift y).deriv]
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hy3 := pow_lt_pow_left₀ hy.2 hy0
    (by norm_num : (3 : ℕ) ≠ 0)
  have hy4 := pow_lt_pow_left₀ hy.2 hy0
    (by norm_num : (4 : ℕ) ≠ 0)
  have hy2 : 0 ≤ y ^ 2 := by positivity
  have hy5 : 0 ≤ y ^ 5 := by positivity
  have hy6 : 0 ≤ y ^ 6 := by positivity
  norm_num at hy3 hy4 ⊢
  nlinarith [hy.1]

/-- Sharp structural bounds for the two combined `P4` correlations at the
retained `p = 3` lag. -/
theorem factorTwoIntrinsicP4PrimeCorrelation_sum_difference_bounds :
    (-29337 / 500000 : ℝ) < factorTwoIntrinsicP4CorrelationSum
        (factorTwoPrimeShift / yoshidaEndpointA) ∧
      factorTwoIntrinsicP4CorrelationSum
          (factorTwoPrimeShift / yoshidaEndpointA) < (-29333 / 500000 : ℝ) ∧
      (56755 / 1000000 : ℝ) < factorTwoIntrinsicP4CorrelationDifference
          (factorTwoPrimeShift / yoshidaEndpointA) ∧
      factorTwoIntrinsicP4CorrelationDifference
          (factorTwoPrimeShift / yoshidaEndpointA) < (56757 / 1000000 : ℝ) := by
  let tau : ℝ := factorTwoPrimeShift / yoshidaEndpointA
  let y : ℝ := tau - 1
  let a : ℝ := 16992 / 100000
  let b : ℝ := 16993 / 100000
  have htau := factorTwoPrimeRatio_sharp_bounds
  have hya : a < y := by
    dsimp only [a, y, tau]
    linarith [htau.1]
  have hyb : y < b := by
    dsimp only [b, y, tau]
    linarith [htau.2]
  have ha : a ∈ Icc (1699 / 10000 : ℝ) (17 / 100) := by
    norm_num [a]
  have hb : b ∈ Icc (1699 / 10000 : ℝ) (17 / 100) := by
    norm_num [b]
  have hy : y ∈ Icc (1699 / 10000 : ℝ) (17 / 100) := by
    constructor <;> dsimp only [y, tau] <;> linarith [htau.1, htau.2]
  have hsumLower :=
    factorTwoIntrinsicP4CorrelationSumShift_strictAntiOn hy hb hyb
  have hsumUpper :=
    factorTwoIntrinsicP4CorrelationSumShift_strictAntiOn ha hy hya
  have hdiffLower :=
    factorTwoIntrinsicP4CorrelationDifferenceShift_strictAntiOn hy hb hyb
  have hdiffUpper :=
    factorTwoIntrinsicP4CorrelationDifferenceShift_strictAntiOn ha hy hya
  constructor
  · calc
      (-29337 / 500000 : ℝ) <
          factorTwoIntrinsicP4CorrelationSumShift b := by
        norm_num [factorTwoIntrinsicP4CorrelationSumShift, b]
      _ < factorTwoIntrinsicP4CorrelationSumShift y := hsumLower
      _ = factorTwoIntrinsicP4CorrelationSum tau := by
        rw [factorTwoIntrinsicP4CorrelationSum_eq_shift]
      _ = _ := by rfl
  constructor
  · calc
      factorTwoIntrinsicP4CorrelationSum
          (factorTwoPrimeShift / yoshidaEndpointA) =
          factorTwoIntrinsicP4CorrelationSumShift y := by
        rw [factorTwoIntrinsicP4CorrelationSum_eq_shift]
      _ < factorTwoIntrinsicP4CorrelationSumShift a := hsumUpper
      _ < (-29333 / 500000 : ℝ) := by
        norm_num [factorTwoIntrinsicP4CorrelationSumShift, a]
  constructor
  · calc
      (56755 / 1000000 : ℝ) <
          factorTwoIntrinsicP4CorrelationDifferenceShift b := by
        norm_num [factorTwoIntrinsicP4CorrelationDifferenceShift, b]
      _ < factorTwoIntrinsicP4CorrelationDifferenceShift y := hdiffLower
      _ = factorTwoIntrinsicP4CorrelationDifference tau := by
        rw [factorTwoIntrinsicP4CorrelationDifference_eq_shift]
      _ = _ := by rfl
  · calc
      factorTwoIntrinsicP4CorrelationDifference
          (factorTwoPrimeShift / yoshidaEndpointA) =
          factorTwoIntrinsicP4CorrelationDifferenceShift y := by
        rw [factorTwoIntrinsicP4CorrelationDifference_eq_shift]
      _ < factorTwoIntrinsicP4CorrelationDifferenceShift a := hdiffUpper
      _ < (56757 / 1000000 : ℝ) := by
        norm_num [factorTwoIntrinsicP4CorrelationDifferenceShift, a]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PrimeCorrelationStructural
