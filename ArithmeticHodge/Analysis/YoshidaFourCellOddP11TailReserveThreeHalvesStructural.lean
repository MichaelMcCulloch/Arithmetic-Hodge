import ArithmeticHodge.Analysis.YoshidaFourCellOddP11ThreeHalvesClosureStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenGapMarginsStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailReserveThreeHalvesStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredParity
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFourCellOddP11ThreeHalvesClosureStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# The cutoff-eleven reserve in the four-cell odd tail

The first five odd shifted-Legendre moments and parity remove every degree
below eleven.  The resulting exact harmonic gap is an infinite-dimensional
input for the direct corrected tail Schur form.  No scalar matched-factor
bound is asserted here: that stronger surrogate does not preserve the
finite--tail correlation of the production determinant.
-/

private theorem shiftedLegendreReal_one_centered (x : ℝ) :
    (shiftedLegendreReal 1).eval ((x + 1) / 2) = -centeredP1 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP1]
  ring

private theorem shiftedLegendreReal_three_centered (x : ℝ) :
    (shiftedLegendreReal 3).eval ((x + 1) / 2) = -centeredP3 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP3]
  ring

private theorem shiftedLegendreReal_five_centered (x : ℝ) :
    (shiftedLegendreReal 5).eval ((x + 1) / 2) =
      -factorTwoCenteredP5 x := by
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP5]
  ring

private theorem shiftedLegendreReal_seven_centered (x : ℝ) :
    (shiftedLegendreReal 7).eval ((x + 1) / 2) =
      -factorTwoCenteredP7 x := by
  have h := centeredPullback_factorTwoCenteredP7 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  linarith

private theorem shiftedLegendreReal_nine_centered (x : ℝ) :
    (shiftedLegendreReal 9).eval ((x + 1) / 2) =
      -factorTwoCenteredP9 x := by
  have h := centeredPullback_factorTwoCenteredP9 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  linarith

private theorem centeredPullback_shiftedLegendre_moment_eq
    (r q : ℝ → ℝ) (n : ℕ)
    (hmode : ∀ x : ℝ,
      (shiftedLegendreReal n).eval ((x + 1) / 2) = -q x) :
    (∫ t : unitInterval,
        centeredPullback r (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) =
      -(1 / 2 : ℝ) * (∫ x : ℝ in -1..1, r x * q x) := by
  rw [show (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) =
      ∫ t : ℝ in 0..1,
        centeredPullback r t * (shiftedLegendreReal n).eval t from
    integral_unitInterval_eq_intervalIntegral
      (fun t : ℝ ↦ centeredPullback r t *
        (shiftedLegendreReal n).eval t)]
  have htransport := integral_comp_two_mul_sub_one
    (fun x : ℝ ↦ r x * (shiftedLegendreReal n).eval ((x + 1) / 2))
  rw [show (fun t : ℝ ↦
      r (2 * t - 1) *
        (shiftedLegendreReal n).eval (((2 * t - 1) + 1) / 2)) =
      fun t ↦ centeredPullback r t *
        (shiftedLegendreReal n).eval t by
    funext t
    unfold centeredPullback
    congr 2
    ring] at htransport
  rw [show (fun x : ℝ ↦
      r x * (shiftedLegendreReal n).eval ((x + 1) / 2)) =
      fun x ↦ -(r x * q x) by
    funext x
    rw [hmode]
    ring,
    intervalIntegral.integral_neg] at htransport
  linarith

/-- The named `P₁/P₃/P₅/P₇/P₉` equations and odd parity are
exactly the full shifted-Legendre moment gap below degree eleven. -/
theorem centeredLegendreMomentsVanishBelow_eleven_of_P11Plus
    (r : ℝ → ℝ) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    centeredLegendreMomentsVanishBelow r 11 := by
  intro n hn
  by_cases heven : Even n
  · apply unitIntervalIntegral_eq_zero_of_symm_neg
    intro t
    rw [centeredPullback_symm_of_odd r hodd,
      shiftedLegendreReal_eval_symm, heven.neg_one_pow]
    ring
  · have hoddn : Odd n := Nat.not_even_iff_odd.mp heven
    rcases hoddn with ⟨m, hm⟩
    have hnCases : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9 := by
      omega
    rcases hnCases with rfl | rfl | rfl | rfl | rfl
    · rw [centeredPullback_shiftedLegendre_moment_eq r centeredP1 1
          shiftedLegendreReal_one_centered]
      unfold centeredOddP1Coefficient at h1
      nlinarith
    · rw [centeredPullback_shiftedLegendre_moment_eq r centeredP3 3
          shiftedLegendreReal_three_centered]
      unfold centeredOddP3Coefficient at h3
      nlinarith
    · rw [centeredPullback_shiftedLegendre_moment_eq r factorTwoCenteredP5 5
          shiftedLegendreReal_five_centered]
      unfold centeredOddP5Coefficient at h5
      nlinarith
    · rw [centeredPullback_shiftedLegendre_moment_eq r factorTwoCenteredP7 7
          shiftedLegendreReal_seven_centered]
      unfold centeredOddP7Coefficient at h7
      nlinarith
    · rw [centeredPullback_shiftedLegendre_moment_eq r factorTwoCenteredP9 9
          shiftedLegendreReal_nine_centered]
      unfold centeredOddP9Coefficient at h9
      nlinarith

/-- The genuine `P₁₁+` tail has the exact harmonic-eleven global raw
reserve.  This is an infinite spectral statement, not a mode truncation. -/
theorem harmonic_eleven_mul_intrinsicEnergy_le_raw_div_four_of_P11Plus
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    (harmonic 11 : ℝ) * factorTwoIntrinsicEnergy r ≤
      centeredRawLogEnergy r / 4 := by
  apply harmonic_mul_intrinsicEnergy_le_raw_div_four
    r hr.continuous
      (hr.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)) 11
  exact centeredLegendreMomentsVanishBelow_eleven_of_P11Plus
    r hodd h1 h3 h5 h7 h9

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailReserveThreeHalvesStructural
