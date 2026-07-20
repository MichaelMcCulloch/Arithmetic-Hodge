import ArithmeticHodge.Analysis.YoshidaFourCellOddP51RawMassCancellationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailRawGapStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredParity
open ShiftedLegendreL2HigherGap
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51RawMassCancellationStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# The genuine `P53+` raw spectral gap

The indexed `P51` Galerkin tail equations are exactly the complete centered
Legendre moment gap below degree fifty-three.  Consequently the whole
infinite tail, rather than a finite truncation of it, receives the harmonic
fifty-three raw-log reserve.
-/

private theorem centeredPullback_centeredP1_eq_neg_shiftedLegendre_one
    (t : ℝ) :
    centeredPullback centeredP1 t = -(shiftedLegendreReal 1).eval t := by
  norm_num [centeredPullback, centeredP1, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose]
  ring

private theorem unitMoment_one_eq_neg_third_coefficient
    (r : ℝ → ℝ) :
    (∫ t : unitInterval,
        centeredPullback r (t : ℝ) * (shiftedLegendreReal 1).eval (t : ℝ)) =
      -(1 / 3 : ℝ) * centeredOddP1Coefficient r := by
  rw [show (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal 1).eval (t : ℝ)) =
      ∫ t : ℝ in 0..1,
        centeredPullback r t * (shiftedLegendreReal 1).eval t from
    integral_unitInterval_eq_intervalIntegral
      (fun t : ℝ ↦ centeredPullback r t *
        (shiftedLegendreReal 1).eval t)]
  calc
    (∫ t : ℝ in 0..1,
        centeredPullback r t * (shiftedLegendreReal 1).eval t) =
        ∫ t : ℝ in 0..1,
          -(r (2 * t - 1) * centeredP1 (2 * t - 1)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      have hmode := centeredPullback_centeredP1_eq_neg_shiftedLegendre_one t
      change r (2 * t - 1) * (shiftedLegendreReal 1).eval t =
        -(r (2 * t - 1) * centeredP1 (2 * t - 1))
      unfold centeredPullback at hmode
      rw [show (shiftedLegendreReal 1).eval t =
          -centeredP1 (2 * t - 1) by linarith]
      ring
    _ = -(1 / 2 : ℝ) *
        (∫ x : ℝ in -1..1, r x * centeredP1 x) := by
      rw [intervalIntegral.integral_neg,
        integral_comp_two_mul_sub_one
          (fun x : ℝ ↦ r x * centeredP1 x)]
      ring
    _ = -(1 / 3 : ℝ) * centeredOddP1Coefficient r := by
      rw [integral_mul_centeredP1_eq]
      ring

private theorem unitMoment_retained_eq_neg_positiveHalf
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r)
    (i : Fin 25) :
    (∫ t : unitInterval,
        centeredPullback r (t : ℝ) *
          (shiftedLegendreReal
            (fourCellOddFiniteRetainedDegree i)).eval (t : ℝ)) =
      -fourCellOddFiniteRetainedMoment 24 r i := by
  let b := fourCellOddFiniteRetainedBasis i
  have hb : Continuous b :=
    (contDiff_fourCellOddFiniteRetainedBasis i).continuous
  have hbodd : Function.Odd b := odd_fourCellOddFiniteRetainedBasis i
  have heven : Function.Even (fun x : ℝ ↦ r x * b x) := by
    intro x
    dsimp only
    rw [hodd, hbodd]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ r x * b x)
    ((hr.mul hb).intervalIntegrable _ _) heven
  rw [show (∫ t : unitInterval,
      centeredPullback r (t : ℝ) *
        (shiftedLegendreReal
          (fourCellOddFiniteRetainedDegree i)).eval (t : ℝ)) =
      ∫ t : ℝ in 0..1,
        centeredPullback r t *
          (shiftedLegendreReal
            (fourCellOddFiniteRetainedDegree i)).eval t from
    integral_unitInterval_eq_intervalIntegral
      (fun t : ℝ ↦ centeredPullback r t *
        (shiftedLegendreReal
          (fourCellOddFiniteRetainedDegree i)).eval t)]
  calc
    (∫ t : ℝ in 0..1,
        centeredPullback r t *
          (shiftedLegendreReal
            (fourCellOddFiniteRetainedDegree i)).eval t) =
        ∫ t : ℝ in 0..1, -(r (2 * t - 1) * b (2 * t - 1)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      have hmode := centeredPullback_fourCellOddFiniteRetainedBasis i t
      dsimp only [b]
      unfold centeredPullback at hmode ⊢
      rw [show (shiftedLegendreReal
          (fourCellOddFiniteRetainedDegree i)).eval t =
          -fourCellOddFiniteRetainedBasis i (2 * t - 1) by linarith]
      ring
    _ = -(1 / 2 : ℝ) * (∫ x : ℝ in -1..1, r x * b x) := by
      rw [intervalIntegral.integral_neg,
        integral_comp_two_mul_sub_one (fun x : ℝ ↦ r x * b x)]
      ring
    _ = -(∫ x : ℝ in 0..1, r x * b x) := by
      rw [hfold]
      ring
    _ = -(∫ x : ℝ in 0..1, b x * r x) := by
      congr 2
      funext x
      ring
    _ = -fourCellOddFiniteRetainedMoment 24 r i := by
      rfl

/-- The production `P53+` equations annihilate every centered Legendre
coordinate below degree fifty-three, including all even coordinates by
parity. -/
theorem centeredLegendreMomentsVanishBelow_fiftyThree_of_P53Plus
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    centeredLegendreMomentsVanishBelow r 53 := by
  rw [fourCellOddP53PlusMomentConditions_iff] at htail
  intro n hn
  by_cases heven : Even n
  · apply unitIntervalIntegral_eq_zero_of_symm_neg
    intro t
    rw [centeredPullback_symm_of_odd r hodd,
      shiftedLegendreReal_eval_symm, heven.neg_one_pow]
    ring
  · have hoddn : Odd n := Nat.not_even_iff_odd.mp heven
    by_cases hn1 : n = 1
    · subst n
      rw [unitMoment_one_eq_neg_third_coefficient r, htail.1]
      ring
    · have hn3 : 3 ≤ n := by
        rcases hoddn with ⟨k, hk⟩
        omega
      let i : Fin 25 := ⟨(n - 3) / 2, by omega⟩
      have hdegree : fourCellOddFiniteRetainedDegree i = n := by
        rcases hoddn with ⟨k, hk⟩
        unfold fourCellOddFiniteRetainedDegree
        dsimp only [i]
        omega
      rw [← hdegree, unitMoment_retained_eq_neg_positiveHalf
        r hr.continuous hodd i, htail.2 i]
      ring

/-- The entire genuine tail receives the harmonic-fifty-three raw reserve.
No upper cutoff or finite spectral sum occurs. -/
theorem harmonic_fiftyThree_mul_intrinsicEnergy_le_raw_div_four_of_P53Plus
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    (harmonic 53 : ℝ) * factorTwoIntrinsicEnergy r ≤
      centeredRawLogEnergy r / 4 := by
  apply harmonic_mul_intrinsicEnergy_le_raw_div_four
    r hr.continuous
      (hr.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)) 53
  exact centeredLegendreMomentsVanishBelow_fiftyThree_of_P53Plus
    r hr hodd htail

/-- A simple rational consequence of the harmonic gap: the raw logarithmic
reserve alone contains eight copies of positive-half mass on `P53+`. -/
theorem eight_mul_positiveHalfMass_le_raw_div_four_of_P53Plus
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    8 * (∫ x : ℝ in 0..1, r x ^ 2) ≤ centeredRawLogEnergy r / 4 := by
  have hraw :=
    harmonic_fiftyThree_mul_intrinsicEnergy_le_raw_div_four_of_P53Plus
      r hr hodd htail
  have hfour31 : (4 : ℝ) ≤ harmonic 31 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hfour53 : (4 : ℝ) ≤ harmonic 53 :=
    hfour31.trans (harmonic_cast_mono (by norm_num : 31 ≤ 53))
  have henergy : factorTwoIntrinsicEnergy r =
      2 * (∫ x : ℝ in 0..1, r x ^ 2) := by
    unfold factorTwoIntrinsicEnergy
    exact integral_sq_eq_two_mul_positiveHalf
      r hr.continuous (Or.inr hodd)
  have hmass : 0 ≤ factorTwoIntrinsicEnergy r :=
    factorTwoIntrinsicEnergy_nonneg r
  have hscaled := mul_le_mul_of_nonneg_right hfour53 hmass
  rw [henergy] at hscaled hraw
  convert hscaled.trans hraw using 1
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailRawGapStructural
