import ArithmeticHodge.Analysis.YoshidaEndpointCleanQuadratic
import ArithmeticHodge.Analysis.YoshidaEndpointQuarticObstruction
import ArithmeticHodge.Analysis.YoshidaEndpointSingularCorrelationLipschitz
import ArithmeticHodge.Analysis.YoshidaFactorTwoStructuralConstantBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaPinnedThreeQuarterCoercivityStructural

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointQuarticObstruction
open YoshidaEndpointSingularCorrelationLipschitz
open YoshidaFactorTwoStructuralConstantBounds
open YoshidaRegularKernelSchur

noncomputable section

/-!
# A structural obstruction to half-mass coercivity on a pinned three-quarter interval

The proposed estimate

`(1 / 2) * ∫ w² ≤ yoshidaEndpointOddCleanQuadratic w`

does not follow merely from pinning a real profile to an interval of length
`3 / 2`.  The counterprofile below is the quadratic Dirichlet arch on
`[-1, 1/2]`, extended by zero.  Its logarithmic term is evaluated through the
continuous autocorrelation identity: no spectral cutoff, mesh, or exhaustive
mode computation enters the argument.
-/

/-- The left-pinned quadratic arch, extended continuously by zero. -/
def leftPinnedParabolicProfile (x : ℝ) : ℝ :=
  max 0 ((x + 1) * (1 / 2 - x))

private theorem leftPinnedParabolicProfile_eq_of_mem
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) (1 / 2)) :
    leftPinnedParabolicProfile x = (x + 1) * (1 / 2 - x) := by
  unfold leftPinnedParabolicProfile
  rw [max_eq_right]
  exact mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])

private theorem leftPinnedParabolicProfile_eq_zero_of_le
    {x : ℝ} (hx : x ≤ -1) : leftPinnedParabolicProfile x = 0 := by
  unfold leftPinnedParabolicProfile
  rw [max_eq_left]
  have hright : 0 ≤ 1 / 2 - x := by linarith
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hright

private theorem leftPinnedParabolicProfile_eq_zero_of_ge
    {x : ℝ} (hx : 1 / 2 ≤ x) : leftPinnedParabolicProfile x = 0 := by
  unfold leftPinnedParabolicProfile
  rw [max_eq_left]
  rcases le_total x (-1) with hxleft | hxright
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

theorem continuous_leftPinnedParabolicProfile :
    Continuous leftPinnedParabolicProfile := by
  unfold leftPinnedParabolicProfile
  fun_prop

theorem leftPinnedParabolicProfile_nonneg (x : ℝ) :
    0 ≤ leftPinnedParabolicProfile x := by
  unfold leftPinnedParabolicProfile
  exact le_max_left _ _

theorem support_leftPinnedParabolicProfile_subset :
    Function.support leftPinnedParabolicProfile ⊆ Icc (-1 : ℝ) (1 / 2) := by
  intro x hx
  constructor
  · by_contra hnot
    exact hx (leftPinnedParabolicProfile_eq_zero_of_le (le_of_not_ge hnot))
  · by_contra hnot
    exact hx (leftPinnedParabolicProfile_eq_zero_of_ge (le_of_not_ge hnot))

private theorem locallyLipschitzOn_leftPinnedParabolicProfile :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) leftPinnedParabolicProfile := by
  have hlip : LipschitzOnWith (3 : NNReal) leftPinnedParabolicProfile
      (Icc (-1 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq]
    unfold leftPinnedParabolicProfile
    calc
      |max 0 ((x + 1) * (1 / 2 - x)) -
          max 0 ((y + 1) * (1 / 2 - y))| ≤
          max |(0 : ℝ) - 0|
            |(x + 1) * (1 / 2 - x) - (y + 1) * (1 / 2 - y)| :=
        abs_max_sub_max_le_max _ _ _ _
      _ = |(x + 1) * (1 / 2 - x) - (y + 1) * (1 / 2 - y)| := by simp
      _ = |x - y| * |x + y + 1 / 2| := by
        rw [show (x + 1) * (1 / 2 - x) - (y + 1) * (1 / 2 - y) =
          -(x - y) * (x + y + 1 / 2) by ring, abs_mul, abs_neg]
      _ ≤ |x - y| * 3 := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
      _ = (3 : ℝ) * |x - y| := by ring
  intro x hx
  exact ⟨3, Icc (-1 : ℝ) 1, self_mem_nhdsWithin, hlip⟩

theorem integral_leftPinnedParabolicProfile :
    (∫ x : ℝ in -1..1, leftPinnedParabolicProfile x) = 9 / 16 := by
  have hleft : IntervalIntegrable leftPinnedParabolicProfile volume (-1) (1 / 2) :=
    continuous_leftPinnedParabolicProfile.intervalIntegrable _ _
  have hright : IntervalIntegrable leftPinnedParabolicProfile volume (1 / 2) 1 :=
    continuous_leftPinnedParabolicProfile.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hpoly :
      (∫ x : ℝ in -1..(1 / 2), leftPinnedParabolicProfile x) =
        ∫ x : ℝ in -1..(1 / 2), (x + 1) * (1 / 2 - x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply leftPinnedParabolicProfile_eq_of_mem
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1 / 2)] using hx
  have hzero : (∫ x : ℝ in (1 / 2)..1, leftPinnedParabolicProfile x) = 0 := by
    calc
      _ = ∫ _x : ℝ in (1 / 2)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        apply leftPinnedParabolicProfile_eq_zero_of_ge
        have hx' : x ∈ Icc (1 / 2 : ℝ) 1 := by
          simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using hx
        exact hx'.1
      _ = 0 := by simp
  rw [hpoly, hzero]
  let F : ℝ → ℝ := fun x ↦ x / 2 - x ^ 2 / 4 - x ^ 3 / 3
  have hderiv (x : ℝ) :
      HasDerivAt F ((x + 1) * (1 / 2 - x)) x := by
    dsimp only [F]
    convert (((hasDerivAt_id x).div_const 2).sub
      (((hasDerivAt_id x).pow 2).div_const 4)).sub
        (((hasDerivAt_id x).pow 3).div_const 3) using 1
    simp only [id_eq, Nat.cast_ofNat]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 / 2))]
  norm_num [F]

theorem integral_leftPinnedParabolicProfile_sq :
    (∫ x : ℝ in -1..1, leftPinnedParabolicProfile x ^ 2) = 81 / 320 := by
  have hcont : Continuous (fun x : ℝ ↦ leftPinnedParabolicProfile x ^ 2) :=
    continuous_leftPinnedParabolicProfile.pow 2
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦ leftPinnedParabolicProfile x ^ 2) volume (-1) (1 / 2) :=
    hcont.intervalIntegrable _ _
  have hright : IntervalIntegrable
      (fun x : ℝ ↦ leftPinnedParabolicProfile x ^ 2) volume (1 / 2) 1 :=
    hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hpoly :
      (∫ x : ℝ in -1..(1 / 2), leftPinnedParabolicProfile x ^ 2) =
        ∫ x : ℝ in -1..(1 / 2), ((x + 1) * (1 / 2 - x)) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    change leftPinnedParabolicProfile x ^ 2 = ((x + 1) * (1 / 2 - x)) ^ 2
    rw [leftPinnedParabolicProfile_eq_of_mem]
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1 / 2)] using hx
  have hzero :
      (∫ x : ℝ in (1 / 2)..1, leftPinnedParabolicProfile x ^ 2) = 0 := by
    calc
      _ = ∫ _x : ℝ in (1 / 2)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change leftPinnedParabolicProfile x ^ 2 = 0
        have hx' : x ∈ Icc (1 / 2 : ℝ) 1 := by
          simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using hx
        rw [leftPinnedParabolicProfile_eq_zero_of_ge hx'.1]
        norm_num
      _ = 0 := by simp
  rw [hpoly, hzero]
  let F : ℝ → ℝ := fun x ↦
    x ^ 5 / 5 + x ^ 4 / 4 - x ^ 3 / 4 - x ^ 2 / 4 + x / 4
  have hderiv (x : ℝ) :
      HasDerivAt F (((x + 1) * (1 / 2 - x)) ^ 2) x := by
    dsimp only [F]
    convert ((((((hasDerivAt_id x).pow 5).div_const 5).add
      (((hasDerivAt_id x).pow 4).div_const 4)).sub
        (((hasDerivAt_id x).pow 3).div_const 4)).sub
          (((hasDerivAt_id x).pow 2).div_const 4)).add
            ((hasDerivAt_id x).div_const 4) using 1
    simp only [id_eq, Nat.cast_ofNat]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 / 2))]
  norm_num [F]

/-- Exact autocorrelation of the pinned arch before its support separates. -/
theorem centeredEndpointCorrelation_leftPinnedParabolicProfile_of_mem
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (3 / 2)) :
    centeredEndpointCorrelation leftPinnedParabolicProfile t =
      81 / 320 - (9 / 16) * t ^ 2 + (3 / 8) * t ^ 3 - t ^ 5 / 30 := by
  unfold centeredEndpointCorrelation
  let g : ℝ → ℝ := fun x ↦
    leftPinnedParabolicProfile (t + x) * leftPinnedParabolicProfile x
  have hg : Continuous g := by
    dsimp only [g]
    exact (continuous_leftPinnedParabolicProfile.comp
      (continuous_const.add continuous_id)).mul
        continuous_leftPinnedParabolicProfile
  have hleft : IntervalIntegrable g volume (-1) (1 / 2 - t) :=
    hg.intervalIntegrable _ _
  have hright : IntervalIntegrable g volume (1 / 2 - t) (1 - t) :=
    hg.intervalIntegrable _ _
  rw [show (fun x : ℝ ↦
      leftPinnedParabolicProfile (t + x) * leftPinnedParabolicProfile x) = g by
    rfl]
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hpoly :
      (∫ x : ℝ in -1..(1 / 2 - t), g x) =
        ∫ x : ℝ in -1..(1 / 2 - t),
          ((t + x + 1) * (1 / 2 - (t + x))) *
            ((x + 1) * (1 / 2 - x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (-1 : ℝ) (1 / 2 - t) := by
      simpa only [uIcc_of_le (by linarith [ht.2] : (-1 : ℝ) ≤ 1 / 2 - t)] using hx
    have hxSupport : x ∈ Icc (-1 : ℝ) (1 / 2) :=
      ⟨hx'.1, by linarith [hx'.2, ht.1]⟩
    have htxSupport : t + x ∈ Icc (-1 : ℝ) (1 / 2) :=
      ⟨by linarith [hx'.1, ht.1], by linarith [hx'.2]⟩
    dsimp only [g]
    rw [leftPinnedParabolicProfile_eq_of_mem hxSupport,
      leftPinnedParabolicProfile_eq_of_mem htxSupport]
  have hzero : (∫ x : ℝ in (1 / 2 - t)..(1 - t), g x) = 0 := by
    calc
      _ = ∫ _x : ℝ in (1 / 2 - t)..(1 - t), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (1 / 2 - t : ℝ) (1 - t) := by
          simpa only [uIcc_of_le (by linarith : (1 / 2 - t : ℝ) ≤ 1 - t)] using hx
        dsimp only [g]
        rw [leftPinnedParabolicProfile_eq_zero_of_ge (by linarith [hx'.1])]
        simp
      _ = 0 := by simp
  rw [hpoly, hzero, add_zero]
  let F : ℝ → ℝ := fun x ↦
    ((9 / 4 : ℝ) * t - (3 / 2) * t ^ 2) * (x + 1) ^ 2 / 2 +
    ((9 / 4 : ℝ) - (9 / 2) * t + t ^ 2) * (x + 1) ^ 3 / 3 +
    ((-3 : ℝ) + 2 * t) * (x + 1) ^ 4 / 4 +
    (x + 1) ^ 5 / 5
  have hderiv (x : ℝ) : HasDerivAt F
      (((t + x + 1) * (1 / 2 - (t + x))) *
        ((x + 1) * (1 / 2 - x))) x := by
    have hu : HasDerivAt (fun y : ℝ ↦ y + 1) 1 x := by
      simpa only [add_zero] using (hasDerivAt_id x).add_const 1
    dsimp only [F]
    convert (((((hu.pow 2).const_mul
      ((9 / 4 : ℝ) * t - (3 / 2) * t ^ 2)).div_const 2).add
        (((hu.pow 3).const_mul
          ((9 / 4 : ℝ) - (9 / 2) * t + t ^ 2)).div_const 3)).add
            (((hu.pow 4).const_mul ((-3 : ℝ) + 2 * t)).div_const 4)).add
              ((hu.pow 5).div_const 5) using 1
    simp only [Nat.cast_ofNat]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 / 2 - t))]
  dsimp only [F]
  ring

/-- Once the shift reaches the support length `3 / 2`, the autocorrelation
vanishes identically. -/
theorem centeredEndpointCorrelation_leftPinnedParabolicProfile_eq_zero
    {t : ℝ} (ht : 3 / 2 ≤ t) (ht2 : t ≤ 2) :
    centeredEndpointCorrelation leftPinnedParabolicProfile t = 0 := by
  unfold centeredEndpointCorrelation
  calc
    _ = ∫ _x : ℝ in -1..1 - t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (-1 : ℝ) (1 - t) := by
        simpa only [uIcc_of_le (by linarith [ht2] : (-1 : ℝ) ≤ 1 - t)] using hx
      change leftPinnedParabolicProfile (t + x) * leftPinnedParabolicProfile x = 0
      rw [leftPinnedParabolicProfile_eq_zero_of_ge]
      · simp
      · linarith [hx'.1, ht]
    _ = 0 := by simp

private theorem correlationDefectIntegral_leftPinnedParabolicProfile :
    (∫ t : ℝ in 0..2,
      (centeredEndpointCorrelation leftPinnedParabolicProfile 0 -
        centeredEndpointCorrelation leftPinnedParabolicProfile t) / t) =
      837 / 3200 + (81 / 320) *
        (Real.log 2 - Real.log (3 / 2)) := by
  let D : ℝ → ℝ := fun t ↦
    (centeredEndpointCorrelation leftPinnedParabolicProfile 0 -
      centeredEndpointCorrelation leftPinnedParabolicProfile t) / t
  let P : ℝ → ℝ := fun t ↦
    (9 / 16 : ℝ) * t - (3 / 8) * t ^ 2 + t ^ 4 / 30
  let T : ℝ → ℝ := fun t ↦ (81 / 320 : ℝ) / t
  have hcorr0 : centeredEndpointCorrelation leftPinnedParabolicProfile 0 =
      81 / 320 := by
    rw [centeredEndpointCorrelation_zero,
      integral_leftPinnedParabolicProfile_sq]
  have hleftPoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (3 / 2)) :
      D t = P t := by
    dsimp only [D, P]
    rw [hcorr0,
      centeredEndpointCorrelation_leftPinnedParabolicProfile_of_mem ht]
    by_cases ht0 : t = 0
    · subst t
      norm_num
    · field_simp [ht0]
      ring
  have hrightPoint (t : ℝ) (ht : t ∈ Icc (3 / 2 : ℝ) 2) :
      D t = T t := by
    dsimp only [D, T]
    rw [hcorr0,
      centeredEndpointCorrelation_leftPinnedParabolicProfile_eq_zero ht.1 ht.2,
      sub_zero]
  have hPInt : IntervalIntegrable P volume 0 (3 / 2) := by
    apply Continuous.intervalIntegrable
    dsimp only [P]
    fun_prop
  have hTInt : IntervalIntegrable T volume (3 / 2) 2 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    dsimp only [T]
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div continuousAt_id (by
      have ht' : t ∈ Icc (3 / 2 : ℝ) 2 := by
        simpa only [uIcc_of_le (by norm_num : (3 / 2 : ℝ) ≤ 2)] using ht
      linarith [ht'.1])
  have hDleft : IntervalIntegrable D volume 0 (3 / 2) := by
    apply hPInt.congr
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) (3 / 2) := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 2)] using ht
    exact (hleftPoint t ⟨ht'.1.le, ht'.2⟩).symm
  have hDright : IntervalIntegrable D volume (3 / 2) 2 := by
    apply hTInt.congr
    intro t ht
    have ht' : t ∈ Ioc (3 / 2 : ℝ) 2 := by
      simpa only [uIoc_of_le (by norm_num : (3 / 2 : ℝ) ≤ 2)] using ht
    exact (hrightPoint t ⟨ht'.1.le, ht'.2⟩).symm
  change (∫ t : ℝ in 0..2, D t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hDleft hDright]
  have hleftValue : (∫ t : ℝ in 0..(3 / 2), D t) = 837 / 3200 := by
    calc
      _ = ∫ t : ℝ in 0..(3 / 2), P t := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply hleftPoint t
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 2)] using ht
      _ = 837 / 3200 := by
        let F : ℝ → ℝ := fun t ↦
          (9 / 32 : ℝ) * t ^ 2 - t ^ 3 / 8 + t ^ 5 / 150
        have hderiv (t : ℝ) : HasDerivAt F (P t) t := by
          dsimp only [F, P]
          convert ((((hasDerivAt_id t).pow 2).const_mul (9 / 32 : ℝ)).sub
            (((hasDerivAt_id t).pow 3).div_const 8)).add
              (((hasDerivAt_id t).pow 5).div_const 150) using 1
          simp only [Nat.cast_ofNat, id_eq]
          ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ht ↦ hderiv t)
          (Continuous.intervalIntegrable (by
            dsimp only [P]
            fun_prop) 0 (3 / 2))]
        norm_num [F]
  have hrightValue :
      (∫ t : ℝ in (3 / 2)..2, D t) =
        (81 / 320) * (Real.log 2 - Real.log (3 / 2)) := by
    calc
      _ = ∫ t : ℝ in (3 / 2)..2, T t := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply hrightPoint t
        simpa only [uIcc_of_le (by norm_num : (3 / 2 : ℝ) ≤ 2)] using ht
      _ = (81 / 320) * (∫ t : ℝ in (3 / 2)..2, t⁻¹) := by
        dsimp only [T]
        rw [show (fun t : ℝ ↦ (81 / 320 : ℝ) / t) =
            fun t ↦ (81 / 320 : ℝ) * t⁻¹ by
          funext t
          rw [div_eq_mul_inv],
          intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [integral_inv_of_pos (by norm_num) (by norm_num),
          Real.log_div (by norm_num) (by norm_num)]
  rw [hleftValue, hrightValue]

/-- Exact singular part of the clean endpoint quadratic on the pinned arch. -/
theorem logEnergy_div_four_add_potential_leftPinnedParabolicProfile :
    centeredRawLogEnergy leftPinnedParabolicProfile / 4 +
        (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * leftPinnedParabolicProfile x ^ 2) =
      837 / 3200 - (81 / 320) * Real.log (3 / 2) := by
  have hidentity :=
    integral_correlation_defect_div_eq_centered_energy_add_potential_of_locallyLipschitzOn
      leftPinnedParabolicProfile continuous_leftPinnedParabolicProfile
        locallyLipschitzOn_leftPinnedParabolicProfile
  rw [correlationDefectIntegral_leftPinnedParabolicProfile,
    integral_leftPinnedParabolicProfile_sq] at hidentity
  linarith

private theorem logEnergy_div_four_add_potential_lt_sixty_three_hundredths :
    centeredRawLogEnergy leftPinnedParabolicProfile / 4 +
        (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * leftPinnedParabolicProfile x ^ 2) <
      (63 / 100 : ℝ) *
        (∫ x : ℝ in -1..1, leftPinnedParabolicProfile x ^ 2) := by
  rw [logEnergy_div_four_add_potential_leftPinnedParabolicProfile,
    integral_leftPinnedParabolicProfile_sq]
  have hlog := strict_log_three_halves_fine_bounds.1
  norm_num at hlog ⊢
  linarith

private theorem log_two_lt_one_hundred_thirty_nine_div_two_hundred :
    Real.log 2 < (139 / 200 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem cosh_yoshidaEndpointA_half_lt_sixty_one_div_sixty :
    Real.cosh (yoshidaEndpointA / 2) < (61 / 60 : ℝ) := by
  let t : ℝ := yoshidaEndpointA / 2
  have ht0 : 0 ≤ t := (half_pos yoshidaEndpointA_pos).le
  have ht : t < (139 / 800 : ℝ) := by
    dsimp only [t]
    unfold yoshidaEndpointA
    linarith [log_two_lt_one_hundred_thirty_nine_div_two_hundred]
  have hprod : 0 < ((139 / 800 : ℝ) - t) *
      ((139 / 800 : ℝ) + t) := by
    apply mul_pos
    · linarith
    · positivity
  have hsq : t ^ 2 < (139 / 800 : ℝ) ^ 2 := by
    nlinarith
  let u : ℝ := t ^ 2 / 2
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    positivity
  have hu61 : u < (1 / 61 : ℝ) := by
    dsimp only [u]
    nlinarith
  have hu1 : u < 1 := lt_trans hu61 (by norm_num)
  have hexp : Real.exp u ≤ 1 / (1 - u) :=
    Real.exp_bound_div_one_sub_of_interval hu0 hu1
  have hfrac : 1 / (1 - u) < (61 / 60 : ℝ) := by
    rw [div_lt_iff₀ (sub_pos.mpr hu1)]
    nlinarith
  have hcosh : Real.cosh t ≤ Real.exp u := by
    dsimp only [u]
    exact Real.cosh_le_exp_half_sq t
  dsimp only [t] at hcosh ⊢
  exact hcosh.trans_lt (hexp.trans_lt hfrac)

private theorem cosh_yoshidaEndpoint_weight_lt_sixty_one_div_sixty
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    Real.cosh (yoshidaEndpointA * x / 2) < (61 / 60 : ℝ) := by
  apply lt_of_le_of_lt _ cosh_yoshidaEndpointA_half_lt_sixty_one_div_sixty
  apply Real.cosh_le_cosh.mpr
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  calc
    |yoshidaEndpointA * x / 2| = yoshidaEndpointA * |x| / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg yoshidaEndpointA_pos.le]
      norm_num
    _ ≤ yoshidaEndpointA * 1 / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hxabs yoshidaEndpointA_pos.le
      linarith
    _ = |yoshidaEndpointA / 2| := by
      rw [abs_div, abs_of_nonneg yoshidaEndpointA_pos.le]
      norm_num

private theorem hyperbolic_leftPinnedParabolicProfile_lt_ninety_one_hundredths :
    yoshidaEndpointHyperbolicQuadratic
        (fun x : ℝ ↦ (leftPinnedParabolicProfile x : ℂ)) <
      (91 / 100 : ℝ) *
        (∫ x : ℝ in -1..1, leftPinnedParabolicProfile x ^ 2) := by
  let f : ℝ → ℂ := fun x ↦ leftPinnedParabolicProfile x
  let C : ℂ := ∫ x : ℝ in -1..1,
    (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * f x
  let S : ℂ := ∫ x : ℝ in -1..1,
    (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * f x
  have hCnorm : ‖C‖ ≤ (61 / 60 : ℝ) * (9 / 16) := by
    calc
      ‖C‖ ≤ ∫ x : ℝ in -1..1,
          ‖(Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * f x‖ := by
        dsimp only [C]
        exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ = ∫ x : ℝ in -1..1,
          Real.cosh (yoshidaEndpointA * x / 2) *
            leftPinnedParabolicProfile x := by
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only [f]
        rw [norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (Real.cosh_pos _),
          abs_of_nonneg (leftPinnedParabolicProfile_nonneg x)]
      _ ≤ ∫ x : ℝ in -1..1,
          (61 / 60 : ℝ) * leftPinnedParabolicProfile x := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · apply Continuous.intervalIntegrable
          exact (by fun_prop : Continuous
            (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2))) |>.mul
              continuous_leftPinnedParabolicProfile
        · exact (continuous_leftPinnedParabolicProfile.const_mul (61 / 60 : ℝ))
            |>.intervalIntegrable _ _
        · intro x hx
          apply mul_le_mul_of_nonneg_right
            (cosh_yoshidaEndpoint_weight_lt_sixty_one_div_sixty hx).le
            (leftPinnedParabolicProfile_nonneg x)
      _ = (61 / 60 : ℝ) * (9 / 16) := by
        rw [intervalIntegral.integral_const_mul,
          integral_leftPinnedParabolicProfile]
  have hCsq : Complex.normSq C ≤ ((61 / 60 : ℝ) * (9 / 16)) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg C) (by positivity)).2 hCnorm
  have hdrop :
      yoshidaEndpointHyperbolicQuadratic f ≤
        2 * yoshidaEndpointA * Complex.normSq C := by
    unfold yoshidaEndpointHyperbolicQuadratic
    dsimp only [C, S]
    have hS0 : 0 ≤ Complex.normSq S := Complex.normSq_nonneg S
    nlinarith [yoshidaEndpointA_pos]
  have hA : 2 * yoshidaEndpointA ≤ (7 / 10 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_bounds.2]
  calc
    yoshidaEndpointHyperbolicQuadratic
        (fun x : ℝ ↦ (leftPinnedParabolicProfile x : ℂ)) =
        yoshidaEndpointHyperbolicQuadratic f := by rfl
    _ ≤ 2 * yoshidaEndpointA * Complex.normSq C := hdrop
    _ ≤ (7 / 10 : ℝ) * ((61 / 60 : ℝ) * (9 / 16)) ^ 2 := by
      calc
        _ ≤ (7 / 10 : ℝ) * Complex.normSq C := by
          exact mul_le_mul_of_nonneg_right hA (Complex.normSq_nonneg C)
        _ ≤ _ := mul_le_mul_of_nonneg_left hCsq (by norm_num)
    _ < (91 / 100 : ℝ) * (81 / 320) := by norm_num
    _ = (91 / 100 : ℝ) *
        (∫ x : ℝ in -1..1, leftPinnedParabolicProfile x ^ 2) := by
      rw [integral_leftPinnedParabolicProfile_sq]

private theorem regular_leftPinnedParabolicProfile_le_seven_fortieths :
    -yoshidaEndpointA *
        (yoshidaEndpointRegularQuadratic
          (fun x : ℝ ↦ (leftPinnedParabolicProfile x : ℂ))).re ≤
      (7 / 40 : ℝ) *
        (∫ x : ℝ in -1..1, leftPinnedParabolicProfile x ^ 2) := by
  let f : ℝ → ℂ := fun x ↦ leftPinnedParabolicProfile x
  let R : ℂ := yoshidaEndpointRegularQuadratic f
  have hf : Continuous f :=
    Complex.continuous_ofReal.comp continuous_leftPinnedParabolicProfile
  have hmassSet :
      (∫ x : ℝ in Icc (-1 : ℝ) 1, ‖f x‖ ^ 2) = 81 / 320 := by
    calc
      _ = ∫ x : ℝ in -1..1, leftPinnedParabolicProfile x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by norm_num),
          ← integral_Icc_eq_integral_Ioc]
        apply setIntegral_congr_fun measurableSet_Icc
        intro x _hx
        dsimp only [f]
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ = 81 / 320 := integral_leftPinnedParabolicProfile_sq
  have hRnorm : ‖R‖ ≤ (1 / 2 : ℝ) * (81 / 320) := by
    have h := norm_yoshidaEndpointRegularQuadratic_le f hf
    rw [hmassSet] at h
    exact h
  have hminusRe : -R.re ≤ ‖R‖ := by
    calc
      -R.re ≤ |R.re| := neg_le_abs R.re
      _ ≤ ‖R‖ := Complex.abs_re_le_norm R
  have hA : yoshidaEndpointA ≤ (7 / 20 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_bounds.2]
  calc
    -yoshidaEndpointA *
        (yoshidaEndpointRegularQuadratic
          (fun x : ℝ ↦ (leftPinnedParabolicProfile x : ℂ))).re =
        yoshidaEndpointA * (-R.re) := by
      dsimp only [R, f]
      ring
    _ ≤ yoshidaEndpointA * ‖R‖ :=
      mul_le_mul_of_nonneg_left hminusRe yoshidaEndpointA_pos.le
    _ ≤ (7 / 20 : ℝ) * ((1 / 2) * (81 / 320)) := by
      exact mul_le_mul hA hRnorm (norm_nonneg R) (by norm_num)
    _ = (7 / 40 : ℝ) *
        (∫ x : ℝ in -1..1, leftPinnedParabolicProfile x ^ 2) := by
      rw [integral_leftPinnedParabolicProfile_sq]
      norm_num

private theorem forty_nine_fortieths_lt_yoshidaEndpointScalarMassLoss :
    (49 / 40 : ℝ) < yoshidaEndpointScalarMassLoss := by
  have hgamma := Real.one_half_lt_eulerMascheroniConstant
  have hlog :=
    three_thousand_six_hundred_forty_seven_div_five_thousand_lt_log_pi_mul_log_two
  unfold yoshidaEndpointScalarMassLoss
  linarith

/-- The pinned arch strictly reverses the proposed half-mass clean
coercivity estimate.  All constants in the proof are structural rational
bounds; the only exact non-polynomial quantity is `log (3/2)` from the
support-separation tail. -/
theorem leftPinnedParabolicProfile_clean_lt_half_mass :
    yoshidaEndpointOddCleanQuadratic leftPinnedParabolicProfile <
      (1 / 2 : ℝ) *
        (∫ x : ℝ in -1..1, leftPinnedParabolicProfile x ^ 2) := by
  let M : ℝ := ∫ x : ℝ in -1..1, leftPinnedParabolicProfile x ^ 2
  have hM : M = 81 / 320 := integral_leftPinnedParabolicProfile_sq
  have hMpos : 0 < M := by rw [hM]; norm_num
  have hsing :=
    logEnergy_div_four_add_potential_lt_sixty_three_hundredths
  have hregular := regular_leftPinnedParabolicProfile_le_seven_fortieths
  have hhyper :=
    hyperbolic_leftPinnedParabolicProfile_lt_ninety_one_hundredths
  have hscalar := forty_nine_fortieths_lt_yoshidaEndpointScalarMassLoss
  have hscalarScaled :
      -yoshidaEndpointScalarMassLoss * M < -(49 / 40 : ℝ) * M := by
    nlinarith
  unfold yoshidaEndpointOddCleanQuadratic
  dsimp only
  change centeredRawLogEnergy leftPinnedParabolicProfile / 4 +
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * leftPinnedParabolicProfile x ^ 2) -
      yoshidaEndpointScalarMassLoss * M -
      yoshidaEndpointA *
        (yoshidaEndpointRegularQuadratic
          (fun x ↦ (leftPinnedParabolicProfile x : ℂ))).re +
      yoshidaEndpointHyperbolicQuadratic
        (fun x ↦ (leftPinnedParabolicProfile x : ℂ)) <
      (1 / 2 : ℝ) * M
  dsimp only [M] at hsing hregular hhyper ⊢
  nlinarith

/-- The natural universal formulation of the proposed pinned estimate on
the locally Lipschitz form domain.  Either reflected pinning orientation is
allowed. -/
def PinnedThreeQuarterHalfCoercivity : Prop :=
  ∀ w : ℝ → ℝ,
    Continuous w →
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) w →
    (Function.support w ⊆ Icc (-1 : ℝ) (1 / 2) ∨
      Function.support w ⊆ Icc (-1 / 2 : ℝ) 1) →
    (1 / 2 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      yoshidaEndpointOddCleanQuadratic w

theorem not_pinnedThreeQuarterHalfCoercivity :
    ¬ PinnedThreeQuarterHalfCoercivity := by
  intro h
  have hclaimed := h leftPinnedParabolicProfile
    continuous_leftPinnedParabolicProfile
    locallyLipschitzOn_leftPinnedParabolicProfile
    (Or.inl support_leftPinnedParabolicProfile_subset)
  exact (not_lt_of_ge hclaimed)
    leftPinnedParabolicProfile_clean_lt_half_mass

end

end ArithmeticHodge.Analysis.YoshidaPinnedThreeQuarterCoercivityStructural
