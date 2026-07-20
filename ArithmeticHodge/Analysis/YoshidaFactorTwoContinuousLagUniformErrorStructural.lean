import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
import ArithmeticHodge.Analysis.YoshidaFactorTwoContinuousLagRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFourCellParityHalfFoldStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoContinuousLagUniformErrorStructural

noncomputable section

open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# Uniform error for continuous-lag representers

A uniform error in the lag kernel costs only the positive-half `L²` mass
of an odd profile.  The proof uses the two ordered integration intervals as a
partition of `[-1,1]`; it does not expand the profile or its Legendre modes.
-/

/-- A uniformly bounded lag weight gives a pointwise `L¹` bound for its
symmetric continuous-lag representer. -/
theorem abs_factorTwoContinuousLagK_le_of_uniform
    (d q : ℝ → ℝ) (eps : ℝ)
    (hq : Continuous q) (heps : 0 ≤ eps)
    (hd : ∀ t ∈ Icc (0 : ℝ) 2, |d t| ≤ eps)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |factorTwoContinuousLagK d q x| ≤
      eps * ∫ y : ℝ in -1..1, |q y| := by
  have hqabs : IntervalIntegrable (fun y : ℝ ↦ |q y|) volume (-1) 1 :=
    hq.abs.intervalIntegrable _ _
  have hqabsRight :
      IntervalIntegrable (fun y : ℝ ↦ |q y|) volume x 1 :=
    hq.abs.intervalIntegrable _ _
  have hqabsLeft :
      IntervalIntegrable (fun y : ℝ ↦ |q y|) volume (-1) x :=
    hq.abs.intervalIntegrable _ _
  have hright :
      |∫ y : ℝ in x..1, d (y - x) * q y| ≤
        eps * ∫ y : ℝ in x..1, |q y| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun y : ℝ ↦ d (y - x) * q y)
      (g := fun y : ℝ ↦ eps * |q y|) hx.2 ?_
      (hqabsRight.const_mul eps)
    · rw [intervalIntegral.integral_const_mul] at h
      simpa only [Real.norm_eq_abs] using h
    · filter_upwards [] with y hy
      have hlag : y - x ∈ Icc (0 : ℝ) 2 := by
        constructor
        · linarith [hy.1]
        · linarith [hx.1, hy.2]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hd (y - x) hlag) le_rfl
        (abs_nonneg (q y)) heps
  have hleft :
      |∫ y : ℝ in -1..x, d (x - y) * q y| ≤
        eps * ∫ y : ℝ in -1..x, |q y| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun y : ℝ ↦ d (x - y) * q y)
      (g := fun y : ℝ ↦ eps * |q y|) hx.1 ?_
      (hqabsLeft.const_mul eps)
    · rw [intervalIntegral.integral_const_mul] at h
      simpa only [Real.norm_eq_abs] using h
    · filter_upwards [] with y hy
      have hlag : x - y ∈ Icc (0 : ℝ) 2 := by
        constructor
        · linarith [hy.2]
        · linarith [hy.1, hx.2]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hd (x - y) hlag) le_rfl
        (abs_nonneg (q y)) heps
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hqabsLeft hqabsRight
  unfold factorTwoContinuousLagK
    factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  calc
    |(∫ y : ℝ in x..1, d (y - x) * q y) +
        ∫ y : ℝ in -1..x, d (x - y) * q y| ≤
        |∫ y : ℝ in x..1, d (y - x) * q y| +
          |∫ y : ℝ in -1..x, d (x - y) * q y| := abs_add_le _ _
    _ ≤ eps * (∫ y : ℝ in x..1, |q y|) +
          eps * (∫ y : ℝ in -1..x, |q y|) :=
      add_le_add hright hleft
    _ = eps * ∫ y : ℝ in -1..1, |q y| := by
      rw [show (∫ y : ℝ in -1..1, |q y|) =
          (∫ y : ℝ in -1..x, |q y|) +
            ∫ y : ℝ in x..1, |q y| from hsplit.symm]
      ring

/-- Cauchy--Schwarz on the centered interval, in the exact `L¹`/`L²`
form used by the lag-kernel error estimate. -/
theorem sq_integral_abs_neg_one_one_le_two_mul_integral_sq
    (q : ℝ → ℝ) (hq : Continuous q) :
    (∫ x : ℝ in -1..1, |q x|) ^ 2 ≤
      2 * ∫ x : ℝ in -1..1, q x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  let f : ℝ → ℝ := fun _ ↦ 1
  let g : ℝ → ℝ := fun x ↦ |q x|
  have hf : Continuous f := continuous_const
  have hg : Continuous g := hq.abs
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hgMeas : AEStronglyMeasurable g μ :=
    hg.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  have h' :
      (∫ x : ℝ in -1..1, |q x|) ^ 2 ≤
        (∫ _x : ℝ in -1..1, (1 : ℝ)) *
          ∫ x : ℝ in -1..1, q x ^ 2 := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μ, f, g, one_mul, one_pow, div_one, sq_abs] using h
  rw [show (∫ _x : ℝ in -1..1, (1 : ℝ)) = 2 by norm_num] at h'
  exact h'

/-- The positive-half `L²` norm of a uniformly small lag representer is at
most `4 * eps²` times the positive-half mass of an odd profile. -/
theorem integral_zero_one_factorTwoContinuousLagK_sq_le_of_uniform_of_odd
    (d q : ℝ → ℝ) (eps : ℝ)
    (hq : Continuous q) (hodd : Function.Odd q) (heps : 0 ≤ eps)
    (hd : ∀ t ∈ Icc (0 : ℝ) 2, |d t| ≤ eps) :
    (∫ x : ℝ in 0..1, factorTwoContinuousLagK d q x ^ 2) ≤
      4 * eps ^ 2 * ∫ x : ℝ in 0..1, q x ^ 2 := by
  let L : ℝ := ∫ y : ℝ in -1..1, |q y|
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ abs_nonneg _)
  have hpoint : ∀ x ∈ Icc (0 : ℝ) 1,
      factorTwoContinuousLagK d q x ^ 2 ≤ eps ^ 2 * L ^ 2 := by
    intro x hx
    have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have habs := abs_factorTwoContinuousLagK_le_of_uniform
      d q eps hq heps hd hx'
    change |factorTwoContinuousLagK d q x| ≤ eps * L at habs
    calc
      factorTwoContinuousLagK d q x ^ 2 =
          |factorTwoContinuousLagK d q x| ^ 2 := by rw [sq_abs]
      _ ≤ (eps * L) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg heps hL0)).2 habs
      _ = eps ^ 2 * L ^ 2 := by ring
  have houterNorm :
      ‖∫ x : ℝ in 0..1, factorTwoContinuousLagK d q x ^ 2‖ ≤
        eps ^ 2 * L ^ 2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (f := fun x : ℝ ↦ factorTwoContinuousLagK d q x ^ 2)
      (C := eps ^ 2 * L ^ 2) ?_
    · simpa only [sub_zero, abs_one, mul_one] using h
    · intro x hx
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x ⟨hx.1.le, hx.2⟩
  have houter :
      (∫ x : ℝ in 0..1, factorTwoContinuousLagK d q x ^ 2) ≤
        eps ^ 2 * L ^ 2 := by
    calc
      (∫ x : ℝ in 0..1, factorTwoContinuousLagK d q x ^ 2) ≤
          ‖∫ x : ℝ in 0..1, factorTwoContinuousLagK d q x ^ 2‖ :=
        Real.le_norm_self _
      _ ≤ eps ^ 2 * L ^ 2 := houterNorm
  have hqSqEven : Function.Even (fun x : ℝ ↦ q x ^ 2) := by
    intro x
    change q (-x) ^ 2 = q x ^ 2
    rw [hodd x]
    ring
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ q x ^ 2) ((hq.pow 2).intervalIntegrable _ _) hqSqEven
  have hcauchy := sq_integral_abs_neg_one_one_le_two_mul_integral_sq q hq
  change L ^ 2 ≤ 2 * ∫ x : ℝ in -1..1, q x ^ 2 at hcauchy
  rw [hfold] at hcauchy
  calc
    (∫ x : ℝ in 0..1, factorTwoContinuousLagK d q x ^ 2) ≤
        eps ^ 2 * L ^ 2 := houter
    _ ≤ eps ^ 2 *
        (4 * ∫ x : ℝ in 0..1, q x ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith [hcauchy]) (sq_nonneg eps)
    _ = 4 * eps ^ 2 * ∫ x : ℝ in 0..1, q x ^ 2 := by ring

/-- Continuous lag convolution is linear in the lag weight.  This bridge
turns the preceding estimate for the error kernel into an estimate for the
difference of two representers. -/
theorem factorTwoContinuousLagK_sub_kernel
    (k k₀ q : ℝ → ℝ) (hk : Continuous k) (hk₀ : Continuous k₀)
    (hq : Continuous q) (x : ℝ) :
    factorTwoContinuousLagK (fun t ↦ k t - k₀ t) q x =
      factorTwoContinuousLagK k q x - factorTwoContinuousLagK k₀ q x := by
  have hkRight : IntervalIntegrable
      (fun y : ℝ ↦ k (y - x) * q y) volume x 1 := by
    exact ((hk.comp (continuous_id.sub continuous_const)).mul hq).intervalIntegrable _ _
  have hk₀Right : IntervalIntegrable
      (fun y : ℝ ↦ k₀ (y - x) * q y) volume x 1 := by
    exact ((hk₀.comp (continuous_id.sub continuous_const)).mul hq).intervalIntegrable _ _
  have hkLeft : IntervalIntegrable
      (fun y : ℝ ↦ k (x - y) * q y) volume (-1) x := by
    exact ((hk.comp (continuous_const.sub continuous_id)).mul hq).intervalIntegrable _ _
  have hk₀Left : IntervalIntegrable
      (fun y : ℝ ↦ k₀ (x - y) * q y) volume (-1) x := by
    exact ((hk₀.comp (continuous_const.sub continuous_id)).mul hq).intervalIntegrable _ _
  unfold factorTwoContinuousLagK
    factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  rw [show (fun y : ℝ ↦ (k (y - x) - k₀ (y - x)) * q y) =
      fun y ↦ k (y - x) * q y - k₀ (y - x) * q y by
    funext y
    ring,
    intervalIntegral.integral_sub hkRight hk₀Right,
    show (fun y : ℝ ↦ (k (x - y) - k₀ (x - y)) * q y) =
      fun y ↦ k (x - y) * q y - k₀ (x - y) * q y by
      funext y
      ring,
    intervalIntegral.integral_sub hkLeft hk₀Left]
  ring

/-- Uniformly close continuous lag kernels have representers whose
positive-half squared distance is at most `4 * eps²` times the positive-half
mass of an odd profile. -/
theorem integral_zero_one_factorTwoContinuousLagK_sub_sq_le_of_uniform_of_odd
    (k k₀ q : ℝ → ℝ) (eps : ℝ)
    (hk : Continuous k) (hk₀ : Continuous k₀)
    (hq : Continuous q) (hodd : Function.Odd q) (heps : 0 ≤ eps)
    (hd : ∀ t ∈ Icc (0 : ℝ) 2, |k t - k₀ t| ≤ eps) :
    (∫ x : ℝ in 0..1,
      (factorTwoContinuousLagK k q x -
        factorTwoContinuousLagK k₀ q x) ^ 2) ≤
      4 * eps ^ 2 * ∫ x : ℝ in 0..1, q x ^ 2 := by
  have h := integral_zero_one_factorTwoContinuousLagK_sq_le_of_uniform_of_odd
    (fun t ↦ k t - k₀ t) q eps hq hodd heps hd
  simpa only [factorTwoContinuousLagK_sub_kernel k k₀ q hk hk₀ hq] using h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoContinuousLagUniformErrorStructural
