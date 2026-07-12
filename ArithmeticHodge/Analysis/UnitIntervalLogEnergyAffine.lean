import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.UnitIntervalLogEnergyAffine

noncomputable section

/-!
# Exact affine transport from `[0,1]` to `[-1,1]`

These identities record the Jacobian constants needed to transport the
unit-interval logarithmic gap to the centered Yoshida interval.  They hold
for arbitrary Bochner integrands and do not use a discretization.
-/

/-- The affine map `t ↦ 2t-1` transports unit-interval integration to half
of centered-interval integration. -/
theorem integral_comp_two_mul_sub_one (g : ℝ → ℝ) :
    (∫ t : ℝ in 0..1, g (2 * t - 1)) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, g x := by
  have h := intervalIntegral.integral_comp_mul_add
    (a := (0 : ℝ)) (b := 1) g (by norm_num : (2 : ℝ) ≠ 0) (-1)
  convert h using 1
  all_goals norm_num [sub_eq_add_neg]

/-- Applying the affine change in both variables contributes the product
Jacobian `1/4`. -/
theorem integral_integral_comp_two_mul_sub_one
    (G : ℝ → ℝ → ℝ) :
    (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
      G (2 * s - 1) (2 * t - 1)) =
      (1 / 4 : ℝ) * ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1,
        G x y := by
  calc
    _ = ∫ s : ℝ in 0..1,
        (1 / 2 : ℝ) * ∫ y : ℝ in -1..1,
          G (2 * s - 1) y := by
      apply intervalIntegral.integral_congr
      intro s _hs
      exact integral_comp_two_mul_sub_one
        (fun y ↦ G (2 * s - 1) y)
    _ = (1 / 2 : ℝ) * ∫ s : ℝ in 0..1,
        ∫ y : ℝ in -1..1, G (2 * s - 1) y := by
      rw [intervalIntegral.integral_const_mul]
    _ = (1 / 2 : ℝ) * ((1 / 2 : ℝ) *
        ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, G x y) := by
      rw [integral_comp_two_mul_sub_one
        (fun x ↦ ∫ y : ℝ in -1..1, G x y)]
    _ = _ := by ring

/-- Pull a centered function back along `t ↦ 2t-1`. -/
def centeredPullback (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w (2 * t - 1)

/-- Nested raw logarithmic energy on the centered interval. -/
def centeredRawLogEnergy (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1,
    (w x - w y) ^ 2 / |x - y|

private theorem centeredPullback_raw_integrand
    (w : ℝ → ℝ) (s t : ℝ) :
    (centeredPullback w s - centeredPullback w t) ^ 2 / |s - t| =
      2 * ((w (2 * s - 1) - w (2 * t - 1)) ^ 2 /
        |(2 * s - 1) - (2 * t - 1)|) := by
  unfold centeredPullback
  rw [show (2 * s - 1) - (2 * t - 1) = 2 * (s - t) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  by_cases hst : |s - t| = 0
  · simp [hst]
  · field_simp [hst]

/-- The raw unit-interval energy of the affine pullback is one half of the
centered raw energy. -/
theorem rawLogEnergy_centeredPullback
    (w : ℝ → ℝ) :
    (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
      (centeredPullback w s - centeredPullback w t) ^ 2 / |s - t|) =
      (1 / 2 : ℝ) * centeredRawLogEnergy w := by
  let G : ℝ → ℝ → ℝ := fun x y ↦
    (w x - w y) ^ 2 / |x - y|
  calc
    _ = ∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        2 * G (2 * s - 1) (2 * t - 1) := by
      apply intervalIntegral.integral_congr
      intro s _hs
      apply intervalIntegral.integral_congr
      intro t _ht
      exact centeredPullback_raw_integrand w s t
    _ = 2 * (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
        G (2 * s - 1) (2 * t - 1)) := by
      rw [show (fun s : ℝ ↦ ∫ t : ℝ in 0..1,
          2 * G (2 * s - 1) (2 * t - 1)) =
          fun s ↦ 2 * ∫ t : ℝ in 0..1,
            G (2 * s - 1) (2 * t - 1) by
        funext s
        rw [intervalIntegral.integral_const_mul],
        intervalIntegral.integral_const_mul]
    _ = 2 * ((1 / 4 : ℝ) *
        ∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1, G x y) := by
      rw [integral_integral_comp_two_mul_sub_one G]
    _ = _ := by
      unfold centeredRawLogEnergy
      ring

/-- Squared mass acquires the single Jacobian `1/2`. -/
theorem normSq_centeredPullback (w : ℝ → ℝ) :
    (∫ t : ℝ in 0..1, centeredPullback w t ^ 2) =
      (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2 := by
  exact integral_comp_two_mul_sub_one (fun x ↦ w x ^ 2)

/-- The unit half-energy gap with constant `2` transports to the centered raw
gap with constant `4`. -/
theorem four_mul_centered_normSq_le_rawLogEnergy
    (w : ℝ → ℝ)
    (hunit :
      2 * (∫ t : ℝ in 0..1, centeredPullback w t ^ 2) ≤
        (1 / 2 : ℝ) *
          (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..1,
            (centeredPullback w s - centeredPullback w t) ^ 2 /
              |s - t|)) :
    4 * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w := by
  rw [normSq_centeredPullback, rawLogEnergy_centeredPullback] at hunit
  linarith

end

end ArithmeticHodge.Analysis.UnitIntervalLogEnergyAffine
