import ArithmeticHodge.Analysis.YoshidaEndpointEvenStructuralReduction

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenP2LogEnergy

open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenStructuralReduction

noncomputable section

/-- The centered logarithmic difference energy is exactly `12/5` on the
fixed degree-two Legendre mode. -/
theorem centeredRawLogEnergy_centeredEvenP2 :
    centeredRawLogEnergy centeredEvenP2 = 12 / 5 := by
  have hpoint (x y : ℝ) :
      (centeredEvenP2 x - centeredEvenP2 y) ^ 2 / |x - y| =
        (9 / 4 : ℝ) * |x - y| * (x + y) ^ 2 := by
    unfold centeredEvenP2
    by_cases hxy : x = y
    · subst y
      simp
    · have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have habs : |x - y| ≠ 0 := abs_ne_zero.mpr hsub
      rw [div_eq_iff habs]
      rw [show ((3 * x ^ 2 - 1) / 2 - (3 * y ^ 2 - 1) / 2) =
        (3 / 2 : ℝ) * (x - y) * (x + y) by ring]
      calc
        ((3 / 2 : ℝ) * (x - y) * (x + y)) ^ 2 =
            (9 / 4 : ℝ) * (x - y) ^ 2 * (x + y) ^ 2 := by ring
        _ = (9 / 4 : ℝ) * |x - y| * (x + y) ^ 2 * |x - y| := by
          rw [← sq_abs (x - y)]
          ring
  have hinner (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      (∫ y : ℝ in -1..1,
        (centeredEvenP2 x - centeredEvenP2 y) ^ 2 / |x - y|) =
          (9 / 4 : ℝ) * ((11 / 6 : ℝ) * x ^ 4 - x ^ 2 + 1 / 2) := by
    rw [show (∫ y : ℝ in -1..1,
        (centeredEvenP2 x - centeredEvenP2 y) ^ 2 / |x - y|) =
      ∫ y : ℝ in -1..1, (9 / 4 : ℝ) * |x - y| * (x + y) ^ 2 by
        apply intervalIntegral.integral_congr
        intro y _hy
        exact hpoint x y]
    rw [show (fun y : ℝ ↦ (9 / 4 : ℝ) * |x - y| * (x + y) ^ 2) =
        fun y ↦ (9 / 4 : ℝ) * (|x - y| * (x + y) ^ 2) by
      funext y
      ring,
      intervalIntegral.integral_const_mul]
    have hleft : IntervalIntegrable
        (fun y : ℝ ↦ |x - y| * (x + y) ^ 2) volume (-1) x := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hright : IntervalIntegrable
        (fun y : ℝ ↦ |x - y| * (x + y) ^ 2) volume x 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
    have hleftEq :
        (∫ y : ℝ in -1..x, |x - y| * (x + y) ^ 2) =
          ∫ y : ℝ in -1..x, (x - y) * (x + y) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hy' : y ≤ x := by
        have : y ∈ Icc (-1) x := by
          simpa only [uIcc_of_le hx.1] using hy
        exact this.2
      change |x - y| * (x + y) ^ 2 = (x - y) * (x + y) ^ 2
      rw [abs_of_nonneg (sub_nonneg.mpr hy')]
    have hrightEq :
        (∫ y : ℝ in x..1, |x - y| * (x + y) ^ 2) =
          ∫ y : ℝ in x..1, (y - x) * (x + y) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hy' : x ≤ y := by
        have : y ∈ Icc x 1 := by
          simpa only [uIcc_of_le hx.2] using hy
        exact this.1
      change |x - y| * (x + y) ^ 2 = (y - x) * (x + y) ^ 2
      rw [abs_of_nonpos (sub_nonpos.mpr hy')]
      ring
    rw [hleftEq, hrightEq]
    have hleftVal :
        (∫ y : ℝ in -1..x, (x - y) * (x + y) ^ 2) =
          (11 / 12 : ℝ) * x ^ 4 + x ^ 3 - x ^ 2 / 2 - x / 3 + 1 / 4 := by
      let F : ℝ → ℝ := fun y ↦
        -x * y ^ 3 / 3 + x ^ 2 * y ^ 2 / 2 + x ^ 3 * y - y ^ 4 / 4
      have hderiv (y : ℝ) : HasDerivAt F ((x - y) * (x + y) ^ 2) y := by
        dsimp only [F]
        convert (((((hasDerivAt_const y (-x)).mul
            ((hasDerivAt_id y).pow 3)).div_const 3).add
          (((hasDerivAt_const y (x ^ 2)).mul
            ((hasDerivAt_id y).pow 2)).div_const 2)).add
          ((hasDerivAt_const y (x ^ 3)).mul (hasDerivAt_id y))).sub
          (((hasDerivAt_id y).pow 4).div_const 4) using 1
        simp only [id_eq]
        ring
      have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _hy ↦ hderiv y)
        (Continuous.intervalIntegrable (by fun_prop) (-1) x)
      rw [hint]
      dsimp only [F]
      ring
    have hrightVal :
        (∫ y : ℝ in x..1, (y - x) * (x + y) ^ 2) =
          (11 / 12 : ℝ) * x ^ 4 - x ^ 3 - x ^ 2 / 2 + x / 3 + 1 / 4 := by
      let F : ℝ → ℝ := fun y ↦
        x * y ^ 3 / 3 - x ^ 2 * y ^ 2 / 2 - x ^ 3 * y + y ^ 4 / 4
      have hderiv (y : ℝ) : HasDerivAt F ((y - x) * (x + y) ^ 2) y := by
        dsimp only [F]
        convert (((((hasDerivAt_const y x).mul
            ((hasDerivAt_id y).pow 3)).div_const 3).sub
          (((hasDerivAt_const y (x ^ 2)).mul
            ((hasDerivAt_id y).pow 2)).div_const 2)).sub
          ((hasDerivAt_const y (x ^ 3)).mul (hasDerivAt_id y))).add
          (((hasDerivAt_id y).pow 4).div_const 4) using 1
        simp only [id_eq]
        ring
      have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _hy ↦ hderiv y)
        (Continuous.intervalIntegrable (by fun_prop) x 1)
      rw [hint]
      dsimp only [F]
      ring
    rw [hleftVal, hrightVal]
    ring
  unfold centeredRawLogEnergy
  calc
    (∫ x : ℝ in -1..1, ∫ y : ℝ in -1..1,
        (centeredEvenP2 x - centeredEvenP2 y) ^ 2 / |x - y|) =
        ∫ x : ℝ in -1..1, (9 / 4 : ℝ) *
          ((11 / 6 : ℝ) * x ^ 4 - x ^ 2 + 1 / 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply hinner x
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
    _ = 12 / 5 := by norm_num

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenP2LogEnergy
