import ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModeL2

set_option autoImplicit false

open MeasureTheory Polynomial
open scoped unitInterval

namespace ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModeThreeL2

noncomputable section

open ShiftedLegendreCenteredLowModes
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine

/-!
# The centered degree-three shifted-Legendre mode in `L²`

This file records the exact centered polynomial and normalization of the
single degree-three mode.  The identities are obtained symbolically from the
shifted-Legendre definition and exact polynomial integration.
-/

@[simp]
theorem centeredShiftedLegendreReal_three :
    centeredShiftedLegendreReal 3 =
      -(1 / 2 : ℝ) • ((5 : ℝ) • X ^ 3 - (3 : ℝ) • X) := by
  apply Polynomial.funext
  intro x
  simp [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Finset.sum_range_succ,
    Polynomial.smul_eq_C_mul]
  norm_num [Nat.choose]
  ring

@[simp]
theorem eval_centeredShiftedLegendreReal_three (x : ℝ) :
    (centeredShiftedLegendreReal 3).eval x =
      -(1 / 2 : ℝ) * (5 * x ^ 3 - 3 * x) := by
  rw [centeredShiftedLegendreReal_three]
  simp [Polynomial.smul_eq_C_mul]

private theorem eval_shiftedLegendreReal_three (t : ℝ) :
    (shiftedLegendreReal 3).eval t =
      1 - 12 * t + 30 * t ^ 2 - 20 * t ^ 3 := by
  calc
    (shiftedLegendreReal 3).eval t =
        (shiftedLegendreReal 3).eval (((2 * t - 1) + 1) / 2) := by
      congr 1
      ring
    _ = (centeredShiftedLegendreReal 3).eval (2 * t - 1) :=
      (eval_centeredShiftedLegendreReal 3 (2 * t - 1)).symm
    _ = -(1 / 2 : ℝ) *
        (5 * (2 * t - 1) ^ 3 - 3 * (2 * t - 1)) :=
      eval_centeredShiftedLegendreReal_three _
    _ = 1 - 12 * t + 30 * t ^ 2 - 20 * t ^ 3 := by ring

/-- The unnormalized degree-three shifted-Legendre mode has exact squared
`L²([0,1])` norm `1/7`. -/
theorem norm_sq_shiftedLegendreL2_three :
    ‖shiftedLegendreL2 3‖ ^ 2 = (1 / 7 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
      (polynomialToContinuous (shiftedLegendreReal 3)))
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ
      (polynomialToContinuous (shiftedLegendreReal 3))) = (1 / 7 : ℝ)
  have hinner := MeasureTheory.ContinuousMap.inner_toLp
    (𝕜 := ℝ) (volume : Measure unitInterval)
    (polynomialToContinuous (shiftedLegendreReal 3))
    (polynomialToContinuous (shiftedLegendreReal 3))
  calc
    _ = ∫ t : unitInterval,
        (polynomialToContinuous (shiftedLegendreReal 3)) t *
          starRingEnd ℝ
            ((polynomialToContinuous (shiftedLegendreReal 3)) t) := hinner
    _ = ∫ t : unitInterval,
        (shiftedLegendreReal 3).eval (t : ℝ) *
          (shiftedLegendreReal 3).eval (t : ℝ) := by
      rfl
    _ = ∫ t : ℝ in 0..1,
        (shiftedLegendreReal 3).eval t *
          (shiftedLegendreReal 3).eval t :=
      integral_unitInterval_eq_intervalIntegral
        (fun t : ℝ ↦
          (shiftedLegendreReal 3).eval t *
            (shiftedLegendreReal 3).eval t)
    _ = ∫ t : ℝ in 0..1,
        (1 - 12 * t + 30 * t ^ 2 - 20 * t ^ 3) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change (shiftedLegendreReal 3).eval t *
        (shiftedLegendreReal 3).eval t =
          (1 - 12 * t + 30 * t ^ 2 - 20 * t ^ 3) ^ 2
      rw [eval_shiftedLegendreReal_three]
      ring
    _ = ∫ t : ℝ in 0..1,
        (400 * t ^ 6 - 1200 * t ^ 5 + 1380 * t ^ 4 -
          760 * t ^ 3 + 204 * t ^ 2 - 24 * t + 1) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      ring
    _ = (1 / 7 : ℝ) := by
      let F : ℝ → ℝ := fun t ↦
        (400 / 7 : ℝ) * t ^ 7 - 200 * t ^ 6 + 276 * t ^ 5 -
          190 * t ^ 4 + 68 * t ^ 3 - 12 * t ^ 2 + t
      have hderiv (t : ℝ) : HasDerivAt F
          (400 * t ^ 6 - 1200 * t ^ 5 + 1380 * t ^ 4 -
            760 * t ^ 3 + 204 * t ^ 2 - 24 * t + 1) t := by
        dsimp only [F]
        have h7 := (hasDerivAt_const t (400 / 7 : ℝ)).mul
          ((hasDerivAt_id t).pow 7)
        have h6 := (hasDerivAt_const t (200 : ℝ)).mul
          ((hasDerivAt_id t).pow 6)
        have h5 := (hasDerivAt_const t (276 : ℝ)).mul
          ((hasDerivAt_id t).pow 5)
        have h4 := (hasDerivAt_const t (190 : ℝ)).mul
          ((hasDerivAt_id t).pow 4)
        have h3 := (hasDerivAt_const t (68 : ℝ)).mul
          ((hasDerivAt_id t).pow 3)
        have h2 := (hasDerivAt_const t (12 : ℝ)).mul
          ((hasDerivAt_id t).pow 2)
        refine ((((((h7.sub h6).add h5).sub h4).add h3).sub h2).add
          (hasDerivAt_id t)).congr_deriv ?_
        simp only [id_eq]
        ring
      have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ht ↦ hderiv t)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
      rw [hint]
      dsimp only [F]
      norm_num

/-- Squaring the inverse degree-three normalization contributes the exact
factor `7`. -/
theorem inv_norm_shiftedLegendreL2_three_sq :
    ‖shiftedLegendreL2 3‖⁻¹ ^ 2 = (7 : ℝ) := by
  rw [inv_pow, norm_sq_shiftedLegendreL2_three]
  norm_num

private theorem shiftedLegendreHilbertBasis_repr_three_eq_unitIntegral
    (f : unitInterval → ℝ)
    (hf : MemLp f 2 (volume : Measure unitInterval)) :
    shiftedLegendreHilbertBasis.repr (hf.toLp f) 3 =
      ‖shiftedLegendreL2 3‖⁻¹ *
        ∫ t : unitInterval,
          f t * (1 - 12 * (t : ℝ) + 30 * (t : ℝ) ^ 2 -
            20 * (t : ℝ) ^ 3) := by
  rw [shiftedLegendreHilbertBasis.repr_apply_apply,
    shiftedLegendreHilbertBasis_apply, normalizedShiftedLegendreL2,
    real_inner_smul_left, real_inner_comm, shiftedLegendreL2,
    ← integral_mul_polynomial_eq_inner f hf]
  apply congrArg (fun z : ℝ ↦ ‖shiftedLegendreL2 3‖⁻¹ * z)
  apply integral_congr_ae
  filter_upwards [] with t
  rw [eval_shiftedLegendreReal_three]

private theorem integral_centeredPullback_mul_degreeThree :
    ∀ w : ℝ → ℝ,
      (∫ t : unitInterval,
        centeredPullback w (t : ℝ) *
          (1 - 12 * (t : ℝ) + 30 * (t : ℝ) ^ 2 -
            20 * (t : ℝ) ^ 3)) =
        -(1 / 4 : ℝ) *
          ∫ x : ℝ in -1..1, (5 * x ^ 3 - 3 * x) * w x := by
  intro w
  calc
    _ = ∫ t : ℝ in 0..1,
        centeredPullback w t *
          (1 - 12 * t + 30 * t ^ 2 - 20 * t ^ 3) :=
      integral_unitInterval_eq_intervalIntegral _
    _ = ∫ t : ℝ in 0..1,
        (fun x : ℝ ↦
          -(1 / 2 : ℝ) * (5 * x ^ 3 - 3 * x) * w x) (2 * t - 1) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      simp only [centeredPullback]
      ring
    _ = (1 / 2 : ℝ) *
        ∫ x : ℝ in -1..1,
          -(1 / 2 : ℝ) * (5 * x ^ 3 - 3 * x) * w x :=
      integral_comp_two_mul_sub_one
        (fun x : ℝ ↦ -(1 / 2 : ℝ) * (5 * x ^ 3 - 3 * x) * w x)
    _ = -(1 / 4 : ℝ) *
        ∫ x : ℝ in -1..1, (5 * x ^ 3 - 3 * x) * w x := by
      conv_lhs => rw [← intervalIntegral.integral_const_mul]
      conv_rhs => rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _hx
      ring

/-- The normalized degree-three Hilbert coefficient of the affine pullback,
with the exact centered cubic pairing, sign, and Jacobian. -/
theorem shiftedLegendreHilbertBasis_repr_centeredPullback_three_eq
    (w : ℝ → ℝ)
    (hw : MemLp
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))
      2 (volume : Measure unitInterval)) :
    shiftedLegendreHilbertBasis.repr
        (hw.toLp (fun t : unitInterval ↦
          centeredPullback w (t : ℝ))) 3 =
      -(1 / 4 : ℝ) * ‖shiftedLegendreL2 3‖⁻¹ *
        ∫ x : ℝ in -1..1, (5 * x ^ 3 - 3 * x) * w x := by
  rw [shiftedLegendreHilbertBasis_repr_three_eq_unitIntegral,
    integral_centeredPullback_mul_degreeThree]
  ring

/-- Squaring the degree-three coefficient gives the exact centered cubic
pairing contribution `7/16`. -/
theorem shiftedLegendreHilbertBasis_repr_centeredPullback_three_sq
    (w : ℝ → ℝ)
    (hw : MemLp
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))
      2 (volume : Measure unitInterval)) :
    (shiftedLegendreHilbertBasis.repr
        (hw.toLp (fun t : unitInterval ↦
          centeredPullback w (t : ℝ))) 3) ^ 2 =
      (7 / 16 : ℝ) *
        (∫ x : ℝ in -1..1, (5 * x ^ 3 - 3 * x) * w x) ^ 2 := by
  rw [shiftedLegendreHilbertBasis_repr_centeredPullback_three_eq w hw]
  calc
    (-(1 / 4 : ℝ) * ‖shiftedLegendreL2 3‖⁻¹ *
        ∫ x : ℝ in -1..1, (5 * x ^ 3 - 3 * x) * w x) ^ 2 =
      (1 / 16 : ℝ) * ‖shiftedLegendreL2 3‖⁻¹ ^ 2 *
        (∫ x : ℝ in -1..1, (5 * x ^ 3 - 3 * x) * w x) ^ 2 := by
      ring
    _ = _ := by
      rw [inv_norm_shiftedLegendreL2_three_sq]
      ring

end

end ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModeThreeL2
