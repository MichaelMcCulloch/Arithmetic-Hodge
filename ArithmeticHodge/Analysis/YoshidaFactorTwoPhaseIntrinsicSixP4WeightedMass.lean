import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass

noncomputable section

open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseLegendreFourFiveStructural

/-!
# Exact weighted mass of the intrinsic `P4` mode

The endpoint-tail Schur argument uses the weight

`W = 41 / 60 + V`,

where `V` is the logarithmic endpoint potential.  This file evaluates the
single weighted mass needed by both endpoint reductions.  The calculation is
an exact logarithmic-moment identity; it contains no quadrature or enclosure.
-/

private theorem integral_eighth_mul_log_one_sub :
    (∫ x : ℝ in 0..1, x ^ 8 * Real.log (1 - x)) = -7129 / 22680 := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ 8 * Real.log y
  calc
    (∫ x : ℝ in 0..1, x ^ 8 * Real.log (1 - x)) =
        ∫ x : ℝ in 0..1, g (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      ring
    _ = ∫ x : ℝ in 0..1, g x := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left (f := g)
          (a := (0 : ℝ)) (b := 1) 1)
    _ = ∫ x : ℝ in 0..1,
        x ^ 8 * Real.log x - 8 * (x ^ 7 * Real.log x) +
          28 * (x ^ 6 * Real.log x) - 56 * (x ^ 5 * Real.log x) +
          70 * (x ^ 4 * Real.log x) - 56 * (x ^ 3 * Real.log x) +
          28 * (x ^ 2 * Real.log x) - 8 * (x ^ 1 * Real.log x) +
          x ^ 0 * Real.log x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      ring
    _ = (∫ x : ℝ in 0..1, x ^ 8 * Real.log x) -
          8 * (∫ x : ℝ in 0..1, x ^ 7 * Real.log x) +
          28 * (∫ x : ℝ in 0..1, x ^ 6 * Real.log x) -
          56 * (∫ x : ℝ in 0..1, x ^ 5 * Real.log x) +
          70 * (∫ x : ℝ in 0..1, x ^ 4 * Real.log x) -
          56 * (∫ x : ℝ in 0..1, x ^ 3 * Real.log x) +
          28 * (∫ x : ℝ in 0..1, x ^ 2 * Real.log x) -
          8 * (∫ x : ℝ in 0..1, x ^ 1 * Real.log x) +
          ∫ x : ℝ in 0..1, x ^ 0 * Real.log x := by
      have hJ (n : ℕ) : IntervalIntegrable
          (fun x : ℝ ↦ x ^ n * Real.log x) volume 0 1 :=
        intervalIntegral.intervalIntegrable_log'.continuousOn_mul
          (continuous_pow n).continuousOn
      rw [intervalIntegral.integral_add
          (((((((hJ 8).sub ((hJ 7).const_mul 8)).add
            ((hJ 6).const_mul 28)).sub ((hJ 5).const_mul 56)).add
            ((hJ 4).const_mul 70)).sub ((hJ 3).const_mul 56)).add
            ((hJ 2).const_mul 28) |>.sub ((hJ 1).const_mul 8)) (hJ 0),
        intervalIntegral.integral_sub
          ((((((hJ 8).sub ((hJ 7).const_mul 8)).add
            ((hJ 6).const_mul 28)).sub ((hJ 5).const_mul 56)).add
            ((hJ 4).const_mul 70)).sub ((hJ 3).const_mul 56) |>.add
            ((hJ 2).const_mul 28)) ((hJ 1).const_mul 8),
        intervalIntegral.integral_add
          (((((hJ 8).sub ((hJ 7).const_mul 8)).add
            ((hJ 6).const_mul 28)).sub ((hJ 5).const_mul 56)).add
            ((hJ 4).const_mul 70) |>.sub ((hJ 3).const_mul 56))
            ((hJ 2).const_mul 28),
        intervalIntegral.integral_sub
          ((((hJ 8).sub ((hJ 7).const_mul 8)).add
            ((hJ 6).const_mul 28)).sub ((hJ 5).const_mul 56) |>.add
            ((hJ 4).const_mul 70)) ((hJ 3).const_mul 56),
        intervalIntegral.integral_add
          (((hJ 8).sub ((hJ 7).const_mul 8)).add
            ((hJ 6).const_mul 28) |>.sub ((hJ 5).const_mul 56))
            ((hJ 4).const_mul 70),
        intervalIntegral.integral_sub
          ((hJ 8).sub ((hJ 7).const_mul 8) |>.add
            ((hJ 6).const_mul 28)) ((hJ 5).const_mul 56),
        intervalIntegral.integral_add
          ((hJ 8).sub ((hJ 7).const_mul 8)) ((hJ 6).const_mul 28),
        intervalIntegral.integral_sub (hJ 8) ((hJ 7).const_mul 8)]
      repeat rw [intervalIntegral.integral_const_mul]
    _ = -7129 / 22680 := by
      repeat rw [integral_pow_mul_log_zero_one]
      norm_num

private theorem integral_eighth_mul_log_one_add :
    (∫ x : ℝ in 0..1, x ^ 8 * Real.log (1 + x)) =
      (2 / 9 : ℝ) * Real.log 2 - 1879 / 22680 := by
  let F : ℝ → ℝ := fun x ↦
    x ^ 9 / 9 * Real.log (1 + x) - x ^ 9 / 81 + x ^ 8 / 72 -
      x ^ 7 / 63 + x ^ 6 / 54 - x ^ 5 / 45 + x ^ 4 / 36 -
      x ^ 3 / 27 + x ^ 2 / 18 - x / 9 + Real.log (1 + x) / 9
  have hderiv (x : ℝ) (hx : 1 + x ≠ 0) :
      HasDerivAt F (x ^ 8 * Real.log (1 + x)) x := by
    have hone : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
      simpa using (hasDerivAt_const x 1).add (hasDerivAt_id x)
    have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 + y))
        ((1 + x)⁻¹) x := by
      simpa only [Function.comp_apply, mul_one] using
        (Real.hasDerivAt_log hx).comp x hone
    dsimp only [F]
    convert (((hasDerivAt_id x).pow 9).div_const 9 |>.mul hlog)
      |>.sub (((hasDerivAt_id x).pow 9).div_const 81)
      |>.add (((hasDerivAt_id x).pow 8).div_const 72)
      |>.sub (((hasDerivAt_id x).pow 7).div_const 63)
      |>.add (((hasDerivAt_id x).pow 6).div_const 54)
      |>.sub (((hasDerivAt_id x).pow 5).div_const 45)
      |>.add (((hasDerivAt_id x).pow 4).div_const 36)
      |>.sub (((hasDerivAt_id x).pow 3).div_const 27)
      |>.add (((hasDerivAt_id x).pow 2).div_const 18)
      |>.sub ((hasDerivAt_id x).div_const 9)
      |>.add (hlog.div_const 9) using 1
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    field_simp [hx]
    ring
  have hcont : ContinuousOn (fun x : ℝ ↦ x ^ 8 * Real.log (1 + x))
      (uIcc (0 : ℝ) 1) := by
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hxne : 1 + x ≠ 0 := by linarith [hxu.1]
    have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
      exact ((Real.hasDerivAt_log hxne).comp x
        (by simpa using
          (hasDerivAt_const x 1).add (hasDerivAt_id x))).continuousAt
    exact ((continuousAt_id.pow 8).mul hlog).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hderiv x (by
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      linarith [hxu.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  ring

private theorem intervalIntegrable_eighth_mul_log_one_sub :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 8 * Real.log (1 - x))
      volume 0 1 := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ 8 * Real.log y
  have hg : IntervalIntegrable g volume 0 1 := by
    have hbase : IntervalIntegrable
        (fun y : ℝ ↦ (1 - y) ^ 8 * Real.log y) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1))
        |>.continuousOn_mul
          ((continuous_const.sub continuous_id).pow 8).continuousOn
    simpa only [g] using hbase
  have hreflect : IntervalIntegrable (fun x : ℝ ↦ g (1 - x))
      volume 0 1 := by
    simpa only [sub_self, sub_zero] using (hg.comp_sub_left 1).symm
  apply hreflect.congr
  intro x _hx
  dsimp only [g]
  ring

private theorem intervalIntegrable_eighth_mul_log_one_add :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 8 * Real.log (1 + x))
      volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hxu : x ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  have hxne : 1 + x ≠ 0 := by linarith [hxu.1]
  have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
    exact ((Real.hasDerivAt_log hxne).comp x
      (by simpa using
        (hasDerivAt_const x 1).add (hasDerivAt_id x))).continuousAt
  exact ((continuousAt_id.pow 8).mul hlog).continuousWithinAt

/-- Exact eighth moment of the logarithmic endpoint potential. -/
theorem integral_endpointPotential_mul_pow_eight :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ 8) =
      1126 / 2835 - (2 / 9 : ℝ) * Real.log 2 := by
  let q : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x ^ 8
  have hqEven : Function.Even q := by
    intro x
    dsimp only [q, yoshidaEndpointPotential]
    congr 1
    · congr 3
      ring
    · ring
  let r : ℝ → ℝ := fun x ↦ -(1 / 2 : ℝ) *
    (x ^ 8 * Real.log (1 - x) + x ^ 8 * Real.log (1 + x))
  have hpoint : ∀ᵐ x : ℝ ∂volume, q x = r x := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-1 : ℝ)] with x hx1 hxneg1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro h
      apply hxneg1
      linarith
    dsimp only [q, r, yoshidaEndpointPotential]
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    ring
  have hrRight : IntervalIntegrable r volume 0 1 := by
    have hsum := intervalIntegrable_eighth_mul_log_one_sub.add
      intervalIntegrable_eighth_mul_log_one_add
    have hscaled := hsum.const_mul (-(1 / 2 : ℝ))
    simpa only [r] using hscaled
  have hqRight : IntervalIntegrable q volume 0 1 := by
    have hrev : r =ᵐ[volume] q := by
      filter_upwards [hpoint] with x hx
      exact hx.symm
    apply hrRight.congr_ae
    exact hrev.filter_mono (ae_mono Measure.restrict_le_self)
  have hqLeft : IntervalIntegrable q volume (-1) 0 := by
    have hneg : IntervalIntegrable (fun x : ℝ ↦ q (-x)) volume (-1) 0 := by
      simpa only [zero_sub, sub_zero] using (hqRight.comp_sub_left 0).symm
    apply hneg.congr
    intro x _hx
    exact hqEven x
  have hfold : (∫ x : ℝ in -1..1, q x) =
      2 * ∫ x : ℝ in 0..1, q x := by
    have hreflect : (∫ x : ℝ in 0..1, q (-x)) =
        ∫ x : ℝ in -1..0, q x := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg
          (f := q) (a := (0 : ℝ)) (b := 1))
    calc
      (∫ x : ℝ in -1..1, q x) =
          (∫ x : ℝ in -1..0, q x) + ∫ x : ℝ in 0..1, q x :=
        (intervalIntegral.integral_add_adjacent_intervals hqLeft hqRight).symm
      _ = (∫ x : ℝ in 0..1, q x) + ∫ x : ℝ in 0..1, q x := by
        congr 1
        rw [← hreflect]
        apply intervalIntegral.integral_congr
        intro x _hx
        exact hqEven x
      _ = _ := by ring
  rw [show (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * x ^ 8) =
      ∫ x : ℝ in -1..1, q x by rfl, hfold]
  have hsplit : (∫ x : ℝ in 0..1, q x) =
      -(1 / 2 : ℝ) *
        ((∫ x : ℝ in 0..1, x ^ 8 * Real.log (1 - x)) +
          ∫ x : ℝ in 0..1, x ^ 8 * Real.log (1 + x)) := by
    calc
      (∫ x : ℝ in 0..1, q x) =
          ∫ x : ℝ in 0..1,
            -(1 / 2 : ℝ) *
              (x ^ 8 * Real.log (1 - x) +
                x ^ 8 * Real.log (1 + x)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hpoint] with x hx _hxI
        simpa only [r] using hx
      _ = -(1 / 2 : ℝ) *
          ∫ x : ℝ in 0..1,
            (x ^ 8 * Real.log (1 - x) +
              x ^ 8 * Real.log (1 + x)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [intervalIntegral.integral_add
          intervalIntegrable_eighth_mul_log_one_sub
          intervalIntegrable_eighth_mul_log_one_add]
  rw [hsplit, integral_eighth_mul_log_one_sub,
    integral_eighth_mul_log_one_add]
  ring

private theorem intervalIntegrable_endpointPotential_mul_pow_zero :
    IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
  simpa only [one_pow, mul_one] using
    intervalIntegrable_endpointPotential_mul_sq
      (fun _ : ℝ ↦ 1) continuous_const

private theorem intervalIntegrable_endpointPotential_mul_pow_two :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
  intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id

private theorem intervalIntegrable_endpointPotential_mul_pow_four :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
  have h := intervalIntegrable_endpointPotential_mul_sq
    (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)
  apply h.congr
  intro x _hx
  ring

private theorem intervalIntegrable_endpointPotential_mul_pow_six :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 6) volume (-1) 1 := by
  have h := intervalIntegrable_endpointPotential_mul_sq
    (fun x : ℝ ↦ x ^ 3) (continuous_id.pow 3)
  apply h.congr
  intro x _hx
  ring

private theorem intervalIntegrable_endpointPotential_mul_pow_eight :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 8) volume (-1) 1 := by
  have h := intervalIntegrable_endpointPotential_mul_sq
    (fun x : ℝ ↦ x ^ 4) (continuous_id.pow 4)
  apply h.congr
  intro x _hx
  ring

/-- Exact endpoint-potential mass of `P4`. -/
theorem integral_endpointPotential_mul_factorTwoCenteredP4_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * factorTwoCenteredP4 x ^ 2) =
        1739 / 5670 - (2 / 9 : ℝ) * Real.log 2 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * factorTwoCenteredP4 x ^ 2) =
      fun x ↦ (1225 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 8) -
        (2100 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) +
        (1110 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
        (180 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) +
        (9 / 64 : ℝ) * yoshidaEndpointPotential x by
    funext x
    unfold factorTwoCenteredP4
    ring]
  rw [intervalIntegral.integral_add
      (((intervalIntegrable_endpointPotential_mul_pow_eight.const_mul
          (1225 / 64 : ℝ)).sub
        (intervalIntegrable_endpointPotential_mul_pow_six.const_mul
          (2100 / 64 : ℝ))).add
        (intervalIntegrable_endpointPotential_mul_pow_four.const_mul
          (1110 / 64 : ℝ)) |>.sub
        (intervalIntegrable_endpointPotential_mul_pow_two.const_mul
          (180 / 64 : ℝ)))
      (intervalIntegrable_endpointPotential_mul_pow_zero.const_mul
        (9 / 64 : ℝ)),
    intervalIntegral.integral_sub
      (((intervalIntegrable_endpointPotential_mul_pow_eight.const_mul
        (1225 / 64 : ℝ)).sub
        (intervalIntegrable_endpointPotential_mul_pow_six.const_mul
          (2100 / 64 : ℝ))).add
        (intervalIntegrable_endpointPotential_mul_pow_four.const_mul
          (1110 / 64 : ℝ)))
      (intervalIntegrable_endpointPotential_mul_pow_two.const_mul
        (180 / 64 : ℝ)),
    intervalIntegral.integral_add
      ((intervalIntegrable_endpointPotential_mul_pow_eight.const_mul
        (1225 / 64 : ℝ)).sub
        (intervalIntegrable_endpointPotential_mul_pow_six.const_mul
          (2100 / 64 : ℝ)))
      (intervalIntegrable_endpointPotential_mul_pow_four.const_mul
        (1110 / 64 : ℝ)),
    intervalIntegral.integral_sub
      (intervalIntegrable_endpointPotential_mul_pow_eight.const_mul
        (1225 / 64 : ℝ))
      (intervalIntegrable_endpointPotential_mul_pow_six.const_mul
        (2100 / 64 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_eight,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq,
    integral_endpointPotential_one]
  ring

/-- The retained weighted `P4` mass is an elementary rational-logarithmic
constant. -/
theorem integral_tailWeight_mul_factorTwoCenteredP4_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2) =
        260 / 567 - (2 / 9 : ℝ) * Real.log 2 := by
  have hP4sq : IntervalIntegrable (fun x : ℝ ↦ factorTwoCenteredP4 x ^ 2)
      volume (-1) 1 :=
    (continuous_factorTwoCenteredP4.pow 2).intervalIntegrable (-1) 1
  have hVP4sq : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * factorTwoCenteredP4 x ^ 2)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq factorTwoCenteredP4
      continuous_factorTwoCenteredP4
  rw [show (fun x : ℝ ↦
      yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2) =
      fun x ↦ (41 / 60 : ℝ) * factorTwoCenteredP4 x ^ 2 +
        yoshidaEndpointPotential x * factorTwoCenteredP4 x ^ 2 by
    funext x
    unfold yoshidaEndpointEvenTailWeight
    ring,
    intervalIntegral.integral_add (hP4sq.const_mul (41 / 60 : ℝ)) hVP4sq,
    intervalIntegral.integral_const_mul,
    integral_factorTwoCenteredP4_sq,
    integral_endpointPotential_mul_factorTwoCenteredP4_sq]
  ring

theorem integral_tailWeight_mul_factorTwoCenteredP4_sq_pos :
    0 < ∫ x : ℝ in -1..1,
      yoshidaEndpointEvenTailWeight x * factorTwoCenteredP4 x ^ 2 := by
  rw [integral_tailWeight_mul_factorTwoCenteredP4_sq]
  nlinarith [Real.log_two_lt_d9]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
