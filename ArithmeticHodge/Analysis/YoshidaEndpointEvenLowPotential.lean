import ArithmeticHodge.Analysis.YoshidaEndpointEvenStructuralReduction
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialExactLowMode
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPotential

open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable

noncomputable section

/-- Exact endpoint-potential mass of the constant centered mode. -/
theorem integral_endpointPotential_one :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) =
      2 - 2 * Real.log 2 := by
  let q : ℝ → ℝ := yoshidaEndpointPotential
  let r : ℝ → ℝ := fun x ↦ -(1 / 2 : ℝ) *
    (Real.log (1 - x) + Real.log (1 + x))
  have hpoint : ∀ᵐ x : ℝ ∂volume, q x = r x := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ),
      MeasureTheory.Measure.ae_ne volume (-1 : ℝ)] with x hx1 hxneg1
    have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    have hadd : 1 + x ≠ 0 := by
      intro hzero
      apply hxneg1
      linarith
    dsimp only [q, r, yoshidaEndpointPotential]
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
      Real.log_mul hsub hadd]
    ring
  have hlog : IntervalIntegrable Real.log volume 0 2 :=
    intervalIntegral.intervalIntegrable_log'
  have hminus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 - x)) volume (-1) 1 := by
    convert (hlog.comp_sub_left 1).symm using 1 <;> norm_num
  have hplus : IntervalIntegrable
      (fun x : ℝ ↦ Real.log (1 + x)) volume (-1) 1 := by
    convert hlog.comp_add_left 1 using 1 <;> norm_num
  have hminusVal :
      (∫ x : ℝ in -1..1, Real.log (1 - x)) =
        2 * Real.log 2 - 2 := by
    rw [intervalIntegral.integral_comp_sub_left,
      integral_log]
    norm_num
  have hplusVal :
      (∫ x : ℝ in -1..1, Real.log (1 + x)) =
        2 * Real.log 2 - 2 := by
    rw [intervalIntegral.integral_comp_add_left,
      integral_log]
    norm_num
  calc
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) =
        ∫ x : ℝ in -1..1, r x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hpoint] with x hx _hxI
      simpa only [q] using hx
    _ = -(1 / 2 : ℝ) *
        ((∫ x : ℝ in -1..1, Real.log (1 - x)) +
          ∫ x : ℝ in -1..1, Real.log (1 + x)) := by
      dsimp only [r]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hminus hplus]
    _ = 2 - 2 * Real.log 2 := by
      rw [hminusVal, hplusVal]
      ring

/-- Exact potential cross between the centered constant and `P₂` modes. -/
theorem integral_endpointPotential_mul_centeredEvenP2 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredEvenP2 x) = 1 / 3 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredEvenP2 x) =
      fun x ↦ (3 / 2 : ℝ) *
          (yoshidaEndpointPotential x * x ^ 2) -
        (1 / 2 : ℝ) * yoshidaEndpointPotential x by
    funext x
    unfold centeredEvenP2
    ring]
  have hV : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa only [one_pow, mul_one] using
      intervalIntegrable_endpointPotential_mul_sq
        (fun _ : ℝ ↦ 1) continuous_const
  have hVx2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  rw [intervalIntegral.integral_sub (hVx2.const_mul (3 / 2 : ℝ))
      (hV.const_mul (1 / 2 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_endpointPotential_mul_sq,
    integral_endpointPotential_one]
  ring

/-- The singular `log (1-x)` degree-four moment on `[0,1]`. -/
theorem integral_fourth_mul_log_one_sub :
    (∫ x : ℝ in 0..1, x ^ 4 * Real.log (1 - x)) = -137 / 300 := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ 4 * Real.log y
  calc
    (∫ x : ℝ in 0..1, x ^ 4 * Real.log (1 - x)) =
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
        (((x ^ 4 * Real.log x - 4 * (x ^ 3 * Real.log x)) +
          6 * (x ^ 2 * Real.log x)) - 4 * (x ^ 1 * Real.log x)) +
          x ^ 0 * Real.log x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      ring
    _ = ((((∫ x : ℝ in 0..1, x ^ 4 * Real.log x) -
          4 * (∫ x : ℝ in 0..1, x ^ 3 * Real.log x)) +
        6 * (∫ x : ℝ in 0..1, x ^ 2 * Real.log x)) -
        4 * (∫ x : ℝ in 0..1, x ^ 1 * Real.log x)) +
        ∫ x : ℝ in 0..1, x ^ 0 * Real.log x := by
      have hJ (n : ℕ) : IntervalIntegrable
          (fun x : ℝ ↦ x ^ n * Real.log x) volume 0 1 :=
        intervalIntegral.intervalIntegrable_log'.continuousOn_mul
          (continuous_pow n).continuousOn
      rw [intervalIntegral.integral_add
          ((((hJ 4).sub ((hJ 3).const_mul 4)).add
            ((hJ 2).const_mul 6)).sub ((hJ 1).const_mul 4)) (hJ 0),
        intervalIntegral.integral_sub
          (((hJ 4).sub ((hJ 3).const_mul 4)).add
            ((hJ 2).const_mul 6)) ((hJ 1).const_mul 4),
        intervalIntegral.integral_add
          ((hJ 4).sub ((hJ 3).const_mul 4)) ((hJ 2).const_mul 6),
        intervalIntegral.integral_sub (hJ 4) ((hJ 3).const_mul 4),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ = -137 / 300 := by
      rw [integral_pow_mul_log_zero_one,
        integral_pow_mul_log_zero_one,
        integral_pow_mul_log_zero_one,
        integral_pow_mul_log_zero_one,
        integral_pow_mul_log_zero_one]
      norm_num

/-- The smooth `log (1+x)` degree-four moment on `[0,1]`. -/
theorem integral_fourth_mul_log_one_add :
    (∫ x : ℝ in 0..1, x ^ 4 * Real.log (1 + x)) =
      (2 / 5 : ℝ) * Real.log 2 - 47 / 300 := by
  let F : ℝ → ℝ := fun x ↦
    x ^ 5 / 5 * Real.log (1 + x) - x ^ 5 / 25 + x ^ 4 / 20 -
      x ^ 3 / 15 + x ^ 2 / 10 - x / 5 + Real.log (1 + x) / 5
  have hderiv (x : ℝ) (hx : 1 + x ≠ 0) :
      HasDerivAt F (x ^ 4 * Real.log (1 + x)) x := by
    have hone : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
      simpa using (hasDerivAt_const x 1).add (hasDerivAt_id x)
    have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 + y))
        ((1 + x)⁻¹) x := by
      simpa only [Function.comp_apply, mul_one] using
        (Real.hasDerivAt_log hx).comp x hone
    dsimp only [F]
    convert (((hasDerivAt_id x).pow 5).div_const 5 |>.mul hlog)
      |>.sub (((hasDerivAt_id x).pow 5).div_const 25)
      |>.add (((hasDerivAt_id x).pow 4).div_const 20)
      |>.sub (((hasDerivAt_id x).pow 3).div_const 15)
      |>.add (((hasDerivAt_id x).pow 2).div_const 10)
      |>.sub ((hasDerivAt_id x).div_const 5)
      |>.add (hlog.div_const 5) using 1
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    field_simp [hx]
    ring
  have hcont : ContinuousOn (fun x : ℝ ↦ x ^ 4 * Real.log (1 + x))
      (uIcc (0 : ℝ) 1) := by
    intro x hx
    have hxu : x ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    have hxne : 1 + x ≠ 0 := by linarith [hxu.1]
    have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
      exact ((Real.hasDerivAt_log hxne).comp x
        (by
          simpa using
            (hasDerivAt_const x 1).add (hasDerivAt_id x))).continuousAt
    exact ((continuousAt_id.pow 4).mul hlog).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hderiv x (by
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      linarith [hxu.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  ring

theorem intervalIntegrable_fourth_mul_log_one_sub :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 4 * Real.log (1 - x))
      volume 0 1 := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ 4 * Real.log y
  have hg : IntervalIntegrable g volume 0 1 := by
    have hbase : IntervalIntegrable
        (fun y : ℝ ↦ (1 - y) ^ 4 * Real.log y) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1))
        |>.continuousOn_mul
          ((continuous_const.sub continuous_id).pow 4).continuousOn
    simpa only [g] using hbase
  have hreflect : IntervalIntegrable (fun x : ℝ ↦ g (1 - x))
      volume 0 1 := by
    simpa only [sub_self, sub_zero] using (hg.comp_sub_left 1).symm
  apply hreflect.congr
  intro x _hx
  dsimp only [g]
  ring

theorem intervalIntegrable_fourth_mul_log_one_add :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 4 * Real.log (1 + x))
      volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hxu : x ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  have hxne : 1 + x ≠ 0 := by linarith [hxu.1]
  have hlog : ContinuousAt (fun y : ℝ ↦ Real.log (1 + y)) x := by
    exact ((Real.hasDerivAt_log hxne).comp x
      (by
        simpa using
          (hasDerivAt_const x 1).add (hasDerivAt_id x))).continuousAt
  exact ((continuousAt_id.pow 4).mul hlog).continuousWithinAt

/-- Exact fourth moment of the endpoint potential on the centered interval. -/
theorem integral_endpointPotential_mul_pow_four :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ 4) =
      46 / 75 - (2 / 5 : ℝ) * Real.log 2 := by
  let q : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x ^ 4
  have hqEven : Function.Even q := by
    intro x
    dsimp only [q, yoshidaEndpointPotential]
    congr 1
    · congr 3
      ring
    · ring
  let r : ℝ → ℝ := fun x ↦ -(1 / 2 : ℝ) *
    (x ^ 4 * Real.log (1 - x) + x ^ 4 * Real.log (1 + x))
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
    have hsum := intervalIntegrable_fourth_mul_log_one_sub.add
      intervalIntegrable_fourth_mul_log_one_add
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
      yoshidaEndpointPotential x * x ^ 4) =
      ∫ x : ℝ in -1..1, q x by rfl, hfold]
  have hsplit : (∫ x : ℝ in 0..1, q x) =
      -(1 / 2 : ℝ) *
        ((∫ x : ℝ in 0..1, x ^ 4 * Real.log (1 - x)) +
          ∫ x : ℝ in 0..1, x ^ 4 * Real.log (1 + x)) := by
    calc
      (∫ x : ℝ in 0..1, q x) =
          ∫ x : ℝ in 0..1,
            -(1 / 2 : ℝ) *
              (x ^ 4 * Real.log (1 - x) +
                x ^ 4 * Real.log (1 + x)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hpoint] with x hx _hxI
        simpa only [r] using hx
      _ = -(1 / 2 : ℝ) *
          ∫ x : ℝ in 0..1,
            (x ^ 4 * Real.log (1 - x) +
              x ^ 4 * Real.log (1 + x)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [intervalIntegral.integral_add
          intervalIntegrable_fourth_mul_log_one_sub
          intervalIntegrable_fourth_mul_log_one_add]
  rw [hsplit, integral_fourth_mul_log_one_sub,
    integral_fourth_mul_log_one_add]
  ring

/-- Exact endpoint-potential diagonal of the centered `P₂` mode. -/
theorem integral_endpointPotential_mul_centeredEvenP2_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredEvenP2 x ^ 2) =
        41 / 75 - (2 / 5 : ℝ) * Real.log 2 := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredEvenP2 x ^ 2) =
      fun x ↦ (9 / 4 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
        (3 / 2 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) +
        (1 / 4 : ℝ) * yoshidaEndpointPotential x by
    funext x
    unfold centeredEvenP2
    ring]
  have hV : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa only [one_pow, mul_one] using
      intervalIntegrable_endpointPotential_mul_sq
        (fun _ : ℝ ↦ 1) continuous_const
  have hVx2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq (fun x : ℝ ↦ x) continuous_id
  have hVx4 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ 4) volume (-1) 1 := by
    have h := intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)
    apply h.congr
    intro x _hx
    ring
  rw [intervalIntegral.integral_add
      ((hVx4.const_mul (9 / 4 : ℝ)).sub
        (hVx2.const_mul (3 / 2 : ℝ)))
      (hV.const_mul (1 / 4 : ℝ)),
    intervalIntegral.integral_sub
      (hVx4.const_mul (9 / 4 : ℝ))
      (hVx2.const_mul (3 / 2 : ℝ)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq,
    integral_endpointPotential_one]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPotential
