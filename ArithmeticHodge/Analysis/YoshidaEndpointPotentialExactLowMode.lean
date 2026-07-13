import ArithmeticHodge.Analysis.YoshidaEndpointPotentialBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialExactLowMode

open YoshidaEndpointPotentialBound

noncomputable section

/-!
# Exact endpoint potential on the centered degree-one mode

The quartic lower bound is too weak on the odd low mode.  This file evaluates
the full logarithmic endpoint potential there by structural improper
integration, with the potential retained exactly.
-/

/-- Every logarithmic moment against a natural power on `[0,1]` has its exact
elementary value. -/
theorem integral_pow_mul_log_zero_one (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n * Real.log x) =
      -(1 / (n + 1 : ℝ) ^ 2) := by
  let c : ℝ := n + 1
  let F : ℝ → ℝ := fun x ↦ x ^ (n + 1) *
    (Real.log x / c - 1 / c ^ 2)
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hderiv (x : ℝ) (hx : 0 < x) :
      HasDerivAt F (x ^ n * Real.log x) x := by
    have hpow := (hasDerivAt_id x).pow (n + 1)
    have hlog := (Real.hasDerivAt_log hx.ne').div_const c
    have hconst := hasDerivAt_const x (1 / c ^ 2)
    dsimp only [c] at hlog hconst
    dsimp only [F, c]
    convert hpow.mul (hlog.sub hconst) using 1
    simp only [id_eq, Pi.sub_apply, Pi.pow_apply, Nat.cast_add, Nat.cast_one]
    rw [Nat.add_sub_cancel]
    field_simp
    ring
  have hint : IntervalIntegrable (fun x : ℝ ↦ x ^ n * Real.log x)
      volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul
      (continuous_pow n).continuousOn
  have hzeroLog : Filter.Tendsto
      (fun x : ℝ ↦ x ^ (n + 1) * Real.log x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [Real.rpow_natCast, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero
        (r := ((n + 1 : ℕ) : ℝ)) (by positivity))
  have hzeroPow : Filter.Tendsto (fun x : ℝ ↦ x ^ (n + 1))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hcont : Continuous (fun x : ℝ ↦ x ^ (n + 1)) :=
      continuous_pow (n + 1)
    have hfull : Filter.Tendsto (fun x : ℝ ↦ x ^ (n + 1))
        (nhds 0) (nhds 0) := by
      have hc0 : ContinuousAt (fun x : ℝ ↦ x ^ (n + 1)) 0 :=
        hcont.continuousAt
      convert hc0.tendsto using 1
      norm_num
    exact hfull.mono_left inf_le_left
  have hzero : Filter.Tendsto F (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hmain :=
      (hzeroLog.const_mul (1 / c)).sub (hzeroPow.const_mul (1 / c ^ 2))
    convert hmain using 1
    · funext x
      dsimp only [F]
      ring
    · ring_nf
  have hone : Filter.Tendsto F (nhdsWithin 1 (Iio 1))
      (nhds (-(1 / c ^ 2))) := by
    have hcont : ContinuousAt F 1 := by
      dsimp only [F]
      exact (continuousAt_id.pow (n + 1)).mul
        (((Real.continuousAt_log (by norm_num)).div_const c).sub
          continuousAt_const)
    convert tendsto_nhdsWithin_of_tendsto_nhds hcont using 1
    dsimp only [F]
    simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (a := (0 : ℝ)) (b := 1) (f := F) (f' := fun x ↦ x ^ n * Real.log x)
      (by norm_num) (fun x hx ↦ hderiv x hx.1) hint hzero hone
  simpa using h

/-- The singular `log (1-x)` degree-two moment. -/
theorem integral_sq_mul_log_one_sub :
    (∫ x : ℝ in 0..1, x ^ 2 * Real.log (1 - x)) = -11 / 18 := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ 2 * Real.log y
  calc
    (∫ x : ℝ in 0..1, x ^ 2 * Real.log (1 - x)) =
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
        x ^ 2 * Real.log x - 2 * (x ^ 1 * Real.log x) +
          x ^ 0 * Real.log x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [g]
      ring
    _ = (∫ x : ℝ in 0..1, x ^ 2 * Real.log x) -
        2 * (∫ x : ℝ in 0..1, x ^ 1 * Real.log x) +
          ∫ x : ℝ in 0..1, x ^ 0 * Real.log x := by
      have hJ (n : ℕ) : IntervalIntegrable
          (fun x : ℝ ↦ x ^ n * Real.log x) volume 0 1 :=
        intervalIntegral.intervalIntegrable_log'.continuousOn_mul
          (continuous_pow n).continuousOn
      rw [intervalIntegral.integral_add
          ((hJ 2).sub ((hJ 1).const_mul 2)) (hJ 0),
        intervalIntegral.integral_sub (hJ 2) ((hJ 1).const_mul 2),
        intervalIntegral.integral_const_mul]
    _ = -11 / 18 := by
      rw [integral_pow_mul_log_zero_one,
        integral_pow_mul_log_zero_one,
        integral_pow_mul_log_zero_one]
      norm_num

/-- The smooth `log (1+x)` degree-two moment. -/
theorem integral_sq_mul_log_one_add :
    (∫ x : ℝ in 0..1, x ^ 2 * Real.log (1 + x)) =
      (2 / 3 : ℝ) * Real.log 2 - 5 / 18 := by
  let F : ℝ → ℝ := fun x ↦
    x ^ 3 / 3 * Real.log (1 + x) - x ^ 3 / 9 + x ^ 2 / 6 - x / 3 +
      Real.log (1 + x) / 3
  have hderiv (x : ℝ) (hx : 1 + x ≠ 0) :
      HasDerivAt F (x ^ 2 * Real.log (1 + x)) x := by
    have hone : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
      simpa using (hasDerivAt_const x 1).add (hasDerivAt_id x)
    have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 + y))
        ((1 + x)⁻¹) x := by
      simpa only [Function.comp_apply, mul_one] using
        (Real.hasDerivAt_log hx).comp x hone
    dsimp only [F]
    convert (((hasDerivAt_id x).pow 3).div_const 3 |>.mul hlog)
      |>.sub (((hasDerivAt_id x).pow 3).div_const 9)
      |>.add (((hasDerivAt_id x).pow 2).div_const 6)
      |>.sub ((hasDerivAt_id x).div_const 3)
      |>.add (hlog.div_const 3) using 1
    simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat]
    field_simp [hx]
    ring
  have hcont : ContinuousOn (fun x : ℝ ↦ x ^ 2 * Real.log (1 + x))
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
    exact ((continuousAt_id.pow 2).mul hlog).continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hderiv x (by
      have hxu : x ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      linarith [hxu.1])) hcont.intervalIntegrable
  rw [hint]
  dsimp only [F]
  norm_num
  ring

theorem intervalIntegrable_sq_mul_log_one_sub :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 2 * Real.log (1 - x)) volume 0 1 := by
  let g : ℝ → ℝ := fun y ↦ (1 - y) ^ 2 * Real.log y
  have hg : IntervalIntegrable g volume 0 1 := by
    have hbase : IntervalIntegrable
        (fun y : ℝ ↦ (1 - y) ^ 2 * Real.log y) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1))
        |>.continuousOn_mul
          ((continuous_const.sub continuous_id).pow 2).continuousOn
    simpa only [g] using hbase
  have hreflect : IntervalIntegrable (fun x : ℝ ↦ g (1 - x)) volume 0 1 := by
    simpa only [sub_self, sub_zero] using (hg.comp_sub_left 1).symm
  apply hreflect.congr
  intro x _hx
  dsimp only [g]
  ring

theorem intervalIntegrable_sq_mul_log_one_add :
    IntervalIntegrable (fun x : ℝ ↦ x ^ 2 * Real.log (1 + x)) volume 0 1 := by
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
  exact ((continuousAt_id.pow 2).mul hlog).continuousWithinAt

theorem integral_sq_centered :
    (∫ x : ℝ in -1..1, x ^ 2) = 2 / 3 := by
  rw [integral_pow]
  norm_num

/-- Exact full endpoint-potential contribution of the centered degree-one
mode. -/
theorem integral_endpointPotential_mul_sq :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ 2) =
      8 / 9 - (2 / 3 : ℝ) * Real.log 2 := by
  let q : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * x ^ 2
  have hqEven : Function.Even q := by
    intro x
    dsimp only [q, yoshidaEndpointPotential]
    congr 1
    · congr 3
      ring
    · ring
  let r : ℝ → ℝ := fun x ↦ -(1 / 2 : ℝ) *
    (x ^ 2 * Real.log (1 - x) + x ^ 2 * Real.log (1 + x))
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
    have hsum := intervalIntegrable_sq_mul_log_one_sub.add
      intervalIntegrable_sq_mul_log_one_add
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
  rw [show (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ 2) =
      ∫ x : ℝ in -1..1, q x by rfl, hfold]
  have hsplit : (∫ x : ℝ in 0..1, q x) =
      -(1 / 2 : ℝ) *
        ((∫ x : ℝ in 0..1, x ^ 2 * Real.log (1 - x)) +
          ∫ x : ℝ in 0..1, x ^ 2 * Real.log (1 + x)) := by
    calc
      (∫ x : ℝ in 0..1, q x) =
          ∫ x : ℝ in 0..1,
            -(1 / 2 : ℝ) *
              (x ^ 2 * Real.log (1 - x) +
                x ^ 2 * Real.log (1 + x)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hpoint] with x hx _hxI
        simpa only [r] using hx
      _ = -(1 / 2 : ℝ) *
          ∫ x : ℝ in 0..1,
            (x ^ 2 * Real.log (1 - x) +
              x ^ 2 * Real.log (1 + x)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [intervalIntegral.integral_add
          intervalIntegrable_sq_mul_log_one_sub
          intervalIntegrable_sq_mul_log_one_add]
  rw [hsplit, integral_sq_mul_log_one_sub, integral_sq_mul_log_one_add]
  ring

/-- Relative to centered `L²` mass, the full potential contributes exactly
`4/3 - log 2` on degree one. -/
theorem endpointPotential_degree_one_ratio :
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * x ^ 2) =
      (4 / 3 - Real.log 2) * ∫ x : ℝ in -1..1, x ^ 2 := by
  rw [integral_endpointPotential_mul_sq, integral_sq_centered]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialExactLowMode
