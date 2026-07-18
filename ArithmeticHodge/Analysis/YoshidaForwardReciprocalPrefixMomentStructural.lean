import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaForwardReciprocalPrefixMomentStructural

noncomputable section

/-!
# Forward reciprocal prefix moments

The forward factor-two logarithm becomes `log ((2 + u) / 2)` after the
centered coordinate is shifted by one.  Its polynomial moments reduce to one
base logarithm and a first-order recurrence; no fixed-degree moment table is
needed.
-/

/-- Prefix moment of the forward reciprocal kernel in the shifted
coordinate. -/
def forwardReciprocalPrefixMoment (n : Nat) (u : Real) : Real :=
  ∫ x : Real in 0..u, x ^ n / (2 + x)

private theorem two_add_pos_on_uIcc
    {u x : Real} (hu : u ∈ Icc (-1 : Real) 2)
    (hx : x ∈ uIcc (0 : Real) u) :
    0 < 2 + x := by
  have hmin : (-1 : Real) ≤ min 0 u := le_min (by norm_num) hu.1
  linarith [hx.1]

/-- Every forward reciprocal monomial is interval-integrable throughout the
range needed by the centered endpoint coordinate. -/
theorem intervalIntegrable_forwardReciprocalPrefixMoment
    (n : Nat) {u : Real} (hu : u ∈ Icc (-1 : Real) 2) :
    IntervalIntegrable (fun x : Real => x ^ n / (2 + x)) volume 0 u := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hpos := two_add_pos_on_uIcc hu hx
  exact ((continuousAt_id.pow n).div
    (continuousAt_const.add continuousAt_id) hpos.ne').continuousWithinAt

/-- Degree-zero forward reciprocal prefix moment. -/
theorem forwardReciprocalPrefixMoment_zero
    {u : Real} (hu : u ∈ Icc (-1 : Real) 2) :
    forwardReciprocalPrefixMoment 0 u =
      Real.log (2 + u) - Real.log 2 := by
  have hcomp := intervalIntegral.integral_comp_add_left
    (f := fun z : Real => 1 / z) (a := (0 : Real)) (b := u) 2
  have hpos := integral_one_div_of_pos
    (by norm_num : (0 : Real) < 2) (by linarith [hu.1] : 0 < 2 + u)
  unfold forwardReciprocalPrefixMoment
  simp only [pow_zero, one_div]
  calc
    (∫ x : Real in 0..u, (2 + x)⁻¹) =
        ∫ z : Real in 2..2 + u, z⁻¹ := by
      simpa only [one_div, add_zero] using hcomp
    _ = Real.log ((2 + u) / 2) := by simpa only [one_div] using hpos
    _ = Real.log (2 + u) - Real.log 2 := by
      rw [Real.log_div (by linarith [hu.1]) (by norm_num : (2 : Real) ≠ 0)]

/-- Structural recurrence for all forward reciprocal prefix moments. -/
theorem forwardReciprocalPrefixMoment_succ
    (n : Nat) {u : Real} (hu : u ∈ Icc (-1 : Real) 2) :
    forwardReciprocalPrefixMoment (n + 1) u =
      u ^ (n + 1) / (n + 1 : Real) -
        2 * forwardReciprocalPrefixMoment n u := by
  have hRec := intervalIntegrable_forwardReciprocalPrefixMoment n hu
  have hPow : IntervalIntegrable (fun x : Real => x ^ n) volume 0 u :=
    (continuous_id.pow n).intervalIntegrable 0 u
  unfold forwardReciprocalPrefixMoment
  calc
    (∫ x : Real in 0..u, x ^ (n + 1) / (2 + x)) =
        ∫ x : Real in 0..u,
          (x ^ n - 2 * (x ^ n / (2 + x))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hpos := two_add_pos_on_uIcc hu hx
      field_simp [hpos.ne']
      ring
    _ = (∫ x : Real in 0..u, x ^ n) -
        ∫ x : Real in 0..u, 2 * (x ^ n / (2 + x)) := by
      rw [intervalIntegral.integral_sub hPow (hRec.const_mul 2)]
    _ = u ^ (n + 1) / (n + 1 : Real) -
        2 * (∫ x : Real in 0..u, x ^ n / (2 + x)) := by
      rw [integral_pow, intervalIntegral.integral_const_mul]
      norm_num

/-- Any reciprocal moment on a subinterval is the difference of two prefix
moments. -/
theorem integral_forwardReciprocal_eq_prefix_sub
    (n : Nat) {a u : Real}
    (ha : a ∈ Icc (-1 : Real) 2) (hu : u ∈ Icc (-1 : Real) 2) :
    (∫ x : Real in a..u, x ^ n / (2 + x)) =
      forwardReciprocalPrefixMoment n u -
        forwardReciprocalPrefixMoment n a := by
  rw [forwardReciprocalPrefixMoment, forwardReciprocalPrefixMoment,
    intervalIntegral.integral_interval_sub_left]
  · exact intervalIntegrable_forwardReciprocalPrefixMoment n hu
  · exact intervalIntegrable_forwardReciprocalPrefixMoment n ha

end

end ArithmeticHodge.Analysis.YoshidaForwardReciprocalPrefixMomentStructural
