import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral

namespace ArithmeticHodge.Analysis.TrapezoidalErrorBounds

/-!
Signed one-step trapezoidal-error bounds and the exact Peano-kernel identity.
The error convention is Mathlib's `trapezoidal_integral - intervalIntegral`.
-/

theorem trapezoidal_error_one_nonpos_of_concaveOn
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hconc : ConcaveOn ℝ (Icc a b) f) :
    trapezoidal_error f 1 a b ≤ 0 := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let line : ℝ → ℝ := fun t ↦
    ((b - t) / (b - a)) * f a + ((t - a) / (b - a)) * f b
  have hba : 0 < b - a := sub_pos.mpr hab
  have hline : IntervalIntegrable line volume a b :=
    Continuous.intervalIntegrable (by fun_prop) a b
  have hpoint : ∀ t ∈ Icc a b, line t ≤ f t := by
    intro t ht
    have hleft : 0 ≤ (b - t) / (b - a) := div_nonneg (sub_nonneg.mpr ht.2) hba.le
    have hright : 0 ≤ (t - a) / (b - a) := div_nonneg (sub_nonneg.mpr ht.1) hba.le
    have hsum : (b - t) / (b - a) + (t - a) / (b - a) = 1 := by
      field_simp
      ring
    have h := hconc.2 (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
      (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
      hleft hright hsum
    have hcoord :
        (b - t) / (b - a) * a + (t - a) / (b - a) * b = t := by
      field_simp
      ring
    simpa [line, smul_eq_mul, hcoord] using h
  have hmono := intervalIntegral.integral_mono_on hab.le hline hf hpoint
  have hlineIntegral :
      (∫ t in a..b, line t) = (b - a) / 2 * (f a + f b) := by
    have hleftInt :
        (∫ t in a..b, (b - t) / (b - a)) = (b - a) / 2 := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub
          (f := fun _ : ℝ ↦ b) (g := fun t : ℝ ↦ t)
          (Continuous.intervalIntegrable continuous_const a b)
          (Continuous.intervalIntegrable continuous_id a b)]
      simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
      field_simp
      ring
    have hrightInt :
        (∫ t in a..b, (t - a) / (b - a)) = (b - a) / 2 := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub
          (f := fun t : ℝ ↦ t) (g := fun _ : ℝ ↦ a)
          (Continuous.intervalIntegrable continuous_id a b)
          (Continuous.intervalIntegrable continuous_const a b)]
      simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
      field_simp
      ring
    rw [show line = fun t ↦
        ((b - t) / (b - a)) * f a + ((t - a) / (b - a)) * f b by rfl,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) a b)
        (Continuous.intervalIntegrable (by fun_prop) a b),
      intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const, hleftInt, hrightInt]
    ring
  rw [hlineIntegral] at hmono
  simpa [trapezoidal_error, trapezoidal_integral_one] using sub_nonpos.mpr hmono

theorem trapezoidal_error_one_nonneg_of_convexOn
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hconv : ConvexOn ℝ (Icc a b) f) :
    0 ≤ trapezoidal_error f 1 a b := by
  have hneg := trapezoidal_error_one_nonpos_of_concaveOn
    hab hf.neg hconv.neg
  have heq : trapezoidal_error (-f) 1 a b =
      -trapezoidal_error f 1 a b := by
    simp [trapezoidal_error, trapezoidal_integral_one]
    ring
  rw [heq] at hneg
  linarith

theorem trapezoidal_error_one_eq_integral_secondDerivKernel
    {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hf' : ∀ t, HasDerivAt f (f' t) t)
    (hf'' : ∀ t, HasDerivAt f' (f'' t) t)
    (hf'_int : IntervalIntegrable f' volume a b)
    (hf''_int : IntervalIntegrable f'' volume a b) :
    trapezoidal_error f 1 a b =
      ∫ t in a..b, ((t - a) * (b - t) / 2) * f'' t := by
  let w : ℝ → ℝ := fun t ↦ (t - a) * (b - t) / 2
  let w' : ℝ → ℝ := fun t ↦ (a + b - 2 * t) / 2
  let w'' : ℝ → ℝ := fun _ ↦ -1
  have hw : ∀ t, HasDerivAt w (w' t) t := by
    intro t
    dsimp [w, w']
    convert ((hasDerivAt_id t).sub_const a |>.mul
      ((hasDerivAt_const t b).sub (hasDerivAt_id t))).div_const 2 using 1
    simp only [Pi.sub_apply, id_eq]
    ring_nf
  have hw' : ∀ t, HasDerivAt w' (w'' t) t := by
    intro t
    dsimp [w', w'']
    convert (((hasDerivAt_const t (a + b)).sub
      ((hasDerivAt_const t 2).mul (hasDerivAt_id t))).div_const 2) using 1
    ring
  have hw'_int : IntervalIntegrable w' volume a b :=
    Continuous.intervalIntegrable (continuous_iff_continuousAt.mpr fun t ↦
      (hw' t).continuousAt) a b
  have hw''_int : IntervalIntegrable w'' volume a b :=
    Continuous.intervalIntegrable continuous_const a b
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := w) (u' := w') (v := f') (v' := f'') (a := a) (b := b)
    (fun t _ht ↦ hw t) (fun t _ht ↦ hf'' t) hw'_int hf''_int
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := w') (u' := w'') (v := f) (v' := f') (a := a) (b := b)
    (fun t _ht ↦ hw' t) (fun t _ht ↦ hf' t) hw''_int hf'_int
  rw [hsecond] at hfirst
  dsimp [w, w', w''] at hfirst ⊢
  simp only [sub_self, zero_mul, mul_zero,
    intervalIntegral.integral_neg, neg_one_mul] at hfirst
  rw [trapezoidal_error, trapezoidal_integral_one]
  linarith

end ArithmeticHodge.Analysis.TrapezoidalErrorBounds
