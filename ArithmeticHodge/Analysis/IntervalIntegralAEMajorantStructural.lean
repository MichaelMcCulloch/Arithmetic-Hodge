import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

open MeasureTheory Set

namespace ArithmeticHodge.Analysis.IntervalIntegralAEMajorantStructural

/-!
# A nonnegative almost-everywhere interval majorant

This packages the common endpoint of pointwise majorant arguments: a
nonnegative measurable function dominated almost everywhere by an integrable
real majorant is itself interval integrable, and its interval integral is no
larger.  The hypotheses are stated on the actual `Ioc` restriction used by an
oriented interval with `a ≤ b`.
-/

theorem intervalIntegrable_and_integral_le_of_ae_nonneg_le
    {a b : ℝ} (hab : a ≤ b) (f M : ℝ → ℝ)
    (hM : IntervalIntegrable M volume a b)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc a b)))
    (hbound : ∀ᵐ x ∂volume.restrict (Ioc a b), 0 ≤ f x ∧ f x ≤ M x) :
    IntervalIntegrable f volume a b ∧
      (∫ x : ℝ in a..b, f x) ≤ ∫ x : ℝ in a..b, M x := by
  have hnorm : ∀ᵐ x ∂volume.restrict (Ioc a b), ‖f x‖ ≤ M x :=
    hbound.mono fun x hx ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
  have hfint : IntervalIntegrable f volume a b := by
    have hf' : AEStronglyMeasurable f (volume.restrict (uIoc a b)) := by
      simpa only [uIoc_of_le hab] using hf
    apply hM.mono_fun' hf'
    simpa only [uIoc_of_le hab] using hnorm
  refine ⟨hfint, ?_⟩
  have hle : ∀ᵐ x ∂volume.restrict (Ioc a b), f x ≤ M x :=
    hbound.mono fun _ hx ↦ hx.2
  have hmono := MeasureTheory.integral_mono_ae hfint.1 hM.1 hle
  simpa only [intervalIntegral.integral_of_le hab] using hmono

end ArithmeticHodge.Analysis.IntervalIntegralAEMajorantStructural
