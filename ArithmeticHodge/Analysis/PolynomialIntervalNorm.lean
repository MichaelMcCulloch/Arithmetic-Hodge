import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false

open MeasureTheory Polynomial Set

namespace ArithmeticHodge.Analysis.PolynomialIntervalNorm

noncomputable section

/-! # Definiteness of the polynomial `L²` pairing on an interval -/

/-- A real polynomial with zero squared integral on `[0,1]` is the zero
polynomial. -/
theorem eq_zero_of_integral_eval_sq_eq_zero
    (p : ℝ[X])
    (hzero : (∫ x : ℝ in 0..1, p.eval x ^ 2) = 0) :
    p = 0 := by
  have hpCont : Continuous (fun x : ℝ ↦ p.eval x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (p.hasDerivAt x).continuousAt
  have hsqInt : IntervalIntegrable (fun x : ℝ ↦ p.eval x ^ 2)
      volume 0 1 :=
    (hpCont.pow 2).intervalIntegrable 0 1
  have hsqAE : (fun x : ℝ ↦ p.eval x ^ 2) =ᵐ[volume.restrict (Ioc 0 1)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
      (by norm_num) (Filter.Eventually.of_forall fun x ↦ sq_nonneg (p.eval x))
      hsqInt).1 hzero
  have hpAE : (fun x : ℝ ↦ p.eval x) =ᵐ[volume.restrict (Ioc 0 1)] 0 := by
    filter_upwards [hsqAE] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    nlinarith
  have hpAEOpen :
      (fun x : ℝ ↦ p.eval x) =ᵐ[volume.restrict (Ioo 0 1)] 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hpAE
  have hpEqOn : Set.EqOn (fun x : ℝ ↦ p.eval x) 0 (Ioo 0 1) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hpAEOpen isOpen_Ioo hpCont.continuousOn
      continuous_const.continuousOn
  apply Polynomial.eq_zero_of_infinite_isRoot p
  apply (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).mono
  intro x hx
  simpa only [Polynomial.IsRoot, Pi.zero_apply] using hpEqOn hx

end

end ArithmeticHodge.Analysis.PolynomialIntervalNorm
