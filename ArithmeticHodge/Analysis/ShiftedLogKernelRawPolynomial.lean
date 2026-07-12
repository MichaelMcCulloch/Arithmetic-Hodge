import ArithmeticHodge.Analysis.ShiftedLegendreLogKernel
import Mathlib.Algebra.Polynomial.Eval.SMul

set_option autoImplicit false

open Finset Polynomial

namespace ArithmeticHodge.Analysis.ShiftedLogKernelRawPolynomial

open ShiftedLegendreLogKernel

noncomputable section

/-! # Raw logarithmic-difference kernel for arbitrary polynomials -/

/-- Coefficientwise removable quotient of `p(x)-p(y)` by `x-y`. -/
def polynomialDifferenceQuotient (p : ℝ[X]) (x y : ℝ) : ℝ :=
  p.sum fun k a ↦ a * monomialDifferenceQuotient k x y

/-- The removable quotient reconstructs the exact polynomial difference. -/
theorem sub_mul_polynomialDifferenceQuotient
    (p : ℝ[X]) (x y : ℝ) :
    (x - y) * polynomialDifferenceQuotient p x y =
      p.eval x - p.eval y := by
  rw [polynomialDifferenceQuotient, Polynomial.sum_def,
    Polynomial.eval_eq_sum, Polynomial.eval_eq_sum,
    Polynomial.sum_def, Polynomial.sum_def, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (x - y) * (p.coeff k * monomialDifferenceQuotient k x y) =
      p.coeff k * ((x - y) * monomialDifferenceQuotient k x y) by ring]
  rw [sub_mul_monomialDifferenceQuotient]
  ring

theorem continuous_polynomialDifferenceQuotient
    (p : ℝ[X]) (x : ℝ) :
    Continuous (fun y : ℝ ↦ polynomialDifferenceQuotient p x y) := by
  unfold polynomialDifferenceQuotient monomialDifferenceQuotient
  simp only [Polynomial.sum_def]
  fun_prop

theorem polynomialDifferenceQuotient_eq_div
    (p : ℝ[X]) {x y : ℝ} (hxy : x ≠ y) :
    polynomialDifferenceQuotient p x y =
      (p.eval x - p.eval y) / (x - y) := by
  apply (eq_div_iff (sub_ne_zero.mpr hxy)).2
  rw [mul_comm]
  exact sub_mul_polynomialDifferenceQuotient p x y

theorem polynomialDifferenceQuotient_eq_div_abs_of_lt
    (p : ℝ[X]) {x y : ℝ} (hyx : y < x) :
    polynomialDifferenceQuotient p x y =
      (p.eval x - p.eval y) / |x - y| := by
  rw [abs_of_pos (sub_pos.mpr hyx)]
  exact polynomialDifferenceQuotient_eq_div p hyx.ne'

theorem neg_polynomialDifferenceQuotient_eq_div_abs_of_lt
    (p : ℝ[X]) {x y : ℝ} (hxy : x < y) :
    -polynomialDifferenceQuotient p x y =
      (p.eval x - p.eval y) / |x - y| := by
  rw [abs_of_neg (sub_neg.mpr hxy)]
  rw [polynomialDifferenceQuotient_eq_div p hxy.ne]
  simp only [div_eq_mul_inv, inv_neg]
  ring

/-- Split regularized logarithmic-kernel action for an arbitrary polynomial. -/
def polynomialLogKernelIntegral (p : ℝ[X]) (x : ℝ) : ℝ :=
  (∫ y in 0..x, polynomialDifferenceQuotient p x y) -
    ∫ y in x..1, polynomialDifferenceQuotient p x y

/-- The coefficientwise polynomial operator is exactly the split regularized
integral, uniformly for every polynomial. -/
theorem polynomialLogKernelIntegral_eq_eval
    (p : ℝ[X]) (x : ℝ) :
    polynomialLogKernelIntegral p x = (shiftedLogKernel p).eval x := by
  unfold polynomialLogKernelIntegral polynomialDifferenceQuotient
  simp only [Polynomial.sum_def]
  rw [intervalIntegral.integral_finset_sum]
  · rw [intervalIntegral.integral_finset_sum]
    · simp_rw [intervalIntegral.integral_const_mul]
      rw [← Finset.sum_sub_distrib]
      rw [shiftedLogKernel, Polynomial.lsum_apply, Polynomial.eval_sum]
      simp only [Polynomial.sum_def]
      apply Finset.sum_congr rfl
      intro k _
      rw [show (shiftedLogKernelMonomialLinear k) (p.coeff k) =
          p.coeff k • shiftedLogKernelMonomial k by rfl]
      rw [Polynomial.eval_smul]
      change (p.coeff k *
          (∫ y in 0..x, monomialDifferenceQuotient k x y)) -
            p.coeff k *
              (∫ y in x..1, monomialDifferenceQuotient k x y) =
        p.coeff k * (shiftedLogKernelMonomial k).eval x
      rw [← mul_sub]
      rw [← shiftedLogKernelMonomialIntegral_eq_eval]
      rfl
    · intro k _
      exact Continuous.intervalIntegrable (by
        unfold monomialDifferenceQuotient
        fun_prop) x 1
  · intro k _
    exact Continuous.intervalIntegrable (by
      unfold monomialDifferenceQuotient
      fun_prop) 0 x

/-- On `[0,1]`, the regularized polynomial action is exactly the original
absolute-distance integral. -/
theorem polynomialLogKernelIntegral_eq_integral_div_abs
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    polynomialLogKernelIntegral p x =
      ∫ y in 0..1, (p.eval x - p.eval y) / |x - y| := by
  have hne : ∀ᵐ y : ℝ, y ≠ x :=
    MeasureTheory.Measure.ae_ne MeasureTheory.volume x
  have hcont := continuous_polynomialDifferenceQuotient p x
  have hlowerAE :
      (fun y : ℝ ↦ polynomialDifferenceQuotient p x y) =ᵐ[
        MeasureTheory.volume.restrict (Set.uIoc 0 x)]
        (fun y ↦ (p.eval x - p.eval y) / |x - y|) := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hne,
      MeasureTheory.ae_restrict_mem measurableSet_uIoc] with y hy hmem
    rw [Set.uIoc_of_le hx.1] at hmem
    have hyx : y < x := lt_of_le_of_ne hmem.2 hy
    exact polynomialDifferenceQuotient_eq_div_abs_of_lt p hyx
  have hupperAE :
      (fun y : ℝ ↦ -polynomialDifferenceQuotient p x y) =ᵐ[
        MeasureTheory.volume.restrict (Set.uIoc x 1)]
        (fun y ↦ (p.eval x - p.eval y) / |x - y|) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with y hmem
    rw [Set.uIoc_of_le hx.2] at hmem
    exact neg_polynomialDifferenceQuotient_eq_div_abs_of_lt p hmem.1
  have habsLower : IntervalIntegrable
      (fun y : ℝ ↦ (p.eval x - p.eval y) / |x - y|)
      MeasureTheory.volume 0 x :=
    (hcont.intervalIntegrable 0 x).congr_ae hlowerAE
  have habsUpper : IntervalIntegrable
      (fun y : ℝ ↦ (p.eval x - p.eval y) / |x - y|)
      MeasureTheory.volume x 1 :=
    (hcont.neg.intervalIntegrable x 1).congr_ae hupperAE
  have hlowerIntegral :=
    intervalIntegral.integral_congr_ae_restrict hlowerAE
  have hupperIntegral :=
    intervalIntegral.integral_congr_ae_restrict hupperAE
  rw [polynomialLogKernelIntegral, sub_eq_add_neg,
    ← intervalIntegral.integral_neg, hlowerIntegral, hupperIntegral]
  exact intervalIntegral.integral_add_adjacent_intervals habsLower habsUpper

/-- Direct production-facing form of the raw polynomial kernel identity. -/
theorem eval_shiftedLogKernel_eq_integral_div_abs
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (shiftedLogKernel p).eval x =
      ∫ y in 0..1, (p.eval x - p.eval y) / |x - y| := by
  rw [← polynomialLogKernelIntegral_eq_eval p x]
  exact polynomialLogKernelIntegral_eq_integral_div_abs p hx

end

end ArithmeticHodge.Analysis.ShiftedLogKernelRawPolynomial
