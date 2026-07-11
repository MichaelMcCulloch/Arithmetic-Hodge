import ArithmeticHodge.Analysis.EntireFunction.MinimumModulus
import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import Mathlib.Analysis.SpecialFunctions.Log.Summable

open Complex Filter Topology Real Set

namespace ArithmeticHodge.Analysis.EntireFunction

set_option autoImplicit false

/-- Away from the zero sequence, the logarithm of the norm of a convergent
canonical product is the sum of the logarithms of the factor norms. -/
theorem log_norm_tprod_weierstraßElementary
    (zeros : ℕ → ℂ) (p : ℕ)
    (hconv : Summable (fun n => (‖zeros n‖⁻¹) ^ ((p : ℝ) + 1)))
    (z : ℂ) (hne : ∀ n, z / zeros n ≠ 1) :
    Real.log ‖∏' n, weierstraßElementary p (z / zeros n)‖ =
      ∑' n, Real.log ‖weierstraßElementary p (z / zeros n)‖ := by
  let u : ℕ → ℂ := fun n => weierstraßElementary p (z / zeros n) - 1
  have hu : Summable (fun n => ‖u n‖) := by
    simpa only [u] using perturbation_summable' zeros p hconv z
  have hlog : Summable (fun n => Real.log ‖1 + u n‖) :=
    hu.summable_log_norm_one_add
  have hpos : ∀ n, 0 < ‖1 + u n‖ := by
    intro n
    apply norm_pos_iff.mpr
    simpa only [u, add_sub_cancel] using
      weierstraßElementary_ne_zero p (z / zeros n) (hne n)
  have hmult : Multipliable (fun n => weierstraßElementary p (z / zeros n)) :=
    multipliable_weierstraßElementary_raw zeros p hconv z
  have hexp :
      Real.exp (∑' n, Real.log ‖1 + u n‖) = ∏' n, ‖1 + u n‖ :=
    Real.rexp_tsum_eq_tprod hpos hlog
  calc
    Real.log ‖∏' n, weierstraßElementary p (z / zeros n)‖ =
        Real.log (∏' n, ‖weierstraßElementary p (z / zeros n)‖) := by
          rw [hmult.norm_tprod]
    _ = Real.log (Real.exp (∑' n, Real.log ‖1 + u n‖)) := by
          rw [hexp]
          congr 2
          ext n
          simp only [u, add_sub_cancel]
    _ = ∑' n, Real.log ‖1 + u n‖ := Real.log_exp _
    _ = ∑' n, Real.log ‖weierstraßElementary p (z / zeros n)‖ := by
          congr 1
          ext n
          simp only [u, add_sub_cancel]

/-- Beyond the radius `2 * R`, every higher power of `R / x` is bounded by
the summable inverse-`beta` weight, provided `beta` does not exceed that
power.  The coarse constant one is sufficient for minimum-modulus bounds. -/
theorem far_ratio_pow_le_inv_rpow
    (x R beta : ℝ) (q : ℕ)
    (hx : 0 < x) (hR : 0 < R) (hfar : 2 * R ≤ x)
    (hbeta_q : beta ≤ q) :
    (R / x) ^ q ≤ R ^ beta * (x⁻¹ ^ beta) := by
  have hratio_pos : 0 < R / x := div_pos hR hx
  have hratio_one : R / x ≤ 1 := by
    rw [div_le_one hx]
    linarith
  calc
    (R / x) ^ q = (R / x) ^ (q : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (R / x) ^ beta :=
      Real.rpow_le_rpow_of_exponent_ge hratio_pos hratio_one hbeta_q
    _ = R ^ beta * (x⁻¹ ^ beta) := by
      rw [Real.div_rpow hR.le hx.le, div_eq_mul_inv, Real.inv_rpow hx.le]

/-- A finite far-tail sum is controlled by the full inverse-`beta` sum. -/
theorem finite_sum_far_ratio_pow_le
    (a : ℕ → ℂ) (beta : ℝ) (q : ℕ)
    (hsumm : Summable (fun n => ‖a n‖⁻¹ ^ beta))
    (R : ℝ) (hR : 0 < R) (hbeta_q : beta ≤ q)
    (u : Finset ℕ)
    (hu : ∀ n ∈ u, 2 * R ≤ ‖a n‖) :
    ∑ n ∈ u, (R / ‖a n‖) ^ q ≤
      (∑' n, ‖a n‖⁻¹ ^ beta) * R ^ beta := by
  have hRbeta : 0 ≤ R ^ beta := Real.rpow_nonneg hR.le beta
  calc
    ∑ n ∈ u, (R / ‖a n‖) ^ q ≤
        ∑ n ∈ u, R ^ beta * (‖a n‖⁻¹ ^ beta) := by
      apply Finset.sum_le_sum
      intro n hn
      exact far_ratio_pow_le_inv_rpow ‖a n‖ R beta q
        (lt_of_lt_of_le (mul_pos two_pos hR) (hu n hn)) hR (hu n hn) hbeta_q
    _ = R ^ beta * ∑ n ∈ u, ‖a n‖⁻¹ ^ beta := by
      rw [Finset.mul_sum]
    _ ≤ R ^ beta * ∑' n, ‖a n‖⁻¹ ^ beta := by
      apply mul_le_mul_of_nonneg_left _ hRbeta
      exact hsumm.sum_le_tsum u
        (fun n _ => Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
    _ = (∑' n, ‖a n‖⁻¹ ^ beta) * R ^ beta := mul_comm _ _

end ArithmeticHodge.Analysis.EntireFunction

#print axioms ArithmeticHodge.Analysis.EntireFunction.log_norm_tprod_weierstraßElementary
