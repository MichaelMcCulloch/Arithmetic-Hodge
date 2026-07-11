import ArithmeticHodge.Analysis.EntireFunction.MinimumModulus
import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Complex Filter Topology Real Set

namespace ArithmeticHodge.Analysis.EntireFunction

set_option autoImplicit false

/-- Triangle-inequality bound for the polynomial exponential correction in `E_p`. -/
theorem norm_weierstraßExpSum_le (p : ℕ) (w : ℂ) :
    ‖weierstraßExpSum p w‖ ≤
      ∑ k ∈ Finset.range p, ‖w‖ ^ (k + 1) / (k + 1 : ℝ) := by
  rw [weierstraßExpSum]
  calc
    ‖∑ k ∈ Finset.range p, w ^ (k + 1) / ((k + 1 : ℕ) : ℂ)‖
        ≤ ∑ k ∈ Finset.range p, ‖w ^ (k + 1) / ((k + 1 : ℕ) : ℂ)‖ :=
          norm_sum_le _ _
    _ = ∑ k ∈ Finset.range p, ‖w‖ ^ (k + 1) / (k + 1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_div, norm_pow]
      simp only [RCLike.norm_natCast]
      push_cast
      norm_num

/-- A separated factor has a logarithmic lower bound consisting of its
distance from the zero, the scale of that zero, and the exponential correction. -/
theorem log_norm_weierstraßElementary_div_lower
    (p : ℕ) (z a : ℂ) (ha : a ≠ 0) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : delta ≤ ‖z - a‖) :
    Real.log delta - Real.log ‖a‖ -
        ∑ k ∈ Finset.range p, ‖z / a‖ ^ (k + 1) / (k + 1 : ℝ) ≤
      Real.log ‖weierstraßElementary p (z / a)‖ := by
  have hza : z ≠ a := by
    intro h
    subst z
    simp at hsep
    linarith
  have hone_sub : (1 : ℂ) - z / a ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hza ((div_eq_one_iff_eq ha).mp h.symm)
  have hnorm_one_sub : ‖(1 : ℂ) - z / a‖ = ‖z - a‖ / ‖a‖ := by
    have heq : (1 : ℂ) - z / a = (a - z) / a := by
      field_simp
    rw [heq, norm_div, norm_sub_rev]
  have hlog_sep : Real.log delta ≤ Real.log ‖z - a‖ :=
    Real.log_le_log hdelta hsep
  have hre_lower : -‖weierstraßExpSum p (z / a)‖ ≤
      (weierstraßExpSum p (z / a)).re := by
    exact (abs_le.mp (abs_re_le_norm (weierstraßExpSum p (z / a)))).1
  rw [weierstraßElementary_eq, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hone_sub)
      (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)),
    Complex.norm_exp, Real.log_exp, hnorm_one_sub,
    Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza))
      (norm_ne_zero_iff.mpr ha)]
  have hsum := norm_weierstraßExpSum_le p (z / a)
  linarith

/-- Inside the half disk, a canonical factor has the standard tail lower bound. -/
theorem neg_two_mul_norm_pow_le_log_norm_weierstraßElementary
    (p : ℕ) (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) :
    -2 * ‖w‖ ^ (p + 1) ≤ Real.log ‖weierstraßElementary p w‖ := by
  let q : ℝ := ‖w‖ ^ (p + 1)
  have hw_nonneg : 0 ≤ ‖w‖ := norm_nonneg w
  have hw_one : ‖w‖ ≤ 1 := hw.trans (by norm_num)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_le_norm : q ≤ ‖w‖ := by
    dsimp [q]
    rw [pow_succ]
    exact mul_le_of_le_one_left hw_nonneg (pow_le_one₀ hw_nonneg hw_one)
  have hq_half : q ≤ 1 / 2 := hq_le_norm.trans hw
  have hclose : ‖1 - weierstraßElementary p w‖ ≤ q := by
    simpa only [q] using weierstraßElementary_bound p w hw
  have hE_lower : 1 - q ≤ ‖weierstraßElementary p w‖ := by
    calc
      1 - q ≤ 1 - ‖1 - weierstraßElementary p w‖ := sub_le_sub_left hclose 1
      _ ≤ ‖weierstraßElementary p w‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) (1 - weierstraßElementary p w)
  have hden_pos : 0 < 1 - q := by linarith
  have hE_pos : 0 < ‖weierstraßElementary p w‖ := hden_pos.trans_le hE_lower
  have hinv_le : ‖weierstraßElementary p w‖⁻¹ ≤ (1 - q)⁻¹ :=
    (inv_le_inv₀ hE_pos hden_pos).2 hE_lower
  have hrat : (1 - q)⁻¹ ≤ 1 + 2 * q := by
    apply (inv_le_iff_one_le_mul₀ hden_pos).2
    nlinarith
  calc
    -2 * ‖w‖ ^ (p + 1) = 1 - (1 + 2 * q) := by simp only [q]; ring
    _ ≤ 1 - ‖weierstraßElementary p w‖⁻¹ :=
      sub_le_sub_left (hinv_le.trans hrat) 1
    _ ≤ Real.log ‖weierstraßElementary p w‖ :=
      Real.one_sub_inv_le_log_of_pos hE_pos

/-- The logarithm of the norm of a finite nonvanishing product is the sum of
the factor log norms. -/
theorem log_norm_finset_prod {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℂ) (hf : ∀ i ∈ s, f i ≠ 0) :
    Real.log ‖∏ i ∈ s, f i‖ = ∑ i ∈ s, Real.log ‖f i‖ := by
  rw [norm_prod, Real.log_prod]
  intro i hi
  exact norm_ne_zero_iff.mpr (hf i hi)

/-- Factorwise logarithmic lower bounds compose over a finite product. -/
theorem sum_le_log_norm_finset_prod {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℂ) (lower : I → ℝ)
    (hf : ∀ i ∈ s, f i ≠ 0)
    (hlower : ∀ i ∈ s, lower i ≤ Real.log ‖f i‖) :
    ∑ i ∈ s, lower i ≤ Real.log ‖∏ i ∈ s, f i‖ := by
  rw [log_norm_finset_prod s f hf]
  exact Finset.sum_le_sum fun i hi => hlower i hi

end ArithmeticHodge.Analysis.EntireFunction
