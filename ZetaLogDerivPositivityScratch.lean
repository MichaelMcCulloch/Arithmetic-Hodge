import ArithmeticHodge.Analysis.ZetaZeroFreeRegionReduction

set_option autoImplicit false

open Complex Real Set
open scoped ArithmeticFunction LSeries.notation

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

theorem trig_341_nonneg_scratch (theta : ℝ) :
    0 ≤ 3 + 4 * Real.cos theta + Real.cos (2 * theta) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (Real.cos theta + 1)]

private theorem re_vonMangoldt_term_scratch
    (sigma t : ℝ) (k : ℕ) :
    (LSeries.term (fun n : ℕ ↦
        (ArithmeticFunction.vonMangoldt n : ℂ))
      ((sigma : ℂ) + t * I) k).re =
      ArithmeticFunction.vonMangoldt k *
        (k : ℝ) ^ (-sigma) * Real.cos (t * Real.log k) := by
  by_cases hk : k = 0
  · subst k
    simp
  rw [LSeries.term_of_ne_zero hk]
  rw [div_eq_mul_inv, ← cpow_neg]
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hk)]
  have hlog : Complex.log (k : ℂ) = (Real.log k : ℂ) :=
    Complex.natCast_log.symm
  have harg :
      Complex.log (k : ℂ) * -((sigma : ℂ) + t * I) =
        ((-sigma * Real.log k : ℝ) : ℂ) +
          ((-t * Real.log k : ℝ) : ℂ) * I := by
    rw [hlog]
    push_cast
    ring
  rw [harg, Complex.exp_add_mul_I]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.exp_ofReal_re,
    Complex.exp_ofReal_im, Complex.cos_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero]
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)),
    show -t * Real.log k = -(t * Real.log k) by ring,
    Real.cos_neg]
  ring

/-- The logarithmic-derivative form of the classical `3-4-1` positivity
inequality, proved termwise from the nonnegative von Mangoldt series. -/
theorem negZetaLogDeriv_trig_nonneg_scratch
    {sigma : ℝ} (hsigma : 1 < sigma) (t : ℝ) :
    0 ≤ 3 * (-(deriv riemannZeta (sigma : ℂ) /
          riemannZeta (sigma : ℂ))).re +
      4 * (-(deriv riemannZeta ((sigma : ℂ) + t * I) /
          riemannZeta ((sigma : ℂ) + t * I))).re +
        (-(deriv riemannZeta ((sigma : ℂ) + (2 * t) * I) /
          riemannZeta ((sigma : ℂ) + (2 * t) * I))).re := by
  let a : ℕ → ℂ := fun n ↦
    (ArithmeticFunction.vonMangoldt n : ℂ)
  have hs0 : 1 < ((sigma : ℂ)).re := by simpa
  have hs1 : 1 < ((sigma : ℂ) + t * I).re := by simpa
  have hs2 : 1 < ((sigma : ℂ) + (2 * t) * I).re := by simpa
  have h0 : Summable (fun k ↦ LSeries.term a (sigma : ℂ) k) := by
    simpa only [a, LSeriesSummable] using
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs0)
  have h1 : Summable
      (fun k ↦ LSeries.term a ((sigma : ℂ) + t * I) k) := by
    simpa only [a, LSeriesSummable] using
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs1)
  have h2 : Summable
      (fun k ↦ LSeries.term a ((sigma : ℂ) + (2 * t) * I) k) := by
    simpa only [a, LSeriesSummable] using
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs2)
  have hF0 : -(deriv riemannZeta (sigma : ℂ) /
      riemannZeta (sigma : ℂ)) = LSeries a (sigma : ℂ) := by
    rw [show -(deriv riemannZeta (sigma : ℂ) /
      riemannZeta (sigma : ℂ)) =
        -deriv riemannZeta (sigma : ℂ) /
          riemannZeta (sigma : ℂ) by ring]
    exact (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs0).symm
  have hF1 : -(deriv riemannZeta ((sigma : ℂ) + t * I) /
      riemannZeta ((sigma : ℂ) + t * I)) =
        LSeries a ((sigma : ℂ) + t * I) := by
    rw [show -(deriv riemannZeta ((sigma : ℂ) + t * I) /
      riemannZeta ((sigma : ℂ) + t * I)) =
        -deriv riemannZeta ((sigma : ℂ) + t * I) /
          riemannZeta ((sigma : ℂ) + t * I) by ring]
    exact (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1).symm
  have hF2 : -(deriv riemannZeta ((sigma : ℂ) + (2 * t) * I) /
      riemannZeta ((sigma : ℂ) + (2 * t) * I)) =
        LSeries a ((sigma : ℂ) + (2 * t) * I) := by
    rw [show -(deriv riemannZeta ((sigma : ℂ) + (2 * t) * I) /
      riemannZeta ((sigma : ℂ) + (2 * t) * I)) =
        -deriv riemannZeta ((sigma : ℂ) + (2 * t) * I) /
          riemannZeta ((sigma : ℂ) + (2 * t) * I) by ring]
    exact (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs2).symm
  rw [hF0, hF1, hF2]
  change 0 ≤ 3 * (LSeries a (sigma : ℂ)).re +
    4 * (LSeries a ((sigma : ℂ) + t * I)).re +
      (LSeries a ((sigma : ℂ) + (2 * t) * I)).re
  simp only [LSeries]
  rw [Complex.re_tsum h0, Complex.re_tsum h1, Complex.re_tsum h2]
  have hR0 := (Complex.hasSum_re h0.hasSum).summable
  have hR1 := (Complex.hasSum_re h1.hasSum).summable
  have hR2 := (Complex.hasSum_re h2.hasSum).summable
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← (hR0.mul_left 3).tsum_add (hR1.mul_left 4),
    ← ((hR0.mul_left 3).add (hR1.mul_left 4)).tsum_add hR2]
  apply tsum_nonneg
  intro k
  rw [show (LSeries.term a (sigma : ℂ) k).re =
      ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-sigma) *
        Real.cos (0 * Real.log k) by
      simpa [a] using
        re_vonMangoldt_term_scratch sigma 0 k]
  rw [show (LSeries.term a ((sigma : ℂ) + t * I) k).re =
      ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-sigma) *
        Real.cos (t * Real.log k) by
      simpa only [a] using re_vonMangoldt_term_scratch sigma t k]
  rw [show (LSeries.term a ((sigma : ℂ) + (2 * t) * I) k).re =
      ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-sigma) *
        Real.cos ((2 * t) * Real.log k) by
      simpa [a] using re_vonMangoldt_term_scratch sigma (2 * t) k]
  have hLambda : 0 ≤ ArithmeticFunction.vonMangoldt k :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hrpow : 0 ≤ (k : ℝ) ^ (-sigma) := Real.rpow_nonneg (Nat.cast_nonneg k) _
  have htrig := trig_341_nonneg_scratch (t * Real.log k)
  rw [show (2 * t) * Real.log k = 2 * (t * Real.log k) by ring]
  calc
    0 ≤ (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-sigma)) *
        (3 + 4 * Real.cos (t * Real.log k) +
          Real.cos (2 * (t * Real.log k))) :=
      mul_nonneg (mul_nonneg hLambda hrpow) htrig
    _ = 3 * (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-sigma) *
          Real.cos (0 * Real.log k)) +
        4 * (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-sigma) *
          Real.cos (t * Real.log k)) +
        ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-sigma) *
          Real.cos (2 * (t * Real.log k)) := by
      rw [zero_mul, Real.cos_zero]
      ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
