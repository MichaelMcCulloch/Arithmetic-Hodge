import ArithmeticHodge.Analysis.ShiftedLogKernelRawPolynomial

set_option autoImplicit false

open Finset Polynomial Set

namespace ArithmeticHodge.Analysis.ShiftedLogKernelCrossEnergy

open ShiftedLegendreLogKernel
open ShiftedLogKernelRawPolynomial

noncomputable section

/-!
# Structural cross-energy control for the logarithmic kernel

The removable polynomial quotient is uniformly bounded on the unit square.
This is the domination input for pairing the singular logarithmic-difference
form with an arbitrary integrable function; no degree cutoff is involved.
-/

/-- A coefficientwise global bound for the removable quotient on `[0,1]^2`. -/
def polynomialDifferenceQuotientBound (p : ℝ[X]) : ℝ :=
  p.sum fun k a ↦ |a| * k

theorem polynomialDifferenceQuotientBound_nonneg (p : ℝ[X]) :
    0 ≤ polynomialDifferenceQuotientBound p := by
  rw [polynomialDifferenceQuotientBound, Polynomial.sum_def]
  exact Finset.sum_nonneg fun k _hk ↦
    mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

private theorem abs_monomialDifferenceQuotient_le
    (k : ℕ) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |monomialDifferenceQuotient k x y| ≤ k := by
  rw [monomialDifferenceQuotient]
  calc
    |∑ j ∈ Finset.range k, x ^ j * y ^ (k - 1 - j)| ≤
        ∑ j ∈ Finset.range k, |x ^ j * y ^ (k - 1 - j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [abs_mul, abs_of_nonneg (pow_nonneg hx.1 _),
        abs_of_nonneg (pow_nonneg hy.1 _)]
      exact mul_le_one₀ (pow_le_one₀ hx.1 hx.2)
        (pow_nonneg hy.1 _) (pow_le_one₀ hy.1 hy.2)
    _ = k := by simp

/-- The coefficientwise removable quotient is uniformly bounded on the whole
unit square. -/
theorem abs_polynomialDifferenceQuotient_le
    (p : ℝ[X]) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |polynomialDifferenceQuotient p x y| ≤
      polynomialDifferenceQuotientBound p := by
  rw [polynomialDifferenceQuotient, polynomialDifferenceQuotientBound,
    Polynomial.sum_def, Polynomial.sum_def]
  calc
    |∑ k ∈ p.support,
        p.coeff k * monomialDifferenceQuotient k x y| ≤
        ∑ k ∈ p.support,
          |p.coeff k * monomialDifferenceQuotient k x y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ p.support, |p.coeff k| * k := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_monomialDifferenceQuotient_le k hx hy) (abs_nonneg _)

/-- The original absolute-distance quotient inherits the same bound; the
diagonal value is harmless and both open half-squares are the two signs of
the removable quotient. -/
theorem abs_eval_sub_div_abs_le
    (p : ℝ[X]) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    abs ((p.eval x - p.eval y) / |x - y|) ≤
      polynomialDifferenceQuotientBound p := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · rw [← neg_polynomialDifferenceQuotient_eq_div_abs_of_lt p hxy,
      abs_neg]
    exact abs_polynomialDifferenceQuotient_le p hx hy
  · subst y
    simp only [sub_self, abs_zero, zero_div]
    exact polynomialDifferenceQuotientBound_nonneg p
  · rw [← polynomialDifferenceQuotient_eq_div_abs_of_lt p hyx]
    exact abs_polynomialDifferenceQuotient_le p hx hy

end

end ArithmeticHodge.Analysis.ShiftedLogKernelCrossEnergy
