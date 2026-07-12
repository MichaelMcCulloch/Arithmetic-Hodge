import Mathlib.NumberTheory.Harmonic.Int
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

set_option autoImplicit false

open Finset Polynomial Set

namespace ArithmeticHodge.Analysis.ShiftedLegendreLogKernel

noncomputable section

/-!
# The shifted logarithmic-difference kernel on monomials

For `x, y ∈ [0,1]`, removing the diagonal singularity from
`(x ^ k - y ^ k) / (x - y)` gives a finite geometric sum.  Integrating the
two sides of the diagonal separately therefore sends the monomial `X ^ k` to

`2 * harmonic k * X ^ k - ∑ j < k, (k - j)⁻¹ * X ^ j`.

The definitions below record this exact triangular polynomial identity.  No
truncation or numerical mode check enters the construction.
-/

/-- The removable polynomial quotient of `x ^ k - y ^ k` by `x - y`. -/
def monomialDifferenceQuotient (k : ℕ) (x y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, x ^ j * y ^ (k - 1 - j)

/-- The geometric-sum identity which removes the diagonal singularity. -/
theorem sub_mul_monomialDifferenceQuotient (k : ℕ) (x y : ℝ) :
    (x - y) * monomialDifferenceQuotient k x y = x ^ k - y ^ k := by
  exact (Commute.all x y).mul_geom_sum₂ k

theorem monomialDifferenceQuotient_eq_div (k : ℕ) {x y : ℝ} (hxy : x ≠ y) :
    monomialDifferenceQuotient k x y = (x ^ k - y ^ k) / (x - y) := by
  apply (eq_div_iff (sub_ne_zero.mpr hxy)).2
  rw [mul_comm]
  exact sub_mul_monomialDifferenceQuotient k x y

theorem neg_monomialDifferenceQuotient_eq_div_rev
    (k : ℕ) {x y : ℝ} (hxy : x ≠ y) :
    -monomialDifferenceQuotient k x y = (x ^ k - y ^ k) / (y - x) := by
  rw [monomialDifferenceQuotient_eq_div k hxy]
  rw [show y - x = -(x - y) by ring]
  simp only [div_eq_mul_inv, inv_neg]
  ring

/-- Below the diagonal the removable quotient agrees with division by the
absolute distance. -/
theorem monomialDifferenceQuotient_eq_div_abs_of_lt
    (k : ℕ) {x y : ℝ} (hyx : y < x) :
    monomialDifferenceQuotient k x y = (x ^ k - y ^ k) / |x - y| := by
  rw [abs_of_pos (sub_pos.mpr hyx)]
  exact monomialDifferenceQuotient_eq_div k hyx.ne'

/-- Above the diagonal the absolute-distance quotient is the negative of the
removable quotient, explaining the sign in the split integral. -/
theorem neg_monomialDifferenceQuotient_eq_div_abs_of_lt
    (k : ℕ) {x y : ℝ} (hxy : x < y) :
    -monomialDifferenceQuotient k x y = (x ^ k - y ^ k) / |x - y| := by
  rw [abs_of_neg (sub_neg.mpr hxy)]
  rw [monomialDifferenceQuotient_eq_div k hxy.ne]
  simp only [div_eq_mul_inv, inv_neg]
  ring

/-- Reversing the primitive denominators produces the harmonic number. -/
theorem sum_range_inv_nat_sub (k : ℕ) :
    (∑ j ∈ Finset.range k, ((((k - j : ℕ) : ℝ))⁻¹)) =
      (harmonic k : ℝ) := by
  rw [show (harmonic k : ℝ) =
      ∑ j ∈ Finset.range k, ((((j + 1 : ℕ) : ℝ))⁻¹) by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  rw [Finset.mem_range] at hj
  omega

/-- Exact integration of the removable monomial quotient on an arbitrary
oriented interval. -/
theorem integral_monomialDifferenceQuotient (k : ℕ) (x a b : ℝ) :
    (∫ y in a..b, monomialDifferenceQuotient k x y) =
      ∑ j ∈ Finset.range k,
        x ^ j * (b ^ (k - j) - a ^ (k - j)) / (k - j : ℕ) := by
  simp only [monomialDifferenceQuotient]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_const_mul, integral_pow]
    rw [Finset.mem_range] at hj
    rw [show k - 1 - j + 1 = k - j by omega]
    have hden : (↑(k - 1 - j) : ℝ) + 1 = (↑(k - j) : ℝ) := by
      norm_cast
      omega
    rw [hden]
    ring
  · intro j hj
    exact (continuous_const.mul (continuous_id.pow (k - 1 - j))).intervalIntegrable a b

/-- The shifted logarithmic-difference action on the monomial `x ^ k`, with
the diagonal replaced by `monomialDifferenceQuotient`.  On the two strict
halves of `[0,1]`, the preceding lemmas identify its integrands with
`(x ^ k - y ^ k) / |x - y|`. -/
def shiftedLogKernelMonomialIntegral (k : ℕ) (x : ℝ) : ℝ :=
  (∫ y in 0..x, monomialDifferenceQuotient k x y) -
    ∫ y in x..1, monomialDifferenceQuotient k x y

/-- The unregularized split integral, written with the denominator carrying
the correct sign on each side of the diagonal. -/
def rawShiftedLogKernelMonomialIntegral (k : ℕ) (x : ℝ) : ℝ :=
  (∫ y in 0..x, (x ^ k - y ^ k) / (x - y)) +
    ∫ y in x..1, (x ^ k - y ^ k) / (y - x)

/-- Replacing the diagonal by the removable geometric quotient does not
change the split interval integral.  The proof explicitly discards the
singleton diagonal as a volume-null set. -/
theorem shiftedLogKernelMonomialIntegral_eq_rawSplit (k : ℕ) (x : ℝ) :
    shiftedLogKernelMonomialIntegral k x =
      rawShiftedLogKernelMonomialIntegral k x := by
  have hne : ∀ᵐ y : ℝ, y ≠ x := by
    exact MeasureTheory.Measure.ae_ne MeasureTheory.volume x
  have hlower :
      (∫ y in 0..x, monomialDifferenceQuotient k x y) =
        ∫ y in 0..x, (x ^ k - y ^ k) / (x - y) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with y hy
    intro _
    exact monomialDifferenceQuotient_eq_div k hy.symm
  have hupper :
      (∫ y in x..1, -monomialDifferenceQuotient k x y) =
        ∫ y in x..1, (x ^ k - y ^ k) / (y - x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with y hy
    intro _
    exact neg_monomialDifferenceQuotient_eq_div_rev k hy.symm
  rw [shiftedLogKernelMonomialIntegral, rawShiftedLogKernelMonomialIntegral,
    sub_eq_add_neg, ← intervalIntegral.integral_neg, hlower, hupper]

/-- On `[0,1]`, the regularized split is exactly the original
absolute-distance integral.  The only point not covered by the strict
off-diagonal identities is `y = x`, which is removed explicitly as a
volume-null singleton. -/
theorem shiftedLogKernelMonomialIntegral_eq_integral_div_abs
    (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    shiftedLogKernelMonomialIntegral k x =
      ∫ y in 0..1, (x ^ k - y ^ k) / |x - y| := by
  have hne : ∀ᵐ y : ℝ, y ≠ x :=
    MeasureTheory.Measure.ae_ne MeasureTheory.volume x
  have hcont : Continuous (fun y : ℝ ↦ monomialDifferenceQuotient k x y) := by
    unfold monomialDifferenceQuotient
    exact continuous_finset_sum _ fun j _ ↦
      continuous_const.mul (continuous_id.pow (k - 1 - j))
  have hlowerAE :
      (fun y : ℝ ↦ monomialDifferenceQuotient k x y) =ᵐ[
        MeasureTheory.volume.restrict (Set.uIoc 0 x)]
        (fun y ↦ (x ^ k - y ^ k) / |x - y|) := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hne,
      MeasureTheory.ae_restrict_mem measurableSet_uIoc] with y hy hmem
    rw [Set.uIoc_of_le hx.1] at hmem
    have hyx : y < x := lt_of_le_of_ne hmem.2 hy
    exact monomialDifferenceQuotient_eq_div_abs_of_lt k hyx
  have hupperAE :
      (fun y : ℝ ↦ -monomialDifferenceQuotient k x y) =ᵐ[
        MeasureTheory.volume.restrict (Set.uIoc x 1)]
        (fun y ↦ (x ^ k - y ^ k) / |x - y|) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with y hmem
    rw [Set.uIoc_of_le hx.2] at hmem
    exact neg_monomialDifferenceQuotient_eq_div_abs_of_lt k hmem.1
  have habsLower : IntervalIntegrable
      (fun y : ℝ ↦ (x ^ k - y ^ k) / |x - y|)
      MeasureTheory.volume 0 x :=
    (hcont.intervalIntegrable 0 x).congr_ae hlowerAE
  have habsUpper : IntervalIntegrable
      (fun y : ℝ ↦ (x ^ k - y ^ k) / |x - y|)
      MeasureTheory.volume x 1 :=
    (hcont.neg.intervalIntegrable x 1).congr_ae hupperAE
  have hlowerIntegral :=
    intervalIntegral.integral_congr_ae_restrict hlowerAE
  have hupperIntegral :=
    intervalIntegral.integral_congr_ae_restrict hupperAE
  rw [shiftedLogKernelMonomialIntegral, sub_eq_add_neg,
    ← intervalIntegral.integral_neg, hlowerIntegral, hupperIntegral]
  exact intervalIntegral.integral_add_adjacent_intervals habsLower habsUpper

/-- Exact symbolic evaluation of the split logarithmic-difference integral. -/
theorem shiftedLogKernelMonomialIntegral_eq (k : ℕ) (x : ℝ) :
    shiftedLogKernelMonomialIntegral k x =
      2 * (harmonic k : ℝ) * x ^ k -
        ∑ j ∈ Finset.range k, ((((k - j : ℕ) : ℝ))⁻¹) * x ^ j := by
  rw [shiftedLogKernelMonomialIntegral,
    integral_monomialDifferenceQuotient,
    integral_monomialDifferenceQuotient,
    ← Finset.sum_sub_distrib]
  calc
    _ = ∑ j ∈ Finset.range k,
        (2 * x ^ k * ((((k - j : ℕ) : ℝ))⁻¹) -
          ((((k - j : ℕ) : ℝ))⁻¹) * x ^ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hpos : 0 < k - j := Nat.sub_pos_of_lt hj
      have hpow : x ^ j * x ^ (k - j) = x ^ k := by
        rw [← pow_add, Nat.add_sub_of_le hj.le]
      have hcast : (↑(k - j) : ℝ) ≠ 0 := by positivity
      rw [zero_pow hpos.ne', one_pow]
      field_simp [hcast]
      calc
        x ^ j * (x ^ (k - j) - 0 - (1 - x ^ (k - j))) =
            2 * (x ^ j * x ^ (k - j)) - x ^ j := by ring
        _ = 2 * x ^ k - x ^ j := by rw [hpow]
    _ = 2 * (harmonic k : ℝ) * x ^ k -
        ∑ j ∈ Finset.range k, ((((k - j : ℕ) : ℝ))⁻¹) * x ^ j := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [sum_range_inv_nat_sub]
      ring

/-- The part of the logarithmic-difference image of `X ^ k` below degree `k`. -/
def shiftedLogKernelLower (k : ℕ) : ℝ[X] :=
  ∑ j : Fin k,
    Polynomial.C ((((k - (j : ℕ) : ℕ) : ℝ))⁻¹) * Polynomial.X ^ (j : ℕ)

/-- The exact polynomial image of `X ^ k` under the shifted logarithmic-
difference kernel on `[0,1]`. -/
def shiftedLogKernelMonomial (k : ℕ) : ℝ[X] :=
  Polynomial.C (2 * (harmonic k : ℝ)) * Polynomial.X ^ k -
    shiftedLogKernelLower k

/-- Scalar multiples of one monomial image, as the coefficientwise building
block for the polynomial operator. -/
def shiftedLogKernelMonomialLinear (k : ℕ) : ℝ →ₗ[ℝ] ℝ[X] where
  toFun c := c • shiftedLogKernelMonomial k
  map_add' a b := by rw [add_smul]
  map_smul' a b := by simp [smul_smul]

/-- The logarithmic-difference operator on real polynomials, extended
linearly from its exact monomial images. -/
def shiftedLogKernel : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.lsum shiftedLogKernelMonomialLinear

@[simp]
theorem shiftedLogKernel_X_pow (k : ℕ) :
    shiftedLogKernel (Polynomial.X ^ k) = shiftedLogKernelMonomial k := by
  simp [shiftedLogKernel, shiftedLogKernelMonomialLinear,
    Polynomial.X_pow_eq_monomial]

theorem degree_shiftedLogKernelLower_lt (k : ℕ) :
    (shiftedLogKernelLower k).degree < k := by
  exact Polynomial.degree_sum_fin_lt fun j : Fin k ↦
    ((((k - (j : ℕ) : ℕ) : ℝ))⁻¹)

/-- Pointwise form of the triangular monomial identity. -/
theorem eval_shiftedLogKernelMonomial (k : ℕ) (x : ℝ) :
    (shiftedLogKernelMonomial k).eval x =
      2 * (harmonic k : ℝ) * x ^ k -
        ∑ j : Fin k, ((((k - (j : ℕ) : ℕ) : ℝ))⁻¹) * x ^ (j : ℕ) := by
  rw [shiftedLogKernelMonomial, Polynomial.eval_sub,
    Polynomial.eval_C_mul, Polynomial.eval_X_pow]
  congr 1
  rw [shiftedLogKernelLower, Polynomial.eval_finset_sum]
  simp

/-- The polynomial definition is exactly the split logarithmic-difference
integral, not a sampled or fitted surrogate. -/
theorem shiftedLogKernelMonomialIntegral_eq_eval (k : ℕ) (x : ℝ) :
    shiftedLogKernelMonomialIntegral k x =
      (shiftedLogKernelMonomial k).eval x := by
  rw [shiftedLogKernelMonomialIntegral_eq, eval_shiftedLogKernelMonomial]
  congr 1
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]

/-- The coefficient at the input degree is the structural eigenvalue
`2 * harmonic k`. -/
theorem coeff_shiftedLogKernelMonomial (k : ℕ) :
    (shiftedLogKernelMonomial k).coeff k = 2 * (harmonic k : ℝ) := by
  rw [shiftedLogKernelMonomial, Polynomial.coeff_sub]
  rw [Polynomial.coeff_eq_zero_of_degree_lt (degree_shiftedLogKernelLower_lt k)]
  rw [Polynomial.coeff_C_mul_X_pow]
  simp

/-- Subtracting the harmonic eigenvalue leaves only degrees strictly below
the input degree. -/
theorem degree_shiftedLogKernelMonomial_sub_eigen_lt (k : ℕ) :
    (shiftedLogKernelMonomial k -
      Polynomial.C (2 * (harmonic k : ℝ)) * Polynomial.X ^ k).degree <
        (k : WithBot ℕ) := by
  have hrewrite :
      shiftedLogKernelMonomial k -
          Polynomial.C (2 * (harmonic k : ℝ)) * Polynomial.X ^ k =
        -shiftedLogKernelLower k := by
    rw [shiftedLogKernelMonomial]
    abel
  rw [hrewrite, Polynomial.degree_neg]
  exact degree_shiftedLogKernelLower_lt k

/-- Every positive-degree monomial image retains its degree. -/
theorem degree_shiftedLogKernelMonomial {k : ℕ} (hk : k ≠ 0) :
    (shiftedLogKernelMonomial k).degree = k := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero
  · apply (Polynomial.degree_sub_le _ _).trans
    refine max_le ?_ (degree_shiftedLogKernelLower_lt k).le
    exact Polynomial.degree_C_mul_X_pow_le _ _
  · rw [coeff_shiftedLogKernelMonomial]
    have hhq : harmonic k ≠ 0 := (harmonic_pos hk).ne'
    have hhr : (harmonic k : ℝ) ≠ 0 := by exact_mod_cast hhq
    exact mul_ne_zero (by norm_num) hhr

/-- The leading coefficient of every positive-degree image is the same
harmonic eigenvalue visible in the triangular formula. -/
theorem leadingCoeff_shiftedLogKernelMonomial {k : ℕ} (hk : k ≠ 0) :
    (shiftedLogKernelMonomial k).leadingCoeff = 2 * (harmonic k : ℝ) := by
  rw [Polynomial.leadingCoeff,
    Polynomial.natDegree_eq_of_degree_eq_some (degree_shiftedLogKernelMonomial hk),
    coeff_shiftedLogKernelMonomial]

end

end ArithmeticHodge.Analysis.ShiftedLegendreLogKernel
