import ArithmeticHodge.Analysis.MultiplicativeWeilFunctional
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadratic

/-!
# Small-support quadratic Bombieri tests

Multiplicative autocorrelation turns a support interval `[a,b]` into the
ratio interval `[a/b,b/a]`.  If `b/a < 2`, that interval contains no prime
power `n ≥ 2` or its reciprocal, so the finite von Mangoldt contribution to
Bombieri's functional vanishes.
-/

set_option autoImplicit false

open Complex Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Ratios of points in `[a,b]` lie in `[a/b,b/a]`. -/
theorem quadraticRatioSet_subset_Icc
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Icc a b) :
    quadraticRatioSet g ⊆ Icc (a / b) (b / a) := by
  rintro _x ⟨p, hp, rfl⟩
  have hp1 := hsupport hp.1
  have hp2 := hsupport hp.2
  have hb : 0 < b := ha.trans_le hab
  have hp2pos : 0 < p.2 := ha.trans_le hp2.1
  constructor
  · rw [div_le_div_iff₀ hb hp2pos]
    exact (mul_le_mul_of_nonneg_left hp2.2 ha.le).trans
      (mul_le_mul_of_nonneg_right hp1.1 hb.le)
  · rw [div_le_div_iff₀ hp2pos ha]
    exact (mul_le_mul_of_nonneg_right hp1.2 ha.le).trans
      (mul_le_mul_of_nonneg_left hp2.1 hb.le)

/-- The bundled quadratic test inherits the ratio interval of the original
support. -/
theorem bombieriQuadraticTest_tsupport_subset_Icc
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Icc a b) :
    tsupport (bombieriQuadraticTest g) ⊆ Icc (a / b) (b / a) :=
  (bombieriQuadraticTest_tsupport_subset_ratio g).trans
    (quadraticRatioSet_subset_Icc g ha hab hsupport)

/-- A test supported strictly between `1/2` and `2` has zero von Mangoldt
contribution: the `n = 1` coefficient vanishes and every `n ≥ 2` misses both
the direct and reflected supports. -/
theorem primeSum_eq_zero_of_tsupport_subset_Ioo_half_two
    (f : BombieriTest) (hsupport : tsupport f ⊆ Ioo (1 / 2) 2) :
    primeSum f = 0 := by
  rw [primeSum]
  have hterm (k : ℕ) : vonMangoldtPrimeSummand f k = 0 := by
    cases k with
    | zero =>
        simp [vonMangoldtPrimeSummand]
    | succ k =>
        let n : ℝ := ((k + 1 + 1 : ℕ) : ℝ)
        have hn : 2 ≤ n := by
          dsimp only [n]
          exact_mod_cast (show 2 ≤ k + 1 + 1 by omega)
        have hnpos : 0 < n := zero_lt_two.trans_le hn
        have hdirect : f n = 0 := by
          by_contra hne
          have hmem := hsupport
            (subset_tsupport f (Function.mem_support.mpr hne))
          exact (not_lt_of_ge hn) hmem.2
        have hinvLe : n⁻¹ ≤ 1 / 2 := by
          simpa only [one_div] using
            (inv_le_inv₀ hnpos (by norm_num : (0 : ℝ) < 2)).2 hn
        have hinverse : f n⁻¹ = 0 := by
          by_contra hne
          have hmem := hsupport
            (subset_tsupport f (Function.mem_support.mpr hne))
          exact (not_lt_of_ge hinvLe) hmem.1
        have hreflected : transpose (f : ℝ → ℂ) n = 0 := by
          rw [transpose_apply_of_pos _ hnpos, hinverse, zero_div]
        change (ArithmeticFunction.vonMangoldt (k + 1 + 1) : ℂ) *
          (f n + transpose (f : ℝ → ℂ) n) = 0
        rw [hdirect, hreflected, zero_add, mul_zero]
  simp only [hterm, tsum_zero]

/-- If the multiplicative width of the original support is less than two,
the quadratic test has no prime contribution. -/
theorem primeSum_bombieriQuadraticTest_eq_zero_of_support_ratio_lt_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Icc a b) (hratio : b / a < 2) :
    primeSum (bombieriQuadraticTest g) = 0 := by
  apply primeSum_eq_zero_of_tsupport_subset_Ioo_half_two
  intro x hx
  have hxIcc := bombieriQuadraticTest_tsupport_subset_Icc
    g ha hab hsupport hx
  have hb : 0 < b := ha.trans_le hab
  have hba : b < 2 * a := by
    exact (div_lt_iff₀ ha).mp hratio
  have hlower : 1 / 2 < a / b := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hb]
    nlinarith
  exact ⟨hlower.trans_le hxIcc.1, hxIcc.2.trans_lt hratio⟩

/-- On a support interval of multiplicative width below two, Bombieri's
quadratic functional consists only of its polar and archimedean pieces. -/
theorem bombieriFunctional_quadratic_eq_polar_add_arch_of_support_ratio_lt_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Icc a b) (hratio : b / a < 2) :
    bombieriFunctional (bombieriQuadraticTest g) =
      mellin (bombieriQuadraticTest g : ℝ → ℂ) 1 +
        mellin (bombieriQuadraticTest g : ℝ → ℂ) 0 +
          bombieriArchTerm (bombieriQuadraticTest g) := by
  rw [bombieriFunctional_apply,
    primeSum_bombieriQuadraticTest_eq_zero_of_support_ratio_lt_two
      g ha hab hsupport hratio]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
