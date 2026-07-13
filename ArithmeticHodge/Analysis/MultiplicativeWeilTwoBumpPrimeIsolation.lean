import ArithmeticHodge.Analysis.MultiplicativeWeilTwoBumpCrossFormula

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Exact prime isolation for the factor-two two-bump family

For a test of multiplicative support width at most two, the mixed test with a
factor-two normalized dilation can meet the positive integers only at two and
three.  This is a structural support theorem; no finite coefficient table is
used.
-/

/-- Above the endpoint two, the quadratic autocorrelation vanishes by its
ratio-support inclusion. -/
theorem bombieriQuadraticTest_apply_eq_zero_of_two_lt
    (g : BombieriTest) {a b x : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (hx : 2 < x) :
    bombieriQuadraticTest g x = 0 := by
  by_contra hne
  have hmem := bombieriQuadraticTest_tsupport_subset_Icc
    g ha hab hsupport
    (subset_tsupport (bombieriQuadraticTest g)
      (Function.mem_support.mpr hne))
  exact (not_lt_of_ge (hmem.2.trans hratio)) hx

/-- Endpoint-inclusive version of the upper support bound. -/
theorem bombieriQuadraticTest_apply_eq_zero_of_two_le
    (g : BombieriTest) {a b x : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (hx : 2 ≤ x) :
    bombieriQuadraticTest g x = 0 := by
  rcases hx.eq_or_lt with hxeq | hxlt
  · rw [← hxeq]
    exact bombieriQuadraticTest_apply_two_eq_zero_of_support_ratio_le_two
      g ha hsupport hratio
  · exact bombieriQuadraticTest_apply_eq_zero_of_two_lt
      g ha hab hsupport hratio hxlt

/-- Every direct mixed value at or beyond four vanishes. -/
theorem bombieriQuadraticCrossTest_smul_dilation_two_apply_eq_zero_of_four_le
    (g : BombieriTest) (c : ℂ) {a b x : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (hx : 4 ≤ x) :
    bombieriQuadraticCrossTest g
        (c • normalizedDilation 2 (by norm_num) g) x = 0 := by
  rw [bombieriQuadraticCrossTest_smul_dilation_two,
    bombieriQuadraticTest_apply_eq_zero_of_two_le
      g ha hab hsupport hratio (by linarith : 2 ≤ x / 2),
    bombieriQuadraticTest_apply_eq_zero_of_two_le
      g ha hab hsupport hratio (by linarith : 2 ≤ 2 * x)]
  ring

/-- All prime kernels with natural index at least three (integer argument at
least four) vanish. -/
theorem primeKernel_bombieriQuadraticCrossTest_smul_dilation_two_eq_zero_of_three_le
    (g : BombieriTest) (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) {k : ℕ} (hk : 3 ≤ k) :
    primeKernel
        (bombieriQuadraticCrossTest g
          (c • normalizedDilation 2 (by norm_num) g)) k = 0 := by
  let f : BombieriTest := bombieriQuadraticCrossTest g
    (c • normalizedDilation 2 (by norm_num) g)
  let x : ℝ := ((k + 1 : ℕ) : ℝ)
  have hx : 4 ≤ x := by
    dsimp only [x]
    exact_mod_cast (show 4 ≤ k + 1 by omega)
  have hxpos : 0 < x := (by linarith : 0 < x)
  have hdirect : f x = 0 := by
    dsimp only [f]
    exact
      bombieriQuadraticCrossTest_smul_dilation_two_apply_eq_zero_of_four_le
        g c ha hab hsupport hratio hx
  have hreflected : transpose (f : ℝ → ℂ) x = 0 := by
    have hconj := transpose_bombieriQuadraticCrossTest_apply_eq_conj
      g (c • normalizedDilation 2 (by norm_num) g) hxpos
    change transpose (f : ℝ → ℂ) x = starRingEnd ℂ (f x) at hconj
    rw [hdirect, map_zero] at hconj
    exact hconj
  change f x + transpose (f : ℝ → ℂ) x = 0
  rw [hdirect, hreflected, zero_add]

/-- The infinite prime sum is exactly the sum of its `n = 2` and `n = 3`
terms. -/
theorem primeSum_bombieriQuadraticCrossTest_smul_dilation_two_eq_two_terms
    (g : BombieriTest) (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    primeSum
        (bombieriQuadraticCrossTest g
          (c • normalizedDilation 2 (by norm_num) g)) =
      vonMangoldtPrimeSummand
          (bombieriQuadraticCrossTest g
            (c • normalizedDilation 2 (by norm_num) g)) 1 +
        vonMangoldtPrimeSummand
          (bombieriQuadraticCrossTest g
            (c • normalizedDilation 2 (by norm_num) g)) 2 := by
  rw [primeSum, tsum_eq_sum (s := Finset.range 3) (by
    intro k hk
    have hkge : 3 ≤ k := by
      simpa only [Finset.mem_range, not_lt] using hk
    rw [vonMangoldtPrimeSummand]
    rw [primeKernel_bombieriQuadraticCrossTest_smul_dilation_two_eq_zero_of_three_le
      g c ha hab hsupport hratio hkge, mul_zero])]
  norm_num [Finset.sum_range_succ, vonMangoldtPrimeSummand]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
