import ArithmeticHodge.Analysis.MultiplicativeWeilPrimeDilationObstruction

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# The factor-two mixed correlation enters the actual prime kernel

The previous obstruction identifies a positive value at the inverse lag.
Hermitian symmetry transports it to the `n = 2` prime kernel, showing that the
full Bombieri functional subtracts a genuinely positive mixed contribution.
-/

/-- The mixed quadratic test has the same pointwise Hermitian symmetry as a
quadratic diagonal. -/
theorem transpose_bombieriQuadraticCrossTest_apply_eq_conj
    (f g : BombieriTest) {x : ℝ} (hx : 0 < x) :
    transpose (bombieriQuadraticCrossTest f g : ℝ → ℂ) x =
      starRingEnd ℂ (bombieriQuadraticCrossTest f g x) := by
  have hsum := transpose_bombieriQuadraticTest_apply_eq_conj (f + g) hx
  have hf := transpose_bombieriQuadraticTest_apply_eq_conj f hx
  have hg := transpose_bombieriQuadraticTest_apply_eq_conj g hx
  rw [transpose_apply_of_pos _ hx] at hsum hf hg
  rw [transpose_apply_of_pos _ hx]
  change (bombieriQuadraticTest (f + g) x⁻¹ -
      bombieriQuadraticTest f x⁻¹ - bombieriQuadraticTest g x⁻¹) / x =
    starRingEnd ℂ
      (bombieriQuadraticTest (f + g) x -
        bombieriQuadraticTest f x - bombieriQuadraticTest g x)
  calc
    (bombieriQuadraticTest (f + g) x⁻¹ -
        bombieriQuadraticTest f x⁻¹ - bombieriQuadraticTest g x⁻¹) / x =
        bombieriQuadraticTest (f + g) x⁻¹ / x -
          bombieriQuadraticTest f x⁻¹ / x -
            bombieriQuadraticTest g x⁻¹ / x := by ring
    _ = starRingEnd ℂ (bombieriQuadraticTest (f + g) x) -
          starRingEnd ℂ (bombieriQuadraticTest f x) -
            starRingEnd ℂ (bombieriQuadraticTest g x) := by
      rw [hsum, hf, hg]
    _ = starRingEnd ℂ
        (bombieriQuadraticTest (f + g) x -
          bombieriQuadraticTest f x - bombieriQuadraticTest g x) := by
      simp only [map_sub]

/-- For a nonzero ratio-at-most-two test, the mixed test with its factor-two
dilation contributes strictly positively to the actual `n = 2` prime kernel.
The Bombieri functional subtracts this quantity. -/
theorem primeKernel_bombieriQuadraticCrossTest_dilation_two_re_pos
    (g : BombieriTest) {a b : ℝ}
    (hg : g ≠ 0) (ha : 0 < a)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 < (primeKernel
      (bombieriQuadraticCrossTest g
        (normalizedDilation 2 (by norm_num) g)) 1).re := by
  let h : BombieriTest := normalizedDilation 2 (by norm_num) g
  let c : BombieriTest := bombieriQuadraticCrossTest g h
  have hhalf : 0 < (c (1 / 2 : ℝ)).re := by
    dsimp only [c, h]
    exact bombieriQuadraticCrossTest_half_dilation_re_pos_of_ratio_le_two
      g hg ha hsupport hratio
  have htranspose :
      transpose (c : ℝ → ℂ) 2 = starRingEnd ℂ (c 2) := by
    dsimp only [c, h]
    exact transpose_bombieriQuadraticCrossTest_apply_eq_conj
      g (normalizedDilation 2 (by norm_num) g) (by norm_num)
  have hrelation : c (1 / 2 : ℝ) / 2 = starRingEnd ℂ (c 2) := by
    rw [transpose_apply_of_pos _ (by norm_num : (0 : ℝ) < 2)] at htranspose
    norm_num at htranspose ⊢
    exact htranspose
  have hre : (c (1 / 2 : ℝ)).re / 2 = (c 2).re := by
    calc
      (c (1 / 2 : ℝ)).re / 2 = (c (1 / 2 : ℝ) / 2).re := by
        simp
      _ = (starRingEnd ℂ (c 2)).re := congrArg Complex.re hrelation
      _ = (c 2).re := by simp
  have hc2 : 0 < (c 2).re := by linarith
  change 0 < (c 2 + transpose (c : ℝ → ℂ) 2).re
  rw [htranspose]
  simp only [Complex.add_re, Complex.conj_re]
  linarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
