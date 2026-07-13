import ArithmeticHodge.Analysis.MultiplicativeWeilTwoBumpPrimeIsolation

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Closed form of the factor-two mixed prime contribution

The two surviving prime indices combine into one complex cross symbol.  The
prime contribution of the scalar two-bump family is twice the real part of
the scalar times this symbol.
-/

/-- The exact prime-side off-diagonal symbol at factor two. -/
def factorTwoPrimeCrossSymbol (g : BombieriTest) : ℂ :=
  (((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ) : ℂ) *
      starRingEnd ℂ (bombieriQuadraticTest g 1)) +
    (((ArithmeticFunction.vonMangoldt 3 / Real.sqrt 2 : ℝ) : ℂ) *
      starRingEnd ℂ (bombieriQuadraticTest g (3 / 2 : ℝ)))

theorem bombieriQuadraticCrossTest_smul_dilation_two_apply_two
    (g : BombieriTest) (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    bombieriQuadraticCrossTest g
        (c • normalizedDilation 2 (by norm_num) g) 2 =
      starRingEnd ℂ c / ((Real.sqrt 2 : ℝ) : ℂ) *
        bombieriQuadraticTest g 1 := by
  rw [bombieriQuadraticCrossTest_smul_dilation_two]
  have hfour : bombieriQuadraticTest g 4 = 0 :=
    bombieriQuadraticTest_apply_eq_zero_of_two_le
      g ha hab hsupport hratio (by norm_num)
  norm_num [hfour]

theorem bombieriQuadraticCrossTest_smul_dilation_two_apply_three
    (g : BombieriTest) (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    bombieriQuadraticCrossTest g
        (c • normalizedDilation 2 (by norm_num) g) 3 =
      starRingEnd ℂ c / ((Real.sqrt 2 : ℝ) : ℂ) *
        bombieriQuadraticTest g (3 / 2 : ℝ) := by
  rw [bombieriQuadraticCrossTest_smul_dilation_two]
  have hsix : bombieriQuadraticTest g 6 = 0 :=
    bombieriQuadraticTest_apply_eq_zero_of_two_le
      g ha hab hsupport hratio (by norm_num)
  norm_num [hsix]

theorem primeKernel_bombieriQuadraticCrossTest_smul_dilation_two_one
    (g : BombieriTest) (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    primeKernel
        (bombieriQuadraticCrossTest g
          (c • normalizedDilation 2 (by norm_num) g)) 1 =
      ((2 * (starRingEnd ℂ c / ((Real.sqrt 2 : ℝ) : ℂ) *
        bombieriQuadraticTest g 1).re : ℝ) : ℂ) := by
  change bombieriQuadraticCrossTest g
        (c • normalizedDilation 2 (by norm_num) g) 2 +
      transpose
        (bombieriQuadraticCrossTest g
          (c • normalizedDilation 2 (by norm_num) g) : ℝ → ℂ) 2 = _
  rw [transpose_bombieriQuadraticCrossTest_apply_eq_conj
      g (c • normalizedDilation 2 (by norm_num) g) (by norm_num),
    bombieriQuadraticCrossTest_smul_dilation_two_apply_two
      g c ha hab hsupport hratio]
  exact Complex.add_conj _

theorem primeKernel_bombieriQuadraticCrossTest_smul_dilation_two_two
    (g : BombieriTest) (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    primeKernel
        (bombieriQuadraticCrossTest g
          (c • normalizedDilation 2 (by norm_num) g)) 2 =
      ((2 * (starRingEnd ℂ c / ((Real.sqrt 2 : ℝ) : ℂ) *
        bombieriQuadraticTest g (3 / 2 : ℝ)).re : ℝ) : ℂ) := by
  change bombieriQuadraticCrossTest g
        (c • normalizedDilation 2 (by norm_num) g) 3 +
      transpose
        (bombieriQuadraticCrossTest g
          (c • normalizedDilation 2 (by norm_num) g) : ℝ → ℂ) 3 = _
  rw [transpose_bombieriQuadraticCrossTest_apply_eq_conj
      g (c • normalizedDilation 2 (by norm_num) g) (by norm_num),
    bombieriQuadraticCrossTest_smul_dilation_two_apply_three
      g c ha hab hsupport hratio]
  exact Complex.add_conj _

/-- Exact closed form of the complete mixed prime contribution. -/
theorem primeSum_bombieriQuadraticCrossTest_smul_dilation_two_eq
    (g : BombieriTest) (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    primeSum
        (bombieriQuadraticCrossTest g
          (c • normalizedDilation 2 (by norm_num) g)) =
      ((2 * (c * factorTwoPrimeCrossSymbol g).re : ℝ) : ℂ) := by
  rw [primeSum_bombieriQuadraticCrossTest_smul_dilation_two_eq_two_terms
      g c ha hab hsupport hratio]
  unfold vonMangoldtPrimeSummand
  rw [primeKernel_bombieriQuadraticCrossTest_smul_dilation_two_one
      g c ha hab hsupport hratio,
    primeKernel_bombieriQuadraticCrossTest_smul_dilation_two_two
      g c ha hab hsupport hratio]
  unfold factorTwoPrimeCrossSymbol
  apply Complex.ext
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im,
      Complex.div_ofReal_re, Complex.div_ofReal_im, zero_mul, sub_zero,
      mul_zero]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, add_zero]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
