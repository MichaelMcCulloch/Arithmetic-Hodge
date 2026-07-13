import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticScalar

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Exact factor-two two-bump functional

The local Hermitian cross and the two surviving prime terms combine into a
single global cross symbol.  The complete scalar family is therefore an exact
two-dimensional Hermitian quadratic.
-/

/-- Local cross minus the exact mixed prime symbol. -/
def factorTwoGlobalCrossSymbol (g : BombieriTest) : ℂ :=
  bombieriLocalCriticalForm g
      (normalizedDilation 2 (by norm_num) g) -
    factorTwoPrimeCrossSymbol g

/-- The mixed global functional is twice the real part of the scalar times
the factor-two global cross symbol. -/
theorem bombieriFunctional_quadraticCross_smul_dilation_two_eq
    (g : BombieriTest) (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    bombieriFunctional
        (bombieriQuadraticCrossTest g
          (c • normalizedDilation 2 (by norm_num) g)) =
      ((2 * (c * factorTwoGlobalCrossSymbol g).re : ℝ) : ℂ) := by
  rw [bombieriFunctional_quadraticCross_eq_localCross_sub_prime,
    primeSum_bombieriQuadraticCrossTest_smul_dilation_two_eq
      g c ha hab hsupport hratio]
  simp only [map_smul, smul_eq_mul]
  have hleft := LinearMap.map_smulₛₗ₂ bombieriLocalCriticalForm c
    (normalizedDilation 2 (by norm_num) g) g
  simp only [smul_eq_mul] at hleft
  rw [hleft]
  rw [← bombieriLocalCriticalForm_conj_apply
    (normalizedDilation 2 (by norm_num) g) g]
  unfold factorTwoGlobalCrossSymbol
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.ofReal_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, sub_zero]
    ring

/-- Complex-valued exact decomposition of the full two-bump quadratic. -/
theorem bombieriFunctional_twoBump_eq
    (g : BombieriTest) (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g)) =
      bombieriFunctional (bombieriQuadraticTest g) +
        ((Complex.normSq c : ℝ) : ℂ) *
          bombieriFunctional (bombieriQuadraticTest g) +
        ((2 * (c * factorTwoGlobalCrossSymbol g).re : ℝ) : ℂ) := by
  rw [bombieriFunctional_quadratic_add_eq_diagonal_add_cross,
    bombieriFunctional_quadratic_smul_normalizedDilation,
    bombieriFunctional_quadraticCross_smul_dilation_two_eq
      g c ha hab hsupport hratio]

/-- Real-valued exact scalar family formula. -/
theorem bombieriFunctional_twoBump_re
    (g : BombieriTest) (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriFunctional
      (bombieriQuadraticTest
        (g + c • normalizedDilation 2 (by norm_num) g))).re =
      (1 + Complex.normSq c) *
          (bombieriFunctional (bombieriQuadraticTest g)).re +
        2 * (c * factorTwoGlobalCrossSymbol g).re := by
  rw [bombieriFunctional_twoBump_eq
    g c ha hab hsupport hratio]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
