import ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalPhysical
import ArithmeticHodge.Analysis.MultiplicativeWeilTwoBumpDeterminant

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoParityDeterminant

noncomputable section

open MultiplicativeWeil
open YoshidaCriticalLogCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoDiagonalGeometric
open YoshidaFactorTwoDiagonalPhysical

/-!
# Exact folded factor-two determinant

The factor-two cross norm and same-seed determinant are rewritten exactly in
the real symmetric and imaginary antisymmetric parity channels of the folded
self-correlation.  The endpoint-retaining physical diagonal remains coupled
to both channels.
-/

/-- The factor-two cross norm is the sum of the squares of its exact folded
real and imaginary parity channels. -/
theorem factorTwoGlobalCrossSymbol_normSq_eq_foldedParity
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let R : ℝ :=
      (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoSymmetricWeight s * (factorTwoSelfCorrelation g s).re) -
        (Real.log 2 / Real.sqrt 2) * (factorTwoSelfCorrelation g 0).re -
        (Real.log 3 / Real.sqrt 3) *
          (factorTwoSelfCorrelation g factorTwoPrimeShift).re
    let I : ℝ :=
      (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoAntisymmetricWeight s * (factorTwoSelfCorrelation g s).im) -
        (Real.log 3 / Real.sqrt 3) *
          (factorTwoSelfCorrelation g factorTwoPrimeShift).im
    Complex.normSq (factorTwoGlobalCrossSymbol g) = R ^ 2 + I ^ 2 := by
  dsimp only
  rw [Complex.normSq_apply,
    factorTwoGlobalCrossSymbol_re_eq_parity g ha hab hsupport hratio,
    factorTwoGlobalCrossSymbol_im_eq_parity g ha hab hsupport hratio]
  ring

/-- The exact factor-two determinant gap in the endpoint-retaining physical
diagonal and folded parity coordinates. -/
theorem bombieriFactorTwoDeterminantGap_eq_foldedParity
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    let D : ℝ :=
      (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoDiagonalPhysicalIntegrand g s) -
        (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
          Real.log 2 + Real.log Real.pi) * factorTwoSelfCorrelationRe g 0 -
        2 * (Real.log 2 / Real.sqrt 2) *
          factorTwoSelfCorrelationRe g factorTwoLogLength
    let R : ℝ :=
      (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoSymmetricWeight s * (factorTwoSelfCorrelation g s).re) -
        (Real.log 2 / Real.sqrt 2) * (factorTwoSelfCorrelation g 0).re -
        (Real.log 3 / Real.sqrt 3) *
          (factorTwoSelfCorrelation g factorTwoPrimeShift).re
    let I : ℝ :=
      (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoAntisymmetricWeight s * (factorTwoSelfCorrelation g s).im) -
        (Real.log 3 / Real.sqrt 3) *
          (factorTwoSelfCorrelation g factorTwoPrimeShift).im
    (bombieriFunctional (bombieriQuadraticTest g)).re ^ 2 -
        Complex.normSq (factorTwoGlobalCrossSymbol g) =
      D ^ 2 - R ^ 2 - I ^ 2 := by
  dsimp only
  rw [bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
      g ha hab hsupport hratio,
    factorTwoGlobalCrossSymbol_normSq_eq_foldedParity
      g ha hab hsupport hratio]
  ring

/-- Universal nonnegativity on the same-seed factor-two span is exactly the
folded parity determinant inequality. -/
theorem bombieriFunctional_twoBump_nonneg_iff_foldedParity
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      let D : ℝ :=
        (∫ s : ℝ in 0..factorTwoLogLength,
            factorTwoDiagonalPhysicalIntegrand g s) -
          (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
            Real.log 2 + Real.log Real.pi) * factorTwoSelfCorrelationRe g 0 -
          2 * (Real.log 2 / Real.sqrt 2) *
            factorTwoSelfCorrelationRe g factorTwoLogLength
      let R : ℝ :=
        (∫ s : ℝ in 0..factorTwoLogLength,
            factorTwoSymmetricWeight s * (factorTwoSelfCorrelation g s).re) -
          (Real.log 2 / Real.sqrt 2) * (factorTwoSelfCorrelation g 0).re -
          (Real.log 3 / Real.sqrt 3) *
            (factorTwoSelfCorrelation g factorTwoPrimeShift).re
      let I : ℝ :=
        (∫ s : ℝ in 0..factorTwoLogLength,
            factorTwoAntisymmetricWeight s * (factorTwoSelfCorrelation g s).im) -
          (Real.log 3 / Real.sqrt 3) *
            (factorTwoSelfCorrelation g factorTwoPrimeShift).im
      R ^ 2 + I ^ 2 ≤ D ^ 2 := by
  dsimp only
  rw [bombieriFunctional_twoBump_nonneg_iff g ha hab hsupport hratio,
    factorTwoGlobalCrossSymbol_normSq_eq_foldedParity
      g ha hab hsupport hratio,
    bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
      g ha hab hsupport hratio]

/-- A strict reverse of the folded parity determinant is exactly the existence
of a negative same-seed factor-two Bombieri test. -/
theorem exists_bombieriFunctional_twoBump_neg_iff_foldedParity
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      let D : ℝ :=
        (∫ s : ℝ in 0..factorTwoLogLength,
            factorTwoDiagonalPhysicalIntegrand g s) -
          (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
            Real.log 2 + Real.log Real.pi) * factorTwoSelfCorrelationRe g 0 -
          2 * (Real.log 2 / Real.sqrt 2) *
            factorTwoSelfCorrelationRe g factorTwoLogLength
      let R : ℝ :=
        (∫ s : ℝ in 0..factorTwoLogLength,
            factorTwoSymmetricWeight s * (factorTwoSelfCorrelation g s).re) -
          (Real.log 2 / Real.sqrt 2) * (factorTwoSelfCorrelation g 0).re -
          (Real.log 3 / Real.sqrt 3) *
            (factorTwoSelfCorrelation g factorTwoPrimeShift).re
      let I : ℝ :=
        (∫ s : ℝ in 0..factorTwoLogLength,
            factorTwoAntisymmetricWeight s * (factorTwoSelfCorrelation g s).im) -
          (Real.log 3 / Real.sqrt 3) *
            (factorTwoSelfCorrelation g factorTwoPrimeShift).im
      D ^ 2 < R ^ 2 + I ^ 2 := by
  dsimp only
  rw [exists_bombieriFunctional_twoBump_neg_iff g ha hab hsupport hratio,
    factorTwoGlobalCrossSymbol_normSq_eq_foldedParity
      g ha hab hsupport hratio,
    bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
      g ha hab hsupport hratio]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoParityDeterminant
