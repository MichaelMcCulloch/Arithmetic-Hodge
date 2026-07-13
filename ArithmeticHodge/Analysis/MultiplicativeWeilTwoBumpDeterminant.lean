import ArithmeticHodge.Analysis.HermitianScalarDeterminant
import ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportEndpointPositive

set_option autoImplicit false

open Complex Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

open ArithmeticHodge.Analysis
open ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportEndpointPositive

noncomputable section

/-!
# Exact determinant alternative for the factor-two Bombieri family

Restricted-support structural positivity supplies the nonnegative diagonal.
The factor-two family is nonnegative in every complex direction exactly when
one explicit Hermitian determinant is nonnegative; strict determinant failure
is exactly a negative Bombieri witness.
-/

theorem bombieriFunctional_twoBump_nonneg_iff
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      Complex.normSq (factorTwoGlobalCrossSymbol g) ≤
        (bombieriFunctional (bombieriQuadraticTest g)).re ^ 2 := by
  have hA :
      0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re :=
    bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two
      g ha hab hsupport hratio
  simpa only [bombieriFunctional_twoBump_re
      g _ ha hab hsupport hratio,
    hermitianScalarValue] using
    hermitianScalar_nonneg_iff
      (bombieriFunctional (bombieriQuadraticTest g)).re
      (factorTwoGlobalCrossSymbol g) hA

theorem exists_bombieriFunctional_twoBump_neg_iff
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      (bombieriFunctional (bombieriQuadraticTest g)).re ^ 2 <
        Complex.normSq (factorTwoGlobalCrossSymbol g) := by
  have hA :
      0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re :=
    bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two
      g ha hab hsupport hratio
  simpa only [bombieriFunctional_twoBump_re
      g _ ha hab hsupport hratio,
    hermitianScalarValue] using
    exists_hermitianScalar_neg_iff
      (bombieriFunctional (bombieriQuadraticTest g)).re
      (factorTwoGlobalCrossSymbol g) hA

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
