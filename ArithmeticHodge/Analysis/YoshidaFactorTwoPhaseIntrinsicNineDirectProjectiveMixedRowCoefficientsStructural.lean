import ArithmeticHodge.Analysis.AffineDeterminantRowSubsetStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural

set_option autoImplicit false

open Matrix Polynomial

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveMixedRowCoefficientsStructural

noncomputable section

open AffineDeterminantRowSubsetStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural

/-!
# Mixed-row coefficients for the cutoff-nine determinant pencil

Each coefficient of a dephased prefix determinant is an invariant sum of
mixed endpoint-row determinants.  The formula retains the leading-prefix
geometry and introduces no permutation expansion.
-/

/-- Exact mixed-row formula for every coefficient of every direct dephased
prefix determinant. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_mixedRows
    (k : ℕ) (hk : k ≤ 9) (j : ℕ) :
    (factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial k hk).coeff j =
      ∑ s ∈ (Finset.univ : Finset (Fin k)).powersetCard j,
        Matrix.det
          (s.piecewise
            (factorTwoIntrinsicNineDirectDephasedLinear k hk)
            (factorTwoIntrinsicNineDirectDephasedConstant k hk)) := by
  simpa only [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial] using
    coeff_det_X_smul_add_C_eq_sum_mixedRows_card
      (factorTwoIntrinsicNineDirectDephasedLinear k hk)
      (factorTwoIntrinsicNineDirectDephasedConstant k hk) j

theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_coeff_mixedRows
    (j : ℕ) :
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff j =
      ∑ s ∈ (Finset.univ : Finset (Fin 7)).powersetCard j,
        Matrix.det
          (s.piecewise
            (factorTwoIntrinsicNineDirectDephasedLinear 7 (by omega))
            (factorTwoIntrinsicNineDirectDephasedConstant 7 (by omega))) := by
  simpa only [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven] using
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_mixedRows
      7 (by omega) j

theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight_coeff_mixedRows
    (j : ℕ) :
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight.coeff j =
      ∑ s ∈ (Finset.univ : Finset (Fin 8)).powersetCard j,
        Matrix.det
          (s.piecewise
            (factorTwoIntrinsicNineDirectDephasedLinear 8 (by omega))
            (factorTwoIntrinsicNineDirectDephasedConstant 8 (by omega))) := by
  simpa only [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialEight] using
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_mixedRows
      8 (by omega) j

theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine_coeff_mixedRows
    (j : ℕ) :
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine.coeff j =
      ∑ s ∈ (Finset.univ : Finset (Fin 9)).powersetCard j,
        Matrix.det
          (s.piecewise
            (factorTwoIntrinsicNineDirectDephasedLinear 9 (by omega))
            (factorTwoIntrinsicNineDirectDephasedConstant 9 (by omega))) := by
  simpa only [factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialNine] using
    factorTwoIntrinsicNineDirectPrefixDeterminantPolynomial_coeff_mixedRows
      9 (by omega) j

end


end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveMixedRowCoefficientsStructural
