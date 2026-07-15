import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC1Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC3Structural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourConeStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC1Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC3Structural

/-!
# Unconditional raw four-mode projective cone

The three mixed coefficients have independent structural proofs.  Combining
them with the already-positive endpoint coefficients places the complete raw
quartic in the strict nonnegative coefficient cone.
-/

/-- The raw `P₀/P₂/P₄/P₁` determinant has a positive constant
coefficient and every coefficient is nonnegative. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFour_mem_cone :
    StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawMinorFourPolynomial := by
  exact factorTwoIntrinsicSixProjectiveRawMinorFour_mem_cone_of_middle
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_one_nonneg
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_two_nonneg
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_three_nonneg

/-- Consequently, the second projective pivot is strictly positive on the
whole nonnegative projective half-line. -/
theorem factorTwoIntrinsicSixProjectiveBaseMinorTwoX_pos
    (x : ℝ) (hx : 0 ≤ x) :
    0 < factorTwoIntrinsicSixProjectiveBaseMinorTwoX x := by
  exact factorTwoIntrinsicSixProjectiveBaseMinorTwoX_pos_of_middle x hx
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_one_nonneg
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_two_nonneg
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient_three_nonneg

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourConeStructural
