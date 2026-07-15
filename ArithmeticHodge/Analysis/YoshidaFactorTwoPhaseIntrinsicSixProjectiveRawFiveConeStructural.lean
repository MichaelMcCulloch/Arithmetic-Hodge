import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOuterConeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC2Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveConeStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOuterConeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural

/-- The complete raw five-mode minor lies in the strict nonnegative coefficient cone. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFive_mem_cone :
    StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial := by
  exact factorTwoIntrinsicSixProjectiveRawMinorFive_mem_cone_iff_middle_two.2
    ⟨factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_two_nonneg,
      factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_three_nonneg⟩

/-- The third projective Schur gate is now unconditional on the nonnegative
projective half-line. -/
theorem factorTwoIntrinsicSixProjectiveBaseDetX_pos
    (x : ℝ) (hx : 0 ≤ x) :
    0 < factorTwoIntrinsicSixProjectiveBaseDetX x := by
  exact factorTwoIntrinsicSixProjectiveBaseDetX_pos_of_raw_cone
    x hx factorTwoIntrinsicSixProjectiveRawMinorFive_mem_cone

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveConeStructural
