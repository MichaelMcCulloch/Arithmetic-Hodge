import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC1Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC4Structural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOuterConeStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC1Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC4Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural

/-!
# Outer-coefficient closure for the raw five-mode cone

The first and fourth mixed coefficients have now been proved nonnegative.
Consequently the raw quintic coefficient cone is equivalent to the two
central coefficient obligations alone.
-/

/-- Exact two-gate frontier remaining after the structural `C1` and `C4`
proofs. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFive_mem_cone_iff_middle_two :
    StrictNonnegativeCoefficientCone
        factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial ↔
      0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 2 ∧
        0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 3 := by
  rw [factorTwoIntrinsicSixProjectiveRawMinorFive_mem_cone_iff_middle]
  constructor
  · rintro ⟨_, h2, h3, _⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨
      factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_one_nonneg,
      h2,
      h3,
      factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_four_nonneg⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOuterConeStructural
