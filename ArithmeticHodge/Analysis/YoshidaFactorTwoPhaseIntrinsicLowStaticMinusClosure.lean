import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusPositive

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusClosure

open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusPositive
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive

/-!
# Intrinsic static-minus closure

The structural alternating-kernel bounds supply the sole premise of the
rational Schur argument, so the intrinsic static-minus Cauchy gate is now
unconditional.
-/

/-- The intrinsic static-minus endpoint satisfies its exact Cauchy gate. -/
theorem factorTwoIntrinsicStaticMinusCauchy :
    FactorTwoIntrinsicStaticCauchy (-1) := by
  exact factorTwoIntrinsicStaticMinusCauchy_of_alternatingSharpBounds
    factorTwoIntrinsicAlternatingSharpBounds

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticMinusClosure
