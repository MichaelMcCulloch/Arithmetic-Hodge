import ArithmeticHodge.Analysis.ThreeByThreeConvexPencil
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4Schur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStructuralPositive

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction

noncomputable section

open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseLowSchur

/-!
# Endpoint reduction for the even `P₀/P₂/P₄` determinant

The leading coefficient in the sequential six-mode Schur proof is exactly
the determinant of the even three-mode phase matrix.  Since that matrix is
affine in the symmetric phase, positivity of its two signed endpoint
determinants propagates to the whole interval by convexity.
-/

/-- The six scalar entries of the even `P₀/P₂/P₄` phase matrix. -/
def factorTwoIntrinsicP024Determinant (a : ℝ) : ℝ :=
  symmetricDeterminant
    (factorTwoStructuralPhaseLow00 a)
    (factorTwoStructuralPhaseLow02 a)
    (factorTwoIntrinsicFourP45Cross04 a)
    (factorTwoStructuralPhaseLow22 a)
    (factorTwoIntrinsicFourP45Cross24 a)
    (factorTwoIntrinsicP4PhaseDiagonal a)

theorem factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant
    (a : ℝ) :
    factorTwoIntrinsicSixP4SchurLeading a =
      factorTwoIntrinsicP024Determinant a := by
  unfold factorTwoIntrinsicSixP4SchurLeading
    factorTwoIntrinsicSixLowDet factorTwoIntrinsicSixP4Low0
    factorTwoIntrinsicSixP4Low2 factorTwoIntrinsicP024Determinant
    symmetricDeterminant
  ring

/-- The two signed endpoint determinants are the only conditions needed for
the even three-mode leading gate throughout `[-1,1]`. -/
theorem factorTwoIntrinsicSixP4SchurLeading_pos_of_endpoints
    (a : ℝ) (haLower : -1 ≤ a) (haUpper : a ≤ 1)
    (hPlus : 0 < factorTwoIntrinsicSixP4SchurLeading 1)
    (hMinus : 0 < factorTwoIntrinsicSixP4SchurLeading (-1)) :
    0 < factorTwoIntrinsicSixP4SchurLeading a := by
  let lambda : ℝ := (1 + a) / 2
  let mu : ℝ := (1 - a) / 2
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    linarith
  have hmu : 0 ≤ mu := by
    dsimp only [mu]
    linarith
  have hsum : lambda + mu = 1 := by
    dsimp only [lambda, mu]
    ring
  have hPlusDet : 0 < factorTwoIntrinsicP024Determinant 1 := by
    rw [← factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant]
    exact hPlus
  have hMinusDet : 0 < factorTwoIntrinsicP024Determinant (-1) := by
    rw [← factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant]
    exact hMinus
  have hconv := convex_leadingMinors_pos
    (factorTwoStructuralPhaseLow00 1)
    (factorTwoStructuralPhaseLow02 1)
    (factorTwoIntrinsicFourP45Cross04 1)
    (factorTwoStructuralPhaseLow22 1)
    (factorTwoIntrinsicFourP45Cross24 1)
    (factorTwoIntrinsicP4PhaseDiagonal 1)
    (factorTwoStructuralPhaseLow00 (-1))
    (factorTwoStructuralPhaseLow02 (-1))
    (factorTwoIntrinsicFourP45Cross04 (-1))
    (factorTwoStructuralPhaseLow22 (-1))
    (factorTwoIntrinsicFourP45Cross24 (-1))
    (factorTwoIntrinsicP4PhaseDiagonal (-1))
    lambda mu hlambda hmu hsum
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.1
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.2
    (by simpa only [factorTwoIntrinsicP024Determinant] using hPlusDet)
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.1
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.2
    (by simpa only [factorTwoIntrinsicP024Determinant] using hMinusDet)
  rw [factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant]
  have hdet := hconv.2.2
  convert hdet using 1
  all_goals
    dsimp only [lambda, mu]
    unfold factorTwoIntrinsicP024Determinant symmetricDeterminant
      factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
      factorTwoStructuralPhaseLow22 factorTwoIntrinsicFourP45Cross04
      factorTwoIntrinsicFourP45Cross24
      factorTwoIntrinsicP4PhaseDiagonal
    ring

/-- Disk form of the endpoint reduction. -/
theorem factorTwoIntrinsicSixP4SchurLeading_pos_of_endpoint_gates
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hPlus : 0 < factorTwoIntrinsicSixP4SchurLeading 1)
    (hMinus : 0 < factorTwoIntrinsicSixP4SchurLeading (-1)) :
    0 < factorTwoIntrinsicSixP4SchurLeading a := by
  have haLower : -1 ≤ a := by
    nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
  have haUpper : a ≤ 1 := by
    nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  exact factorTwoIntrinsicSixP4SchurLeading_pos_of_endpoints
    a haLower haUpper hPlus hMinus

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
