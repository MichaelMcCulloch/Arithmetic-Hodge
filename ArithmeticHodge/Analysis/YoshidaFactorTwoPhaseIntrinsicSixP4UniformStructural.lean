import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4UniformStructural

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur

/-!
# Uniform structural positivity of the intrinsic six-mode `P4` pivot

The two signed endpoint determinants are positive by the structural endpoint
proofs.  Convexity of the affine `P0/P2/P4` matrix propagates positivity to
every phase in `[-1,1]`.  Exact projective homogenization then transfers this
result to the whole nonnegative projective half-line.
-/

/-- The intrinsic six-mode `P4` Schur leading coefficient is positive at every
phase in the closed interval `[-1,1]`. -/
theorem factorTwoIntrinsicSixP4SchurLeading_pos
    (a : ℝ) (haLower : -1 ≤ a) (haUpper : a ≤ 1) :
    0 < factorTwoIntrinsicSixP4SchurLeading a := by
  exact factorTwoIntrinsicSixP4SchurLeading_pos_of_endpoints
    a haLower haUpper
    factorTwoIntrinsicSixP4SchurLeading_plus_pos
    factorTwoIntrinsicSixP4SchurLeading_minus_pos

/-- Disk-coordinate form of uniform intrinsic six-mode `P4` positivity. -/
theorem factorTwoIntrinsicSixP4SchurLeading_pos_on_disk
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 < factorTwoIntrinsicSixP4SchurLeading a := by
  exact factorTwoIntrinsicSixP4SchurLeading_pos_of_endpoint_gates
    a b hab
    factorTwoIntrinsicSixP4SchurLeading_plus_pos
    factorTwoIntrinsicSixP4SchurLeading_minus_pos

/-- The first intrinsic six-mode projective pivot is positive on the entire
nonnegative projective half-line. -/
theorem factorTwoIntrinsicSixProjectiveP4Pivot_pos
    (x : ℝ) (hx : 0 ≤ x) :
    0 < factorTwoIntrinsicSixProjectiveP4Pivot x := by
  apply (factorTwoIntrinsicSixProjectiveP4Pivot_pos_iff x hx).2
  have hden : 0 < 1 + x := by linarith
  apply factorTwoIntrinsicSixP4SchurLeading_pos
  · exact (le_div_iff₀ hden).2 (by linarith)
  · exact (div_le_iff₀ hden).2 (by linarith)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4UniformStructural
