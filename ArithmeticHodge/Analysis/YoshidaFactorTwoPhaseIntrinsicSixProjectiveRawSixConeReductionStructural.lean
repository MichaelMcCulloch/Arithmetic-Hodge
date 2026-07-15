import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4UniformStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourConeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientFrontierStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixFactorStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixConeReductionStructural

noncomputable section

open Polynomial
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4UniformStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourConeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixCoefficientFrontierStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixFactorStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Raw-six cone reduction for the final projective gate

The exact fraction-free factorization makes the final gap positive pointwise
from the already-positive low determinant and the raw-six coefficient cone.
Thus no separate coefficient expansion of the much larger gap polynomial is
needed.
-/

/-- Positivity of the raw-six determinant cone transfers through the exact
factorization to the final `P₅` gap on the nonnegative half-line. -/
theorem factorTwoIntrinsicSixProjectiveP5Gap_eval_pos_of_raw_cone
    (x : ℝ) (hx : 0 ≤ x)
    (hRawSix : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial) :
    0 < factorTwoIntrinsicSixProjectiveP5GapPolynomial.eval x := by
  rw [factorTwoIntrinsicSixProjectiveP5GapPolynomial_factor,
    eval_mul, eval_pow,
    eval_factorTwoIntrinsicSixProjectiveRawLowDetPolynomial]
  exact mul_pos
    (pow_pos (factorTwoIntrinsicSixProjectiveLowDet_pos x hx) 3)
    (eval_pos_of_mem_strictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial hRawSix x hx)

/-- The unconditional raw-four cone, any raw-five cone proof, and any
raw-six cone proof close all four six-mode projective Schur gates. -/
theorem factorTwoIntrinsicSixProjectiveXGates_of_raw_cones
    (x : ℝ) (hx : 0 ≤ x)
    (hRawFive : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial)
    (hRawSix : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial) :
    FactorTwoIntrinsicSixProjectiveXGates x := by
  refine ⟨factorTwoIntrinsicSixProjectiveP4Pivot_pos x hx,
    factorTwoIntrinsicSixProjectiveBaseMinorTwoX_pos x hx,
    factorTwoIntrinsicSixProjectiveBaseDetX_pos_of_raw_cone x hx hRawFive,
    ?_⟩
  have hgap :=
    factorTwoIntrinsicSixProjectiveP5Gap_eval_pos_of_raw_cone x hx hRawSix
  rw [eval_factorTwoIntrinsicSixProjectiveP5GapPolynomial] at hgap
  linarith

/-- Exact scalar frontier: after a raw-five cone proof, the seven displayed
raw-six coefficient signs close every projective gate. -/
theorem factorTwoIntrinsicSixProjectiveXGates_of_rawSix_coefficients
    (x : ℝ) (hx : 0 ≤ x)
    (hRawFive : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial)
    (hSigns :
      0 < factorTwoIntrinsicSixProjectiveRawSixCoefficient 0 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 1 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 2 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 3 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 4 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 5 ∧
      0 ≤ factorTwoIntrinsicSixProjectiveRawSixCoefficient 6) :
    FactorTwoIntrinsicSixProjectiveXGates x := by
  exact factorTwoIntrinsicSixProjectiveXGates_of_raw_cones x hx hRawFive
    (factorTwoIntrinsicSixProjectiveRawDeterminant_mem_cone_iff_coefficients.2
      hSigns)

/-- The same finite cone data closes the complete intrinsic six-mode phase
at the rational projective parametrization. -/
theorem factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_raw_cones
    (c0 c2 c4 c1 c3 c5 t x : ℝ) (hx : x = t ^ 2)
    (hRawFive : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawMinorFivePolynomial)
    (hRawSix : StrictNonnegativeCoefficientCone
      factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4)
      (factorTwoIntrinsicSixOddTail c1 c3 c5)
      ((1 - x) / (1 + x)) (2 * t / (1 + x)) := by
  have hxNonneg : 0 ≤ x := by
    rw [hx]
    positivity
  exact factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_projective_x_gates
    c0 c2 c4 c1 c3 c5 t x hx
    (factorTwoIntrinsicSixProjectiveXGates_of_raw_cones
      x hxNonneg hRawFive hRawSix)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixConeReductionStructural
