import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingCorrelations
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedAlternatingModelsStructural

noncomputable section

open MeasureTheory Real Set
open CenteredOddOneThreeEnergy
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelStructural
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicSixP5AlternatingCorrelations
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseLegendreFourFiveStructural

/-!
# Public alternating models for the unbalanced six-mode split

The earlier `P4/P1` and `P4/P3` enclosure modules keep their exact
correlation polynomials and kernel decompositions private.  The unbalanced
Schur argument needs those decompositions before taking separate interval
bounds, so this file exposes just those exact identities.  The three public
`P5` identities are also collected below for convenient simultaneous use.
-/

/-- Scalar polynomial left after factoring `t * (2 - t)` from the ordered
`P4/P1` correlation difference. -/
def alternatingQ41 (t : ℝ) : ℝ :=
  -1 + 4 * t - (23 / 6 : ℝ) * t ^ 2 + (7 / 12 : ℝ) * t ^ 3 +
    (7 / 24 : ℝ) * t ^ 4

/-- Scalar polynomial left after factoring `t * (2 - t)` from the ordered
`P4/P3` correlation difference. -/
def alternatingQ43 (t : ℝ) : ℝ :=
  -1 + (3 / 2 : ℝ) * t + (3 / 4 : ℝ) * t ^ 2 -
    (7 / 8 : ℝ) * t ^ 3 - (7 / 16 : ℝ) * t ^ 4 +
    (5 / 32 : ℝ) * t ^ 5 + (5 / 64 : ℝ) * t ^ 6

/-- Exact ordered-correlation difference for the `P4/P1` entry. -/
theorem crossDifference_p4_p1
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation centeredP1 factorTwoCenteredP4 t -
        factorTwoCenteredCrossCorrelation factorTwoCenteredP4 centeredP1 t =
      intrinsicAlternatingCorrelation alternatingQ41 t := by
  unfold factorTwoCenteredCrossCorrelation centeredP1 factorTwoCenteredP4
    intrinsicAlternatingCorrelation alternatingQ41
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  simp only [smul_eq_mul]
  ring

/-- Exact ordered-correlation difference for the `P4/P3` entry. -/
theorem crossDifference_p4_p3
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 2) :
    factorTwoCenteredCrossCorrelation centeredP3 factorTwoCenteredP4 t -
        factorTwoCenteredCrossCorrelation factorTwoCenteredP4 centeredP3 t =
      intrinsicAlternatingCorrelation alternatingQ43 t := by
  unfold factorTwoCenteredCrossCorrelation centeredP3 factorTwoCenteredP4
    intrinsicAlternatingCorrelation alternatingQ43
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  repeat rw [intervalIntegral.integral_const]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  repeat rw [integral_id]
  rw [intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  have htwo :
      (∫ x : ℝ in -1..1 - t, t * x ^ 2 * (45 / 4)) =
        (45 * t / 4) * (((1 - t) ^ 3 - (-1 : ℝ) ^ 3) / 3) := by
    rw [show (fun x : ℝ ↦ t * x ^ 2 * (45 / 4)) =
        fun x ↦ (45 * t / 4) * x ^ 2 by funext x; ring,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  have hfour :
      (∫ x : ℝ in -1..1 - t, t * x ^ 4 * 45) =
        (45 * t) * (((1 - t) ^ 5 - (-1 : ℝ) ^ 5) / 5) := by
    rw [show (fun x : ℝ ↦ t * x ^ 4 * 45) =
        fun x ↦ (45 * t) * x ^ 4 by funext x; ring,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [htwo, hfour]
  simp only [smul_eq_mul]
  ring

/-- Structural kernel decomposition of the `P4/P1` alternating entry. -/
theorem factorTwoIntrinsicFourP45Cross41_eq_structuralModel :
    factorTwoIntrinsicFourP45Cross41 =
      intrinsicAlternatingRegularError alternatingQ41 +
        intrinsicAlternatingArchModel alternatingQ41 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ41
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoIntrinsicFourP45Cross41
  exact factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
    factorTwoCenteredP4 centeredP1 alternatingQ41
    (by unfold alternatingQ41; fun_prop) crossDifference_p4_p1

/-- Structural kernel decomposition of the `P4/P3` alternating entry. -/
theorem factorTwoIntrinsicFourP45Cross43_eq_structuralModel :
    factorTwoIntrinsicFourP45Cross43 =
      intrinsicAlternatingRegularError alternatingQ43 +
        intrinsicAlternatingArchModel alternatingQ43 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ43
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoIntrinsicFourP45Cross43
  exact factorTwoCenteredAlternatingCoupling_eq_regularError_add_archModel
    factorTwoCenteredP4 centeredP3 alternatingQ43
    (by unfold alternatingQ43; fun_prop) crossDifference_p4_p3

/-- The three existing `P5` alternating decompositions, packaged as one
structural input for the unbalanced Schur argument. -/
theorem factorTwoIntrinsicSixP5Alternating_eq_structuralModels :
    (factorTwoIntrinsicFourP45Cross05 =
      intrinsicAlternatingRegularError alternatingQ05 +
        intrinsicAlternatingArchModel alternatingQ05 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ05
          (factorTwoPrimeShift / yoshidaEndpointA)) ∧
    (factorTwoIntrinsicFourP45Cross25 =
      intrinsicAlternatingRegularError alternatingQ25 +
        intrinsicAlternatingArchModel alternatingQ25 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ25
          (factorTwoPrimeShift / yoshidaEndpointA)) ∧
    (factorTwoIntrinsicSixAlternating45 =
      intrinsicAlternatingRegularError alternatingQ45 +
        intrinsicAlternatingArchModel alternatingQ45 -
      (Real.log 3 / Real.sqrt 3) *
        intrinsicAlternatingCorrelation alternatingQ45
          (factorTwoPrimeShift / yoshidaEndpointA)) := by
  exact ⟨factorTwoIntrinsicFourP45Cross05_eq_structuralModel,
    factorTwoIntrinsicFourP45Cross25_eq_structuralModel,
    factorTwoIntrinsicSixAlternating45_eq_structuralModel⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedAlternatingModelsStructural
