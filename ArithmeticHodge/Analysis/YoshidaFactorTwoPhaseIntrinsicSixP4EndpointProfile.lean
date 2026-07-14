import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile

noncomputable section

open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4LeadingReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixSchurExpansion
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation

/-!
# Profile meaning of the even `P₀/P₂/P₄` endpoint determinant

The six entries of the leading matrix are not treated as unrelated scalars.
They are exactly the endpoint phase form on the genuine three-mode even
profile.  Thus strict positivity of that profile form yields the determinant
gate by the structural `3 x 3` Sylvester criterion.
-/

/-- The intrinsic even profile through degree four. -/
def factorTwoIntrinsicEvenP024Profile
    (c0 c2 c4 : ℝ) : ℝ → ℝ :=
  factorTwoEvenStructuralLowProfile c0 c2 +
    factorTwoIntrinsicSixEvenTail c4

/-- Exact coordinate expansion of the complete endpoint phase on
`c₀ P₀ + c₂ P₂ + c₄ P₄`. -/
theorem factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic
    (c0 c2 c4 a : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        (0 : ℝ → ℝ) a 0 =
      symmetricQuadratic
        (factorTwoStructuralPhaseLow00 a)
        (factorTwoStructuralPhaseLow02 a)
        (factorTwoIntrinsicFourP45Cross04 a)
        (factorTwoStructuralPhaseLow22 a)
        (factorTwoIntrinsicFourP45Cross24 a)
        (factorTwoIntrinsicP4PhaseDiagonal a)
        c0 c2 c4 := by
  have hrContinuous : Continuous (factorTwoIntrinsicSixEvenTail c4) := by
    unfold factorTwoIntrinsicSixEvenTail
    exact continuous_const.mul continuous_factorTwoCenteredP4
  have hrEven : Function.Even (factorTwoIntrinsicSixEvenTail c4) := by
    intro x
    unfold factorTwoIntrinsicSixEvenTail
    rw [even_factorTwoCenteredP4]
  have hrCoefficients :
      centeredEvenP0Coefficient (factorTwoIntrinsicSixEvenTail c4) = 0 ∧
        centeredEvenP2Coefficient (factorTwoIntrinsicSixEvenTail c4) = 0 := by
    constructor
    · unfold centeredEvenP0Coefficient factorTwoIntrinsicSixEvenTail
      rw [intervalIntegral.integral_const_mul,
        integral_factorTwoCenteredP4]
      ring
    · unfold centeredEvenP2Coefficient factorTwoIntrinsicSixEvenTail
      rw [show (fun x : ℝ ↦
          c4 * factorTwoCenteredP4 x * centeredEvenP2 x) =
          fun x ↦ c4 *
            (factorTwoCenteredP4 x * centeredEvenP2 x) by
        funext x
        ring,
        intervalIntegral.integral_const_mul,
        integral_factorTwoCenteredP4_mul_centeredEvenP2]
      ring
  have hrLocal : LocallyLipschitzOn (Set.Icc (-1) 1)
      (factorTwoIntrinsicSixEvenTail c4) := by
    have hdiff : ContDiff ℝ 1 (factorTwoIntrinsicSixEvenTail c4) := by
      unfold factorTwoIntrinsicSixEvenTail factorTwoCenteredP4
      fun_prop
    exact hdiff.locallyLipschitz.locallyLipschitzOn
  have h := factorTwoEndpointChannelPhase_structuralLowTail
    (factorTwoIntrinsicSixEvenTail c4) (0 : ℝ → ℝ)
    hrContinuous hrEven hrCoefficients.1 hrCoefficients.2 hrLocal
    continuous_zero c0 c2 a 0
  have hOddZero : (0 : ℝ → ℝ) =
      factorTwoIntrinsicSixOddTail 0 0 0 := by
    funext x
    unfold factorTwoIntrinsicSixOddTail
      factorTwoOddStructuralLowProfile
    simp
  rw [hOddZero,
    factorTwoStructuralPhaseLowTail0_intrinsicSix c4 0 0 0 a 0,
    factorTwoStructuralPhaseLowTail2_intrinsicSix c4 0 0 0 a 0,
    factorTwoStructuralPhaseTail_intrinsicSix c4 0 0 0 a 0] at h
  unfold factorTwoIntrinsicEvenP024Profile
  rw [hOddZero, h]
  unfold factorTwoIntrinsicSixLowTail0 factorTwoIntrinsicSixLowTail2
    factorTwoIntrinsicSixTailQuadratic factorTwoIntrinsicOddPhaseQuadratic
  rw [factorTwoEndpointChannelPhase_P4_P5_expansion]
  unfold symmetricQuadratic
  ring

/-- A structural proof of strict positivity of the three-mode endpoint form
implies the endpoint determinant gate. -/
theorem factorTwoIntrinsicP024Determinant_pos_of_profile_pos
    (a : ℝ)
    (hpos : ∀ c0 c2 c4 : ℝ, c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 →
      0 < factorTwoEndpointChannelPhase
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        (0 : ℝ → ℝ) a 0) :
    0 < factorTwoIntrinsicP024Determinant a := by
  have hgates := leadingMinors_pos_of_symmetricQuadratic_pos
    (factorTwoStructuralPhaseLow00 a)
    (factorTwoStructuralPhaseLow02 a)
    (factorTwoIntrinsicFourP45Cross04 a)
    (factorTwoStructuralPhaseLow22 a)
    (factorTwoIntrinsicFourP45Cross24 a)
    (factorTwoIntrinsicP4PhaseDiagonal a)
    (fun c0 c2 c4 hne ↦ by
      rw [← factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic]
      exact hpos c0 c2 c4 hne)
  simpa only [factorTwoIntrinsicP024Determinant] using hgates.2.2

/-- Equivalent interface in terms of the sequential Schur leading scalar. -/
theorem factorTwoIntrinsicSixP4SchurLeading_pos_of_profile_pos
    (a : ℝ)
    (hpos : ∀ c0 c2 c4 : ℝ, c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 →
      0 < factorTwoEndpointChannelPhase
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        (0 : ℝ → ℝ) a 0) :
    0 < factorTwoIntrinsicSixP4SchurLeading a := by
  rw [factorTwoIntrinsicSixP4SchurLeading_eq_P024Determinant]
  exact factorTwoIntrinsicP024Determinant_pos_of_profile_pos a hpos

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
