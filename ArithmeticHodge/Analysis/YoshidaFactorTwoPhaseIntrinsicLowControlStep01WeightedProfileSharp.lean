import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01SharpClosure

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01WeightedProfileSharp

noncomputable section

open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01CauchyStructural
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Positive
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01SharpClosure
open YoshidaFactorTwoPhaseIntrinsicLowControlMonotonicity
open YoshidaFactorTwoPhaseIntrinsicLowControlsPositive
open YoshidaFactorTwoPhaseLowSchur

/-!
# Coupled residual for the intrinsic Step01 weighted profile

The remainder left after discarding the whole singular square is not
nonnegative.  Instead, multiply the exact Cauchy inequality by the positive
even determinant.  The determinant slope denominator then cancels, leaving
one genuine `2 x 2` quadratic in the odd coefficients.  No alternating
entry is estimated in this algebraic reduction.
-/

def factorTwoIntrinsicStep01CoupledResidual11 : ℝ :=
  factorTwoIntrinsicEvenDetCoefficient0 *
      (-2 * factorTwoCenteredSymmetricPerturbation centeredP1) +
    factorTwoIntrinsicEvenDetCoefficient1 *
      factorTwoIntrinsicOddPhaseLow11 1 -
    (factorTwoStructuralPhaseLow22 1 *
          factorTwoIntrinsicAlternating01 ^ 2 -
      2 * factorTwoStructuralPhaseLow02 1 *
          factorTwoIntrinsicAlternating01 * factorTwoIntrinsicAlternating21 +
      factorTwoStructuralPhaseLow00 1 *
          factorTwoIntrinsicAlternating21 ^ 2)

def factorTwoIntrinsicStep01CoupledResidual13 : ℝ :=
  factorTwoIntrinsicEvenDetCoefficient0 *
      (-2 * factorTwoCenteredSymmetricPerturbationBilinear
        centeredP1 centeredP3) +
    factorTwoIntrinsicEvenDetCoefficient1 *
      factorTwoIntrinsicOddPhaseLow13 1 -
    (factorTwoStructuralPhaseLow22 1 *
          factorTwoIntrinsicAlternating01 * factorTwoIntrinsicAlternating03 -
      factorTwoStructuralPhaseLow02 1 *
          (factorTwoIntrinsicAlternating01 * factorTwoIntrinsicAlternating23 +
            factorTwoIntrinsicAlternating03 * factorTwoIntrinsicAlternating21) +
      factorTwoStructuralPhaseLow00 1 *
          factorTwoIntrinsicAlternating21 * factorTwoIntrinsicAlternating23)

def factorTwoIntrinsicStep01CoupledResidual33 : ℝ :=
  factorTwoIntrinsicEvenDetCoefficient0 *
      (-2 * factorTwoCenteredSymmetricPerturbation centeredP3) +
    factorTwoIntrinsicEvenDetCoefficient1 *
      factorTwoIntrinsicOddPhaseLow33 1 -
    (factorTwoStructuralPhaseLow22 1 *
          factorTwoIntrinsicAlternating03 ^ 2 -
      2 * factorTwoStructuralPhaseLow02 1 *
          factorTwoIntrinsicAlternating03 * factorTwoIntrinsicAlternating23 +
      factorTwoStructuralPhaseLow00 1 *
          factorTwoIntrinsicAlternating23 ^ 2)

/-- Exact denominator-free residual identity.  The four alternating entries
remain in their full adjugate quadratic rather than four absolute-value
budgets. -/
theorem three_mul_factorTwoIntrinsicBoundaryControlStep01_eq_coupledResidual
    (c d : ℝ) :
    3 * factorTwoIntrinsicBoundaryControlStep01 c d =
      factorTwoIntrinsicStep01CoupledResidual11 * c ^ 2 +
        2 * factorTwoIntrinsicStep01CoupledResidual13 * c * d +
        factorTwoIntrinsicStep01CoupledResidual33 * d ^ 2 := by
  rw [three_mul_factorTwoIntrinsicBoundaryControlStep01]
  unfold factorTwoIntrinsicStep01CoupledResidual11
    factorTwoIntrinsicStep01CoupledResidual13
    factorTwoIntrinsicStep01CoupledResidual33
    factorTwoIntrinsicOddDirectionQuadratic
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicAdjugateCoefficient0
    factorTwoIntrinsicEvenAdjugateCoupling
    factorTwoIntrinsicAlternatingRow0
    factorTwoIntrinsicAlternatingRow2
  ring

/-- The three Sylvester gates of the coupled residual imply the exact
four-variable Step01 Cauchy inequality. -/
theorem factorTwoIntrinsicStep01ExactCauchy_of_coupledResidual_gates
    (h11 : 0 ≤ factorTwoIntrinsicStep01CoupledResidual11)
    (h33 : 0 ≤ factorTwoIntrinsicStep01CoupledResidual33)
    (hdet : factorTwoIntrinsicStep01CoupledResidual13 ^ 2 ≤
      factorTwoIntrinsicStep01CoupledResidual11 *
        factorTwoIntrinsicStep01CoupledResidual33) :
    FactorTwoIntrinsicStep01ExactCauchy := by
  have hresidual : ∀ c d : ℝ,
      0 ≤ factorTwoIntrinsicStep01CoupledResidual11 * c ^ 2 +
        2 * factorTwoIntrinsicStep01CoupledResidual13 * c * d +
        factorTwoIntrinsicStep01CoupledResidual33 * d ^ 2 :=
    (real_quadratic_pencil_nonneg_iff
      factorTwoIntrinsicStep01CoupledResidual11
      factorTwoIntrinsicStep01CoupledResidual33
      factorTwoIntrinsicStep01CoupledResidual13).mpr ⟨h11, h33, hdet⟩
  have hstep : ∀ c d : ℝ,
      0 ≤ factorTwoIntrinsicBoundaryControlStep01 c d := by
    intro c d
    have h := hresidual c d
    rw [← three_mul_factorTwoIntrinsicBoundaryControlStep01_eq_coupledResidual]
      at h
    linarith
  exact (factorTwoIntrinsicBoundaryControlStep01_nonneg_iff_exactCauchy
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.1
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.2).mp hstep

/-- Exact Cauchy plus positivity of the even endpoint recovers the full
weighted-profile nonnegativity.  This retains precisely the amount of the
five-square reserve needed to offset the signed smooth remainder. -/
theorem factorTwoIntrinsicStep01WeightedProfileForm_nonneg_of_exactCauchy
    (hCauchy : FactorTwoIntrinsicStep01ExactCauchy)
    (u v c d : ℝ) :
    0 ≤ factorTwoIntrinsicStep01WeightedProfileForm
      (factorTwoEvenStructuralLowProfile u v)
      (factorTwoOddStructuralLowProfile c d)
      factorTwoIntrinsicStep01Slope := by
  let E : ℝ := factorTwoIntrinsicEvenPlusQuadratic u v
  let B : ℝ := factorTwoIntrinsicStep01ExactOddBudget c d
  let J : ℝ := factorTwoIntrinsicAlternatingBilinear u v c d
  have hE : 0 ≤ E := by
    by_cases hne : u ≠ 0 ∨ v ≠ 0
    · dsimp only [E, factorTwoIntrinsicEvenPlusQuadratic]
      rw [factorTwoStructuralPhaseLow_endpoint_quadratic]
      simpa only [one_mul] using
        (factorTwoIntrinsicEven_plus_endpoint_structural_pos u v hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      simp [E, factorTwoIntrinsicEvenPlusQuadratic]
  have hB : 0 ≤ B := by
    have htest := hCauchy 1 0 c d
    have h00 := factorTwoIntrinsicEven_plus_endpoint_structural_gates.1
    dsimp only [E, B, J] at ⊢
    unfold factorTwoIntrinsicAlternatingBilinear
      factorTwoIntrinsicEvenPlusQuadratic at htest
    norm_num at htest
    nlinarith [sq_nonneg (factorTwoIntrinsicAlternatingRow0 c d)]
  have hJ := hCauchy u v c d
  change J ^ 2 ≤ E * B at hJ
  have hpencil : ∀ r s : ℝ,
      0 ≤ E * r ^ 2 + 2 * (J / 2) * r * s + (B / 4) * s ^ 2 := by
    apply (real_quadratic_pencil_nonneg_iff E (B / 4) (J / 2)).mpr
    constructor
    · exact hE
    constructor
    · positivity
    · nlinarith
  have hone := hpencil 1 1
  rw [factorTwoIntrinsicStep01WeightedProfileForm_eq_intrinsic]
  dsimp only [E, B, J] at hone ⊢
  nlinarith

theorem factorTwoIntrinsicStep01WeightedProfileForm_nonneg_of_coupledResidual_gates
    (h11 : 0 ≤ factorTwoIntrinsicStep01CoupledResidual11)
    (h33 : 0 ≤ factorTwoIntrinsicStep01CoupledResidual33)
    (hdet : factorTwoIntrinsicStep01CoupledResidual13 ^ 2 ≤
      factorTwoIntrinsicStep01CoupledResidual11 *
        factorTwoIntrinsicStep01CoupledResidual33) :
    ∀ u v c d : ℝ,
      0 ≤ factorTwoIntrinsicStep01WeightedProfileForm
        (factorTwoEvenStructuralLowProfile u v)
        (factorTwoOddStructuralLowProfile c d)
        factorTwoIntrinsicStep01Slope := by
  intro u v c d
  exact factorTwoIntrinsicStep01WeightedProfileForm_nonneg_of_exactCauchy
    (factorTwoIntrinsicStep01ExactCauchy_of_coupledResidual_gates
      h11 h33 hdet) u v c d

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01WeightedProfileSharp
