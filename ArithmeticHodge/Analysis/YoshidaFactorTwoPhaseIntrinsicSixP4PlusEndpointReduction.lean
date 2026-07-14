import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointReduction

noncomputable section

open ThreeByThreeConvexPencil
open ThreeByThreeRankOneSchur
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural lower form at the positive `P₀/P₂/P₄` endpoint

The proved positive-endpoint lower matrix on `P₀/P₂` is extended by the
exact `P₄` column and diagonal.  Consequently the difference from the actual
three-mode endpoint form is still exactly the old two-mode Loewner defect.
The only remaining analytic input is one strict adjugate inequality for that
new column; everything in this module is structural quadratic-form algebra.
-/

def factorTwoIntrinsicSixP4PlusLower00 : ℝ :=
  evenStructuralPlusKernel00

def factorTwoIntrinsicSixP4PlusLower02 : ℝ :=
  evenStructuralPlusKernel02

def factorTwoIntrinsicSixP4PlusLower04 : ℝ :=
  factorTwoIntrinsicFourP45Cross04 1

def factorTwoIntrinsicSixP4PlusLower22 : ℝ :=
  evenStructuralPlusKernel22

def factorTwoIntrinsicSixP4PlusLower24 : ℝ :=
  factorTwoIntrinsicFourP45Cross24 1

def factorTwoIntrinsicSixP4PlusLower44 : ℝ :=
  factorTwoIntrinsicP4PhaseDiagonal 1

/-- The positive-endpoint lower quadratic on the intrinsic even
`P₀/P₂/P₄` coordinates. -/
def factorTwoIntrinsicSixP4PlusLowerQuadratic
    (c0 c2 c4 : ℝ) : ℝ :=
  symmetricQuadratic
    factorTwoIntrinsicSixP4PlusLower00
    factorTwoIntrinsicSixP4PlusLower02
    factorTwoIntrinsicSixP4PlusLower04
    factorTwoIntrinsicSixP4PlusLower22
    factorTwoIntrinsicSixP4PlusLower24
    factorTwoIntrinsicSixP4PlusLower44
    c0 c2 c4

/-- The determinant of the positive-endpoint lower matrix. -/
def factorTwoIntrinsicSixP4PlusLowerDeterminant : ℝ :=
  symmetricDeterminant
    factorTwoIntrinsicSixP4PlusLower00
    factorTwoIntrinsicSixP4PlusLower02
    factorTwoIntrinsicSixP4PlusLower04
    factorTwoIntrinsicSixP4PlusLower22
    factorTwoIntrinsicSixP4PlusLower24
    factorTwoIntrinsicSixP4PlusLower44

/-- Replacing only the `P₀/P₂` block by its established structural lower
matrix gives a Loewner lower form for the complete positive endpoint. -/
theorem factorTwoIntrinsicSixP4PlusLowerQuadratic_le_profile
    (c0 c2 c4 : ℝ) :
    factorTwoIntrinsicSixP4PlusLowerQuadratic c0 c2 c4 ≤
      factorTwoEndpointChannelPhase
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        (0 : ℝ → ℝ) 1 0 := by
  have hlow := evenStructuralPlusKernel_quadratic_le_endpoint c0 c2
  have hphaseLow :
      factorTwoStructuralPhaseLow00 1 * c0 ^ 2 +
          2 * factorTwoStructuralPhaseLow02 1 * c0 * c2 +
          factorTwoStructuralPhaseLow22 1 * c2 ^ 2 =
        yoshidaEndpointOddCleanQuadratic
            (factorTwoEvenStructuralLowProfile c0 c2) +
          factorTwoCenteredSymmetricPerturbation
            (factorTwoEvenStructuralLowProfile c0 c2) := by
    simpa only [one_mul] using
      factorTwoStructuralPhaseLow_endpoint_quadratic 1 c0 c2
  rw [← hphaseLow] at hlow
  rw [factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic]
  unfold factorTwoIntrinsicSixP4PlusLowerQuadratic symmetricQuadratic
    factorTwoIntrinsicSixP4PlusLower00
    factorTwoIntrinsicSixP4PlusLower02
    factorTwoIntrinsicSixP4PlusLower04
    factorTwoIntrinsicSixP4PlusLower22
    factorTwoIntrinsicSixP4PlusLower24
    factorTwoIntrinsicSixP4PlusLower44
  linarith

/-- The strict column Schur gate is exactly positivity of the determinant of
the lower `P₀/P₂/P₄` matrix. -/
theorem factorTwoIntrinsicSixP4PlusLowerDeterminant_pos
    (hSchur :
      factorTwoIntrinsicSixP4PlusLower22 *
            factorTwoIntrinsicSixP4PlusLower04 ^ 2 -
          2 * factorTwoIntrinsicSixP4PlusLower02 *
            factorTwoIntrinsicSixP4PlusLower04 *
            factorTwoIntrinsicSixP4PlusLower24 +
          factorTwoIntrinsicSixP4PlusLower00 *
            factorTwoIntrinsicSixP4PlusLower24 ^ 2 <
        leadingMinorTwo
            factorTwoIntrinsicSixP4PlusLower00
            factorTwoIntrinsicSixP4PlusLower02
            factorTwoIntrinsicSixP4PlusLower22 *
          factorTwoIntrinsicSixP4PlusLower44) :
    0 < factorTwoIntrinsicSixP4PlusLowerDeterminant := by
  unfold factorTwoIntrinsicSixP4PlusLowerDeterminant
    symmetricDeterminant
  unfold leadingMinorTwo at hSchur
  nlinarith

/-- The single strict adjugate/Schur inequality for the exact `P₄` column
closes the positive endpoint leading gate. -/
theorem factorTwoIntrinsicSixP4SchurLeading_one_pos_of_plus_lower_schur
    (hSchur :
      factorTwoIntrinsicSixP4PlusLower22 *
            factorTwoIntrinsicSixP4PlusLower04 ^ 2 -
          2 * factorTwoIntrinsicSixP4PlusLower02 *
            factorTwoIntrinsicSixP4PlusLower04 *
            factorTwoIntrinsicSixP4PlusLower24 +
          factorTwoIntrinsicSixP4PlusLower00 *
            factorTwoIntrinsicSixP4PlusLower24 ^ 2 <
        leadingMinorTwo
            factorTwoIntrinsicSixP4PlusLower00
            factorTwoIntrinsicSixP4PlusLower02
            factorTwoIntrinsicSixP4PlusLower22 *
          factorTwoIntrinsicSixP4PlusLower44) :
    0 < factorTwoIntrinsicSixP4SchurLeading 1 := by
  apply factorTwoIntrinsicSixP4SchurLeading_pos_of_profile_pos
  intro c0 c2 c4 hne
  have hLower : 0 <
      factorTwoIntrinsicSixP4PlusLowerQuadratic c0 c2 c4 := by
    exact symmetricQuadratic_pos
      factorTwoIntrinsicSixP4PlusLower00
      factorTwoIntrinsicSixP4PlusLower02
      factorTwoIntrinsicSixP4PlusLower04
      factorTwoIntrinsicSixP4PlusLower22
      factorTwoIntrinsicSixP4PlusLower24
      factorTwoIntrinsicSixP4PlusLower44
      (by
        simpa only [factorTwoIntrinsicSixP4PlusLower00] using
          evenStructuralPlusKernel_principal_minors_pos.1)
      (by
        simpa only [factorTwoIntrinsicSixP4PlusLower00,
          factorTwoIntrinsicSixP4PlusLower02,
          factorTwoIntrinsicSixP4PlusLower22] using
          evenStructuralPlusKernel_principal_minors_pos.2)
      (factorTwoIntrinsicSixP4PlusLowerDeterminant_pos hSchur)
      c0 c2 c4 hne
  exact hLower.trans_le
    (factorTwoIntrinsicSixP4PlusLowerQuadratic_le_profile c0 c2 c4)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointReduction
