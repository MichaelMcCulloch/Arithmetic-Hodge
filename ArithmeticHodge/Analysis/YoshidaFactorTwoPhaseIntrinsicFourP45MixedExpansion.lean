import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEvenCleanPolarizationBridge
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45Reduction

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseEvenCleanPolarizationBridge
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45Reduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation

/-!
# Exact mixed coordinates for the first six intrinsic modes

The four same-parity entries retain the complete clean-plus-symmetric phase
pairing.  The four opposite-parity entries retain the alternating coupling.
Together they give the exact `4 x 2` coordinate expansion of the single mixed
Schur scalar.
-/

/-- The complete same-parity `P₀`--`P₄` cross entry. -/
def factorTwoIntrinsicFourP45Cross04 (a : ℝ) : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 +
    a * factorTwoCenteredSymmetricPerturbationBilinear
      centeredEvenP0 factorTwoCenteredP4

/-- The complete same-parity `P₂`--`P₄` cross entry. -/
def factorTwoIntrinsicFourP45Cross24 (a : ℝ) : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 +
    a * factorTwoCenteredSymmetricPerturbationBilinear
      centeredEvenP2 factorTwoCenteredP4

/-- The complete same-parity `P₁`--`P₅` cross entry. -/
def factorTwoIntrinsicFourP45Cross15 (a : ℝ) : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredP1 factorTwoCenteredP5 +
    a * factorTwoCenteredSymmetricPerturbationBilinear
      centeredP1 factorTwoCenteredP5

/-- The complete same-parity `P₃`--`P₅` cross entry. -/
def factorTwoIntrinsicFourP45Cross35 (a : ℝ) : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredP3 factorTwoCenteredP5 +
    a * factorTwoCenteredSymmetricPerturbationBilinear
      centeredP3 factorTwoCenteredP5

/-- The alternating `P₀`--`P₅` cross entry. -/
def factorTwoIntrinsicFourP45Cross05 : ℝ :=
  factorTwoCenteredAlternatingCoupling centeredEvenP0 factorTwoCenteredP5

/-- The alternating `P₂`--`P₅` cross entry. -/
def factorTwoIntrinsicFourP45Cross25 : ℝ :=
  factorTwoCenteredAlternatingCoupling centeredEvenP2 factorTwoCenteredP5

/-- The alternating `P₄`--`P₁` cross entry. -/
def factorTwoIntrinsicFourP45Cross41 : ℝ :=
  factorTwoCenteredAlternatingCoupling factorTwoCenteredP4 centeredP1

/-- The alternating `P₄`--`P₃` cross entry. -/
def factorTwoIntrinsicFourP45Cross43 : ℝ :=
  factorTwoCenteredAlternatingCoupling factorTwoCenteredP4 centeredP3

private theorem centeredEvenP2Coefficient_const_mul_factorTwoCenteredP4
    (c : ℝ) :
    centeredEvenP2Coefficient (fun x ↦ c * factorTwoCenteredP4 x) = 0 := by
  unfold centeredEvenP2Coefficient
  rw [show (fun x : ℝ ↦
      c * factorTwoCenteredP4 x * centeredEvenP2 x) =
      fun x ↦ c * (factorTwoCenteredP4 x * centeredEvenP2 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    integral_factorTwoCenteredP4_mul_centeredEvenP2]
  ring

private theorem centeredOddCoefficients_const_mul_factorTwoCenteredP5
    (c : ℝ) :
    centeredOddP1Coefficient (fun x ↦ c * factorTwoCenteredP5 x) = 0 ∧
      centeredOddP3Coefficient (fun x ↦ c * factorTwoCenteredP5 x) = 0 := by
  constructor
  · unfold centeredOddP1Coefficient
    rw [show (fun x : ℝ ↦ c * factorTwoCenteredP5 x * centeredP1 x) =
        fun x ↦ c * (factorTwoCenteredP5 x * centeredP1 x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP5_mul_centeredP1]
    ring
  · unfold centeredOddP3Coefficient
    rw [show (fun x : ℝ ↦ c * factorTwoCenteredP5 x * centeredP3 x) =
        fun x ↦ c * (factorTwoCenteredP5 x * centeredP3 x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP5_mul_centeredP3]
    ring

private theorem locallyLipschitzOn_const_mul_factorTwoCenteredP4
    (c : ℝ) :
    LocallyLipschitzOn (Icc (-1) 1)
      (fun x ↦ c * factorTwoCenteredP4 x) := by
  have h : ContDiff ℝ 1 (fun x ↦ c * factorTwoCenteredP4 x) := by
    unfold factorTwoCenteredP4
    fun_prop
  exact h.locallyLipschitz.locallyLipschitzOn

private theorem locallyLipschitzOn_const_mul_factorTwoCenteredP5
    (c : ℝ) :
    LocallyLipschitzOn (Icc (-1) 1)
      (fun x ↦ c * factorTwoCenteredP5 x) := by
  have h : ContDiff ℝ 1 (fun x ↦ c * factorTwoCenteredP5 x) := by
    unfold factorTwoCenteredP5
    fun_prop
  exact h.locallyLipschitz.locallyLipschitzOn

/-- Exact intact `4 x 2` coordinate expansion of the mixed Schur scalar. -/
theorem factorTwoIntrinsicFourP45Mixed_eq_cross_entries
    (c0 c2 c1 c3 c4 c5 a b : ℝ) :
    factorTwoIntrinsicFourP45Mixed c0 c2 c1 c3 c4 c5 a b =
      c4 *
          (c0 * factorTwoIntrinsicFourP45Cross04 a +
            c2 * factorTwoIntrinsicFourP45Cross24 a) +
        c5 *
          (c1 * factorTwoIntrinsicFourP45Cross15 a +
            c3 * factorTwoIntrinsicFourP45Cross35 a) +
        (b / 2) *
          (c5 *
              (c0 * factorTwoIntrinsicFourP45Cross05 +
                c2 * factorTwoIntrinsicFourP45Cross25) +
            c4 *
              (c1 * factorTwoIntrinsicFourP45Cross41 +
                c3 * factorTwoIntrinsicFourP45Cross43)) := by
  have heContinuous : Continuous (fun x ↦ c4 * factorTwoCenteredP4 x) :=
    continuous_const.mul continuous_factorTwoCenteredP4
  have hoContinuous : Continuous (fun x ↦ c5 * factorTwoCenteredP5 x) :=
    continuous_const.mul continuous_factorTwoCenteredP5
  have heClean :=
    factorTwoCenteredCleanPolarization_evenStructuralLow_tail_eq_bilinear
      (fun x ↦ c4 * factorTwoCenteredP4 x) heContinuous
      (centeredEvenP2Coefficient_const_mul_factorTwoCenteredP4 c4)
      (locallyLipschitzOn_const_mul_factorTwoCenteredP4 c4) c0 c2
  have hoClean :=
    factorTwoCenteredCleanPolarization_oddStructuralLow_tail_eq_bilinear
      (fun x ↦ c5 * factorTwoCenteredP5 x) hoContinuous
      (locallyLipschitzOn_const_mul_factorTwoCenteredP5 c5)
      (centeredOddCoefficients_const_mul_factorTwoCenteredP5 c5).1
      (centeredOddCoefficients_const_mul_factorTwoCenteredP5 c5).2 c1 c3
  have heLowEq : factorTwoEvenStructuralLowProfile c0 c2 =
      yoshidaEndpointEvenLowProfile c0 c2 := by
    funext x
    unfold factorTwoEvenStructuralLowProfile yoshidaEndpointEvenLowProfile
      centeredEvenP0
    ring
  have heCleanEntry0 :
      yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 =
        ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailRepresenter0 x * factorTwoCenteredP4 x := by
    have h := yoshidaEndpointEvenCleanBilinear_low_tail_eq_representers
      factorTwoCenteredP4 continuous_factorTwoCenteredP4
      even_factorTwoCenteredP4
      factorTwoCenteredP4_intrinsic_coefficients_zero.1
      factorTwoCenteredP4_intrinsic_coefficients_zero.2 1 0
    have hprofile : yoshidaEndpointEvenLowProfile 1 0 = centeredEvenP0 := by
      funext x
      unfold yoshidaEndpointEvenLowProfile centeredEvenP0
      ring
    rw [hprofile] at h
    simpa using h
  have heCleanEntry2 :
      yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 =
        ∫ x : ℝ in -1..1,
          yoshidaEndpointEvenTailRepresenter2 x * factorTwoCenteredP4 x := by
    have h := yoshidaEndpointEvenCleanBilinear_low_tail_eq_representers
      factorTwoCenteredP4 continuous_factorTwoCenteredP4
      even_factorTwoCenteredP4
      factorTwoCenteredP4_intrinsic_coefficients_zero.1
      factorTwoCenteredP4_intrinsic_coefficients_zero.2 0 1
    have hprofile : yoshidaEndpointEvenLowProfile 0 1 = centeredEvenP2 := by
      funext x
      unfold yoshidaEndpointEvenLowProfile
      ring
    rw [hprofile] at h
    simpa using h
  have heCleanBase :
      yoshidaEndpointEvenCleanBilinear
          (factorTwoEvenStructuralLowProfile c0 c2) factorTwoCenteredP4 =
        c0 * yoshidaEndpointEvenCleanBilinear
            centeredEvenP0 factorTwoCenteredP4 +
          c2 * yoshidaEndpointEvenCleanBilinear
            centeredEvenP2 factorTwoCenteredP4 := by
    rw [heLowEq,
      yoshidaEndpointEvenCleanBilinear_low_tail_eq_representers
        factorTwoCenteredP4 continuous_factorTwoCenteredP4
        even_factorTwoCenteredP4
        factorTwoCenteredP4_intrinsic_coefficients_zero.1
        factorTwoCenteredP4_intrinsic_coefficients_zero.2]
    rw [← heCleanEntry0, ← heCleanEntry2]
  have heCleanExpanded :
      factorTwoCenteredCleanPolarization
          (factorTwoEvenStructuralLowProfile c0 c2)
          (fun x ↦ c4 * factorTwoCenteredP4 x) =
        c4 *
          (c0 * yoshidaEndpointEvenCleanBilinear
              centeredEvenP0 factorTwoCenteredP4 +
            c2 * yoshidaEndpointEvenCleanBilinear
              centeredEvenP2 factorTwoCenteredP4) := by
    rw [heClean,
      yoshidaEndpointEvenCleanBilinear_const_mul_right,
      heCleanBase]
  have hoCleanBase := yoshidaEndpointEvenCleanBilinear_oddStructuralLow
    c1 c3 factorTwoCenteredP5 continuous_factorTwoCenteredP5
    factorTwoCenteredP5_intrinsic_coefficients_zero.1
    factorTwoCenteredP5_intrinsic_coefficients_zero.2
  have hoCleanExpanded :
      factorTwoCenteredCleanPolarization
          (factorTwoOddStructuralLowProfile c1 c3)
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c5 *
          (c1 * yoshidaEndpointEvenCleanBilinear
              centeredP1 factorTwoCenteredP5 +
            c3 * yoshidaEndpointEvenCleanBilinear
              centeredP3 factorTwoCenteredP5) := by
    rw [hoClean,
      yoshidaEndpointEvenCleanBilinear_const_mul_right,
      hoCleanBase]
  have heSymEntry0 :
      factorTwoCenteredSymmetricPerturbationBilinear centeredEvenP0
          (fun x ↦ c4 * factorTwoCenteredP4 x) =
        c4 * factorTwoCenteredSymmetricPerturbationBilinear
          centeredEvenP0 factorTwoCenteredP4 := by
    simpa [smul_eq_mul] using
      (factorTwoCenteredSymmetricPerturbationBilinear_smul_smul
        1 c4 centeredEvenP0 factorTwoCenteredP4)
  have heSymEntry2 :
      factorTwoCenteredSymmetricPerturbationBilinear centeredEvenP2
          (fun x ↦ c4 * factorTwoCenteredP4 x) =
        c4 * factorTwoCenteredSymmetricPerturbationBilinear
          centeredEvenP2 factorTwoCenteredP4 := by
    simpa [smul_eq_mul] using
      (factorTwoCenteredSymmetricPerturbationBilinear_smul_smul
        1 c4 centeredEvenP2 factorTwoCenteredP4)
  have heSymExpanded :
      factorTwoCenteredSymmetricPerturbationBilinear
          (factorTwoEvenStructuralLowProfile c0 c2)
          (fun x ↦ c4 * factorTwoCenteredP4 x) =
        c4 *
          (c0 * factorTwoCenteredSymmetricPerturbationBilinear
              centeredEvenP0 factorTwoCenteredP4 +
            c2 * factorTwoCenteredSymmetricPerturbationBilinear
              centeredEvenP2 factorTwoCenteredP4) := by
    rw [factorTwoCenteredSymmetricPerturbationBilinear_structuralLow
      c0 c2 (fun x ↦ c4 * factorTwoCenteredP4 x) heContinuous,
      heSymEntry0, heSymEntry2]
    ring
  have hoSymEntry1 :
      factorTwoCenteredSymmetricPerturbationBilinear centeredP1
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c5 * factorTwoCenteredSymmetricPerturbationBilinear
          centeredP1 factorTwoCenteredP5 := by
    simpa [smul_eq_mul] using
      (factorTwoCenteredSymmetricPerturbationBilinear_smul_smul
        1 c5 centeredP1 factorTwoCenteredP5)
  have hoSymEntry3 :
      factorTwoCenteredSymmetricPerturbationBilinear centeredP3
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c5 * factorTwoCenteredSymmetricPerturbationBilinear
          centeredP3 factorTwoCenteredP5 := by
    simpa [smul_eq_mul] using
      (factorTwoCenteredSymmetricPerturbationBilinear_smul_smul
        1 c5 centeredP3 factorTwoCenteredP5)
  have hoSymExpanded :
      factorTwoCenteredSymmetricPerturbationBilinear
          (factorTwoOddStructuralLowProfile c1 c3)
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c5 *
          (c1 * factorTwoCenteredSymmetricPerturbationBilinear
              centeredP1 factorTwoCenteredP5 +
            c3 * factorTwoCenteredSymmetricPerturbationBilinear
              centeredP3 factorTwoCenteredP5) := by
    rw [factorTwoCenteredSymmetricPerturbationBilinear_oddStructuralLow
      c1 c3 (fun x ↦ c5 * factorTwoCenteredP5 x) hoContinuous,
      hoSymEntry1, hoSymEntry3]
    ring
  have heAltEntry0 :
      factorTwoCenteredAlternatingCoupling centeredEvenP0
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c5 * factorTwoCenteredAlternatingCoupling
          centeredEvenP0 factorTwoCenteredP5 := by
    simpa [smul_eq_mul] using
      (factorTwoCenteredAlternatingCoupling_smul_right
        c5 centeredEvenP0 factorTwoCenteredP5)
  have heAltEntry2 :
      factorTwoCenteredAlternatingCoupling centeredEvenP2
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c5 * factorTwoCenteredAlternatingCoupling
          centeredEvenP2 factorTwoCenteredP5 := by
    simpa [smul_eq_mul] using
      (factorTwoCenteredAlternatingCoupling_smul_right
        c5 centeredEvenP2 factorTwoCenteredP5)
  have heAltExpanded :
      factorTwoCenteredAlternatingCoupling
          (factorTwoEvenStructuralLowProfile c0 c2)
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c5 *
          (c0 * factorTwoCenteredAlternatingCoupling
              centeredEvenP0 factorTwoCenteredP5 +
            c2 * factorTwoCenteredAlternatingCoupling
              centeredEvenP2 factorTwoCenteredP5) := by
    rw [factorTwoCenteredAlternatingCoupling_structuralLow
      c0 c2 (fun x ↦ c5 * factorTwoCenteredP5 x) hoContinuous,
      heAltEntry0, heAltEntry2]
    ring
  have hoAltEntry1 :
      factorTwoCenteredAlternatingCoupling
          (fun x ↦ c4 * factorTwoCenteredP4 x) centeredP1 =
        c4 * factorTwoCenteredAlternatingCoupling
          factorTwoCenteredP4 centeredP1 := by
    simpa [smul_eq_mul] using
      (factorTwoCenteredAlternatingCoupling_smul_left
        c4 factorTwoCenteredP4 centeredP1)
  have hoAltEntry3 :
      factorTwoCenteredAlternatingCoupling
          (fun x ↦ c4 * factorTwoCenteredP4 x) centeredP3 =
        c4 * factorTwoCenteredAlternatingCoupling
          factorTwoCenteredP4 centeredP3 := by
    simpa [smul_eq_mul] using
      (factorTwoCenteredAlternatingCoupling_smul_left
        c4 factorTwoCenteredP4 centeredP3)
  have hoAltExpanded :
      factorTwoCenteredAlternatingCoupling
          (fun x ↦ c4 * factorTwoCenteredP4 x)
          (factorTwoOddStructuralLowProfile c1 c3) =
        c4 *
          (c1 * factorTwoCenteredAlternatingCoupling
              factorTwoCenteredP4 centeredP1 +
            c3 * factorTwoCenteredAlternatingCoupling
              factorTwoCenteredP4 centeredP3) := by
    rw [factorTwoCenteredAlternatingCoupling_oddStructuralLow_right
      (fun x ↦ c4 * factorTwoCenteredP4 x) heContinuous c1 c3,
      hoAltEntry1, hoAltEntry3]
    ring
  unfold factorTwoIntrinsicFourP45Mixed factorTwoEndpointLowTailMixed
  rw [heCleanExpanded, hoCleanExpanded, heSymExpanded, hoSymExpanded,
    heAltExpanded, hoAltExpanded]
  unfold factorTwoIntrinsicFourP45Cross04
    factorTwoIntrinsicFourP45Cross24
    factorTwoIntrinsicFourP45Cross15
    factorTwoIntrinsicFourP45Cross35
    factorTwoIntrinsicFourP45Cross05
    factorTwoIntrinsicFourP45Cross25
    factorTwoIntrinsicFourP45Cross41
    factorTwoIntrinsicFourP45Cross43
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
