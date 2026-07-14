import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixSchurReduction

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixSchurExpansion

noncomputable section

open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenLowProfile
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicFourP45Reduction
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation

/-!
# Exact coordinate expansion of the six-mode Schur residual

The two low-to-tail functionals are linear and the remaining tail phase is
quadratic in `(c₄,c₁,c₃,c₅)`.  The formulas below keep every clean,
symmetric, and alternating cross entry intact.
-/

/-- First complete `P₀`-to-tail functional. -/
def factorTwoIntrinsicSixLowTail0
    (c4 c1 c3 c5 a b : ℝ) : ℝ :=
  c4 * factorTwoIntrinsicFourP45Cross04 a +
    (b / 2) *
      (factorTwoIntrinsicAlternatingRow0 c1 c3 +
        c5 * factorTwoIntrinsicFourP45Cross05)

/-- Second complete `P₂`-to-tail functional. -/
def factorTwoIntrinsicSixLowTail2
    (c4 c1 c3 c5 a b : ℝ) : ℝ :=
  c4 * factorTwoIntrinsicFourP45Cross24 a +
    (b / 2) *
      (factorTwoIntrinsicAlternatingRow2 c1 c3 +
        c5 * factorTwoIntrinsicFourP45Cross25)

/-- Exact tail phase after the `P₀/P₂` plane has been removed. -/
def factorTwoIntrinsicSixTailQuadratic
    (c4 c1 c3 c5 a b : ℝ) : ℝ :=
  factorTwoIntrinsicOddPhaseQuadratic a c1 c3 +
    factorTwoEndpointChannelPhase
      (fun x ↦ c4 * factorTwoCenteredP4 x)
      (fun x ↦ c5 * factorTwoCenteredP5 x) a b +
    2 *
      (c5 *
          (c1 * factorTwoIntrinsicFourP45Cross15 a +
            c3 * factorTwoIntrinsicFourP45Cross35 a) +
        (b / 2) * c4 *
          (c1 * factorTwoIntrinsicFourP45Cross41 +
            c3 * factorTwoIntrinsicFourP45Cross43))

theorem factorTwoStructuralPhaseLowTail0_intrinsicSix
    (c4 c1 c3 c5 a b : ℝ) :
    factorTwoStructuralPhaseLowTail0
        (factorTwoIntrinsicSixEvenTail c4)
        (factorTwoIntrinsicSixOddTail c1 c3 c5) a b =
      factorTwoIntrinsicSixLowTail0 c4 c1 c3 c5 a b := by
  have hQ :
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
  have hP :
      factorTwoCenteredSymmetricPerturbationBilinear centeredEvenP0
          (fun x ↦ c4 * factorTwoCenteredP4 x) =
        c4 * factorTwoCenteredSymmetricPerturbationBilinear
          centeredEvenP0 factorTwoCenteredP4 := by
    simpa [factorTwoIntrinsicSixEvenTail, smul_eq_mul] using
      (factorTwoCenteredSymmetricPerturbationBilinear_smul_smul
        1 c4 centeredEvenP0 factorTwoCenteredP4)
  have hJLow := factorTwoCenteredAlternatingCoupling_oddStructuralLow_right
    centeredEvenP0 (by unfold centeredEvenP0; fun_prop) c1 c3
  have hJP5 :
      factorTwoCenteredAlternatingCoupling centeredEvenP0
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c5 * factorTwoCenteredAlternatingCoupling
          centeredEvenP0 factorTwoCenteredP5 := by
    simpa [smul_eq_mul] using
      (factorTwoCenteredAlternatingCoupling_smul_right
        c5 centeredEvenP0 factorTwoCenteredP5)
  have hJ := factorTwoCenteredAlternatingCoupling_add_right
    centeredEvenP0 (factorTwoOddStructuralLowProfile c1 c3)
      (fun x ↦ c5 * factorTwoCenteredP5 x)
      (by unfold centeredEvenP0; fun_prop)
      (continuous_factorTwoOddStructuralLowProfile c1 c3)
      (continuous_const.mul continuous_factorTwoCenteredP5)
  unfold factorTwoStructuralPhaseLowTail0
    factorTwoIntrinsicSixLowTail0 factorTwoIntrinsicSixEvenTail
    factorTwoIntrinsicSixOddTail
  rw [show (fun x : ℝ ↦
      yoshidaEndpointEvenTailRepresenter0 x *
        (c4 * factorTwoCenteredP4 x)) =
      fun x ↦ c4 *
        (yoshidaEndpointEvenTailRepresenter0 x * factorTwoCenteredP4 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul, ← hQ, hP, hJ, hJLow, hJP5]
  unfold factorTwoIntrinsicFourP45Cross04
    factorTwoIntrinsicFourP45Cross05
    factorTwoIntrinsicAlternatingRow0
    factorTwoIntrinsicAlternating01 factorTwoIntrinsicAlternating03
  ring

theorem factorTwoStructuralPhaseLowTail2_intrinsicSix
    (c4 c1 c3 c5 a b : ℝ) :
    factorTwoStructuralPhaseLowTail2
        (factorTwoIntrinsicSixEvenTail c4)
        (factorTwoIntrinsicSixOddTail c1 c3 c5) a b =
      factorTwoIntrinsicSixLowTail2 c4 c1 c3 c5 a b := by
  have hQ :
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
  have hP :
      factorTwoCenteredSymmetricPerturbationBilinear centeredEvenP2
          (fun x ↦ c4 * factorTwoCenteredP4 x) =
        c4 * factorTwoCenteredSymmetricPerturbationBilinear
          centeredEvenP2 factorTwoCenteredP4 := by
    simpa [factorTwoIntrinsicSixEvenTail, smul_eq_mul] using
      (factorTwoCenteredSymmetricPerturbationBilinear_smul_smul
        1 c4 centeredEvenP2 factorTwoCenteredP4)
  have hJLow := factorTwoCenteredAlternatingCoupling_oddStructuralLow_right
    centeredEvenP2 (by unfold centeredEvenP2; fun_prop) c1 c3
  have hJP5 :
      factorTwoCenteredAlternatingCoupling centeredEvenP2
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c5 * factorTwoCenteredAlternatingCoupling
          centeredEvenP2 factorTwoCenteredP5 := by
    simpa [smul_eq_mul] using
      (factorTwoCenteredAlternatingCoupling_smul_right
        c5 centeredEvenP2 factorTwoCenteredP5)
  have hJ := factorTwoCenteredAlternatingCoupling_add_right
    centeredEvenP2 (factorTwoOddStructuralLowProfile c1 c3)
      (fun x ↦ c5 * factorTwoCenteredP5 x)
      (by unfold centeredEvenP2; fun_prop)
      (continuous_factorTwoOddStructuralLowProfile c1 c3)
      (continuous_const.mul continuous_factorTwoCenteredP5)
  unfold factorTwoStructuralPhaseLowTail2
    factorTwoIntrinsicSixLowTail2 factorTwoIntrinsicSixEvenTail
    factorTwoIntrinsicSixOddTail
  rw [show (fun x : ℝ ↦
      yoshidaEndpointEvenTailRepresenter2 x *
        (c4 * factorTwoCenteredP4 x)) =
      fun x ↦ c4 *
        (yoshidaEndpointEvenTailRepresenter2 x * factorTwoCenteredP4 x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul, ← hQ, hP, hJ, hJLow, hJP5]
  unfold factorTwoIntrinsicFourP45Cross24
    factorTwoIntrinsicFourP45Cross25
    factorTwoIntrinsicAlternatingRow2
    factorTwoIntrinsicAlternating21 factorTwoIntrinsicAlternating23
  ring

theorem factorTwoStructuralPhaseTail_intrinsicSix
    (c4 c1 c3 c5 a b : ℝ) :
    factorTwoStructuralPhaseTail
        (factorTwoIntrinsicSixEvenTail c4)
        (factorTwoIntrinsicSixOddTail c1 c3 c5) a b =
      factorTwoIntrinsicSixTailQuadratic c4 c1 c3 c5 a b := by
  have hdecomp := factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    (0 : ℝ → ℝ)
    (fun x ↦ c4 * factorTwoCenteredP4 x)
    (factorTwoOddStructuralLowProfile c1 c3)
    (fun x ↦ c5 * factorTwoCenteredP5 x)
    (by fun_prop)
    (continuous_const.mul continuous_factorTwoCenteredP4)
    (continuous_factorTwoOddStructuralLowProfile c1 c3)
    (continuous_const.mul continuous_factorTwoCenteredP5) a b
  have hLow := factorTwoEndpointChannelPhase_intrinsicLow_expansion
    0 0 c1 c3 a b
  have hMixed := factorTwoIntrinsicFourP45Mixed_eq_cross_entries
    0 0 c1 c3 c4 c5 a b
  have hzero : factorTwoEvenStructuralLowProfile 0 0 =
      (0 : ℝ → ℝ) := by
    funext x
    simp [factorTwoEvenStructuralLowProfile]
  rw [hzero] at hLow
  have hLow' :
      factorTwoEndpointChannelPhase (0 : ℝ → ℝ)
          (factorTwoOddStructuralLowProfile c1 c3) a b =
        factorTwoIntrinsicOddPhaseQuadratic a c1 c3 := by
    simpa [factorTwoEvenStructuralLowProfile] using hLow
  have hMixed' :
      factorTwoEndpointLowTailMixed
          (0 : ℝ → ℝ)
          (fun x ↦ c4 * factorTwoCenteredP4 x)
          (factorTwoOddStructuralLowProfile c1 c3)
          (fun x ↦ c5 * factorTwoCenteredP5 x) a b =
        c5 *
            (c1 * factorTwoIntrinsicFourP45Cross15 a +
              c3 * factorTwoIntrinsicFourP45Cross35 a) +
          (b / 2) * c4 *
            (c1 * factorTwoIntrinsicFourP45Cross41 +
              c3 * factorTwoIntrinsicFourP45Cross43) := by
    unfold factorTwoIntrinsicFourP45Mixed at hMixed
    rw [hzero] at hMixed
    rw [hMixed]
    ring
  unfold factorTwoStructuralPhaseTail factorTwoIntrinsicSixEvenTail
    factorTwoIntrinsicSixOddTail factorTwoIntrinsicSixTailQuadratic
  have htotal := hdecomp
  rw [hLow', hMixed'] at htotal
  have hzeroAdd : (0 : ℝ → ℝ) +
      (fun x ↦ c4 * factorTwoCenteredP4 x) =
        (fun x ↦ c4 * factorTwoCenteredP4 x) := by
    funext x
    simp
  rw [hzeroAdd] at htotal
  rw [htotal]
  ring

/-- The original function-level residual is exactly the explicit coordinate
quadratic above. -/
theorem factorTwoIntrinsicSixSchurResidual_eq_expansion
    (c4 c1 c3 c5 a b : ℝ) :
    factorTwoIntrinsicSixSchurResidual c4 c1 c3 c5 a b =
      (factorTwoStructuralPhaseLow00 a *
            factorTwoStructuralPhaseLow22 a -
          factorTwoStructuralPhaseLow02 a ^ 2) *
          factorTwoIntrinsicSixTailQuadratic c4 c1 c3 c5 a b -
        (factorTwoStructuralPhaseLow22 a *
              factorTwoIntrinsicSixLowTail0 c4 c1 c3 c5 a b ^ 2 -
          2 * factorTwoStructuralPhaseLow02 a *
              factorTwoIntrinsicSixLowTail0 c4 c1 c3 c5 a b *
              factorTwoIntrinsicSixLowTail2 c4 c1 c3 c5 a b +
          factorTwoStructuralPhaseLow00 a *
              factorTwoIntrinsicSixLowTail2 c4 c1 c3 c5 a b ^ 2) := by
  unfold factorTwoIntrinsicSixSchurResidual
  rw [factorTwoStructuralPhaseTail_intrinsicSix,
    factorTwoStructuralPhaseLowTail0_intrinsicSix,
    factorTwoStructuralPhaseLowTail2_intrinsicSix]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixSchurExpansion
