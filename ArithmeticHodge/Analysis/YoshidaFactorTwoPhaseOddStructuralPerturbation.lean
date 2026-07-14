import ArithmeticHodge.Analysis.YoshidaEndpointOddResidualRegularity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddStructuralPerturbation

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur

/-!
# Intrinsic odd low-mode algebra for the factor-two phase

The odd profile is split into its structural `P₁/P₃` component and a
genuine residual.  The lemmas below expand the complete factor-two
perturbation, including its singular archimedean term and both retained prime
atoms.  The clean quadratic is deliberately left inside the exact phase and
polarization APIs: no coefficientwise clean split is asserted here.
-/

/-- The intrinsic odd low profile is the sum of its two real scalar
multiples. -/
theorem factorTwoOddStructuralLowProfile_eq_smul_add
    (c d : ℝ) :
    factorTwoOddStructuralLowProfile c d =
      c • centeredP1 + d • centeredP3 := by
  funext x
  simp only [factorTwoOddStructuralLowProfile, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]

/-- Exact `P₁/P₃` quadratic expansion of the complete symmetric
factor-two perturbation. -/
theorem factorTwoCenteredSymmetricPerturbation_oddStructuralLow
    (c d : ℝ) :
    factorTwoCenteredSymmetricPerturbation
        (factorTwoOddStructuralLowProfile c d) =
      c ^ 2 * factorTwoCenteredSymmetricPerturbation centeredP1 +
        2 * c * d *
          factorTwoCenteredSymmetricPerturbationBilinear
            centeredP1 centeredP3 +
        d ^ 2 * factorTwoCenteredSymmetricPerturbation centeredP3 := by
  have h1 : Continuous centeredP1 := by
    unfold centeredP1
    fun_prop
  have h3 : Continuous centeredP3 := by
    unfold centeredP3
    fun_prop
  rw [factorTwoOddStructuralLowProfile_eq_smul_add,
    factorTwoCenteredSymmetricPerturbation_add_eq_bilinear
      (c • centeredP1) (d • centeredP3)
      (h1.const_smul c) (h3.const_smul d),
    factorTwoCenteredSymmetricPerturbation_smul,
    factorTwoCenteredSymmetricPerturbation_smul,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul]
  ring

/-- Exact symmetric-perturbation pairing of the odd structural low profile
against a continuous residual. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_oddStructuralLow
    (c d : ℝ) (r : ℝ → ℝ) (hr : Continuous r) :
    factorTwoCenteredSymmetricPerturbationBilinear
        (factorTwoOddStructuralLowProfile c d) r =
      c * factorTwoCenteredSymmetricPerturbationBilinear centeredP1 r +
        d * factorTwoCenteredSymmetricPerturbationBilinear centeredP3 r := by
  have h1 : Continuous centeredP1 := by
    unfold centeredP1
    fun_prop
  have h3 : Continuous centeredP3 := by
    unfold centeredP3
    fun_prop
  rw [factorTwoOddStructuralLowProfile_eq_smul_add,
    factorTwoCenteredSymmetricPerturbationBilinear_add_left
      (c • centeredP1) (d • centeredP3) r
      (h1.const_smul c) (h3.const_smul d) hr,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_left,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_left]

/-- The preceding pairing specialized to the canonical `P₁/P₃`
residual of a continuous odd profile. -/
theorem factorTwoCenteredSymmetricPerturbationBilinear_oddLow_oneThreeResidual
    (c d : ℝ) (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoCenteredSymmetricPerturbationBilinear
        (factorTwoOddStructuralLowProfile c d)
        (centeredOddOneThreeResidual w) =
      c * factorTwoCenteredSymmetricPerturbationBilinear
          centeredP1 (centeredOddOneThreeResidual w) +
        d * factorTwoCenteredSymmetricPerturbationBilinear
          centeredP3 (centeredOddOneThreeResidual w) := by
  exact factorTwoCenteredSymmetricPerturbationBilinear_oddStructuralLow
    c d (centeredOddOneThreeResidual w)
      (continuous_centeredOddOneThreeResidual w hw)

/-- Exact alternating coupling when the `P₁/P₃` low profile occupies
the right argument. -/
theorem factorTwoCenteredAlternatingCoupling_oddStructuralLow_right
    (u : ℝ → ℝ) (hu : Continuous u) (c d : ℝ) :
    factorTwoCenteredAlternatingCoupling u
        (factorTwoOddStructuralLowProfile c d) =
      c * factorTwoCenteredAlternatingCoupling u centeredP1 +
        d * factorTwoCenteredAlternatingCoupling u centeredP3 := by
  have h1 : Continuous centeredP1 := by
    unfold centeredP1
    fun_prop
  have h3 : Continuous centeredP3 := by
    unfold centeredP3
    fun_prop
  rw [factorTwoOddStructuralLowProfile_eq_smul_add,
    factorTwoCenteredAlternatingCoupling_add_right
      u (c • centeredP1) (d • centeredP3)
      hu (h1.const_smul c) (h3.const_smul d),
    factorTwoCenteredAlternatingCoupling_smul_right,
    factorTwoCenteredAlternatingCoupling_smul_right]

/-- Exact alternating coupling when the `P₁/P₃` low profile occupies
the left argument. -/
theorem factorTwoCenteredAlternatingCoupling_oddStructuralLow_left
    (c d : ℝ) (u : ℝ → ℝ) (hu : Continuous u) :
    factorTwoCenteredAlternatingCoupling
        (factorTwoOddStructuralLowProfile c d) u =
      c * factorTwoCenteredAlternatingCoupling centeredP1 u +
        d * factorTwoCenteredAlternatingCoupling centeredP3 u := by
  have h1 : Continuous centeredP1 := by
    unfold centeredP1
    fun_prop
  have h3 : Continuous centeredP3 := by
    unfold centeredP3
    fun_prop
  rw [factorTwoOddStructuralLowProfile_eq_smul_add,
    factorTwoCenteredAlternatingCoupling_add_left
      (c • centeredP1) (d • centeredP3) u
      (h1.const_smul c) (h3.const_smul d) hu,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_left]

/-- Exact full-phase decomposition after combining the intrinsic even
`P₀/P₂` low profile with the intrinsic odd `P₁/P₃` low profile.
The pure low phase and the clean part of the mixed polarization remain
intact; only the already-proved add/add identity is specialized. -/
theorem factorTwoEndpointChannelPhase_structuralLow_add_add_eq_low_mixed_tail
    (eTail oTail : ℝ → ℝ)
    (heTail : Continuous eTail) (hoTail : Continuous oTail)
    (c0 c2 c1 c3 alpha beta : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoEvenStructuralLowProfile c0 c2 + eTail)
        (factorTwoOddStructuralLowProfile c1 c3 + oTail)
        alpha beta =
      factorTwoEndpointChannelPhase
          (factorTwoEvenStructuralLowProfile c0 c2)
          (factorTwoOddStructuralLowProfile c1 c3)
          alpha beta +
        2 * factorTwoEndpointLowTailMixed
          (factorTwoEvenStructuralLowProfile c0 c2) eTail
          (factorTwoOddStructuralLowProfile c1 c3) oTail
          alpha beta +
        factorTwoEndpointChannelPhase eTail oTail alpha beta := by
  exact factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    (factorTwoEvenStructuralLowProfile c0 c2) eTail
    (factorTwoOddStructuralLowProfile c1 c3) oTail
    (continuous_factorTwoEvenStructuralLowProfile c0 c2) heTail
    (continuous_factorTwoOddStructuralLowProfile c1 c3) hoTail
    alpha beta

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddStructuralPerturbation
