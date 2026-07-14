import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixSchurReduction

noncomputable section

open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicEvenEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# One-Schur reduction for the first six intrinsic modes

Eliminating only the `P₀/P₂` plane turns the six-mode problem into a
single quadratic residual on `(P₄,P₁,P₃,P₅)`.  This is sharper than
splitting the already-positive four-mode and `P₄/P₅` blocks, whose mixed
Schur condition is quartic in their coefficients.
-/

/-- The even residual after removing the intrinsic `P₀/P₂` plane. -/
def factorTwoIntrinsicSixEvenTail (c4 : ℝ) : ℝ → ℝ :=
  fun x ↦ c4 * factorTwoCenteredP4 x

/-- The entire odd profile retained on the tail side of the first Schur
elimination. -/
def factorTwoIntrinsicSixOddTail (c1 c3 c5 : ℝ) : ℝ → ℝ :=
  factorTwoOddStructuralLowProfile c1 c3 +
    fun x ↦ c5 * factorTwoCenteredP5 x

/-- The exact inverse-free Schur residual after eliminating `P₀/P₂`.
It is quadratic, rather than quartic, in the four remaining coefficients. -/
def factorTwoIntrinsicSixSchurResidual
    (c4 c1 c3 c5 a b : ℝ) : ℝ :=
  (factorTwoStructuralPhaseLow00 a *
        factorTwoStructuralPhaseLow22 a -
      factorTwoStructuralPhaseLow02 a ^ 2) *
      factorTwoStructuralPhaseTail
        (factorTwoIntrinsicSixEvenTail c4)
        (factorTwoIntrinsicSixOddTail c1 c3 c5) a b -
    (factorTwoStructuralPhaseLow22 a *
          factorTwoStructuralPhaseLowTail0
            (factorTwoIntrinsicSixEvenTail c4)
            (factorTwoIntrinsicSixOddTail c1 c3 c5) a b ^ 2 -
      2 * factorTwoStructuralPhaseLow02 a *
          factorTwoStructuralPhaseLowTail0
            (factorTwoIntrinsicSixEvenTail c4)
            (factorTwoIntrinsicSixOddTail c1 c3 c5) a b *
          factorTwoStructuralPhaseLowTail2
            (factorTwoIntrinsicSixEvenTail c4)
            (factorTwoIntrinsicSixOddTail c1 c3 c5) a b +
      factorTwoStructuralPhaseLow00 a *
          factorTwoStructuralPhaseLowTail2
            (factorTwoIntrinsicSixEvenTail c4)
            (factorTwoIntrinsicSixOddTail c1 c3 c5) a b ^ 2)

private theorem continuous_factorTwoIntrinsicSixEvenTail (c4 : ℝ) :
    Continuous (factorTwoIntrinsicSixEvenTail c4) := by
  unfold factorTwoIntrinsicSixEvenTail
  exact continuous_const.mul continuous_factorTwoCenteredP4

private theorem even_factorTwoIntrinsicSixEvenTail (c4 : ℝ) :
    Function.Even (factorTwoIntrinsicSixEvenTail c4) := by
  intro x
  unfold factorTwoIntrinsicSixEvenTail
  rw [even_factorTwoCenteredP4]

private theorem factorTwoIntrinsicSixEvenTail_coefficients_zero (c4 : ℝ) :
    centeredEvenP0Coefficient (factorTwoIntrinsicSixEvenTail c4) = 0 ∧
      centeredEvenP2Coefficient (factorTwoIntrinsicSixEvenTail c4) = 0 := by
  constructor
  · unfold centeredEvenP0Coefficient factorTwoIntrinsicSixEvenTail
    rw [show (fun x : ℝ ↦ c4 * factorTwoCenteredP4 x) =
        fun x ↦ c4 * factorTwoCenteredP4 x by rfl,
      intervalIntegral.integral_const_mul,
      show (∫ x : ℝ in -1..1, factorTwoCenteredP4 x) = 0 by
        simpa [centeredEvenP0Coefficient] using
          factorTwoCenteredP4_intrinsic_coefficients_zero.1]
    ring
  · unfold centeredEvenP2Coefficient factorTwoIntrinsicSixEvenTail
    rw [show (fun x : ℝ ↦
        c4 * factorTwoCenteredP4 x * centeredEvenP2 x) =
        fun x ↦ c4 *
          (factorTwoCenteredP4 x * centeredEvenP2 x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul,
      show (∫ x : ℝ in -1..1,
          factorTwoCenteredP4 x * centeredEvenP2 x) = 0 by
        simpa [centeredEvenP2Coefficient] using
          factorTwoCenteredP4_intrinsic_coefficients_zero.2]
    ring

private theorem locallyLipschitzOn_factorTwoIntrinsicSixEvenTail (c4 : ℝ) :
    LocallyLipschitzOn (Icc (-1) 1)
      (factorTwoIntrinsicSixEvenTail c4) := by
  have h : ContDiff ℝ 1 (factorTwoIntrinsicSixEvenTail c4) := by
    unfold factorTwoIntrinsicSixEvenTail factorTwoCenteredP4
    fun_prop
  exact h.locallyLipschitz.locallyLipschitzOn

private theorem continuous_factorTwoIntrinsicSixOddTail
    (c1 c3 c5 : ℝ) :
    Continuous (factorTwoIntrinsicSixOddTail c1 c3 c5) := by
  unfold factorTwoIntrinsicSixOddTail
  exact (continuous_factorTwoOddStructuralLowProfile c1 c3).add
    (continuous_const.mul continuous_factorTwoCenteredP5)

/-- Structural positivity of the intrinsic even endpoint pencils reduces
the complete six-mode phase to the one displayed quadratic residual. -/
theorem factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_schur
    (c0 c2 c4 c1 c3 c5 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hSchur : 0 ≤
      factorTwoIntrinsicSixSchurResidual c4 c1 c3 c5 a b) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4)
      (factorTwoIntrinsicSixOddTail c1 c3 c5) a b := by
  have hLow := factorTwoStructuralPhaseLow_pos_of_endpoint_certificates
    a b hab
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.1
    factorTwoIntrinsicEven_plus_endpoint_structural_gates.2
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.1
    factorTwoIntrinsicEven_minus_endpoint_kernel_gates.2
  apply factorTwoEndpointChannelPhase_structuralLowTail_nonneg
    (factorTwoIntrinsicSixEvenTail c4)
    (factorTwoIntrinsicSixOddTail c1 c3 c5)
    (continuous_factorTwoIntrinsicSixEvenTail c4)
    (even_factorTwoIntrinsicSixEvenTail c4)
    (factorTwoIntrinsicSixEvenTail_coefficients_zero c4).1
    (factorTwoIntrinsicSixEvenTail_coefficients_zero c4).2
    (locallyLipschitzOn_factorTwoIntrinsicSixEvenTail c4)
    (continuous_factorTwoIntrinsicSixOddTail c1 c3 c5)
    c0 c2 a b hLow.1 hLow.2
  unfold factorTwoIntrinsicSixSchurResidual at hSchur
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
