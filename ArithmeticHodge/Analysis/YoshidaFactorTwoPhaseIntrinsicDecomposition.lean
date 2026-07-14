import ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualRegularity
import ArithmeticHodge.Analysis.YoshidaEndpointOddFullPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddStructuralPerturbation

set_option autoImplicit false

open Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicDecomposition

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenResidualRegularity
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation

/-!
# Canonical intrinsic decomposition of the full phase

Every parity profile is split by its first two allowed shifted-Legendre
degrees: `P₀/P₂` on the even side and `P₁/P₃` on the odd side.  The
following identity retains the complete signed clean, archimedean, and prime
terms in the low block, mixed polarization, and infinite residual block.
There is no Fourier cutoff.
-/

/-- The canonical intrinsic even low projection. -/
def factorTwoCanonicalEvenLow (e : ℝ → ℝ) : ℝ → ℝ :=
  factorTwoEvenStructuralLowProfile
    (centeredEvenP0Coefficient e) (centeredEvenP2Coefficient e)

/-- The canonical intrinsic odd low projection. -/
def factorTwoCanonicalOddLow (o : ℝ → ℝ) : ℝ → ℝ :=
  factorTwoOddStructuralLowProfile
    (centeredOddP1Coefficient o) (centeredOddP3Coefficient o)

theorem continuous_factorTwoCanonicalEvenLow
    (e : ℝ → ℝ) :
    Continuous (factorTwoCanonicalEvenLow e) :=
  continuous_factorTwoEvenStructuralLowProfile _ _

theorem continuous_factorTwoCanonicalOddLow
    (o : ℝ → ℝ) :
    Continuous (factorTwoCanonicalOddLow o) :=
  continuous_factorTwoOddStructuralLowProfile _ _

theorem factorTwoCanonicalEvenLow_add_residual
    (e : ℝ → ℝ) :
    factorTwoCanonicalEvenLow e + centeredEvenZeroTwoResidual e = e := by
  exact low_add_zeroTwoResidual_eq e

theorem factorTwoCanonicalOddLow_add_residual
    (o : ℝ → ℝ) :
    factorTwoCanonicalOddLow o + centeredOddOneThreeResidual o = o := by
  exact oddLow_add_oneThreeResidual_eq o

/-- Exact canonical low/mixed/residual expansion of the complete endpoint
phase.  In particular, neither the clean polarization nor a retained-prime
correlation is estimated or detached. -/
theorem factorTwoEndpointChannelPhase_eq_intrinsicLow_mixed_residual
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (a b : ℝ) :
    factorTwoEndpointChannelPhase e o a b =
      factorTwoEndpointChannelPhase
          (factorTwoCanonicalEvenLow e)
          (factorTwoCanonicalOddLow o) a b +
        2 * factorTwoEndpointLowTailMixed
          (factorTwoCanonicalEvenLow e)
          (centeredEvenZeroTwoResidual e)
          (factorTwoCanonicalOddLow o)
          (centeredOddOneThreeResidual o) a b +
        factorTwoEndpointChannelPhase
          (centeredEvenZeroTwoResidual e)
          (centeredOddOneThreeResidual o) a b := by
  have heTail : Continuous (centeredEvenZeroTwoResidual e) :=
    continuous_centeredEvenZeroTwoResidual e hec
  have hoTail : Continuous (centeredOddOneThreeResidual o) :=
    continuous_centeredOddOneThreeResidual o hoc
  have hsplit :=
    factorTwoEndpointChannelPhase_structuralLow_add_add_eq_low_mixed_tail
      (centeredEvenZeroTwoResidual e)
      (centeredOddOneThreeResidual o) heTail hoTail
      (centeredEvenP0Coefficient e) (centeredEvenP2Coefficient e)
      (centeredOddP1Coefficient o) (centeredOddP3Coefficient o) a b
  have heq :
      factorTwoEvenStructuralLowProfile
          (centeredEvenP0Coefficient e) (centeredEvenP2Coefficient e) +
        centeredEvenZeroTwoResidual e = e := by
    simpa only [factorTwoCanonicalEvenLow] using
      factorTwoCanonicalEvenLow_add_residual e
  have hoq :
      factorTwoOddStructuralLowProfile
          (centeredOddP1Coefficient o) (centeredOddP3Coefficient o) +
        centeredOddOneThreeResidual o = o := by
    simpa only [factorTwoCanonicalOddLow] using
      factorTwoCanonicalOddLow_add_residual o
  rw [heq, hoq] at hsplit
  simpa only [factorTwoCanonicalEvenLow, factorTwoCanonicalOddLow]
    using hsplit

/-- The canonical residuals have exactly the parity required by the
infinite-dimensional phase argument. -/
theorem intrinsicResidual_parity
    (e o : ℝ → ℝ) (heven : Function.Even e) (hodd : Function.Odd o) :
    Function.Even (centeredEvenZeroTwoResidual e) ∧
      Function.Odd (centeredOddOneThreeResidual o) := by
  constructor
  · intro x
    unfold centeredEvenZeroTwoResidual centeredEvenP0 centeredEvenP2
    rw [heven]
    ring
  · exact odd_centeredOddOneThreeResidual o hodd

/-- The canonical residuals annihilate all four intrinsic low
coefficients. -/
theorem intrinsicResidual_coefficients_zero
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o) :
    centeredEvenP0Coefficient (centeredEvenZeroTwoResidual e) = 0 ∧
      centeredEvenP2Coefficient (centeredEvenZeroTwoResidual e) = 0 ∧
      centeredOddP1Coefficient (centeredOddOneThreeResidual o) = 0 ∧
      centeredOddP3Coefficient (centeredOddOneThreeResidual o) = 0 := by
  exact ⟨centeredEvenP0Coefficient_zeroTwoResidual_eq_zero e hec,
    centeredEvenP2Coefficient_zeroTwoResidual_eq_zero e hec,
    centeredOddP1Coefficient_oneThreeResidual_eq_zero o hoc,
    centeredOddP3Coefficient_oneThreeResidual_eq_zero o hoc⟩

/-- Local Lipschitz form-domain regularity is preserved by the canonical
intrinsic residual projections. -/
theorem intrinsicResidual_locallyLipschitzOn
    (e o : ℝ → ℝ)
    (he : LocallyLipschitzOn (Icc (-1) 1) e)
    (ho : LocallyLipschitzOn (Icc (-1) 1) o) :
    LocallyLipschitzOn (Icc (-1) 1) (centeredEvenZeroTwoResidual e) ∧
      LocallyLipschitzOn (Icc (-1) 1)
        (centeredOddOneThreeResidual o) := by
  exact ⟨locallyLipschitzOn_centeredEvenZeroTwoResidual e he,
    locallyLipschitzOn_centeredOddOneThreeResidual o ho⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicDecomposition
