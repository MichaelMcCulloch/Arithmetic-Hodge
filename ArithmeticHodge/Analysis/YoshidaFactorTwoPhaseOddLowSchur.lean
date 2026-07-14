import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaEndpointOddLowGramExpansion
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddStructuralPerturbation

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddLowSchur

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseOddStructuralPerturbation

/-!
# Intrinsic odd low-mode Schur reduction

The odd profile is split into its exact shifted-Legendre `P₁/P₃` block
and an infinite residual annihilating those two coefficients.  Every signed
term in the factor-two phase is polarized before applying the scalar Schur
complement.  There is no Fourier cutoff or finite-mode enumeration.
-/

/-- The three entries of the phase-dependent odd `P₁/P₃` Gram pencil. -/
def factorTwoOddStructuralPhaseLow11 (alpha : ℝ) : ℝ :=
  yoshidaEndpointOddLowGram11 +
    alpha * factorTwoCenteredSymmetricPerturbation centeredP1

def factorTwoOddStructuralPhaseLow13 (alpha : ℝ) : ℝ :=
  yoshidaEndpointOddLowGram13 +
    alpha * factorTwoCenteredSymmetricPerturbationBilinear
      centeredP1 centeredP3

def factorTwoOddStructuralPhaseLow33 (alpha : ℝ) : ℝ :=
  yoshidaEndpointOddLowGram33 +
    alpha * factorTwoCenteredSymmetricPerturbation centeredP3

/-- Complete phase pairings of the two odd low modes against the residual
and the even channel.  The `beta / 2` normalization makes the quadratic
cross terms exactly `2*c*ell₁ + 2*d*ell₃`. -/
def factorTwoOddStructuralPhaseLowTail1
    (e r : ℝ → ℝ) (alpha beta : ℝ) : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredP1 r +
    alpha * factorTwoCenteredSymmetricPerturbationBilinear centeredP1 r +
    (beta / 2) * factorTwoCenteredAlternatingCoupling e centeredP1

def factorTwoOddStructuralPhaseLowTail3
    (e r : ℝ → ℝ) (alpha beta : ℝ) : ℝ :=
  yoshidaEndpointEvenCleanBilinear centeredP3 r +
    alpha * factorTwoCenteredSymmetricPerturbationBilinear centeredP3 r +
    (beta / 2) * factorTwoCenteredAlternatingCoupling e centeredP3

/-- The complete coupled phase after removing the intrinsic odd low block. -/
def factorTwoOddStructuralPhaseTail
    (e r : ℝ → ℝ) (alpha beta : ℝ) : ℝ :=
  factorTwoEndpointChannelPhase e r alpha beta

/-- Positivity of the affine odd low pencil on `[-1,1]` follows from its two
signed endpoints by convexity of the quadratic form.  No determinant search
over the phase parameter is needed. -/
theorem factorTwoOddStructuralPhaseLow_pos_of_endpoints
    (alpha : ℝ) (halphaLower : -1 ≤ alpha) (halphaUpper : alpha ≤ 1)
    (hplus11 : 0 < factorTwoOddStructuralPhaseLow11 1)
    (hplusDet : 0 <
      factorTwoOddStructuralPhaseLow11 1 *
          factorTwoOddStructuralPhaseLow33 1 -
        factorTwoOddStructuralPhaseLow13 1 ^ 2)
    (hminus11 : 0 < factorTwoOddStructuralPhaseLow11 (-1))
    (hminusDet : 0 <
      factorTwoOddStructuralPhaseLow11 (-1) *
          factorTwoOddStructuralPhaseLow33 (-1) -
        factorTwoOddStructuralPhaseLow13 (-1) ^ 2) :
    0 < factorTwoOddStructuralPhaseLow11 alpha ∧
      0 < factorTwoOddStructuralPhaseLow11 alpha *
          factorTwoOddStructuralPhaseLow33 alpha -
        factorTwoOddStructuralPhaseLow13 alpha ^ 2 := by
  let lambda : ℝ := (1 + alpha) / 2
  let mu : ℝ := (1 - alpha) / 2
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    linarith
  have hmu : 0 ≤ mu := by
    dsimp only [mu]
    linarith
  have hquadratic (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
      0 < factorTwoOddStructuralPhaseLow11 alpha * c ^ 2 +
        2 * factorTwoOddStructuralPhaseLow13 alpha * c * d +
        factorTwoOddStructuralPhaseLow33 alpha * d ^ 2 := by
    let Qplus := factorTwoOddStructuralPhaseLow11 1 * c ^ 2 +
      2 * factorTwoOddStructuralPhaseLow13 1 * c * d +
      factorTwoOddStructuralPhaseLow33 1 * d ^ 2
    let Qminus := factorTwoOddStructuralPhaseLow11 (-1) * c ^ 2 +
      2 * factorTwoOddStructuralPhaseLow13 (-1) * c * d +
      factorTwoOddStructuralPhaseLow33 (-1) * d ^ 2
    have hplus : 0 < Qplus := real_twoByTwo_quadratic_pos _ _ _ c d
      hplus11 hplusDet hne
    have hminus : 0 < Qminus := real_twoByTwo_quadratic_pos _ _ _ c d
      hminus11 hminusDet hne
    have hconvex :
        factorTwoOddStructuralPhaseLow11 alpha * c ^ 2 +
            2 * factorTwoOddStructuralPhaseLow13 alpha * c * d +
            factorTwoOddStructuralPhaseLow33 alpha * d ^ 2 =
          lambda * Qplus + mu * Qminus := by
      dsimp only [lambda, mu, Qplus, Qminus]
      unfold factorTwoOddStructuralPhaseLow11
        factorTwoOddStructuralPhaseLow13
        factorTwoOddStructuralPhaseLow33
      ring
    rw [hconvex]
    rcases hlambda.eq_or_lt with hlambdaZero | hlambdaPos
    · have hmuOne : mu = 1 := by
        dsimp only [lambda, mu] at hlambdaZero ⊢
        linarith
      rw [← hlambdaZero, hmuOne, zero_mul, one_mul]
      simpa using hminus
    · exact add_pos_of_pos_of_nonneg (mul_pos hlambdaPos hplus)
        (mul_nonneg hmu hminus.le)
  exact real_twoByTwo_coefficients_pos_of_quadratic_pos _ _ _ hquadratic

/-- Closed-disk version of the endpoint convexity criterion. -/
theorem factorTwoOddStructuralPhaseLow_pos_of_endpoint_certificates
    (alpha beta : ℝ) (hab : alpha ^ 2 + beta ^ 2 ≤ 1)
    (hplus11 : 0 < factorTwoOddStructuralPhaseLow11 1)
    (hplusDet : 0 <
      factorTwoOddStructuralPhaseLow11 1 *
          factorTwoOddStructuralPhaseLow33 1 -
        factorTwoOddStructuralPhaseLow13 1 ^ 2)
    (hminus11 : 0 < factorTwoOddStructuralPhaseLow11 (-1))
    (hminusDet : 0 <
      factorTwoOddStructuralPhaseLow11 (-1) *
          factorTwoOddStructuralPhaseLow33 (-1) -
        factorTwoOddStructuralPhaseLow13 (-1) ^ 2) :
    0 < factorTwoOddStructuralPhaseLow11 alpha ∧
      0 < factorTwoOddStructuralPhaseLow11 alpha *
          factorTwoOddStructuralPhaseLow33 alpha -
        factorTwoOddStructuralPhaseLow13 alpha ^ 2 := by
  have halphaLower : -1 ≤ alpha := by
    nlinarith [sq_nonneg beta, sq_nonneg (alpha + 1)]
  have halphaUpper : alpha ≤ 1 := by
    nlinarith [sq_nonneg beta, sq_nonneg (alpha - 1)]
  exact factorTwoOddStructuralPhaseLow_pos_of_endpoints alpha
    halphaLower halphaUpper hplus11 hplusDet hminus11 hminusDet

/-- Exact odd `P₁/P₃` low/tail expansion of the complete signed phase. -/
theorem factorTwoEndpointChannelPhase_oddStructuralLowTail
    (e r : ℝ → ℝ) (he : Continuous e) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (c d alpha beta : ℝ) :
    factorTwoEndpointChannelPhase e
        (factorTwoOddStructuralLowProfile c d + r) alpha beta =
      factorTwoOddStructuralPhaseLow11 alpha * c ^ 2 +
        2 * factorTwoOddStructuralPhaseLow13 alpha * c * d +
        factorTwoOddStructuralPhaseLow33 alpha * d ^ 2 +
        2 * c * factorTwoOddStructuralPhaseLowTail1 e r alpha beta +
        2 * d * factorTwoOddStructuralPhaseLowTail3 e r alpha beta +
        factorTwoOddStructuralPhaseTail e r alpha beta := by
  have hlow : Continuous (factorTwoOddStructuralLowProfile c d) :=
    continuous_factorTwoOddStructuralLowProfile c d
  have hQ :=
    yoshidaEndpointOddCleanQuadratic_oddStructuralLow_tail_eq_bilinear
      r hr hlocal hone hthree c d
  have hQlow := yoshidaEndpointOddLowGram_quadratic c d
  have hQcross := yoshidaEndpointEvenCleanBilinear_oddStructuralLow
    c d r hr hone hthree
  have hP := factorTwoCenteredSymmetricPerturbation_add_eq_bilinear
    (factorTwoOddStructuralLowProfile c d) r hlow hr
  have hPlow :=
    factorTwoCenteredSymmetricPerturbation_oddStructuralLow c d
  have hPcross :=
    factorTwoCenteredSymmetricPerturbationBilinear_oddStructuralLow
      c d r hr
  have hJ := factorTwoCenteredAlternatingCoupling_add_right
    e (factorTwoOddStructuralLowProfile c d) r he hlow hr
  have hJlow :=
    factorTwoCenteredAlternatingCoupling_oddStructuralLow_right e he c d
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
    factorTwoOddStructuralPhaseLow11 factorTwoOddStructuralPhaseLow13
    factorTwoOddStructuralPhaseLow33 factorTwoOddStructuralPhaseLowTail1
    factorTwoOddStructuralPhaseLowTail3 factorTwoOddStructuralPhaseTail
  rw [hQ, hQlow, hQcross, hP, hPlow, hPcross, hJ, hJlow]
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
  ring

/-- Exact two-by-two Schur closure of the intrinsic odd low block. -/
theorem factorTwoEndpointChannelPhase_oddStructuralLowTail_nonneg
    (e r : ℝ → ℝ) (he : Continuous e) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) r)
    (hone : centeredOddP1Coefficient r = 0)
    (hthree : centeredOddP3Coefficient r = 0)
    (c d alpha beta : ℝ)
    (h11 : 0 < factorTwoOddStructuralPhaseLow11 alpha)
    (hdet : 0 <
      factorTwoOddStructuralPhaseLow11 alpha *
          factorTwoOddStructuralPhaseLow33 alpha -
        factorTwoOddStructuralPhaseLow13 alpha ^ 2)
    (hschur :
      factorTwoOddStructuralPhaseLow33 alpha *
          factorTwoOddStructuralPhaseLowTail1 e r alpha beta ^ 2 -
        2 * factorTwoOddStructuralPhaseLow13 alpha *
          factorTwoOddStructuralPhaseLowTail1 e r alpha beta *
          factorTwoOddStructuralPhaseLowTail3 e r alpha beta +
        factorTwoOddStructuralPhaseLow11 alpha *
          factorTwoOddStructuralPhaseLowTail3 e r alpha beta ^ 2 ≤
        (factorTwoOddStructuralPhaseLow11 alpha *
            factorTwoOddStructuralPhaseLow33 alpha -
          factorTwoOddStructuralPhaseLow13 alpha ^ 2) *
          factorTwoOddStructuralPhaseTail e r alpha beta) :
    0 ≤ factorTwoEndpointChannelPhase e
      (factorTwoOddStructuralLowProfile c d + r) alpha beta := by
  rw [factorTwoEndpointChannelPhase_oddStructuralLowTail
    e r he hr hlocal hone hthree c d alpha beta]
  exact TwoByTwoSchur.quadratic_add_tail_nonneg
    (factorTwoOddStructuralPhaseLow11 alpha)
    (factorTwoOddStructuralPhaseLow13 alpha)
    (factorTwoOddStructuralPhaseLow33 alpha)
    (factorTwoOddStructuralPhaseLowTail1 e r alpha beta)
    (factorTwoOddStructuralPhaseLowTail3 e r alpha beta)
    (factorTwoOddStructuralPhaseTail e r alpha beta)
    c d h11 hdet hschur

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddLowSchur
