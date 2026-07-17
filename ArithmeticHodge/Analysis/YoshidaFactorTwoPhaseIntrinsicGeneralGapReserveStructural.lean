import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicGeneralGapReserveStructural

open ShiftedLegendreL2Basis
open ShiftedLegendreL2HigherGap
open ShiftedLegendreCenteredParity
open ShiftedLegendreOrthogonality
open YoshidaEndpointHyperbolicBound
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPullbackLipschitz
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual

noncomputable section

/-!
# The phase reserve at arbitrary Legendre gaps

The singular-square lower bound and the projected smooth-remainder estimate
do not depend on the fixed ninth and tenth cutoffs used by the first
higher-residual positivity theorem.  Combining them with the exact harmonic
gap at arbitrary even and odd cutoffs retains the full cutoff-dependent
energy coefficients and half of both endpoint-potential energies.
-/

/-- The exact quantitative phase reserve above arbitrary even and odd
shifted-Legendre gaps.  The displayed energy coefficients need not be
nonnegative; subsequent applications can select cutoffs for which they have
the required margin. -/
theorem factorTwoEndpointChannelPhase_general_gap_reserve
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (kE kO : ℕ)
    (heLow : centeredLegendreMomentsVanishBelow e kE)
    (hoLow : centeredLegendreMomentsVanishBelow o kO)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    ((harmonic kE : ℝ) -
          factorTwoIntrinsicProjectedEvenRemainderLoss a b -
          Real.log 2 / 2) * factorTwoIntrinsicEnergy e +
        ((harmonic kO : ℝ) -
          factorTwoIntrinsicProjectedOddRemainderLoss a b -
          Real.log 2 / 2) * factorTwoIntrinsicEnergy o +
        (1 / 2 : ℝ) *
          (factorTwoIntrinsicPotentialEnergy e +
            factorTwoIntrinsicPotentialEnergy o) ≤
      factorTwoEndpointChannelPhase e o a b := by
  have heRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    e hec helocal kE heLow
  have hoRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    o hoc holocal kO hoLow
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    e o hec hoc helocal holocal a b hab
  have hremainder := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    e o hec hoc he ho he0 a b hab
  rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    e o hec hoc a b]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicGeneralGapReserveStructural
