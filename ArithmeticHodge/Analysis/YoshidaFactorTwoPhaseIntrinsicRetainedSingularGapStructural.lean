import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicGeneralGapReserveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural

open YoshidaEndpointEvenStructuralReduction
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural
open YoshidaFactorTwoPhaseSingularSquare

noncomputable section

/-!
# Retaining the positive singular operator above an arbitrary gap

The scalar residual reserves discard the positive singular square after
using it to pay the projected smooth loss.  For the low--tail problem this is
too lossy: the singular polarization is a large part of the surviving mixed
row.  Here an arbitrary fraction `theta` of that genuine positive quadratic
form is retained.  The remaining fraction is converted into the harmonic
Legendre gap and pays the complete projected remainder.
-/

/-- The protected block is exactly one half of the weighted singular energy
minus the elementary `log 2` mass. -/
theorem half_singularWeightedEnergy_eq_protected_add_logMass
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) :
    (1 / 2 : ℝ) *
        factorTwoPhaseSingularWeightedEnergy e o a b =
      factorTwoIntrinsicProtectedBlock e o a b +
        Real.log 2 *
          (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o) := by
  have h :=
    centeredEnergy_add_potential_add_logMass_sub_half_phasePole_eq_square
      e o hec hoc helocal holocal a b
  unfold factorTwoPhaseSingularWeightedEnergy
    factorTwoIntrinsicProtectedBlock factorTwoIntrinsicEnergy
    factorTwoIntrinsicPotentialEnergy
  nlinarith

/-- Above arbitrary even and odd Legendre gaps, the phase retains `theta` of
the positive weighted singular operator.  The displayed complementary
coefficients are exact: at `theta = 0` this recovers the general-gap scalar
reserve, while positive `theta` makes the singular Cauchy inequality
available for low--tail completion.

Only `theta ≤ 1` is needed for the lower bound.  The additional
`0 ≤ theta` hypothesis records precisely when the retained singular term is
itself a positive quadratic form. -/
theorem factorTwoEndpointChannelPhase_general_gap_retain_singular
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (kE kO : ℕ)
    (heLow : centeredLegendreMomentsVanishBelow e kE)
    (hoLow : centeredLegendreMomentsVanishBelow o kO)
    (a b theta : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (_htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    theta * ((1 / 2 : ℝ) *
        factorTwoPhaseSingularWeightedEnergy e o a b) +
      (((1 - theta) * (harmonic kE : ℝ) -
            factorTwoIntrinsicProjectedEvenRemainderLoss a b -
            ((1 + theta) / 2) * Real.log 2) *
          factorTwoIntrinsicEnergy e +
        ((1 - theta) * (harmonic kO : ℝ) -
            factorTwoIntrinsicProjectedOddRemainderLoss a b -
            ((1 + theta) / 2) * Real.log 2) *
          factorTwoIntrinsicEnergy o +
        ((1 - theta) / 2) *
          (factorTwoIntrinsicPotentialEnergy e +
            factorTwoIntrinsicPotentialEnergy o)) ≤
      factorTwoEndpointChannelPhase e o a b := by
  have heRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    e hec helocal kE heLow
  have hoRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    o hoc holocal kO hoLow
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    e o hec hoc helocal holocal a b hab
  have hremainder := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    e o hec hoc he ho he0 a b hab
  have hbase :
      (harmonic kE : ℝ) * factorTwoIntrinsicEnergy e +
          (harmonic kO : ℝ) * factorTwoIntrinsicEnergy o +
          (1 / 2 : ℝ) *
            (factorTwoIntrinsicPotentialEnergy e +
              factorTwoIntrinsicPotentialEnergy o) -
          (Real.log 2 / 2) *
            (factorTwoIntrinsicEnergy e + factorTwoIntrinsicEnergy o) ≤
        factorTwoIntrinsicProtectedBlock e o a b := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (sub_nonneg.mpr htheta1)
  have hsingular := half_singularWeightedEnergy_eq_protected_add_logMass
    e o hec hoc helocal holocal a b
  rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    e o hec hoc a b]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
