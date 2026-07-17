import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularReserveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRetainedSingularSchurStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularSchurStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenStructuralReduction
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularReserveStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseRetainedSingularSchurStructural
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

noncomputable section

/-!
# Cutoff-eleven retained-singular Schur handoff

For a transported polynomial low block and a moment-gap-eleven residual,
raw logarithmic and ordinary `L²` orthogonality are automatic.  This module
instantiates the retained-singular Schur theorem with those exact identities
and with the unconditional `1 / 64` tail reserve.
-/

theorem contDiff_centeredPolynomialLift (p : ℝ[X]) :
    ContDiff ℝ 1 (centeredPolynomialLift p) := by
  have hp : ContDiff ℝ 1 (fun y : ℝ ↦ p.eval y) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      p.contDiff_aeval (𝕜 := ℝ) 1
  have haff : ContDiff ℝ 1 (fun x : ℝ ↦ (x + 1) / 2) := by
    fun_prop
  simpa only [centeredPolynomialLift, Function.comp_apply] using hp.comp haff

theorem continuous_centeredPolynomialLift (p : ℝ[X]) :
    Continuous (centeredPolynomialLift p) :=
  (contDiff_centeredPolynomialLift p).continuous

theorem locallyLipschitzOn_centeredPolynomialLift (p : ℝ[X]) :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) (centeredPolynomialLift p) :=
  (contDiff_centeredPolynomialLift p).locallyLipschitz.locallyLipschitzOn

/-- The retained-singular low--tail determinant at cutoff eleven.  All
orthogonality and tail-reserve obligations are discharged structurally; the
remaining hypotheses are exactly the finite-low complement and its weighted
selector estimate. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retain_one_div_sixty_four
    (pE pO : ℝ[X]) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heR : Function.Even eR) (hoR : Function.Odd oR)
    (heR0 : centeredEvenP0Coefficient eR = 0)
    (heRlocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoRlocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 11)
    (hoGap : centeredLegendreMomentsVanishBelow oR 11)
    (hpE : pE.natDegree < 11) (hpO : pO.natDegree < 11)
    (a b lowComplement : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hlowComplement : 0 ≤ lowComplement)
    (hlowRetains :
      (1 / 64 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) +
        lowComplement ≤
          factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b)
    (hremaining :
      (factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) eR
          (centeredPolynomialLift pO) oR a b -
        (1 / 64 : ℝ) * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b) ^ 2 ≤
        lowComplement *
          factorTwoIntrinsicElevenRetainedWeightedReserve eR oR) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) eR
        (centeredPolynomialLift pO) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  have heLowc := continuous_centeredPolynomialLift pE
  have hoLowc := continuous_centeredPolynomialLift pO
  have heLowLocal := locallyLipschitzOn_centeredPolynomialLift pE
  have hoLowLocal := locallyLipschitzOn_centeredPolynomialLift pO
  have heRaw := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    pE eR heRc heRlocal heGap hpE
  have hoRaw := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    pO oR hoRc hoRlocal hoGap hpO
  have heOrth := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    pE eR heRc heGap hpE
  have hoOrth := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    pO oR hoRc hoGap hpO
  have htailComplement :=
    factorTwoIntrinsicElevenRetainedWeightedReserve_nonneg eR oR
  have htailRetains :=
    factorTwoEndpointChannelPhase_gap_eleven_retain_one_div_sixty_four
      eR oR heRc hoRc heR hoR heR0 heRlocal hoRlocal
        heGap hoGap a b hab
  exact factorTwoEndpointLowTailMixed_sq_le_of_retained_singular
    (centeredPolynomialLift pE) (centeredPolynomialLift pO) eR oR
      heLowc hoLowc heRc hoRc
      heLowLocal hoLowLocal heRlocal hoRlocal
      a b (1 / 64 : ℝ) lowComplement
      (factorTwoIntrinsicElevenRetainedWeightedReserve eR oR)
      hab (by norm_num) heRaw hoRaw heOrth hoOrth
      hlowComplement htailComplement hlowRetains htailRetains hremaining

/-- Asymmetric cutoff-eleven Schur handoff.  The low block retains `1 / 1024`
of the half singular energy, the tail retains its unconditional `1 / 64`, and
`1 / 256` of the pole row is removed.  These coefficients saturate the exact
geometric-mean condition `(1 / 256)² = (1 / 1024) * (1 / 64)`. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retain_one_div_one_thousand_twenty_four
    (pE pO : ℝ[X]) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heR : Function.Even eR) (hoR : Function.Odd oR)
    (heR0 : centeredEvenP0Coefficient eR = 0)
    (heRlocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoRlocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 11)
    (hoGap : centeredLegendreMomentsVanishBelow oR 11)
    (hpE : pE.natDegree < 11) (hpO : pO.natDegree < 11)
    (a b lowComplement : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hlowComplement : 0 ≤ lowComplement)
    (hlowRetains :
      (1 / 1024 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) +
        lowComplement ≤
          factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b)
    (hremaining :
      (factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) eR
          (centeredPolynomialLift pO) oR a b -
        (1 / 256 : ℝ) * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b) ^ 2 ≤
        lowComplement *
          factorTwoIntrinsicElevenRetainedWeightedReserve eR oR) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) eR
        (centeredPolynomialLift pO) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  have heLowc := continuous_centeredPolynomialLift pE
  have hoLowc := continuous_centeredPolynomialLift pO
  have heLowLocal := locallyLipschitzOn_centeredPolynomialLift pE
  have hoLowLocal := locallyLipschitzOn_centeredPolynomialLift pO
  have heRaw := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    pE eR heRc heRlocal heGap hpE
  have hoRaw := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    pO oR hoRc hoRlocal hoGap hpO
  have heOrth := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    pE eR heRc heGap hpE
  have hoOrth := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    pO oR hoRc hoGap hpO
  have htailComplement :=
    factorTwoIntrinsicElevenRetainedWeightedReserve_nonneg eR oR
  have htailRetains :=
    factorTwoEndpointChannelPhase_gap_eleven_retain_one_div_sixty_four
      eR oR heRc hoRc heR hoR heR0 heRlocal hoRlocal
        heGap hoGap a b hab
  exact
    factorTwoEndpointLowTailMixed_sq_le_of_asymmetrically_retained_singular
    (centeredPolynomialLift pE) (centeredPolynomialLift pO) eR oR
      heLowc hoLowc heRc hoRc
      heLowLocal hoLowLocal heRlocal hoRlocal
      a b (1 / 1024 : ℝ) (1 / 64 : ℝ) (1 / 256 : ℝ) lowComplement
      (factorTwoIntrinsicElevenRetainedWeightedReserve eR oR)
      hab (by norm_num) (by norm_num) (by norm_num)
      heRaw hoRaw heOrth hoOrth
      hlowComplement htailComplement hlowRetains htailRetains hremaining

/-- Retuned asymmetric cutoff-eleven Schur handoff.  The low block retains
`1 / 2048` of the half singular energy, the tail keeps its unconditional
`1 / 64` reserve, and `1 / 512` of the pole row is removed.  The geometric
condition has slack:
`(1 / 512)^2 ≤ (1 / 2048) * (1 / 64)`. -/
theorem factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_retain_one_div_two_thousand_forty_eight
    (pE pO : ℝ[X]) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heR : Function.Even eR) (hoR : Function.Odd oR)
    (heR0 : centeredEvenP0Coefficient eR = 0)
    (heRlocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoRlocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 11)
    (hoGap : centeredLegendreMomentsVanishBelow oR 11)
    (hpE : pE.natDegree < 11) (hpO : pO.natDegree < 11)
    (a b lowComplement : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hlowComplement : 0 ≤ lowComplement)
    (hlowRetains :
      (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b) +
        lowComplement ≤
          factorTwoEndpointChannelPhase
            (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b)
    (hremaining :
      (factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) eR
          (centeredPolynomialLift pO) oR a b -
        (1 / 512 : ℝ) * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          eR oR a b) ^ 2 ≤
        lowComplement *
          factorTwoIntrinsicElevenRetainedWeightedReserve eR oR) :
    factorTwoEndpointLowTailMixed
        (centeredPolynomialLift pE) eR
        (centeredPolynomialLift pO) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredPolynomialLift pE) (centeredPolynomialLift pO) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  have heLowc := continuous_centeredPolynomialLift pE
  have hoLowc := continuous_centeredPolynomialLift pO
  have heLowLocal := locallyLipschitzOn_centeredPolynomialLift pE
  have hoLowLocal := locallyLipschitzOn_centeredPolynomialLift pO
  have heRaw := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    pE eR heRc heRlocal heGap hpE
  have hoRaw := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    pO oR hoRc hoRlocal hoGap hpO
  have heOrth := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    pE eR heRc heGap hpE
  have hoOrth := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    pO oR hoRc hoGap hpO
  have htailComplement :=
    factorTwoIntrinsicElevenRetainedWeightedReserve_nonneg eR oR
  have htailRetains :=
    factorTwoEndpointChannelPhase_gap_eleven_retain_one_div_sixty_four
      eR oR heRc hoRc heR hoR heR0 heRlocal hoRlocal
        heGap hoGap a b hab
  exact
    factorTwoEndpointLowTailMixed_sq_le_of_asymmetrically_retained_singular
      (centeredPolynomialLift pE) (centeredPolynomialLift pO) eR oR
      heLowc hoLowc heRc hoRc
      heLowLocal hoLowLocal heRlocal hoRlocal
      a b (1 / 2048 : ℝ) (1 / 64 : ℝ) (1 / 512 : ℝ) lowComplement
      (factorTwoIntrinsicElevenRetainedWeightedReserve eR oR)
      hab (by norm_num) (by norm_num) (by norm_num)
      heRaw hoRaw heOrth hoOrth
      hlowComplement htailComplement hlowRetains htailRetains hremaining

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularSchurStructural
