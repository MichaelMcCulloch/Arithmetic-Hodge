import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

noncomputable section

/-!
# Retained cutoff-eleven representers

The cutoff-eleven tail phase retains `1 / 64` of the positive singular Gram.
This module identifies the matching low--tail potential/pole polarization as
an exact pair of one-variable representers and subtracts it from the complete
low--tail representer.  The result is the precise row that must be charged to
the remaining multiplication reserve.
-/

/-- Even representer of the potential plus reflected-pole polarization. -/
def factorTwoIntrinsicElevenPotentialPoleEvenRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  yoshidaEndpointPotential x * centeredPolynomialLift pE x +
    factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b x

/-- Odd representer of the potential plus reflected-pole polarization. -/
def factorTwoIntrinsicElevenPotentialPoleOddRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  yoshidaEndpointPotential x * centeredPolynomialLift pO x +
    factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b x

/-- Complete even representer after removing an arbitrary coefficient of
the potential/reflected-pole polarization. -/
def factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    (gamma : ℝ) (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b x -
    gamma *
      factorTwoIntrinsicElevenPotentialPoleEvenRepresenter pE pO a b x

/-- Complete odd representer after removing an arbitrary coefficient of
the potential/reflected-pole polarization. -/
def factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
    (gamma : ℝ) (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b x -
    gamma *
      factorTwoIntrinsicElevenPotentialPoleOddRepresenter pE pO a b x

/-- Complete even representer after spending `1 / 64` of the singular Gram. -/
def factorTwoIntrinsicElevenRetainedEvenMixedRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b x -
    (1 / 64 : ℝ) *
      factorTwoIntrinsicElevenPotentialPoleEvenRepresenter pE pO a b x

/-- Complete odd representer after spending `1 / 64` of the singular Gram. -/
def factorTwoIntrinsicElevenRetainedOddMixedRepresenter
    (pE pO : ℝ[X]) (a b : ℝ) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b x -
    (1 / 64 : ℝ) *
      factorTwoIntrinsicElevenPotentialPoleOddRepresenter pE pO a b x

private theorem continuous_centeredPolynomialLift_retained (p : ℝ[X]) :
    Continuous (centeredPolynomialLift p) := by
  unfold centeredPolynomialLift
  fun_prop

theorem intervalIntegrable_potentialPoleEvenRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenPotentialPoleEvenRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hP := continuous_centeredPolynomialLift_retained pE
  have hV : IntervalIntegrable (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredPolynomialLift pE x * r x)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul
      (centeredPolynomialLift pE) r hP hr
  have hR := intervalIntegrable_reflectedEvenRepresenter_mul
    pE pO r hr a b
  apply (hV.add hR).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenPotentialPoleEvenRepresenter
  ring

theorem intervalIntegrable_potentialPoleOddRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenPotentialPoleOddRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hP := continuous_centeredPolynomialLift_retained pO
  have hV : IntervalIntegrable (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredPolynomialLift pO x * r x)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul
      (centeredPolynomialLift pO) r hP hr
  have hR := intervalIntegrable_reflectedOddRepresenter_mul
    pE pO r hr a b
  apply (hV.add hR).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenPotentialPoleOddRepresenter
  ring

/-- The potential and reflected-pole low--tail polarization is exactly its
two-channel representer pairing. -/
theorem factorTwoPhasePotentialPoleMixed_centeredPolynomialLift_eq_pairing
    (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o)
    (heGap : centeredLegendreMomentsVanishBelow e 11)
    (hoGap : centeredLegendreMomentsVanishBelow o 11)
    (hpEdeg : pE.natDegree < 11) (hpOdeg : pO.natDegree < 11)
    (a b : ℝ) :
    factorTwoPhasePotentialPoleMixed
        (centeredPolynomialLift pE) (centeredPolynomialLift pO)
        e o a b =
      factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenPotentialPoleEvenRepresenter pE pO a b)
        (factorTwoIntrinsicElevenPotentialPoleOddRepresenter pE pO a b)
        e o := by
  have hPE := continuous_centeredPolynomialLift_retained pE
  have hPO := continuous_centeredPolynomialLift_retained pO
  have hVE : IntervalIntegrable (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredPolynomialLift pE x * e x)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul
      (centeredPolynomialLift pE) e hPE he
  have hVO : IntervalIntegrable (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredPolynomialLift pO x * o x)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul
      (centeredPolynomialLift pO) o hPO ho
  have hRE := intervalIntegrable_reflectedEvenRepresenter_mul
    pE pO e he a b
  have hRO := intervalIntegrable_reflectedOddRepresenter_mul
    pE pO o ho a b
  have hReflected := factorTwoIntrinsicElevenReflectedMixed_eq_pairing
    pE pO e o he ho heGap hoGap hpEdeg hpOdeg a b
  have hPairing :
      factorTwoIntrinsicElevenMixedPairing
          (factorTwoIntrinsicElevenPotentialPoleEvenRepresenter pE pO a b)
          (factorTwoIntrinsicElevenPotentialPoleOddRepresenter pE pO a b)
          e o =
        (∫ x : ℝ in -1..1,
            yoshidaEndpointPotential x * centeredPolynomialLift pE x * e x) +
          (∫ x : ℝ in -1..1,
            yoshidaEndpointPotential x * centeredPolynomialLift pO x * o x) +
          factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b)
            (factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b)
            e o := by
    unfold factorTwoIntrinsicElevenMixedPairing
      factorTwoIntrinsicElevenPotentialPoleEvenRepresenter
      factorTwoIntrinsicElevenPotentialPoleOddRepresenter
    rw [show (fun x : ℝ ↦
        (yoshidaEndpointPotential x * centeredPolynomialLift pE x +
          factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b x) *
            e x) = fun x ↦
        yoshidaEndpointPotential x * centeredPolynomialLift pE x * e x +
          factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b x * e x by
      funext x
      ring,
      intervalIntegral.integral_add hVE hRE,
      show (fun x : ℝ ↦
        (yoshidaEndpointPotential x * centeredPolynomialLift pO x +
          factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b x) *
            o x) = fun x ↦
        yoshidaEndpointPotential x * centeredPolynomialLift pO x * o x +
          factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b x * o x by
      funext x
      ring,
      intervalIntegral.integral_add hVO hRO]
    ring
  calc
    factorTwoPhasePotentialPoleMixed
        (centeredPolynomialLift pE) (centeredPolynomialLift pO)
        e o a b =
      (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredPolynomialLift pE x * e x) +
        (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredPolynomialLift pO x * o x) +
        factorTwoIntrinsicElevenReflectedMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          e o a b := by
      unfold factorTwoPhasePotentialPoleMixed
        factorTwoIntrinsicElevenReflectedMixed
      ring
    _ = (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredPolynomialLift pE x * e x) +
        (∫ x : ℝ in -1..1,
          yoshidaEndpointPotential x * centeredPolynomialLift pO x * o x) +
        factorTwoIntrinsicElevenMixedPairing
          (factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b)
          (factorTwoIntrinsicElevenReflectedOddRepresenter pE pO a b)
          e o := by rw [hReflected]
    _ = _ := hPairing.symm

/-- Bilinearity of the two-channel pairing under subtraction of a common
scalar multiple. -/
theorem factorTwoIntrinsicElevenMixedPairing_sub_const_mul
    (FE FO GE GO e o : ℝ → ℝ) (c : ℝ)
    (hFE : IntervalIntegrable (fun x ↦ FE x * e x) volume (-1) 1)
    (hGE : IntervalIntegrable (fun x ↦ GE x * e x) volume (-1) 1)
    (hFO : IntervalIntegrable (fun x ↦ FO x * o x) volume (-1) 1)
    (hGO : IntervalIntegrable (fun x ↦ GO x * o x) volume (-1) 1) :
    factorTwoIntrinsicElevenMixedPairing
        (fun x ↦ FE x - c * GE x) (fun x ↦ FO x - c * GO x) e o =
      factorTwoIntrinsicElevenMixedPairing FE FO e o -
        c * factorTwoIntrinsicElevenMixedPairing GE GO e o := by
  unfold factorTwoIntrinsicElevenMixedPairing
  rw [show (fun x : ℝ ↦ (FE x - c * GE x) * e x) = fun x ↦
      FE x * e x - c * (GE x * e x) by
    funext x
    ring,
    intervalIntegral.integral_sub hFE (hGE.const_mul c),
    show (fun x : ℝ ↦ (FO x - c * GO x) * o x) = fun x ↦
      FO x * o x - c * (GO x * o x) by
    funext x
    ring,
    intervalIntegral.integral_sub hFO (hGO.const_mul c)]
  repeat rw [intervalIntegral.integral_const_mul]
  ring

theorem intervalIntegrable_retainedEvenRepresenterAt_mul
    (gamma : ℝ) (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r)
    (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        gamma pE pO a b x * r x) volume (-1) 1 := by
  have hF := intervalIntegrable_completeEvenRepresenter_mul pE pO r hr a b
  have hP := intervalIntegrable_potentialPoleEvenRepresenter_mul
    pE pO r hr a b
  apply (hF.sub (hP.const_mul gamma)).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
  ring

theorem intervalIntegrable_retainedOddRepresenterAt_mul
    (gamma : ℝ) (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r)
    (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        gamma pE pO a b x * r x) volume (-1) 1 := by
  have hF := intervalIntegrable_completeOddRepresenter_mul pE pO r hr a b
  have hP := intervalIntegrable_potentialPoleOddRepresenter_mul
    pE pO r hr a b
  apply (hF.sub (hP.const_mul gamma)).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
  ring

/-- Removing any scalar multiple of the potential/reflected-pole row is
exactly represented by the correspondingly parameterized cutoff-eleven
representers. -/
theorem factorTwoEndpointLowTailMixed_sub_potentialPole_eq_pairing
    (gamma : ℝ) (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heGap : centeredLegendreMomentsVanishBelow e 11)
    (hoGap : centeredLegendreMomentsVanishBelow o 11)
    (hpEdeg : pE.natDegree < 11) (hpOdeg : pO.natDegree < 11)
    (a b : ℝ) :
    factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) e
          (centeredPolynomialLift pO) o a b -
        gamma * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          e o a b =
      factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
          gamma pE pO a b)
        (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
          gamma pE pO a b)
        e o := by
  have hComplete :=
    factorTwoEndpointLowTailMixed_centeredPolynomialLift_eq_intrinsicElevenPairing
      pE pO e o he ho heLocal hoLocal heGap hoGap hpEdeg hpOdeg a b
  have hPole := factorTwoPhasePotentialPoleMixed_centeredPolynomialLift_eq_pairing
    pE pO e o he ho heGap hoGap hpEdeg hpOdeg a b
  have hFE := intervalIntegrable_completeEvenRepresenter_mul pE pO e he a b
  have hFO := intervalIntegrable_completeOddRepresenter_mul pE pO o ho a b
  have hPE := intervalIntegrable_potentialPoleEvenRepresenter_mul
    pE pO e he a b
  have hPO := intervalIntegrable_potentialPoleOddRepresenter_mul
    pE pO o ho a b
  have hLinear := factorTwoIntrinsicElevenMixedPairing_sub_const_mul
    (factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b)
    (factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b)
    (factorTwoIntrinsicElevenPotentialPoleEvenRepresenter pE pO a b)
    (factorTwoIntrinsicElevenPotentialPoleOddRepresenter pE pO a b)
    e o gamma hFE hPE hFO hPO
  rw [hComplete, hPole]
  simpa only [factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt,
    factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt] using hLinear.symm

theorem intervalIntegrable_retainedEvenRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenRetainedEvenMixedRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hF := intervalIntegrable_completeEvenRepresenter_mul pE pO r hr a b
  have hP := intervalIntegrable_potentialPoleEvenRepresenter_mul
    pE pO r hr a b
  apply (hF.sub (hP.const_mul (1 / 64 : ℝ))).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenRetainedEvenMixedRepresenter
  ring

theorem intervalIntegrable_retainedOddRepresenter_mul
    (pE pO : ℝ[X]) (r : ℝ → ℝ) (hr : Continuous r) (a b : ℝ) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenRetainedOddMixedRepresenter pE pO a b x * r x)
      volume (-1) 1 := by
  have hF := intervalIntegrable_completeOddRepresenter_mul pE pO r hr a b
  have hP := intervalIntegrable_potentialPoleOddRepresenter_mul
    pE pO r hr a b
  apply (hF.sub (hP.const_mul (1 / 64 : ℝ))).congr
  intro x _hx
  unfold factorTwoIntrinsicElevenRetainedOddMixedRepresenter
  ring

/-- After retaining `1 / 64` of the singular Gram, the remaining low--tail
row is exactly the pairing with the retained representers. -/
theorem factorTwoEndpointLowTailMixed_sub_one_div_sixty_four_potentialPole_eq_pairing
    (pE pO : ℝ[X]) (e o : ℝ → ℝ)
    (he : Continuous e) (ho : Continuous o)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heGap : centeredLegendreMomentsVanishBelow e 11)
    (hoGap : centeredLegendreMomentsVanishBelow o 11)
    (hpEdeg : pE.natDegree < 11) (hpOdeg : pO.natDegree < 11)
    (a b : ℝ) :
    factorTwoEndpointLowTailMixed
          (centeredPolynomialLift pE) e
          (centeredPolynomialLift pO) o a b -
        (1 / 64 : ℝ) * factorTwoPhasePotentialPoleMixed
          (centeredPolynomialLift pE) (centeredPolynomialLift pO)
          e o a b =
      factorTwoIntrinsicElevenMixedPairing
        (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter pE pO a b)
        (factorTwoIntrinsicElevenRetainedOddMixedRepresenter pE pO a b)
        e o := by
  have hComplete :=
    factorTwoEndpointLowTailMixed_centeredPolynomialLift_eq_intrinsicElevenPairing
      pE pO e o he ho heLocal hoLocal heGap hoGap hpEdeg hpOdeg a b
  have hPole := factorTwoPhasePotentialPoleMixed_centeredPolynomialLift_eq_pairing
    pE pO e o he ho heGap hoGap hpEdeg hpOdeg a b
  have hFE := intervalIntegrable_completeEvenRepresenter_mul pE pO e he a b
  have hFO := intervalIntegrable_completeOddRepresenter_mul pE pO o ho a b
  have hPE := intervalIntegrable_potentialPoleEvenRepresenter_mul
    pE pO e he a b
  have hPO := intervalIntegrable_potentialPoleOddRepresenter_mul
    pE pO o ho a b
  have hLinear := factorTwoIntrinsicElevenMixedPairing_sub_const_mul
    (factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b)
    (factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b)
    (factorTwoIntrinsicElevenPotentialPoleEvenRepresenter pE pO a b)
    (factorTwoIntrinsicElevenPotentialPoleOddRepresenter pE pO a b)
    e o (1 / 64 : ℝ) hFE hPE hFO hPO
  rw [hComplete, hPole]
  simpa only [factorTwoIntrinsicElevenRetainedEvenMixedRepresenter,
    factorTwoIntrinsicElevenRetainedOddMixedRepresenter] using hLinear.symm

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
