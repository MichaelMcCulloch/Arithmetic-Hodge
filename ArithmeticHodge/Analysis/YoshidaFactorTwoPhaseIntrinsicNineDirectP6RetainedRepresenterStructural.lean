import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6RetainedRepresenterStructural

noncomputable section

open ShiftedLegendreLogEnergyOrthogonalProjection
open UnitIntervalLogEnergyAffine
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

/-!
# The pole-subtracted direct `P6` row

The direct cutoff-six border has one complete coupled representer.  At the
same gap, the potential/reflected-pole polarization has its own exact
representer.  Subtracting the latter before Cauchy--Schwarz therefore leaves
one exact pole-free row; no triangle inequality or coordinatewise estimate is
introduced.
-/

/-- The potential/reflected-pole representer attached to a direct six-vector. -/
def factorTwoIntrinsicNineDirectP6PotentialPoleRepresenter
    (a b : ℝ) (x : Fin 6 → ℝ) (z : ℝ) : ℝ :=
  factorTwoIntrinsicElevenPotentialPoleEvenRepresenter
    (factorTwoIntrinsicNineDirectP024Polynomial x)
    (factorTwoIntrinsicNineDirectP135Polynomial x) a b z

/-- The complete direct `P6` row after removing an arbitrary fraction of its
potential/reflected-pole component. -/
def factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
    (gamma a b : ℝ) (x : Fin 6 → ℝ) (z : ℝ) : ℝ :=
  factorTwoIntrinsicNineDirectP6WholeRepresenter a b x z -
    gamma * factorTwoIntrinsicNineDirectP6PotentialPoleRepresenter a b x z

/-- At the actual cutoff-six gap, the potential/reflected-pole mixed row is
exactly the pairing of its one-variable representer with `P6`. -/
theorem factorTwoPhasePotentialPoleMixed_directP6_eq_pairing
    (a b : ℝ) (x : Fin 6 → ℝ) :
    factorTwoPhasePotentialPoleMixed
        (factorTwoIntrinsicNineDirectP024Profile x)
        (factorTwoIntrinsicNineDirectP135Profile x)
        factorTwoCenteredP6 (0 : ℝ → ℝ) a b =
      ∫ z : ℝ in -1..1,
        factorTwoIntrinsicNineDirectP6PotentialPoleRepresenter a b x z *
          factorTwoCenteredP6 z := by
  let pE := factorTwoIntrinsicNineDirectP024Polynomial x
  let pO := factorTwoIntrinsicNineDirectP135Polynomial x
  have hpEdeg : pE.natDegree < 6 := by
    simpa only [pE] using
      factorTwoIntrinsicNineDirectP024Polynomial_natDegree_lt_six x
  have hpOdeg : pO.natDegree < 6 := by
    simpa only [pO] using
      factorTwoIntrinsicNineDirectP135Polynomial_natDegree_lt_six x
  have hzeroGap : centeredLegendreMomentsVanishBelow
      (0 : ℝ → ℝ) 6 := by
    intro n hn
    simp [centeredPullback]
  have hPairing :=
    factorTwoPhasePotentialPoleMixed_centeredPolynomialLift_eq_pairing
      pE pO factorTwoCenteredP6 (0 : ℝ → ℝ)
      continuous_factorTwoCenteredP6 continuous_zero
      factorTwoCenteredP6_momentsVanishBelow hzeroGap hpEdeg hpOdeg a b
  have hLiftE : centeredPolynomialLift pE =
      factorTwoIntrinsicNineDirectP024Profile x := by
    simpa only [pE] using centeredPolynomialLift_directP024Polynomial x
  have hLiftO : centeredPolynomialLift pO =
      factorTwoIntrinsicNineDirectP135Profile x := by
    simpa only [pO] using centeredPolynomialLift_directP135Polynomial x
  rw [hLiftE, hLiftO] at hPairing
  simpa [factorTwoIntrinsicElevenMixedPairing,
    factorTwoIntrinsicNineDirectP6PotentialPoleRepresenter, pE, pO] using
      hPairing

/-- Exact subtraction of any potential-pole fraction from the direct `P6`
border.  The result remains a single `L²` pairing. -/
theorem factorTwoIntrinsicNineDirectP6BorderFunctional_sub_potentialPole_eq_pairing
    (gamma a b : ℝ) (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectP6BorderFunctional a b x -
        gamma * factorTwoPhasePotentialPoleMixed
          (factorTwoIntrinsicNineDirectP024Profile x)
          (factorTwoIntrinsicNineDirectP135Profile x)
          factorTwoCenteredP6 (0 : ℝ → ℝ) a b =
      ∫ z : ℝ in -1..1,
        factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
            gamma a b x z * factorTwoCenteredP6 z := by
  let pE := factorTwoIntrinsicNineDirectP024Polynomial x
  let pO := factorTwoIntrinsicNineDirectP135Polynomial x
  have hComplete := intervalIntegrable_completeEvenRepresenter_mul
    pE pO factorTwoCenteredP6 continuous_factorTwoCenteredP6 a b
  have hRank : IntervalIntegrable (fun z : ℝ ↦
      factorTwoIntrinsicNineDirectP6RankRepresenter a x z *
        factorTwoCenteredP6 z) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold factorTwoIntrinsicNineDirectP6RankRepresenter
    exact (continuous_const.mul continuous_factorTwoCenteredP6).mul
      continuous_factorTwoCenteredP6
  have hWhole : IntervalIntegrable (fun z : ℝ ↦
      factorTwoIntrinsicNineDirectP6WholeRepresenter a b x z *
        factorTwoCenteredP6 z) volume (-1) 1 := by
    apply (hComplete.add hRank).congr
    intro z _hz
    unfold factorTwoIntrinsicNineDirectP6WholeRepresenter
    dsimp only [pE, pO]
    ring
  have hPole := intervalIntegrable_potentialPoleEvenRepresenter_mul
    pE pO factorTwoCenteredP6 continuous_factorTwoCenteredP6 a b
  have hPole' : IntervalIntegrable (fun z : ℝ ↦
      factorTwoIntrinsicNineDirectP6PotentialPoleRepresenter a b x z *
        factorTwoCenteredP6 z) volume (-1) 1 := by
    simpa only [factorTwoIntrinsicNineDirectP6PotentialPoleRepresenter,
      pE, pO] using hPole
  rw [factorTwoIntrinsicNineDirectP6BorderFunctional_eq_wholeRepresenterPairing,
    factorTwoPhasePotentialPoleMixed_directP6_eq_pairing]
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_sub hWhole (hPole'.const_mul gamma)]
  apply intervalIntegral.integral_congr
  intro z _hz
  unfold factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
  ring

/-- The exact fraction matched to the `1/2048` low and `1/128` high singular
reserves remains a single pole-subtracted pairing. -/
theorem factorTwoIntrinsicNineDirectP6BorderFunctional_sub_one_div_512_potentialPole_eq_pairing
    (a b : ℝ) (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectP6BorderFunctional a b x -
        (1 / 512 : ℝ) * factorTwoPhasePotentialPoleMixed
          (factorTwoIntrinsicNineDirectP024Profile x)
          (factorTwoIntrinsicNineDirectP135Profile x)
          factorTwoCenteredP6 (0 : ℝ → ℝ) a b =
      ∫ z : ℝ in -1..1,
        factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
            (1 / 512 : ℝ) a b x z * factorTwoCenteredP6 z := by
  exact
    factorTwoIntrinsicNineDirectP6BorderFunctional_sub_potentialPole_eq_pairing
      (1 / 512 : ℝ) a b x

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6RetainedRepresenterStructural
