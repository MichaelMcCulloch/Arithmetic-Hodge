import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderDecompositionStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural

noncomputable section

open ShiftedLegendreBasis
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural

/-!
# One complete representer for the direct `P6` border

The direct cutoff-six border is kept as a single pairing before any norm
estimate is made.  The assembled cutoff-eleven representer supplies every
clean, analytic, forward, reflected, and retained-prime row.  The sole
cutoff-six polynomial remainder is the exact `P0`--`P6` rank-one term.
-/

/-- The first three direct coordinates as a transported polynomial. -/
def factorTwoIntrinsicNineDirectP024Polynomial
    (x : Fin 6 → ℝ) : ℝ[X] :=
  factorTwoIntrinsicNineEvenPolynomial (x 0) (x 1) (x 2) 0 0

/-- The last three core coordinates as a transported polynomial. -/
def factorTwoIntrinsicNineDirectP135Polynomial
    (x : Fin 6 → ℝ) : ℝ[X] :=
  factorTwoIntrinsicNineOddPolynomial (x 3) (x 4) (x 5) 0

/-- Transporting the direct even polynomial gives its exact endpoint
profile. -/
theorem centeredPolynomialLift_directP024Polynomial
    (x : Fin 6 → ℝ) :
    centeredPolynomialLift (factorTwoIntrinsicNineDirectP024Polynomial x) =
      factorTwoIntrinsicNineDirectP024Profile x := by
  rw [factorTwoIntrinsicNineDirectP024Polynomial,
    centeredPolynomialLift_intrinsicNineEvenPolynomial]
  funext t
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
    factorTwoIntrinsicNineDirectP024Profile factorTwoIntrinsicSixEvenTail
  simp only [Pi.add_apply]
  ring

/-- Transporting the direct odd polynomial gives its exact endpoint
profile. -/
theorem centeredPolynomialLift_directP135Polynomial
    (x : Fin 6 → ℝ) :
    centeredPolynomialLift (factorTwoIntrinsicNineDirectP135Polynomial x) =
      factorTwoIntrinsicNineDirectP135Profile x := by
  rw [factorTwoIntrinsicNineDirectP135Polynomial,
    centeredPolynomialLift_intrinsicNineOddPolynomial]
  funext t
  unfold factorTwoIntrinsicNineOddProfile factorTwoIntrinsicEightOddProfile
    factorTwoIntrinsicNineDirectP135Profile
  simp only [Pi.add_apply]
  ring

theorem factorTwoIntrinsicNineDirectP024Polynomial_natDegree_lt_six
    (x : Fin 6 → ℝ) :
    (factorTwoIntrinsicNineDirectP024Polynomial x).natDegree < 6 := by
  unfold factorTwoIntrinsicNineDirectP024Polynomial
    factorTwoIntrinsicNineEvenPolynomial
  simp only [zero_smul, add_zero]
  have hdeg : ((x 0) • shiftedLegendreReal 0 +
      (x 1) • shiftedLegendreReal 2 +
      (x 2) • shiftedLegendreReal 4).natDegree ≤ 4 := by
    compute_degree
  omega

theorem factorTwoIntrinsicNineDirectP135Polynomial_natDegree_lt_six
    (x : Fin 6 → ℝ) :
    (factorTwoIntrinsicNineDirectP135Polynomial x).natDegree < 6 := by
  unfold factorTwoIntrinsicNineDirectP135Polynomial
    factorTwoIntrinsicNineOddPolynomial
  simp only [neg_zero, zero_smul, add_zero]
  have hdeg : ((-(x 3)) • shiftedLegendreReal 1 +
      (-(x 4)) • shiftedLegendreReal 3 +
      (-(x 5)) • shiftedLegendreReal 5).natDegree ≤ 5 := by
    compute_degree
  omega

/-- The exact polynomial boundary rank which must be retained alongside the
complete singular representer. -/
def factorTwoIntrinsicNineDirectP6RankRepresenter
    (a : ℝ) (x : Fin 6 → ℝ) (z : ℝ) : ℝ :=
  a * poleFreeCoeff6 yoshidaEndpointA * (16 / 231 : ℝ) * x 0 *
    factorTwoCenteredP6 z

/-- The normalization `16/231` pairs with `∫ P6² = 2/13` to recover the
exact `32/3003` matrix-row coefficient. -/
theorem integral_factorTwoIntrinsicNineDirectP6RankRepresenter_mul_P6
    (a : ℝ) (x : Fin 6 → ℝ) :
    (∫ z : ℝ in -1..1,
      factorTwoIntrinsicNineDirectP6RankRepresenter a x z *
        factorTwoCenteredP6 z) =
      a * poleFreeCoeff6 yoshidaEndpointA * (32 / 3003 : ℝ) * x 0 := by
  unfold factorTwoIntrinsicNineDirectP6RankRepresenter
  rw [show (fun z : ℝ ↦
      (a * poleFreeCoeff6 yoshidaEndpointA * (16 / 231 : ℝ) *
          x 0 * factorTwoCenteredP6 z) * factorTwoCenteredP6 z) =
    fun z ↦
      (a * poleFreeCoeff6 yoshidaEndpointA * (16 / 231 : ℝ) * x 0) *
        factorTwoCenteredP6 z ^ 2 by
      funext z
      ring,
    intervalIntegral.integral_const_mul,
    integral_factorTwoCenteredP6_sq]
  ring

/-- Every analytic family in the `P6` row, including the retained prime lag,
is kept inside this one function before applying Cauchy--Schwarz. -/
def factorTwoIntrinsicNineDirectP6WholeRepresenter
    (a b : ℝ) (x : Fin 6 → ℝ) (z : ℝ) : ℝ :=
  factorTwoIntrinsicElevenEvenMixedRepresenter
      (factorTwoIntrinsicNineDirectP024Polynomial x)
      (factorTwoIntrinsicNineDirectP135Polynomial x) a b z +
    factorTwoIntrinsicNineDirectP6RankRepresenter a x z

/-- The complete direct `P6` matrix row is exactly one `L²` pairing with
`P6`.  No triangle inequality or termwise absolute-value estimate enters. -/
theorem factorTwoIntrinsicNineDirectP6BorderFunctional_eq_wholeRepresenterPairing
    (a b : ℝ) (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectP6BorderFunctional a b x =
      ∫ z : ℝ in -1..1,
        factorTwoIntrinsicNineDirectP6WholeRepresenter a b x z *
          factorTwoCenteredP6 z := by
  let pE := factorTwoIntrinsicNineDirectP024Polynomial x
  let pO := factorTwoIntrinsicNineDirectP135Polynomial x
  have hpEdeg : pE.natDegree < 6 := by
    simpa only [pE] using
      factorTwoIntrinsicNineDirectP024Polynomial_natDegree_lt_six x
  have hpOdeg : pO.natDegree < 6 := by
    simpa only [pO] using
      factorTwoIntrinsicNineDirectP135Polynomial_natDegree_lt_six x
  have hzeroLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (0 : ℝ → ℝ) := by
    have hdiff : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    exact hdiff.locallyLipschitz.locallyLipschitzOn
  have hzeroGap : centeredLegendreMomentsVanishBelow
      (0 : ℝ → ℝ) 6 := by
    intro n hn
    simp [centeredPullback]
  have hNormal :=
    factorTwoIntrinsicNineDirectP6BorderFunctional_eq_complete_normalForm
      a b x
  have hLiftE : centeredPolynomialLift pE =
      factorTwoIntrinsicNineDirectP024Profile x := by
    simpa only [pE] using centeredPolynomialLift_directP024Polynomial x
  have hLiftO : centeredPolynomialLift pO =
      factorTwoIntrinsicNineDirectP135Profile x := by
    simpa only [pO] using centeredPolynomialLift_directP135Polynomial x
  rw [← hLiftE, ← hLiftO] at hNormal
  have hAnalytic :=
    factorTwoP67ResidualAnalyticMixed_eq_intrinsicElevenPairing
      pE pO factorTwoCenteredP6 (0 : ℝ → ℝ)
      continuous_factorTwoCenteredP6 continuous_zero a b
  have hForward :=
    factorTwoP67ResidualForwardHankelMixed_eq_intrinsicElevenPairing
      pE pO factorTwoCenteredP6 (0 : ℝ → ℝ)
      continuous_factorTwoCenteredP6 continuous_zero
      factorTwoCenteredP6_momentsVanishBelow hzeroGap hpEdeg hpOdeg a b
  have hClean :=
    factorTwoIntrinsicNineNonpolynomialMixed_zero_eq_cleanPairing
      pE pO factorTwoCenteredP6 (0 : ℝ → ℝ)
      continuous_factorTwoCenteredP6 continuous_zero
      locallyLipschitzOn_factorTwoCenteredP6 hzeroLocal
      factorTwoCenteredP6_momentsVanishBelow hzeroGap hpEdeg hpOdeg
  have hNonpolynomial :=
    factorTwoIntrinsicNineNonpolynomialMixed_eq_zero_add_reflected_add_prime
      (centeredPolynomialLift pE) (centeredPolynomialLift pO)
      factorTwoCenteredP6 (0 : ℝ → ℝ) a b
  have hReflected := factorTwoIntrinsicElevenReflectedMixed_eq_pairing
    pE pO factorTwoCenteredP6 (0 : ℝ → ℝ)
    continuous_factorTwoCenteredP6 continuous_zero
    factorTwoCenteredP6_momentsVanishBelow hzeroGap hpEdeg hpOdeg a b
  have hPrime := factorTwoIntrinsicElevenPrimeMixed_eq_pairing
    pE pO factorTwoCenteredP6 (0 : ℝ → ℝ)
    continuous_factorTwoCenteredP6 continuous_zero a b
  have hComplete :=
    factorTwoIntrinsicElevenMixedPairing_complete_eq_components
      pE pO factorTwoCenteredP6 (0 : ℝ → ℝ)
      continuous_factorTwoCenteredP6 continuous_zero a b
  have hBase :
      factorTwoIntrinsicNineDirectP6BorderFunctional a b x =
        factorTwoIntrinsicElevenMixedPairing
            (factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b)
            (factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b)
            factorTwoCenteredP6 (0 : ℝ → ℝ) +
          a * poleFreeCoeff6 yoshidaEndpointA *
            (32 / 3003 : ℝ) * x 0 := by
    calc
      factorTwoIntrinsicNineDirectP6BorderFunctional a b x =
          factorTwoP67ResidualAnalyticMixed
              (centeredPolynomialLift pE) (centeredPolynomialLift pO)
              factorTwoCenteredP6 (0 : ℝ → ℝ) a b +
            factorTwoP67ResidualForwardHankelMixed
              (centeredPolynomialLift pE) (centeredPolynomialLift pO)
              factorTwoCenteredP6 (0 : ℝ → ℝ) a b +
            a * poleFreeCoeff6 yoshidaEndpointA *
              (32 / 3003 : ℝ) * x 0 +
            factorTwoIntrinsicNineNonpolynomialMixed
              (centeredPolynomialLift pE) (centeredPolynomialLift pO)
              factorTwoCenteredP6 (0 : ℝ → ℝ) a b := hNormal
      _ = factorTwoIntrinsicElevenMixedPairing
              (factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b)
              (factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b)
              factorTwoCenteredP6 (0 : ℝ → ℝ) +
            a * poleFreeCoeff6 yoshidaEndpointA *
              (32 / 3003 : ℝ) * x 0 := by
        rw [hAnalytic, hForward, hNonpolynomial, hClean, hReflected, hPrime,
          hComplete]
        ring
  have hPairing :
      factorTwoIntrinsicElevenMixedPairing
          (factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b)
          (factorTwoIntrinsicElevenOddMixedRepresenter pE pO a b)
          factorTwoCenteredP6 (0 : ℝ → ℝ) =
        ∫ z : ℝ in -1..1,
          factorTwoIntrinsicElevenEvenMixedRepresenter pE pO a b z *
            factorTwoCenteredP6 z := by
    unfold factorTwoIntrinsicElevenMixedPairing
    simp
  have hCompleteInt := intervalIntegrable_completeEvenRepresenter_mul
    pE pO factorTwoCenteredP6 continuous_factorTwoCenteredP6 a b
  have hRankInt : IntervalIntegrable (fun z : ℝ ↦
      factorTwoIntrinsicNineDirectP6RankRepresenter a x z *
        factorTwoCenteredP6 z) volume (-1) 1 := by
    have h : Continuous (fun z : ℝ ↦
        (a * poleFreeCoeff6 yoshidaEndpointA * (16 / 231 : ℝ) * x 0) *
          factorTwoCenteredP6 z * factorTwoCenteredP6 z) :=
      (continuous_const.mul continuous_factorTwoCenteredP6).mul
        continuous_factorTwoCenteredP6
    simpa only [factorTwoIntrinsicNineDirectP6RankRepresenter] using
      h.intervalIntegrable (μ := volume) (-1) 1
  rw [hBase, hPairing,
    ← integral_factorTwoIntrinsicNineDirectP6RankRepresenter_mul_P6 a x,
    ← intervalIntegral.integral_add hCompleteInt hRankInt]
  apply intervalIntegral.integral_congr
  intro z _hz
  unfold factorTwoIntrinsicNineDirectP6WholeRepresenter
  dsimp only [pE, pO]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural
