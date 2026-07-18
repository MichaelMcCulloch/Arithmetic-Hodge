import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP6BoundaryPolynomialStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderDecompositionStructural

open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseP6BoundaryPolynomialStructural
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural

noncomputable section

/-!
# Semantic decomposition of the direct `P6` border

The direct matrix border is first identified with the complete endpoint
low--tail mixed functional for the `P0/P2/P4` and `P1/P3/P5` profiles against
`P6`.  This keeps every analytic family coupled before the cutoff-six moment
cancellations are applied.
-/

/-- The first three direct coordinates as one even endpoint profile. -/
def factorTwoIntrinsicNineDirectP024Profile
    (x : Fin 6 → ℝ) : ℝ → ℝ :=
  factorTwoEvenStructuralLowProfile (x 0) (x 1) +
    factorTwoIntrinsicSixEvenTail (x 2)

/-- The last three core coordinates as one odd endpoint profile. -/
def factorTwoIntrinsicNineDirectP135Profile
    (x : Fin 6 → ℝ) : ℝ → ℝ :=
  factorTwoIntrinsicSixOddTail (x 3) (x 4) (x 5)

theorem continuous_factorTwoIntrinsicNineDirectP024Profile
    (x : Fin 6 → ℝ) :
    Continuous (factorTwoIntrinsicNineDirectP024Profile x) := by
  unfold factorTwoIntrinsicNineDirectP024Profile
  exact (continuous_factorTwoEvenStructuralLowProfile (x 0) (x 1)).add
    (continuous_const.mul continuous_factorTwoCenteredP4)

theorem continuous_factorTwoIntrinsicNineDirectP135Profile
    (x : Fin 6 → ℝ) :
    Continuous (factorTwoIntrinsicNineDirectP135Profile x) := by
  unfold factorTwoIntrinsicNineDirectP135Profile
    factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  fun_prop

private theorem intrinsicNineEvenProfile_core_eq
    (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineEvenProfile (x 0) (x 1) (x 2) 0 0 =
      factorTwoIntrinsicNineDirectP024Profile x := by
  funext t
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
    factorTwoIntrinsicNineDirectP024Profile factorTwoIntrinsicSixEvenTail
  simp only [Pi.add_apply]
  ring

private theorem intrinsicNineEvenProfile_core_add_P6_eq
    (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineEvenProfile (x 0) (x 1) (x 2) 1 0 =
      factorTwoIntrinsicNineDirectP024Profile x + factorTwoCenteredP6 := by
  funext t
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
    factorTwoIntrinsicNineDirectP024Profile factorTwoIntrinsicSixEvenTail
  simp only [Pi.add_apply]
  ring

private theorem intrinsicNineEvenProfile_P6_eq :
    factorTwoIntrinsicNineEvenProfile 0 0 0 1 0 =
      factorTwoCenteredP6 := by
  funext t
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
    factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
  simp only [Pi.add_apply]
  ring

private theorem intrinsicNineOddProfile_core_eq
    (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineOddProfile (x 3) (x 4) (x 5) 0 =
      factorTwoIntrinsicNineDirectP135Profile x := by
  funext t
  unfold factorTwoIntrinsicNineOddProfile factorTwoIntrinsicEightOddProfile
    factorTwoIntrinsicNineDirectP135Profile
  simp only [Pi.add_apply]
  ring

private theorem intrinsicNineOddProfile_zero_eq :
    factorTwoIntrinsicNineOddProfile 0 0 0 0 = (0 : ℝ → ℝ) := by
  funext t
  unfold factorTwoIntrinsicNineOddProfile factorTwoIntrinsicEightOddProfile
    factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
  simp

/-- The matrix row is exactly the complete endpoint mixed functional.  The
charged reserve cancels from the polarization because it is diagonal in
`P6/P7/P8`. -/
theorem factorTwoIntrinsicNineDirectP6BorderFunctional_eq_lowTailMixed
    (a b : ℝ) (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectP6BorderFunctional a b x =
      factorTwoEndpointLowTailMixed
        (factorTwoIntrinsicNineDirectP024Profile x)
        factorTwoCenteredP6
        (factorTwoIntrinsicNineDirectP135Profile x)
        0 a b := by
  let eLow := factorTwoIntrinsicNineDirectP024Profile x
  let oLow := factorTwoIntrinsicNineDirectP135Profile x
  have heLow : Continuous eLow := by
    simpa only [eLow] using
      continuous_factorTwoIntrinsicNineDirectP024Profile x
  have hoLow : Continuous oLow := by
    simpa only [oLow] using
      continuous_factorTwoIntrinsicNineDirectP135Profile x
  have hphase := factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    eLow factorTwoCenteredP6 oLow (0 : ℝ → ℝ)
      heLow continuous_factorTwoCenteredP6 hoLow continuous_zero a b
  simp only [add_zero] at hphase
  have hQplus := factorTwoIntrinsicNineDirectLowQuadratic_eq_phase_sub_reserve
    a b (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) 1 0 0
  have hQlow := factorTwoIntrinsicNineDirectLowQuadratic_eq_phase_sub_reserve
    a b (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) 0 0 0
  have hQP6 := factorTwoIntrinsicNineDirectLowQuadratic_eq_phase_sub_reserve
    a b 0 0 0 0 0 0 1 0 0
  rw [intrinsicNineEvenProfile_core_add_P6_eq,
    intrinsicNineOddProfile_core_eq] at hQplus
  rw [intrinsicNineEvenProfile_core_eq,
    intrinsicNineOddProfile_core_eq] at hQlow
  rw [intrinsicNineEvenProfile_P6_eq,
    intrinsicNineOddProfile_zero_eq] at hQP6
  dsimp only [eLow, oLow] at hphase
  have hsemantic :
      factorTwoIntrinsicNineDirectLowQuadratic a b
          (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) 1 0 0 -
        factorTwoIntrinsicNineDirectLowQuadratic a b
          (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) 0 0 0 -
        factorTwoIntrinsicNineDirectLowQuadratic a b
          0 0 0 0 0 0 1 0 0 =
        2 * factorTwoEndpointLowTailMixed
          (factorTwoIntrinsicNineDirectP024Profile x)
          factorTwoCenteredP6
          (factorTwoIntrinsicNineDirectP135Profile x)
          0 a b := by
    rw [hQplus, hQlow, hQP6, hphase]
    unfold factorTwoIntrinsicNineP678LowReserve
    ring
  have hrow :
      2 * factorTwoIntrinsicNineDirectP6BorderFunctional a b x =
      factorTwoIntrinsicNineDirectLowQuadratic a b
          (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) 1 0 0 -
        factorTwoIntrinsicNineDirectLowQuadratic a b
          (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) 0 0 0 -
        factorTwoIntrinsicNineDirectLowQuadratic a b
          0 0 0 0 0 0 1 0 0 := by
    classical
    unfold factorTwoIntrinsicNineDirectP6BorderFunctional
      factorTwoIntrinsicNineDirectP6BorderVector
      factorTwoIntrinsicNineDirectP6PrefixMatrix
      factorTwoIntrinsicNineDirectPrefix
      factorTwoIntrinsicNineDirectLowMatrix
      factorTwoIntrinsicNineDirectCoordinateBilinear
      factorTwoIntrinsicNineDirectCoordinateQuadratic
      factorTwoIntrinsicNineDirectLowQuadratic
      factorTwoIntrinsicNineDirectEvenQuadratic
      factorTwoIntrinsicNineDirectOddQuadratic
      factorTwoIntrinsicNineDirectAlternating
      factorTwoIntrinsicNineDirectUnit
      factorTwoIntrinsicSixStaticEven
      factorTwoIntrinsicSixStaticOdd
      factorTwoIntrinsicSixStaticAlternating
      factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicNineP678LowReserve
    simp [dotProduct, Fin.sum_univ_succ, Pi.single_apply]
    ring
  linarith

/-- At cutoff six, the complete mixed functional consists of one smooth
regular integral plus the coupled five-family nonpolynomial aggregate. -/
theorem factorTwoEndpointLowTailMixed_directP6_eq_decomposition
    (a b : ℝ) (x : Fin 6 → ℝ) :
    factorTwoEndpointLowTailMixed
        (factorTwoIntrinsicNineDirectP024Profile x)
        factorTwoCenteredP6
        (factorTwoIntrinsicNineDirectP135Profile x)
        0 a b =
      (1 / 2 : ℝ) * (∫ t : ℝ in 0..2,
        factorTwoP67ResidualSmoothMixedIntegrand
          (factorTwoIntrinsicNineDirectP024Profile x)
          (factorTwoIntrinsicNineDirectP135Profile x)
          factorTwoCenteredP6 (0 : ℝ → ℝ) a b t) +
        factorTwoIntrinsicNineNonpolynomialMixed
          (factorTwoIntrinsicNineDirectP024Profile x)
          (factorTwoIntrinsicNineDirectP135Profile x)
          factorTwoCenteredP6 (0 : ℝ → ℝ) a b := by
  let pE : ℝ[X] := factorTwoIntrinsicNineEvenPolynomial
    (x 0) (x 1) (x 2) 0 0
  let pO : ℝ[X] := factorTwoIntrinsicNineOddPolynomial
    (x 3) (x 4) (x 5) 0
  have hpEdeg : pE.natDegree < 6 := by
    dsimp only [pE, factorTwoIntrinsicNineEvenPolynomial]
    simp only [zero_smul, add_zero]
    have hdeg : ((x 0) • shiftedLegendreReal 0 +
        (x 1) • shiftedLegendreReal 2 +
        (x 2) • shiftedLegendreReal 4).natDegree ≤ 4 := by
      compute_degree
    omega
  have hpOdeg : pO.natDegree < 6 := by
    dsimp only [pO, factorTwoIntrinsicNineOddPolynomial]
    simp only [neg_zero, zero_smul, add_zero]
    have hdeg : ((-(x 3)) • shiftedLegendreReal 1 +
        (-(x 4)) • shiftedLegendreReal 3 +
        (-(x 5)) • shiftedLegendreReal 5).natDegree ≤ 5 := by
      compute_degree
    omega
  have hzeroLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (0 : ℝ → ℝ) := by
    have hdiff : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    exact hdiff.locallyLipschitz.locallyLipschitzOn
  have hzeroGap : centeredLegendreMomentsVanishBelow
      (0 : ℝ → ℝ) 6 := by
    intro n hn
    simp [centeredPullback]
  have h := factorTwoEndpointLowTailMixed_centeredPolynomialLift_eq
    pE pO factorTwoCenteredP6 (0 : ℝ → ℝ)
    continuous_factorTwoCenteredP6 continuous_zero
    locallyLipschitzOn_factorTwoCenteredP6 hzeroLocal
    factorTwoCenteredP6_momentsVanishBelow hzeroGap
    hpEdeg hpOdeg a b
  dsimp only [pE, pO] at h
  rw [centeredPolynomialLift_intrinsicNineEvenPolynomial,
    centeredPolynomialLift_intrinsicNineOddPolynomial,
    intrinsicNineEvenProfile_core_eq,
    intrinsicNineOddProfile_core_eq] at h
  exact h

/-- Combined with the semantic bridge, this is the first exact normal form
for the matrix border itself. -/
theorem factorTwoIntrinsicNineDirectP6BorderFunctional_eq_decomposition
    (a b : ℝ) (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectP6BorderFunctional a b x =
      (1 / 2 : ℝ) * (∫ t : ℝ in 0..2,
        factorTwoP67ResidualSmoothMixedIntegrand
          (factorTwoIntrinsicNineDirectP024Profile x)
          (factorTwoIntrinsicNineDirectP135Profile x)
          factorTwoCenteredP6 (0 : ℝ → ℝ) a b t) +
        factorTwoIntrinsicNineNonpolynomialMixed
          (factorTwoIntrinsicNineDirectP024Profile x)
          (factorTwoIntrinsicNineDirectP135Profile x)
          factorTwoCenteredP6 (0 : ℝ → ℝ) a b := by
  rw [factorTwoIntrinsicNineDirectP6BorderFunctional_eq_lowTailMixed,
    factorTwoEndpointLowTailMixed_directP6_eq_decomposition]

/-- The complete smooth part of the direct `P6` border retains exactly one
degree-six polynomial row, supported on the `P0` coordinate. -/
theorem integral_factorTwoIntrinsicNineDirectP6SmoothMixed_eq
    (a b : ℝ) (x : Fin 6 → ℝ) :
    (∫ t : ℝ in 0..2,
      factorTwoP67ResidualSmoothMixedIntegrand
        (factorTwoIntrinsicNineDirectP024Profile x)
        (factorTwoIntrinsicNineDirectP135Profile x)
        factorTwoCenteredP6 (0 : ℝ → ℝ) a b t) =
      2 * (factorTwoP67ResidualAnalyticMixed
            (factorTwoIntrinsicNineDirectP024Profile x)
            (factorTwoIntrinsicNineDirectP135Profile x)
            factorTwoCenteredP6 (0 : ℝ → ℝ) a b +
          factorTwoP67ResidualForwardHankelMixed
            (factorTwoIntrinsicNineDirectP024Profile x)
            (factorTwoIntrinsicNineDirectP135Profile x)
            factorTwoCenteredP6 (0 : ℝ → ℝ) a b) +
        2 * a *
          (poleFreeCoeff6 yoshidaEndpointA * (32 / 3003 : ℝ) * x 0) := by
  simpa only [factorTwoIntrinsicNineDirectP024Profile,
    factorTwoIntrinsicNineDirectP135Profile] using
    integral_factorTwoP67ResidualSmoothMixedIntegrand_directP6_eq
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) a b

/-- Exact cutoff-six border normal form.  The direct matrix row is one
coupled sum of the analytic remainder, forward Hankel pole, retained `P0`
rank-one row, and the five-family nonpolynomial aggregate. -/
theorem factorTwoIntrinsicNineDirectP6BorderFunctional_eq_complete_normalForm
    (a b : ℝ) (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectP6BorderFunctional a b x =
      factorTwoP67ResidualAnalyticMixed
          (factorTwoIntrinsicNineDirectP024Profile x)
          (factorTwoIntrinsicNineDirectP135Profile x)
          factorTwoCenteredP6 (0 : ℝ → ℝ) a b +
        factorTwoP67ResidualForwardHankelMixed
          (factorTwoIntrinsicNineDirectP024Profile x)
          (factorTwoIntrinsicNineDirectP135Profile x)
          factorTwoCenteredP6 (0 : ℝ → ℝ) a b +
        a * poleFreeCoeff6 yoshidaEndpointA * (32 / 3003 : ℝ) * x 0 +
        factorTwoIntrinsicNineNonpolynomialMixed
          (factorTwoIntrinsicNineDirectP024Profile x)
          (factorTwoIntrinsicNineDirectP135Profile x)
          factorTwoCenteredP6 (0 : ℝ → ℝ) a b := by
  rw [factorTwoIntrinsicNineDirectP6BorderFunctional_eq_decomposition,
    integral_factorTwoIntrinsicNineDirectP6SmoothMixed_eq]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderDecompositionStructural
