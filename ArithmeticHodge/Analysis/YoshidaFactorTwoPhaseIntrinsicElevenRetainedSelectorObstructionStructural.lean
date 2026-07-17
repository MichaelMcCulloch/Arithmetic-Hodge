import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorObstructionStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaRegularKernelSchur

noncomputable section

/-!
# Obstruction to the retained cutoff-eleven selector target

The retained `1 / 128` singular charge is too large on a concrete vector in
the low `{P₀,P₂}` plane.  Its exact low complement is negative, whereas every
constrained selector dual is nonnegative.  Thus no choice of polynomial
selectors can satisfy the finite hypothesis of the retained Schur handoff
for this vector.
-/

/-- The obstructing cutoff-eleven polynomial, equal to `-8 L₀ + 9 L₂`. -/
def factorTwoIntrinsicElevenRetainedBadEvenPolynomial : ℝ[X] :=
  factorTwoIntrinsicNineEvenPolynomial (-8) 9 0 0 0

theorem factorTwoIntrinsicElevenRetainedBadEvenPolynomial_natDegree_lt :
    factorTwoIntrinsicElevenRetainedBadEvenPolynomial.natDegree < 11 := by
  unfold factorTwoIntrinsicElevenRetainedBadEvenPolynomial
    factorTwoIntrinsicNineEvenPolynomial
  have hdeg :
      (((-8 : ℝ) • shiftedLegendreReal 0 + (9 : ℝ) • shiftedLegendreReal 2 +
        (0 : ℝ) • shiftedLegendreReal 4 + (0 : ℝ) • shiftedLegendreReal 6 +
        (0 : ℝ) • shiftedLegendreReal 8)).natDegree ≤ 8 := by
    compute_degree
  omega

theorem centeredPolynomialLift_retainedBadEvenPolynomial :
    centeredPolynomialLift factorTwoIntrinsicElevenRetainedBadEvenPolynomial =
      yoshidaEndpointEvenLowProfile (-8) 9 := by
  unfold factorTwoIntrinsicElevenRetainedBadEvenPolynomial
  rw [centeredPolynomialLift_intrinsicNineEvenPolynomial]
  funext x
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
    factorTwoIntrinsicSixEvenTail factorTwoEvenStructuralLowProfile
    yoshidaEndpointEvenLowProfile centeredEvenP0
  simp only [Pi.add_apply]
  ring

/-- The exact low complement required by the retained selector theorem is
strictly negative on `-8 P₀ + 9 P₂`. -/
theorem factorTwoIntrinsicElevenRetainedBadLowComplement_neg :
    factorTwoEndpointChannelPhase
          (yoshidaEndpointEvenLowProfile (-8) 9) 0 0 0 -
        (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
          (yoshidaEndpointEvenLowProfile (-8) 9) 0 0 0 < 0 := by
  let e : ℝ → ℝ := yoshidaEndpointEvenLowProfile (-8) 9
  have heProfile : e = fun x : ℝ ↦
      (-8 : ℝ) * centeredEvenP0 x + 9 * centeredEvenP2 x := by
    funext x
    simp [e, yoshidaEndpointEvenLowProfile, centeredEvenP0]
  have hclean : yoshidaEndpointOddCleanQuadratic e < (1963 / 2000 : ℝ) := by
    rw [heProfile, yoshidaEndpointEvenLowGram_quadratic_eq_clean]
    have h00 := intrinsicEven_cleanGram00_lt_step01
    have h02 := intrinsicEven_cleanGram02_bounds.1
    have h22 := intrinsicEven_cleanGram22_lt_step01
    norm_num at h00 h02 h22 ⊢
    nlinarith
  have hzero : yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
    unfold yoshidaEndpointOddCleanQuadratic centeredRawLogEnergy
      yoshidaEndpointRegularQuadratic yoshidaEndpointHyperbolicQuadratic
    simp
  have hphase : factorTwoEndpointChannelPhase e 0 0 0 =
      yoshidaEndpointOddCleanQuadratic e := by
    unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    rw [hzero]
    ring
  have hec : Continuous e := by
    simpa only [e] using continuous_yoshidaEndpointEvenLowProfile (-8) 9
  have helocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) e := by
    have hd : ContDiff ℝ 1 e := by
      dsimp only [e]
      unfold yoshidaEndpointEvenLowProfile centeredEvenP2
      fun_prop
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have h0c : Continuous (0 : ℝ → ℝ) := continuous_zero
  have h0local : LocallyLipschitzOn (Icc (-1 : ℝ) 1) (0 : ℝ → ℝ) := by
    have hd : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    change LocallyLipschitzOn (Icc (-1 : ℝ) 1) (fun _ : ℝ ↦ (0 : ℝ))
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hraw0 : centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
    unfold centeredRawLogEnergy
    simp
  have hs0 := half_singularWeightedEnergy_eq_protected_add_logMass
    e (0 : ℝ → ℝ) hec h0c helocal h0local 0 0
  have hsing :
      (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy e 0 0 0 =
        2161 / 800 := by
    unfold factorTwoIntrinsicProtectedBlock factorTwoIntrinsicEnergy
      factorTwoIntrinsicPotentialEnergy at hs0
    simp [factorTwoCenteredPhaseCorrelation, hraw0] at hs0
    dsimp only [e] at hs0
    rw [centeredRawLogEnergy_yoshidaEndpointEvenLowProfile,
      integral_endpointPotential_mul_yoshidaEndpointEvenLowProfile_sq,
      integral_yoshidaEndpointEvenLowProfile_sq] at hs0
    norm_num at hs0 ⊢
    ring_nf at hs0
    nlinarith
  change factorTwoEndpointChannelPhase e 0 0 0 -
      (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy e 0 0 0 < 0
  rw [hphase, hsing]
  linarith

/-- No pair of polynomial selectors can meet the retained finite-selector
hypothesis on the obstructing low vector.  This is independent of selector
degree and weighted-dual regularity. -/
theorem factorTwoIntrinsicElevenRetainedBadSelector_impossible
    (qE qO : ℝ[X]) :
    ¬ factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter
            factorTwoIntrinsicElevenRetainedBadEvenPolynomial 0 0 0)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenter
            factorTwoIntrinsicElevenRetainedBadEvenPolynomial 0 0 0)
          qE qO ≤
        factorTwoEndpointChannelPhase
            (centeredPolynomialLift
              factorTwoIntrinsicElevenRetainedBadEvenPolynomial)
            (centeredPolynomialLift (0 : ℝ[X])) 0 0 -
          (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift
              factorTwoIntrinsicElevenRetainedBadEvenPolynomial)
            (centeredPolynomialLift (0 : ℝ[X])) 0 0 := by
  intro hselector
  have hnonneg :=
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_nonneg
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter
        factorTwoIntrinsicElevenRetainedBadEvenPolynomial 0 0 0)
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenter
        factorTwoIntrinsicElevenRetainedBadEvenPolynomial 0 0 0)
      qE qO
  have hzero : centeredPolynomialLift (0 : ℝ[X]) = (0 : ℝ → ℝ) := by
    funext x
    simp [centeredPolynomialLift]
  have hright :
      factorTwoEndpointChannelPhase
            (centeredPolynomialLift
              factorTwoIntrinsicElevenRetainedBadEvenPolynomial)
            (centeredPolynomialLift (0 : ℝ[X])) 0 0 -
          (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift
              factorTwoIntrinsicElevenRetainedBadEvenPolynomial)
            (centeredPolynomialLift (0 : ℝ[X])) 0 0 < 0 := by
    rw [centeredPolynomialLift_retainedBadEvenPolynomial, hzero]
    exact factorTwoIntrinsicElevenRetainedBadLowComplement_neg
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorObstructionStructural
