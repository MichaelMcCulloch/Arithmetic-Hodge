import ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFactorTwoForwardPolePolynomialReductionStructural
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConcreteSelectorsStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularSchurStructural
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoReflectedPolePolynomialReductionStructural
open YoshidaRegularKernelBound

noncomputable section

/-!
# Homogeneity of the cutoff-eleven selector problem

The retained selector certificate is a quadratic problem.  This file records
that fact before any basis is chosen: simultaneous scaling of a representer
and its polynomial selector scales the weighted dual cost by the square of
the scalar.  Consequently finite selector certificates may be proved on a
normalized coefficient sphere and transported to the whole low space.
-/

theorem centeredPolynomialLift_smul
    (c : ℝ) (p : ℝ[X]) (x : ℝ) :
    centeredPolynomialLift (c • p) x =
      c * centeredPolynomialLift p x := by
  unfold centeredPolynomialLift
  simp only [Polynomial.eval_smul, smul_eq_mul]

theorem centeredPolynomialLift_add
    (p q : ℝ[X]) (x : ℝ) :
    centeredPolynomialLift (p + q) x =
      centeredPolynomialLift p x + centeredPolynomialLift q x := by
  unfold centeredPolynomialLift
  rw [Polynomial.eval_add]

theorem factorTwoIntrinsicElevenSelectorResidual_smul
    (c : ℝ) (F : ℝ → ℝ) (p : ℝ[X]) (x : ℝ) :
    factorTwoIntrinsicElevenSelectorResidual
        (fun y ↦ c * F y) (c • p) x =
      c * factorTwoIntrinsicElevenSelectorResidual F p x := by
  unfold factorTwoIntrinsicElevenSelectorResidual
  rw [centeredPolynomialLift_smul]
  ring

theorem factorTwoIntrinsicElevenSelectorDual_smul
    (W F : ℝ → ℝ) (c : ℝ) (p : ℝ[X]) :
    factorTwoIntrinsicElevenSelectorDual W
        (fun x ↦ c * F x) (c • p) =
      c ^ 2 * factorTwoIntrinsicElevenSelectorDual W F p := by
  unfold factorTwoIntrinsicElevenSelectorDual
  rw [show (fun x : ℝ ↦
      factorTwoIntrinsicElevenSelectorResidual
          (fun y ↦ c * F y) (c • p) x ^ 2 / W x) =
      fun x ↦ c ^ 2 *
        (factorTwoIntrinsicElevenSelectorResidual F p x ^ 2 / W x) by
    funext x
    rw [factorTwoIntrinsicElevenSelectorResidual_smul]
    ring,
    intervalIntegral.integral_const_mul]

theorem factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_smul
    (FE FO : ℝ → ℝ) (c : ℝ) (pE pO : ℝ[X]) :
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
        (fun x ↦ c * FE x) (fun x ↦ c * FO x)
        (c • pE) (c • pO) =
      c ^ 2 *
        factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          FE FO pE pO := by
  unfold factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
  rw [factorTwoIntrinsicElevenSelectorDual_smul,
    factorTwoIntrinsicElevenSelectorDual_smul]
  ring

theorem natDegree_smul_lt_eleven
    (c : ℝ) (p : ℝ[X]) (hp : p.natDegree < 11) :
    (c • p).natDegree < 11 := by
  exact lt_of_le_of_lt (Polynomial.natDegree_smul_le c p) hp

/-! ## Exact phase splitting when the odd low polynomial vanishes -/

/-- Phase-independent retained even row on an even-only low profile. -/
def retainedEvenBaseRepresenterAt
    (gamma : ℝ) (p : ℝ[X]) : ℝ → ℝ :=
  factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    gamma p 0 0 0

/-- Coefficient of the symmetric phase in the retained even row. -/
def retainedEvenSymmetricRepresenterAt
    (gamma : ℝ) (p : ℝ[X]) : ℝ → ℝ :=
  fun x ↦
    factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        gamma p 0 1 0 x -
      retainedEvenBaseRepresenterAt gamma p x

/-- Coefficient of the alternating phase in the retained odd row. -/
def retainedOddAlternatingRepresenterAt
    (gamma : ℝ) (p : ℝ[X]) : ℝ → ℝ :=
  factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
    gamma p 0 0 1

private theorem centeredPolynomialLift_zero (x : ℝ) :
    centeredPolynomialLift (0 : ℝ[X]) x = 0 := by
  simp [centeredPolynomialLift]

private theorem centeredPolynomialLift_zero_fun :
    centeredPolynomialLift (0 : ℝ[X]) = (0 : ℝ → ℝ) := by
  funext x
  exact centeredPolynomialLift_zero x

private theorem factorTwoIntrinsicElevenCleanSurvivorRepresenter_zero
    (x : ℝ) :
    factorTwoIntrinsicElevenCleanSurvivorRepresenter (0 : ℝ[X]) x = 0 := by
  unfold factorTwoIntrinsicElevenCleanSurvivorRepresenter
    yoshidaEndpointEvenRegularRepresenter
    yoshidaEndpointCoshMoment yoshidaEndpointSinhMoment
  simp [centeredPolynomialLift]

private theorem factorTwoContinuousLagK_zero_right
    (q : ℝ → ℝ) (x : ℝ) :
    factorTwoContinuousLagK q (0 : ℝ → ℝ) x = 0 := by
  unfold factorTwoContinuousLagK factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  simp

private theorem factorTwoContinuousLagJ_zero_right
    (q : ℝ → ℝ) (x : ℝ) :
    factorTwoContinuousLagJ q (0 : ℝ → ℝ) x = 0 := by
  unfold factorTwoContinuousLagJ factorTwoContinuousLagRightRepresenter
    factorTwoContinuousLagLeftRepresenter
  simp

private theorem factorTwoFixedLagK_zero_right
    (tau x : ℝ) :
    factorTwoFixedLagK tau (0 : ℝ → ℝ) x = 0 := by
  unfold factorTwoFixedLagK factorTwoFixedLagRightRepresenter
    factorTwoFixedLagLeftRepresenter
  simp

private theorem factorTwoFixedLagJ_zero_right
    (tau x : ℝ) :
    factorTwoFixedLagJ tau (0 : ℝ → ℝ) x = 0 := by
  unfold factorTwoFixedLagJ factorTwoFixedLagRightRepresenter
    factorTwoFixedLagLeftRepresenter
  simp

private theorem forwardPoleKLogSelector_zero (x : ℝ) :
    forwardPoleKLogSelector (0 : ℝ[X]) x = 0 := by
  simp [forwardPoleKLogSelector]

private theorem forwardPoleLLogSelector_zero (x : ℝ) :
    forwardPoleLLogSelector (0 : ℝ[X]) x = 0 := by
  simp [forwardPoleLLogSelector]

private theorem reflectedPoleKLogSelector_zero (x : ℝ) :
    reflectedPoleKLogSelector (0 : ℝ[X]) x = 0 := by
  simp [reflectedPoleKLogSelector]

private theorem reflectedPoleJLogSelector_zero (x : ℝ) :
    reflectedPoleJLogSelector (0 : ℝ[X]) x = 0 := by
  simp [reflectedPoleJLogSelector]

private theorem analyticEven_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenAnalyticEvenRepresenter p 0 a b x =
      a * factorTwoIntrinsicElevenAnalyticEvenRepresenter p 0 1 0 x := by
  unfold factorTwoIntrinsicElevenAnalyticEvenRepresenter
  rw [centeredPolynomialLift_zero_fun,
    factorTwoContinuousLagJ_zero_right]
  ring

private theorem forwardEven_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenForwardEvenRepresenter p 0 a b x =
      a * factorTwoIntrinsicElevenForwardEvenRepresenter p 0 1 0 x := by
  unfold factorTwoIntrinsicElevenForwardEvenRepresenter
  rw [forwardPoleLLogSelector_zero]
  ring

private theorem reflectedEven_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenReflectedEvenRepresenter p 0 a b x =
      a * factorTwoIntrinsicElevenReflectedEvenRepresenter p 0 1 0 x := by
  unfold factorTwoIntrinsicElevenReflectedEvenRepresenter
  rw [reflectedPoleJLogSelector_zero]
  ring

private theorem primeEven_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenPrimeEvenRepresenter p 0 a b x =
      a * factorTwoIntrinsicElevenPrimeEvenRepresenter p 0 1 0 x := by
  unfold factorTwoIntrinsicElevenPrimeEvenRepresenter
  rw [centeredPolynomialLift_zero_fun,
    factorTwoFixedLagJ_zero_right]
  ring

private theorem potentialPoleEven_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenPotentialPoleEvenRepresenter p 0 a b x =
      factorTwoIntrinsicElevenPotentialPoleEvenRepresenter p 0 0 0 x +
        a *
          (factorTwoIntrinsicElevenPotentialPoleEvenRepresenter p 0 1 0 x -
            factorTwoIntrinsicElevenPotentialPoleEvenRepresenter p 0 0 0 x) := by
  unfold factorTwoIntrinsicElevenPotentialPoleEvenRepresenter
  rw [reflectedEven_zero_odd_phase p a b x,
    reflectedEven_zero_odd_phase p 0 0 x,
    reflectedEven_zero_odd_phase p 1 0 x]
  ring

private theorem completeEven_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenEvenMixedRepresenter p 0 a b x =
      factorTwoIntrinsicElevenEvenMixedRepresenter p 0 0 0 x +
        a *
          (factorTwoIntrinsicElevenEvenMixedRepresenter p 0 1 0 x -
            factorTwoIntrinsicElevenEvenMixedRepresenter p 0 0 0 x) := by
  unfold factorTwoIntrinsicElevenEvenMixedRepresenter
  rw [analyticEven_zero_odd_phase p a b x,
    analyticEven_zero_odd_phase p 0 0 x,
    analyticEven_zero_odd_phase p 1 0 x,
    forwardEven_zero_odd_phase p a b x,
    forwardEven_zero_odd_phase p 0 0 x,
    forwardEven_zero_odd_phase p 1 0 x,
    reflectedEven_zero_odd_phase p a b x,
    reflectedEven_zero_odd_phase p 0 0 x,
    reflectedEven_zero_odd_phase p 1 0 x,
    primeEven_zero_odd_phase p a b x,
    primeEven_zero_odd_phase p 0 0 x,
    primeEven_zero_odd_phase p 1 0 x]
  ring

private theorem analyticOdd_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenAnalyticOddRepresenter p 0 a b x =
      b * factorTwoIntrinsicElevenAnalyticOddRepresenter p 0 0 1 x := by
  unfold factorTwoIntrinsicElevenAnalyticOddRepresenter
  rw [centeredPolynomialLift_zero_fun,
    factorTwoContinuousLagK_zero_right]
  ring

private theorem forwardOdd_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenForwardOddRepresenter p 0 a b x =
      b * factorTwoIntrinsicElevenForwardOddRepresenter p 0 0 1 x := by
  unfold factorTwoIntrinsicElevenForwardOddRepresenter
  rw [forwardPoleKLogSelector_zero]
  ring

private theorem reflectedOdd_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenReflectedOddRepresenter p 0 a b x =
      b * factorTwoIntrinsicElevenReflectedOddRepresenter p 0 0 1 x := by
  unfold factorTwoIntrinsicElevenReflectedOddRepresenter
  rw [reflectedPoleKLogSelector_zero]
  ring

private theorem primeOdd_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenPrimeOddRepresenter p 0 a b x =
      b * factorTwoIntrinsicElevenPrimeOddRepresenter p 0 0 1 x := by
  unfold factorTwoIntrinsicElevenPrimeOddRepresenter
  rw [centeredPolynomialLift_zero_fun,
    factorTwoFixedLagK_zero_right]
  ring

private theorem potentialPoleOdd_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenPotentialPoleOddRepresenter p 0 a b x =
      b * factorTwoIntrinsicElevenPotentialPoleOddRepresenter p 0 0 1 x := by
  unfold factorTwoIntrinsicElevenPotentialPoleOddRepresenter
  rw [centeredPolynomialLift_zero,
    reflectedOdd_zero_odd_phase p a b x]
  ring

private theorem completeOdd_zero_odd_phase
    (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenOddMixedRepresenter p 0 a b x =
      b * factorTwoIntrinsicElevenOddMixedRepresenter p 0 0 1 x := by
  unfold factorTwoIntrinsicElevenOddMixedRepresenter
  rw [factorTwoIntrinsicElevenCleanSurvivorRepresenter_zero,
    analyticOdd_zero_odd_phase p a b x,
    forwardOdd_zero_odd_phase p a b x,
    reflectedOdd_zero_odd_phase p a b x,
    primeOdd_zero_odd_phase p a b x]
  simp only [zero_add]
  ring

/-- With no odd low polynomial, the retained even representer is exactly
affine in the symmetric phase and independent of the alternating phase. -/
theorem retainedEvenRepresenterAt_zero_odd_phase_split
    (gamma : ℝ) (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        gamma p 0 a b x =
      retainedEvenBaseRepresenterAt gamma p x +
        a * retainedEvenSymmetricRepresenterAt gamma p x := by
  unfold retainedEvenSymmetricRepresenterAt retainedEvenBaseRepresenterAt
    factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
  rw [completeEven_zero_odd_phase p a b x,
    potentialPoleEven_zero_odd_phase p a b x]
  ring

/-- With no odd low polynomial, the retained odd representer is exactly
linear in the alternating phase and independent of the symmetric phase. -/
theorem retainedOddRepresenterAt_zero_odd_phase_split
    (gamma : ℝ) (p : ℝ[X]) (a b x : ℝ) :
    factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        gamma p 0 a b x =
      b * retainedOddAlternatingRepresenterAt gamma p x := by
  unfold retainedOddAlternatingRepresenterAt
    factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
  rw [completeOdd_zero_odd_phase p a b x,
    potentialPoleOdd_zero_odd_phase p a b x]
  ring

/-! ## Exact three-coordinate selector Gram -/

/-- Linear selector assembled from three fixed basis selectors. -/
def threeSelectorPolynomial
    (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X]) : ℝ[X] :=
  c0 • q0 + c2 • q2 + c4 • q4

/-- Linear representer assembled from three fixed basis rows. -/
def threeSelectorRepresenter
    (c0 c2 c4 : ℝ) (F0 F2 F4 : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ c0 * F0 x + c2 * F2 x + c4 * F4 x

theorem threeSelectorPolynomial_natDegree_lt
    (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X])
    (hq0 : q0.natDegree < 11) (hq2 : q2.natDegree < 11)
    (hq4 : q4.natDegree < 11) :
    (threeSelectorPolynomial c0 c2 c4 q0 q2 q4).natDegree < 11 := by
  unfold threeSelectorPolynomial
  exact natDegree_add_lt_eleven _ _
    (natDegree_add_lt_eleven _ _
      (natDegree_smul_lt_eleven c0 q0 hq0)
      (natDegree_smul_lt_eleven c2 q2 hq2))
    (natDegree_smul_lt_eleven c4 q4 hq4)

/-! ## The concrete `P₀/P₂/P₄` polynomial -/

/-- Unit-interval polynomial whose centered lift is the intrinsic even
`P₀/P₂/P₄` profile.  Naming this slice keeps the selector construction tied
to the production coordinates rather than to an abstract three-vector. -/
def retainedP024Polynomial (c0 c2 c4 : ℝ) : ℝ[X] :=
  factorTwoIntrinsicNineEvenPolynomial c0 c2 c4 0 0

/-- The production `P₀/P₂/P₄` polynomial is literally the three-coordinate
selector synthesis in the shifted Legendre basis. -/
theorem retainedP024Polynomial_eq_threeSelectorPolynomial
    (c0 c2 c4 : ℝ) :
    retainedP024Polynomial c0 c2 c4 =
      threeSelectorPolynomial c0 c2 c4
        (shiftedLegendreReal 0) (shiftedLegendreReal 2)
        (shiftedLegendreReal 4) := by
  unfold retainedP024Polynomial factorTwoIntrinsicNineEvenPolynomial
    threeSelectorPolynomial
  simp

theorem retainedP024Polynomial_natDegree_lt
    (c0 c2 c4 : ℝ) :
    (retainedP024Polynomial c0 c2 c4).natDegree < 11 := by
  rw [retainedP024Polynomial_eq_threeSelectorPolynomial]
  apply threeSelectorPolynomial_natDegree_lt
  all_goals
    rw [natDegree_shiftedLegendreReal]
    omega

/-- Centering the concrete polynomial recovers exactly the profile used by
the retained `P₀/P₂/P₄` low-complement theorem. -/
theorem centeredPolynomialLift_retainedP024Polynomial
    (c0 c2 c4 : ℝ) :
    centeredPolynomialLift (retainedP024Polynomial c0 c2 c4) =
      factorTwoIntrinsicEvenP024Profile c0 c2 c4 := by
  unfold retainedP024Polynomial
  rw [centeredPolynomialLift_intrinsicNineEvenPolynomial]
  funext x
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
    factorTwoIntrinsicEvenP024Profile factorTwoIntrinsicSixEvenTail
    factorTwoEvenStructuralLowProfile
  simp

private theorem centeredPolynomialLift_threeSelectorPolynomial
    (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X]) (x : ℝ) :
    centeredPolynomialLift
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) x =
      c0 * centeredPolynomialLift q0 x +
        c2 * centeredPolynomialLift q2 x +
        c4 * centeredPolynomialLift q4 x := by
  unfold threeSelectorPolynomial centeredPolynomialLift
  simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]

private theorem integrableOn_regularKernel_mul_centeredPolynomialLift
    (p : ℝ[X]) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    IntegrableOn
      (fun y : ℝ ↦
        yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
          centeredPolynomialLift p y)
      (Icc (-1 : ℝ) 1) volume := by
  let g : ℝ → ℝ := fun y ↦
    (1 / 4 : ℝ) * |centeredPolynomialLift p y|
  have hg : IntegrableOn g (Icc (-1 : ℝ) 1) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    dsimp only [g]
    exact (continuous_const.mul (continuous_centeredPolynomialLift p).abs).continuousOn
  apply hg.mono'
  · exact ((measurable_yoshidaRegularKernel.comp
      (measurable_const.mul
        ((measurable_const.sub measurable_id).abs))).mul
      (continuous_centeredPolynomialLift p).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hdist : |x - y| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have harg0 : 0 ≤ yoshidaEndpointA * |x - y| :=
      mul_nonneg yoshidaEndpointA_pos.le (abs_nonneg _)
    have harg2 : yoshidaEndpointA * |x - y| ≤ Real.log 2 := by
      unfold yoshidaEndpointA
      nlinarith [mul_le_mul_of_nonneg_left hdist
        (by positivity : 0 ≤ Real.log 2 / 2)]
    have hkernel := yoshidaRegularKernel_mem_Icc harg0 harg2
    dsimp only [g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkernel.1]
    exact mul_le_mul_of_nonneg_right hkernel.2 (abs_nonneg _)

private theorem regularRepresenter_threeSelectorPolynomial_on_Icc
    (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    yoshidaEndpointEvenRegularRepresenter
        (centeredPolynomialLift
          (threeSelectorPolynomial c0 c2 c4 q0 q2 q4)) x =
      c0 * yoshidaEndpointEvenRegularRepresenter
          (centeredPolynomialLift q0) x +
        c2 * yoshidaEndpointEvenRegularRepresenter
          (centeredPolynomialLift q2) x +
        c4 * yoshidaEndpointEvenRegularRepresenter
          (centeredPolynomialLift q4) x := by
  have h0 := integrableOn_regularKernel_mul_centeredPolynomialLift q0 x hx
  have h2 := integrableOn_regularKernel_mul_centeredPolynomialLift q2 x hx
  have h4 := integrableOn_regularKernel_mul_centeredPolynomialLift q4 x hx
  have hinner :
      (∫ y : ℝ in Icc (-1) 1,
          c0 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
            centeredPolynomialLift q0 y) +
          c2 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
            centeredPolynomialLift q2 y)) =
        (∫ y : ℝ in Icc (-1) 1,
          c0 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
            centeredPolynomialLift q0 y)) +
        ∫ y : ℝ in Icc (-1) 1,
          c2 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
            centeredPolynomialLift q2 y) := by
    simpa only [Pi.add_apply] using
      (MeasureTheory.integral_add
        (μ := volume.restrict (Icc (-1 : ℝ) 1))
        (h0.const_mul c0) (h2.const_mul c2))
  have houter :
      (∫ y : ℝ in Icc (-1) 1,
          (c0 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
              centeredPolynomialLift q0 y) +
            c2 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
              centeredPolynomialLift q2 y)) +
          c4 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
            centeredPolynomialLift q4 y)) =
        (∫ y : ℝ in Icc (-1) 1,
          c0 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
              centeredPolynomialLift q0 y) +
            c2 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
              centeredPolynomialLift q2 y)) +
        ∫ y : ℝ in Icc (-1) 1,
          c4 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
            centeredPolynomialLift q4 y) := by
    simpa only [Pi.add_apply] using
      (MeasureTheory.integral_add
        (μ := volume.restrict (Icc (-1 : ℝ) 1))
        ((h0.const_mul c0).add (h2.const_mul c2)) (h4.const_mul c4))
  unfold yoshidaEndpointEvenRegularRepresenter
  rw [show (fun y : ℝ ↦
      yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
        centeredPolynomialLift
          (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) y) =
      fun y ↦
        c0 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
          centeredPolynomialLift q0 y) +
        c2 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
          centeredPolynomialLift q2 y) +
        c4 * (yoshidaRegularKernel (yoshidaEndpointA * |x - y|) *
          centeredPolynomialLift q4 y) by
    funext y
    rw [centeredPolynomialLift_threeSelectorPolynomial]
    ring,
    houter, hinner]
  repeat rw [MeasureTheory.integral_const_mul]

private theorem intervalIntegrable_boundedLag_right_centeredPolynomialLift
    (q : ℝ → ℝ) (p : ℝ[X]) (x : ℝ)
    (hq : Measurable q) (C : ℝ)
    (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    IntervalIntegrable
      (fun y : ℝ ↦ q (y - x) * centeredPolynomialLift p y)
      volume x 1 := by
  let g : ℝ → ℝ := fun y ↦ C * |centeredPolynomialLift p y|
  have hgIcc : IntegrableOn g (Icc x 1) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    dsimp only [g]
    exact (continuous_const.mul (continuous_centeredPolynomialLift p).abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc x 1)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ ↦ q (y - x) * centeredPolynomialLift p y)
      (volume.restrict (Ioc x 1)) :=
    ((hq.comp (measurable_id.sub measurable_const)).mul
      (continuous_centeredPolynomialLift p).measurable).aestronglyMeasurable
  have hbound : ∀ᵐ y : ℝ ∂(volume.restrict (Ioc x 1)),
      ‖q (y - x) * centeredPolynomialLift p y‖ ≤ g y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hlag : y - x ∈ Icc (0 : ℝ) 2 :=
      ⟨by linarith [hy.1], by linarith [hx.1, hy.2]⟩
    have hqbound := hqC (y - x) hlag
    dsimp only [g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hqbound (abs_nonneg _)
  constructor
  · exact Integrable.mono' hg hmeas hbound
  · simp [hx.2]

private theorem intervalIntegrable_boundedLag_left_centeredPolynomialLift
    (q : ℝ → ℝ) (p : ℝ[X]) (x : ℝ)
    (hq : Measurable q) (C : ℝ)
    (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    IntervalIntegrable
      (fun y : ℝ ↦ q (x - y) * centeredPolynomialLift p y)
      volume (-1) x := by
  let g : ℝ → ℝ := fun y ↦ C * |centeredPolynomialLift p y|
  have hgIcc : IntegrableOn g (Icc (-1) x) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    dsimp only [g]
    exact (continuous_const.mul (continuous_centeredPolynomialLift p).abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (-1) x)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ ↦ q (x - y) * centeredPolynomialLift p y)
      (volume.restrict (Ioc (-1) x)) :=
    ((hq.comp (measurable_const.sub measurable_id)).mul
      (continuous_centeredPolynomialLift p).measurable).aestronglyMeasurable
  have hbound : ∀ᵐ y : ℝ ∂(volume.restrict (Ioc (-1) x)),
      ‖q (x - y) * centeredPolynomialLift p y‖ ≤ g y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hlag : x - y ∈ Icc (0 : ℝ) 2 :=
      ⟨by linarith [hy.2], by linarith [hx.2, hy.1]⟩
    have hqbound := hqC (x - y) hlag
    dsimp only [g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hqbound (abs_nonneg _)
  constructor
  · exact Integrable.mono' hg hmeas hbound
  · simp [hx.1]

private theorem continuousLagRight_centeredPolynomialLift_add_on_Icc
    (q : ℝ → ℝ) (p r : ℝ[X]) (x : ℝ)
    (hq : Measurable q) (C : ℝ)
    (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoContinuousLagRightRepresenter q
        (centeredPolynomialLift (p + r)) x =
      factorTwoContinuousLagRightRepresenter q
          (centeredPolynomialLift p) x +
        factorTwoContinuousLagRightRepresenter q
          (centeredPolynomialLift r) x := by
  have hp := intervalIntegrable_boundedLag_right_centeredPolynomialLift
    q p x hq C hqC hx
  have hr := intervalIntegrable_boundedLag_right_centeredPolynomialLift
    q r x hq C hqC hx
  unfold factorTwoContinuousLagRightRepresenter
  rw [show (fun y : ℝ ↦ q (y - x) *
      centeredPolynomialLift (p + r) y) =
      fun y ↦ q (y - x) * centeredPolynomialLift p y +
        q (y - x) * centeredPolynomialLift r y by
    funext y
    rw [centeredPolynomialLift_add]
    ring]
  exact intervalIntegral.integral_add hp hr

private theorem continuousLagLeft_centeredPolynomialLift_add_on_Icc
    (q : ℝ → ℝ) (p r : ℝ[X]) (x : ℝ)
    (hq : Measurable q) (C : ℝ)
    (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoContinuousLagLeftRepresenter q
        (centeredPolynomialLift (p + r)) x =
      factorTwoContinuousLagLeftRepresenter q
          (centeredPolynomialLift p) x +
        factorTwoContinuousLagLeftRepresenter q
          (centeredPolynomialLift r) x := by
  have hp := intervalIntegrable_boundedLag_left_centeredPolynomialLift
    q p x hq C hqC hx
  have hr := intervalIntegrable_boundedLag_left_centeredPolynomialLift
    q r x hq C hqC hx
  unfold factorTwoContinuousLagLeftRepresenter
  rw [show (fun y : ℝ ↦ q (x - y) *
      centeredPolynomialLift (p + r) y) =
      fun y ↦ q (x - y) * centeredPolynomialLift p y +
        q (x - y) * centeredPolynomialLift r y by
    funext y
    rw [centeredPolynomialLift_add]
    ring]
  exact intervalIntegral.integral_add hp hr

private theorem continuousLagRight_centeredPolynomialLift_smul
    (q : ℝ → ℝ) (c : ℝ) (p : ℝ[X]) (x : ℝ) :
    factorTwoContinuousLagRightRepresenter q
        (centeredPolynomialLift (c • p)) x =
      c * factorTwoContinuousLagRightRepresenter q
        (centeredPolynomialLift p) x := by
  unfold factorTwoContinuousLagRightRepresenter
  rw [show (fun y : ℝ ↦ q (y - x) *
      centeredPolynomialLift (c • p) y) =
      fun y ↦ c * (q (y - x) * centeredPolynomialLift p y) by
    funext y
    rw [centeredPolynomialLift_smul]
    ring,
    intervalIntegral.integral_const_mul]

private theorem continuousLagLeft_centeredPolynomialLift_smul
    (q : ℝ → ℝ) (c : ℝ) (p : ℝ[X]) (x : ℝ) :
    factorTwoContinuousLagLeftRepresenter q
        (centeredPolynomialLift (c • p)) x =
      c * factorTwoContinuousLagLeftRepresenter q
        (centeredPolynomialLift p) x := by
  unfold factorTwoContinuousLagLeftRepresenter
  rw [show (fun y : ℝ ↦ q (x - y) *
      centeredPolynomialLift (c • p) y) =
      fun y ↦ c * (q (x - y) * centeredPolynomialLift p y) by
    funext y
    rw [centeredPolynomialLift_smul]
    ring,
    intervalIntegral.integral_const_mul]

private theorem continuousLagK_threeSelectorPolynomial_on_Icc
    (q : ℝ → ℝ) (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (hq : Measurable q) (C : ℝ)
    (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoContinuousLagK q
        (centeredPolynomialLift
          (threeSelectorPolynomial c0 c2 c4 q0 q2 q4)) x =
      c0 * factorTwoContinuousLagK q (centeredPolynomialLift q0) x +
        c2 * factorTwoContinuousLagK q (centeredPolynomialLift q2) x +
        c4 * factorTwoContinuousLagK q (centeredPolynomialLift q4) x := by
  unfold factorTwoContinuousLagK threeSelectorPolynomial
  rw [continuousLagRight_centeredPolynomialLift_add_on_Icc
      q (c0 • q0 + c2 • q2) (c4 • q4) x hq C hqC hx,
    continuousLagRight_centeredPolynomialLift_add_on_Icc
      q (c0 • q0) (c2 • q2) x hq C hqC hx,
    continuousLagLeft_centeredPolynomialLift_add_on_Icc
      q (c0 • q0 + c2 • q2) (c4 • q4) x hq C hqC hx,
    continuousLagLeft_centeredPolynomialLift_add_on_Icc
      q (c0 • q0) (c2 • q2) x hq C hqC hx,
    continuousLagRight_centeredPolynomialLift_smul,
    continuousLagRight_centeredPolynomialLift_smul,
    continuousLagRight_centeredPolynomialLift_smul,
    continuousLagLeft_centeredPolynomialLift_smul,
    continuousLagLeft_centeredPolynomialLift_smul,
    continuousLagLeft_centeredPolynomialLift_smul]
  ring

private theorem continuousLagJ_threeSelectorPolynomial_on_Icc
    (q : ℝ → ℝ) (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (hq : Measurable q) (C : ℝ)
    (hqC : ∀ t ∈ Icc (0 : ℝ) 2, |q t| ≤ C)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoContinuousLagJ q
        (centeredPolynomialLift
          (threeSelectorPolynomial c0 c2 c4 q0 q2 q4)) x =
      c0 * factorTwoContinuousLagJ q (centeredPolynomialLift q0) x +
        c2 * factorTwoContinuousLagJ q (centeredPolynomialLift q2) x +
        c4 * factorTwoContinuousLagJ q (centeredPolynomialLift q4) x := by
  unfold factorTwoContinuousLagJ threeSelectorPolynomial
  rw [continuousLagRight_centeredPolynomialLift_add_on_Icc
      q (c0 • q0 + c2 • q2) (c4 • q4) x hq C hqC hx,
    continuousLagRight_centeredPolynomialLift_add_on_Icc
      q (c0 • q0) (c2 • q2) x hq C hqC hx,
    continuousLagLeft_centeredPolynomialLift_add_on_Icc
      q (c0 • q0 + c2 • q2) (c4 • q4) x hq C hqC hx,
    continuousLagLeft_centeredPolynomialLift_add_on_Icc
      q (c0 • q0) (c2 • q2) x hq C hqC hx,
    continuousLagRight_centeredPolynomialLift_smul,
    continuousLagRight_centeredPolynomialLift_smul,
    continuousLagRight_centeredPolynomialLift_smul,
    continuousLagLeft_centeredPolynomialLift_smul,
    continuousLagLeft_centeredPolynomialLift_smul,
    continuousLagLeft_centeredPolynomialLift_smul]
  ring

private theorem centeredMoment_threeSelectorPolynomial
    (k : ℝ → ℝ) (hk : Continuous k)
    (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X]) :
    (∫ x : ℝ in -1..1,
        k x * centeredPolynomialLift
          (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) x) =
      c0 * (∫ x : ℝ in -1..1,
        k x * centeredPolynomialLift q0 x) +
      c2 * (∫ x : ℝ in -1..1,
        k x * centeredPolynomialLift q2 x) +
      c4 * (∫ x : ℝ in -1..1,
        k x * centeredPolynomialLift q4 x) := by
  have h0 : IntervalIntegrable
      (fun x : ℝ ↦ k x * centeredPolynomialLift q0 x)
      volume (-1) 1 :=
    (hk.mul (continuous_centeredPolynomialLift q0)).intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ k x * centeredPolynomialLift q2 x)
      volume (-1) 1 :=
    (hk.mul (continuous_centeredPolynomialLift q2)).intervalIntegrable (-1) 1
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ k x * centeredPolynomialLift q4 x)
      volume (-1) 1 :=
    (hk.mul (continuous_centeredPolynomialLift q4)).intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦ k x *
      centeredPolynomialLift
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) x) =
      fun x ↦
        c0 * (k x * centeredPolynomialLift q0 x) +
        c2 * (k x * centeredPolynomialLift q2 x) +
        c4 * (k x * centeredPolynomialLift q4 x) by
    funext x
    rw [centeredPolynomialLift_threeSelectorPolynomial]
    ring,
    intervalIntegral.integral_add
      ((h0.const_mul c0).add (h2.const_mul c2)) (h4.const_mul c4),
    intervalIntegral.integral_add (h0.const_mul c0) (h2.const_mul c2)]
  repeat rw [intervalIntegral.integral_const_mul]

private theorem coshMoment_threeSelectorPolynomial
    (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X]) :
    yoshidaEndpointCoshMoment
        (centeredPolynomialLift
          (threeSelectorPolynomial c0 c2 c4 q0 q2 q4)) =
      c0 * yoshidaEndpointCoshMoment (centeredPolynomialLift q0) +
        c2 * yoshidaEndpointCoshMoment (centeredPolynomialLift q2) +
        c4 * yoshidaEndpointCoshMoment (centeredPolynomialLift q4) := by
  unfold yoshidaEndpointCoshMoment
  exact centeredMoment_threeSelectorPolynomial
    (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2))
    (by fun_prop) c0 c2 c4 q0 q2 q4

private theorem sinhMoment_threeSelectorPolynomial
    (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X]) :
    yoshidaEndpointSinhMoment
        (centeredPolynomialLift
          (threeSelectorPolynomial c0 c2 c4 q0 q2 q4)) =
      c0 * yoshidaEndpointSinhMoment (centeredPolynomialLift q0) +
        c2 * yoshidaEndpointSinhMoment (centeredPolynomialLift q2) +
        c4 * yoshidaEndpointSinhMoment (centeredPolynomialLift q4) := by
  unfold yoshidaEndpointSinhMoment
  exact centeredMoment_threeSelectorPolynomial
    (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2))
    (by fun_prop) c0 c2 c4 q0 q2 q4

private theorem cleanSurvivor_threeSelectorPolynomial_on_Icc
    (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenCleanSurvivorRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) x =
      c0 * factorTwoIntrinsicElevenCleanSurvivorRepresenter q0 x +
        c2 * factorTwoIntrinsicElevenCleanSurvivorRepresenter q2 x +
        c4 * factorTwoIntrinsicElevenCleanSurvivorRepresenter q4 x := by
  unfold factorTwoIntrinsicElevenCleanSurvivorRepresenter
  rw [centeredPolynomialLift_threeSelectorPolynomial,
    regularRepresenter_threeSelectorPolynomial_on_Icc c0 c2 c4 q0 q2 q4 x hx,
    coshMoment_threeSelectorPolynomial,
    sinhMoment_threeSelectorPolynomial]
  ring

private theorem fixedLagK_threeSelectorPolynomial
    (tau c0 c2 c4 x : ℝ) (q0 q2 q4 : ℝ[X]) :
    factorTwoFixedLagK tau
        (centeredPolynomialLift
          (threeSelectorPolynomial c0 c2 c4 q0 q2 q4)) x =
      c0 * factorTwoFixedLagK tau (centeredPolynomialLift q0) x +
        c2 * factorTwoFixedLagK tau (centeredPolynomialLift q2) x +
        c4 * factorTwoFixedLagK tau (centeredPolynomialLift q4) x := by
  unfold factorTwoFixedLagK factorTwoFixedLagRightRepresenter
    factorTwoFixedLagLeftRepresenter
  by_cases hR : x ∈ Icc (-1 : ℝ) (1 - tau) <;>
    by_cases hL : x ∈ Icc (-1 + tau) 1 <;>
    simp [hR, hL] <;>
    repeat' rw [centeredPolynomialLift_threeSelectorPolynomial] <;>
    ring

private theorem fixedLagJ_threeSelectorPolynomial
    (tau c0 c2 c4 x : ℝ) (q0 q2 q4 : ℝ[X]) :
    factorTwoFixedLagJ tau
        (centeredPolynomialLift
          (threeSelectorPolynomial c0 c2 c4 q0 q2 q4)) x =
      c0 * factorTwoFixedLagJ tau (centeredPolynomialLift q0) x +
        c2 * factorTwoFixedLagJ tau (centeredPolynomialLift q2) x +
        c4 * factorTwoFixedLagJ tau (centeredPolynomialLift q4) x := by
  unfold factorTwoFixedLagJ factorTwoFixedLagRightRepresenter
    factorTwoFixedLagLeftRepresenter
  by_cases hR : x ∈ Icc (-1 : ℝ) (1 - tau) <;>
    by_cases hL : x ∈ Icc (-1 + tau) 1 <;>
    simp [hR, hL] <;>
    repeat' rw [centeredPolynomialLift_threeSelectorPolynomial] <;>
    ring

private theorem forwardPoleKLogSelector_threeSelectorPolynomial
    (c0 c2 c4 x : ℝ) (q0 q2 q4 : ℝ[X]) :
    forwardPoleKLogSelector
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) x =
      c0 * forwardPoleKLogSelector q0 x +
        c2 * forwardPoleKLogSelector q2 x +
        c4 * forwardPoleKLogSelector q4 x := by
  unfold forwardPoleKLogSelector threeSelectorPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  ring

private theorem forwardPoleLLogSelector_threeSelectorPolynomial
    (c0 c2 c4 x : ℝ) (q0 q2 q4 : ℝ[X]) :
    forwardPoleLLogSelector
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) x =
      c0 * forwardPoleLLogSelector q0 x +
        c2 * forwardPoleLLogSelector q2 x +
        c4 * forwardPoleLLogSelector q4 x := by
  unfold forwardPoleLLogSelector threeSelectorPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  ring

private theorem reflectedPoleKLogSelector_threeSelectorPolynomial
    (c0 c2 c4 x : ℝ) (q0 q2 q4 : ℝ[X]) :
    reflectedPoleKLogSelector
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) x =
      c0 * reflectedPoleKLogSelector q0 x +
        c2 * reflectedPoleKLogSelector q2 x +
        c4 * reflectedPoleKLogSelector q4 x := by
  unfold reflectedPoleKLogSelector threeSelectorPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  ring

private theorem reflectedPoleJLogSelector_threeSelectorPolynomial
    (c0 c2 c4 x : ℝ) (q0 q2 q4 : ℝ[X]) :
    reflectedPoleJLogSelector
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) x =
      c0 * reflectedPoleJLogSelector q0 x +
        c2 * reflectedPoleJLogSelector q2 x +
        c4 * reflectedPoleJLogSelector q4 x := by
  unfold reflectedPoleJLogSelector threeSelectorPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  ring

private theorem analyticEven_threeSelectorPolynomial_zero_odd_on_Icc
    (c0 c2 c4 a b : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenAnalyticEvenRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenAnalyticEvenRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenAnalyticEvenRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenAnalyticEvenRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenAnalyticEvenRepresenter
  rw [continuousLagK_threeSelectorPolynomial_on_Icc
      factorTwoSymmetricAnalyticLag c0 c2 c4 q0 q2 q4 x
      measurable_factorTwoSymmetricAnalyticLag (3 / 8000)
      (fun _t ht ↦ abs_factorTwoSymmetricAnalyticLag_le ht) hx,
    centeredPolynomialLift_zero_fun]
  repeat rw [factorTwoContinuousLagJ_zero_right]
  ring

private theorem analyticOdd_threeSelectorPolynomial_zero_odd_on_Icc
    (c0 c2 c4 a b : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenAnalyticOddRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenAnalyticOddRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenAnalyticOddRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenAnalyticOddRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenAnalyticOddRepresenter
  rw [continuousLagJ_threeSelectorPolynomial_on_Icc
      factorTwoAlternatingAnalyticLag c0 c2 c4 q0 q2 q4 x
      measurable_factorTwoAlternatingAnalyticLag (1 / 1000)
      (fun _t ht ↦ abs_factorTwoAlternatingAnalyticLag_le ht) hx,
    centeredPolynomialLift_zero_fun]
  repeat rw [factorTwoContinuousLagK_zero_right]
  ring

private theorem forwardEven_threeSelectorPolynomial_zero_odd
    (c0 c2 c4 a b x : ℝ) (q0 q2 q4 : ℝ[X]) :
    factorTwoIntrinsicElevenForwardEvenRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenForwardEvenRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenForwardEvenRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenForwardEvenRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenForwardEvenRepresenter
  rw [forwardPoleKLogSelector_threeSelectorPolynomial]
  repeat rw [forwardPoleLLogSelector_zero]
  ring

private theorem forwardOdd_threeSelectorPolynomial_zero_odd
    (c0 c2 c4 a b x : ℝ) (q0 q2 q4 : ℝ[X]) :
    factorTwoIntrinsicElevenForwardOddRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenForwardOddRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenForwardOddRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenForwardOddRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenForwardOddRepresenter
  rw [forwardPoleLLogSelector_threeSelectorPolynomial]
  repeat rw [forwardPoleKLogSelector_zero]
  ring

private theorem reflectedEven_threeSelectorPolynomial_zero_odd
    (c0 c2 c4 a b x : ℝ) (q0 q2 q4 : ℝ[X]) :
    factorTwoIntrinsicElevenReflectedEvenRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenReflectedEvenRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenReflectedEvenRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenReflectedEvenRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenReflectedEvenRepresenter
  rw [reflectedPoleKLogSelector_threeSelectorPolynomial]
  repeat rw [reflectedPoleJLogSelector_zero]
  ring

private theorem reflectedOdd_threeSelectorPolynomial_zero_odd
    (c0 c2 c4 a b x : ℝ) (q0 q2 q4 : ℝ[X]) :
    factorTwoIntrinsicElevenReflectedOddRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenReflectedOddRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenReflectedOddRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenReflectedOddRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenReflectedOddRepresenter
  rw [reflectedPoleJLogSelector_threeSelectorPolynomial]
  repeat rw [reflectedPoleKLogSelector_zero]
  ring

private theorem primeEven_threeSelectorPolynomial_zero_odd
    (c0 c2 c4 a b x : ℝ) (q0 q2 q4 : ℝ[X]) :
    factorTwoIntrinsicElevenPrimeEvenRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenPrimeEvenRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenPrimeEvenRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenPrimeEvenRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenPrimeEvenRepresenter
  rw [fixedLagK_threeSelectorPolynomial, centeredPolynomialLift_zero_fun]
  repeat rw [factorTwoFixedLagJ_zero_right]
  ring

private theorem primeOdd_threeSelectorPolynomial_zero_odd
    (c0 c2 c4 a b x : ℝ) (q0 q2 q4 : ℝ[X]) :
    factorTwoIntrinsicElevenPrimeOddRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenPrimeOddRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenPrimeOddRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenPrimeOddRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenPrimeOddRepresenter
  rw [fixedLagJ_threeSelectorPolynomial, centeredPolynomialLift_zero_fun]
  repeat rw [factorTwoFixedLagK_zero_right]
  ring

private theorem completeEven_threeSelectorPolynomial_zero_odd_on_Icc
    (c0 c2 c4 a b : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenEvenMixedRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenEvenMixedRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenEvenMixedRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenEvenMixedRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenEvenMixedRepresenter
  rw [cleanSurvivor_threeSelectorPolynomial_on_Icc c0 c2 c4 q0 q2 q4 x hx,
    analyticEven_threeSelectorPolynomial_zero_odd_on_Icc
      c0 c2 c4 a b q0 q2 q4 x hx,
    forwardEven_threeSelectorPolynomial_zero_odd,
    reflectedEven_threeSelectorPolynomial_zero_odd,
    primeEven_threeSelectorPolynomial_zero_odd]
  ring

private theorem completeOdd_threeSelectorPolynomial_zero_odd_on_Icc
    (c0 c2 c4 a b : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenOddMixedRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenOddMixedRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenOddMixedRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenOddMixedRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenOddMixedRepresenter
  repeat rw [factorTwoIntrinsicElevenCleanSurvivorRepresenter_zero]
  rw [analyticOdd_threeSelectorPolynomial_zero_odd_on_Icc
      c0 c2 c4 a b q0 q2 q4 x hx,
    forwardOdd_threeSelectorPolynomial_zero_odd,
    reflectedOdd_threeSelectorPolynomial_zero_odd,
    primeOdd_threeSelectorPolynomial_zero_odd]
  ring

private theorem potentialPoleEven_threeSelectorPolynomial_zero_odd_on_Icc
    (c0 c2 c4 a b : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (_hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenPotentialPoleEvenRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenPotentialPoleEvenRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenPotentialPoleEvenRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenPotentialPoleEvenRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenPotentialPoleEvenRepresenter
  rw [centeredPolynomialLift_threeSelectorPolynomial,
    reflectedEven_threeSelectorPolynomial_zero_odd]
  ring

private theorem potentialPoleOdd_threeSelectorPolynomial_zero_odd_on_Icc
    (c0 c2 c4 a b : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (_hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenPotentialPoleOddRepresenter
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      c0 * factorTwoIntrinsicElevenPotentialPoleOddRepresenter q0 0 a b x +
        c2 * factorTwoIntrinsicElevenPotentialPoleOddRepresenter q2 0 a b x +
        c4 * factorTwoIntrinsicElevenPotentialPoleOddRepresenter q4 0 a b x := by
  unfold factorTwoIntrinsicElevenPotentialPoleOddRepresenter
  repeat rw [centeredPolynomialLift_zero]
  rw [reflectedOdd_threeSelectorPolynomial_zero_odd]
  ring

/-- On the physical interval, the retained even production row is linear in
the concrete three-coordinate low polynomial. -/
theorem retainedEvenMixedRepresenterAt_threeSelectorPolynomial_on_Icc
    (gamma c0 c2 c4 a b : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt gamma
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      threeSelectorRepresenter c0 c2 c4
        (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt gamma q0 0 a b)
        (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt gamma q2 0 a b)
        (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt gamma q4 0 a b) x := by
  unfold factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    threeSelectorRepresenter
  rw [completeEven_threeSelectorPolynomial_zero_odd_on_Icc
      c0 c2 c4 a b q0 q2 q4 x hx,
    potentialPoleEven_threeSelectorPolynomial_zero_odd_on_Icc
      c0 c2 c4 a b q0 q2 q4 x hx]
  ring

/-- Odd-channel analogue of
`retainedEvenMixedRepresenterAt_threeSelectorPolynomial_on_Icc`. -/
theorem retainedOddMixedRepresenterAt_threeSelectorPolynomial_on_Icc
    (gamma c0 c2 c4 a b : ℝ) (q0 q2 q4 : ℝ[X])
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt gamma
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) 0 a b x =
      threeSelectorRepresenter c0 c2 c4
        (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt gamma q0 0 a b)
        (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt gamma q2 0 a b)
        (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt gamma q4 0 a b) x := by
  unfold factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
    threeSelectorRepresenter
  rw [completeOdd_threeSelectorPolynomial_zero_odd_on_Icc
      c0 c2 c4 a b q0 q2 q4 x hx,
    potentialPoleOdd_threeSelectorPolynomial_zero_odd_on_Icc
      c0 c2 c4 a b q0 q2 q4 x hx]
  ring

/-- A pointwise equality of selector representers on the physical interval
preserves their one-channel weighted dual cost. -/
theorem factorTwoIntrinsicElevenSelectorDual_congr_on_Icc
    (W F G : ℝ → ℝ) (q : ℝ[X])
    (h : ∀ x ∈ Icc (-1 : ℝ) 1, F x = G x) :
    factorTwoIntrinsicElevenSelectorDual W F q =
      factorTwoIntrinsicElevenSelectorDual W G q := by
  unfold factorTwoIntrinsicElevenSelectorDual
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  dsimp only
  unfold factorTwoIntrinsicElevenSelectorResidual
  rw [h x hx]

/-- A pointwise equality of both retained rows on the physical interval
preserves every two-channel selector cost. -/
theorem factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_congr_on_Icc
    (FE GE FO GO : ℝ → ℝ) (qE qO : ℝ[X])
    (hE : ∀ x ∈ Icc (-1 : ℝ) 1, FE x = GE x)
    (hO : ∀ x ∈ Icc (-1 : ℝ) 1, FO x = GO x) :
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual FE FO qE qO =
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual GE GO qE qO := by
  unfold factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
    factorTwoIntrinsicElevenSelectorDual
  congr 1
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    dsimp only
    unfold factorTwoIntrinsicElevenSelectorResidual
    rw [hE x hx]
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    dsimp only
    unfold factorTwoIntrinsicElevenSelectorResidual
    rw [hO x hx]

theorem threeSelectorResidual_eq
    (c0 c2 c4 : ℝ) (F0 F2 F4 : ℝ → ℝ)
    (q0 q2 q4 : ℝ[X]) (x : ℝ) :
    factorTwoIntrinsicElevenSelectorResidual
        (threeSelectorRepresenter c0 c2 c4 F0 F2 F4)
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) x =
      c0 * factorTwoIntrinsicElevenSelectorResidual F0 q0 x +
        c2 * factorTwoIntrinsicElevenSelectorResidual F2 q2 x +
        c4 * factorTwoIntrinsicElevenSelectorResidual F4 q4 x := by
  unfold factorTwoIntrinsicElevenSelectorResidual
    threeSelectorRepresenter threeSelectorPolynomial centeredPolynomialLift
  simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  ring

/-- Polarized weighted selector pairing.  Its diagonal is the selector dual
cost, and its six entries are the exact Gram data for a three-coordinate
low slice. -/
def factorTwoIntrinsicElevenSelectorCrossDual
    (W F G : ℝ → ℝ) (p q : ℝ[X]) : ℝ :=
  ∫ x : ℝ in -1..1,
    factorTwoIntrinsicElevenSelectorResidual F p x *
      factorTwoIntrinsicElevenSelectorResidual G q x / W x

theorem factorTwoIntrinsicElevenSelectorCrossDual_self
    (W F : ℝ → ℝ) (p : ℝ[X]) :
    factorTwoIntrinsicElevenSelectorCrossDual W F F p p =
      factorTwoIntrinsicElevenSelectorDual W F p := by
  unfold factorTwoIntrinsicElevenSelectorCrossDual
    factorTwoIntrinsicElevenSelectorDual
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

/-- Integrability package needed only to distribute the interval integral
over the six entries of a three-coordinate weighted Gram. -/
structure ThreeSelectorGramIntegrable
    (W F0 F2 F4 : ℝ → ℝ) (q0 q2 q4 : ℝ[X]) : Prop where
  i00 : IntervalIntegrable (fun x ↦
    factorTwoIntrinsicElevenSelectorResidual F0 q0 x *
      factorTwoIntrinsicElevenSelectorResidual F0 q0 x / W x)
    volume (-1) 1
  i02 : IntervalIntegrable (fun x ↦
    factorTwoIntrinsicElevenSelectorResidual F0 q0 x *
      factorTwoIntrinsicElevenSelectorResidual F2 q2 x / W x)
    volume (-1) 1
  i04 : IntervalIntegrable (fun x ↦
    factorTwoIntrinsicElevenSelectorResidual F0 q0 x *
      factorTwoIntrinsicElevenSelectorResidual F4 q4 x / W x)
    volume (-1) 1
  i22 : IntervalIntegrable (fun x ↦
    factorTwoIntrinsicElevenSelectorResidual F2 q2 x *
      factorTwoIntrinsicElevenSelectorResidual F2 q2 x / W x)
    volume (-1) 1
  i24 : IntervalIntegrable (fun x ↦
    factorTwoIntrinsicElevenSelectorResidual F2 q2 x *
      factorTwoIntrinsicElevenSelectorResidual F4 q4 x / W x)
    volume (-1) 1
  i44 : IntervalIntegrable (fun x ↦
    factorTwoIntrinsicElevenSelectorResidual F4 q4 x *
      factorTwoIntrinsicElevenSelectorResidual F4 q4 x / W x)
    volume (-1) 1

/-- Two normalized weighted-dual `L²` rows have an integrable polarized
Gram entry. -/
theorem intervalIntegrable_selectorCross_of_memLp
    (W F G : ℝ → ℝ) (p q : ℝ[X])
    (hW : ∀ x ∈ Icc (-1 : ℝ) 1, 0 < W x)
    (hF : MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual F p x /
        Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hG : MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual G q x /
        Real.sqrt (W x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1))) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual F p x *
        factorTwoIntrinsicElevenSelectorResidual G q x / W x)
      volume (-1) 1 := by
  let mu : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hscaled : Integrable (fun x : ℝ ↦
      (factorTwoIntrinsicElevenSelectorResidual F p x /
          Real.sqrt (W x)) *
        (factorTwoIntrinsicElevenSelectorResidual G q x /
          Real.sqrt (W x))) mu := by
    have h := hF.integrable_mul hG
    simpa only [mu, Pi.mul_apply] using h
  have hscaledEq : ∀ᵐ x ∂mu,
      (factorTwoIntrinsicElevenSelectorResidual F p x /
          Real.sqrt (W x)) *
        (factorTwoIntrinsicElevenSelectorResidual G q x /
          Real.sqrt (W x)) =
      factorTwoIntrinsicElevenSelectorResidual F p x *
        factorTwoIntrinsicElevenSelectorResidual G q x / W x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hWx := hW x ⟨hx.1.le, hx.2⟩
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hWx.le]
  have hcross : Integrable (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual F p x *
        factorTwoIntrinsicElevenSelectorResidual G q x / W x) mu :=
    hscaled.congr hscaledEq
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  simpa only [mu] using hcross

/-- Three retained even rows automatically supply all six integrability
obligations of their weighted selector Gram. -/
theorem retainedEvenThreeSelectorGramIntegrable
    (gamma : ℝ) (p0 p2 p4 q0 q2 q4 : ℝ[X]) (a b : ℝ) :
    ThreeSelectorGramIntegrable
      factorTwoIntrinsicElevenRetainedEvenWeight
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        gamma p0 0 a b)
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        gamma p2 0 a b)
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        gamma p4 0 a b)
      q0 q2 q4 := by
  have h0 :=
    factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma p0 0 q0 a b
  have h2 :=
    factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma p2 0 q2 a b
  have h4 :=
    factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma p4 0 q4 a b
  refine ⟨
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      h0 h0,
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      h0 h2,
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      h0 h4,
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      h2 h2,
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      h2 h4,
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      h4 h4⟩

/-- Odd-channel analogue of `retainedEvenThreeSelectorGramIntegrable`. -/
theorem retainedOddThreeSelectorGramIntegrable
    (gamma : ℝ) (p0 p2 p4 q0 q2 q4 : ℝ[X]) (a b : ℝ) :
    ThreeSelectorGramIntegrable
      factorTwoIntrinsicElevenRetainedOddWeight
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        gamma p0 0 a b)
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        gamma p2 0 a b)
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
        gamma p4 0 a b)
      q0 q2 q4 := by
  have h0 :=
    factorTwoIntrinsicElevenRetainedOddSelectorResidual_div_sqrt_memLp_two
      gamma p0 0 q0 a b
  have h2 :=
    factorTwoIntrinsicElevenRetainedOddSelectorResidual_div_sqrt_memLp_two
      gamma p2 0 q2 a b
  have h4 :=
    factorTwoIntrinsicElevenRetainedOddSelectorResidual_div_sqrt_memLp_two
      gamma p4 0 q4 a b
  refine ⟨
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
      h0 h0,
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
      h0 h2,
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
      h0 h4,
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
      h2 h2,
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
      h2 h4,
    intervalIntegrable_selectorCross_of_memLp _ _ _ _ _
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
      h4 h4⟩

/-- Exact finite-Gram identity for a linear three-coordinate selector.  No
mode enumeration or inequality is used: the weighted dual is literally the
displayed symmetric quadratic in the six polarized selector pairings. -/
theorem factorTwoIntrinsicElevenSelectorDual_three_eq_symmetricQuadratic
    (W F0 F2 F4 : ℝ → ℝ) (q0 q2 q4 : ℝ[X])
    (hInt : ThreeSelectorGramIntegrable W F0 F2 F4 q0 q2 q4)
    (c0 c2 c4 : ℝ) :
    factorTwoIntrinsicElevenSelectorDual W
        (threeSelectorRepresenter c0 c2 c4 F0 F2 F4)
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) =
      symmetricQuadratic
        (factorTwoIntrinsicElevenSelectorCrossDual W F0 F0 q0 q0)
        (factorTwoIntrinsicElevenSelectorCrossDual W F0 F2 q0 q2)
        (factorTwoIntrinsicElevenSelectorCrossDual W F0 F4 q0 q4)
        (factorTwoIntrinsicElevenSelectorCrossDual W F2 F2 q2 q2)
        (factorTwoIntrinsicElevenSelectorCrossDual W F2 F4 q2 q4)
        (factorTwoIntrinsicElevenSelectorCrossDual W F4 F4 q4 q4)
        c0 c2 c4 := by
  let R0 : ℝ → ℝ := factorTwoIntrinsicElevenSelectorResidual F0 q0
  let R2 : ℝ → ℝ := factorTwoIntrinsicElevenSelectorResidual F2 q2
  let R4 : ℝ → ℝ := factorTwoIntrinsicElevenSelectorResidual F4 q4
  let I00 : ℝ → ℝ := fun x ↦ R0 x * R0 x / W x
  let I02 : ℝ → ℝ := fun x ↦ R0 x * R2 x / W x
  let I04 : ℝ → ℝ := fun x ↦ R0 x * R4 x / W x
  let I22 : ℝ → ℝ := fun x ↦ R2 x * R2 x / W x
  let I24 : ℝ → ℝ := fun x ↦ R2 x * R4 x / W x
  let I44 : ℝ → ℝ := fun x ↦ R4 x * R4 x / W x
  have h00 : IntervalIntegrable I00 volume (-1) 1 := by
    simpa only [I00, R0] using hInt.i00
  have h02 : IntervalIntegrable I02 volume (-1) 1 := by
    simpa only [I02, R0, R2] using hInt.i02
  have h04 : IntervalIntegrable I04 volume (-1) 1 := by
    simpa only [I04, R0, R4] using hInt.i04
  have h22 : IntervalIntegrable I22 volume (-1) 1 := by
    simpa only [I22, R2] using hInt.i22
  have h24 : IntervalIntegrable I24 volume (-1) 1 := by
    simpa only [I24, R2, R4] using hInt.i24
  have h44 : IntervalIntegrable I44 volume (-1) 1 := by
    simpa only [I44, R4] using hInt.i44
  have hT00 : IntervalIntegrable (fun x ↦ c0 ^ 2 * I00 x)
      volume (-1) 1 := h00.const_mul _
  have hT02 : IntervalIntegrable (fun x ↦ (2 * c0 * c2) * I02 x)
      volume (-1) 1 := h02.const_mul _
  have hT04 : IntervalIntegrable (fun x ↦ (2 * c0 * c4) * I04 x)
      volume (-1) 1 := h04.const_mul _
  have hT22 : IntervalIntegrable (fun x ↦ c2 ^ 2 * I22 x)
      volume (-1) 1 := h22.const_mul _
  have hT24 : IntervalIntegrable (fun x ↦ (2 * c2 * c4) * I24 x)
      volume (-1) 1 := h24.const_mul _
  have hT44 : IntervalIntegrable (fun x ↦ c4 ^ 2 * I44 x)
      volume (-1) 1 := h44.const_mul _
  unfold factorTwoIntrinsicElevenSelectorDual
  rw [show (fun x : ℝ ↦
      factorTwoIntrinsicElevenSelectorResidual
          (threeSelectorRepresenter c0 c2 c4 F0 F2 F4)
          (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) x ^ 2 / W x) =
      fun x ↦
        (((((c0 ^ 2 * I00 x + (2 * c0 * c2) * I02 x) +
          (2 * c0 * c4) * I04 x) + c2 ^ 2 * I22 x) +
          (2 * c2 * c4) * I24 x) + c4 ^ 2 * I44 x) by
    funext x
    rw [threeSelectorResidual_eq]
    dsimp only [I00, I02, I04, I22, I24, I44, R0, R2, R4]
    ring]
  rw [intervalIntegral.integral_add
      ((((hT00.add hT02).add hT04).add hT22).add hT24) hT44,
    intervalIntegral.integral_add
      (((hT00.add hT02).add hT04).add hT22) hT24,
    intervalIntegral.integral_add
      ((hT00.add hT02).add hT04) hT22,
    intervalIntegral.integral_add (hT00.add hT02) hT04,
    intervalIntegral.integral_add hT00 hT02]
  repeat rw [intervalIntegral.integral_const_mul]
  unfold factorTwoIntrinsicElevenSelectorCrossDual symmetricQuadratic
  dsimp only [I00, I02, I04, I22, I24, I44, R0, R2, R4]
  ring

/-- Polarized two-channel retained selector pairing. -/
def factorTwoIntrinsicElevenRetainedSelectorCrossDual
    (FE GE FO GO : ℝ → ℝ)
    (pE qE pO qO : ℝ[X]) : ℝ :=
  factorTwoIntrinsicElevenSelectorCrossDual
      factorTwoIntrinsicElevenRetainedEvenWeight FE GE pE qE +
    factorTwoIntrinsicElevenSelectorCrossDual
      factorTwoIntrinsicElevenRetainedOddWeight FO GO pO qO

/-- Exact two-channel three-coordinate Gram identity. -/
theorem
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_three_eq_symmetricQuadratic
    (FE0 FE2 FE4 FO0 FO2 FO4 : ℝ → ℝ)
    (qE0 qE2 qE4 qO0 qO2 qO4 : ℝ[X])
    (hEven : ThreeSelectorGramIntegrable
      factorTwoIntrinsicElevenRetainedEvenWeight
      FE0 FE2 FE4 qE0 qE2 qE4)
    (hOdd : ThreeSelectorGramIntegrable
      factorTwoIntrinsicElevenRetainedOddWeight
      FO0 FO2 FO4 qO0 qO2 qO4)
    (c0 c2 c4 : ℝ) :
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
        (threeSelectorRepresenter c0 c2 c4 FE0 FE2 FE4)
        (threeSelectorRepresenter c0 c2 c4 FO0 FO2 FO4)
        (threeSelectorPolynomial c0 c2 c4 qE0 qE2 qE4)
        (threeSelectorPolynomial c0 c2 c4 qO0 qO2 qO4) =
      symmetricQuadratic
        (factorTwoIntrinsicElevenRetainedSelectorCrossDual
          FE0 FE0 FO0 FO0 qE0 qE0 qO0 qO0)
        (factorTwoIntrinsicElevenRetainedSelectorCrossDual
          FE0 FE2 FO0 FO2 qE0 qE2 qO0 qO2)
        (factorTwoIntrinsicElevenRetainedSelectorCrossDual
          FE0 FE4 FO0 FO4 qE0 qE4 qO0 qO4)
        (factorTwoIntrinsicElevenRetainedSelectorCrossDual
          FE2 FE2 FO2 FO2 qE2 qE2 qO2 qO2)
        (factorTwoIntrinsicElevenRetainedSelectorCrossDual
          FE2 FE4 FO2 FO4 qE2 qE4 qO2 qO4)
        (factorTwoIntrinsicElevenRetainedSelectorCrossDual
          FE4 FE4 FO4 FO4 qE4 qE4 qO4 qO4)
        c0 c2 c4 := by
  unfold factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
  rw [factorTwoIntrinsicElevenSelectorDual_three_eq_symmetricQuadratic
      _ _ _ _ _ _ _ hEven,
    factorTwoIntrinsicElevenSelectorDual_three_eq_symmetricQuadratic
      _ _ _ _ _ _ _ hOdd]
  unfold factorTwoIntrinsicElevenRetainedSelectorCrossDual symmetricQuadratic
  ring

/-- A strict `3 x 3` gap between a target low quadratic and the exact
two-channel selector Gram constructs selectors for every coefficient vector.
This is the structural finite Schur bridge used by the retained `P₀/P₂/P₄`
slice; its hypotheses are six exact Gram entries and three scalar pivots. -/
theorem exists_threeSelector_of_strict_gap_pivots
    (FE0 FE2 FE4 FO0 FO2 FO4 : ℝ → ℝ)
    (qE0 qE2 qE4 qO0 qO2 qO4 : ℝ[X])
    (hqE0 : qE0.natDegree < 11) (hqE2 : qE2.natDegree < 11)
    (hqE4 : qE4.natDegree < 11) (hqO0 : qO0.natDegree < 11)
    (hqO2 : qO2.natDegree < 11) (hqO4 : qO4.natDegree < 11)
    (hEven : ThreeSelectorGramIntegrable
      factorTwoIntrinsicElevenRetainedEvenWeight
      FE0 FE2 FE4 qE0 qE2 qE4)
    (hOdd : ThreeSelectorGramIntegrable
      factorTwoIntrinsicElevenRetainedOddWeight
      FO0 FO2 FO4 qO0 qO2 qO4)
    (L00 L02 L04 L22 L24 L44 : ℝ)
    (h00 : 0 < L00 -
      factorTwoIntrinsicElevenRetainedSelectorCrossDual
        FE0 FE0 FO0 FO0 qE0 qE0 qO0 qO0)
    (hminor : 0 < leadingMinorTwo
      (L00 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
        FE0 FE0 FO0 FO0 qE0 qE0 qO0 qO0)
      (L02 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
        FE0 FE2 FO0 FO2 qE0 qE2 qO0 qO2)
      (L22 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
        FE2 FE2 FO2 FO2 qE2 qE2 qO2 qO2))
    (hdet : 0 < symmetricDeterminant
      (L00 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
        FE0 FE0 FO0 FO0 qE0 qE0 qO0 qO0)
      (L02 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
        FE0 FE2 FO0 FO2 qE0 qE2 qO0 qO2)
      (L04 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
        FE0 FE4 FO0 FO4 qE0 qE4 qO0 qO4)
      (L22 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
        FE2 FE2 FO2 FO2 qE2 qE2 qO2 qO2)
      (L24 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
        FE2 FE4 FO2 FO4 qE2 qE4 qO2 qO4)
      (L44 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
        FE4 FE4 FO4 FO4 qE4 qE4 qO4 qO4))
    (c0 c2 c4 : ℝ) :
    ∃ qE qO : ℝ[X],
      qE.natDegree < 11 ∧ qO.natDegree < 11 ∧
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (threeSelectorRepresenter c0 c2 c4 FE0 FE2 FE4)
          (threeSelectorRepresenter c0 c2 c4 FO0 FO2 FO4)
          qE qO ≤
        symmetricQuadratic L00 L02 L04 L22 L24 L44 c0 c2 c4 := by
  let qE := threeSelectorPolynomial c0 c2 c4 qE0 qE2 qE4
  let qO := threeSelectorPolynomial c0 c2 c4 qO0 qO2 qO4
  refine ⟨qE, qO,
    threeSelectorPolynomial_natDegree_lt
      c0 c2 c4 qE0 qE2 qE4 hqE0 hqE2 hqE4,
    threeSelectorPolynomial_natDegree_lt
      c0 c2 c4 qO0 qO2 qO4 hqO0 hqO2 hqO4, ?_⟩
  have hGram :=
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_three_eq_symmetricQuadratic
      FE0 FE2 FE4 FO0 FO2 FO4 qE0 qE2 qE4 qO0 qO2 qO4
      hEven hOdd c0 c2 c4
  have hgap := symmetricQuadratic_nonneg
    (L00 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
      FE0 FE0 FO0 FO0 qE0 qE0 qO0 qO0)
    (L02 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
      FE0 FE2 FO0 FO2 qE0 qE2 qO0 qO2)
    (L04 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
      FE0 FE4 FO0 FO4 qE0 qE4 qO0 qO4)
    (L22 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
      FE2 FE2 FO2 FO2 qE2 qE2 qO2 qO2)
    (L24 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
      FE2 FE4 FO2 FO4 qE2 qE4 qO2 qO4)
    (L44 - factorTwoIntrinsicElevenRetainedSelectorCrossDual
      FE4 FE4 FO4 FO4 qE4 qE4 qO4 qO4)
    h00 hminor hdet c0 c2 c4
  rw [hGram]
  unfold symmetricQuadratic at hgap ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
