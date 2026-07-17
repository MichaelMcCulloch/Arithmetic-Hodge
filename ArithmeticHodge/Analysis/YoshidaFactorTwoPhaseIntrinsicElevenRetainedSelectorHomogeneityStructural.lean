import ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoContinuousLagRepresenterStructural
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFactorTwoForwardPolePolynomialReductionStructural
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConcreteSelectorsStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoReflectedPolePolynomialReductionStructural

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
