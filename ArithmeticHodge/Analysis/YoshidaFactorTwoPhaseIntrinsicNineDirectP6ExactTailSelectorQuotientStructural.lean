import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorGramStructural

set_option autoImplicit false

open Matrix Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorQuotientStructural

noncomputable section

open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConcreteSelectorsStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorPoleRemainderStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailResidualStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6RetainedRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoReflectedPoleEntropyStructural

/-!
# Exact quotient removal for the direct `P6` selector rows

The retained endpoint weight is affine in the singular endpoint potential.
Consequently each exact pole-subtracted selector row splits on the physical
interval as

`residual = weight * poleRow + shiftedRemainder`.

This identity removes the singular quotient before any estimate is taken.  It
is the structural input for a full-matrix reciprocal-majorant bound on the two
concrete endpoint selector Grams.
-/

/-- The exact selector residual in the `i`th endpoint-even basis direction. -/
def factorTwoIntrinsicNineDirectP6ExactResidualRow
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i : Fin 3) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenSelectorResidual
    (factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma i)
    (q i) x

/-- The polynomial correction left after expressing an exact direct `P6` row
in the retained base and symmetric selector coordinates. -/
def factorTwoIntrinsicNineDirectP6ExactSelectorCorrectionPolynomial
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i : Fin 3) : ℝ[X] :=
  factorTwoIntrinsicNineDirectP6RankPolynomial sigma
      (factorTwoIntrinsicNineDirectP024Embed (Pi.single i 1)) +
    retainedP024SelectorWholeEvenPolynomial
      (Sum.inl i : Fin 3 ⊕ Fin 3) +
    sigma • retainedP024SelectorWholeEvenPolynomial
      (Sum.inr i : Fin 3 ⊕ Fin 3) -
    q i

/-- The exact affine pole row in the `i`th direct endpoint direction. -/
def factorTwoIntrinsicNineDirectP6ExactResidualPoleRow
    (sigma : ℝ) (i : Fin 3) (x : ℝ) : ℝ :=
  retainedP024SelectorWholeEvenPoleRow
      (Sum.inl i : Fin 3 ⊕ Fin 3) x +
    sigma * retainedP024SelectorWholeEvenPoleRow
      (Sum.inr i : Fin 3 ⊕ Fin 3) x

/-- The direct endpoint pole row has no hidden selector dependence: it is the
retained `P0/P2/P4` mode plus one constant symmetric trace. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualPoleRow_eq
    (sigma : ℝ) (i : Fin 3) (x : ℝ) :
    factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma i x =
      (511 / 252 : ℝ) *
          centeredPolynomialLift
            (ShiftedLegendreOrthogonality.shiftedLegendreReal (2 * i.1)) x -
        sigma * (511 / 504 : ℝ) := by
  unfold factorTwoIntrinsicNineDirectP6ExactResidualPoleRow
    retainedP024SelectorWholeEvenPoleRow retainedP024EvenMode
  ring

/-- The bounded shifted remainder after the exact pole row has been removed. -/
def factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i : Fin 3) (x : ℝ) : ℝ :=
  retainedP024SelectorWholeEvenShiftedRemainder
      (Sum.inl i : Fin 3 ⊕ Fin 3) x +
    sigma * retainedP024SelectorWholeEvenShiftedRemainder
      (Sum.inr i : Fin 3 ⊕ Fin 3) x +
    centeredPolynomialLift
      (factorTwoIntrinsicNineDirectP6ExactSelectorCorrectionPolynomial
        sigma q i) x

/-- A retained remainder with its auxiliary high-degree selector put back.
This is the quantity in which the old `P0/P2/P4` selector disappears from the
new direct endpoint row. -/
def factorTwoIntrinsicNineDirectP6SelectorFreeRetainedRemainder
    (k : Fin 3 ⊕ Fin 3) (x : ℝ) : ℝ :=
  retainedP024SelectorWholeEvenRemainder k x +
    centeredPolynomialLift (retainedP024SelectorWholeEvenPolynomial k) x

theorem factorTwoIntrinsicNineDirectP6SelectorFreeRetainedRemainder_inl
    (i : Fin 3) (x : ℝ) :
    factorTwoIntrinsicNineDirectP6SelectorFreeRetainedRemainder
        (Sum.inl i : Fin 3 ⊕ Fin 3) x =
      factorTwoIntrinsicElevenCleanSurvivorRepresenter
          (retainedP024EvenMode i) x -
        yoshidaEndpointPotential x *
          centeredPolynomialLift (retainedP024EvenMode i) x := by
  unfold factorTwoIntrinsicNineDirectP6SelectorFreeRetainedRemainder
    retainedP024SelectorWholeEvenRemainder
    retainedP024SelectorWholeEvenPolynomial
    retainedP024SelectorBaseRemainder
  ring

theorem factorTwoIntrinsicNineDirectP6SelectorFreeRetainedRemainder_inr
    (i : Fin 3) (x : ℝ) :
    factorTwoIntrinsicNineDirectP6SelectorFreeRetainedRemainder
        (Sum.inr i : Fin 3 ⊕ Fin 3) x =
      factorTwoIntrinsicElevenAnalyticEvenRepresenter
          (retainedP024EvenMode i) 0 1 0 x +
        factorTwoIntrinsicElevenForwardEvenRepresenter
          (retainedP024EvenMode i) 0 1 0 x +
        factorTwoIntrinsicElevenPrimeEvenRepresenter
          (retainedP024EvenMode i) 0 1 0 x -
        (511 / 2048 : ℝ) *
          (retainedP024KPotentialTraceRemainder i x +
            reflectedPoleKEntropyRemainder (retainedP024EvenMode i) x) := by
  unfold factorTwoIntrinsicNineDirectP6SelectorFreeRetainedRemainder
    retainedP024SelectorWholeEvenRemainder
    retainedP024SelectorWholeEvenPolynomial
    retainedP024SelectorSymmetricRemainder
  ring

/-- Cancellation-preserving normal form for the shifted direct row.  The old
degree-ten retained selector cancels exactly before the reciprocal multiplier
is estimated; only the chosen direct selector `q` and the genuine rank-`P6`
correction remain. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_eq_selectorFree
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i : Fin 3) (x : ℝ) :
    factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i x =
      factorTwoIntrinsicNineDirectP6SelectorFreeRetainedRemainder
          (Sum.inl i : Fin 3 ⊕ Fin 3) x +
        sigma * factorTwoIntrinsicNineDirectP6SelectorFreeRetainedRemainder
          (Sum.inr i : Fin 3 ⊕ Fin 3) x -
        retainedP024EvenMass *
          factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma i x +
        centeredPolynomialLift
          (factorTwoIntrinsicNineDirectP6RankPolynomial sigma
              (factorTwoIntrinsicNineDirectP024Embed (Pi.single i 1)) -
            q i) x := by
  unfold factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder
    factorTwoIntrinsicNineDirectP6SelectorFreeRetainedRemainder
    retainedP024SelectorWholeEvenShiftedRemainder
    factorTwoIntrinsicNineDirectP6ExactSelectorCorrectionPolynomial
    factorTwoIntrinsicNineDirectP6ExactResidualPoleRow
    centeredPolynomialLift
  simp only [Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_smul, smul_eq_mul]
  ring

/-- The exact direct basis representer is the sum of its retained base row,
its phase-symmetric row, and its finite-rank polynomial correction. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter_eq_p024
    (sigma : ℝ) (i : Fin 3) (x : ℝ) :
    factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma i x =
      retainedP024SelectorWholeEvenRepresenter
          (Sum.inl i : Fin 3 ⊕ Fin 3) x +
        sigma * retainedP024SelectorWholeEvenRepresenter
          (Sum.inr i : Fin 3 ⊕ Fin 3) x +
        centeredPolynomialLift
          (factorTwoIntrinsicNineDirectP6RankPolynomial sigma
            (factorTwoIntrinsicNineDirectP024Embed (Pi.single i 1))) x := by
  have hEven :
      factorTwoIntrinsicNineDirectP024Polynomial
          (factorTwoIntrinsicNineDirectP024Embed (Pi.single i 1)) =
        retainedP024EvenMode i := by
    fin_cases i <;>
      simp [factorTwoIntrinsicNineDirectP024Polynomial,
        factorTwoIntrinsicNineDirectP024Embed,
        factorTwoIntrinsicNineEvenPolynomial, retainedP024EvenMode]
  have hOdd :
      factorTwoIntrinsicNineDirectP135Polynomial
          (factorTwoIntrinsicNineDirectP024Embed (Pi.single i 1)) = 0 := by
    simp [factorTwoIntrinsicNineDirectP135Polynomial,
      factorTwoIntrinsicNineDirectP024Embed,
      factorTwoIntrinsicNineOddPolynomial]
  have hWhole :
      factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma i x =
        factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 512 : ℝ) (retainedP024EvenMode i) 0 sigma 0 x +
          factorTwoIntrinsicNineDirectP6RankRepresenter sigma
            (factorTwoIntrinsicNineDirectP024Embed (Pi.single i 1)) x := by
    unfold factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter
      factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
      factorTwoIntrinsicNineDirectP6WholeRepresenter
      factorTwoIntrinsicNineDirectP6PotentialPoleRepresenter
      factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    rw [hEven, hOdd]
    ring
  rw [hWhole, retainedEvenRepresenterAt_zero_odd_phase_split]
  rw [← congrFun
    (centeredPolynomialLift_directP6RankPolynomial sigma
      (factorTwoIntrinsicNineDirectP024Embed (Pi.single i 1))) x]
  rfl

/-- Before quotient removal, the exact residual is already the sum of two
retained `P0/P2/P4` residual rows and one polynomial correction. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualRow_eq_p024
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i : Fin 3) (x : ℝ) :
    factorTwoIntrinsicNineDirectP6ExactResidualRow sigma q i x =
      factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenRepresenter
            (Sum.inl i : Fin 3 ⊕ Fin 3))
          (retainedP024SelectorWholeEvenPolynomial
            (Sum.inl i : Fin 3 ⊕ Fin 3)) x +
        sigma * factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenRepresenter
            (Sum.inr i : Fin 3 ⊕ Fin 3))
          (retainedP024SelectorWholeEvenPolynomial
            (Sum.inr i : Fin 3 ⊕ Fin 3)) x +
        centeredPolynomialLift
          (factorTwoIntrinsicNineDirectP6ExactSelectorCorrectionPolynomial
            sigma q i) x := by
  unfold factorTwoIntrinsicNineDirectP6ExactResidualRow
    factorTwoIntrinsicElevenSelectorResidual
  rw [factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter_eq_p024]
  unfold factorTwoIntrinsicNineDirectP6ExactSelectorCorrectionPolynomial
    centeredPolynomialLift
  simp only [Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_smul, smul_eq_mul]
  ring

/-- A retained endpoint selector residual is exactly its weight times its
pole row plus the shifted bounded remainder. -/
theorem retainedP024SelectorWholeEvenResidual_eq_weight_mul_pole_add_shifted
    (k : Fin 3 ⊕ Fin 3) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenSelectorResidual
        (retainedP024SelectorWholeEvenRepresenter k)
        (retainedP024SelectorWholeEvenPolynomial k) x =
      factorTwoIntrinsicElevenRetainedEvenWeight x *
          retainedP024SelectorWholeEvenPoleRow k x +
        retainedP024SelectorWholeEvenShiftedRemainder k x := by
  rw [retainedP024SelectorWholeEvenResidual_eq_pole_add_remainder k hx,
    retainedP024RetainedEvenWeight_eq_affine x]
  unfold retainedP024SelectorWholeEvenShiftedRemainder
  ring

/-- Exact quotient removal for every direct endpoint basis row. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualRow_eq_weight_mul_pole_add_shifted
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i : Fin 3)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    factorTwoIntrinsicNineDirectP6ExactResidualRow sigma q i x =
      factorTwoIntrinsicElevenRetainedEvenWeight x *
          factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma i x +
        factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder
          sigma q i x := by
  rw [factorTwoIntrinsicNineDirectP6ExactResidualRow_eq_p024 sigma q i x,
    retainedP024SelectorWholeEvenResidual_eq_weight_mul_pole_add_shifted
      (Sum.inl i) hx,
    retainedP024SelectorWholeEvenResidual_eq_weight_mul_pole_add_shifted
      (Sum.inr i) hx]
  unfold factorTwoIntrinsicNineDirectP6ExactResidualPoleRow
    factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorQuotientStructural
