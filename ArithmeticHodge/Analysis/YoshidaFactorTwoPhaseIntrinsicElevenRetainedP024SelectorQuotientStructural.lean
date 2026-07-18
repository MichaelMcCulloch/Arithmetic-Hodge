import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorPoleRemainderStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedReciprocalMajorantStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural

open AffineWeightQuotient
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoPhaseIntrinsicElevenConcreteSelectorsStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorPoleRemainderStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural

noncomputable section

/-!
# Exact quotient extraction for the retained P024 selector

After the endpoint-trace pole has been removed from every P0/P2/P4 selector
row, division by either retained affine weight is exact.  The only remaining
quotient has numerator equal to the mass-shifted bounded remainders below.
-/

def retainedP024EvenMass : ℝ := 13 / 100

def retainedP024OddMass : ℝ := 1 / 30

/-- Bounded numerator left in an even selector row after exact affine-weight
division. -/
def retainedP024SelectorWholeEvenShiftedRemainder
    (k : Fin 3 ⊕ Fin 3) (x : ℝ) : ℝ :=
  retainedP024SelectorWholeEvenRemainder k x -
    retainedP024EvenMass * retainedP024SelectorWholeEvenPoleRow k x

/-- Bounded numerator left in an alternating odd selector row after exact
affine-weight division. -/
def retainedP024SelectorAlternatingShiftedRemainder
    (i : Fin 3) (x : ℝ) : ℝ :=
  retainedP024SelectorAlternatingRemainder i x -
    retainedP024OddMass * retainedP024SelectorAlternatingPoleRow i x

theorem retainedP024RetainedEvenWeight_eq_affine (x : ℝ) :
    factorTwoIntrinsicElevenRetainedEvenWeight x =
      retainedP024EvenMass +
        retainedP024PoleSlope * yoshidaEndpointPotential x := by
  rfl

theorem retainedP024RetainedOddWeight_eq_affine (x : ℝ) :
    factorTwoIntrinsicElevenRetainedOddWeight x =
      retainedP024OddMass +
        retainedP024PoleSlope * yoshidaEndpointPotential x := by
  rfl

/-- Polarized exact division of two retained-even P024 residual rows. -/
theorem retainedP024SelectorWholeEvenResidual_mul_div_weight_eq
    (i j : Fin 3 ⊕ Fin 3) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenRepresenter i)
          (retainedP024SelectorWholeEvenPolynomial i) x *
        factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenRepresenter j)
          (retainedP024SelectorWholeEvenPolynomial j) x /
        factorTwoIntrinsicElevenRetainedEvenWeight x =
      retainedP024PoleSlope * yoshidaEndpointPotential x *
          retainedP024SelectorWholeEvenPoleRow i x *
          retainedP024SelectorWholeEvenPoleRow j x +
        retainedP024SelectorWholeEvenPoleRow i x *
          retainedP024SelectorWholeEvenRemainder j x +
        retainedP024SelectorWholeEvenPoleRow j x *
          retainedP024SelectorWholeEvenRemainder i x -
        retainedP024EvenMass *
          retainedP024SelectorWholeEvenPoleRow i x *
          retainedP024SelectorWholeEvenPoleRow j x +
        retainedP024SelectorWholeEvenShiftedRemainder i x *
            retainedP024SelectorWholeEvenShiftedRemainder j x /
          factorTwoIntrinsicElevenRetainedEvenWeight x := by
  rw [retainedP024SelectorWholeEvenResidual_eq_pole_add_remainder i hx,
    retainedP024SelectorWholeEvenResidual_eq_pole_add_remainder j hx]
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hne :
      retainedP024EvenMass +
          retainedP024PoleSlope * yoshidaEndpointPotential x ≠ 0 := by
    rw [← retainedP024RetainedEvenWeight_eq_affine]
    exact ne_of_gt
      (factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hxIcc)
  have h := mul_div_affine_weight_decomposition
    (yoshidaEndpointPotential x) retainedP024EvenMass
    retainedP024PoleSlope
    (retainedP024SelectorWholeEvenPoleRow i x)
    (retainedP024SelectorWholeEvenPoleRow j x)
    (retainedP024SelectorWholeEvenRemainder i x)
    (retainedP024SelectorWholeEvenRemainder j x) hne
  simpa [retainedP024SelectorWholeEvenShiftedRemainder,
    retainedP024RetainedEvenWeight_eq_affine] using h

/-- Polarized exact division of two alternating retained-odd P024 residual
rows. -/
theorem retainedP024SelectorAlternatingResidual_mul_div_weight_eq
    (i j : Fin 3) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenSelectorResidual
          (retainedOddAlternatingRepresenterAt
            (1 / 512 : ℝ) (retainedP024EvenMode i))
          (retainedP024SelectorAlternatingPolynomial i) x *
        factorTwoIntrinsicElevenSelectorResidual
          (retainedOddAlternatingRepresenterAt
            (1 / 512 : ℝ) (retainedP024EvenMode j))
          (retainedP024SelectorAlternatingPolynomial j) x /
        factorTwoIntrinsicElevenRetainedOddWeight x =
      retainedP024PoleSlope * yoshidaEndpointPotential x *
          retainedP024SelectorAlternatingPoleRow i x *
          retainedP024SelectorAlternatingPoleRow j x +
        retainedP024SelectorAlternatingPoleRow i x *
          retainedP024SelectorAlternatingRemainder j x +
        retainedP024SelectorAlternatingPoleRow j x *
          retainedP024SelectorAlternatingRemainder i x -
        retainedP024OddMass *
          retainedP024SelectorAlternatingPoleRow i x *
          retainedP024SelectorAlternatingPoleRow j x +
        retainedP024SelectorAlternatingShiftedRemainder i x *
            retainedP024SelectorAlternatingShiftedRemainder j x /
          factorTwoIntrinsicElevenRetainedOddWeight x := by
  rw [retainedP024SelectorAlternatingResidual_eq_pole_add_remainder i hx,
    retainedP024SelectorAlternatingResidual_eq_pole_add_remainder j hx]
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hne :
      retainedP024OddMass +
          retainedP024PoleSlope * yoshidaEndpointPotential x ≠ 0 := by
    rw [← retainedP024RetainedOddWeight_eq_affine]
    exact ne_of_gt
      (factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hxIcc)
  have h := mul_div_affine_weight_decomposition
    (yoshidaEndpointPotential x) retainedP024OddMass
    retainedP024PoleSlope
    (retainedP024SelectorAlternatingPoleRow i x)
    (retainedP024SelectorAlternatingPoleRow j x)
    (retainedP024SelectorAlternatingRemainder i x)
    (retainedP024SelectorAlternatingRemainder j x) hne
  simpa [retainedP024SelectorAlternatingShiftedRemainder,
    retainedP024RetainedOddWeight_eq_affine] using h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
