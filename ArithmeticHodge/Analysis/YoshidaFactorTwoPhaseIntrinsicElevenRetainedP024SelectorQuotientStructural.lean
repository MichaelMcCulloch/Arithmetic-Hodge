import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorPoleRemainderStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedReciprocalMajorantStructural

set_option autoImplicit false

open Matrix MeasureTheory Real Set

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
open YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural

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

/-! ## Integrated extracted Grams -/

/-- The exact affine-weight quotient expansion of one combined retained-even
Gram entry. -/
def retainedP024SelectorWholeEvenQuotientExpansion
    (i j : Fin 3 ⊕ Fin 3) (x : ℝ) : ℝ :=
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
      factorTwoIntrinsicElevenRetainedEvenWeight x

/-- The exact affine-weight quotient expansion of one alternating retained-odd
Gram entry. -/
def retainedP024SelectorAlternatingQuotientExpansion
    (i j : Fin 3) (x : ℝ) : ℝ :=
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
      factorTwoIntrinsicElevenRetainedOddWeight x

/-- Entrywise integral of the exact retained-even quotient expansion. -/
def retainedP024SelectorWholeEvenExtractedGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ := fun i j ↦
  ∫ x : ℝ in -1..1,
    retainedP024SelectorWholeEvenQuotientExpansion i j x

/-- Entrywise integral of the exact alternating quotient expansion. -/
def retainedP024SelectorAlternatingExtractedGram :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j ↦
  ∫ x : ℝ in -1..1,
    retainedP024SelectorAlternatingQuotientExpansion i j x

/-- The complete six-row retained-even Gram is exactly its endpoint-pole
quotient expansion.  The two endpoints are removed only almost everywhere. -/
theorem retainedP024SelectorWholeEvenGram_eq_extracted :
    retainedP024SelectorWholeEvenGram =
      retainedP024SelectorWholeEvenExtractedGram := by
  ext i j
  unfold retainedP024SelectorWholeEvenGram
    factorTwoIntrinsicElevenSelectorGram
    factorTwoIntrinsicElevenSelectorCrossDual
    retainedP024SelectorWholeEvenExtractedGram
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hx1
  intro hx
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  simpa [retainedP024SelectorWholeEvenQuotientExpansion] using
    retainedP024SelectorWholeEvenResidual_mul_div_weight_eq i j hxIoo

/-- The fixed alternating selector Gram is exactly its endpoint-pole quotient
expansion, again modulo only the measure-zero endpoints. -/
theorem retainedP024SelectorAlternatingGram_eq_extracted :
    retainedP024SelectorAlternatingGram =
      retainedP024SelectorAlternatingExtractedGram := by
  ext i j
  unfold retainedP024SelectorAlternatingGram
    retainedP024AlternatingSelectorGram
  rw [retainedP024ThreeSelectorGramMatrix_apply]
  unfold factorTwoIntrinsicElevenSelectorCrossDual
    retainedP024SelectorAlternatingExtractedGram
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.Measure.ae_ne volume (1 : ℝ)] with x hx1
  intro hx
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  have hpoint :=
    retainedP024SelectorAlternatingResidual_mul_div_weight_eq i j hxIoo
  fin_cases i <;> fin_cases j <;>
    simpa [retainedP024EvenMode,
      retainedP024SelectorAlternatingPolynomial,
      retainedP024SelectorAlternatingQuotientExpansion] using hpoint

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
