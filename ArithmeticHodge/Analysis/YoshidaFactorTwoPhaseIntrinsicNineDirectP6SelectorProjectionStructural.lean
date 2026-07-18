import ArithmeticHodge.Analysis.FiniteWeightedSelectorProjectionResidualStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorGramStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorProjectionStructural

noncomputable section

open ArithmeticHodge.Analysis.FiniteBilinearGramProjectionStructural
open ArithmeticHodge.Analysis.FiniteWeightedSelectorProjection
open ArithmeticHodge.Analysis.FiniteWeightedSelectorProjectionResidualStructural
open ShiftedLegendreBasis
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorGramStructural

/-!
# Finite projection coordinates for the direct `P6` selector

At the `P6` gap we restrict the selector search to the even polynomial space
spanned by `P0`, `P2`, and `P4`.  This file turns a `6 × 3` coefficient matrix
into the corresponding six selector polynomials and identifies their analytic
weighted Gram with the exact finite projection defect.
-/

/-- The admissible even selector basis at the `P6` gap. -/
def factorTwoIntrinsicNineDirectP6EvenSelectorBasis
    (k : Fin 3) : ℝ[X] :=
  shiftedLegendreReal (2 * k.1)

/-- Centered lifts of the three admissible even selector modes. -/
def factorTwoIntrinsicNineDirectP6EvenSelectorLift
    (k : Fin 3) : ℝ → ℝ :=
  centeredPolynomialLift
    (factorTwoIntrinsicNineDirectP6EvenSelectorBasis k)

/-- Phase-independent part of a complete direct `P6` basis row. -/
def factorTwoIntrinsicNineDirectP6BaseRepresenter
    (i : Fin 6) : ℝ → ℝ :=
  factorTwoIntrinsicNineDirectP6BasisRepresenter 0 0 i

/-- Coefficient of the symmetric phase in a complete direct `P6` basis row. -/
def factorTwoIntrinsicNineDirectP6SymmetricRepresenter
    (i : Fin 6) : ℝ → ℝ := fun z ↦
  factorTwoIntrinsicNineDirectP6BasisRepresenter 1 0 i z -
    factorTwoIntrinsicNineDirectP6BaseRepresenter i z

/-- Coefficient of the alternating phase in a complete direct `P6` basis
row. -/
def factorTwoIntrinsicNineDirectP6AlternatingRepresenter
    (i : Fin 6) : ℝ → ℝ := fun z ↦
  factorTwoIntrinsicNineDirectP6BasisRepresenter 0 1 i z -
    factorTwoIntrinsicNineDirectP6BaseRepresenter i z

private theorem directP6AnalyticEvenRepresenter_affine_phase
    (pE pO : ℝ[X]) (a b z : ℝ) :
    factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO a b z =
      factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO 0 0 z +
        a * (factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO 1 0 z -
          factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO 0 0 z) +
        b * (factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO 0 1 z -
          factorTwoIntrinsicElevenAnalyticEvenRepresenter pE pO 0 0 z) := by
  unfold factorTwoIntrinsicElevenAnalyticEvenRepresenter
  ring

private theorem directP6ForwardEvenRepresenter_affine_phase
    (pE pO : ℝ[X]) (a b z : ℝ) :
    factorTwoIntrinsicElevenForwardEvenRepresenter pE pO a b z =
      factorTwoIntrinsicElevenForwardEvenRepresenter pE pO 0 0 z +
        a * (factorTwoIntrinsicElevenForwardEvenRepresenter pE pO 1 0 z -
          factorTwoIntrinsicElevenForwardEvenRepresenter pE pO 0 0 z) +
        b * (factorTwoIntrinsicElevenForwardEvenRepresenter pE pO 0 1 z -
          factorTwoIntrinsicElevenForwardEvenRepresenter pE pO 0 0 z) := by
  unfold factorTwoIntrinsicElevenForwardEvenRepresenter
  ring

private theorem directP6ReflectedEvenRepresenter_affine_phase
    (pE pO : ℝ[X]) (a b z : ℝ) :
    factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO a b z =
      factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO 0 0 z +
        a * (factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO 1 0 z -
          factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO 0 0 z) +
        b * (factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO 0 1 z -
          factorTwoIntrinsicElevenReflectedEvenRepresenter pE pO 0 0 z) := by
  unfold factorTwoIntrinsicElevenReflectedEvenRepresenter
  ring

private theorem directP6PrimeEvenRepresenter_affine_phase
    (pE pO : ℝ[X]) (a b z : ℝ) :
    factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO a b z =
      factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO 0 0 z +
        a * (factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO 1 0 z -
          factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO 0 0 z) +
        b * (factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO 0 1 z -
          factorTwoIntrinsicElevenPrimeEvenRepresenter pE pO 0 0 z) := by
  unfold factorTwoIntrinsicElevenPrimeEvenRepresenter
  ring

/-- Every complete direct `P6` basis row is exactly affine in the two phase
coordinates. -/
theorem factorTwoIntrinsicNineDirectP6BasisRepresenter_affine_phase
    (a b : ℝ) (i : Fin 6) (z : ℝ) :
    factorTwoIntrinsicNineDirectP6BasisRepresenter a b i z =
      factorTwoIntrinsicNineDirectP6BaseRepresenter i z +
        a * factorTwoIntrinsicNineDirectP6SymmetricRepresenter i z +
        b * factorTwoIntrinsicNineDirectP6AlternatingRepresenter i z := by
  unfold factorTwoIntrinsicNineDirectP6SymmetricRepresenter
    factorTwoIntrinsicNineDirectP6AlternatingRepresenter
    factorTwoIntrinsicNineDirectP6BaseRepresenter
    factorTwoIntrinsicNineDirectP6BasisRepresenter
    YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural.factorTwoIntrinsicNineDirectP6WholeRepresenter
    YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural.factorTwoIntrinsicNineDirectP6RankRepresenter
    factorTwoIntrinsicElevenEvenMixedRepresenter
  rw [directP6AnalyticEvenRepresenter_affine_phase,
    directP6ForwardEvenRepresenter_affine_phase,
    directP6ReflectedEvenRepresenter_affine_phase,
    directP6PrimeEvenRepresenter_affine_phase]
  ring

/-- Six selector polynomials synthesized from one `6 × 3` coefficient
matrix. -/
def factorTwoIntrinsicNineDirectP6SelectorPolynomial
    (C : Matrix (Fin 6) (Fin 3) ℝ) (i : Fin 6) : ℝ[X] :=
  ∑ k : Fin 3,
    C i k • factorTwoIntrinsicNineDirectP6EvenSelectorBasis k

theorem factorTwoIntrinsicNineDirectP6SelectorPolynomial_natDegree_lt_six
    (C : Matrix (Fin 6) (Fin 3) ℝ) (i : Fin 6) :
    (factorTwoIntrinsicNineDirectP6SelectorPolynomial C i).natDegree < 6 := by
  unfold factorTwoIntrinsicNineDirectP6SelectorPolynomial
    factorTwoIntrinsicNineDirectP6EvenSelectorBasis
  have hle : (∑ k : Fin 3,
      C i k • shiftedLegendreReal (2 * k.1)).natDegree ≤ 4 :=
    Polynomial.natDegree_sum_le_of_forall_le Finset.univ _
      (fun k _hk ↦
        (Polynomial.natDegree_smul_le (C i k)
          (shiftedLegendreReal (2 * k.1))).trans (by
            rw [natDegree_shiftedLegendreReal]
            omega))
  omega

theorem centeredPolynomialLift_directP6SelectorPolynomial
    (C : Matrix (Fin 6) (Fin 3) ℝ) (i : Fin 6) (z : ℝ) :
    centeredPolynomialLift
        (factorTwoIntrinsicNineDirectP6SelectorPolynomial C i) z =
      ∑ k : Fin 3,
        C i k * factorTwoIntrinsicNineDirectP6EvenSelectorLift k z := by
  simp only [factorTwoIntrinsicNineDirectP6SelectorPolynomial,
    factorTwoIntrinsicNineDirectP6EvenSelectorLift,
    centeredPolynomialLift, Polynomial.eval_finset_sum,
    Polynomial.eval_smul, smul_eq_mul]

/-- The abstract finite projection residual is exactly the selector residual
used by the retained-weight Cauchy theorem. -/
theorem directP6ProjectionResidualRow_eq_selectorResidual
    (a b : ℝ) (C : Matrix (Fin 6) (Fin 3) ℝ)
    (i : Fin 6) (z : ℝ) :
    finiteProjectionResidualRow
        (factorTwoIntrinsicNineDirectP6BasisRepresenter a b)
        factorTwoIntrinsicNineDirectP6EvenSelectorLift C i z =
      factorTwoIntrinsicElevenSelectorResidual
        (factorTwoIntrinsicNineDirectP6BasisRepresenter a b i)
        (factorTwoIntrinsicNineDirectP6SelectorPolynomial C i) z := by
  unfold finiteProjectionResidualRow
    factorTwoIntrinsicElevenSelectorResidual
  rw [centeredPolynomialLift_directP6SelectorPolynomial]
  rfl

/-- The analytic selector Gram is the weighted Gram of the six finite
projection-residual rows. -/
theorem factorTwoIntrinsicNineDirectP6SelectorGram_eq_projectionResidualGram
    (a b : ℝ) (C : Matrix (Fin 6) (Fin 3) ℝ) :
    factorTwoIntrinsicNineDirectP6SelectorGram a b
        (factorTwoIntrinsicNineDirectP6SelectorPolynomial C) =
      finiteWeightedGram factorTwoIntrinsicElevenRetainedEvenWeight
        (finiteProjectionResidualRow
          (factorTwoIntrinsicNineDirectP6BasisRepresenter a b)
          factorTwoIntrinsicNineDirectP6EvenSelectorLift C) := by
  ext i j
  simp only [factorTwoIntrinsicNineDirectP6SelectorGram,
    finiteWeightedGram, factorTwoIntrinsicElevenSelectorGram,
    factorTwoIntrinsicElevenSelectorCrossDual]
  apply intervalIntegral.integral_congr
  intro z _hz
  dsimp only
  rw [← directP6ProjectionResidualRow_eq_selectorResidual,
    ← directP6ProjectionResidualRow_eq_selectorResidual]
  simp only [factorTwoIntrinsicElevenSelectorResidual,
    centeredPolynomialLift, Polynomial.eval_zero, sub_zero]

private theorem directP6EvenSelectorLift_div_sqrt_memLp_two
    (k : Fin 3) :
    MemLp (fun z ↦
      factorTwoIntrinsicNineDirectP6EvenSelectorLift k z /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight z)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have h :=
    factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      0 0 0 (factorTwoIntrinsicNineDirectP6EvenSelectorBasis k) 0 0
  apply (memLp_congr_ae (μ := volume.restrict (Ioc (-1 : ℝ) 1)) ?_).mpr
    h.neg
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  have hzero :
      factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
          0 0 0 0 0 z = 0 := by
    have hlin :=
      retainedEvenMixedRepresenterAt_threeSelectorPolynomial_on_Icc
        0 0 0 0 0 0
        (shiftedLegendreReal 0) (shiftedLegendreReal 2)
          (shiftedLegendreReal 4) z
        (show z ∈ Icc (-1 : ℝ) 1 from ⟨hz.1.le, hz.2⟩)
    simpa [threeSelectorPolynomial, threeSelectorRepresenter] using hlin
  unfold factorTwoIntrinsicNineDirectP6EvenSelectorLift
    factorTwoIntrinsicElevenSelectorResidual
  change centeredPolynomialLift
      (factorTwoIntrinsicNineDirectP6EvenSelectorBasis k) z /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight z) =
    -((factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
          0 0 0 0 0 z -
        centeredPolynomialLift
          (factorTwoIntrinsicNineDirectP6EvenSelectorBasis k) z) /
      Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight z))
  rw [hzero]
  ring

/-- Exact inverse-free projection formula for every `6 × 3` selector
coefficient matrix.  The three finite matrices on the right are the only
weighted moments that a concrete selector certificate must control. -/
theorem factorTwoIntrinsicNineDirectP6SelectorGram_eq_projectionDefect
    (a b : ℝ) (C : Matrix (Fin 6) (Fin 3) ℝ) :
    factorTwoIntrinsicNineDirectP6SelectorGram a b
        (factorTwoIntrinsicNineDirectP6SelectorPolynomial C) =
      finiteWeightedGram factorTwoIntrinsicElevenRetainedEvenWeight
          (factorTwoIntrinsicNineDirectP6BasisRepresenter a b) -
        (finiteWeightedCrossGram factorTwoIntrinsicElevenRetainedEvenWeight
              (factorTwoIntrinsicNineDirectP6BasisRepresenter a b)
              factorTwoIntrinsicNineDirectP6EvenSelectorLift * Cᴴ +
          C * (finiteWeightedCrossGram
              factorTwoIntrinsicElevenRetainedEvenWeight
              (factorTwoIntrinsicNineDirectP6BasisRepresenter a b)
              factorTwoIntrinsicNineDirectP6EvenSelectorLift)ᴴ -
          C * finiteWeightedGram factorTwoIntrinsicElevenRetainedEvenWeight
              factorTwoIntrinsicNineDirectP6EvenSelectorLift * Cᴴ) := by
  rw [factorTwoIntrinsicNineDirectP6SelectorGram_eq_projectionResidualGram]
  apply finiteWeightedGram_projectionResidualRow_eq
  · intro z hz
    exact factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hz
  · intro i
    simpa [factorTwoIntrinsicElevenSelectorResidual,
      centeredPolynomialLift] using
      (directP6BasisSelectorResidual_div_sqrt_memLp_two
        a b (fun _ ↦ (0 : ℝ[X])) i)
  · exact directP6EvenSelectorLift_div_sqrt_memLp_two

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorProjectionStructural
