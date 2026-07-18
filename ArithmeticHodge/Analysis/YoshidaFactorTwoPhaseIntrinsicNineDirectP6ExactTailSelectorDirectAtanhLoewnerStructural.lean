import ArithmeticHodge.Analysis.YoshidaEndpointPotentialAtanhLower
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorReciprocalLoewnerStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhLoewnerStructural

noncomputable section

open FiniteIntervalMultiplierGramLoewnerStructural
open FiniteIntervalWeightedGramTraceStructural
open YoshidaEndpointPotentialAtanhLower
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorReciprocalLoewnerStructural

/-!
# Direct atanh Loewner bound for the exact `P6` selector rows

The retained even weight has the exact affine form

`13 / 100 + (63 / 128) * yoshidaEndpointPotential`.

Replacing only the endpoint potential by its two-term transformed atanh
lower bound preserves both the retained mass and the exact potential slope.
Its reciprocal therefore gives a sharper full-matrix upper Gram than the
earlier route through a scalar multiple of the old tail weight.
-/

/-- Direct transformed-series lower approximation to the retained even
weight, keeping its exact potential slope `63 / 128`. -/
def directP6RetainedEvenAtanhTwoTermWeight (x : ℝ) : ℝ :=
  (13 / 100 : ℝ) + (63 / 128 : ℝ) *
    yoshidaEndpointPotentialAtanhTwoTerm x

/-- The direct transformed-series weight remains strictly positive on the
whole closed physical interval. -/
theorem directP6RetainedEvenAtanhTwoTermWeight_pos_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 < directP6RetainedEvenAtanhTwoTermWeight x := by
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
  have hden : 0 < 2 - x ^ 2 := by linarith
  have ht : 0 ≤ x ^ 2 / (2 - x ^ 2) :=
    div_nonneg (sq_nonneg x) hden.le
  unfold directP6RetainedEvenAtanhTwoTermWeight
    yoshidaEndpointPotentialAtanhTwoTerm
  dsimp only
  positivity

/-- The transformed-series weight is below the exact retained even weight at
every interior point. -/
theorem directP6RetainedEvenAtanhTwoTermWeight_le_retainedEvenWeight
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    directP6RetainedEvenAtanhTwoTermWeight x ≤
      factorTwoIntrinsicElevenRetainedEvenWeight x := by
  have hV := atanhTwoTerm_le_yoshidaEndpointPotential (abs_lt.mpr hx)
  unfold directP6RetainedEvenAtanhTwoTermWeight
    factorTwoIntrinsicElevenRetainedEvenWeight
  nlinarith

/-- Reversing the direct weight comparison gives the reciprocal multiplier
needed for the Loewner upper Gram. -/
theorem inv_retainedEvenWeight_le_directP6AtanhTwoTerm
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (factorTwoIntrinsicElevenRetainedEvenWeight x)⁻¹ ≤
      (directP6RetainedEvenAtanhTwoTermWeight x)⁻¹ := by
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hret := factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hxIcc
  have hlower := directP6RetainedEvenAtanhTwoTermWeight_pos_on_Icc hxIcc
  exact (inv_le_inv₀ hret hlower).2
    (directP6RetainedEvenAtanhTwoTermWeight_le_retainedEvenWeight hx)

/-- The reciprocal direct weight is continuous on the integration interval. -/
theorem continuousOn_inv_directP6RetainedEvenAtanhTwoTermWeight :
    ContinuousOn (fun x : ℝ ↦
      (directP6RetainedEvenAtanhTwoTermWeight x)⁻¹) (Icc (-1) 1) := by
  have hWeight : ContinuousOn directP6RetainedEvenAtanhTwoTermWeight
      (Icc (-1 : ℝ) 1) := by
    intro x hx
    have hxAbs : |x| ≤ 1 := abs_le.mpr hx
    have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
    have hden : 2 - x ^ 2 ≠ 0 := by linarith
    have ht : ContinuousAt (fun y : ℝ ↦ y ^ 2 / (2 - y ^ 2)) x :=
      (continuousAt_id.pow 2).div
        (continuousAt_const.sub (continuousAt_id.pow 2)) hden
    have hV : ContinuousAt (fun y : ℝ ↦
        y ^ 2 / (2 - y ^ 2) +
          (y ^ 2 / (2 - y ^ 2)) ^ 3 / 3) x :=
      ht.add ((ht.pow 3).div_const 3)
    unfold directP6RetainedEvenAtanhTwoTermWeight
      yoshidaEndpointPotentialAtanhTwoTerm
    dsimp only
    exact (continuousAt_const.add (continuousAt_const.mul hV)).continuousWithinAt
  exact hWeight.inv₀ fun x hx ↦
    (directP6RetainedEvenAtanhTwoTermWeight_pos_on_Icc hx).ne'

/-- Products of exact shifted rows remain integrable after multiplication by
the reciprocal direct atanh weight. -/
theorem intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanh
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i j : Fin 3) :
    IntervalIntegrable (fun x ↦
      (directP6RetainedEvenAtanhTwoTermWeight x)⁻¹ *
        factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i x *
        factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q j x)
      volume (-1) 1 := by
  have hcross :=
    intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_mul
      sigma q i j
  have hmult : ContinuousOn (fun x : ℝ ↦
      (directP6RetainedEvenAtanhTwoTermWeight x)⁻¹) (uIcc (-1) 1) := by
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
      continuousOn_inv_directP6RetainedEvenAtanhTwoTermWeight
  simpa only [mul_assoc] using hcross.continuousOn_mul hmult

/-- Reciprocal-multiplier Gram for the three exact shifted direct rows. -/
def factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperGram
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteIntervalMultiplierGram (-1) 1
    (fun x ↦ (directP6RetainedEvenAtanhTwoTermWeight x)⁻¹)
    (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q)

/-- The reciprocal-multiplier presentation is exactly the weighted Gram for
the direct two-term atanh weight. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperGram_eq_weightedGram
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperGram sigma q =
      finiteIntervalWeightedGram (-1) 1
        directP6RetainedEvenAtanhTwoTermWeight
        (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q) := by
  symm
  exact finiteIntervalWeightedGram_eq_multiplierGram_inv _ _ _ _

/-- Complete selector upper Gram obtained by replacing only the shifted
quotient Gram with the direct atanh reciprocal-multiplier Gram. -/
def factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  factorTwoIntrinsicNineDirectP6ExactResidualNonquotientGram sigma q +
    factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperGram sigma q

/-- The direct atanh reciprocal Gram dominates the exact weighted shifted
Gram in full Loewner order. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperGram_sub_posSemidef
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    (factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperGram sigma q -
      factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainderGram sigma q).PosSemidef := by
  exact finiteIntervalMultiplierGram_sub_weightedGram_posSemidef_of_inv_le_Ioo
    (-1) 1 (by norm_num)
    factorTwoIntrinsicElevenRetainedEvenWeight
    (fun x ↦ (directP6RetainedEvenAtanhTwoTermWeight x)⁻¹)
    (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q)
    (intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainderCross
      sigma q)
    (intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanh
      sigma q)
    (fun _x hx ↦ inv_retainedEvenWeight_le_directP6AtanhTwoTerm hx)

/-- Adding back the unchanged nonquotient part transfers the direct atanh
bound to the complete exact selector Gram. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram_sub_posSemidef
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    (factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram sigma q -
      factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q).PosSemidef := by
  rw [factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram_eq_nonquotient_add_remainder]
  simpa only [
    factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram,
    add_sub_add_left_eq_sub] using
    factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperGram_sub_posSemidef
      sigma q

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhLoewnerStructural
