import ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhReciprocalMajorant
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedReciprocalMajorantStructural

open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaEndpointEvenAtanhTailWeight
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenProjectedDualIdentity
open YoshidaEndpointEvenTailRepresenter
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural

noncomputable section

/-!
# Reciprocal majorants for the retained cutoff-eleven weights

Both retained weights dominate exact positive multiples of the old endpoint
tail weight.  Reversing those inequalities and composing with the structural
atanh reciprocal majorant gives polynomial upper bounds for the only quotient
left after endpoint-pole extraction.
-/

/-- The retained even weight dominates the sharp scalar multiple of the old
endpoint tail weight forced by their masses at the origin. -/
theorem scaled_tailWeight_le_retainedEvenWeight
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (39 / 205 : ℝ) * yoshidaEndpointEvenTailWeight x ≤
      factorTwoIntrinsicElevenRetainedEvenWeight x := by
  have hV := yoshidaEndpointPotential_nonneg_on_Icc hx
  unfold yoshidaEndpointEvenTailWeight
    factorTwoIntrinsicElevenRetainedEvenWeight
  nlinarith

/-- The retained odd weight dominates the sharp scalar multiple of the old
endpoint tail weight forced by their masses at the origin. -/
theorem scaled_tailWeight_le_retainedOddWeight
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (2 / 41 : ℝ) * yoshidaEndpointEvenTailWeight x ≤
      factorTwoIntrinsicElevenRetainedOddWeight x := by
  have hV := yoshidaEndpointPotential_nonneg_on_Icc hx
  unfold yoshidaEndpointEvenTailWeight
    factorTwoIntrinsicElevenRetainedOddWeight
  nlinarith

/-- Polynomial reciprocal majorant for the retained even weight. -/
theorem inv_retainedEvenWeight_le_reciprocalMajorant
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (factorTwoIntrinsicElevenRetainedEvenWeight x)⁻¹ ≤
      (205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x := by
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hret := factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hxIcc
  have htail := yoshidaEndpointEvenTailWeight_pos_on_Icc hxIcc
  have hatanh := yoshidaEndpointEvenAtanhTailWeight_pos_on_Icc hxIcc
  have hscaled : 0 < (39 / 205 : ℝ) * yoshidaEndpointEvenTailWeight x := by
    positivity
  have hretInv :
      (factorTwoIntrinsicElevenRetainedEvenWeight x)⁻¹ ≤
        ((39 / 205 : ℝ) * yoshidaEndpointEvenTailWeight x)⁻¹ :=
    (inv_le_inv₀ hret hscaled).2 (scaled_tailWeight_le_retainedEvenWeight hxIcc)
  have htailInv :
      (yoshidaEndpointEvenTailWeight x)⁻¹ ≤
        (yoshidaEndpointEvenAtanhTailWeight x)⁻¹ :=
    (inv_le_inv₀ htail hatanh).2 (atanhTailWeight_le_tailWeight hx)
  have hatanhInv := inv_atanhTailWeight_le_reciprocalMajorant hxIcc
  calc
    (factorTwoIntrinsicElevenRetainedEvenWeight x)⁻¹ ≤
        ((39 / 205 : ℝ) * yoshidaEndpointEvenTailWeight x)⁻¹ := hretInv
    _ = (205 / 39 : ℝ) * (yoshidaEndpointEvenTailWeight x)⁻¹ := by
      field_simp
    _ ≤ (205 / 39 : ℝ) *
        (yoshidaEndpointEvenAtanhTailWeight x)⁻¹ := by
      exact mul_le_mul_of_nonneg_left htailInv (by norm_num)
    _ ≤ (205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x := by
      exact mul_le_mul_of_nonneg_left hatanhInv (by norm_num)

/-- Polynomial reciprocal majorant for the retained odd weight. -/
theorem inv_retainedOddWeight_le_reciprocalMajorant
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (factorTwoIntrinsicElevenRetainedOddWeight x)⁻¹ ≤
      (41 / 2 : ℝ) * atanhTailWeightReciprocalMajorant x := by
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hret := factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hxIcc
  have htail := yoshidaEndpointEvenTailWeight_pos_on_Icc hxIcc
  have hatanh := yoshidaEndpointEvenAtanhTailWeight_pos_on_Icc hxIcc
  have hscaled : 0 < (2 / 41 : ℝ) * yoshidaEndpointEvenTailWeight x := by
    positivity
  have hretInv :
      (factorTwoIntrinsicElevenRetainedOddWeight x)⁻¹ ≤
        ((2 / 41 : ℝ) * yoshidaEndpointEvenTailWeight x)⁻¹ :=
    (inv_le_inv₀ hret hscaled).2 (scaled_tailWeight_le_retainedOddWeight hxIcc)
  have htailInv :
      (yoshidaEndpointEvenTailWeight x)⁻¹ ≤
        (yoshidaEndpointEvenAtanhTailWeight x)⁻¹ :=
    (inv_le_inv₀ htail hatanh).2 (atanhTailWeight_le_tailWeight hx)
  have hatanhInv := inv_atanhTailWeight_le_reciprocalMajorant hxIcc
  calc
    (factorTwoIntrinsicElevenRetainedOddWeight x)⁻¹ ≤
        ((2 / 41 : ℝ) * yoshidaEndpointEvenTailWeight x)⁻¹ := hretInv
    _ = (41 / 2 : ℝ) * (yoshidaEndpointEvenTailWeight x)⁻¹ := by
      field_simp
    _ ≤ (41 / 2 : ℝ) *
        (yoshidaEndpointEvenAtanhTailWeight x)⁻¹ := by
      exact mul_le_mul_of_nonneg_left htailInv (by norm_num)
    _ ≤ (41 / 2 : ℝ) * atanhTailWeightReciprocalMajorant x := by
      exact mul_le_mul_of_nonneg_left hatanhInv (by norm_num)

/-- Square-quotient form of the retained even reciprocal majorant. -/
theorem sq_div_retainedEvenWeight_le_reciprocalMajorant_mul_sq
    (h : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    h ^ 2 / factorTwoIntrinsicElevenRetainedEvenWeight x ≤
      (205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x * h ^ 2 := by
  rw [div_eq_mul_inv]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left
      (inv_retainedEvenWeight_le_reciprocalMajorant hx) (sq_nonneg h)

/-- Square-quotient form of the retained odd reciprocal majorant. -/
theorem sq_div_retainedOddWeight_le_reciprocalMajorant_mul_sq
    (h : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    h ^ 2 / factorTwoIntrinsicElevenRetainedOddWeight x ≤
      (41 / 2 : ℝ) * atanhTailWeightReciprocalMajorant x * h ^ 2 := by
  rw [div_eq_mul_inv]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left
      (inv_retainedOddWeight_le_reciprocalMajorant hx) (sq_nonneg h)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedReciprocalMajorantStructural
