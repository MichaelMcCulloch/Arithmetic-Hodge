import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorReciprocalLoewnerStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorQuotientStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorReciprocalLoewnerStructural

noncomputable section

open FiniteIntervalMultiplierGramLoewnerStructural
open FiniteIntervalWeightedGramTraceStructural
open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorReciprocalLoewnerStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedReciprocalMajorantStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorQuotientStructural

/-!
# Reciprocal Loewner control of the exact direct `P6` selector Gram

After exact quotient removal, every selector row is `W * P + T`.  This module
keeps the resulting three rows coupled: the only remaining inverse weight is
the positive Gram of the shifted remainders `T`, and the existing polynomial
reciprocal majorant is applied to that complete Gram in Loewner order.
-/

/-- The direct pole rows are continuous polynomials. -/
theorem continuous_factorTwoIntrinsicNineDirectP6ExactResidualPoleRow
    (sigma : ℝ) (i : Fin 3) :
    Continuous
      (factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma i) := by
  unfold factorTwoIntrinsicNineDirectP6ExactResidualPoleRow
  exact
    (continuous_retainedP024SelectorWholeEvenPoleRow (Sum.inl i)).add
      ((continuous_retainedP024SelectorWholeEvenPoleRow (Sum.inr i)).const_mul
        sigma)

/-- The exact shifted remainder belongs to the retained weighted dual space. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_div_sqrt_memLp_two
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i : Fin 3) :
    MemLp (fun x ↦
      factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hresidual :=
    exactResidualBasisSelectorResidual_div_sqrt_memLp_two sigma q i
  have hpole := sqrt_retainedEvenWeight_mul_memLp_two
    (factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma i)
    (continuous_factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma i)
  have hsub := hresidual.sub hpole
  apply (memLp_congr_ae (μ := volume.restrict (Ioc (-1 : ℝ) 1)) ?_).mpr hsub
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ))] with x hx hx1
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  change
    factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x) =
      factorTwoIntrinsicNineDirectP6ExactResidualRow sigma q i x /
          Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x) -
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x) *
          factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma i x
  rw [factorTwoIntrinsicNineDirectP6ExactResidualRow_eq_weight_mul_pole_add_shifted
    sigma q i hxIoo]
  have hW := factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hxIcc
  have hsqrt : 0 < Real.sqrt
      (factorTwoIntrinsicElevenRetainedEvenWeight x) := Real.sqrt_pos.2 hW
  field_simp [ne_of_gt hsqrt]
  rw [Real.sq_sqrt hW.le]
  ring

/-- The shifted-remainder quotient therefore has integrable polarized cross
entries. -/
theorem intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainderCross
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i j : Fin 3) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i x *
        factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q j x /
          factorTwoIntrinsicElevenRetainedEvenWeight x)
      volume (-1) 1 := by
  have hi : MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i)
          0 x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
      factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_div_sqrt_memLp_two
        sigma q i
  have hj : MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q j)
          0 x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
      factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_div_sqrt_memLp_two
        sigma q j
  simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
    intervalIntegrable_selectorCross_of_memLp
      factorTwoIntrinsicElevenRetainedEvenWeight
      (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i)
      (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q j)
      (0 : ℝ[X]) (0 : ℝ[X])
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      hi hj

/-- The exact shifted remainder is uniformly bounded on the physical
half-open interval. -/
theorem exists_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_abs_bound
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i : Fin 3) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder
        sigma q i x| ≤ B := by
  obtain ⟨B₀, hB₀, hbound₀⟩ :=
    exists_retainedP024SelectorWholeEvenShiftedRemainder_abs_bound
      (Sum.inl i : Fin 3 ⊕ Fin 3)
  obtain ⟨B₁, hB₁, hbound₁⟩ :=
    exists_retainedP024SelectorWholeEvenShiftedRemainder_abs_bound
      (Sum.inr i : Fin 3 ⊕ Fin 3)
  obtain ⟨B₂, hB₂, hbound₂⟩ :=
    exists_centeredPolynomialLift_abs_bound
      (factorTwoIntrinsicNineDirectP6ExactSelectorCorrectionPolynomial
        sigma q i)
  refine ⟨B₀ + |sigma| * B₁ + B₂ + 1, by positivity, ?_⟩
  intro x hx
  unfold factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder
  let A := retainedP024SelectorWholeEvenShiftedRemainder (Sum.inl i) x
  let B := retainedP024SelectorWholeEvenShiftedRemainder (Sum.inr i) x
  let C := centeredPolynomialLift
    (factorTwoIntrinsicNineDirectP6ExactSelectorCorrectionPolynomial sigma q i) x
  change |A + sigma * B + C| ≤ B₀ + |sigma| * B₁ + B₂ + 1
  calc
    |A + sigma * B + C| ≤ |A| + |sigma * B| + |C| := by
      nlinarith [abs_add_le (A + sigma * B) C,
        abs_add_le A (sigma * B)]
    _ = |A| + |sigma| * |B| + |C| := by rw [abs_mul]
    _ ≤ B₀ + |sigma| * B₁ + B₂ := by
      gcongr
      · simpa only [A] using hbound₀ x hx
      · simpa only [B] using hbound₁ x hx
      · simpa only [C] using hbound₂ x hx
    _ ≤ B₀ + |sigma| * B₁ + B₂ + 1 := by linarith

/-- Each exact shifted row is interval integrable before inserting a
reciprocal multiplier. -/
theorem intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i : Fin 3) :
    IntervalIntegrable
      (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i)
      volume (-1) 1 := by
  let μ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hdiv :=
    (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_div_sqrt_memLp_two
      sigma q i).1
  have hWmeas : Measurable factorTwoIntrinsicElevenRetainedEvenWeight := by
    unfold factorTwoIntrinsicElevenRetainedEvenWeight yoshidaEndpointPotential
    fun_prop
  have hsqrtMeas : AEStronglyMeasurable
      (fun x : ℝ ↦ Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) μ :=
    hWmeas.sqrt.aestronglyMeasurable
  have hrawMeas : AEStronglyMeasurable
      (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i) μ := by
    apply (hdiv.mul hsqrtMeas).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hW := factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc
      (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
    exact div_mul_cancel₀ _ (Real.sqrt_ne_zero'.2 hW)
  obtain ⟨B, _hBpos, hB⟩ :=
    exists_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_abs_bound
      sigma q i
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  refine IntegrableOn.of_bound measure_Ioc_lt_top hrawMeas B ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa only [Real.norm_eq_abs] using hB x hx

/-- Products of two exact shifted rows are integrable. -/
theorem intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_mul
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i j : Fin 3) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i x *
        factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q j x)
      volume (-1) 1 := by
  have hi :=
    intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder
      sigma q i
  have hj :=
    intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder
      sigma q j
  obtain ⟨B, _hBpos, hB⟩ :=
    exists_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_abs_bound
      sigma q j
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hi hj ⊢
  apply hi.mul_bdd hj.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa only [Real.norm_eq_abs] using hB x hx

/-- The reciprocal-polynomial upper entries are integrable. -/
theorem intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpper
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i j : Fin 3) :
    IntervalIntegrable (fun x ↦
      ((205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x) *
        factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i x *
        factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q j x)
      volume (-1) 1 := by
  have hcross :=
    intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_mul
      sigma q i j
  have hmult : Continuous
      (fun x : ℝ ↦ (205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x) := by
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
    fun_prop
  simpa only [mul_assoc] using hcross.continuousOn_mul hmult.continuousOn

/-- The nonquotient part of the product of two exact rows. -/
def factorTwoIntrinsicNineDirectP6ExactResidualNonquotientIntegrand
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i j : Fin 3) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenRetainedEvenWeight x *
      factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma i x *
      factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma j x +
    factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma i x *
      factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q j x +
    factorTwoIntrinsicNineDirectP6ExactResidualPoleRow sigma j x *
      factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i x

/-- Matrix of the inverse-weight-free terms in the exact row products. -/
def factorTwoIntrinsicNineDirectP6ExactResidualNonquotientGram
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ := fun i j ↦
  ∫ x : ℝ in -1..1,
    factorTwoIntrinsicNineDirectP6ExactResidualNonquotientIntegrand
      sigma q i j x

/-- The remaining positive weighted Gram after exact quotient removal. -/
def factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainderGram
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteIntervalWeightedGram (-1) 1
    factorTwoIntrinsicElevenRetainedEvenWeight
    (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q)

/-- Polynomial reciprocal-majorant Gram for the three exact shifted rows. -/
def factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperGram
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteIntervalMultiplierGram (-1) 1
    (fun x ↦ (205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x)
    (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q)

/-- Complete inverse-weight-free upper Gram for the exact direct rows. -/
def factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperSelectorGram
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  factorTwoIntrinsicNineDirectP6ExactResidualNonquotientGram sigma q +
    factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperGram sigma q

/-- Entry form of the exact selector Gram in the direct-row notation. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram_apply
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i j : Fin 3) :
    factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q i j =
      ∫ x : ℝ in -1..1,
        factorTwoIntrinsicNineDirectP6ExactResidualRow sigma q i x *
          factorTwoIntrinsicNineDirectP6ExactResidualRow sigma q j x /
            factorTwoIntrinsicElevenRetainedEvenWeight x := by
  rfl

/-- Exact residual-row products are integrable in the retained weight. -/
theorem intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualCross
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i j : Fin 3) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicNineDirectP6ExactResidualRow sigma q i x *
        factorTwoIntrinsicNineDirectP6ExactResidualRow sigma q j x /
          factorTwoIntrinsicElevenRetainedEvenWeight x)
      volume (-1) 1 := by
  simpa only [factorTwoIntrinsicNineDirectP6ExactResidualRow] using
    intervalIntegrable_selectorCross_of_memLp
      factorTwoIntrinsicElevenRetainedEvenWeight
      (factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma i)
      (factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma j)
      (q i) (q j)
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      (exactResidualBasisSelectorResidual_div_sqrt_memLp_two sigma q i)
      (exactResidualBasisSelectorResidual_div_sqrt_memLp_two sigma q j)

/-- The inverse-weight-free remainder of the row-product expansion is itself
integrable. -/
theorem intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualNonquotient
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i j : Fin 3) :
    IntervalIntegrable
      (factorTwoIntrinsicNineDirectP6ExactResidualNonquotientIntegrand
        sigma q i j)
      volume (-1) 1 := by
  have hdiff :=
    (intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualCross
      sigma q i j).sub
      (intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainderCross
        sigma q i j)
  apply hdiff.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ))] with x hx hx1
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  rw [factorTwoIntrinsicNineDirectP6ExactResidualRow_eq_weight_mul_pole_add_shifted
      sigma q i hxIoo,
    factorTwoIntrinsicNineDirectP6ExactResidualRow_eq_weight_mul_pole_add_shifted
      sigma q j hxIoo]
  have hW := factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  unfold factorTwoIntrinsicNineDirectP6ExactResidualNonquotientIntegrand
  field_simp [ne_of_gt hW]
  ring

/-- Exact matrix separation: all singular quotients are confined to one
positive shifted-remainder Gram. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram_eq_nonquotient_add_remainder
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q =
      factorTwoIntrinsicNineDirectP6ExactResidualNonquotientGram sigma q +
        factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainderGram
          sigma q := by
  ext i j
  rw [factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram_apply]
  simp only [Matrix.add_apply,
    factorTwoIntrinsicNineDirectP6ExactResidualNonquotientGram,
    factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainderGram,
    finiteIntervalWeightedGram]
  rw [← intervalIntegral.integral_add
    (intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualNonquotient
      sigma q i j)
    (intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainderCross
      sigma q i j)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [show ∀ᵐ x : ℝ ∂volume, x ≠ 1 by
    exact MeasureTheory.Measure.ae_ne volume 1] with x hx1
  intro hx
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  rw [factorTwoIntrinsicNineDirectP6ExactResidualRow_eq_weight_mul_pole_add_shifted
      sigma q i hxIoo,
    factorTwoIntrinsicNineDirectP6ExactResidualRow_eq_weight_mul_pole_add_shifted
      sigma q j hxIoo]
  have hW := factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc
    (show x ∈ Icc (-1 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
  unfold factorTwoIntrinsicNineDirectP6ExactResidualNonquotientIntegrand
  field_simp [ne_of_gt hW]
  ring

/-- The reciprocal-polynomial shifted-remainder Gram is a full Loewner upper
bound for the exact weighted shifted-remainder Gram. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperGram_sub_posSemidef
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    (factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperGram sigma q -
      factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainderGram
        sigma q).PosSemidef := by
  exact finiteIntervalMultiplierGram_sub_weightedGram_posSemidef_of_inv_le_Ioo
    (-1) 1 (by norm_num)
    factorTwoIntrinsicElevenRetainedEvenWeight
    (fun x ↦ (205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x)
    (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q)
    (intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainderCross
      sigma q)
    (intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpper
      sigma q)
    (fun _x hx ↦ inv_retainedEvenWeight_le_reciprocalMajorant hx)

/-- The complete inverse-weight-free direct selector Gram dominates the exact
selector Gram in Loewner order. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperSelectorGram_sub_posSemidef
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    (factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperSelectorGram
        sigma q -
      factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q).PosSemidef := by
  rw [factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram_eq_nonquotient_add_remainder]
  simpa only [
    factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperSelectorGram,
    add_sub_add_left_eq_sub] using
    factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperGram_sub_posSemidef
      sigma q

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorReciprocalLoewnerStructural
