import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedRegularRemainderStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCapacityCrossStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped Interval

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCombinedNormStructural

noncomputable section

open YoshidaConstantBounds
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenEndpointSeedCapacityCrossStructural
open YoshidaFourCellEvenEndpointSeedCutoffEightBridgeStructural
open YoshidaFourCellEvenEndpointSeedRegularRemainderStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellEvenZeroCoshCoupledCoreStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural

private theorem intervalIntegrable_sq_of_memLp_two_restrict
    (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1))) :
    IntervalIntegrable (fun x : ℝ ↦ f x ^ 2) volume (-1) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  apply (hf.integrable_norm_pow (by norm_num)).congr
  filter_upwards with x
  rw [Real.norm_eq_abs, sq_abs]

/-- A fixed-ratio Young inequality for two square-integrable representers.
The constants are chosen for the endpoint-row margins: the identity behind
the pointwise estimate is `(A/2 + 2*c*E)^2 ≥ 0`. -/
theorem integral_sub_const_mul_sq_le_five_four_add_five
    (A E : ℝ → ℝ) (c : ℝ)
    (hA : MemLp A 2 (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hE : MemLp E 2 (volume.restrict (Ioc (-1 : ℝ) 1))) :
    (∫ x : ℝ in -1..1, (A x - c * E x) ^ 2) ≤
      (5 / 4 : ℝ) * (∫ x : ℝ in -1..1, A x ^ 2) +
        5 * c ^ 2 * (∫ x : ℝ in -1..1, E x ^ 2) := by
  have hAE : MemLp (fun x : ℝ ↦ A x - c * E x) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      hA.sub (hE.const_smul c)
  have hleft := intervalIntegrable_sq_of_memLp_two_restrict _ hAE
  have hAsq := intervalIntegrable_sq_of_memLp_two_restrict A hA
  have hEsq := intervalIntegrable_sq_of_memLp_two_restrict E hE
  have hright : IntervalIntegrable
      (fun x : ℝ ↦ (5 / 4 : ℝ) * A x ^ 2 +
        (5 * c ^ 2) * E x ^ 2) volume (-1) 1 :=
    (hAsq.const_mul (5 / 4)).add (hEsq.const_mul (5 * c ^ 2))
  calc
    (∫ x : ℝ in -1..1, (A x - c * E x) ^ 2) ≤
        ∫ x : ℝ in -1..1,
          (5 / 4 : ℝ) * A x ^ 2 + (5 * c ^ 2) * E x ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) hleft hright
      intro x _hx
      nlinarith [sq_nonneg (A x / 2 + 2 * c * E x)]
    _ = (5 / 4 : ℝ) * (∫ x : ℝ in -1..1, A x ^ 2) +
        5 * c ^ 2 * (∫ x : ℝ in -1..1, E x ^ 2) := by
      rw [intervalIntegral.integral_add
          (hAsq.const_mul (5 / 4)) (hEsq.const_mul (5 * c ^ 2)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- Any projected capacity row with squared norm at most `21/100000`
remains within the endpoint determinant budget after restoring the complete
analytic regular remainder.  This combines the exact `1/80` seed reserve
with the `1/245000` remainder norm and loses only the displayed structural
Young factor. -/
theorem integral_capacity_sub_regularRemainder_sq_le_endpointSeed_budget
    (A : ℝ → ℝ)
    (hA : MemLp A 2 (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hAnorm : (∫ x : ℝ in -1..1, A x ^ 2) ≤
      (21 / 100000 : ℝ)) :
    (∫ x : ℝ in -1..1,
      (A x - fourCellOperatorHalfWidth *
        fourCellEndpointSeedRegularRemainderRepresenter x) ^ 2) ≤
      fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
        (553 / 20000 : ℝ) := by
  let a : ℝ := fourCellOperatorHalfWidth
  let E : ℝ → ℝ := fourCellEndpointSeedRegularRemainderRepresenter
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlogUpper : Real.log 2 ≤ (6932 / 10000 : ℝ) :=
    strict_log_two_bounds.2.le
  have hlogSq : Real.log 2 ^ 2 ≤ (6932 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlogUpper 2
  have haSq : a ^ 2 ≤ (19 / 100 : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hlogSq
      (by norm_num : (0 : ℝ) ≤ 25 / 64)
    calc
      a ^ 2 = (25 / 64 : ℝ) * Real.log 2 ^ 2 := by
        dsimp only [a]
        unfold fourCellOperatorHalfWidth
        ring
      _ ≤ (25 / 64 : ℝ) * (6932 / 10000 : ℝ) ^ 2 := hscaled
      _ ≤ (19 / 100 : ℝ) := by norm_num
  have hE : MemLp E 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [E] using memLp_fourCellEndpointSeedRegularRemainderRepresenter
  have hEnorm : (∫ x : ℝ in -1..1, E x ^ 2) ≤
      (1 / 245000 : ℝ) := by
    simpa only [E] using
      integral_fourCellEndpointSeedRegularRemainderRepresenter_sq_le
  have hEnonneg : 0 ≤ ∫ x : ℝ in -1..1, E x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ sq_nonneg _)
  have hyoung := integral_sub_const_mul_sq_le_five_four_add_five
    A E a hA hE
  have hAterm :
      (5 / 4 : ℝ) * (∫ x : ℝ in -1..1, A x ^ 2) ≤
        (5 / 4 : ℝ) * (21 / 100000) :=
    mul_le_mul_of_nonneg_left hAnorm (by norm_num)
  have hEterm :
      5 * a ^ 2 * (∫ x : ℝ in -1..1, E x ^ 2) ≤
        5 * (19 / 100 : ℝ) * (1 / 245000) := by
    calc
      5 * a ^ 2 * (∫ x : ℝ in -1..1, E x ^ 2) ≤
          5 * (19 / 100 : ℝ) * (∫ x : ℝ in -1..1, E x ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left haSq (by norm_num)) hEnonneg
      _ ≤ 5 * (19 / 100 : ℝ) * (1 / 245000) :=
        mul_le_mul_of_nonneg_left hEnorm (by norm_num)
  have hrat :
      (5 / 4 : ℝ) * (21 / 100000) +
          5 * (19 / 100 : ℝ) * (1 / 245000) ≤
        (1 / 80 : ℝ) * (553 / 20000) := by
    norm_num
  have hseed :=
    one_div_eighty_lt_fourCellEvenExactBracket_endpointCoshSeed.le
  have hbudget :
      (1 / 80 : ℝ) * (553 / 20000) ≤
        fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
          (553 / 20000 : ℝ) :=
    mul_le_mul_of_nonneg_right hseed (by norm_num)
  change (∫ x : ℝ in -1..1, (A x - a * E x) ^ 2) ≤ _
  exact hyoung.trans ((add_le_add hAterm hEterm).trans (hrat.trans hbudget))

/-- The canonical projected endpoint-capacity row, with the analytic regular
remainder restored, fits the complete endpoint determinant budget. -/
theorem integral_endpointSeedProjectedCapacity_sub_regularRemainder_sq_le_budget :
    (∫ x : ℝ in -1..1,
      (fourCellEvenEndpointSeedProjectedCapacityRepresenter x -
        fourCellOperatorHalfWidth *
          fourCellEndpointSeedRegularRemainderRepresenter x) ^ 2) ≤
      fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
        (553 / 20000 : ℝ) := by
  exact integral_capacity_sub_regularRemainder_sq_le_endpointSeed_budget
    fourCellEvenEndpointSeedProjectedCapacityRepresenter
      memLp_fourCellEvenEndpointSeedProjectedCapacityRepresenter
      integral_endpointSeedProjectedCapacityRepresenter_sq_le

/-- The canonical degree-below-eight removal identifies the complete tail
row with the combined capacity/regular-remainder representer, so the norm
budget above is exactly the dual bound required by the endpoint Schur step. -/
theorem integral_endpointSeedProjectedTailRowRepresenter_canonical_sq_le_budget :
    (∫ x : ℝ in -1..1,
      fourCellEvenEndpointSeedProjectedTailRowRepresenter
        fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x ^ 2) ≤
      fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
        (553 / 20000 : ℝ) := by
  calc
    (∫ x : ℝ in -1..1,
        fourCellEvenEndpointSeedProjectedTailRowRepresenter
          fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x ^ 2) =
      ∫ x : ℝ in -1..1,
        (fourCellEvenEndpointSeedProjectedCapacityRepresenter x -
          fourCellOperatorHalfWidth *
            fourCellEndpointSeedRegularRemainderRepresenter x) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      change
        fourCellEvenEndpointSeedProjectedTailRowRepresenter
            fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial x ^ 2 =
          (fourCellEvenEndpointSeedProjectedCapacityRepresenter x -
            fourCellOperatorHalfWidth *
              fourCellEndpointSeedRegularRemainderRepresenter x) ^ 2
      rw [endpointSeedProjectedTailRowRepresenter_canonical_eq,
        fourCellEvenEndpointSeedRegularTailRepresenter_sub_selector_eq_remainder
          hx]
    _ ≤ fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
        (553 / 20000 : ℝ) :=
      integral_endpointSeedProjectedCapacity_sub_regularRemainder_sq_le_budget

/-- Structural endpoint-row Schur closure on every genuine cutoff-eight
tail.  The coupled-core diagonal and the complete capacity/regular row are
both discharged, with no spectral truncation or exhaustive enumeration. -/
theorem fourCellEvenEndpointSeedRow_tail_sq_le_seed_mul_polarFree
    (r : ℝ → ℝ) (hr : Continuous r)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r)
    (heven : Function.Even r)
    (hzero : fourCellPositiveCoshMoment r
      (fourCellOperatorHalfWidth / 2) = 0)
    (hlow : centeredLegendreMomentsVanishBelow r 8) :
    fourCellEvenEndpointSeedRow r ^ 2 ≤
      fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
        fourCellEvenPolarFreeOperator r := by
  exact fourCellEvenEndpointSeedRow_tail_sq_le_seed_mul_polarFree_of_norm
    r hr hlocal heven hzero hlow
      (thirtyThree_div_twenty_mass_le_canonicalCoupledCore_cutoffEight
        r hr hlocal heven hzero)
      fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial
      natDegree_fourCellEvenEndpointSeedCanonicalTailSelectorPolynomial_lt_eight
      integral_endpointSeedProjectedTailRowRepresenter_canonical_sq_le_budget

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedCombinedNormStructural
