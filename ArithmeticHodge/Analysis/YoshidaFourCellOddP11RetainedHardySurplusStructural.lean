import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CrossSquareExtensionStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11RetainedHardySurplusStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointWeightedCauchy
open YoshidaFourCellOddP11CrossSquareExtensionStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Quantitative lower-strip reserve in the `P₁₁+` Hardy surplus

The raw-strip partition retains both the lower `P₁` spectral surplus and
the inverse-cube cross square.  On a globally `P₁`-orthogonal profile the
exact cross-square extension coefficient recovers most of the negative local
moment term.  A final sharp interval Cauchy estimate leaves
`15625 / 11172` copies of lower-strip mass after the standard
`2 L + (6/5) J` payment.

This is a form-level consequence of the coupled raw kernel.  It does not
replace the genuine `P₁₁+` tail by a finite list of modes.
-/

/-- Sharp Cauchy constant for the lower physical `P₁` moment. -/
private theorem lowerP1Moment_sq_le_nine_one_twenty_fifths_lowerMass
    (r : ℝ → ℝ) (hr : Continuous r) :
    (∫ x : ℝ in 0..3 / 5, x * r x) ^ 2 ≤
      (9 / 125 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (3 / 5))
  have hxMeas : AEStronglyMeasurable (fun x : ℝ ↦ x) μ :=
    continuous_id.aestronglyMeasurable.restrict
  have hrMeas : AEStronglyMeasurable r μ :=
    hr.aestronglyMeasurable.restrict
  have hxLp : MemLp (fun x : ℝ ↦ x) 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hxMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖x‖ ^ 2)
        (Icc (0 : ℝ) (3 / 5)) :=
      (continuous_norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hrLp : MemLp r 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hrMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
        (Icc (0 : ℝ) (3 / 5)) :=
      (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hcauchy := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1)
    (fun x : ℝ ↦ x) r (by simp) (by simpa using hxLp)
      (by simpa using hrLp)
  have hcauchy' :
      (∫ x : ℝ in 0..3 / 5, x * r x) ^ 2 ≤
        (∫ x : ℝ in 0..3 / 5, x ^ 2) *
          (∫ x : ℝ in 0..3 / 5, r x ^ 2) := by
    repeat rw [intervalIntegral.integral_of_le (by norm_num)]
    simpa only [μ, div_one, one_mul] using hcauchy
  have hx2 : (∫ x : ℝ in 0..3 / 5, x ^ 2) = 9 / 125 := by
    rw [integral_pow]
    norm_num
  rw [hx2] at hcauchy'
  exact hcauchy'

/-- The complete raw reserve still contains this exact lower-mass margin
after paying the weighted upper strip.  The coefficient is the exact Schur
completion
`11/3 + (1953125/100548 - 625/27) * (9/125)`.
-/
theorem thirtySevenNineSixNine_div_elevenOneSevenTwo_lowerMass_add_weightedUpper_le_raw
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0) :
    (37969 / 11172 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) +
        (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x) ≤
      fourCellOddRawStripCancellationReserve r := by
  have hraw :=
    lowerP1Surplus_add_weightedUpperMass_add_crossP1Square_le_rawReserve
      r hr hodd
  have hcross := exact_lowerP1Deviation_sq_le_crossP1Square r hr hodd
  rw [h1, mul_zero, sub_zero] at hcross
  have hmoment :=
    lowerP1Moment_sq_le_nine_one_twenty_fifths_lowerMass r hr.continuous
  nlinarith

/-- After the standard physical lower/weighted-upper payment, the retained
Hardy surplus controls `15625 / 11172` copies of lower-strip mass. -/
theorem fifteenSixTwoFive_div_elevenOneSevenTwo_lowerMass_le_retainedRawSurplus
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0) :
    (15625 / 11172 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) ≤
      fourCellOddRawStripCancellationReserve r -
        2 * (∫ x : ℝ in 0..3 / 5, r x ^ 2) -
        (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x) := by
  have hraw :=
    thirtySevenNineSixNine_div_elevenOneSevenTwo_lowerMass_add_weightedUpper_le_raw
      r hr hodd h1
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11RetainedHardySurplusStructural
