import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterSingleCrossingStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutFrontierStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ArithmeticFunction BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutCrossingPrimeSplitStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneCutPrimePhaseStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneQuarterSingleCrossingStructural
open MultiplicativeWeilMonotoneRealCutFrontierStructural

/-!
# Signed prime split for a negative real monotone cut

For a coefficient-conjugation-fixed parent with nonnegative pointwise values,
the directed parent product is nonnegative.  A negative real head--suffix
phase has one multiplier sign crossing.  Prime correlations which cross it
therefore contribute nonpositively to the prime cost; only correlations whose
two points stay on the same side contribute a nonnegative cost.
-/

/-- Real prime-ratio integrand in head-cell plus suffix coordinates. -/
def monotoneRealCutPrimeRatioIntegrand
    (parent : BombieriTest) (k : ℤ) (a x y : ℝ) : ℝ :=
  monotoneQuarterHeadSuffixMultiplier k a (x * y) *
    monotoneQuarterHeadSuffixMultiplier k a y *
      (monotoneCutParentProduct parent x y).re

/-- Same-side region, including the zero boundary of the crossing. -/
def monotoneRealCutSameSideRegion (k : ℤ) (a x : ℝ) : Set ℝ :=
  {y : ℝ | 0 < y ∧
    0 ≤ monotoneQuarterHeadSuffixMultiplier k a y *
      monotoneQuarterHeadSuffixMultiplier k a (x * y)}

/-- Strict positive-to-negative crossing region. -/
def monotoneRealCutCrossingRegion (k : ℤ) (a x : ℝ) : Set ℝ :=
  {y : ℝ | 0 < y ∧
    monotoneQuarterHeadSuffixMultiplier k a y *
      monotoneQuarterHeadSuffixMultiplier k a (x * y) < 0}

/-- The real phase mask for nested scalar `a-1` is exactly the product of the
head--suffix multipliers. -/
theorem monotoneCutPhaseRealMask_headSuffix
    (k : ℤ) (a x y : ℝ) :
    monotoneCutPhaseRealMask k ((a - 1 : ℝ) : ℂ) x y =
      monotoneQuarterHeadSuffixMultiplier k a (x * y) *
        monotoneQuarterHeadSuffixMultiplier k a y := by
  rw [monotoneCutPhaseRealMask_eq_completed]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [monotoneQuarterHeadSuffixMultiplier_eq_nested,
    monotoneQuarterHeadSuffixMultiplier_eq_nested]
  unfold monotoneQuarterNestedMultiplier
  ring

/-- A real, pointwise nonnegative parent has nonnegative directed product. -/
theorem monotoneCutParentProduct_re_nonnegative_of_conjugate_fixed
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (x y : ℝ) :
    0 ≤ (monotoneCutParentProduct parent x y).re := by
  unfold monotoneCutParentProduct
  rw [Complex.mul_re]
  have hxy := apply_im_eq_zero_of_conjugate_fixed parent hfixed (x * y)
  have hy := apply_im_eq_zero_of_conjugate_fixed parent hfixed y
  change 0 ≤
    (parent (x * y)).re * (parent y).re -
      (parent (x * y)).im * (-(parent y).im)
  rw [hxy, hy]
  simp only [neg_zero, mul_zero, sub_zero]
  exact mul_nonneg (hnonneg (x * y)) (hnonneg y)

/-- For a negative real head--suffix phase and an expanding ratio, membership
in the crossing set is exactly a positive-to-negative multiplier crossing. -/
theorem mem_monotoneRealCutCrossingRegion_iff
    (k : ℤ) {a x y : ℝ} (ha : a < 0) (hx : 1 ≤ x) :
    y ∈ monotoneRealCutCrossingRegion k a x ↔
      0 < y ∧
        0 < monotoneQuarterHeadSuffixMultiplier k a y ∧
          monotoneQuarterHeadSuffixMultiplier k a (x * y) < 0 := by
  unfold monotoneRealCutCrossingRegion
  constructor
  · rintro ⟨hy, hmul⟩
    have hyxy : y ≤ x * y := by
      calc
        y = 1 * y := by ring
        _ ≤ x * y := mul_le_mul_of_nonneg_right hx hy.le
    have hcross :=
      (monotoneQuarterHeadSuffixMultiplier_mul_neg_iff_crossingLevel
        k ha hyxy).1 hmul
    have hd : a - 1 < 0 := by linarith
    have hneg :=
      (monotoneQuarterNestedMultiplier_neg_iff_crossingLevel_lt_step
        k hd (x * y)).2 (by
          have hlevel :
              monotoneQuarterNestedCrossingLevel (a - 1) = (1 - a)⁻¹ := by
            unfold monotoneQuarterNestedCrossingLevel
            field_simp [show a - 1 ≠ 0 by linarith,
              show 1 - a ≠ 0 by linarith]
            ring
          rw [hlevel]
          exact hcross.2)
    rw [← monotoneQuarterHeadSuffixMultiplier_eq_nested] at hneg
    exact ⟨hy, hcross.1, hneg⟩
  · rintro ⟨hy, hpos, hneg⟩
    exact ⟨hy, mul_neg_of_pos_of_neg hpos hneg⟩

/-- Same-side and crossing regions are disjoint and exhaust the positive
integration domain. -/
theorem monotoneRealCut_sameSide_union_crossing
    (k : ℤ) (a x : ℝ) :
    monotoneRealCutSameSideRegion k a x ∪
        monotoneRealCutCrossingRegion k a x = Set.Ioi 0 := by
  ext y
  unfold monotoneRealCutSameSideRegion monotoneRealCutCrossingRegion
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_Ioi]
  constructor
  · rintro (⟨hy, _h⟩ | ⟨hy, _h⟩) <;> exact hy
  · intro hy
    by_cases hprod :
        0 ≤ monotoneQuarterHeadSuffixMultiplier k a y *
          monotoneQuarterHeadSuffixMultiplier k a (x * y)
    · exact Or.inl ⟨hy, hprod⟩
    · exact Or.inr ⟨hy, lt_of_not_ge hprod⟩

theorem monotoneRealCut_sameSide_disjoint_crossing
    (k : ℤ) (a x : ℝ) :
    Disjoint (monotoneRealCutSameSideRegion k a x)
      (monotoneRealCutCrossingRegion k a x) := by
  rw [Set.disjoint_left]
  intro y hsame hcross
  exact (not_lt_of_ge hsame.2) hcross.2

/-- The prime-ratio integrand is nonnegative on the same-side region. -/
theorem monotoneRealCutPrimeRatioIntegrand_nonnegative_on_sameSide
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) (a x : ℝ) {y : ℝ}
    (hy : y ∈ monotoneRealCutSameSideRegion k a x) :
    0 ≤ monotoneRealCutPrimeRatioIntegrand parent k a x y := by
  unfold monotoneRealCutPrimeRatioIntegrand
  have hp := monotoneCutParentProduct_re_nonnegative_of_conjugate_fixed
    parent hfixed hnonneg x y
  exact mul_nonneg (by simpa only [mul_comm] using hy.2) hp

/-- The crossing integrand is favorable: it is nonpositive before the prime
sum is subtracted from the local critical energy. -/
theorem monotoneRealCutPrimeRatioIntegrand_nonpositive_on_crossing
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) (a x : ℝ) {y : ℝ}
    (hy : y ∈ monotoneRealCutCrossingRegion k a x) :
    monotoneRealCutPrimeRatioIntegrand parent k a x y ≤ 0 := by
  unfold monotoneRealCutPrimeRatioIntegrand
  have hp := monotoneCutParentProduct_re_nonnegative_of_conjugate_fixed
    parent hfixed hnonneg x y
  exact mul_nonpos_of_nonpos_of_nonneg
    (by simpa only [mul_comm] using hy.2.le) hp

theorem continuous_monotoneQuarterHeadSuffixMultiplier
    (k : ℤ) (a : ℝ) :
    Continuous (monotoneQuarterHeadSuffixMultiplier k a) := by
  unfold monotoneQuarterHeadSuffixMultiplier
  exact (monotoneQuarterWeight_contDiff k).continuous.add
    (continuous_const.mul (monotoneQuarterStep_contDiff (k + 1)).continuous)

theorem measurableSet_monotoneRealCutSameSideRegion
    (k : ℤ) (a x : ℝ) :
    MeasurableSet (monotoneRealCutSameSideRegion k a x) := by
  have hcont : Continuous (fun y : ℝ ↦
      monotoneQuarterHeadSuffixMultiplier k a y *
        monotoneQuarterHeadSuffixMultiplier k a (x * y)) := by
    exact (continuous_monotoneQuarterHeadSuffixMultiplier k a).mul
      ((continuous_monotoneQuarterHeadSuffixMultiplier k a).comp
        (continuous_const.mul continuous_id))
  change MeasurableSet (Set.Ioi 0 ∩ {y : ℝ | 0 ≤
    monotoneQuarterHeadSuffixMultiplier k a y *
      monotoneQuarterHeadSuffixMultiplier k a (x * y)})
  exact measurableSet_Ioi.inter
    (measurableSet_le measurable_const hcont.measurable)

theorem measurableSet_monotoneRealCutCrossingRegion
    (k : ℤ) (a x : ℝ) :
    MeasurableSet (monotoneRealCutCrossingRegion k a x) := by
  have hcont : Continuous (fun y : ℝ ↦
      monotoneQuarterHeadSuffixMultiplier k a y *
        monotoneQuarterHeadSuffixMultiplier k a (x * y)) := by
    exact (continuous_monotoneQuarterHeadSuffixMultiplier k a).mul
      ((continuous_monotoneQuarterHeadSuffixMultiplier k a).comp
        (continuous_const.mul continuous_id))
  change MeasurableSet (Set.Ioi 0 ∩ {y : ℝ |
    monotoneQuarterHeadSuffixMultiplier k a y *
      monotoneQuarterHeadSuffixMultiplier k a (x * y) < 0})
  exact measurableSet_Ioi.inter
    (measurableSet_lt hcont.measurable measurable_const)

private theorem monotoneRealCutPrimeRatioIntegrand_integrable
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (k : ℤ) (a x : ℝ) :
    Integrable (monotoneRealCutPrimeRatioIntegrand parent k a x) := by
  let q := monotoneCutPencil parent k ((a - 1 : ℝ) : ℂ)
  have hcont : Continuous (fun y : ℝ ↦
      q (x * y) * starRingEnd ℂ (q y)) := by
    fun_prop
  have hcompact : HasCompactSupport (fun y : ℝ ↦
      starRingEnd ℂ (q y)) :=
    q.hasCompactSupport.comp_left (map_zero (starRingEnd ℂ))
  have hintComplex : Integrable (fun y : ℝ ↦
      q (x * y) * starRingEnd ℂ (q y)) :=
    hcont.integrable_of_hasCompactSupport hcompact.mul_left
  apply hintComplex.re.congr
  filter_upwards [] with y
  dsimp only [q]
  rw [monotoneCutPencil_mul_conj_eq_phaseMask]
  change (monotoneCutPhaseMask k ((a - 1 : ℝ) : ℂ) x y *
    monotoneCutParentProduct parent x y).re = _
  rw [
    monotoneCutPhaseMask_mul_parentProduct_re_of_conjugate_fixed
      parent hfixed,
    monotoneCutPhaseRealMask_headSuffix]
  rfl

/-- The nonnegative same-side part of one prime-ratio correlation. -/
def monotoneRealCutSameSidePrimeCost
    (parent : BombieriTest) (k : ℤ) (a x : ℝ) : ℝ :=
  ∫ y : ℝ in monotoneRealCutSameSideRegion k a x,
    monotoneRealCutPrimeRatioIntegrand parent k a x y

/-- The favorable nonpositive crossing part of one prime-ratio correlation. -/
def monotoneRealCutCrossingPrimeContribution
    (parent : BombieriTest) (k : ℤ) (a x : ℝ) : ℝ :=
  ∫ y : ℝ in monotoneRealCutCrossingRegion k a x,
    monotoneRealCutPrimeRatioIntegrand parent k a x y

theorem monotoneRealCutSameSidePrimeCost_nonnegative
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) (a x : ℝ) :
    0 ≤ monotoneRealCutSameSidePrimeCost parent k a x := by
  unfold monotoneRealCutSameSidePrimeCost
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem
    (measurableSet_monotoneRealCutSameSideRegion k a x)] with y hy
  exact monotoneRealCutPrimeRatioIntegrand_nonnegative_on_sameSide
    parent hfixed hnonneg k a x hy

theorem monotoneRealCutCrossingPrimeContribution_nonpositive
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) (a x : ℝ) :
    monotoneRealCutCrossingPrimeContribution parent k a x ≤ 0 := by
  unfold monotoneRealCutCrossingPrimeContribution
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem
    (measurableSet_monotoneRealCutCrossingRegion k a x)] with y hy
  exact monotoneRealCutPrimeRatioIntegrand_nonpositive_on_crossing
    parent hfixed hnonneg k a x hy

/-- Exact signed decomposition at one expanding prime ratio.  The second
summand is favorable; the first is the entire remaining nonnegative cost. -/
theorem monotoneCutSignedPhaseIntegral_real_headSuffix_eq_sameSide_add_crossing
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (k : ℤ) (a x : ℝ) :
    monotoneCutSignedPhaseIntegral parent k ((a - 1 : ℝ) : ℂ) x =
      monotoneRealCutSameSidePrimeCost parent k a x +
        monotoneRealCutCrossingPrimeContribution parent k a x := by
  rw [monotoneCutSignedPhaseIntegral_eq_real_of_conjugate_fixed
    parent hfixed]
  have hint := monotoneRealCutPrimeRatioIntegrand_integrable
    parent hfixed k a x
  have hsameMeas := measurableSet_monotoneRealCutSameSideRegion k a x
  have hcrossMeas := measurableSet_monotoneRealCutCrossingRegion k a x
  calc
    (∫ y : ℝ in Set.Ioi 0,
        monotoneCutPhaseRealMask k ((a - 1 : ℝ) : ℂ) x y *
          (monotoneCutParentProduct parent x y).re) =
        ∫ y : ℝ in Set.Ioi 0,
          monotoneRealCutPrimeRatioIntegrand parent k a x y := by
            apply integral_congr_ae
            filter_upwards [] with y
            rw [monotoneCutPhaseRealMask_headSuffix]
            rfl
    _ = ∫ y : ℝ in
          monotoneRealCutSameSideRegion k a x ∪
            monotoneRealCutCrossingRegion k a x,
          monotoneRealCutPrimeRatioIntegrand parent k a x y := by
            rw [monotoneRealCut_sameSide_union_crossing]
    _ = (∫ y : ℝ in monotoneRealCutSameSideRegion k a x,
          monotoneRealCutPrimeRatioIntegrand parent k a x y) +
        ∫ y : ℝ in monotoneRealCutCrossingRegion k a x,
          monotoneRealCutPrimeRatioIntegrand parent k a x y := by
            exact MeasureTheory.setIntegral_union
              (monotoneRealCut_sameSide_disjoint_crossing k a x)
              hcrossMeas
              hint.integrableOn hint.integrableOn
    _ = _ := rfl

/-- The signed phase at a negative real head--suffix scalar is bounded above
by the same-side cost alone, because crossing correlations only help. -/
theorem monotoneCutSignedPhaseIntegral_real_headSuffix_le_sameSide
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) (a x : ℝ) :
    monotoneCutSignedPhaseIntegral parent k ((a - 1 : ℝ) : ℂ) x ≤
      monotoneRealCutSameSidePrimeCost parent k a x := by
  rw [monotoneCutSignedPhaseIntegral_real_headSuffix_eq_sameSide_add_crossing
    parent hfixed]
  have hcross := monotoneRealCutCrossingPrimeContribution_nonpositive
    parent hfixed hnonneg k a x
  linarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutCrossingPrimeSplitStructural
