import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutCrossingPrimeSplitStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationCriterionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ArithmeticFunction BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutPositiveParentPropagationAttemptStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneCutPrimePhaseStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneQuarterSingleCrossingStructural
open MultiplicativeWeilMonotoneRealCutCrossingPrimeSplitStructural
open MultiplicativeWeilMonotoneRealCutFrontierStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# One-step propagation for a pointwise nonnegative real parent

The outer cutoff `C_k` is the real nested-cut pencil at `d = 0`, or,
equivalently, the head--suffix pencil with suffix coefficient `a = 1`.
At this physical coefficient the multiplier is just the nonnegative outer
step.  Thus the favorable crossing region is empty: the whole prime term is
the same-side cost.

Comparing the exact local-minus-prime formulas for `C_k` and `C_(k+1)` then
isolates the only unsigned cost that can obstruct one-step propagation: the
positive part of the increase of the same-side von-Mangoldt cost.  Propagation
follows if the corresponding increase of the full local critical energy
dominates that surviving cost.  No sign for this final local-versus-prime
inequality is asserted here.
-/

/-! ## The physical cutoff has no crossing contribution -/

theorem monotoneQuarterHeadSuffixMultiplier_one
    (k : ℤ) (t : ℝ) :
    monotoneQuarterHeadSuffixMultiplier k 1 t =
      monotoneQuarterStep k t := by
  rw [monotoneQuarterHeadSuffixMultiplier_eq_nested]
  unfold monotoneQuarterNestedMultiplier
  ring

theorem monotoneRealCutCrossingRegion_one_eq_empty
    (k : ℤ) (x : ℝ) :
    monotoneRealCutCrossingRegion k 1 x = ∅ := by
  ext y
  constructor
  · rintro ⟨_hy, hneg⟩
    rw [monotoneQuarterHeadSuffixMultiplier_one,
      monotoneQuarterHeadSuffixMultiplier_one] at hneg
    exact (not_lt_of_ge
      (mul_nonneg (monotoneQuarterStep_nonneg k y)
        (monotoneQuarterStep_nonneg k (x * y)))) hneg
  · intro hy
    exact hy.elim

theorem monotoneRealCutSameSideRegion_one_eq_Ioi
    (k : ℤ) (x : ℝ) :
    monotoneRealCutSameSideRegion k 1 x = Set.Ioi 0 := by
  have h := monotoneRealCut_sameSide_union_crossing k 1 x
  rw [monotoneRealCutCrossingRegion_one_eq_empty, Set.union_empty] at h
  exact h

/-- At the physical outer cutoff, the signed phase integral is exactly the
same-side integral; there is no crossing reserve to discard. -/
theorem monotoneCutSignedPhaseIntegral_zero_eq_sameSide
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (k : ℤ) (x : ℝ) :
    monotoneCutSignedPhaseIntegral parent k 0 x =
      monotoneRealCutSameSidePrimeCost parent k 1 x := by
  have h :=
    monotoneCutSignedPhaseIntegral_real_headSuffix_eq_sameSide_add_crossing
      parent hfixed k 1 x
  simpa [monotoneRealCutCrossingPrimeContribution,
    monotoneRealCutCrossingRegion_one_eq_empty] using h

/-- Nesting makes the physical same-side integrand decrease as the cutoff
index increases.  Pointwise nonnegativity of the parent is used exactly to
preserve the multiplier-product order. -/
theorem monotoneRealCutPrimeRatioIntegrand_one_anti_index
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) (x y : ℝ) :
    monotoneRealCutPrimeRatioIntegrand parent (k + 1) 1 x y ≤
      monotoneRealCutPrimeRatioIntegrand parent k 1 x y := by
  unfold monotoneRealCutPrimeRatioIntegrand
  rw [monotoneQuarterHeadSuffixMultiplier_one,
    monotoneQuarterHeadSuffixMultiplier_one,
    monotoneQuarterHeadSuffixMultiplier_one,
    monotoneQuarterHeadSuffixMultiplier_one]
  have hmask :
      monotoneQuarterStep (k + 1) (x * y) *
          monotoneQuarterStep (k + 1) y ≤
        monotoneQuarterStep k (x * y) * monotoneQuarterStep k y := by
    exact mul_le_mul
      (monotoneQuarterStep_succ_le k (x * y))
      (monotoneQuarterStep_succ_le k y)
      (monotoneQuarterStep_nonneg (k + 1) y)
      (monotoneQuarterStep_nonneg k (x * y))
  exact mul_le_mul_of_nonneg_right hmask
    (monotoneCutParentProduct_re_nonnegative_of_conjugate_fixed
      parent hfixed hnonneg x y)

private theorem monotoneRealCutPrimeRatioIntegrand_one_integrable
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (k : ℤ) (x : ℝ) :
    Integrable (monotoneRealCutPrimeRatioIntegrand parent k 1 x) := by
  let q := monotoneCutPencil parent k (((1 : ℝ) - 1 : ℝ) : ℂ)
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
  change (monotoneCutPhaseMask k
      (((1 : ℝ) - 1 : ℝ) : ℂ) x y *
    monotoneCutParentProduct parent x y).re = _
  rw [monotoneCutPhaseMask_mul_parentProduct_re_of_conjugate_fixed
      parent hfixed,
    monotoneCutPhaseRealMask_headSuffix]
  rfl

/-- Hence the same-side integral at every fixed dilation ratio is monotone
under passage from the inner cutoff to the outer cutoff. -/
theorem monotoneRealCutSameSidePrimeCost_one_anti_index
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) (x : ℝ) :
    monotoneRealCutSameSidePrimeCost parent (k + 1) 1 x ≤
      monotoneRealCutSameSidePrimeCost parent k 1 x := by
  unfold monotoneRealCutSameSidePrimeCost
  rw [monotoneRealCutSameSideRegion_one_eq_Ioi,
    monotoneRealCutSameSideRegion_one_eq_Ioi]
  exact MeasureTheory.setIntegral_mono_on
    (monotoneRealCutPrimeRatioIntegrand_one_integrable
      parent hfixed (k + 1) x).integrableOn
    (monotoneRealCutPrimeRatioIntegrand_one_integrable
      parent hfixed k x).integrableOn
    measurableSet_Ioi
    (fun y _hy ↦ monotoneRealCutPrimeRatioIntegrand_one_anti_index
      parent hfixed hnonneg k x y)

/-! ## The surviving unsigned prime cost -/

/-- Complete von-Mangoldt same-side cost of the physical cutoff `C_k`. -/
def monotoneRealCutUnsignedSameSidePrimeCost
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  ∑' n : ℕ,
    ArithmeticFunction.vonMangoldt (n + 1) *
      (2 * monotoneRealCutSameSidePrimeCost parent k 1
        ((n + 1 : ℕ) : ℝ))

theorem monotoneRealCutUnsignedSameSidePrimeCost_nonnegative
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) :
    0 ≤ monotoneRealCutUnsignedSameSidePrimeCost parent k := by
  unfold monotoneRealCutUnsignedSameSidePrimeCost
  apply tsum_nonneg
  intro n
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (mul_nonneg (by norm_num)
      (monotoneRealCutSameSidePrimeCost_nonnegative
        parent hfixed hnonneg k 1 ((n + 1 : ℕ) : ℝ)))

/-- The usual signed prime phase at `d = 0` is precisely the unsigned
same-side cost above. -/
theorem monotoneCutSignedPrimePhaseSum_zero_eq_unsignedSameSide
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (k : ℤ) :
    monotoneCutSignedPrimePhaseSum parent k 0 =
      monotoneRealCutUnsignedSameSidePrimeCost parent k := by
  unfold monotoneCutSignedPrimePhaseSum
    monotoneRealCutUnsignedSameSidePrimeCost
  apply tsum_congr
  intro n
  rw [monotoneCutSignedPhaseIntegral_zero_eq_sameSide parent hfixed]

@[simp] theorem monotoneCutPencil_zero
    (parent : BombieriTest) (k : ℤ) :
    monotoneCutPencil parent k 0 =
      monotoneQuarterCutoff parent k := by
  simp [monotoneCutPencil]

private theorem monotoneRealCutUnsignedSameSidePrimeSummand_eq_re
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (k : ℤ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt (n + 1) *
        (2 * monotoneRealCutSameSidePrimeCost parent k 1
          ((n + 1 : ℕ) : ℝ)) =
      (vonMangoldtPrimeSummand
        (bombieriQuadraticTest (monotoneQuarterCutoff parent k)) n).re := by
  unfold vonMangoldtPrimeSummand
  rw [primeKernel_bombieriQuadraticTest_eq_two_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [← monotoneCutPencil_zero parent k,
    bombieriQuadraticTest_monotoneCutPencil_re_eq_signedPhaseIntegral,
    monotoneCutSignedPhaseIntegral_zero_eq_sameSide parent hfixed]

private theorem monotoneRealCutUnsignedSameSidePrimeSummand_summable
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (k : ℤ) :
    Summable (fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt (n + 1) *
        (2 * monotoneRealCutSameSidePrimeCost parent k 1
          ((n + 1 : ℕ) : ℝ))) := by
  have hs : Summable (fun n : ℕ ↦
      (vonMangoldtPrimeSummand
        (bombieriQuadraticTest (monotoneQuarterCutoff parent k)) n).re) :=
    Complex.reCLM.summable
      (vonMangoldtPrimeSummand_summable
        (bombieriQuadraticTest (monotoneQuarterCutoff parent k)))
  exact hs.congr (fun n ↦
    (monotoneRealCutUnsignedSameSidePrimeSummand_eq_re
      parent hfixed k n).symm)

/-- The total unsigned same-side cost is monotone under nested cutoffs. -/
theorem monotoneRealCutUnsignedSameSidePrimeCost_anti_index
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) :
    monotoneRealCutUnsignedSameSidePrimeCost parent (k + 1) ≤
      monotoneRealCutUnsignedSameSidePrimeCost parent k := by
  unfold monotoneRealCutUnsignedSameSidePrimeCost
  exact (monotoneRealCutUnsignedSameSidePrimeSummand_summable
      parent hfixed (k + 1)).tsum_le_tsum
    (fun n ↦ mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (monotoneRealCutSameSidePrimeCost_one_anti_index
          parent hfixed hnonneg k ((n + 1 : ℕ) : ℝ))
        (by norm_num))
      ArithmeticFunction.vonMangoldt_nonneg)
    (monotoneRealCutUnsignedSameSidePrimeSummand_summable
      parent hfixed k)

/-! ## Exact local-minus-unsigned-cost balance -/

/-- Full local critical energy of the physical cutoff `C_k`. -/
def monotoneRealCutLocalCriticalEnergy
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  (bombieriLocalCriticalForm
    (monotoneQuarterCutoff parent k)
    (monotoneQuarterCutoff parent k)).re

/-- Increase of the full local energy when adjoining the head cell. -/
def monotoneRealCutLocalCriticalIncrement
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  monotoneRealCutLocalCriticalEnergy parent k -
    monotoneRealCutLocalCriticalEnergy parent (k + 1)

/-- The only unfavorable part of the change in unsigned prime cost.  A
decrease in that cost is favorable and is discarded by the positive part. -/
def monotoneRealCutSurvivingSameSidePrimeCost
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  max
    (monotoneRealCutUnsignedSameSidePrimeCost parent k -
      monotoneRealCutUnsignedSameSidePrimeCost parent (k + 1))
    0

theorem monotoneRealCutSurvivingSameSidePrimeCost_nonnegative
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ monotoneRealCutSurvivingSameSidePrimeCost parent k := by
  exact le_max_right _ _

theorem monotoneRealCut_unsignedPrimeIncrement_le_survivingCost
    (parent : BombieriTest) (k : ℤ) :
    monotoneRealCutUnsignedSameSidePrimeCost parent k -
        monotoneRealCutUnsignedSameSidePrimeCost parent (k + 1) ≤
      monotoneRealCutSurvivingSameSidePrimeCost parent k := by
  exact le_max_left _ _

/-- On the target class of pointwise nonnegative real parents, the surviving
positive part is exactly the full same-side prime-cost increment. -/
theorem monotoneRealCutSurvivingSameSidePrimeCost_eq_increment
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) :
    monotoneRealCutSurvivingSameSidePrimeCost parent k =
      monotoneRealCutUnsignedSameSidePrimeCost parent k -
        monotoneRealCutUnsignedSameSidePrimeCost parent (k + 1) := by
  unfold monotoneRealCutSurvivingSameSidePrimeCost
  rw [max_eq_left]
  exact sub_nonneg.mpr
    (monotoneRealCutUnsignedSameSidePrimeCost_anti_index
      parent hfixed hnonneg k)

/-- Exact full-functional formula for one physical cutoff. -/
theorem bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_local_sub_unsigned
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (k : ℤ) :
    bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) =
      monotoneRealCutLocalCriticalEnergy parent k -
        monotoneRealCutUnsignedSameSidePrimeCost parent k := by
  unfold bombieriRealQuadraticValue monotoneRealCutLocalCriticalEnergy
  rw [← monotoneCutPencil_zero parent k,
    bombieriFunctional_monotoneCutPencil_re_eq_local_sub_signedPrime,
    monotoneCutSignedPrimePhaseSum_zero_eq_unsignedSameSide
      parent hfixed]

/-- Exact adjacent-cut balance.  This is stronger information than the bare
propagation implication: it identifies separately the local increment and
the unsigned same-side prime increment. -/
theorem bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_inner_add_increments
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (k : ℤ) :
    bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) =
      bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (k + 1)) +
        monotoneRealCutLocalCriticalIncrement parent k -
        (monotoneRealCutUnsignedSameSidePrimeCost parent k -
          monotoneRealCutUnsignedSameSidePrimeCost parent (k + 1)) := by
  rw [bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_local_sub_unsigned
      parent hfixed k,
    bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_local_sub_unsigned
      parent hfixed (k + 1)]
  unfold monotoneRealCutLocalCriticalIncrement
  ring

/-- Sharp local-versus-same-side sufficient inequality for one-step
propagation.  The right side is a genuinely nonnegative unsigned cost on the
stated parent class, by the preceding monotonicity theorem. -/
theorem bombieriRealQuadraticValue_monotoneQuarterCutoff_propagates_of_local_dominates_sameSideIncrease
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ)
    (hinner : 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent (k + 1)))
    (hlocal :
      monotoneRealCutUnsignedSameSidePrimeCost parent k -
          monotoneRealCutUnsignedSameSidePrimeCost parent (k + 1) ≤
        monotoneRealCutLocalCriticalIncrement parent k) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent k) := by
  have _hcost : 0 ≤
      monotoneRealCutUnsignedSameSidePrimeCost parent k -
        monotoneRealCutUnsignedSameSidePrimeCost parent (k + 1) :=
    sub_nonneg.mpr
      (monotoneRealCutUnsignedSameSidePrimeCost_anti_index
        parent hfixed hnonneg k)
  rw [bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_inner_add_increments
    parent hfixed k]
  linarith

/-- Actual one-step propagation for a conjugation-fixed pointwise-nonnegative
parent, conditional only on the exposed local-versus-surviving-cost bound.
The crossing split shows that no additional signed prime term remains. -/
theorem bombieriRealQuadraticValue_monotoneQuarterCutoff_propagates_of_localIncrement
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ)
    (hinner : 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent (k + 1)))
    (hlocal : monotoneRealCutSurvivingSameSidePrimeCost parent k ≤
      monotoneRealCutLocalCriticalIncrement parent k) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent k) := by
  apply
    bombieriRealQuadraticValue_monotoneQuarterCutoff_propagates_of_local_dominates_sameSideIncrease
      parent hfixed hnonneg k hinner
  rw [← monotoneRealCutSurvivingSameSidePrimeCost_eq_increment
    parent hfixed hnonneg k]
  exact hlocal

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutPositiveParentPropagationAttemptStructural
