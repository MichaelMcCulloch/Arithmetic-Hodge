import ArithmeticHodge.Analysis.MultiplicativeWeilRealLogKernelStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealCutPhaseReductionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ComplexConjugate

namespace ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationLogDefectStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealLogKernelStructural
open YoshidaBombieriCrossDistribution
open YoshidaCauchyPairing

/-!
# Exact logarithmic defect for one monotone propagation step

Write the outer cutoff as

`C_k = M_k + C_(k+1)`,

where `M_k` is the ratio-two head cell.  This file expands the resulting
quadratic defect in critical logarithmic coordinates.  The head--suffix
correlation is the unchanged parent correlation multiplied by an explicit
two-point lag mask.  The complete one-step defect is twice its archimedean
distribution minus twice its symmetric Mangoldt atomic series.

The exact lower bound needed to propagate from `C_(k+1)` to `C_k` is then
recorded as an iff, not introduced as a new global positivity hypothesis.
The pointwise mask is nonnegative, but it multiplies the signed parent
correlation and the Mangoldt part is subtracted.  Thus neither the inner
diagonal hypothesis nor monotonicity alone supplies the required bound.
-/

/-- The head--suffix multiplier at lag `u` and base logarithmic coordinate
`t`.  Physical evaluation occurs at `exp (-t)` in the head and at
`exp (-(u+t))` in the suffix. -/
def monotoneQuarterHeadSuffixLogMultiplier
    (k : ℤ) (u t : ℝ) : ℝ :=
  monotoneQuarterWeight k (Real.exp (-t)) *
    monotoneQuarterStep (k + 1) (Real.exp (-(u + t)))

/-- The critical logarithmic parent product before applying the cutoff
multiplier. -/
def monotoneQuarterParentLogProduct
    (parent : BombieriTest) (u t : ℝ) : ℂ :=
  starRingEnd ℂ (parent.logarithmicPullbackSchwartz (1 / 2) t) *
    parent.logarithmicPullbackSchwartz (1 / 2) (u + t)

/-- The head--suffix correlation displayed as a masked parent integral. -/
def monotoneQuarterHeadSuffixLogCorrelation
    (parent : BombieriTest) (k : ℤ) (u : ℝ) : ℂ :=
  ∫ t : ℝ, ((monotoneQuarterHeadSuffixLogMultiplier k u t : ℝ) : ℂ) *
    monotoneQuarterParentLogProduct parent u t

/-- The critical pullback of the head cell is the parent pullback multiplied
by the head weight at the corresponding physical point. -/
private theorem monotoneQuarterCell_logarithmicPullbackSchwartz
    (parent : BombieriTest) (k : ℤ) (t : ℝ) :
    (monotoneQuarterCell parent k).logarithmicPullbackSchwartz (1 / 2) t =
      ((monotoneQuarterWeight k (Real.exp (-t)) : ℝ) : ℂ) *
        parent.logarithmicPullbackSchwartz (1 / 2) t := by
  simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullback, monotoneQuarterCell_apply]
  push_cast
  ring

/-- The critical pullback of the next cutoff is the parent pullback
multiplied by the next boundary step. -/
private theorem monotoneQuarterCutoff_logarithmicPullbackSchwartz
    (parent : BombieriTest) (k : ℤ) (t : ℝ) :
    (monotoneQuarterCutoff parent k).logarithmicPullbackSchwartz (1 / 2) t =
      ((monotoneQuarterStep k (Real.exp (-t)) : ℝ) : ℂ) *
        parent.logarithmicPullbackSchwartz (1 / 2) t := by
  simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullback, monotoneQuarterCutoff_apply]
  push_cast
  ring

/-- Exact lag-multiplier formula for the head--suffix correlation. -/
theorem bombieriCriticalCrossCorrelation_cell_cutoff_eq_parentLogMultiplier
    (parent : BombieriTest) (k : ℤ) (u : ℝ) :
    bombieriCriticalCrossCorrelation
        (monotoneQuarterCell parent k)
        (monotoneQuarterCutoff parent (k + 1)) u =
      monotoneQuarterHeadSuffixLogCorrelation parent k u := by
  rw [bombieriCriticalCrossCorrelation, crossCorrelation_apply]
  unfold monotoneQuarterHeadSuffixLogCorrelation
  apply integral_congr_ae
  filter_upwards [] with t
  rw [monotoneQuarterCell_logarithmicPullbackSchwartz,
    monotoneQuarterCutoff_logarithmicPullbackSchwartz]
  unfold monotoneQuarterHeadSuffixLogMultiplier
    monotoneQuarterParentLogProduct
  change (starRingEnd ℂ)
      (((monotoneQuarterWeight k (Real.exp (-t)) : ℝ) : ℂ) *
        parent.logarithmicPullbackSchwartz (1 / 2) t) *
      (((monotoneQuarterStep (k + 1) (Real.exp (-(u + t))) : ℝ) : ℂ) *
        parent.logarithmicPullbackSchwartz (1 / 2) (u + t)) = _
  rw [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- The displayed multiplier is pointwise nonnegative. -/
theorem monotoneQuarterHeadSuffixLogMultiplier_nonnegative
    (k : ℤ) (u t : ℝ) :
    0 ≤ monotoneQuarterHeadSuffixLogMultiplier k u t := by
  unfold monotoneQuarterHeadSuffixLogMultiplier
  exact mul_nonneg
    (monotoneQuarterWeight_nonnegative k _)
    (monotoneQuarterStep_nonneg (k + 1) _)

/-- Despite the nonnegative mask, the real integrand retains exactly the sign
of the parent product. -/
theorem monotoneQuarterHeadSuffixLogIntegrand_re
    (parent : BombieriTest) (k : ℤ) (u t : ℝ) :
    (((monotoneQuarterHeadSuffixLogMultiplier k u t : ℝ) : ℂ) *
        monotoneQuarterParentLogProduct parent u t).re =
      monotoneQuarterHeadSuffixLogMultiplier k u t *
        (monotoneQuarterParentLogProduct parent u t).re := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- Cauchy evaluation of the explicit head--suffix parent-mask
correlation. -/
def monotoneQuarterHeadSuffixCauchyValue
    (parent : BombieriTest) (k : ℤ) (j : ℕ) : ℂ :=
  ∫ u : ℝ,
    (Real.exp (-(2 * (j : ℝ) + 1 / 2) * |u|) : ℝ) *
      monotoneQuarterHeadSuffixLogCorrelation parent k u

theorem bombieriCauchyCrossValue_cell_cutoff_eq_parentLogMultiplier
    (parent : BombieriTest) (k : ℤ) (j : ℕ) :
    bombieriCauchyCrossValue
        (monotoneQuarterCell parent k)
        (monotoneQuarterCutoff parent (k + 1)) j =
      monotoneQuarterHeadSuffixCauchyValue parent k j := by
  unfold bombieriCauchyCrossValue monotoneQuarterHeadSuffixCauchyValue
  apply integral_congr_ae
  filter_upwards [] with u
  rw [bombieriCriticalCrossCorrelation_cell_cutoff_eq_parentLogMultiplier]

/-- The renormalized digamma distribution evaluated on the explicit
head--suffix masked-parent correlation. -/
def monotoneQuarterHeadSuffixDigammaValue
    (parent : BombieriTest) (k : ℤ) : ℂ :=
  -(monotoneQuarterHeadSuffixCauchyValue parent k 0 +
      (Real.eulerMascheroniConstant : ℂ) *
        monotoneQuarterHeadSuffixLogCorrelation parent k 0 +
      ∑' j : ℕ,
        (monotoneQuarterHeadSuffixCauchyValue parent k (j + 1) -
          (((j + 1 : ℕ) : ℝ)⁻¹ : ℂ) *
            monotoneQuarterHeadSuffixLogCorrelation parent k 0)) -
    (Real.log Real.pi : ℂ) *
      monotoneQuarterHeadSuffixLogCorrelation parent k 0

theorem bombieriCrossDigammaCauchySeriesValue_cell_cutoff_eq_parentLogMultiplier
    (parent : BombieriTest) (k : ℤ) :
    bombieriCrossDigammaCauchySeriesValue
        (monotoneQuarterCell parent k)
        (monotoneQuarterCutoff parent (k + 1)) =
      monotoneQuarterHeadSuffixDigammaValue parent k := by
  unfold bombieriCrossDigammaCauchySeriesValue
    monotoneQuarterHeadSuffixDigammaValue
  simp_rw [bombieriCriticalCrossCorrelation_cell_cutoff_eq_parentLogMultiplier,
    bombieriCauchyCrossValue_cell_cutoff_eq_parentLogMultiplier]

/-- Explicit archimedean part of the one-step head--suffix cross. -/
def monotoneQuarterHeadSuffixRealArchimedeanCross
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  (∫ u : ℝ, bombieriLogPolarKernel u *
      (monotoneQuarterHeadSuffixLogCorrelation parent k u).re) +
    (monotoneQuarterHeadSuffixDigammaValue parent k).re

/-- Explicit symmetric Mangoldt atomic part of the one-step head--suffix
cross. -/
def monotoneQuarterHeadSuffixRealPrimeCross
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  ∑' j : ℕ, bombieriLogPrimeAtomWeight j *
    ((monotoneQuarterHeadSuffixLogCorrelation parent k
        (-Real.log (((j + 1 : ℕ) : ℝ)))).re +
      (monotoneQuarterHeadSuffixLogCorrelation parent k
        (Real.log (((j + 1 : ℕ) : ℝ)))).re)

/-- Twice the complete head--suffix cross is the exact quadratic defect in
one propagation step. -/
def monotoneQuarterRealLogStepDefect
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  2 * (monotoneQuarterHeadSuffixRealArchimedeanCross parent k -
    monotoneQuarterHeadSuffixRealPrimeCross parent k)

theorem bombieriRealLogArchimedeanCross_cell_cutoff_eq_explicit
    (parent : BombieriTest) (k : ℤ) :
    bombieriRealLogArchimedeanCross
        (monotoneQuarterCell parent k)
        (monotoneQuarterCutoff parent (k + 1)) =
      monotoneQuarterHeadSuffixRealArchimedeanCross parent k := by
  unfold bombieriRealLogArchimedeanCross
    monotoneQuarterHeadSuffixRealArchimedeanCross
    bombieriRealLogCorrelation
  rw [bombieriCrossDigammaCauchySeriesValue_cell_cutoff_eq_parentLogMultiplier]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  rw [bombieriCriticalCrossCorrelation_cell_cutoff_eq_parentLogMultiplier]

theorem bombieriRealLogPrimeAtomCross_cell_cutoff_eq_explicit
    (parent : BombieriTest) (k : ℤ) :
    bombieriRealLogPrimeAtomCross
        (monotoneQuarterCell parent k)
        (monotoneQuarterCutoff parent (k + 1)) =
      monotoneQuarterHeadSuffixRealPrimeCross parent k := by
  unfold bombieriRealLogPrimeAtomCross
    monotoneQuarterHeadSuffixRealPrimeCross bombieriRealLogCorrelation
  apply tsum_congr
  intro j
  rw [bombieriCriticalCrossCorrelation_cell_cutoff_eq_parentLogMultiplier,
    bombieriCriticalCrossCorrelation_cell_cutoff_eq_parentLogMultiplier]

/-- The explicit defect is exactly twice the complete real logarithmic
head--suffix cross. -/
theorem monotoneQuarterRealLogStepDefect_eq_completeCross
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterRealLogStepDefect parent k =
      2 * bombieriCompleteRealLogKernelCross
        (monotoneQuarterCell parent k)
        (monotoneQuarterCutoff parent (k + 1)) := by
  unfold monotoneQuarterRealLogStepDefect
    bombieriCompleteRealLogKernelCross
  rw [bombieriRealLogArchimedeanCross_cell_cutoff_eq_explicit,
    bombieriRealLogPrimeAtomCross_cell_cutoff_eq_explicit]

/-- Exact one-step identity `Q(C_k) = Q(M_k) + Q(C_(k+1)) + defect`. -/
theorem bombieriFunctional_monotoneQuarterCutoff_oneStep_logDefect
    (parent : BombieriTest) (k : ℤ) :
    (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterCutoff parent k))).re =
      (bombieriFunctional
        (bombieriQuadraticTest (monotoneQuarterCell parent k))).re +
      (bombieriFunctional
        (bombieriQuadraticTest
          (monotoneQuarterCutoff parent (k + 1)))).re +
      monotoneQuarterRealLogStepDefect parent k := by
  have hsum :
      monotoneQuarterCell parent k +
          monotoneQuarterCutoff parent (k + 1) =
        monotoneQuarterCutoff parent k := by
    rw [monotoneQuarterCell_eq_cutoff_sub]
    apply TestFunction.ext
    intro x
    simp only [TestFunction.coe_add, Pi.add_apply, TestFunction.coe_sub,
      Pi.sub_apply]
    ring
  rw [← hsum]
  have hexpand := bombieriFunctional_twoBlock_re
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1)) (1 : ℂ)
  simp only [one_smul, Complex.normSq_one, one_mul] at hexpand
  rw [hexpand,
    ← bombieriCompleteRealLogKernelCross_eq_globalCross_re,
    ← monotoneQuarterRealLogStepDefect_eq_completeCross]

/-- The exact weakest one-sided bound needed for this propagation step.  It
is stated locally as an equivalence, rather than packaged as a replacement
positivity hypothesis. -/
theorem monotoneQuarterCutoff_nonnegative_iff_logDefect_lowerBound
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterCutoff parent k))).re ↔
      -((bombieriFunctional
          (bombieriQuadraticTest (monotoneQuarterCell parent k))).re +
        (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCutoff parent (k + 1)))).re) ≤
        monotoneQuarterRealLogStepDefect parent k := by
  rw [bombieriFunctional_monotoneQuarterCutoff_oneStep_logDefect]
  constructor <;> intro h <;> linarith

/-- Under the recursive inner nonnegativity assumption, the threshold in the
preceding exact bound is nonpositive because the head cell is ratio two. -/
theorem monotoneQuarter_logDefect_requiredThreshold_nonpositive
    (parent : BombieriTest) (k : ℤ)
    (hinner : 0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneQuarterCutoff parent (k + 1)))).re) :
    -((bombieriFunctional
        (bombieriQuadraticTest (monotoneQuarterCell parent k))).re +
      (bombieriFunctional
        (bombieriQuadraticTest
          (monotoneQuarterCutoff parent (k + 1)))).re) ≤ 0 := by
  have hhead : 0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterCell parent k))).re :=
    bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
      (monotoneQuarterCell parent k) (monotoneQuarterCell_ratioTwo parent k)
  linarith

/-- The remaining analytic term is exactly archimedean minus Mangoldt.  The
inner diagonal assumption does not alter either signed parent correlation
in this expression. -/
theorem monotoneQuarterRealLogStepDefect_eq_archimedean_sub_mangoldt
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterRealLogStepDefect parent k =
      2 * monotoneQuarterHeadSuffixRealArchimedeanCross parent k -
        2 * monotoneQuarterHeadSuffixRealPrimeCross parent k := by
  unfold monotoneQuarterRealLogStepDefect
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationLogDefectStructural
