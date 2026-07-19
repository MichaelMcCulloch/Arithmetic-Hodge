import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutFrontierStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterSingleCrossingStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ArithmeticFunction BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutContractionAttemptStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneCutPrimePhaseStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneQuarterSingleCrossingStructural
open MultiplicativeWeilMonotoneRealCutFrontierStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# Real nested-cutoff contraction: exact remaining obstruction

For a conjugation-fixed parent, a real nested-cutoff scalar removes the
antisymmetric prime phase exactly.  The remaining cutoff coefficient is the
ordered product of two real nested multipliers.  This file separates that
product into its nonnegative same-side and crossing magnitudes without
changing the sign of the parent correlation.

The separation does not produce a new unconditional scalar interval.  The
full functional still contains the signed head--suffix global cross, or,
equivalently, the same-side and crossing prime kernels both retain the signed
parent correlation.  The exact formulas below isolate this residual datum.
-/

/-! ## Real multiplier and ordered prime mask -/

/-- The real ordered coefficient in the prime correlation. -/
def monotoneRealCutOrderedMask (k : ℤ) (d x y : ℝ) : ℝ :=
  monotoneQuarterNestedMultiplier k d (x * y) *
    monotoneQuarterNestedMultiplier k d y

/-- For a real scalar the completed phase mask is exactly the ordered product
of the two real nested multipliers. -/
theorem monotoneCutPhaseRealMask_ofReal_eq_orderedMask
    (k : ℤ) (d x y : ℝ) :
    monotoneCutPhaseRealMask k (d : ℂ) x y =
      monotoneRealCutOrderedMask k d x y := by
  rw [monotoneCutPhaseRealMask_eq_completed]
  norm_num [monotoneRealCutOrderedMask, monotoneQuarterNestedMultiplier]

/-- At a prime ratio, a negative real mask below the threshold is necessarily
the unique positive-to-negative crossing. -/
theorem monotoneRealCutOrderedMask_neg_iff_crossing
    (k : ℤ) {d x y : ℝ} (hd : d < -1) (hx : 1 ≤ x) (hy : 0 ≤ y) :
    monotoneRealCutOrderedMask k d x y < 0 ↔
      0 < monotoneQuarterNestedMultiplier k d y ∧
        monotoneQuarterNestedMultiplier k d (x * y) < 0 := by
  have hyxy : y ≤ x * y := by nlinarith
  unfold monotoneRealCutOrderedMask
  rw [mul_comm]
  exact monotoneQuarterNestedMultiplier_mul_neg_iff k hd hyxy

/-- In the complementary range `d ≥ -1`, every real ordered mask is
pointwise nonnegative. -/
theorem monotoneRealCutOrderedMask_nonnegative_of_neg_one_le
    (k : ℤ) {d : ℝ} (hd : -1 ≤ d) (x y : ℝ) :
    0 ≤ monotoneRealCutOrderedMask k d x y := by
  exact mul_nonneg
    (monotoneQuarterNestedMultiplier_nonnegative_of_neg_one_le
      k hd (x * y))
    (monotoneQuarterNestedMultiplier_nonnegative_of_neg_one_le k hd y)

/-- The endpoint dilation used below is ordered (`x ≥ 1`). -/
theorem one_le_monotoneRealCut_endpointRatio (k : ℤ) :
    1 ≤ quarterLogLatticePoint (k + 2) /
      quarterLogLatticePoint (k + 1) := by
  apply (le_div_iff₀ (quarterLogLatticePoint_pos (k + 1))).2
  simpa only [one_mul] using
    (quarterLogLatticePoint_mono (show k + 1 ≤ k + 2 by omega))

/-- The threshold `d = -1` is sharp even before integration: below it the two
transition endpoints give a negative ordered coefficient. -/
theorem monotoneRealCutOrderedMask_endpoint
    (k : ℤ) (d : ℝ) :
    monotoneRealCutOrderedMask k d
        (quarterLogLatticePoint (k + 2) /
          quarterLogLatticePoint (k + 1))
        (quarterLogLatticePoint (k + 1)) = 1 + d := by
  have hprod :
      quarterLogLatticePoint (k + 2) /
          quarterLogLatticePoint (k + 1) *
        quarterLogLatticePoint (k + 1) =
      quarterLogLatticePoint (k + 2) := by
    exact div_mul_cancel₀ _ (quarterLogLatticePoint_pos (k + 1)).ne'
  unfold monotoneRealCutOrderedMask
  rw [hprod, monotoneQuarterNestedMultiplier_upper,
    monotoneQuarterNestedMultiplier_shared]
  ring

/-- Consequently every `d < -1` has an explicit negative ordered mask. -/
theorem monotoneRealCutOrderedMask_endpoint_negative
    (k : ℤ) {d : ℝ} (hd : d < -1) :
    monotoneRealCutOrderedMask k d
        (quarterLogLatticePoint (k + 2) /
          quarterLogLatticePoint (k + 1))
        (quarterLogLatticePoint (k + 1)) < 0 := by
  rw [monotoneRealCutOrderedMask_endpoint]
  linarith

/-! ## Same-side/crossing separation -/

/-- Nonnegative magnitude of the same-side part of the ordered mask. -/
def monotoneRealCutSameSideCoefficient (k : ℤ) (d x y : ℝ) : ℝ :=
  max (monotoneRealCutOrderedMask k d x y) 0

/-- Nonnegative magnitude of the crossing part of the ordered mask. -/
def monotoneRealCutCrossingCoefficient (k : ℤ) (d x y : ℝ) : ℝ :=
  max (-monotoneRealCutOrderedMask k d x y) 0

theorem monotoneRealCutSameSideCoefficient_nonnegative
    (k : ℤ) (d x y : ℝ) :
    0 ≤ monotoneRealCutSameSideCoefficient k d x y := by
  exact le_max_right _ _

theorem monotoneRealCutCrossingCoefficient_nonnegative
    (k : ℤ) (d x y : ℝ) :
    0 ≤ monotoneRealCutCrossingCoefficient k d x y := by
  exact le_max_right _ _

/-- Exact positive/negative-part decomposition of the ordered mask. -/
theorem monotoneRealCutOrderedMask_eq_sameSide_sub_crossing
    (k : ℤ) (d x y : ℝ) :
    monotoneRealCutOrderedMask k d x y =
      monotoneRealCutSameSideCoefficient k d x y -
        monotoneRealCutCrossingCoefficient k d x y := by
  by_cases hmask : 0 ≤ monotoneRealCutOrderedMask k d x y
  · rw [monotoneRealCutSameSideCoefficient,
      monotoneRealCutCrossingCoefficient, max_eq_left hmask,
      max_eq_right (neg_nonpos.mpr hmask)]
    ring
  · have hmask' : monotoneRealCutOrderedMask k d x y ≤ 0 :=
      le_of_not_ge hmask
    rw [monotoneRealCutSameSideCoefficient,
      monotoneRealCutCrossingCoefficient, max_eq_right hmask',
      max_eq_left (neg_nonneg.mpr hmask')]
    ring

/-- In the pointwise nonnegative range the crossing magnitude vanishes, but
the parent correlation below is still signed. -/
theorem monotoneRealCutCrossingCoefficient_eq_zero_of_neg_one_le
    (k : ℤ) {d : ℝ} (hd : -1 ≤ d) (x y : ℝ) :
    monotoneRealCutCrossingCoefficient k d x y = 0 := by
  unfold monotoneRealCutCrossingCoefficient monotoneRealCutOrderedMask
  rw [max_eq_right]
  exact neg_nonpos.mpr
    (monotoneRealCutOrderedMask_nonnegative_of_neg_one_le k hd x y)

/-- Real directed parent correlation retained by both pieces. -/
def monotoneRealCutParentCorrelation
    (parent : BombieriTest) (x y : ℝ) : ℝ :=
  (monotoneCutParentProduct parent x y).re

/-- Same-side prime kernel.  Its coefficient is nonnegative, but its parent
correlation need not be. -/
def monotoneRealCutSameSideKernel
    (parent : BombieriTest) (k : ℤ) (d x y : ℝ) : ℝ :=
  monotoneRealCutSameSideCoefficient k d x y *
    monotoneRealCutParentCorrelation parent x y

/-- Crossing prime kernel, recorded with nonnegative crossing magnitude. -/
def monotoneRealCutCrossingKernel
    (parent : BombieriTest) (k : ℤ) (d x y : ℝ) : ℝ :=
  monotoneRealCutCrossingCoefficient k d x y *
    monotoneRealCutParentCorrelation parent x y

/-- Pointwise, the signed real phase is exactly same-side minus crossing.
Both terms retain the original signed parent correlation. -/
theorem monotoneRealCutOrderedMask_mul_parentCorrelation_eq
    (parent : BombieriTest) (k : ℤ) (d x y : ℝ) :
    monotoneRealCutOrderedMask k d x y *
        monotoneRealCutParentCorrelation parent x y =
      monotoneRealCutSameSideKernel parent k d x y -
        monotoneRealCutCrossingKernel parent k d x y := by
  rw [monotoneRealCutOrderedMask_eq_sameSide_sub_crossing]
  unfold monotoneRealCutSameSideKernel monotoneRealCutCrossingKernel
  ring

/-- Wherever the same-side coefficient is nonzero, its kernel has exactly the
sign of the parent correlation. -/
theorem monotoneRealCutSameSideKernel_nonnegative_iff_parentCorrelation
    (parent : BombieriTest) (k : ℤ) (d x y : ℝ)
    (hcoeff : 0 < monotoneRealCutSameSideCoefficient k d x y) :
    0 ≤ monotoneRealCutSameSideKernel parent k d x y ↔
      0 ≤ monotoneRealCutParentCorrelation parent x y := by
  unfold monotoneRealCutSameSideKernel
  exact mul_nonneg_iff_of_pos_left hcoeff

/-- Wherever a crossing occurs, its magnitude also preserves rather than
controls the sign of the parent correlation. -/
theorem monotoneRealCutCrossingKernel_nonnegative_iff_parentCorrelation
    (parent : BombieriTest) (k : ℤ) (d x y : ℝ)
    (hcoeff : 0 < monotoneRealCutCrossingCoefficient k d x y) :
    0 ≤ monotoneRealCutCrossingKernel parent k d x y ↔
      0 ≤ monotoneRealCutParentCorrelation parent x y := by
  unfold monotoneRealCutCrossingKernel
  exact mul_nonneg_iff_of_pos_left hcoeff

/-! ## Exact integral and prime-sum balance -/

/-- The signed same-side-minus-crossing integral at one dilation ratio. -/
def monotoneRealCutSameCrossingBalanceIntegral
    (parent : BombieriTest) (k : ℤ) (d x : ℝ) : ℝ :=
  ∫ y : ℝ in Set.Ioi 0,
    monotoneRealCutSameSideKernel parent k d x y -
      monotoneRealCutCrossingKernel parent k d x y

/-- For a real-valued parent, the exact signed phase integral is the displayed
same-side-minus-crossing balance. -/
theorem monotoneCutSignedPhaseIntegral_eq_sameCrossingBalance
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (d x : ℝ) :
    monotoneCutSignedPhaseIntegral parent k (d : ℂ) x =
      monotoneRealCutSameCrossingBalanceIntegral parent k d x := by
  rw [monotoneCutSignedPhaseIntegral_eq_real_of_conjugate_fixed
    parent hparent]
  unfold monotoneRealCutSameCrossingBalanceIntegral
  apply integral_congr_ae
  filter_upwards [] with y
  rw [monotoneCutPhaseRealMask_ofReal_eq_orderedMask]
  exact monotoneRealCutOrderedMask_mul_parentCorrelation_eq
    parent k d x y

/-- The exact von-Mangoldt sum of the same-side-minus-crossing balance. -/
def monotoneRealCutSameCrossingPrimeBalance
    (parent : BombieriTest) (k : ℤ) (d : ℝ) : ℝ :=
  ∑' n : ℕ,
    ArithmeticFunction.vonMangoldt (n + 1) *
      (2 * monotoneRealCutSameCrossingBalanceIntegral parent k d
        ((n + 1 : ℕ) : ℝ))

theorem monotoneCutSignedPrimePhaseSum_eq_sameCrossingPrimeBalance
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (d : ℝ) :
    monotoneCutSignedPrimePhaseSum parent k (d : ℂ) =
      monotoneRealCutSameCrossingPrimeBalance parent k d := by
  unfold monotoneCutSignedPrimePhaseSum
    monotoneRealCutSameCrossingPrimeBalance
  apply tsum_congr
  intro n
  rw [monotoneCutSignedPhaseIntegral_eq_sameCrossingBalance
    parent hparent]

/-- Exact local-minus-prime formula after the same-side/crossing separation.
This is the prime-side obstruction left by pointwise mask positivity. -/
theorem bombieriFunctional_monotoneCutPencil_real_re_eq_local_sub_sameCrossing
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (d : ℝ) :
    (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneCutPencil parent k (d : ℂ)))).re =
      (bombieriLocalCriticalForm
        (monotoneCutPencil parent k (d : ℂ))
        (monotoneCutPencil parent k (d : ℂ))).re -
      monotoneRealCutSameCrossingPrimeBalance parent k d := by
  rw [bombieriFunctional_monotoneCutPencil_re_eq_local_sub_signedPrime,
    monotoneCutSignedPrimePhaseSum_eq_sameCrossingPrimeBalance
      parent hparent]

/-! ## Equivalent head--suffix functional obstruction -/

/-- Real nested-cutoff coordinates are head cell plus `(d+1)` times the whole
inner suffix. -/
theorem monotoneCutPencil_ofReal_eq_cell_add_suffix
    (parent : BombieriTest) (k : ℤ) (d : ℝ) :
    monotoneCutPencil parent k (d : ℂ) =
      monotoneQuarterCell parent k +
        ((d + 1 : ℝ) : ℂ) • monotoneQuarterCutoff parent (k + 1) := by
  apply TestFunction.ext
  intro x
  simp only [monotoneCutPencil, TestFunction.coe_add, Pi.add_apply,
    TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul,
    monotoneQuarterCell_apply, monotoneQuarterCutoff_apply,
    monotoneQuarterWeight]
  push_cast
  ring

/-- Exact real quadratic polynomial at the cut.  The ratio-two head diagonal
is known nonnegative; the whole-suffix diagonal and the signed global cross
are the remaining quantities. -/
theorem bombieriFunctional_monotoneCutPencil_ofReal_re_eq_head_cross_suffix
    (parent : BombieriTest) (k : ℤ) (d : ℝ) :
    (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneCutPencil parent k (d : ℂ)))).re =
      (bombieriFunctional
        (bombieriQuadraticTest
          (monotoneQuarterCell parent k))).re +
      (d + 1) ^ 2 *
        (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCutoff parent (k + 1)))).re +
      2 * (d + 1) *
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 1))).re := by
  rw [monotoneCutPencil_ofReal_eq_cell_add_suffix,
    bombieriFunctional_twoBlock_re]
  simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re]
  ring

/-- The head diagonal in the preceding polynomial is unconditional. -/
theorem bombieriFunctional_monotoneQuarterCell_re_nonnegative
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterCell parent k))).re := by
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
    (monotoneQuarterCell parent k) (monotoneQuarterCell_ratioTwo parent k)

/-- Above the mask threshold, a nonnegative suffix diagonal closes the real
ray only after adding the missing nonnegative head--suffix cross sign. -/
theorem bombieriFunctional_monotoneCutPencil_ofReal_nonnegative_of_cross_nonnegative
    (parent : BombieriTest) (k : ℤ) {d : ℝ} (hd : -1 ≤ d)
    (hsuffix : 0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneQuarterCutoff parent (k + 1)))).re)
    (hcross : 0 ≤ (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCutoff parent (k + 1))).re) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneCutPencil parent k (d : ℂ)))).re := by
  rw [bombieriFunctional_monotoneCutPencil_ofReal_re_eq_head_cross_suffix]
  exact add_nonneg
    (add_nonneg
      (bombieriFunctional_monotoneQuarterCell_re_nonnegative parent k)
      (mul_nonneg (sq_nonneg _) hsuffix))
    (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hcross)

/-- Below the threshold, the same polynomial closes under the opposite cross
sign.  Single crossing alone does not supply this global sign. -/
theorem bombieriFunctional_monotoneCutPencil_ofReal_nonnegative_of_cross_nonpositive
    (parent : BombieriTest) (k : ℤ) {d : ℝ} (hd : d ≤ -1)
    (hsuffix : 0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneQuarterCutoff parent (k + 1)))).re)
    (hcross : (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCutoff parent (k + 1))).re ≤ 0) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneCutPencil parent k (d : ℂ)))).re := by
  rw [bombieriFunctional_monotoneCutPencil_ofReal_re_eq_head_cross_suffix]
  exact add_nonneg
    (add_nonneg
      (bombieriFunctional_monotoneQuarterCell_re_nonnegative parent k)
      (mul_nonneg (sq_nonneg _) hsuffix))
    (mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)) hcross)

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutContractionAttemptStructural
