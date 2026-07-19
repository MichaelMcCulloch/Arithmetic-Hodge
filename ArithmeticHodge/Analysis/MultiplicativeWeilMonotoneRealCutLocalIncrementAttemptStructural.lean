import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutPositiveParentPropagationAttemptStructural
import ArithmeticHodge.Analysis.YoshidaTZeroTailBounds

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped ArithmeticFunction BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutLocalIncrementAttemptStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneRealCutFrontierStructural
open MultiplicativeWeilMonotoneRealCutPositiveParentPropagationAttemptStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open YoshidaTZeroTailBounds

/-!
# The local-energy increment at a positive monotone cut

The prime cost of a pointwise nonnegative real parent is monotone under the
nested cutoffs.  This file examines whether the full local critical energy
has the matching monotonicity.

The polar endpoint piece really is monotone.  On the critical line, however,
pointwise order of the physical cutoffs does not order their Mellin squared
norms away from frequency zero.  Moreover, at frequency zero the squared
norm increment is nonnegative but the Bombieri local kernel is strictly
negative.  Thus even the valid zero-frequency mask monotonicity enters the
spectral local increment with the wrong sign.

An exact head--suffix expansion isolates the resulting obstruction: the
local increment is the nonnegative ratio-two head diagonal plus twice the
signed local head--suffix cross.  It is negative exactly when that cross
falls below minus one half of the head diagonal.
-/

/-! ## Exact head--suffix local increment -/

theorem monotoneQuarterCutoff_eq_cell_add_suffix
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterCutoff parent k =
      monotoneQuarterCell parent k +
        monotoneQuarterCutoff parent (k + 1) := by
  symm
  simpa using
    (monotoneQuarterCell_add_smul_cutoff_eq_nestedCutoffs
      parent k (1 : ℂ))

/-- The full local increment consists of the head diagonal and the signed
head--suffix local cross. -/
theorem monotoneRealCutLocalCriticalIncrement_eq_head_add_two_cross
    (parent : BombieriTest) (k : ℤ) :
    monotoneRealCutLocalCriticalIncrement parent k =
      (bombieriLocalCriticalForm
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent k)).re +
      2 * (bombieriLocalCriticalForm
        (monotoneQuarterCell parent k)
        (monotoneQuarterCutoff parent (k + 1))).re := by
  let h := monotoneQuarterCell parent k
  let s := monotoneQuarterCutoff parent (k + 1)
  have hcut : monotoneQuarterCutoff parent k = h + s := by
    simpa only [h, s] using
      monotoneQuarterCutoff_eq_cell_add_suffix parent k
  have hconj := congrArg Complex.re
    (bombieriLocalCriticalForm_conj_apply h s)
  simp only [Complex.star_def, Complex.conj_re] at hconj
  unfold monotoneRealCutLocalCriticalIncrement
    monotoneRealCutLocalCriticalEnergy
  rw [hcut]
  simp only [map_add, LinearMap.add_apply, Complex.add_re]
  dsimp only [h, s] at hconj ⊢
  linarith

/-- The ratio-two head local diagonal is unconditionally nonnegative. -/
theorem bombieriLocalCriticalForm_monotoneQuarterCell_re_nonnegative
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ (bombieriLocalCriticalForm
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent k)).re := by
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ :=
    monotoneQuarterCell_ratioTwo parent k
  have hvalue := bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
    (monotoneQuarterCell parent k)
    (monotoneQuarterCell_ratioTwo parent k)
  rw [bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    (monotoneQuarterCell parent k) ha hab hsupport hratio] at hvalue
  exact hvalue

/-- Exact sign obstruction: local monotonicity fails precisely when the
signed head--suffix local cross overwhelms half the positive head diagonal. -/
theorem monotoneRealCutLocalCriticalIncrement_neg_iff_cross
    (parent : BombieriTest) (k : ℤ) :
    monotoneRealCutLocalCriticalIncrement parent k < 0 ↔
      (bombieriLocalCriticalForm
        (monotoneQuarterCell parent k)
        (monotoneQuarterCutoff parent (k + 1))).re <
      -(1 / 2 : ℝ) *
        (bombieriLocalCriticalForm
          (monotoneQuarterCell parent k)
          (monotoneQuarterCell parent k)).re := by
  rw [monotoneRealCutLocalCriticalIncrement_eq_head_add_two_cross]
  constructor <;> intro h <;> linarith

/-! ## Real Mellin endpoints of nonnegative tests -/

theorem mellinLinearMap_ofReal_im_eq_zero_of_conjugate_fixed
    (f : BombieriTest)
    (hfixed : bombieriConjugateTest f = f)
    (sigma : ℝ) :
    (mellinLinearMap (sigma : ℂ) f).im = 0 := by
  have hm := congrArg
    (fun g : BombieriTest ↦ mellinLinearMap (sigma : ℂ) g) hfixed
  change mellin (bombieriConjugateTest f : ℝ → ℂ) (sigma : ℂ) =
    mellin (f : ℝ → ℂ) (sigma : ℂ) at hm
  rw [mellin_bombieriConjugateTest] at hm
  unfold coefficientConjugate at hm
  have hstar : starRingEnd ℂ (sigma : ℂ) = (sigma : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  rw [hstar] at hm
  have him := congrArg Complex.im hm
  change -(mellin (f : ℝ → ℂ) (sigma : ℂ)).im =
    (mellin (f : ℝ → ℂ) (sigma : ℂ)).im at him
  change (mellin (f : ℝ → ℂ) (sigma : ℂ)).im = 0
  linarith

theorem mellinLinearMap_ofReal_re_nonnegative
    (f : BombieriTest)
    (hnonneg : ∀ t : ℝ, 0 ≤ (f t).re)
    (sigma : ℝ) :
    0 ≤ (mellinLinearMap (sigma : ℂ) f).re := by
  have hint := f.mellinConvergent (sigma : ℂ)
  change 0 ≤ (mellin (f : ℝ → ℂ) (sigma : ℂ)).re
  unfold mellin
  calc
    0 ≤ ∫ t : ℝ in Set.Ioi 0,
        ((t : ℂ) ^ ((sigma : ℂ) - 1) • f t).re := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hpow :
          (t : ℂ) ^ ((sigma : ℂ) - 1) =
            ((t ^ (sigma - 1) : ℝ) : ℂ) := by
        calc
          (t : ℂ) ^ ((sigma : ℂ) - 1) =
              (t : ℂ) ^ ((sigma - 1 : ℝ) : ℂ) := by
                congr 1
                push_cast
                rfl
          _ = ((t ^ (sigma - 1) : ℝ) : ℂ) :=
            (Complex.ofReal_cpow ht.le _).symm
      rw [hpow]
      simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (hnonneg t)
    _ = (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ ((sigma : ℂ) - 1) • f t).re := integral_re hint

theorem monotoneQuarterCell_re_nonnegative
    (parent : BombieriTest)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) (t : ℝ) :
    0 ≤ (monotoneQuarterCell parent k t).re := by
  rw [monotoneQuarterCell_apply, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (monotoneQuarterWeight_nonnegative k t) (hnonneg t)

theorem monotoneQuarterCutoff_re_nonnegative
    (parent : BombieriTest)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) (t : ℝ) :
    0 ≤ (monotoneQuarterCutoff parent k t).re := by
  rw [monotoneQuarterCutoff_apply, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (monotoneQuarterStep_nonneg k t) (hnonneg t)

/-! ## Polar endpoint monotonicity -/

def monotoneRealCutPolarEndpointEnergy
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  2 * (mellinLinearMap 1 (monotoneQuarterCutoff parent k) *
    star (mellinLinearMap 0 (monotoneQuarterCutoff parent k))).re

def monotoneRealCutPolarEndpointIncrement
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  monotoneRealCutPolarEndpointEnergy parent k -
    monotoneRealCutPolarEndpointEnergy parent (k + 1)

private theorem polarEndpoint_add_sub_exact
    (h1 h0 s1 s0 : ℂ)
    (hh1 : h1.im = 0) (hh0 : h0.im = 0)
    (hs1 : s1.im = 0) (hs0 : s0.im = 0) :
    2 * ((h1 + s1) * star (h0 + s0)).re -
        2 * (s1 * star s0).re =
      2 * (h1.re * h0.re + h1.re * s0.re + s1.re * h0.re) := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [hh1, hh0, hs1, hs0]
  ring

/-- Exact positive expansion of the polar endpoint increment. -/
theorem monotoneRealCutPolarEndpointIncrement_eq
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (k : ℤ) :
    monotoneRealCutPolarEndpointIncrement parent k =
      2 * (
        (mellinLinearMap 1 (monotoneQuarterCell parent k)).re *
          (mellinLinearMap 0 (monotoneQuarterCell parent k)).re +
        (mellinLinearMap 1 (monotoneQuarterCell parent k)).re *
          (mellinLinearMap 0
            (monotoneQuarterCutoff parent (k + 1))).re +
        (mellinLinearMap 1
            (monotoneQuarterCutoff parent (k + 1))).re *
          (mellinLinearMap 0 (monotoneQuarterCell parent k)).re) := by
  let h := monotoneQuarterCell parent k
  let s := monotoneQuarterCutoff parent (k + 1)
  have hcut : monotoneQuarterCutoff parent k = h + s := by
    simpa only [h, s] using
      monotoneQuarterCutoff_eq_cell_add_suffix parent k
  have hhfixed : bombieriConjugateTest h = h := by
    simpa only [h] using
      bombieriConjugateTest_monotoneQuarterCell parent hfixed k
  have hsfixed : bombieriConjugateTest s = s := by
    simpa only [s] using
      bombieriConjugateTest_monotoneQuarterCutoff parent hfixed (k + 1)
  have hh0 := mellinLinearMap_ofReal_im_eq_zero_of_conjugate_fixed
    h hhfixed 0
  have hh1 := mellinLinearMap_ofReal_im_eq_zero_of_conjugate_fixed
    h hhfixed 1
  have hs0 := mellinLinearMap_ofReal_im_eq_zero_of_conjugate_fixed
    s hsfixed 0
  have hs1 := mellinLinearMap_ofReal_im_eq_zero_of_conjugate_fixed
    s hsfixed 1
  norm_num at hh0 hh1 hs0 hs1
  unfold monotoneRealCutPolarEndpointIncrement
    monotoneRealCutPolarEndpointEnergy
  rw [hcut]
  simp only [map_add]
  dsimp only [h, s] at hh0 hh1 hs0 hs1 ⊢
  exact polarEndpoint_add_sub_exact _ _ _ _ hh1 hh0 hs1 hs0

theorem monotoneRealCutPolarEndpointIncrement_nonnegative
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) :
    0 ≤ monotoneRealCutPolarEndpointIncrement parent k := by
  rw [monotoneRealCutPolarEndpointIncrement_eq parent hfixed]
  have hh0 := mellinLinearMap_ofReal_re_nonnegative
    (monotoneQuarterCell parent k)
    (monotoneQuarterCell_re_nonnegative parent hnonneg k) 0
  have hh1 := mellinLinearMap_ofReal_re_nonnegative
    (monotoneQuarterCell parent k)
    (monotoneQuarterCell_re_nonnegative parent hnonneg k) 1
  have hs0 := mellinLinearMap_ofReal_re_nonnegative
    (monotoneQuarterCutoff parent (k + 1))
    (monotoneQuarterCutoff_re_nonnegative parent hnonneg (k + 1)) 0
  have hs1 := mellinLinearMap_ofReal_re_nonnegative
    (monotoneQuarterCutoff parent (k + 1))
    (monotoneQuarterCutoff_re_nonnegative parent hnonneg (k + 1)) 1
  positivity

/-! ## Critical-line mask obstruction -/

def monotoneRealCutCriticalLineDensity
    (parent : BombieriTest) (k : ℤ) (v : ℝ) : ℝ :=
  (bombieriLocalCriticalKernel v).re *
    Complex.normSq (mellinLinearMap
      ((1 / 2 : ℝ) + v * Complex.I)
      (monotoneQuarterCutoff parent k))

def monotoneRealCutCriticalLineEnergy
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ v : ℝ,
    monotoneRealCutCriticalLineDensity parent k v

def monotoneRealCutCriticalLineIncrement
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  monotoneRealCutCriticalLineEnergy parent k -
    monotoneRealCutCriticalLineEnergy parent (k + 1)

private theorem bombieriLocalCriticalQuadraticIntegrand_integrable'
    (f : BombieriTest) :
    Integrable (bombieriLocalCriticalQuadraticIntegrand f) := by
  apply (bombieriLocalCriticalCrossIntegrand_integrable f f).congr
  filter_upwards [] with v
  simp only [bombieriLocalCriticalQuadraticIntegrand,
    bombieriLocalCriticalCrossIntegrand, Complex.normSq_eq_conj_mul_self,
    mellinLinearMap_apply, starRingEnd_apply]
  ring

private theorem monotoneRealCutCriticalLineDensity_integrable
    (parent : BombieriTest) (k : ℤ) :
    Integrable (monotoneRealCutCriticalLineDensity parent k) := by
  have hint := bombieriLocalCriticalQuadraticIntegrand_integrable'
    (monotoneQuarterCutoff parent k)
  apply hint.re.congr
  filter_upwards [] with v
  unfold monotoneRealCutCriticalLineDensity
    bombieriLocalCriticalQuadraticIntegrand bombieriLocalCriticalKernel
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

/-- The local critical energy is exactly its polar endpoint energy plus the
complete signed critical-line density integral. -/
theorem monotoneRealCutLocalCriticalEnergy_eq_polar_add_criticalLine
    (parent : BombieriTest) (k : ℤ) :
    monotoneRealCutLocalCriticalEnergy parent k =
      monotoneRealCutPolarEndpointEnergy parent k +
        monotoneRealCutCriticalLineEnergy parent k := by
  let f := monotoneQuarterCutoff parent k
  have hint := bombieriLocalCriticalQuadraticIntegrand_integrable' f
  have hre :
      (∫ v : ℝ, (bombieriLocalCriticalQuadraticIntegrand f v).re) =
        (∫ v : ℝ, bombieriLocalCriticalQuadraticIntegrand f v).re := by
    simpa only using integral_re hint
  have hdensity :
      (∫ v : ℝ, bombieriLocalCriticalQuadraticIntegrand f v).re =
        ∫ v : ℝ, monotoneRealCutCriticalLineDensity parent k v := by
    rw [← hre]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp only [f]
    unfold monotoneRealCutCriticalLineDensity
      bombieriLocalCriticalQuadraticIntegrand bombieriLocalCriticalKernel
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    rfl
  unfold monotoneRealCutLocalCriticalEnergy
    monotoneRealCutPolarEndpointEnergy monotoneRealCutCriticalLineEnergy
  rw [bombieriLocalCriticalForm_self]
  unfold bombieriLocalCriticalQuadratic
  dsimp only [f] at hdensity
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [hdensity]

/-- Consequently the full local increment splits exactly into the monotone
polar increment and the signed critical-line increment. -/
theorem monotoneRealCutLocalCriticalIncrement_eq_polar_add_criticalLine
    (parent : BombieriTest) (k : ℤ) :
    monotoneRealCutLocalCriticalIncrement parent k =
      monotoneRealCutPolarEndpointIncrement parent k +
        monotoneRealCutCriticalLineIncrement parent k := by
  rw [monotoneRealCutLocalCriticalIncrement,
    monotoneRealCutLocalCriticalEnergy_eq_polar_add_criticalLine,
    monotoneRealCutLocalCriticalEnergy_eq_polar_add_criticalLine]
  unfold monotoneRealCutPolarEndpointIncrement
    monotoneRealCutCriticalLineIncrement
  ring

def monotoneRealCutCriticalNormIncrementDensity
    (parent : BombieriTest) (k : ℤ) (v : ℝ) : ℝ :=
  Complex.normSq (mellinLinearMap
      ((1 / 2 : ℝ) + v * Complex.I)
      (monotoneQuarterCutoff parent k)) -
    Complex.normSq (mellinLinearMap
      ((1 / 2 : ℝ) + v * Complex.I)
      (monotoneQuarterCutoff parent (k + 1)))

private theorem normSq_add_sub_normSq_eq_head_cross
    (a b : ℂ) :
    Complex.normSq (a + b) - Complex.normSq b =
      Complex.normSq a + 2 * (star a * b).re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-- Exact critical-line norm increment: a positive head square plus a signed
head--suffix interference term. -/
theorem monotoneRealCutCriticalNormIncrementDensity_eq_head_cross
    (parent : BombieriTest) (k : ℤ) (v : ℝ) :
    monotoneRealCutCriticalNormIncrementDensity parent k v =
      Complex.normSq (mellinLinearMap
        ((1 / 2 : ℝ) + v * Complex.I)
        (monotoneQuarterCell parent k)) +
      2 * (star (mellinLinearMap
          ((1 / 2 : ℝ) + v * Complex.I)
          (monotoneQuarterCell parent k)) *
        mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I)
          (monotoneQuarterCutoff parent (k + 1))).re := by
  rw [monotoneRealCutCriticalNormIncrementDensity,
    monotoneQuarterCutoff_eq_cell_add_suffix]
  simp only [map_add]
  exact normSq_add_sub_normSq_eq_head_cross _ _

/-- At nonzero critical frequency an antiphase suffix makes the squared-norm
increment strictly negative.  Physical pointwise order alone supplies no
Mellin-phase exclusion of this mechanism. -/
theorem monotoneRealCutCriticalNormIncrementDensity_neg_of_antiphase
    (parent : BombieriTest) (k : ℤ) (v : ℝ)
    (hanti : mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I)
        (monotoneQuarterCutoff parent (k + 1)) =
      -mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I)
        (monotoneQuarterCell parent k))
    (hhead : mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I)
        (monotoneQuarterCell parent k) ≠ 0) :
    monotoneRealCutCriticalNormIncrementDensity parent k v < 0 := by
  rw [monotoneRealCutCriticalNormIncrementDensity_eq_head_cross, hanti]
  have hnorm : 0 < Complex.normSq (mellinLinearMap
      ((1 / 2 : ℝ) + v * Complex.I)
      (monotoneQuarterCell parent k)) :=
    Complex.normSq_pos.mpr hhead
  let A := mellinLinearMap ((1 / 2 : ℝ) + v * Complex.I)
    (monotoneQuarterCell parent k)
  have hmul : (star A * -A).re = -Complex.normSq A := by
    simp only [mul_neg, Complex.neg_re, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  change Complex.normSq A + 2 * (star A * -A).re < 0
  rw [hmul]
  change 0 < Complex.normSq A at hnorm
  nlinarith

/-- At frequency zero the physical nonnegative-parent mask monotonicity is
valid: the outer half-Mellin squared norm dominates the inner one. -/
theorem monotoneRealCutCriticalNormIncrementDensity_zero_nonnegative
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) :
    0 ≤ monotoneRealCutCriticalNormIncrementDensity parent k 0 := by
  rw [monotoneRealCutCriticalNormIncrementDensity_eq_head_cross]
  norm_num
  have hhfixed := bombieriConjugateTest_monotoneQuarterCell
    parent hfixed k
  have hsfixed := bombieriConjugateTest_monotoneQuarterCutoff
    parent hfixed (k + 1)
  have hhIm := mellinLinearMap_ofReal_im_eq_zero_of_conjugate_fixed
    (monotoneQuarterCell parent k) hhfixed (1 / 2)
  have hsIm := mellinLinearMap_ofReal_im_eq_zero_of_conjugate_fixed
    (monotoneQuarterCutoff parent (k + 1)) hsfixed (1 / 2)
  have hhRe := mellinLinearMap_ofReal_re_nonnegative
    (monotoneQuarterCell parent k)
    (monotoneQuarterCell_re_nonnegative parent hnonneg k) (1 / 2)
  have hsRe := mellinLinearMap_ofReal_re_nonnegative
    (monotoneQuarterCutoff parent (k + 1))
    (monotoneQuarterCutoff_re_nonnegative parent hnonneg (k + 1)) (1 / 2)
  simp only [mellinLinearMap_apply] at hhIm hsIm hhRe hsRe
  norm_num at hhIm hsIm hhRe hsRe
  simp only [Complex.normSq_apply]
  rw [hhIm, hsIm]
  nlinarith [sq_nonneg (mellin (monotoneQuarterCell parent k : ℝ → ℂ)
    (1 / 2 : ℂ)).re]

/-- The local critical kernel has the opposite sign at zero frequency. -/
theorem bombieriLocalCriticalKernel_zero_re_negative :
    (bombieriLocalCriticalKernel 0).re < 0 := by
  unfold bombieriLocalCriticalKernel
  norm_num
  have hdig := digamma_quarter_vertical_re_zero_neg
  have hlog : 0 < Real.log Real.pi :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  linarith

def monotoneRealCutCriticalWeightedIncrementDensity
    (parent : BombieriTest) (k : ℤ) (v : ℝ) : ℝ :=
  (bombieriLocalCriticalKernel v).re *
    monotoneRealCutCriticalNormIncrementDensity parent k v

/-- Integrated form of the obstruction: the critical-line increment is the
Bombieri kernel paired with the signed norm increment, with no omitted local
term. -/
theorem monotoneRealCutCriticalLineIncrement_eq_weightedIntegral
    (parent : BombieriTest) (k : ℤ) :
    monotoneRealCutCriticalLineIncrement parent k =
      (1 / (2 * Real.pi)) * ∫ v : ℝ,
        monotoneRealCutCriticalWeightedIncrementDensity parent k v := by
  have hk := monotoneRealCutCriticalLineDensity_integrable parent k
  have hnext := monotoneRealCutCriticalLineDensity_integrable parent (k + 1)
  unfold monotoneRealCutCriticalLineIncrement
    monotoneRealCutCriticalLineEnergy
  calc
    (1 / (2 * Real.pi)) *
          (∫ v : ℝ, monotoneRealCutCriticalLineDensity parent k v) -
        (1 / (2 * Real.pi)) *
          (∫ v : ℝ, monotoneRealCutCriticalLineDensity parent (k + 1) v) =
        (1 / (2 * Real.pi)) *
          ((∫ v : ℝ, monotoneRealCutCriticalLineDensity parent k v) -
            ∫ v : ℝ,
              monotoneRealCutCriticalLineDensity parent (k + 1) v) := by ring
    _ = (1 / (2 * Real.pi)) * ∫ v : ℝ,
          (monotoneRealCutCriticalLineDensity parent k v -
            monotoneRealCutCriticalLineDensity parent (k + 1) v) := by
          rw [integral_sub hk hnext]
    _ = (1 / (2 * Real.pi)) * ∫ v : ℝ,
          monotoneRealCutCriticalWeightedIncrementDensity parent k v := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with v
          unfold monotoneRealCutCriticalLineDensity
            monotoneRealCutCriticalWeightedIncrementDensity
            monotoneRealCutCriticalNormIncrementDensity
          ring

/-- Full component formula for the attempted local domination.  The first
summand is nonnegative on positive real parents; all remaining local sign
uncertainty is the displayed kernel-weighted Mellin norm increment. -/
theorem monotoneRealCutLocalCriticalIncrement_eq_polar_add_weightedIntegral
    (parent : BombieriTest) (k : ℤ) :
    monotoneRealCutLocalCriticalIncrement parent k =
      monotoneRealCutPolarEndpointIncrement parent k +
        (1 / (2 * Real.pi)) * ∫ v : ℝ,
          monotoneRealCutCriticalWeightedIncrementDensity parent k v := by
  rw [monotoneRealCutLocalCriticalIncrement_eq_polar_add_criticalLine,
    monotoneRealCutCriticalLineIncrement_eq_weightedIntegral]

/-- Therefore the valid zero-frequency norm monotonicity contributes with a
nonpositive sign to the critical-line local increment. -/
theorem monotoneRealCutCriticalWeightedIncrementDensity_zero_nonpositive
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ) :
    monotoneRealCutCriticalWeightedIncrementDensity parent k 0 ≤ 0 := by
  unfold monotoneRealCutCriticalWeightedIncrementDensity
  exact mul_nonpos_of_nonpos_of_nonneg
    (bombieriLocalCriticalKernel_zero_re_negative.le)
    (monotoneRealCutCriticalNormIncrementDensity_zero_nonnegative
      parent hfixed hnonneg k)

/-- If the head has positive half-Mellin mass, the zero-frequency local
spectral density is strictly negative. -/
theorem monotoneRealCutCriticalWeightedIncrementDensity_zero_negative
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ)
    (hhead : 0 < (mellinLinearMap (1 / 2 : ℂ)
      (monotoneQuarterCell parent k)).re) :
    monotoneRealCutCriticalWeightedIncrementDensity parent k 0 < 0 := by
  have hnorm : 0 < monotoneRealCutCriticalNormIncrementDensity
      parent k 0 := by
    rw [monotoneRealCutCriticalNormIncrementDensity_eq_head_cross]
    norm_num
    have hhfixed := bombieriConjugateTest_monotoneQuarterCell
      parent hfixed k
    have hsfixed := bombieriConjugateTest_monotoneQuarterCutoff
      parent hfixed (k + 1)
    have hhIm := mellinLinearMap_ofReal_im_eq_zero_of_conjugate_fixed
      (monotoneQuarterCell parent k) hhfixed (1 / 2)
    have hsIm := mellinLinearMap_ofReal_im_eq_zero_of_conjugate_fixed
      (monotoneQuarterCutoff parent (k + 1)) hsfixed (1 / 2)
    have hsRe := mellinLinearMap_ofReal_re_nonnegative
      (monotoneQuarterCutoff parent (k + 1))
      (monotoneQuarterCutoff_re_nonnegative parent hnonneg (k + 1)) (1 / 2)
    simp only [mellinLinearMap_apply] at hhIm hsIm hsRe
    norm_num at hhIm hsIm hsRe
    change 0 < (mellin (monotoneQuarterCell parent k : ℝ → ℂ)
        (1 / 2 : ℂ)).re at hhead
    simp only [Complex.normSq_apply]
    rw [hhIm, hsIm]
    nlinarith [sq_nonneg (mellin (monotoneQuarterCell parent k : ℝ → ℂ)
      (1 / 2 : ℂ)).re]
  unfold monotoneRealCutCriticalWeightedIncrementDensity
  exact mul_neg_of_neg_of_pos bombieriLocalCriticalKernel_zero_re_negative
    hnorm

/-! ## Exact remaining propagation balance -/

/-- After the polar endpoint is separated, domination of the prime increment
is exactly a global lower bound for the kernel-weighted critical-line
increment.  The pointwise sign results above show why this remaining bound
cannot be obtained from monotonicity of the Mellin norm mask. -/
theorem monotoneRealCutUnsignedSameSideIncrease_le_localIncrement_iff_spectral
    (parent : BombieriTest) (k : ℤ) :
    monotoneRealCutUnsignedSameSidePrimeCost parent k -
          monotoneRealCutUnsignedSameSidePrimeCost parent (k + 1) ≤
        monotoneRealCutLocalCriticalIncrement parent k ↔
      monotoneRealCutUnsignedSameSidePrimeCost parent k -
            monotoneRealCutUnsignedSameSidePrimeCost parent (k + 1) -
          monotoneRealCutPolarEndpointIncrement parent k ≤
        (1 / (2 * Real.pi)) * ∫ v : ℝ,
          monotoneRealCutCriticalWeightedIncrementDensity parent k v := by
  rw [monotoneRealCutLocalCriticalIncrement_eq_polar_add_weightedIntegral]
  constructor <;> intro h <;> linarith

/-- The restricted propagation theorem in its strongest component-level
form: the sole remaining input is the displayed global spectral
compensation bound. -/
theorem bombieriRealQuadraticValue_monotoneQuarterCutoff_propagates_of_spectralCompensation
    (parent : BombieriTest)
    (hfixed : bombieriConjugateTest parent = parent)
    (hnonneg : ∀ t : ℝ, 0 ≤ (parent t).re)
    (k : ℤ)
    (hinner : 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent (k + 1)))
    (hspectral :
      monotoneRealCutUnsignedSameSidePrimeCost parent k -
            monotoneRealCutUnsignedSameSidePrimeCost parent (k + 1) -
          monotoneRealCutPolarEndpointIncrement parent k ≤
        (1 / (2 * Real.pi)) * ∫ v : ℝ,
          monotoneRealCutCriticalWeightedIncrementDensity parent k v) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent k) := by
  apply
    bombieriRealQuadraticValue_monotoneQuarterCutoff_propagates_of_local_dominates_sameSideIncrease
      parent hfixed hnonneg k hinner
  rw [monotoneRealCutLocalCriticalIncrement_eq_polar_add_weightedIntegral]
  linarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutLocalIncrementAttemptStructural
