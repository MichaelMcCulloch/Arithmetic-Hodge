import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutPrimePhaseStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterStepTotalPositivityStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealCutPhaseReductionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutFrontierStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneCutPrimePhaseStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural

/-!
# The real monotone-cut frontier

Global Bombieri positivity reduces exactly to coefficient-conjugation-fixed
parents.  For such a parent its directed pointwise correlation is real, so the
antisymmetric cutoff mask---although nonnegative at every prime ratio---drops
out of the quadratic value.  Once the inner cutoff diagonal is known
nonnegative, every complex cut phase is therefore equivalent to the one real
scalar line.

This removes both the arbitrary complex parent phase and the imaginary cut
phase from the selected monotone-partition frontier.  The remaining analytic
problem is the real head--suffix pencil with its symmetric prime correlation.
-/

/-- Values of a coefficient-conjugation-fixed Bombieri test have zero
imaginary part. -/
theorem apply_im_eq_zero_of_conjugate_fixed
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (x : ℝ) :
    (parent x).im = 0 := by
  have hx := congrArg (fun f : BombieriTest ↦ f x) hparent
  have him := congrArg Complex.im hx
  change -(parent x).im = (parent x).im at him
  linarith

/-- Consequently every directed parent product is real pointwise. -/
theorem monotoneCutParentProduct_im_eq_zero_of_conjugate_fixed
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (x y : ℝ) :
    (monotoneCutParentProduct parent x y).im = 0 := by
  unfold monotoneCutParentProduct
  rw [Complex.mul_im]
  have hxy := apply_im_eq_zero_of_conjugate_fixed parent hparent (x * y)
  have hy := apply_im_eq_zero_of_conjugate_fixed parent hparent y
  have hstarRe : (starRingEnd ℂ (parent y)).re = (parent y).re := rfl
  have hstarIm : (starRingEnd ℂ (parent y)).im = -(parent y).im := rfl
  rw [hstarRe, hstarIm, hxy, hy]
  ring

/-- For a real-valued parent the antisymmetric phase term vanishes before
integration, leaving only the real phase mask times a real correlation. -/
theorem monotoneCutPhaseMask_mul_parentProduct_re_of_conjugate_fixed
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (d : ℂ) (x y : ℝ) :
    (monotoneCutPhaseMask k d x y *
        monotoneCutParentProduct parent x y).re =
      monotoneCutPhaseRealMask k d x y *
        (monotoneCutParentProduct parent x y).re := by
  rw [monotoneCutPhaseMask_mul_parentProduct_re,
    monotoneCutParentProduct_im_eq_zero_of_conjugate_fixed
      parent hparent x y]
  ring

/-- Integrated form of the same cancellation: the signed phase integral has
no antisymmetric contribution for a real-valued parent. -/
theorem monotoneCutSignedPhaseIntegral_eq_real_of_conjugate_fixed
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (d : ℂ) (x : ℝ) :
    monotoneCutSignedPhaseIntegral parent k d x =
      ∫ y : ℝ in Set.Ioi 0,
        monotoneCutPhaseRealMask k d x y *
          (monotoneCutParentProduct parent x y).re := by
  unfold monotoneCutSignedPhaseIntegral
  apply integral_congr_ae
  filter_upwards [] with y
  rw [monotoneCutParentProduct_im_eq_zero_of_conjugate_fixed
    parent hparent x y]
  ring

/-- Exact full-functional phase reduction for the specialized nested-cutoff
pencil.  The imaginary scalar direction is only a nonnegative multiple of the
inner-cutoff diagonal. -/
theorem bombieriFunctional_monotoneCutPencil_re_eq_realPhase_add_imagSq
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) (d : ℂ) :
    (bombieriFunctional
        (bombieriQuadraticTest (monotoneCutPencil parent k d))).re =
      (bombieriFunctional
        (bombieriQuadraticTest
          (monotoneCutPencil parent k (d.re : ℂ)))).re +
        d.im ^ 2 *
          (bombieriFunctional
            (bombieriQuadraticTest
              (monotoneQuarterCutoff parent (k + 1)))).re := by
  exact bombieriFunctional_twoBlock_re_eq_realPhase_add_imagSq
    (monotoneQuarterCutoff parent k)
    (monotoneQuarterCutoff parent (k + 1))
    (bombieriConjugateTest_monotoneQuarterCutoff parent hparent k)
    (bombieriConjugateTest_monotoneQuarterCutoff parent hparent (k + 1)) d

/-- Assuming the already-recursive inner diagonal, the full complex nested
cutoff pencil is nonnegative exactly when every real phase is nonnegative. -/
theorem bombieriFunctional_monotoneCutPencil_all_complex_nonneg_iff_all_real
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ)
    (hinner : 0 ≤
      (bombieriFunctional
        (bombieriQuadraticTest
          (monotoneQuarterCutoff parent (k + 1)))).re) :
    (∀ d : ℂ,
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest (monotoneCutPencil parent k d))).re) ↔
      ∀ a : ℝ,
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneCutPencil parent k (a : ℂ)))).re := by
  exact bombieriFunctional_twoBlock_all_complex_nonneg_iff_all_real
    (monotoneQuarterCutoff parent k)
    (monotoneQuarterCutoff parent (k + 1))
    (bombieriConjugateTest_monotoneQuarterCutoff parent hparent k)
    (bombieriConjugateTest_monotoneQuarterCutoff parent hparent (k + 1))
    hinner

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutFrontierStructural
