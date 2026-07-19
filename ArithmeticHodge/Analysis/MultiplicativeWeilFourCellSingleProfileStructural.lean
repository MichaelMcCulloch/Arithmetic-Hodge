import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellEnergyAbsorptionStructural
import ArithmeticHodge.Analysis.YoshidaClippedCriticalForm
import ArithmeticHodge.Analysis.YoshidaCriticalLogCorrelation
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointClean

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellSingleProfileStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilBelowThreePrimeReductionStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open YoshidaCauchyPairing
open YoshidaCriticalLogCorrelation
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoEndpointClean

/-!
# The complete four-cell obstruction as one clipped profile

Splitting a four-cell block into two ratio-two halves is useful for importing
known diagonal estimates, but it hides the coupling that has to absorb the
prime-two atom.  Here the whole block is centered once.  Its local reserve is
one clipped critical quadratic at half-width `5 log 2 / 8`, and its only prime
cost is one autocorrelation of that very same profile at lag `-log 2`.

This is an unconditional coordinate reduction.  It does not assign a sign to
the resulting single-profile form.
-/

/-- Exact logarithmic half-width of the five-quarter-step support band. -/
def fourCellWholeHalfWidth (k : ℤ) : ℝ :=
  logarithmicHalfWidth (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 5))

/-- Multiplicative center of the complete four-cell support band. -/
def fourCellWholeCenter (k : ℤ) : ℝ :=
  logarithmicCenter (quarterLogLatticePoint k)
    (quarterLogLatticePoint (k + 5))

/-- The complete four-cell block after one common logarithmic centering. -/
def fourCellWholeCentered
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  normalizedDilation (fourCellWholeCenter k)
    (logarithmicCenter_pos _ _) (monotoneQuarterFourBlock parent k)

/-- The single clipped critical profile of the centered four-cell block. -/
def fourCellWholeProfile
    (parent : BombieriTest) (k : ℤ) :
    YoshidaClippedSmooth (fourCellWholeHalfWidth k) :=
  yoshidaCriticalPullbackCropLinear (fourCellWholeHalfWidth k)
    (fourCellWholeCentered parent k)

theorem fourCellWholeHalfWidth_eq (k : ℤ) :
    fourCellWholeHalfWidth k = 5 * Real.log 2 / 8 := by
  unfold fourCellWholeHalfWidth logarithmicHalfWidth
  unfold quarterLogLatticePoint
  rw [Real.log_exp, Real.log_exp]
  push_cast
  ring

theorem fourCellWholeHalfWidth_pos (k : ℤ) :
    0 < fourCellWholeHalfWidth k := by
  rw [fourCellWholeHalfWidth_eq]
  positivity

theorem fourCellWholeCentered_criticalPullbackSupported
    (parent : BombieriTest) (k : ℤ) :
    YoshidaCriticalPullbackSupported (fourCellWholeHalfWidth k)
      (fourCellWholeCentered parent k) := by
  intro u hu
  unfold fourCellWholeCentered fourCellWholeCenter
  apply logCenteredNormalizedDilation_logarithmicPullback_eq_zero_outside
    (monotoneQuarterFourBlock parent k)
    (quarterLogLatticePoint_pos k)
    (quarterLogLatticePoint_mono (by omega))
    (by
      simpa [monotoneQuarterFourBlock,
        monotoneQuarterFourCellBlock] using
        monotoneQuarterFourCellBlock_tsupport_subset parent k 0)
  exact hu

private theorem bombieriLocalCriticalForm_self_normalizedDilation
    (lambda : ℝ) (hlambda : 0 < lambda) (g : BombieriTest) :
    bombieriLocalCriticalForm (normalizedDilation lambda hlambda g)
        (normalizedDilation lambda hlambda g) =
      bombieriLocalCriticalForm g g := by
  have hd := bombieriFunctional_quadratic_eq_localCritical_sub_prime
    (normalizedDilation lambda hlambda g)
  have hg := bombieriFunctional_quadratic_eq_localCritical_sub_prime g
  rw [bombieriQuadraticTest_normalizedDilation] at hd
  have h := hd.symm.trans hg
  simpa only [sub_left_inj] using h

/-- The complete local reserve is one clipped critical quadratic, rather than
three separately bounded diagonal/cross terms. -/
theorem fourCellWhole_clippedLocal_eq_localCritical
    (parent : BombieriTest) (k : ℤ) :
    yoshidaClippedLocalCriticalForm (fourCellWholeHalfWidth k)
        (fourCellWholeHalfWidth_pos k)
        (fourCellWholeProfile parent k)
        (fourCellWholeProfile parent k) =
      bombieriLocalCriticalForm (monotoneQuarterFourBlock parent k)
        (monotoneQuarterFourBlock parent k) := by
  let lambda := fourCellWholeCenter k
  have hlambda : 0 < lambda := logarithmicCenter_pos _ _
  let g := monotoneQuarterFourBlock parent k
  let gc := fourCellWholeCentered parent k
  have hsupported := fourCellWholeCentered_criticalPullbackSupported parent k
  have hcrop := yoshidaClippedLocalCriticalForm_crop_eq_bombieriLocalCriticalForm
    (fourCellWholeHalfWidth_pos k) gc gc hsupported hsupported
  change yoshidaClippedLocalCriticalForm (fourCellWholeHalfWidth k)
      (fourCellWholeHalfWidth_pos k)
      (fourCellWholeProfile parent k) (fourCellWholeProfile parent k) =
    bombieriLocalCriticalForm g g
  calc
    yoshidaClippedLocalCriticalForm (fourCellWholeHalfWidth k)
        (fourCellWholeHalfWidth_pos k)
        (fourCellWholeProfile parent k) (fourCellWholeProfile parent k) =
      bombieriLocalCriticalForm gc gc := hcrop
    _ = bombieriLocalCriticalForm g g := by
      dsimp only [gc, g, fourCellWholeCentered, lambda, fourCellWholeCenter]
      exact bombieriLocalCriticalForm_self_normalizedDilation
        (fourCellWholeCenter k) hlambda g

/-- Since the crop equals the supported pullback globally, its autocorrelation
is exactly the critical self-correlation of the centered four-cell block. -/
theorem fourCellWholeProfile_crossCorrelation_eq
    (parent : BombieriTest) (k : ℤ) (s : ℝ) :
    crossCorrelation
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (fourCellWholeProfile parent k : ℝ → ℂ) s =
      factorTwoSelfCorrelation (fourCellWholeCentered parent k) s := by
  have hsupported := fourCellWholeCentered_criticalPullbackSupported parent k
  have hprofile :
      (fourCellWholeProfile parent k : ℝ → ℂ) =
        (fourCellWholeCentered parent k).logarithmicPullbackSchwartz
          (1 / 2) := by
    exact yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hsupported
  rw [factorTwoSelfCorrelation, crossCorrelation_apply,
    crossCorrelation_apply]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [hprofile]

/-- The prime-two quadratic is the lag `-log 2` autocorrelation of the same
single clipped profile, with the exact critical Jacobian `sqrt 2`. -/
theorem sqrt_two_mul_fourCell_quadratic_eq_profileCorrelation
    (parent : BombieriTest) (k : ℤ) :
    ((Real.sqrt 2 : ℝ) : ℂ) *
        bombieriQuadraticTest (monotoneQuarterFourBlock parent k) 2 =
      crossCorrelation
        (fourCellWholeProfile parent k : ℝ → ℂ)
        (fourCellWholeProfile parent k : ℝ → ℂ) (-Real.log 2) := by
  let g := monotoneQuarterFourBlock parent k
  let gc := fourCellWholeCentered parent k
  have hcorr := factorTwoSelfCorrelation_neg_log_eq_sqrt_mul_quadratic
    gc 2 (by norm_num)
  dsimp only [gc, fourCellWholeCentered] at hcorr
  rw [bombieriQuadraticTest_normalizedDilation] at hcorr
  rw [fourCellWholeProfile_crossCorrelation_eq parent k]
  simpa only [g] using hcorr.symm

/-- Exact coupled target: four-cell positivity is one clipped local quadratic
minus one autocorrelation of the same profile.  No diagonal Cauchy estimate
or independent-profile relaxation remains in this coordinate. -/
theorem bombieriFunctional_fourBlock_re_eq_singleProfile
    (parent : BombieriTest) (k : ℤ) :
    (bombieriFunctional
        (bombieriQuadraticTest (monotoneQuarterFourBlock parent k))).re =
      (yoshidaClippedLocalCriticalForm (fourCellWholeHalfWidth k)
        (fourCellWholeHalfWidth_pos k)
        (fourCellWholeProfile parent k)
        (fourCellWholeProfile parent k)).re -
      Real.sqrt 2 * Real.log 2 *
        (crossCorrelation
          (fourCellWholeProfile parent k : ℝ → ℂ)
          (fourCellWholeProfile parent k : ℝ → ℂ)
          (-Real.log 2)).re := by
  have hbalance :=
    bombieriFunctional_fourCell_re_eq_localCritical_sub_dilationCorrelation
      parent k 0
  rw [← monotoneQuarterFourBlock_eq_belowThreeFourCellBlock parent k]
    at hbalance
  rw [hbalance]
  rw [← fourCellWhole_clippedLocal_eq_localCritical parent k]
  have hprime := congrArg Complex.re
    (sqrt_two_mul_fourCell_quadratic_eq_profileCorrelation parent k)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hprime
  have hcritical := congrArg Complex.re
    (criticalDilationCorrelation_eq_sqrt_mul_quadraticTest
      (monotoneQuarterFourBlock parent k) 2)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hcritical
  rw [hcritical, hprime]

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellSingleProfileStructural
